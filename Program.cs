using Org.BouncyCastle.Asn1.X9;
using Org.BouncyCastle.Crypto.Parameters;
using Org.BouncyCastle.Math;
using Org.BouncyCastle.Math.EC;

public class ECRecover
{
    // Thanks to:
    // https://github.com/decred/dcrd/blob/75147d231e40ab4f6794fb8b63ad365be2c2fb4f/dcrec/secp256k1/ecdsa/signature.go#L796
    // and
    // https://github.com/emeraldpay/etherjar/blob/2e6ae0d869820d362c5405a1f0b180c3b2af1a6d/etherjar-tx/src/main/java/io/emeraldpay/etherjar/tx/Signer.java#L240
    // G = curve generator
    // N = group order
    // P = field prime, also known as field characteristic
    // Q = public key
    // m = message
    // e = hash of the message
    // r, s = signature
    // X = random point used when creating signature whose x coordinate is r
    //
    // The equation to recover a public key candidate from an ECDSA signature
    // is:
    // Q = r^-1(sX - eG).
    //
    // This can be verified by plugging it in for Q in the sig verification
    // equation:
    // X = s^-1(eG + rQ) (mod N)
    //  => s^-1(eG + r(r^-1(sX - eG))) (mod N)
    //  => s^-1(eG + sX - eG) (mod N)
    //  => s^-1(sX) (mod N)
    //  => X (mod N)

    // Specifically for secp256k1:
    // 1. Fail if r and s are not in [1, N-1]
    // 2. Convert r to integer mod P
    // 3. If pubkey recovery code overflow bit is set:
    //    3.1 Fail if r + N >= P
    //    3.2 r = r + N (mod P)
    // 4. y = +sqrt(r^3 + 7) (mod P)
    //    4.1 Fail if y does not exist
    //    4.2 y = -y if needed to match pubkey recovery code oddness bit
    // 5. X = (r, y)
    // 6. e = H(m) mod N
    // 7. w = r^-1 mod N
    // 8. u1 = -(e * w) mod N
    //    u2 = s * w mod N
    // 9. Q = u1G + u2X
    // 10. Fail if Q is the point at infinity

    public const byte compactSigMagicOffset = 27;
    public const byte compactSigCompPubKey = 4;
    public const byte minValidCode = compactSigMagicOffset;
    public const byte maxValidCode = compactSigMagicOffset + compactSigCompPubKey + 3;
    public static readonly X9ECParameters curve = ECNamedCurveTable.GetByName("secp256k1");
    public static readonly ECDomainParameters domainParams = new ECDomainParameters(curve.Curve, curve.G, curve.N, curve.H, curve.GetSeed());

    public static byte[] ECrecoverPublicKey(byte[] message, byte[] signature)
    {
        if(message.Length != 32)  throw new ArgumentException($"Invalid message length {message.Length}; expected 32");
        if(signature.Length != 65)  throw new ArgumentException($"Invalid signature length {signature.Length}; expected 65 with (r,s,v)");
        byte[] r = signature[..32];
        byte[] s = signature[32..64];
        byte v = signature[64];
        return ECrecoverPublicKey(message, r, s, v);
    }

    public static byte[] ECrecoverPublicKey(byte[] message, byte[] rByte, byte[] sByte, byte vByte)
    {
        if (message.Length != 32) throw new ArgumentException($"Invalid message length {message.Length}; expected 32");
        if (rByte.Length != 32) throw new ArgumentException($"Invalid r length {rByte.Length}; expected 32");
        if (sByte.Length != 32) throw new ArgumentException($"Invalid s length {sByte.Length}; expected 32");
        if (vByte < minValidCode || vByte > maxValidCode) throw new ArgumentException($"Invalid v=={vByte}; expected v in [{minValidCode}, {maxValidCode}]");

        BigInteger r = new BigInteger(1, rByte);
        BigInteger s = new BigInteger(1, sByte);

        return ECrecoverPublicKey(message, r, s, vByte);
    }

    public static byte[] ECrecoverPublicKey(byte[] message, BigInteger r, BigInteger s, byte v)
    {
        if (v < minValidCode || v > maxValidCode) throw new ArgumentException($"Invalid v=={v}; expected v in [{minValidCode}, {maxValidCode}]");
        if (r.CompareTo(BigInteger.One) < 0 || r.CompareTo(curve.N) > 0) throw new ArgumentException($"Invalid r value {r}; expected [1, {curve.N}]");
        if (s.CompareTo(BigInteger.One) < 0 || s.CompareTo(curve.N) > 0) throw new ArgumentException($"Invalid s value {s}; expected [1, {curve.N}]");

        byte sigRecoveryCode = (byte)(v - 27);
        //bool wasCompressed = (sigRecoveryCode&compactSigCompPubKey) != 0;
        byte pubKeyRecoveryCode = (byte)(sigRecoveryCode & 3);

        BigInteger i = BigInteger.ValueOf(pubKeyRecoveryCode / 2);
        BigInteger x = r.Add(i.Multiply(curve.N));
        if (x.CompareTo(curve.Curve.Field.Characteristic) > 0)
            throw new ArgumentException("Cannot have point co-ordinates larger than this as everything takes place modulo P");

        ECPoint R = DecompressKey(x, (pubKeyRecoveryCode & 1) == 1);
        if (!R.Multiply(curve.N).IsInfinity)
            throw new ArgumentException("If nR != point at infinity, then recId (i.e. v) is invalid");

        BigInteger e = new BigInteger(1, message);
        BigInteger eInv = BigInteger.Zero.Subtract(e).Mod(curve.N);
        BigInteger rInv = r.ModInverse(curve.N);
        BigInteger srInv = rInv.Multiply(s).Mod(curve.N);
        BigInteger eInvrInv = rInv.Multiply(eInv).Mod(curve.N);

        ECPoint q = ECAlgorithms.SumOfTwoMultiplies(domainParams.G, eInvrInv, R, srInv);

        byte[] full = q.GetEncoded(false);
        // For Ethereum we don't use first byte of the key
        return full[1..];
    }

    public static ECPoint DecompressKey(BigInteger xBN, bool yBit)
    {
        var Curve = curve.Curve;
        ECFieldElement x = Curve.FromBigInteger(xBN);
        ECFieldElement alpha = x.Multiply(x.Square().Add(Curve.A)).Add(Curve.B);
        ECFieldElement beta = alpha.Sqrt();
        if (beta == null)
            throw new ArgumentException("Invalid point compression");
        ECPoint ecPoint;
        BigInteger nBeta = beta.ToBigInteger();
        if (nBeta.TestBit(0) == yBit)
            ecPoint = Curve.CreatePoint(x.ToBigInteger(), nBeta);
        else
        {
            ECFieldElement y = Curve.FromBigInteger(Curve.Field.Characteristic.Subtract(nBeta));
            ecPoint = Curve.CreatePoint(x.ToBigInteger(), y.ToBigInteger());
        }
        return ecPoint;
    }

    public static byte[] StringToByteArray(string hex)
    {
        if (hex.StartsWith("0x"))
            hex = hex.Substring(2);
        int NumberChars = hex.Length;
        byte[] bytes = new byte[NumberChars / 2];
        for (int i = 0; i < NumberChars; i += 2)
            bytes[i / 2] = Convert.ToByte(hex.Substring(i, 2), 16);
        return bytes;
    }

    static void Main(string[] args)
    {
        // string privateKey = "0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6";
        // Go to https://www.ethtools.online/eth-priv-to-pub to check the results
        string signature = "0xa5fd961062409874e2cd448d32f9144d109aadc602b17fe38fa7f0db650cb6a50fc8dd3f1f57dbfd62aed188bf0de50a45155710db81cb250c7527f8bb0dd7bc1b";
        string hashedMessage = "0x8b324e5601157c55abacfe60de27a774e09137007a949ef7d5815f098b5beebf";
        byte[] pubkey = ECrecoverPublicKey(StringToByteArray(hashedMessage), StringToByteArray(signature));
        // 20B871F3CED029E14472EC4EBC3C0448164942B123AA6AF91A3386C1C403E0EBD3B4A5752A2B6C49E574619E6AA0549EB9CCD036B9BBC507E1F7F9712A236092
        Console.WriteLine(Convert.ToHexString(pubkey));
    }
}

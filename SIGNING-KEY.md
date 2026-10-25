# DARM release signing key

PerceptraAI Lab signs published DARM qualification evidence with this Ed25519 key (DSSE envelopes produced by `gate7.sign`).

- **Fingerprint** (SHA-256 of the raw 32-byte public key): `713f88cb3c2cfe50de081e251155af4fd444db0e77289ec02f352cbbe7e65d2f`
- **Key ID:** `713f88cb3c2cfe50`
- **First used:** v0.5.2 signed qualification, 19 October 2026. Also signs the v0.5.3 qualification (25 October 2026).

```
-----BEGIN PUBLIC KEY-----
MCowBQYDK2VwAyEAW6TslmtIB+gHT/jPtzRsuRndBrC3zXnwf876lWzFQtg=
-----END PUBLIC KEY-----
```

**Not a DARM signing key:** `b7423d90571b55f472013a553436a407e0be00b76d3f91254928a98b5d3a706c`, shipped in the pilot appliance 0.1.2 `keys/` folder. It has never signed published evidence. Do not trust signatures made with it.

To check a copy of the public key against the fingerprint above:

```
python3 -c "import hashlib,sys;from cryptography.hazmat.primitives import serialization as s;k=s.load_pem_public_key(open(sys.argv[1],'rb').read());print(hashlib.sha256(k.public_bytes(s.Encoding.Raw,s.PublicFormat.Raw)).hexdigest())" darm-claims.pub
```

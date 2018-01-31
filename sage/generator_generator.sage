## Generate extra generators for secp256k1

import sys;
import hashlib;

# Original parameters for secp256k1
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
F = FiniteField (p)
C = EllipticCurve ([F(0), F(7)])
G = C.lift_x(0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798)

N_PAIRS = 65536

# Create generator
def generator(curve, seed):
    hash = hashlib.sha256(seed).hexdigest()
    hashint = int(hash, 16)
    return curve.lift_x(hashint)

def word(n, shift):
    return (int(n) >> shift) % 0x100000000

# Print it in a C-readable format
def print_generator(generator):
    (x, y) = generator.xy()
    sys.stdout.write("SECP256K1_GE_CONST(\n")
    sys.stdout.write("    0x%08xUL, 0x%08xUL, 0x%08xUL, 0x%08xUL,\n" % (word(x, 224), word(x, 192), word(x, 160), word(x, 128)))
    sys.stdout.write("    0x%08xUL, 0x%08xUL, 0x%08xUL, 0x%08xUL,\n" % (word(x, 96), word(x, 64), word(x, 32), word(x, 0)))
    sys.stdout.write("    0x%08xUL, 0x%08xUL, 0x%08xUL, 0x%08xUL,\n" % (word(y, 224), word(y, 192), word(y, 160), word(y, 128)))
    sys.stdout.write("    0x%08xUL, 0x%08xUL, 0x%08xUL, 0x%08xUL\n"  % (word(y, 96), word(y, 64), word(y, 32), word(y, 0)))
    sys.stdout.write(")")

# Bytes of G, encoded as a compressed pubkey, in hex
ghex = '0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8'

# Elements' H
sys.stdout.write("#ifndef _SECP256K1_MODULE_BULLETPROOF_GENERATORS_\n");
sys.stdout.write("#define _SECP256K1_MODULE_BULLETPROOF_GENERATORS_\n");
sys.stdout.write("/* File generated by sage/generator_generator.sage */\n\n")
sys.stdout.write("#include \"group.h\"\n\n")

sys.stdout.write("/* Elements' H, sha256(G) */\n")
sys.stdout.write("static const secp256k1_ge secp256k1_ge_const_g2 = ")
print_generator(generator(C, ghex.decode('hex')))
sys.stdout.write(";\n\n")

# 128 generators
sys.stdout.write("/* 128 generators to be used for rangeproofs. Each is computed by hashing\n")
sys.stdout.write(" * G alongside the smallest one-byte index that works.\n")
sys.stdout.write(" */\n")
sys.stdout.write("static const secp256k1_ge secp256k1_ge_const_gi[%d] = {\n" % N_PAIRS)
idx = 0
done = 0
while done < N_PAIRS:
    idx += 1  ## it can be checked that 0 doesn't work, so harmless to skip it
    try:
        if idx < 0x100:
            gen = generator(C, ("%s%02x" % (ghex, idx)).decode('hex'))
        elif idx < 0x10000:
            gen = generator(C, ("%s%04x" % (ghex, idx)).decode('hex'))
        elif idx < 0x1000000:
            gen = generator(C, ("%s%06x" % (ghex, idx)).decode('hex'))
        sys.stdout.write("/* sha256(G || %d) */\n" % idx)
        print_generator(gen)
        if done == N_PAIRS - 1:
            sys.stdout.write("\n")
        else:
            sys.stdout.write(",\n")
        done += 1
    except ValueError:
        continue
sys.stdout.write("};\n\n")
sys.stdout.write("#endif")

#done
sys.stdout.flush()


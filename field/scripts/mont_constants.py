#!/usr/bin/env python3
"""Print Montgomery constants for a prime modulus.

Usage:
    python3 mont_constants.py <modulus>
    python3 mont_constants.py 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

Outputs, for R = 2^(64 * n) where n is the number of u64 limbs needed to hold p:
  * R^2 mod p as little-endian u64 limbs
  * -p^-1 mod 2^64 (the CIOS/SOS reduction multiplier)
"""

import sys


def parse_modulus(s: str) -> int:
    s = s.strip().replace("_", "")
    if s.lower().startswith("0x"):
        return int(s, 16)
    return int(s)


def limbs_le(x: int, n: int) -> list[int]:
    mask = (1 << 64) - 1
    return [(x >> (64 * i)) & mask for i in range(n)]


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <modulus>", file=sys.stderr)
        return 1
    p = parse_modulus(sys.argv[1])
    if p <= 1 or p % 2 == 0:
        print("modulus must be an odd integer > 1", file=sys.stderr)
        return 1

    n = (p.bit_length() + 63) // 64
    r = 1 << (64 * n)
    r_squared = (r * r) % p
    p_inv_pos = pow(p, -1, 1 << 64)
    p_inv_neg = (-p_inv_pos) & ((1 << 64) - 1)

    print(f"limbs (n): {n}")
    print(f"R^2 mod p:")
    for i, limb in enumerate(limbs_le(r_squared, n)):
        print(f"  [{i}] 0x{limb:016X}")
    print(f"-p^-1 mod 2^64: 0x{p_inv_neg:016X}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

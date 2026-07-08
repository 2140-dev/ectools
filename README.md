# ectools

This repository implements finite field arithmetic, elliptic curves in short Weierstrass form, and other primitives that may be used in more complex protocols, such as pairings, isogenies, etc. When cryptographic protocols are proposed in academia, these crates may be used to implement them and assess performance and complexity.

## Crates
- `curve` implementation of point addition and multiplication over a generic elliptic curve
- `field` airthmetic over finite fields

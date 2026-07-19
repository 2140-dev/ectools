use curve::{Curve, Point, Scalar, Secp256k1Curve};
use field::{FieldElement, Secp256k1FieldOrder, Secp256k1GroupOrder};
use rand::{RngExt, rng};

use std::{
    collections::BTreeMap,
    hash::{DefaultHasher, Hash, Hasher},
};

type Sc = Scalar<Secp256k1GroupOrder>;
type Fe = FieldElement<Secp256k1GroupOrder>;
type Pt = Point<Secp256k1FieldOrder>;

const N: u64 = 5;
const T: usize = 3;

fn mul_point(k: Fe, p: Pt) -> Pt {
    Secp256k1Curve.multiply(Sc::from_bytes(k.to_bytes_le()), p)
}

fn eval_poly(coeffs: &[Fe], x: Fe) -> Fe {
    let mut acc = Fe::zero();
    for c in coeffs.iter().rev() {
        acc = acc * x + *c;
    }
    acc
}

fn lagrange_at_zero(i: u64, signers: &[u64]) -> Fe {
    let i_fe = Fe::from_u64(i);
    let mut num = Fe::one();
    let mut den = Fe::one();
    for &j in signers {
        if j == i {
            continue;
        }
        let j_fe = Fe::from_u64(j);
        num *= j_fe;
        den *= j_fe - i_fe;
    }
    num * den.inv()
}

fn hash_rho(i: u64, msg: &str, b: &[(u64, Pt, Pt)]) -> Fe {
    let mut h = DefaultHasher::new();
    "FROST-rho".hash(&mut h);
    i.hash(&mut h);
    msg.hash(&mut h);
    for (j, d, e) in b {
        j.hash(&mut h);
        d.hash(&mut h);
        e.hash(&mut h);
    }
    Fe::from_u64(h.finish())
}

fn hash_challenge(r: Pt, x: Pt, msg: &str) -> Fe {
    let mut h = DefaultHasher::new();
    "FROST-chal".hash(&mut h);
    r.hash(&mut h);
    x.hash(&mut h);
    msg.hash(&mut h);
    Fe::from_u64(h.finish())
}

fn main() {
    let mut args = std::env::args();
    let _prog = args.next().unwrap();
    let msg = args
        .next()
        .expect("Usage: cargo run --release --example frost -- \"some message\"");
    println!("Message: {msg}");

    let curve = Secp256k1Curve;
    let g = Secp256k1Curve::generator();
    let mut rng = rng();

    let mut coeffs: Vec<Fe> = Vec::with_capacity(T);
    for _ in 0..T {
        coeffs.push(Fe::from_bytes_unchecked(rng.random::<[u8; 32]>()));
    }
    let secret = coeffs[0];
    let group_pk = mul_point(secret, g);
    println!("Dealer produced group public key for {T}-of-{N} threshold.");

    let shares: BTreeMap<u64, Fe> = (1..=N)
        .map(|i| (i, eval_poly(&coeffs, Fe::from_u64(i))))
        .collect();
    let verification_shares: BTreeMap<u64, Pt> =
        shares.iter().map(|(i, s)| (*i, mul_point(*s, g))).collect();

    let signers: Vec<u64> = vec![1, 3, 4];
    assert_eq!(signers.len(), T);

    let mut secret_nonces: BTreeMap<u64, (Fe, Fe)> = BTreeMap::new();
    let mut commitments: Vec<(u64, Pt, Pt)> = Vec::with_capacity(T);
    for &i in &signers {
        let d = Fe::from_bytes_unchecked(rng.random::<[u8; 32]>());
        let e = Fe::from_bytes_unchecked(rng.random::<[u8; 32]>());
        let big_d = mul_point(d, g);
        let big_e = mul_point(e, g);
        secret_nonces.insert(i, (d, e));
        commitments.push((i, big_d, big_e));
    }
    println!(
        "Round 1: {} nonce commitments published.",
        commitments.len()
    );

    let mut rho: BTreeMap<u64, Fe> = BTreeMap::new();
    let mut r = Pt::infinity();
    for (i, big_d, big_e) in &commitments {
        let rho_i = hash_rho(*i, &msg, &commitments);
        rho.insert(*i, rho_i);
        r = curve.add(r, curve.add(*big_d, mul_point(rho_i, *big_e)));
    }
    let c = hash_challenge(r, group_pk, &msg);

    let mut partials: BTreeMap<u64, Fe> = BTreeMap::new();
    for &i in &signers {
        let (d_i, e_i) = secret_nonces[&i];
        let rho_i = rho[&i];
        let lambda_i = lagrange_at_zero(i, &signers);
        let s_i = shares[&i];
        let z_i = d_i + e_i * rho_i + lambda_i * s_i * c;
        partials.insert(i, z_i);
    }
    println!("Round 2: {T} partial signatures produced.");

    let probe = signers[0];
    let (_, big_d_p, big_e_p) = commitments
        .iter()
        .find(|(j, _, _)| *j == probe)
        .copied()
        .unwrap();
    let lhs_partial = mul_point(partials[&probe], g);
    let rhs_partial = curve.add(
        curve.add(big_d_p, mul_point(rho[&probe], big_e_p)),
        mul_point(
            lagrange_at_zero(probe, &signers) * c,
            verification_shares[&probe],
        ),
    );
    assert_eq!(lhs_partial, rhs_partial, "partial signature check failed");
    println!("Partial signature from signer {probe} verified.");

    let mut z = Fe::zero();
    for &i in &signers {
        z += partials[&i];
    }

    let lhs = mul_point(z, g);
    let rhs = curve.add(r, mul_point(c, group_pk));
    assert_eq!(lhs, rhs, "aggregate signature failed to verify");
    println!("FROST aggregate signature (R, z) verified.");
}

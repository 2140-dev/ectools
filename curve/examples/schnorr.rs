use curve::{Curve, Scalar, Secp256k1Curve};
use field::{FieldElement, Secp256k1GroupOrder};
use rand::{RngExt, rng};

use std::{
    hash::{DefaultHasher, Hash, Hasher},
    time::SystemTime,
};

type Sc = Scalar<Secp256k1GroupOrder>;
type Fe = FieldElement<Secp256k1GroupOrder>;

fn main() {
    let mut args = std::env::args();
    let _prog = args.next().unwrap();
    let message = args
        .next()
        .expect("Usage: cargo run --release \"some message\"");
    println!("Message: {message}");
    let mut rng = rng();
    let private_bytes = rng.random::<[u8; 32]>();
    let private_key = Sc::from_bytes(private_bytes);
    let public_key = Secp256k1Curve::point_from_scalar(private_key);
    println!("Generated public/private keypair.");
    let nonce_bytes = rng.random::<[u8; 32]>();
    let nonce = Sc::from_bytes(nonce_bytes);
    let r = Secp256k1Curve::point_from_scalar(nonce);
    let mut hasher = DefaultHasher::new();
    r.hash(&mut hasher);
    message.hash(&mut hasher);
    let e = hasher.finish();
    let e = Fe::from_u64(e);
    let x = Fe::from_bytes_unchecked(private_bytes);
    let k = Fe::from_bytes_unchecked(nonce_bytes);
    let s = k + e * x;
    let curve = Secp256k1Curve;
    println!("Produced signature (R, s)");
    let time = SystemTime::now();
    let lhs = Secp256k1Curve::point_from_scalar(Sc::from_bytes(s.to_bytes_le()));
    let rhs = curve.add(
        curve.multiply(Sc::from_bytes(e.to_bytes_le()), public_key),
        r,
    );
    assert_eq!(lhs, rhs, "points did not match");
    println!("Schnorr signature verified");
    println!("Took {} microseconds", time.elapsed().unwrap().as_micros());
}

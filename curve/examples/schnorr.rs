use curve::{Scalar, Secp256k1Curve};
use field::FieldElement;
use rand::{RngExt, rng};

use std::{
    hash::{DefaultHasher, Hash, Hasher},
    time::SystemTime,
};

fn main() {
    let mut args = std::env::args();
    let _prog = args.next().unwrap();
    let message = args
        .next()
        .expect("Usage: cargo run --release \"some message\"");
    println!("Message: {message}");
    let mut rng = rng();
    let private_bytes = rng.random::<[u8; 32]>();
    let private_key = Scalar::from_bytes(private_bytes);
    let public_key = Secp256k1Curve::point_from_scalar(private_key);
    println!("Generated public/private keypair.");
    let nonce_bytes = rng.random::<[u8; 32]>();
    let nonce = Scalar::from_bytes(nonce_bytes);
    let r = Secp256k1Curve::point_from_scalar(nonce);
    let mut hasher = DefaultHasher::new();
    r.hash(&mut hasher);
    message.hash(&mut hasher);
    let e = hasher.finish();
    let e = FieldElement::<field::Secp256k1GroupOrder>::from_u64(e);
    let x = FieldElement::<field::Secp256k1GroupOrder>::from_bytes_unchecked(private_bytes);
    let k = FieldElement::<field::Secp256k1GroupOrder>::from_bytes_unchecked(nonce_bytes);
    let s = k + e * x;
    println!("Produced signature (R, s)");
    let time = SystemTime::now();
    let lhs = Secp256k1Curve::point_from_scalar(Scalar::from_bytes(s.to_bytes_le()));
    let rhs = public_key.mul(Scalar::from_bytes(e.to_bytes_le())).add(&r);
    assert_eq!(lhs, rhs, "points did not match");
    println!("Schnorr signature verified");
    println!("Took {} milliseconds", time.elapsed().unwrap().as_millis());
}

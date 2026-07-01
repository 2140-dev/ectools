use core::fmt;
use field::{FieldElement, FieldOrder, Limbs, Secp256k1FieldOrder, Secp256k1GroupOrder};

/// y^2 = x^3 + Ax + B
pub trait Curve<F: FieldOrder>: fmt::Debug + Clone + Copy + PartialEq + Eq {
    fn a(&self) -> FieldElement<F>;
    fn b(&self) -> FieldElement<F>;

    fn add(&self, p1: Point<F>, p2: Point<F>) -> Point<F> {
        p1.add(&p2, self.a())
    }

    fn multiply<G: FieldOrder>(&self, scalar: Scalar<G>, point: Point<F>) -> Point<F> {
        point.mul(scalar, self.a())
    }

    fn j_invariant(&self) -> FieldElement<F> {
        let a = self.a();
        let b = self.b();
        let four_a_cubed = FieldElement::from_u64(4) * a * a * a;
        let discriminant = four_a_cubed + FieldElement::from_u64(27) * b * b;
        FieldElement::from_u64(1728) * four_a_cubed * discriminant.inv()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1Curve;

impl Secp256k1Curve {
    pub const A: FieldElement<Secp256k1FieldOrder> = FieldElement::ZERO;
    pub const B: FieldElement<Secp256k1FieldOrder> = FieldElement::from_limbs_unchecked([7, 0, 0, 0]);

    pub const GENERATOR: Point<Secp256k1FieldOrder> = Point::Affine {
        x: FieldElement::from_limbs_unchecked([
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ]),
        y: FieldElement::from_limbs_unchecked([
            0x9C47D08FFB10D4B8,
            0xFD17B448A6855419,
            0x5DA4FBFC0E1108A8,
            0x483ADA7726A3C465,
        ]),
    };

    pub fn point_from_scalar(scalar: Scalar<Secp256k1GroupOrder>) -> Point<Secp256k1FieldOrder> {
        Self.multiply(scalar, Self::GENERATOR)
    }
}

impl Curve<Secp256k1FieldOrder> for Secp256k1Curve {
    fn a(&self) -> FieldElement<Secp256k1FieldOrder> {
        Self::A
    }

    fn b(&self) -> FieldElement<Secp256k1FieldOrder> {
        Self::B
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub enum Point<F: FieldOrder> {
    Affine {
        x: FieldElement<F>,
        y: FieldElement<F>,
    },
    Infinity,
}

impl<F: FieldOrder> Point<F> {
    fn add(&self, other: &Self, a: FieldElement<F>) -> Self {
        match self {
            Self::Affine { x: x1, y: y1 } => match other {
                Self::Affine { x: x2, y: y2 } => {
                    if x1 == x2 && y1 == y2 {
                        return self.double(a);
                    }
                    if x1 == x2 && y1 + y2 == FieldElement::ZERO {
                        Self::Infinity
                    } else {
                        let lambda = (y2 - y1) * (x2 - x1).inv();
                        let x3 = lambda * lambda - x1 - x2;
                        let y3 = lambda * (x1 - x3) - y1;
                        Self::Affine { x: x3, y: y3 }
                    }
                }
                Self::Infinity => *self,
            },
            Self::Infinity => *other,
        }
    }

    fn double(&self, a: FieldElement<F>) -> Self {
        match self {
            Self::Affine { x, y } => {
                if *y == FieldElement::ZERO {
                    return Self::Infinity;
                }
                let lambda = (FieldElement::THREE * (x * x) + a) * (FieldElement::TWO * y).inv();
                let x2 = lambda * lambda - FieldElement::TWO * x;
                let y2 = lambda * (x - x2) - y;
                Self::Affine { x: x2, y: y2 }
            }
            Self::Infinity => *self,
        }
    }

    pub fn is_infinity(&self) -> bool {
        matches!(self, Self::Infinity)
    }

    fn mul<G: FieldOrder>(&self, scalar: Scalar<G>, a: FieldElement<F>) -> Self {
        let mut result = Self::Infinity;
        for &limb in scalar.0.as_ref().iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                result = result.double(a);
                if (limb >> bit_idx) & 1 == 1 {
                    result = result.add(self, a);
                }
            }
        }
        result
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, std::hash::Hash)]
pub struct Scalar<F: FieldOrder>(F::Limbs);

impl<F: FieldOrder> Scalar<F> {
    pub const fn from_limbs(limbs: F::Limbs) -> Self {
        Self(limbs)
    }

    pub fn from_u64(x: u64) -> Self {
        Self(<F::Limbs as Limbs>::from_u64(x))
    }

    pub fn from_u128(n: u128) -> Self {
        let mut limbs = <F::Limbs as Limbs>::ZERO;
        {
            let s = limbs.as_mut();
            s[0] = n as u64;
            if s.len() >= 2 {
                s[1] = (n >> 64) as u64;
            }
        }
        Self(limbs)
    }
}

impl<F: FieldOrder<Limbs = [u64; 4]>> Scalar<F> {
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        Self([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::{Secp256k1FieldOrder as Fp, Secp256k1GroupOrder};

    type Fe = FieldElement<Fp>;
    type Pt = Point<Fp>;
    type Sc = Scalar<Secp256k1GroupOrder>;

    const CURVE: Secp256k1Curve = Secp256k1Curve;

    fn fe(limbs: [u64; 4]) -> Fe {
        Fe::from_limbs_unchecked(limbs)
    }

    fn generator() -> Pt {
        Pt::Affine {
            x: fe([
                0x59F2815B16F81798,
                0x029BFCDB2DCE28D9,
                0x55A06295CE870B07,
                0x79BE667EF9DCBBAC,
            ]),
            y: fe([
                0x9C47D08FFB10D4B8,
                0xFD17B448A6855419,
                0x5DA4FBFC0E1108A8,
                0x483ADA7726A3C465,
            ]),
        }
    }

    fn two_g() -> Pt {
        Pt::Affine {
            x: fe([
                0xABAC09B95C709EE5,
                0x5C778E4B8CEF3CA7,
                0x3045406E95C07CD8,
                0xC6047F9441ED7D6D,
            ]),
            y: fe([
                0x236431A950CFE52A,
                0xF7F632653266D0E1,
                0xA3C58419466CEAEE,
                0x1AE168FEA63DC339,
            ]),
        }
    }

    fn three_g() -> Pt {
        Pt::Affine {
            x: fe([
                0x8601F113BCE036F9,
                0xB531C845836F99B0,
                0x49344F85F89D5229,
                0xF9308A019258C310,
            ]),
            y: fe([
                0x6CB9FD7584B8E672,
                0x6500A99934C2231B,
                0x0FE337E62A37F356,
                0x388F7B0F632DE814,
            ]),
        }
    }

    fn neg(p: &Pt) -> Pt {
        match p {
            Pt::Affine { x, y } => Pt::Affine {
                x: *x,
                y: Fe::ZERO - *y,
            },
            Pt::Infinity => *p,
        }
    }

    fn infinity() -> Pt {
        Pt::Infinity
    }

    #[test]
    fn double_generator_matches_2g() {
        assert_eq!(CURVE.add(generator(), generator()), two_g());
    }

    #[test]
    fn add_g_plus_2g_matches_3g() {
        assert_eq!(CURVE.add(generator(), two_g()), three_g());
    }

    #[test]
    fn add_2g_plus_g_matches_3g() {
        assert_eq!(CURVE.add(two_g(), generator()), three_g());
    }

    #[test]
    fn add_infinity_right_identity() {
        let g = generator();
        assert_eq!(CURVE.add(g, infinity()), g);
    }

    #[test]
    fn add_infinity_left_identity() {
        let g = generator();
        assert_eq!(CURVE.add(infinity(), g), g);
    }

    #[test]
    fn add_point_and_negation_is_infinity() {
        let g = generator();
        assert!(CURVE.add(g, neg(&g)).is_infinity());
    }

    #[test]
    fn add_is_commutative() {
        let a = generator();
        let b = two_g();
        assert_eq!(CURVE.add(a, b), CURVE.add(b, a));
    }

    #[test]
    fn add_is_associative() {
        let a = generator();
        let b = two_g();
        let c = three_g();
        assert_eq!(CURVE.add(CURVE.add(a, b), c), CURVE.add(a, CURVE.add(b, c)));
    }

    #[test]
    fn infinity_plus_infinity_is_infinity() {
        assert!(CURVE.add(infinity(), infinity()).is_infinity());
    }

    #[test]
    fn mul_by_zero_is_infinity() {
        assert!(
            CURVE
                .multiply(Sc::from_u128(0), generator())
                .is_infinity()
        );
    }

    #[test]
    fn mul_by_one_is_identity() {
        let g = generator();
        assert_eq!(CURVE.multiply(Sc::from_u128(1), g), g);
    }

    #[test]
    fn mul_by_two_matches_double() {
        let g = generator();
        assert_eq!(CURVE.multiply(Sc::from_u128(2), g), CURVE.add(g, g));
    }

    #[test]
    fn mul_by_three_matches_3g() {
        assert_eq!(CURVE.multiply(Sc::from_u128(3), generator()), three_g());
    }

    #[test]
    fn mul_scalar_additivity() {
        let g = generator();
        let a = CURVE.multiply(Sc::from_u128(7), g);
        let b = CURVE.multiply(Sc::from_u128(11), g);
        let sum = CURVE.multiply(Sc::from_u128(18), g);
        assert_eq!(CURVE.add(a, b), sum);
    }

    #[test]
    fn mul_infinity_is_infinity() {
        assert!(
            CURVE
                .multiply(Sc::from_u128(12345), infinity())
                .is_infinity()
        );
    }

    #[test]
    fn struct_generator_matches_local_generator() {
        assert_eq!(Secp256k1Curve::GENERATOR, generator());
    }

    #[test]
    fn struct_generator_mul_by_one_is_itself() {
        assert_eq!(
            CURVE.multiply(Sc::from_u128(1), Secp256k1Curve::GENERATOR),
            Secp256k1Curve::GENERATOR
        );
    }

    #[test]
    fn struct_generator_mul_by_two_matches_2g() {
        assert_eq!(
            CURVE.multiply(Sc::from_u128(2), Secp256k1Curve::GENERATOR),
            two_g()
        );
    }

    #[test]
    fn struct_generator_mul_by_three_matches_3g() {
        assert_eq!(
            CURVE.multiply(Sc::from_u128(3), Secp256k1Curve::GENERATOR),
            three_g()
        );
    }

    #[test]
    fn struct_generator_mul_scalar_additivity() {
        let a = CURVE.multiply(Sc::from_u128(7), Secp256k1Curve::GENERATOR);
        let b = CURVE.multiply(Sc::from_u128(11), Secp256k1Curve::GENERATOR);
        let sum = CURVE.multiply(Sc::from_u128(18), Secp256k1Curve::GENERATOR);
        assert_eq!(CURVE.add(a, b), sum);
    }

    #[test]
    fn struct_generator_mul_by_group_order_is_infinity() {
        let n = Sc::from_bytes([
            0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC,
            0xAE, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);
        assert!(CURVE.multiply(n, Secp256k1Curve::GENERATOR).is_infinity());
    }

    #[test]
    fn mul_by_group_order_is_infinity() {
        // n = 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_BAAEDCE6_AF48A03B_BFD25E8C_D0364141
        // in little-endian byte order:
        let n = Sc::from_bytes([
            0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC,
            0xAE, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);
        assert!(CURVE.multiply(n, generator()).is_infinity());
    }

    #[test]
    fn j_invariant() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct E;
        impl Curve<Secp256k1GroupOrder> for E {
            fn a(&self) -> FieldElement<Secp256k1GroupOrder> {
                FieldElement::ONE
            }
            fn b(&self) -> FieldElement<Secp256k1GroupOrder> {
                FieldElement::ZERO
            }
        }
        assert_eq!(FieldElement::from_u64(1728), E.j_invariant());
    }
}

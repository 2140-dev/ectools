use core::fmt;
use core::marker::PhantomData;
use field::{FieldElement, FieldOrder};

pub trait Curve<F: FieldOrder>: fmt::Debug + Clone + Copy + PartialEq + Eq {
    /// y^2 = x^3 + Ax + B
    const A: FieldElement<F>;
    const B: FieldElement<F>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1Curve;

impl Secp256k1Curve {
    pub const GENERATOR: Point<field::Secp256k1FieldOrder, Self> = Point::Affine {
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

    pub fn point_from_scalar(scalar: Scalar) -> Point<field::Secp256k1FieldOrder, Self> {
        Self::GENERATOR.mul(scalar)
    }
}

impl Curve<field::Secp256k1FieldOrder> for Secp256k1Curve {
    const A: FieldElement<field::Secp256k1FieldOrder> = FieldElement::ZERO;
    const B: FieldElement<field::Secp256k1FieldOrder> = FieldElement::from_u64(7);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Infinity<F: FieldOrder, C: Curve<F>> {
    _m1: PhantomData<C>,
    _m2: PhantomData<F>,
}

impl<F: FieldOrder, C: Curve<F>> Infinity<F, C> {
    pub const fn new() -> Self {
        Self {
            _m1: PhantomData,
            _m2: PhantomData,
        }
    }
}

impl<F: FieldOrder, C: Curve<F>> Default for Infinity<F, C> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub enum Point<F: FieldOrder, EC: Curve<F>> {
    Affine {
        x: FieldElement<F>,
        y: FieldElement<F>,
    },
    Infinity(Infinity<F, EC>),
}

impl<F: FieldOrder, EC: Curve<F>> Point<F, EC> {
    pub fn add(&self, other: &Self) -> Self {
        match self {
            Self::Affine { x: x1, y: y1 } => match other {
                Self::Affine { x: x2, y: y2 } => {
                    if x1 == x2 && y1 == y2 {
                        return self.double();
                    }
                    if x1 == x2 && y1 + y2 == FieldElement::ZERO {
                        Self::Infinity(Infinity::new())
                    } else {
                        let lambda = (y2 - y1) * (x2 - x1).inv();
                        let x3 = lambda * lambda - x1 - x2;
                        let y3 = lambda * (x1 - x3) - y1;
                        Self::Affine { x: x3, y: y3 }
                    }
                }
                Self::Infinity(_) => *self,
            },
            Self::Infinity(_) => *other,
        }
    }

    pub fn double(&self) -> Self {
        match self {
            Self::Affine { x, y } => {
                if *y == FieldElement::ZERO {
                    return Self::Infinity(Infinity::new());
                }
                let lambda =
                    (FieldElement::THREE * (x * x) + EC::A) * (FieldElement::TWO * y).inv();
                let x2 = lambda * lambda - FieldElement::TWO * x;
                let y2 = lambda * (x - x2) - y;
                Self::Affine { x: x2, y: y2 }
            }
            Self::Infinity(_) => *self,
        }
    }

    pub fn is_infinity(&self) -> bool {
        matches!(self, Self::Infinity(_))
    }

    pub fn mul(&self, scalar: Scalar) -> Self {
        self.mul_le_bytes(scalar.0)
    }

    // pub fn mul_fe(&self, scalar: FieldElement<F>) -> Self {
    // self.mul_le_bytes(scalar.to_bytes_le())
    // }

    #[inline]
    fn mul_le_bytes(&self, bytes: [u8; 32]) -> Self {
        let mut result = Self::Infinity(Infinity::new());
        for byte in bytes.iter().rev() {
            for bit_idx in (0..u8::BITS).rev() {
                result = result.double();
                if (byte >> bit_idx) & 1 == 1 {
                    result = result.add(self);
                }
            }
        }
        result
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Scalar([u8; 32]);

impl Scalar {
    pub const fn from_u128(num: u128) -> Self {
        let le = num.to_le_bytes();
        let mut bytes = [0u8; 32];
        let mut i = 0;
        while i < 16 {
            bytes[i] = le[i];
            i += 1;
        }
        Self(bytes)
    }

    pub const fn from_bytes(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::Secp256k1FieldOrder as Fp;

    type Fe = FieldElement<Fp>;
    type Pt = Point<Fp, Secp256k1Curve>;

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
            Pt::Infinity(_) => *p,
        }
    }

    fn infinity() -> Pt {
        Pt::Infinity(Infinity::new())
    }

    #[test]
    fn double_generator_matches_2g() {
        assert_eq!(generator().double(), two_g());
    }

    #[test]
    fn add_g_plus_2g_matches_3g() {
        assert_eq!(generator().add(&two_g()), three_g());
    }

    #[test]
    fn add_2g_plus_g_matches_3g() {
        assert_eq!(two_g().add(&generator()), three_g());
    }

    #[test]
    fn add_same_point_reduces_to_double() {
        let g = generator();
        assert_eq!(g.add(&g), g.double());
    }

    #[test]
    fn add_infinity_right_identity() {
        let g = generator();
        assert_eq!(g.add(&infinity()), g);
    }

    #[test]
    fn add_infinity_left_identity() {
        let g = generator();
        assert_eq!(infinity().add(&g), g);
    }

    #[test]
    fn add_point_and_negation_is_infinity() {
        let g = generator();
        assert!(g.add(&neg(&g)).is_infinity());
    }

    #[test]
    fn add_is_commutative() {
        let a = generator();
        let b = two_g();
        assert_eq!(a.add(&b), b.add(&a));
    }

    #[test]
    fn add_is_associative() {
        let a = generator();
        let b = two_g();
        let c = three_g();
        assert_eq!(a.add(&b).add(&c), a.add(&b.add(&c)));
    }

    #[test]
    fn double_infinity_is_infinity() {
        assert!(infinity().double().is_infinity());
    }

    #[test]
    fn infinity_plus_infinity_is_infinity() {
        assert!(infinity().add(&infinity()).is_infinity());
    }

    #[test]
    fn mul_by_zero_is_infinity() {
        assert!(generator().mul(Scalar::from_u128(0)).is_infinity());
    }

    #[test]
    fn mul_by_one_is_identity() {
        let g = generator();
        assert_eq!(g.mul(Scalar::from_u128(1)), g);
    }

    #[test]
    fn mul_by_two_matches_double() {
        let g = generator();
        assert_eq!(g.mul(Scalar::from_u128(2)), g.double());
    }

    #[test]
    fn mul_by_three_matches_3g() {
        assert_eq!(generator().mul(Scalar::from_u128(3)), three_g());
    }

    #[test]
    fn mul_scalar_additivity() {
        let g = generator();
        let a = g.mul(Scalar::from_u128(7));
        let b = g.mul(Scalar::from_u128(11));
        let sum = g.mul(Scalar::from_u128(18));
        assert_eq!(a.add(&b), sum);
    }

    #[test]
    fn mul_infinity_is_infinity() {
        assert!(infinity().mul(Scalar::from_u128(12345)).is_infinity());
    }

    #[test]
    fn struct_generator_matches_local_generator() {
        assert_eq!(Secp256k1Curve::GENERATOR, generator());
    }

    #[test]
    fn struct_generator_mul_by_one_is_itself() {
        assert_eq!(
            Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(1)),
            Secp256k1Curve::GENERATOR
        );
    }

    #[test]
    fn struct_generator_mul_by_two_matches_2g() {
        assert_eq!(Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(2)), two_g());
    }

    #[test]
    fn struct_generator_mul_by_three_matches_3g() {
        assert_eq!(
            Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(3)),
            three_g()
        );
    }

    #[test]
    fn struct_generator_mul_scalar_additivity() {
        let a = Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(7));
        let b = Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(11));
        let sum = Secp256k1Curve::GENERATOR.mul(Scalar::from_u128(18));
        assert_eq!(a.add(&b), sum);
    }

    #[test]
    fn struct_generator_mul_by_group_order_is_infinity() {
        let n = Scalar::from_bytes([
            0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC,
            0xAE, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);
        assert!(Secp256k1Curve::GENERATOR.mul(n).is_infinity());
    }

    #[test]
    fn mul_by_group_order_is_infinity() {
        // n = 0xFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFE_BAAEDCE6_AF48A03B_BFD25E8C_D0364141
        // in little-endian byte order:
        let n = Scalar::from_bytes([
            0x41, 0x41, 0x36, 0xD0, 0x8C, 0x5E, 0xD2, 0xBF, 0x3B, 0xA0, 0x48, 0xAF, 0xE6, 0xDC,
            0xAE, 0xBA, 0xFE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);
        assert!(generator().mul(n).is_infinity());
    }
}

use core::fmt;
use core::hash::{Hash, Hasher};
use field::{FieldElement, FieldOrder, Limbs, Secp256k1FieldOrder, Secp256k1GroupOrder, Sqrt3Mod4};

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

    fn lift(&self, x: FieldElement<F>) -> Option<Point<F>>
    where
        F: Sqrt3Mod4,
    {
        let rhs = x * x * x + self.a() * x + self.b();
        let y = rhs.sqrt();
        if y * y == rhs {
            Some(Point::from_affine(x, y))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1Curve;

impl Secp256k1Curve {
    pub const A: FieldElement<Secp256k1FieldOrder> = FieldElement::ZERO;
    pub const B: FieldElement<Secp256k1FieldOrder> =
        FieldElement::from_limbs_unchecked([7, 0, 0, 0]);

    pub const GENERATOR: Point<Secp256k1FieldOrder> = Point::from_affine(
        FieldElement::from_limbs_unchecked([
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ]),
        FieldElement::from_limbs_unchecked([
            0x9C47D08FFB10D4B8,
            0xFD17B448A6855419,
            0x5DA4FBFC0E1108A8,
            0x483ADA7726A3C465,
        ]),
    );

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

#[derive(Debug, Clone, Copy)]
pub struct Point<F: FieldOrder> {
    x: FieldElement<F>,
    y: FieldElement<F>,
    z: FieldElement<F>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub enum PointRepresentation<F: FieldOrder> {
    Affine {
        x: FieldElement<F>,
        y: FieldElement<F>,
    },
    Infinity,
}

impl<F: FieldOrder> Point<F> {
    pub const INFINITY: Self = Self {
        x: FieldElement::ONE,
        y: FieldElement::ONE,
        z: FieldElement::ZERO,
    };

    pub const fn from_affine(x: FieldElement<F>, y: FieldElement<F>) -> Self {
        Self {
            x,
            y,
            z: FieldElement::ONE,
        }
    }

    pub fn representation(&self) -> PointRepresentation<F> {
        if self.z == FieldElement::ZERO {
            return PointRepresentation::Infinity;
        }
        let z_inv = self.z.inv();
        let z_inv_sq = z_inv * z_inv;
        let z_inv_cu = z_inv_sq * z_inv;
        PointRepresentation::Affine {
            x: self.x * z_inv_sq,
            y: self.y * z_inv_cu,
        }
    }

    pub fn is_infinity(&self) -> bool {
        self.z == FieldElement::ZERO
    }

    pub fn neg(&self) -> Self {
        Self {
            x: self.x,
            y: FieldElement::ZERO - self.y,
            z: self.z,
        }
    }

    fn double(&self, a: FieldElement<F>) -> Self {
        if self.z == FieldElement::ZERO {
            return *self;
        }
        let xx = self.x * self.x;
        let yy = self.y * self.y;
        let yyyy = yy * yy;
        let zz = self.z * self.z;
        let x_plus_yy = self.x + yy;
        let s_half = x_plus_yy * x_plus_yy - xx - yyyy;
        let s = s_half + s_half;
        let three_xx = xx + xx + xx;
        let m = three_xx + a * zz * zz;
        let two_s = s + s;
        let t = m * m - two_s;
        let x3 = t;
        let two_yyyy = yyyy + yyyy;
        let four_yyyy = two_yyyy + two_yyyy;
        let eight_yyyy = four_yyyy + four_yyyy;
        let y3 = m * (s - t) - eight_yyyy;
        let y_plus_z = self.y + self.z;
        let z3 = y_plus_z * y_plus_z - yy - zz;
        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    fn add(&self, other: &Self, a: FieldElement<F>) -> Self {
        if self.z == FieldElement::ZERO {
            return *other;
        }
        if other.z == FieldElement::ZERO {
            return *self;
        }
        let z1z1 = self.z * self.z;
        let z2z2 = other.z * other.z;
        let u1 = self.x * z2z2;
        let u2 = other.x * z1z1;
        let s1 = self.y * other.z * z2z2;
        let s2 = other.y * self.z * z1z1;
        let h = u2 - u1;
        let r_half = s2 - s1;
        if h == FieldElement::ZERO {
            if r_half == FieldElement::ZERO {
                return self.double(a);
            } else {
                return Self::INFINITY;
            }
        }
        let two_h = h + h;
        let i = two_h * two_h;
        let j = h * i;
        let r = r_half + r_half;
        let v = u1 * i;
        let two_v = v + v;
        let x3 = r * r - j - two_v;
        let s1_j = s1 * j;
        let two_s1_j = s1_j + s1_j;
        let y3 = r * (v - x3) - two_s1_j;
        let z1_plus_z2 = self.z + other.z;
        let z3 = (z1_plus_z2 * z1_plus_z2 - z1z1 - z2z2) * h;
        Self {
            x: x3,
            y: y3,
            z: z3,
        }
    }

    fn mul<G: FieldOrder>(&self, scalar: Scalar<G>, a: FieldElement<F>) -> Self {
        let mut result = Self::INFINITY;
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

impl<F: FieldOrder> PartialEq for Point<F> {
    fn eq(&self, other: &Self) -> bool {
        let z1_zero = self.z == FieldElement::ZERO;
        let z2_zero = other.z == FieldElement::ZERO;
        if z1_zero || z2_zero {
            return z1_zero && z2_zero;
        }
        let z1_sq = self.z * self.z;
        let z2_sq = other.z * other.z;
        let z1_cu = z1_sq * self.z;
        let z2_cu = z2_sq * other.z;
        (self.x * z2_sq == other.x * z1_sq) && (self.y * z2_cu == other.y * z1_cu)
    }
}

impl<F: FieldOrder> Eq for Point<F> {}

impl<F: FieldOrder + Hash> Hash for Point<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.representation().hash(state);
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
        Pt::from_affine(
            fe([
                0x59F2815B16F81798,
                0x029BFCDB2DCE28D9,
                0x55A06295CE870B07,
                0x79BE667EF9DCBBAC,
            ]),
            fe([
                0x9C47D08FFB10D4B8,
                0xFD17B448A6855419,
                0x5DA4FBFC0E1108A8,
                0x483ADA7726A3C465,
            ]),
        )
    }

    fn two_g() -> Pt {
        Pt::from_affine(
            fe([
                0xABAC09B95C709EE5,
                0x5C778E4B8CEF3CA7,
                0x3045406E95C07CD8,
                0xC6047F9441ED7D6D,
            ]),
            fe([
                0x236431A950CFE52A,
                0xF7F632653266D0E1,
                0xA3C58419466CEAEE,
                0x1AE168FEA63DC339,
            ]),
        )
    }

    fn three_g() -> Pt {
        Pt::from_affine(
            fe([
                0x8601F113BCE036F9,
                0xB531C845836F99B0,
                0x49344F85F89D5229,
                0xF9308A019258C310,
            ]),
            fe([
                0x6CB9FD7584B8E672,
                0x6500A99934C2231B,
                0x0FE337E62A37F356,
                0x388F7B0F632DE814,
            ]),
        )
    }

    fn infinity() -> Pt {
        Pt::INFINITY
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
        assert!(CURVE.add(g, g.neg()).is_infinity());
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
        assert!(CURVE.multiply(Sc::from_u128(0), generator()).is_infinity());
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

    #[test]
    fn representation_of_infinity_is_infinity_variant() {
        assert_eq!(Pt::INFINITY.representation(), PointRepresentation::Infinity);
    }

    #[test]
    fn representation_of_affine_recovers_coords() {
        let g = generator();
        let g_x = fe([
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ]);
        let g_y = fe([
            0x9C47D08FFB10D4B8,
            0xFD17B448A6855419,
            0x5DA4FBFC0E1108A8,
            0x483ADA7726A3C465,
        ]);
        assert_eq!(
            g.representation(),
            PointRepresentation::Affine { x: g_x, y: g_y }
        );
    }

    #[test]
    fn representation_after_arithmetic_normalizes() {
        let two_g_via_add = CURVE.add(generator(), generator());
        let g_x = fe([
            0xABAC09B95C709EE5,
            0x5C778E4B8CEF3CA7,
            0x3045406E95C07CD8,
            0xC6047F9441ED7D6D,
        ]);
        let g_y = fe([
            0x236431A950CFE52A,
            0xF7F632653266D0E1,
            0xA3C58419466CEAEE,
            0x1AE168FEA63DC339,
        ]);
        assert_eq!(
            two_g_via_add.representation(),
            PointRepresentation::Affine { x: g_x, y: g_y }
        );
    }

    #[test]
    fn lift_recovers_generator() {
        let g_x = fe([
            0x59F2815B16F81798,
            0x029BFCDB2DCE28D9,
            0x55A06295CE870B07,
            0x79BE667EF9DCBBAC,
        ]);
        let lifted = CURVE.lift(g_x).expect("generator x is on-curve");
        match lifted.representation() {
            PointRepresentation::Affine { x, y } => {
                assert_eq!(x, g_x);
                let g_y = fe([
                    0x9C47D08FFB10D4B8,
                    0xFD17B448A6855419,
                    0x5DA4FBFC0E1108A8,
                    0x483ADA7726A3C465,
                ]);
                assert!(y == g_y || y == Fe::ZERO - g_y);
            }
            PointRepresentation::Infinity => panic!("expected affine"),
        }
    }

    #[test]
    fn lift_none_off_curve() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct E;
        impl Curve<Fp> for E {
            fn a(&self) -> Fe {
                Fe::ONE
            }
            fn b(&self) -> Fe {
                Fe::ZERO - Fe::TWO
            }
        }
        assert!(E.lift(Fe::ZERO).is_none());
    }

    #[test]
    fn lift_two_torsion() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        struct E;
        impl Curve<Fp> for E {
            fn a(&self) -> Fe {
                Fe::ONE
            }
            fn b(&self) -> Fe {
                Fe::ZERO - Fe::TWO
            }
        }
        let p = E.lift(Fe::ONE).expect("(1, 0) is on E");
        assert_eq!(
            p.representation(),
            PointRepresentation::Affine {
                x: Fe::ONE,
                y: Fe::ZERO
            }
        );
    }
}

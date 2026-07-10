use core::fmt;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::{Csidh512FieldOrder, Field, FieldElement, Sqrt3Mod4};

pub trait ExtensionField: fmt::Debug + Clone + Copy + PartialEq + Eq {
    type Base: Field;
    fn non_residue() -> FieldElement<Self::Base>;

    #[inline]
    fn mul_by_non_residue(x: FieldElement<Self::Base>) -> FieldElement<Self::Base> {
        x * Self::non_residue()
    }
}

pub trait NonResidueMinusOne: ExtensionField {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct ExtensionFieldElement<E: ExtensionField> {
    c0: FieldElement<E::Base>,
    c1: FieldElement<E::Base>,
    _marker: PhantomData<E>,
}

impl<E: ExtensionField> ExtensionFieldElement<E> {
    pub fn new(c0: FieldElement<E::Base>, c1: FieldElement<E::Base>) -> Self {
        Self {
            c0,
            c1,
            _marker: PhantomData,
        }
    }

    pub fn zero() -> Self {
        Self::new(FieldElement::zero(), FieldElement::zero())
    }

    pub fn one() -> Self {
        Self::new(FieldElement::one(), FieldElement::zero())
    }

    pub fn from_base(x: FieldElement<E::Base>) -> Self {
        Self::new(x, FieldElement::zero())
    }

    pub fn c0(&self) -> FieldElement<E::Base> {
        self.c0
    }

    pub fn c1(&self) -> FieldElement<E::Base> {
        self.c1
    }

    pub fn add(&self, rhs: &Self) -> Self {
        Self::new(self.c0 + rhs.c0, self.c1 + rhs.c1)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self::new(self.c0 - rhs.c0, self.c1 - rhs.c1)
    }

    pub fn neg(&self) -> Self {
        let zero = FieldElement::zero();
        Self::new(zero - self.c0, zero - self.c1)
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let t0 = self.c0 * rhs.c0;
        let t1 = self.c1 * rhs.c1;
        let s = (self.c0 + self.c1) * (rhs.c0 + rhs.c1);
        let c1 = s - t0 - t1;
        let c0 = t0 + E::mul_by_non_residue(t1);
        Self::new(c0, c1)
    }

    pub fn sqr(&self) -> Self {
        let t0 = self.c0 * self.c0;
        let t1 = self.c1 * self.c1;
        let ab = self.c0 * self.c1;
        let c0 = t0 + E::mul_by_non_residue(t1);
        let c1 = ab + ab;
        Self::new(c0, c1)
    }

    pub fn conjugate(&self) -> Self {
        Self::new(self.c0, FieldElement::zero() - self.c1)
    }

    pub fn frobenius(&self) -> Self {
        self.conjugate()
    }

    pub fn inv(&self) -> Self {
        let norm = self.c0 * self.c0 - E::mul_by_non_residue(self.c1 * self.c1);
        let norm_inv = norm.inv();
        Self::new(
            self.c0 * norm_inv,
            (FieldElement::zero() - self.c1) * norm_inv,
        )
    }

    pub fn pow(&self, exp: &[u64]) -> Self {
        let mut result = Self::one();
        for &limb in exp.iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                result = result.sqr();
                if (limb >> bit_idx) & 1 == 1 {
                    result = result.mul(self);
                }
            }
        }
        result
    }

    pub fn scale(&self, s: FieldElement<E::Base>) -> Self {
        Self::new(self.c0 * s, self.c1 * s)
    }
}

impl<E: NonResidueMinusOne> ExtensionFieldElement<E>
where
    E::Base: Sqrt3Mod4,
{
    pub fn sqrt(&self) -> Self {
        let a = self.c0;
        let b = self.c1;
        let zero = FieldElement::zero();

        if b == zero {
            let sa = a.sqrt();
            if sa * sa == a {
                return Self::new(sa, zero);
            }
            let s = (zero - a).sqrt();
            return Self::new(zero, s);
        }

        let n = (a * a + b * b).sqrt();
        let two_inv = FieldElement::two().inv();
        let mut delta = (a + n) * two_inv;
        let mut x = delta.sqrt();
        if x * x != delta {
            delta = (a - n) * two_inv;
            x = delta.sqrt();
        }
        let two_x_inv = (x + x).inv();
        let y = b * two_x_inv;
        Self::new(x, y)
    }
}

impl<E: ExtensionField> Add for ExtensionFieldElement<E> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        ExtensionFieldElement::<E>::add(&self, &rhs)
    }
}

impl<E: ExtensionField> Add<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn add(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::add(&self, rhs)
    }
}

impl<E: ExtensionField> Add<ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn add(self, rhs: ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::add(self, &rhs)
    }
}

impl<E: ExtensionField> Add<&ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn add(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::add(self, rhs)
    }
}

impl<E: ExtensionField> AddAssign for ExtensionFieldElement<E> {
    fn add_assign(&mut self, rhs: Self) {
        *self = ExtensionFieldElement::<E>::add(self, &rhs);
    }
}

impl<E: ExtensionField> AddAssign<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    fn add_assign(&mut self, rhs: &ExtensionFieldElement<E>) {
        *self = ExtensionFieldElement::<E>::add(self, rhs);
    }
}

impl<E: ExtensionField> Sub for ExtensionFieldElement<E> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        ExtensionFieldElement::<E>::sub(&self, &rhs)
    }
}

impl<E: ExtensionField> Sub<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn sub(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::sub(&self, rhs)
    }
}

impl<E: ExtensionField> Sub<ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn sub(self, rhs: ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::sub(self, &rhs)
    }
}

impl<E: ExtensionField> Sub<&ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn sub(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::sub(self, rhs)
    }
}

impl<E: ExtensionField> SubAssign for ExtensionFieldElement<E> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = ExtensionFieldElement::<E>::sub(self, &rhs);
    }
}

impl<E: ExtensionField> SubAssign<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    fn sub_assign(&mut self, rhs: &ExtensionFieldElement<E>) {
        *self = ExtensionFieldElement::<E>::sub(self, rhs);
    }
}

impl<E: ExtensionField> Mul for ExtensionFieldElement<E> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        ExtensionFieldElement::<E>::mul(&self, &rhs)
    }
}

impl<E: ExtensionField> Mul<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn mul(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::mul(&self, rhs)
    }
}

impl<E: ExtensionField> Mul<ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn mul(self, rhs: ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::mul(self, &rhs)
    }
}

impl<E: ExtensionField> Mul<&ExtensionFieldElement<E>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn mul(self, rhs: &ExtensionFieldElement<E>) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::mul(self, rhs)
    }
}

impl<E: ExtensionField> MulAssign for ExtensionFieldElement<E> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = ExtensionFieldElement::<E>::mul(self, &rhs);
    }
}

impl<E: ExtensionField> MulAssign<&ExtensionFieldElement<E>> for ExtensionFieldElement<E> {
    fn mul_assign(&mut self, rhs: &ExtensionFieldElement<E>) {
        *self = ExtensionFieldElement::<E>::mul(self, rhs);
    }
}

impl<E: ExtensionField> Mul<FieldElement<E::Base>> for ExtensionFieldElement<E> {
    type Output = Self;
    fn mul(self, rhs: FieldElement<E::Base>) -> Self {
        self.scale(rhs)
    }
}

impl<E: ExtensionField> Mul<FieldElement<E::Base>> for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn mul(self, rhs: FieldElement<E::Base>) -> ExtensionFieldElement<E> {
        self.scale(rhs)
    }
}

impl<E: ExtensionField> Neg for ExtensionFieldElement<E> {
    type Output = Self;
    fn neg(self) -> Self {
        ExtensionFieldElement::<E>::neg(&self)
    }
}

impl<E: ExtensionField> Neg for &ExtensionFieldElement<E> {
    type Output = ExtensionFieldElement<E>;
    fn neg(self) -> ExtensionFieldElement<E> {
        ExtensionFieldElement::<E>::neg(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Csidh512Fp2;

impl ExtensionField for Csidh512Fp2 {
    type Base = Csidh512FieldOrder;

    fn non_residue() -> FieldElement<Csidh512FieldOrder> {
        FieldElement::zero() - FieldElement::one()
    }

    #[inline]
    fn mul_by_non_residue(x: FieldElement<Csidh512FieldOrder>) -> FieldElement<Csidh512FieldOrder> {
        FieldElement::zero() - x
    }
}

impl NonResidueMinusOne for Csidh512Fp2 {}

#[cfg(test)]
mod tests {
    use super::*;

    type Fp = FieldElement<Csidh512FieldOrder>;
    type F2 = ExtensionFieldElement<Csidh512Fp2>;

    fn i() -> F2 {
        F2::new(Fp::zero(), Fp::one())
    }

    fn fe(x: u64) -> Fp {
        Fp::from_u64(x)
    }

    fn el(a: u64, b: u64) -> F2 {
        F2::new(fe(a), fe(b))
    }

    #[test]
    fn i_squared_is_neg_one() {
        let i2 = i() * i();
        assert_eq!(i2, F2::new(Fp::zero() - Fp::one(), Fp::zero()));
    }

    #[test]
    fn add_componentwise() {
        let a = el(3, 5);
        let b = el(7, 11);
        assert_eq!(a + b, el(10, 16));
    }

    #[test]
    fn sub_componentwise() {
        let a = el(10, 20);
        let b = el(3, 5);
        assert_eq!(a - b, el(7, 15));
    }

    #[test]
    fn neg_negates_both_coords() {
        let a = el(3, 5);
        assert_eq!(a + (-a), F2::zero());
    }

    #[test]
    fn mul_matches_definition() {
        let a = el(3, 5);
        let b = el(7, 11);
        let expected = F2::new(
            fe(3) * fe(7) - fe(5) * fe(11),
            fe(3) * fe(11) + fe(5) * fe(7),
        );
        assert_eq!(a * b, expected);
    }

    #[test]
    fn mul_one_is_identity() {
        let a = el(12345, 67890);
        assert_eq!(a * F2::one(), a);
        assert_eq!(F2::one() * a, a);
    }

    #[test]
    fn mul_zero_is_zero() {
        let a = el(12345, 67890);
        assert_eq!(a * F2::zero(), F2::zero());
    }

    #[test]
    fn mul_commutative() {
        let a = F2::new(
            Fp::from_limbs_unchecked([0x1234, 0x5678, 0xABCD, 0, 0, 0, 0, 0]),
            Fp::from_limbs_unchecked([0xF00D, 0xBEEF, 0, 0, 0, 0, 0, 0]),
        );
        let b = F2::new(
            Fp::from_limbs_unchecked([0xAAAA, 0xBBBB, 0, 7, 0, 0, 0, 0]),
            Fp::from_limbs_unchecked([13, 17, 19, 0, 0, 0, 0, 0]),
        );
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn sqr_matches_mul_self() {
        let a = el(1234567, 7654321);
        assert_eq!(a.sqr(), a * a);
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(F2::one().inv(), F2::one());
    }

    #[test]
    fn x_times_inv_x_is_one() {
        let a = el(3, 5);
        assert_eq!(a * a.inv(), F2::one());
    }

    #[test]
    fn x_times_inv_x_is_one_multilimb() {
        let a = F2::new(
            Fp::from_limbs_unchecked([0xDEADBEEF, 0xABCD, 0x1234, 0x5678, 0, 0, 0, 0]),
            Fp::from_limbs_unchecked([0xCAFEF00D, 0x9999, 0, 0x1111, 0, 0, 0, 0]),
        );
        assert_eq!(a * a.inv(), F2::one());
    }

    #[test]
    fn inv_of_pure_imaginary() {
        let a = i();
        assert_eq!(a * a.inv(), F2::one());
    }

    #[test]
    fn conjugate_involution() {
        let a = el(42, 99);
        assert_eq!(a.conjugate().conjugate(), a);
    }

    #[test]
    fn conjugate_is_homomorphism() {
        let a = el(3, 5);
        let b = el(7, 11);
        assert_eq!((a * b).conjugate(), a.conjugate() * b.conjugate());
    }

    #[test]
    fn conjugate_flips_imag_sign() {
        let a = el(3, 5);
        assert_eq!(a.conjugate(), F2::new(fe(3), Fp::zero() - fe(5)));
    }

    #[test]
    fn pow_zero_is_one() {
        let a = el(42, 17);
        assert_eq!(a.pow(&[]), F2::one());
        assert_eq!(a.pow(&[0]), F2::one());
    }

    #[test]
    fn pow_one_is_identity() {
        let a = el(42, 17);
        assert_eq!(a.pow(&[1]), a);
    }

    #[test]
    fn pow_two_equals_square() {
        let a = el(42, 17);
        assert_eq!(a.pow(&[2]), a * a);
    }

    #[test]
    fn scale_by_base() {
        let a = el(3, 5);
        let s = fe(4);
        assert_eq!(a.scale(s), el(12, 20));
        assert_eq!(a * s, el(12, 20));
    }

    #[test]
    fn sqrt_of_zero_is_zero() {
        assert_eq!(F2::zero().sqrt(), F2::zero());
    }

    #[test]
    fn sqrt_of_one_squares_to_one() {
        let r = F2::one().sqrt();
        assert_eq!(r * r, F2::one());
    }

    #[test]
    fn sqrt_of_pure_real_square() {
        let x = el(7, 0);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_pure_imag_square() {
        let x = el(0, 7);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_mixed_square_roundtrips() {
        let x = el(3, 5);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_multilimb_square_roundtrips() {
        let x = F2::new(
            Fp::from_limbs_unchecked([
                0x0123456789ABCDEF,
                0xFEDCBA9876543210,
                0x1111222233334444,
                0x5555666677778888,
                0,
                0,
                0,
                0,
            ]),
            Fp::from_limbs_unchecked([0xDEADBEEFCAFEF00D, 0x9999AAAABBBBCCCC, 0, 0, 0, 0, 0, 0]),
        );
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }
}

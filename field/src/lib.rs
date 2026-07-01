use core::fmt;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

pub trait PrimeModulus: fmt::Debug + Clone + Copy {
    const MODULUS: [u64; 4];
}

#[derive(Debug, Clone, Copy)]
pub struct Secp256k1;

impl PrimeModulus for Secp256k1 {
    const MODULUS: [u64; 4] = [
        0xFFFFFFFEFFFFFC2F,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
    ];
}

#[derive(Debug, Clone, Copy)]
pub struct FieldElement<P: PrimeModulus> {
    limbs: [u64; 4],
    _marker: PhantomData<P>,
}

impl<P: PrimeModulus> FieldElement<P> {
    pub const ONE: Self = Self {
        limbs: [1, 0, 0, 0],
        _marker: PhantomData,
    };

    pub fn from_u64(small: u64) -> Self {
        Self {
            limbs: [small, 0, 0, 0],
            _marker: PhantomData,
        }
    }

    pub fn from_limbs_unchecked(limbs: [u64; 4]) -> Self {
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    pub fn from_bytes_unchecked(bytes: [u8; 32]) -> Self {
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];
        Self {
            limbs,
            _marker: PhantomData,
        }
    }
}

impl<P: PrimeModulus> FieldElement<P> {
    pub fn add(&self, rhs: &Self) -> Self {
        let (s0, c) = self.limbs[0].carrying_add(rhs.limbs[0], false);
        let (s1, c) = self.limbs[1].carrying_add(rhs.limbs[1], c);
        let (s2, c) = self.limbs[2].carrying_add(rhs.limbs[2], c);
        let (s3, carry) = self.limbs[3].carrying_add(rhs.limbs[3], c);

        let (d0, b) = s0.borrowing_sub(P::MODULUS[0], false);
        let (d1, b) = s1.borrowing_sub(P::MODULUS[1], b);
        let (d2, b) = s2.borrowing_sub(P::MODULUS[2], b);
        let (d3, borrow) = s3.borrowing_sub(P::MODULUS[3], b);

        let limbs = if carry || !borrow {
            [d0, d1, d2, d3]
        } else {
            [s0, s1, s2, s3]
        };
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let (d0, b) = self.limbs[0].borrowing_sub(rhs.limbs[0], false);
        let (d1, b) = self.limbs[1].borrowing_sub(rhs.limbs[1], b);
        let (d2, b) = self.limbs[2].borrowing_sub(rhs.limbs[2], b);
        let (d3, borrow) = self.limbs[3].borrowing_sub(rhs.limbs[3], b);

        let limbs = if borrow {
            let (r0, c) = d0.carrying_add(P::MODULUS[0], false);
            let (r1, c) = d1.carrying_add(P::MODULUS[1], c);
            let (r2, c) = d2.carrying_add(P::MODULUS[2], c);
            let (r3, _) = d3.carrying_add(P::MODULUS[3], c);
            [r0, r1, r2, r3]
        } else {
            [d0, d1, d2, d3]
        };
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn mul(&self, rhs: &Self) -> Self {
        let wide = wide_mul(&self.limbs, &rhs.limbs);
        let limbs = reduce_wide::<P>(wide);
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    pub fn pow(&self, exp: [u64; 4]) -> Self {
        let mut result = Self::ONE;
        for limb in exp.into_iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                result = result.mul(&result);
                if (limb >> bit_idx) & 1 == 1 {
                    result = result.mul(self);
                }
            }
        }
        result
    }

    pub fn inv(&self) -> Self {
        self.pow([
            P::MODULUS[0].wrapping_sub(2),
            P::MODULUS[1],
            P::MODULUS[2],
            P::MODULUS[3],
        ])
    }
}

#[inline]
fn wide_mul(a: &[u64; 4], b: &[u64; 4]) -> [u64; 8] {
    let mut t = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u64;
        for j in 0..4 {
            let (lo, hi) = a[i].carrying_mul_add(b[j], t[i + j], carry);
            t[i + j] = lo;
            carry = hi;
        }
        t[i + 4] = carry;
    }
    t
}

#[inline]
fn ge_modulus<P: PrimeModulus>(x: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if x[i] != P::MODULUS[i] {
            return x[i] > P::MODULUS[i];
        }
    }
    true
}

#[inline]
fn reduce_wide<P: PrimeModulus>(x: [u64; 8]) -> [u64; 4] {
    let mut r = [0u64; 4];
    for bit_idx in (0..512).rev() {
        let top = r[3] >> 63;
        r[3] = (r[3] << 1) | (r[2] >> 63);
        r[2] = (r[2] << 1) | (r[1] >> 63);
        r[1] = (r[1] << 1) | (r[0] >> 63);
        r[0] = (r[0] << 1) | ((x[bit_idx / 64] >> (bit_idx % 64)) & 1);

        if top == 1 || ge_modulus::<P>(&r) {
            let (d0, b) = r[0].borrowing_sub(P::MODULUS[0], false);
            let (d1, b) = r[1].borrowing_sub(P::MODULUS[1], b);
            let (d2, b) = r[2].borrowing_sub(P::MODULUS[2], b);
            let (d3, _) = r[3].borrowing_sub(P::MODULUS[3], b);
            r = [d0, d1, d2, d3];
        }
    }
    r
}

impl<P: PrimeModulus> Add for FieldElement<P> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        FieldElement::<P>::add(&self, &rhs)
    }
}

impl<P: PrimeModulus> Add<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(&self, rhs)
    }
}

impl<P: PrimeModulus> Add<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, &rhs)
    }
}

impl<P: PrimeModulus> Add<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, rhs)
    }
}

impl<P: PrimeModulus> AddAssign for FieldElement<P> {
    fn add_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::add(self, &rhs);
    }
}

impl<P: PrimeModulus> AddAssign<&FieldElement<P>> for FieldElement<P> {
    fn add_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::add(self, rhs);
    }
}

impl<P: PrimeModulus> Sub for FieldElement<P> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        FieldElement::<P>::sub(&self, &rhs)
    }
}

impl<P: PrimeModulus> Sub<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(&self, rhs)
    }
}

impl<P: PrimeModulus> Sub<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, &rhs)
    }
}

impl<P: PrimeModulus> Sub<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, rhs)
    }
}

impl<P: PrimeModulus> SubAssign for FieldElement<P> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::sub(self, &rhs);
    }
}

impl<P: PrimeModulus> SubAssign<&FieldElement<P>> for FieldElement<P> {
    fn sub_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::sub(self, rhs);
    }
}

impl<P: PrimeModulus> Mul for FieldElement<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        FieldElement::<P>::mul(&self, &rhs)
    }
}

impl<P: PrimeModulus> Mul<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(&self, rhs)
    }
}

impl<P: PrimeModulus> Mul<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, &rhs)
    }
}

impl<P: PrimeModulus> Mul<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, rhs)
    }
}

impl<P: PrimeModulus> MulAssign for FieldElement<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::mul(self, &rhs);
    }
}

impl<P: PrimeModulus> MulAssign<&FieldElement<P>> for FieldElement<P> {
    fn mul_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::mul(self, rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Fp = FieldElement<Secp256k1>;
    const P: [u64; 4] = Secp256k1::MODULUS;

    fn p_minus(n: u64) -> [u64; 4] {
        [P[0].wrapping_sub(n), P[1], P[2], P[3]]
    }

    #[test]
    fn add_zero_plus_zero() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 0, 0, 0]);
    }

    #[test]
    fn add_one_plus_one() {
        let a = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [2, 0, 0, 0]);
    }

    #[test]
    fn add_p_minus_one_plus_one_wraps_to_zero() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 0, 0, 0]);
    }

    #[test]
    fn add_overflows_field_order() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((a + b).limbs, p_minus(2));
    }

    #[test]
    fn add_assign_value() {
        let mut a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        a += b;
        assert_eq!(a.limbs, [12, 0, 0, 0]);
    }

    #[test]
    fn add_assign_ref() {
        let mut a = Fp::from_limbs_unchecked(p_minus(3));
        let b = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        a += &b;
        assert_eq!(a.limbs, [2, 0, 0, 0]);
    }

    #[test]
    fn add_carry_limb0_to_limb1() {
        let a = Fp::from_limbs_unchecked([u64::MAX, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 1, 0, 0]);
    }

    #[test]
    fn add_carry_limb1_to_limb2() {
        let a = Fp::from_limbs_unchecked([0, u64::MAX, 0, 0]);
        let b = Fp::from_limbs_unchecked([0, 1, 0, 0]);
        assert_eq!((a + b).limbs, [0, 0, 1, 0]);
    }

    #[test]
    fn add_carry_chain_across_all_limbs() {
        let a = Fp::from_limbs_unchecked([u64::MAX, u64::MAX, u64::MAX, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 0, 0, 1]);
    }

    #[test]
    fn add_intra_limb_carry_with_nonzero_high() {
        let a = Fp::from_limbs_unchecked([u64::MAX, 5, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 6, 0, 0]);
    }

    #[test]
    fn add_carry_to_high_limb_below_modulus() {
        let a = Fp::from_limbs_unchecked([u64::MAX, u64::MAX, u64::MAX, 0x7FFFFFFFFFFFFFFF]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b).limbs, [0, 0, 0, 0x8000000000000000]);
    }

    #[test]
    fn sub_simple() {
        let a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        assert_eq!((a - b).limbs, [2, 0, 0, 0]);
    }

    #[test]
    fn sub_self_is_zero() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((a - a).limbs, [0, 0, 0, 0]);
    }

    #[test]
    fn sub_underflow_wraps_via_modulus() {
        let a = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        assert_eq!((a - b).limbs, p_minus(2));
    }

    #[test]
    fn sub_zero_minus_one_is_p_minus_one() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a - b).limbs, p_minus(1));
    }

    #[test]
    fn sub_borrow_limb1_to_limb0() {
        let a = Fp::from_limbs_unchecked([0, 1, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a - b).limbs, [u64::MAX, 0, 0, 0]);
    }

    #[test]
    fn sub_borrow_chain_across_all_limbs() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 1]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a - b).limbs, [u64::MAX, u64::MAX, u64::MAX, 0]);
    }

    #[test]
    fn sub_assign_value() {
        let mut a = Fp::from_limbs_unchecked([10, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([4, 0, 0, 0]);
        a -= b;
        assert_eq!(a.limbs, [6, 0, 0, 0]);
    }

    #[test]
    fn sub_assign_ref_with_wrap() {
        let mut a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        a -= &b;
        assert_eq!(a.limbs, p_minus(1));
    }

    #[test]
    fn mul_zero() {
        let a = Fp::from_limbs_unchecked([12345, 6789, 0, 0]);
        let zero = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!((a * zero).limbs, [0, 0, 0, 0]);
    }

    #[test]
    fn mul_one_is_identity() {
        let a = Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        let one = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a * one).limbs, [0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
    }

    #[test]
    fn mul_small_no_reduction() {
        let a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!((a * b).limbs, [35, 0, 0, 0]);
    }

    #[test]
    fn mul_2_to_128_squared_reduces_to_c() {
        let a = Fp::from_limbs_unchecked([0, 0, 1, 0]);
        assert_eq!((a * a).limbs, [0x1_0000_03D1, 0, 0, 0]);
    }

    #[test]
    fn mul_neg_one_squared_is_one() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((neg_one * neg_one).limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn mul_neg_one_times_x_is_neg_x() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        let x = Fp::from_limbs_unchecked([12345, 0, 0, 0]);
        assert_eq!((neg_one * x).limbs, p_minus(12345));
    }

    #[test]
    fn mul_commutative() {
        let a = Fp::from_limbs_unchecked([0x1234_5678_9ABC_DEF0, 0xFEDC_BA98_7654_3210, 7, 11]);
        let b = Fp::from_limbs_unchecked([0xAAAA_BBBB_CCCC_DDDD, 13, 0, 0xEEEE]);
        assert_eq!((a * b).limbs, (b * a).limbs);
    }

    #[test]
    fn mul_assign_value() {
        let mut a = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([4, 0, 0, 0]);
        a *= b;
        assert_eq!(a.limbs, [12, 0, 0, 0]);
    }

    #[test]
    fn mul_assign_ref() {
        let mut a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked(p_minus(1));
        a *= &b;
        assert_eq!(a.limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn pow_by_zero_is_one() {
        let a = Fp::from_limbs_unchecked([12345, 67890, 0, 0]);
        assert_eq!(a.pow([0, 0, 0, 0]).limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn pow_by_one_is_identity() {
        let a = Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        assert_eq!(a.pow([1, 0, 0, 0]).limbs, [0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
    }

    #[test]
    fn pow_by_two_equals_square() {
        let a = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!(a.pow([2, 0, 0, 0]).limbs, (a * a).limbs);
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(Fp::ONE.inv().limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn inv_of_neg_one_is_neg_one() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!(neg_one.inv().limbs, p_minus(1));
    }

    #[test]
    fn x_times_inv_x_is_one_small() {
        let a = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!((a * a.inv()).limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn x_times_inv_x_is_one_multi_limb() {
        let a = Fp::from_limbs_unchecked([0xDEAD_BEEF_CAFE_F00D, 0xABCD, 0x1234, 0x5678]);
        assert_eq!((a * a.inv()).limbs, [1, 0, 0, 0]);
    }

    #[test]
    fn inv_of_zero_is_zero() {
        let zero = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!(zero.inv().limbs, [0, 0, 0, 0]);
    }

    #[test]
    fn from_bytes_little_endian() {
        let mut bytes = [0u8; 32];
        bytes[0] = 0x2F;
        bytes[1] = 0xFC;
        bytes[2] = 0xFF;
        bytes[3] = 0xFF;
        bytes[4] = 0xFE;
        bytes[5] = 0xFF;
        bytes[6] = 0xFF;
        bytes[7] = 0xFF;
        for i in bytes.iter_mut().skip(8) {
            *i = 0xFF;
        }
        let a = Fp::from_bytes_unchecked(bytes);
        assert_eq!(a.limbs, P);
    }
}

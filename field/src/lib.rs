use core::fmt;
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

pub trait Limbs:
    Copy + fmt::Debug + PartialEq + Eq + Hash + AsRef<[u64]> + AsMut<[u64]> + Default
{
}

impl<const N: usize> Limbs for [u64; N] where [u64; N]: Default {}

pub struct MontgomeryParams<T: Limbs> {
    r_squared: T,
    p_inv: u64,
}

pub trait Field: fmt::Debug + Clone + Copy + PartialEq + Eq {
    type Limbs: Limbs;
    const MODULUS: Self::Limbs;
    const PARAMS: MontgomeryParams<Self::Limbs>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1FieldOrder;

impl Field for Secp256k1FieldOrder {
    type Limbs = [u64; 4];
    const MODULUS: [u64; 4] = [
        0xFFFFFFFEFFFFFC2F,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
    ];
    const PARAMS: MontgomeryParams<[u64; 4]> = MontgomeryParams {
        r_squared: [
            0x000007A2000E90A1,
            0x0000000000000001,
            0x0000000000000000,
            0x0000000000000000,
        ],
        p_inv: 0xD838091DD2253531,
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1GroupOrder;

impl Field for Secp256k1GroupOrder {
    type Limbs = [u64; 4];
    const MODULUS: [u64; 4] = [
        0xBFD25E8CD0364141,
        0xBAAEDCE6AF48A03B,
        0xFFFFFFFFFFFFFFFE,
        0xFFFFFFFFFFFFFFFF,
    ];
    const PARAMS: MontgomeryParams<[u64; 4]> = MontgomeryParams {
        r_squared: [
            0x896CF21467D7D140,
            0x741496C20E7CF878,
            0xE697F5E45BCD07C6,
            0x9D671CD581C69BC5,
        ],
        p_inv: 0x4B0DFF665588B13F,
    };
}

/// CSIDH-512 base field: p = 4·(ℓ₁·…·ℓ₇₄) − 1 where ℓᵢ runs over the 74
/// small primes {3, 5, …, 373, 587} listed in the original CSIDH paper.
/// p is 511 bits and ≡ 3 (mod 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Csidh512FieldOrder;

impl Field for Csidh512FieldOrder {
    type Limbs = [u64; 8];
    const MODULUS: [u64; 8] = [
        0x1B81B90533C6C87B,
        0xC2721BF457ACA835,
        0x516730CC1F0B4F25,
        0xA7AAC6C567F35507,
        0x5AFBFCC69322C9CD,
        0xB42D083AEDC88C42,
        0xFC8AB0D15E3E4C4A,
        0x65B48E8F740F89BF,
    ];
    const PARAMS: MontgomeryParams<[u64; 8]> = MontgomeryParams {
        r_squared: [
            0x36905B572FFC1724,
            0x67086F4525F1F27D,
            0x4FAF3FBFD22370CA,
            0x192EA214BCC584B1,
            0x5DAE03EE2F5DE3D0,
            0x1E9248731776B371,
            0xAD5F166E20E4F52D,
            0x4ED759AEA6F3917E,
        ],
        p_inv: 0x66C1301F632E294D,
    };
}

/// Marker trait for prime fields with p ≡ 3 (mod 4), enabling the fast
/// square-root x^((p+1)/4).
pub trait Sqrt3Mod4: Field {}

impl Sqrt3Mod4 for Secp256k1FieldOrder {}
impl Sqrt3Mod4 for Csidh512FieldOrder {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct FieldElement<P: Field> {
    limbs: P::Limbs,
    _marker: PhantomData<P>,
}

impl<P: Field> FieldElement<P> {
    pub fn zero() -> Self {
        Self::from_u64(0)
    }

    pub fn one() -> Self {
        Self::from_u64(1)
    }

    pub fn two() -> Self {
        Self::from_u64(2)
    }

    pub fn three() -> Self {
        Self::from_u64(3)
    }

    pub fn from_u64(x: u64) -> Self {
        let mut canonical = P::Limbs::default();
        canonical.as_mut()[0] = x;
        Self::from_limbs_unchecked(canonical)
    }

    pub fn from_limbs_unchecked(canonical: P::Limbs) -> Self {
        Self {
            limbs: mont_mul::<P>(&canonical, &P::PARAMS.r_squared),
            _marker: PhantomData,
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let a = self.limbs.as_ref();
        let b = rhs.limbs.as_ref();
        let m = P::MODULUS;
        let m_slice = m.as_ref();

        let mut sum = P::Limbs::default();
        let mut c = false;
        for (i, s) in sum.as_mut().iter_mut().enumerate() {
            let (v, nc) = a[i].carrying_add(b[i], c);
            *s = v;
            c = nc;
        }
        let carry = c;

        let mut diff = P::Limbs::default();
        let mut br = false;
        {
            let sum_slice = sum.as_ref();
            for (i, d) in diff.as_mut().iter_mut().enumerate() {
                let (v, nb) = sum_slice[i].borrowing_sub(m_slice[i], br);
                *d = v;
                br = nb;
            }
        }
        let borrow = br;

        let limbs = if carry || !borrow { diff } else { sum };
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        let a = self.limbs.as_ref();
        let b = rhs.limbs.as_ref();
        let m = P::MODULUS;
        let m_slice = m.as_ref();

        let mut diff = P::Limbs::default();
        let mut br = false;
        for (i, d) in diff.as_mut().iter_mut().enumerate() {
            let (v, nb) = a[i].borrowing_sub(b[i], br);
            *d = v;
            br = nb;
        }
        let borrow = br;

        let limbs = if borrow {
            let mut r = P::Limbs::default();
            let mut c = false;
            {
                let diff_slice = diff.as_ref();
                for (i, ri) in r.as_mut().iter_mut().enumerate() {
                    let (v, nc) = diff_slice[i].carrying_add(m_slice[i], c);
                    *ri = v;
                    c = nc;
                }
            }
            r
        } else {
            diff
        };
        Self {
            limbs,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn mul(&self, rhs: &Self) -> Self {
        Self {
            limbs: mont_mul::<P>(&self.limbs, &rhs.limbs),
            _marker: PhantomData,
        }
    }

    pub fn pow(&self, exp: P::Limbs) -> Self {
        let mut result = Self::one();
        for &limb in exp.as_ref().iter().rev() {
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
        let mut exp = P::MODULUS;
        {
            let exp_slice = exp.as_mut();
            let (r0, mut borrow) = exp_slice[0].borrowing_sub(2, false);
            exp_slice[0] = r0;
            for e in exp_slice.iter_mut().skip(1) {
                let (ri, nb) = e.borrowing_sub(0, borrow);
                *e = ri;
                borrow = nb;
            }
        }

        let mut result = Self::one().limbs;

        for &limb in exp.as_ref().iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                result = mont_mul::<P>(&result, &result);
                if (limb >> bit_idx) & 1 == 1 {
                    result = mont_mul::<P>(&result, &self.limbs);
                }
            }
        }

        Self {
            limbs: result,
            _marker: PhantomData,
        }
    }
}

impl<P: Sqrt3Mod4> FieldElement<P> {
    /// Returns a square root of `self` via `self^((p+1)/4)`.
    ///
    /// If `self` is a non-residue the return value is not a true square root;
    /// callers should verify by squaring (`r * r == self`).
    pub fn sqrt(&self) -> Self {
        let mut exp = P::MODULUS;
        {
            let s = exp.as_mut();
            let (v0, mut carry) = s[0].overflowing_add(1);
            s[0] = v0;
            for e in s.iter_mut().skip(1) {
                if !carry {
                    break;
                }
                let (v, nc) = e.overflowing_add(1);
                *e = v;
                carry = nc;
            }
        }
        {
            let s = exp.as_mut();
            let n = s.len();
            let mut carry = 0u64;
            for i in (0..n).rev() {
                let next_carry = s[i] & 0b11;
                s[i] = (s[i] >> 2) | (carry << 62);
                carry = next_carry;
            }
        }
        self.pow(exp)
    }
}

impl<P: Field<Limbs = [u64; 4]>> FieldElement<P> {
    pub fn from_bytes_unchecked(bytes: [u8; 32]) -> Self {
        let canonical = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];
        Self::from_limbs_unchecked(canonical)
    }

    pub fn to_bytes_le(&self) -> [u8; 32] {
        let mut one = [0u64; 4];
        one[0] = 1;
        let canonical = mont_mul::<P>(&self.limbs, &one);
        let mut bytes = [0u8; 32];
        bytes[0..8].copy_from_slice(&canonical[0].to_le_bytes());
        bytes[8..16].copy_from_slice(&canonical[1].to_le_bytes());
        bytes[16..24].copy_from_slice(&canonical[2].to_le_bytes());
        bytes[24..32].copy_from_slice(&canonical[3].to_le_bytes());
        bytes
    }
}

#[inline]
fn ge_modulus<P: Field>(x: &P::Limbs) -> bool {
    let x_slice = x.as_ref();
    let m = P::MODULUS;
    let m_slice = m.as_ref();
    for i in (0..x_slice.len()).rev() {
        if x_slice[i] != m_slice[i] {
            return x_slice[i] > m_slice[i];
        }
    }
    true
}

pub fn mont_mul<P: Field>(a: &P::Limbs, b: &P::Limbs) -> P::Limbs {
    let a = a.as_ref();
    let b = b.as_ref();
    let m = P::MODULUS;
    let p = m.as_ref();
    let p_inv = P::PARAMS.p_inv;
    let n = a.len();

    let mut t = P::Limbs::default();
    let mut t_hi: u64 = 0;
    let mut t_hi1: u64 = 0;

    for &bi in b {
        let mut carry = 0u64;
        {
            let t_mut = t.as_mut();
            for j in 0..n {
                let prod = (a[j] as u128) * (bi as u128) + (t_mut[j] as u128) + (carry as u128);
                t_mut[j] = prod as u64;
                carry = (prod >> 64) as u64;
            }
        }
        let s = (t_hi as u128) + (carry as u128);
        t_hi = s as u64;
        t_hi1 = t_hi1.wrapping_add((s >> 64) as u64);

        let mm = t.as_ref()[0].wrapping_mul(p_inv);
        let prod0 = (mm as u128) * (p[0] as u128) + (t.as_ref()[0] as u128);
        let mut carry = (prod0 >> 64) as u64;
        {
            let t_mut = t.as_mut();
            for j in 1..n {
                let prod = (mm as u128) * (p[j] as u128) + (t_mut[j] as u128) + (carry as u128);
                t_mut[j - 1] = prod as u64;
                carry = (prod >> 64) as u64;
            }
        }
        let s = (t_hi as u128) + (carry as u128);
        t.as_mut()[n - 1] = s as u64;
        let cout = (s >> 64) as u64;
        let s2 = (t_hi1 as u128) + (cout as u128);
        t_hi = s2 as u64;
        t_hi1 = (s2 >> 64) as u64;
    }

    if t_hi != 0 || ge_modulus::<P>(&t) {
        let t_mut = t.as_mut();
        let mut borrow = false;
        for i in 0..n {
            let (d, nb) = t_mut[i].borrowing_sub(p[i], borrow);
            t_mut[i] = d;
            borrow = nb;
        }
    }
    t
}

impl<P: Field> Add for FieldElement<P> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        FieldElement::<P>::add(&self, &rhs)
    }
}

impl<P: Field> Add<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(&self, rhs)
    }
}

impl<P: Field> Add<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, &rhs)
    }
}

impl<P: Field> Add<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, rhs)
    }
}

impl<P: Field> AddAssign for FieldElement<P> {
    fn add_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::add(self, &rhs);
    }
}

impl<P: Field> AddAssign<&FieldElement<P>> for FieldElement<P> {
    fn add_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::add(self, rhs);
    }
}

impl<P: Field> Sub for FieldElement<P> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        FieldElement::<P>::sub(&self, &rhs)
    }
}

impl<P: Field> Sub<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(&self, rhs)
    }
}

impl<P: Field> Sub<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, &rhs)
    }
}

impl<P: Field> Sub<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, rhs)
    }
}

impl<P: Field> SubAssign for FieldElement<P> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::sub(self, &rhs);
    }
}

impl<P: Field> SubAssign<&FieldElement<P>> for FieldElement<P> {
    fn sub_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::sub(self, rhs);
    }
}

impl<P: Field> Mul for FieldElement<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        FieldElement::<P>::mul(&self, &rhs)
    }
}

impl<P: Field> Mul<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(&self, rhs)
    }
}

impl<P: Field> Mul<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, &rhs)
    }
}

impl<P: Field> Mul<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, rhs)
    }
}

impl<P: Field> MulAssign for FieldElement<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::mul(self, &rhs);
    }
}

impl<P: Field> MulAssign<&FieldElement<P>> for FieldElement<P> {
    fn mul_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::mul(self, rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Fp = FieldElement<Secp256k1FieldOrder>;
    const P: [u64; 4] = Secp256k1FieldOrder::MODULUS;

    fn p_minus(n: u64) -> [u64; 4] {
        [P[0].wrapping_sub(n), P[1], P[2], P[3]]
    }

    #[test]
    fn add_zero_plus_zero() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 0, 0, 0]));
    }

    #[test]
    fn add_one_plus_one() {
        let a = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([2, 0, 0, 0]));
    }

    #[test]
    fn add_p_minus_one_plus_one_wraps_to_zero() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 0, 0, 0]));
    }

    #[test]
    fn add_overflows_field_order() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((a + b), Fp::from_limbs_unchecked(p_minus(2)));
    }

    #[test]
    fn add_assign_value() {
        let mut a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        a += b;
        assert_eq!(a, Fp::from_limbs_unchecked([12, 0, 0, 0]));
    }

    #[test]
    fn add_assign_ref() {
        let mut a = Fp::from_limbs_unchecked(p_minus(3));
        let b = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        a += &b;
        assert_eq!(a, Fp::from_limbs_unchecked([2, 0, 0, 0]));
    }

    #[test]
    fn add_carry_limb0_to_limb1() {
        let a = Fp::from_limbs_unchecked([u64::MAX, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 1, 0, 0]));
    }

    #[test]
    fn add_carry_limb1_to_limb2() {
        let a = Fp::from_limbs_unchecked([0, u64::MAX, 0, 0]);
        let b = Fp::from_limbs_unchecked([0, 1, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 0, 1, 0]));
    }

    #[test]
    fn add_carry_chain_across_all_limbs() {
        let a = Fp::from_limbs_unchecked([u64::MAX, u64::MAX, u64::MAX, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 0, 0, 1]));
    }

    #[test]
    fn add_intra_limb_carry_with_nonzero_high() {
        let a = Fp::from_limbs_unchecked([u64::MAX, 5, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a + b), Fp::from_limbs_unchecked([0, 6, 0, 0]));
    }

    #[test]
    fn add_carry_to_high_limb_below_modulus() {
        let a = Fp::from_limbs_unchecked([u64::MAX, u64::MAX, u64::MAX, 0x7FFFFFFFFFFFFFFF]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!(
            (a + b),
            Fp::from_limbs_unchecked([0, 0, 0, 0x8000000000000000])
        );
    }

    #[test]
    fn sub_simple() {
        let a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        assert_eq!((a - b), Fp::from_limbs_unchecked([2, 0, 0, 0]));
    }

    #[test]
    fn sub_self_is_zero() {
        let a = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((a - a), Fp::from_limbs_unchecked([0, 0, 0, 0]));
    }

    #[test]
    fn sub_underflow_wraps_via_modulus() {
        let a = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        assert_eq!((a - b), Fp::from_limbs_unchecked(p_minus(2)));
    }

    #[test]
    fn sub_zero_minus_one_is_p_minus_one() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a - b), Fp::from_limbs_unchecked(p_minus(1)));
    }

    #[test]
    fn sub_borrow_limb1_to_limb0() {
        let a = Fp::from_limbs_unchecked([0, 1, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!((a - b), Fp::from_limbs_unchecked([u64::MAX, 0, 0, 0]));
    }

    #[test]
    fn sub_borrow_chain_across_all_limbs() {
        let a = Fp::from_limbs_unchecked([0, 0, 0, 1]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!(
            (a - b),
            Fp::from_limbs_unchecked([u64::MAX, u64::MAX, u64::MAX, 0])
        );
    }

    #[test]
    fn sub_assign_value() {
        let mut a = Fp::from_limbs_unchecked([10, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([4, 0, 0, 0]);
        a -= b;
        assert_eq!(a, Fp::from_limbs_unchecked([6, 0, 0, 0]));
    }

    #[test]
    fn sub_assign_ref_with_wrap() {
        let mut a = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        a -= &b;
        assert_eq!(a, Fp::from_limbs_unchecked(p_minus(1)));
    }

    #[test]
    fn mul_zero() {
        let a = Fp::from_limbs_unchecked([12345, 6789, 0, 0]);
        let zero = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!((a * zero), Fp::from_limbs_unchecked([0, 0, 0, 0]));
    }

    #[test]
    fn mul_one_is_identity() {
        let a = Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        let one = Fp::from_limbs_unchecked([1, 0, 0, 0]);
        assert_eq!(
            (a * one),
            Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D])
        );
    }

    #[test]
    fn mul_small_no_reduction() {
        let a = Fp::from_limbs_unchecked([5, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!((a * b), Fp::from_limbs_unchecked([35, 0, 0, 0]));
    }

    #[test]
    fn mul_2_to_128_squared_reduces_to_c() {
        let a = Fp::from_limbs_unchecked([0, 0, 1, 0]);
        assert_eq!((a * a), Fp::from_limbs_unchecked([0x1_0000_03D1, 0, 0, 0]));
    }

    #[test]
    fn mul_neg_one_squared_is_one() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!((neg_one * neg_one), Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn mul_neg_one_times_x_is_neg_x() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        let x = Fp::from_limbs_unchecked([12345, 0, 0, 0]);
        assert_eq!((neg_one * x), Fp::from_limbs_unchecked(p_minus(12345)));
    }

    #[test]
    fn mul_commutative() {
        let a = Fp::from_limbs_unchecked([0x1234_5678_9ABC_DEF0, 0xFEDC_BA98_7654_3210, 7, 11]);
        let b = Fp::from_limbs_unchecked([0xAAAA_BBBB_CCCC_DDDD, 13, 0, 0xEEEE]);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn mul_assign_value() {
        let mut a = Fp::from_limbs_unchecked([3, 0, 0, 0]);
        let b = Fp::from_limbs_unchecked([4, 0, 0, 0]);
        a *= b;
        assert_eq!(a, Fp::from_limbs_unchecked([12, 0, 0, 0]));
    }

    #[test]
    fn mul_assign_ref() {
        let mut a = Fp::from_limbs_unchecked(p_minus(1));
        let b = Fp::from_limbs_unchecked(p_minus(1));
        a *= &b;
        assert_eq!(a, Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn pow_by_zero_is_one() {
        let a = Fp::from_limbs_unchecked([12345, 67890, 0, 0]);
        assert_eq!(a.pow([0, 0, 0, 0]), Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn pow_by_one_is_identity() {
        let a = Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        assert_eq!(
            a.pow([1, 0, 0, 0]),
            Fp::from_limbs_unchecked([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D])
        );
    }

    #[test]
    fn pow_by_two_equals_square() {
        let a = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!(a.pow([2, 0, 0, 0]), a * a);
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(Fp::one().inv(), Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn inv_of_neg_one_is_neg_one() {
        let neg_one = Fp::from_limbs_unchecked(p_minus(1));
        assert_eq!(neg_one.inv(), Fp::from_limbs_unchecked(p_minus(1)));
    }

    #[test]
    fn x_times_inv_x_is_one_small() {
        let a = Fp::from_limbs_unchecked([7, 0, 0, 0]);
        assert_eq!((a * a.inv()), Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn x_times_inv_x_is_one_multi_limb() {
        let a = Fp::from_limbs_unchecked([0xDEAD_BEEF_CAFE_F00D, 0xABCD, 0x1234, 0x5678]);
        assert_eq!((a * a.inv()), Fp::from_limbs_unchecked([1, 0, 0, 0]));
    }

    #[test]
    fn inv_of_zero_is_zero() {
        let zero = Fp::from_limbs_unchecked([0, 0, 0, 0]);
        assert_eq!(zero.inv(), Fp::from_limbs_unchecked([0, 0, 0, 0]));
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
        assert_eq!(a, Fp::from_limbs_unchecked(P));
    }

    #[test]
    fn sqrt_of_zero_is_zero() {
        assert_eq!(Fp::zero().sqrt(), Fp::zero());
    }

    #[test]
    fn sqrt_of_one_squares_to_one() {
        let r = Fp::one().sqrt();
        assert_eq!(r * r, Fp::one());
    }

    #[test]
    fn sqrt_of_secp256k1_square_roundtrips() {
        let x = Fp::from_u64(42);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_secp256k1_multilimb_square_roundtrips() {
        let x = Fp::from_limbs_unchecked([0xDEAD_BEEF_CAFE_F00D, 0xABCD, 0x1234, 0x5678]);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_non_residue_does_not_square_back() {
        // 3 is a non-residue mod p_{secp256k1}. Sqrt gives some r with r² ≠ 3.
        // (We rely on this behavior for the QR test in CSIDH point sampling.)
        let three = Fp::from_u64(3);
        let r = three.sqrt();
        assert_ne!(r * r, three);
    }

    type Fc = FieldElement<Csidh512FieldOrder>;

    #[test]
    fn csidh_sqrt_of_zero_is_zero() {
        assert_eq!(Fc::zero().sqrt(), Fc::zero());
    }

    #[test]
    fn csidh_sqrt_of_one_squares_to_one() {
        let r = Fc::one().sqrt();
        assert_eq!(r * r, Fc::one());
    }

    #[test]
    fn csidh_sqrt_of_small_square_roundtrips() {
        let x = Fc::from_u64(1234567);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn csidh_sqrt_of_multilimb_square_roundtrips() {
        let x = Fc::from_limbs_unchecked([
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            0x1111_2222_3333_4444,
            0x5555_6666_7777_8888,
            0x9999_AAAA_BBBB_CCCC,
            0xDEAD_BEEF_CAFE_F00D,
            0x0F0F_F0F0_5A5A_A5A5,
            0x0000_0001_0000_0001,
        ]);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn csidh_modulus_is_congruent_to_3_mod_4() {
        // Precondition for the sqrt formula: p ≡ 3 (mod 4).
        assert_eq!(Csidh512FieldOrder::MODULUS[0] & 0b11, 0b11);
    }
}

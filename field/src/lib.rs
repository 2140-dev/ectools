use core::fmt;
use core::hash::Hash;
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

pub trait Limbs:
    Copy + fmt::Debug + PartialEq + Eq + Hash + AsRef<[u64]> + AsMut<[u64]>
{
    const ZERO: Self;
    fn from_u64(x: u64) -> Self;
}

impl<const N: usize> Limbs for [u64; N] {
    const ZERO: Self = [0u64; N];
    fn from_u64(x: u64) -> Self {
        let mut r = [0u64; N];
        r[0] = x;
        r
    }
}

pub trait FieldOrder: fmt::Debug + Clone + Copy + PartialEq + Eq {
    type Limbs: Limbs;
    const MODULUS: Self::Limbs;
    const PINV: u64;
    const R2: Self::Limbs;
    const ONE_MONT: Self::Limbs;
    const TWO_MONT: Self::Limbs;
    const THREE_MONT: Self::Limbs;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1FieldOrder;

impl FieldOrder for Secp256k1FieldOrder {
    type Limbs = [u64; 4];
    const MODULUS: [u64; 4] = [
        0xFFFFFFFEFFFFFC2F,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
    ];
    const PINV: u64 = compute_pinv(Self::MODULUS[0]);
    const R2: [u64; 4] = compute_r_squared(Self::MODULUS);
    const ONE_MONT: [u64; 4] =
        mont_mul_ct([1, 0, 0, 0], Self::R2, Self::MODULUS, Self::PINV);
    const TWO_MONT: [u64; 4] =
        mod_add_ct(Self::ONE_MONT, Self::ONE_MONT, Self::MODULUS);
    const THREE_MONT: [u64; 4] =
        mod_add_ct(Self::TWO_MONT, Self::ONE_MONT, Self::MODULUS);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Secp256k1GroupOrder;

impl FieldOrder for Secp256k1GroupOrder {
    type Limbs = [u64; 4];
    const MODULUS: [u64; 4] = [
        0xBFD25E8CD0364141,
        0xBAAEDCE6AF48A03B,
        0xFFFFFFFFFFFFFFFE,
        0xFFFFFFFFFFFFFFFF,
    ];
    const PINV: u64 = compute_pinv(Self::MODULUS[0]);
    const R2: [u64; 4] = compute_r_squared(Self::MODULUS);
    const ONE_MONT: [u64; 4] =
        mont_mul_ct([1, 0, 0, 0], Self::R2, Self::MODULUS, Self::PINV);
    const TWO_MONT: [u64; 4] =
        mod_add_ct(Self::ONE_MONT, Self::ONE_MONT, Self::MODULUS);
    const THREE_MONT: [u64; 4] =
        mod_add_ct(Self::TWO_MONT, Self::ONE_MONT, Self::MODULUS);
}

/// CSIDH-512 base field: p = 4·(ℓ₁·…·ℓ₇₄) − 1 where ℓᵢ runs over the 74
/// small primes {3, 5, …, 373, 587} listed in the original CSIDH paper.
/// p is 511 bits and ≡ 3 (mod 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Csidh512FieldOrder;

impl FieldOrder for Csidh512FieldOrder {
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
    const PINV: u64 = compute_pinv(Self::MODULUS[0]);
    const R2: [u64; 8] = compute_r_squared(Self::MODULUS);
    const ONE_MONT: [u64; 8] = mont_mul_ct(
        [1, 0, 0, 0, 0, 0, 0, 0],
        Self::R2,
        Self::MODULUS,
        Self::PINV,
    );
    const TWO_MONT: [u64; 8] =
        mod_add_ct(Self::ONE_MONT, Self::ONE_MONT, Self::MODULUS);
    const THREE_MONT: [u64; 8] =
        mod_add_ct(Self::TWO_MONT, Self::ONE_MONT, Self::MODULUS);
}

/// Marker trait for prime fields with p ≡ 3 (mod 4), enabling the fast
/// square-root x^((p+1)/4).
pub trait Sqrt3Mod4: FieldOrder {}

impl Sqrt3Mod4 for Secp256k1FieldOrder {}
impl Sqrt3Mod4 for Csidh512FieldOrder {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct FieldElement<P: FieldOrder> {
    limbs: P::Limbs,
    _marker: PhantomData<P>,
}

impl<P: FieldOrder> FieldElement<P> {
    pub const ZERO: Self = Self {
        limbs: <P::Limbs as Limbs>::ZERO,
        _marker: PhantomData,
    };

    pub const ONE: Self = Self {
        limbs: P::ONE_MONT,
        _marker: PhantomData,
    };

    pub const TWO: Self = Self {
        limbs: P::TWO_MONT,
        _marker: PhantomData,
    };

    pub const THREE: Self = Self {
        limbs: P::THREE_MONT,
        _marker: PhantomData,
    };

    pub fn from_u64(x: u64) -> Self {
        Self::from_limbs_unchecked(<P::Limbs as Limbs>::from_u64(x))
    }

    pub fn from_limbs_unchecked(canonical_limbs: P::Limbs) -> Self {
        let r2 = P::R2;
        let m = P::MODULUS;
        Self {
            limbs: mont_mul(&canonical_limbs, &r2, &m, P::PINV),
            _marker: PhantomData,
        }
    }

    pub const fn from_montgomery_limbs_unchecked(mont_limbs: P::Limbs) -> Self {
        Self {
            limbs: mont_limbs,
            _marker: PhantomData,
        }
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let a = self.limbs.as_ref();
        let b = rhs.limbs.as_ref();
        let m = P::MODULUS;
        let m_slice = m.as_ref();

        let mut sum = <P::Limbs as Limbs>::ZERO;
        let mut c = false;
        for (i, s) in sum.as_mut().iter_mut().enumerate() {
            let (v, nc) = a[i].carrying_add(b[i], c);
            *s = v;
            c = nc;
        }
        let carry = c;

        let mut diff = <P::Limbs as Limbs>::ZERO;
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

        let mut diff = <P::Limbs as Limbs>::ZERO;
        let mut br = false;
        for (i, d) in diff.as_mut().iter_mut().enumerate() {
            let (v, nb) = a[i].borrowing_sub(b[i], br);
            *d = v;
            br = nb;
        }
        let borrow = br;

        let limbs = if borrow {
            let mut r = <P::Limbs as Limbs>::ZERO;
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
        let m = P::MODULUS;
        Self {
            limbs: mont_mul(&self.limbs, &rhs.limbs, &m, P::PINV),
            _marker: PhantomData,
        }
    }

    pub fn pow(&self, exp: P::Limbs) -> Self {
        let mut result = Self::ONE;
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
        self.pow(exp)
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

impl<P: FieldOrder<Limbs = [u64; 4]>> FieldElement<P> {
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
        let one: [u64; 4] = [1, 0, 0, 0];
        let m = P::MODULUS;
        let canonical = mont_mul(&self.limbs, &one, &m, P::PINV);
        let mut bytes = [0u8; 32];
        bytes[0..8].copy_from_slice(&canonical[0].to_le_bytes());
        bytes[8..16].copy_from_slice(&canonical[1].to_le_bytes());
        bytes[16..24].copy_from_slice(&canonical[2].to_le_bytes());
        bytes[24..32].copy_from_slice(&canonical[3].to_le_bytes());
        bytes
    }
}

pub const fn compute_pinv(m0: u64) -> u64 {
    let mut y: u64 = 1;
    let mut i = 0;
    while i < 6 {
        y = y.wrapping_mul(2u64.wrapping_sub(m0.wrapping_mul(y)));
        i += 1;
    }
    y.wrapping_neg()
}

pub const fn ge_ct<const N: usize>(a: &[u64; N], b: &[u64; N]) -> bool {
    let mut i = N;
    while i > 0 {
        i -= 1;
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}

pub const fn compute_r_squared<const N: usize>(m: [u64; N]) -> [u64; N] {
    let mut x = [0u64; N];
    x[0] = 1;
    let total_bits = 2 * 64 * N;
    let mut i = 0;
    while i < total_bits {
        let mut carry: u64 = 0;
        let mut j = 0;
        while j < N {
            let new = (x[j] << 1) | carry;
            carry = x[j] >> 63;
            x[j] = new;
            j += 1;
        }
        let overflow = carry != 0;
        if overflow || ge_ct(&x, &m) {
            let mut borrow: u64 = 0;
            let mut k = 0;
            while k < N {
                let (d, b1) = x[k].overflowing_sub(m[k]);
                let (d2, b2) = d.overflowing_sub(borrow);
                x[k] = d2;
                borrow = b1 as u64 | b2 as u64;
                k += 1;
            }
        }
        i += 1;
    }
    x
}

pub const fn mont_mul_ct<const N: usize>(
    a: [u64; N],
    b: [u64; N],
    p: [u64; N],
    pinv: u64,
) -> [u64; N] {
    let mut t = [0u64; N];
    let mut t_hi: u64 = 0;
    let mut t_hi1: u64 = 0;

    let mut i = 0;
    while i < N {
        let bi = b[i];
        let mut carry: u64 = 0;
        let mut j = 0;
        while j < N {
            let prod = a[j] as u128 * bi as u128 + t[j] as u128 + carry as u128;
            t[j] = prod as u64;
            carry = (prod >> 64) as u64;
            j += 1;
        }
        let s = t_hi as u128 + carry as u128;
        t_hi = s as u64;
        t_hi1 = t_hi1.wrapping_add((s >> 64) as u64);

        let m = t[0].wrapping_mul(pinv);
        let prod = m as u128 * p[0] as u128 + t[0] as u128;
        let mut carry = (prod >> 64) as u64;
        let mut j = 1;
        while j < N {
            let prod = m as u128 * p[j] as u128 + t[j] as u128 + carry as u128;
            t[j - 1] = prod as u64;
            carry = (prod >> 64) as u64;
            j += 1;
        }
        let s = t_hi as u128 + carry as u128;
        t[N - 1] = s as u64;
        let cout = (s >> 64) as u64;
        let s2 = t_hi1 as u128 + cout as u128;
        t_hi = s2 as u64;
        t_hi1 = (s2 >> 64) as u64;

        i += 1;
    }

    if t_hi != 0 || ge_ct(&t, &p) {
        let mut borrow: u64 = 0;
        let mut j = 0;
        while j < N {
            let (d, b1) = t[j].overflowing_sub(p[j]);
            let (d2, b2) = d.overflowing_sub(borrow);
            t[j] = d2;
            borrow = b1 as u64 | b2 as u64;
            j += 1;
        }
    }
    t
}

pub const fn mod_add_ct<const N: usize>(
    a: [u64; N],
    b: [u64; N],
    m: [u64; N],
) -> [u64; N] {
    let mut sum = [0u64; N];
    let mut c: u64 = 0;
    let mut i = 0;
    while i < N {
        let s = a[i] as u128 + b[i] as u128 + c as u128;
        sum[i] = s as u64;
        c = (s >> 64) as u64;
        i += 1;
    }
    let carry = c != 0;
    let mut diff = [0u64; N];
    let mut borrow: u64 = 0;
    let mut i = 0;
    while i < N {
        let (d, b1) = sum[i].overflowing_sub(m[i]);
        let (d2, b2) = d.overflowing_sub(borrow);
        diff[i] = d2;
        borrow = b1 as u64 | b2 as u64;
        i += 1;
    }
    if carry || borrow == 0 { diff } else { sum }
}

fn mont_mul<L: Limbs>(a: &L, b: &L, p: &L, pinv: u64) -> L {
    let a = a.as_ref();
    let b = b.as_ref();
    let p_slice = p.as_ref();
    let n = a.len();

    let mut t = L::ZERO;
    let mut t_hi: u64 = 0;
    let mut t_hi1: u64 = 0;

    for i in 0..n {
        let bi = b[i];
        {
            let t_mut = t.as_mut();
            let mut carry: u64 = 0;
            for j in 0..n {
                let prod =
                    a[j] as u128 * bi as u128 + t_mut[j] as u128 + carry as u128;
                t_mut[j] = prod as u64;
                carry = (prod >> 64) as u64;
            }
            let s = t_hi as u128 + carry as u128;
            t_hi = s as u64;
            t_hi1 = t_hi1.wrapping_add((s >> 64) as u64);
        }
        let m = t.as_ref()[0].wrapping_mul(pinv);
        {
            let t_mut = t.as_mut();
            let prod = m as u128 * p_slice[0] as u128 + t_mut[0] as u128;
            let mut carry = (prod >> 64) as u64;
            for j in 1..n {
                let prod = m as u128 * p_slice[j] as u128
                    + t_mut[j] as u128
                    + carry as u128;
                t_mut[j - 1] = prod as u64;
                carry = (prod >> 64) as u64;
            }
            let s = t_hi as u128 + carry as u128;
            t_mut[n - 1] = s as u64;
            let cout = (s >> 64) as u64;
            let s2 = t_hi1 as u128 + cout as u128;
            t_hi = s2 as u64;
            t_hi1 = (s2 >> 64) as u64;
        }
    }

    let sub = t_hi != 0 || {
        let t_r = t.as_ref();
        let mut ge = true;
        for i in (0..n).rev() {
            if t_r[i] != p_slice[i] {
                ge = t_r[i] > p_slice[i];
                break;
            }
        }
        ge
    };
    if sub {
        let t_mut = t.as_mut();
        let mut borrow: u64 = 0;
        for j in 0..n {
            let (d, b1) = t_mut[j].overflowing_sub(p_slice[j]);
            let (d2, b2) = d.overflowing_sub(borrow);
            t_mut[j] = d2;
            borrow = b1 as u64 | b2 as u64;
        }
    }
    t
}

impl<P: FieldOrder> Add for FieldElement<P> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        FieldElement::<P>::add(&self, &rhs)
    }
}

impl<P: FieldOrder> Add<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(&self, rhs)
    }
}

impl<P: FieldOrder> Add<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, &rhs)
    }
}

impl<P: FieldOrder> Add<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn add(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::add(self, rhs)
    }
}

impl<P: FieldOrder> AddAssign for FieldElement<P> {
    fn add_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::add(self, &rhs);
    }
}

impl<P: FieldOrder> AddAssign<&FieldElement<P>> for FieldElement<P> {
    fn add_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::add(self, rhs);
    }
}

impl<P: FieldOrder> Sub for FieldElement<P> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        FieldElement::<P>::sub(&self, &rhs)
    }
}

impl<P: FieldOrder> Sub<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(&self, rhs)
    }
}

impl<P: FieldOrder> Sub<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, &rhs)
    }
}

impl<P: FieldOrder> Sub<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn sub(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::sub(self, rhs)
    }
}

impl<P: FieldOrder> SubAssign for FieldElement<P> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::sub(self, &rhs);
    }
}

impl<P: FieldOrder> SubAssign<&FieldElement<P>> for FieldElement<P> {
    fn sub_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::sub(self, rhs);
    }
}

impl<P: FieldOrder> Mul for FieldElement<P> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        FieldElement::<P>::mul(&self, &rhs)
    }
}

impl<P: FieldOrder> Mul<&FieldElement<P>> for FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(&self, rhs)
    }
}

impl<P: FieldOrder> Mul<FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, &rhs)
    }
}

impl<P: FieldOrder> Mul<&FieldElement<P>> for &FieldElement<P> {
    type Output = FieldElement<P>;
    fn mul(self, rhs: &FieldElement<P>) -> FieldElement<P> {
        FieldElement::<P>::mul(self, rhs)
    }
}

impl<P: FieldOrder> MulAssign for FieldElement<P> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = FieldElement::<P>::mul(self, &rhs);
    }
}

impl<P: FieldOrder> MulAssign<&FieldElement<P>> for FieldElement<P> {
    fn mul_assign(&mut self, rhs: &FieldElement<P>) {
        *self = FieldElement::<P>::mul(self, rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Fp = FieldElement<Secp256k1FieldOrder>;
    const P: [u64; 4] = Secp256k1FieldOrder::MODULUS;

    fn fe(limbs: [u64; 4]) -> Fp {
        Fp::from_limbs_unchecked(limbs)
    }

    fn p_minus(n: u64) -> [u64; 4] {
        [P[0].wrapping_sub(n), P[1], P[2], P[3]]
    }

    #[test]
    fn add_zero_plus_zero() {
        assert_eq!(fe([0, 0, 0, 0]) + fe([0, 0, 0, 0]), fe([0, 0, 0, 0]));
    }

    #[test]
    fn add_one_plus_one() {
        assert_eq!(fe([1, 0, 0, 0]) + fe([1, 0, 0, 0]), fe([2, 0, 0, 0]));
    }

    #[test]
    fn add_p_minus_one_plus_one_wraps_to_zero() {
        assert_eq!(fe(p_minus(1)) + fe([1, 0, 0, 0]), fe([0, 0, 0, 0]));
    }

    #[test]
    fn add_overflows_field_order() {
        assert_eq!(fe(p_minus(1)) + fe(p_minus(1)), fe(p_minus(2)));
    }

    #[test]
    fn add_assign_value() {
        let mut a = fe([5, 0, 0, 0]);
        let b = fe([7, 0, 0, 0]);
        a += b;
        assert_eq!(a, fe([12, 0, 0, 0]));
    }

    #[test]
    fn add_assign_ref() {
        let mut a = fe(p_minus(3));
        let b = fe([5, 0, 0, 0]);
        a += &b;
        assert_eq!(a, fe([2, 0, 0, 0]));
    }

    #[test]
    fn add_carry_limb0_to_limb1() {
        assert_eq!(
            fe([u64::MAX, 0, 0, 0]) + fe([1, 0, 0, 0]),
            fe([0, 1, 0, 0])
        );
    }

    #[test]
    fn add_carry_limb1_to_limb2() {
        assert_eq!(
            fe([0, u64::MAX, 0, 0]) + fe([0, 1, 0, 0]),
            fe([0, 0, 1, 0])
        );
    }

    #[test]
    fn add_carry_chain_across_all_limbs() {
        assert_eq!(
            fe([u64::MAX, u64::MAX, u64::MAX, 0]) + fe([1, 0, 0, 0]),
            fe([0, 0, 0, 1]),
        );
    }

    #[test]
    fn add_intra_limb_carry_with_nonzero_high() {
        assert_eq!(
            fe([u64::MAX, 5, 0, 0]) + fe([1, 0, 0, 0]),
            fe([0, 6, 0, 0]),
        );
    }

    #[test]
    fn add_carry_to_high_limb_below_modulus() {
        assert_eq!(
            fe([u64::MAX, u64::MAX, u64::MAX, 0x7FFFFFFFFFFFFFFF])
                + fe([1, 0, 0, 0]),
            fe([0, 0, 0, 0x8000000000000000]),
        );
    }

    #[test]
    fn sub_simple() {
        assert_eq!(fe([5, 0, 0, 0]) - fe([3, 0, 0, 0]), fe([2, 0, 0, 0]));
    }

    #[test]
    fn sub_self_is_zero() {
        let a = fe(p_minus(1));
        assert_eq!(a - a, fe([0, 0, 0, 0]));
    }

    #[test]
    fn sub_underflow_wraps_via_modulus() {
        assert_eq!(fe([3, 0, 0, 0]) - fe([5, 0, 0, 0]), fe(p_minus(2)));
    }

    #[test]
    fn sub_zero_minus_one_is_p_minus_one() {
        assert_eq!(fe([0, 0, 0, 0]) - fe([1, 0, 0, 0]), fe(p_minus(1)));
    }

    #[test]
    fn sub_borrow_limb1_to_limb0() {
        assert_eq!(
            fe([0, 1, 0, 0]) - fe([1, 0, 0, 0]),
            fe([u64::MAX, 0, 0, 0]),
        );
    }

    #[test]
    fn sub_borrow_chain_across_all_limbs() {
        assert_eq!(
            fe([0, 0, 0, 1]) - fe([1, 0, 0, 0]),
            fe([u64::MAX, u64::MAX, u64::MAX, 0]),
        );
    }

    #[test]
    fn sub_assign_value() {
        let mut a = fe([10, 0, 0, 0]);
        let b = fe([4, 0, 0, 0]);
        a -= b;
        assert_eq!(a, fe([6, 0, 0, 0]));
    }

    #[test]
    fn sub_assign_ref_with_wrap() {
        let mut a = fe([0, 0, 0, 0]);
        let b = fe([1, 0, 0, 0]);
        a -= &b;
        assert_eq!(a, fe(p_minus(1)));
    }

    #[test]
    fn mul_zero() {
        let a = fe([12345, 6789, 0, 0]);
        let zero = fe([0, 0, 0, 0]);
        assert_eq!(a * zero, fe([0, 0, 0, 0]));
    }

    #[test]
    fn mul_one_is_identity() {
        let a = fe([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        assert_eq!(a * Fp::ONE, a);
    }

    #[test]
    fn mul_small_no_reduction() {
        assert_eq!(fe([5, 0, 0, 0]) * fe([7, 0, 0, 0]), fe([35, 0, 0, 0]));
    }

    #[test]
    fn mul_2_to_128_squared_reduces_to_c() {
        let a = fe([0, 0, 1, 0]);
        assert_eq!(a * a, fe([0x1_0000_03D1, 0, 0, 0]));
    }

    #[test]
    fn mul_neg_one_squared_is_one() {
        let neg_one = fe(p_minus(1));
        assert_eq!(neg_one * neg_one, fe([1, 0, 0, 0]));
    }

    #[test]
    fn mul_neg_one_times_x_is_neg_x() {
        let neg_one = fe(p_minus(1));
        let x = fe([12345, 0, 0, 0]);
        assert_eq!(neg_one * x, fe(p_minus(12345)));
    }

    #[test]
    fn mul_commutative() {
        let a = fe([0x1234_5678_9ABC_DEF0, 0xFEDC_BA98_7654_3210, 7, 11]);
        let b = fe([0xAAAA_BBBB_CCCC_DDDD, 13, 0, 0xEEEE]);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn mul_assign_value() {
        let mut a = fe([3, 0, 0, 0]);
        let b = fe([4, 0, 0, 0]);
        a *= b;
        assert_eq!(a, fe([12, 0, 0, 0]));
    }

    #[test]
    fn mul_assign_ref() {
        let mut a = fe(p_minus(1));
        let b = fe(p_minus(1));
        a *= &b;
        assert_eq!(a, fe([1, 0, 0, 0]));
    }

    #[test]
    fn pow_by_zero_is_one() {
        let a = fe([12345, 67890, 0, 0]);
        assert_eq!(a.pow([0, 0, 0, 0]), Fp::ONE);
    }

    #[test]
    fn pow_by_one_is_identity() {
        let a = fe([0xDEAD, 0xBEEF, 0xCAFE, 0xF00D]);
        assert_eq!(a.pow([1, 0, 0, 0]), a);
    }

    #[test]
    fn pow_by_two_equals_square() {
        let a = fe([7, 0, 0, 0]);
        assert_eq!(a.pow([2, 0, 0, 0]), a * a);
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(Fp::ONE.inv(), Fp::ONE);
    }

    #[test]
    fn inv_of_neg_one_is_neg_one() {
        let neg_one = fe(p_minus(1));
        assert_eq!(neg_one.inv(), neg_one);
    }

    #[test]
    fn x_times_inv_x_is_one_small() {
        let a = fe([7, 0, 0, 0]);
        assert_eq!(a * a.inv(), Fp::ONE);
    }

    #[test]
    fn x_times_inv_x_is_one_multi_limb() {
        let a = fe([0xDEAD_BEEF_CAFE_F00D, 0xABCD, 0x1234, 0x5678]);
        assert_eq!(a * a.inv(), Fp::ONE);
    }

    #[test]
    fn inv_of_zero_is_zero() {
        assert_eq!(Fp::ZERO.inv(), Fp::ZERO);
    }

    #[test]
    fn from_bytes_round_trips_le() {
        let mut bytes = [0u8; 32];
        bytes[0] = 0x2E;
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
        assert_eq!(a.to_bytes_le(), bytes);
    }

    #[test]
    fn to_bytes_of_one_is_one() {
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(Fp::ONE.to_bytes_le(), expected);
    }

    #[test]
    fn from_u64_matches_from_limbs() {
        assert_eq!(Fp::from_u64(42), fe([42, 0, 0, 0]));
    }

    #[test]
    fn sqrt_of_zero_is_zero() {
        assert_eq!(Fp::ZERO.sqrt(), Fp::ZERO);
    }

    #[test]
    fn sqrt_of_one_squares_to_one() {
        let r = Fp::ONE.sqrt();
        assert_eq!(r * r, Fp::ONE);
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
        let x = fe([0xDEAD_BEEF_CAFE_F00D, 0xABCD, 0x1234, 0x5678]);
        let x2 = x * x;
        let r = x2.sqrt();
        assert_eq!(r * r, x2);
    }

    #[test]
    fn sqrt_of_non_residue_does_not_square_back() {
        let three = Fp::from_u64(3);
        let r = three.sqrt();
        assert_ne!(r * r, three);
    }

    type Fc = FieldElement<Csidh512FieldOrder>;

    #[test]
    fn csidh_sqrt_of_zero_is_zero() {
        assert_eq!(Fc::ZERO.sqrt(), Fc::ZERO);
    }

    #[test]
    fn csidh_sqrt_of_one_squares_to_one() {
        let r = Fc::ONE.sqrt();
        assert_eq!(r * r, Fc::ONE);
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
        assert_eq!(Csidh512FieldOrder::MODULUS[0] & 0b11, 0b11);
    }
}

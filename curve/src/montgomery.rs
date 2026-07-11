use core::fmt;
use core::hash::{Hash, Hasher};
use field::{
    Csidh512FieldOrder, ExtensionField, ExtensionFieldElement, Field, FieldElement,
    NonResidueMinusOne, Sqrt3Mod4,
};

use crate::Scalar;

pub trait MontgomeryCurve<F: Field>: fmt::Debug + Clone + Copy + PartialEq + Eq {
    fn a(&self) -> FieldElement<F>;
    fn b(&self) -> FieldElement<F>;

    fn a24(&self) -> FieldElement<F> {
        (self.a() + FieldElement::two()) * FieldElement::from_u64(4).inv()
    }

    fn x_double(&self, point: MontgomeryPoint<F>) -> MontgomeryPoint<F> {
        point.x_double(self.a24())
    }

    fn x_add(
        &self,
        p: MontgomeryPoint<F>,
        q: MontgomeryPoint<F>,
        p_minus_q: MontgomeryPoint<F>,
    ) -> MontgomeryPoint<F> {
        p.x_add(&q, &p_minus_q)
    }

    fn x_double_and_add(
        &self,
        p: MontgomeryPoint<F>,
        q: MontgomeryPoint<F>,
        p_minus_q: MontgomeryPoint<F>,
    ) -> (MontgomeryPoint<F>, MontgomeryPoint<F>) {
        p.x_double_and_add(&q, &p_minus_q, self.a24())
    }

    fn mult<G: Field>(&self, scalar: Scalar<G>, point: MontgomeryPoint<F>) -> MontgomeryPoint<F> {
        point.mult(scalar, self.a24())
    }

    fn j_invariant(&self) -> FieldElement<F> {
        let a2 = self.a() * self.a();
        let t = a2 - FieldElement::three();
        let num = FieldElement::from_u64(256) * t * t * t;
        let denom = a2 - FieldElement::from_u64(4);
        num * denom.inv()
    }

    fn is_on_curve(&self, x: FieldElement<F>) -> bool
    where
        F: Sqrt3Mod4,
    {
        let rhs = x * (x * x + self.a() * x + FieldElement::one());
        let y2 = rhs * self.b().inv();
        let y = y2.sqrt();
        y * y == y2
    }

    fn lift(&self, x: FieldElement<F>) -> Option<MontgomeryPoint<F>>
    where
        F: Sqrt3Mod4,
    {
        if self.is_on_curve(x) {
            Some(MontgomeryPoint::from_affine(x))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MontgomeryPoint<F: Field> {
    x: FieldElement<F>,
    z: FieldElement<F>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub enum MontgomeryPointRepresentation<F: Field> {
    Affine(FieldElement<F>),
    Infinity,
}

impl<F: Field> MontgomeryPoint<F> {
    pub fn infinity() -> Self {
        Self {
            x: FieldElement::one(),
            z: FieldElement::zero(),
        }
    }

    pub const fn from_projective_unchecked(x: FieldElement<F>, z: FieldElement<F>) -> Self {
        Self { x, z }
    }

    pub fn from_affine(x: FieldElement<F>) -> Self {
        Self::from_projective_unchecked(x, FieldElement::one())
    }

    pub fn x(&self) -> FieldElement<F> {
        self.x
    }

    pub fn z(&self) -> FieldElement<F> {
        self.z
    }

    pub fn is_infinity(&self) -> bool {
        self.z == FieldElement::zero()
    }

    pub fn representation(&self) -> MontgomeryPointRepresentation<F> {
        if self.is_infinity() {
            MontgomeryPointRepresentation::Infinity
        } else {
            MontgomeryPointRepresentation::Affine(self.x * self.z.inv())
        }
    }

    pub fn x_double(&self, a24: FieldElement<F>) -> Self {
        let a = self.x + self.z;
        let aa = a * a;
        let b = self.x - self.z;
        let bb = b * b;
        let x3 = aa * bb;
        let e = aa - bb;
        let z3 = e * (bb + a24 * e);
        Self { x: x3, z: z3 }
    }

    pub fn x_add(&self, other: &Self, p_minus_q: &Self) -> Self {
        let a = self.x + self.z;
        let b = self.x - self.z;
        let c = other.x + other.z;
        let d = other.x - other.z;
        let da = d * a;
        let bc = b * c;
        let sum = da + bc;
        let diff = da - bc;
        Self {
            x: p_minus_q.z * sum * sum,
            z: p_minus_q.x * diff * diff,
        }
    }

    pub fn x_double_and_add(
        &self,
        other: &Self,
        p_minus_q: &Self,
        a24: FieldElement<F>,
    ) -> (Self, Self) {
        (self.x_double(a24), self.x_add(other, p_minus_q))
    }

    pub fn mult<G: Field>(&self, scalar: Scalar<G>, a24: FieldElement<F>) -> Self {
        if self.is_infinity() {
            return Self::infinity();
        }
        let mut r0 = Self::infinity();
        let mut r1 = *self;
        let base = *self;
        let limbs = scalar.0.as_ref();
        for &limb in limbs.iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                let bit = (limb >> bit_idx) & 1 == 1;
                cswap(&mut r0, &mut r1, bit);
                let new_r1 = r0.x_add(&r1, &base);
                let new_r0 = r0.x_double(a24);
                r0 = new_r0;
                r1 = new_r1;
                cswap(&mut r0, &mut r1, bit);
            }
        }
        r0
    }
}

fn cswap<F: Field>(a: &mut MontgomeryPoint<F>, b: &mut MontgomeryPoint<F>, swap: bool) {
    if swap {
        core::mem::swap(a, b);
    }
}

impl<F: Field> PartialEq for MontgomeryPoint<F> {
    fn eq(&self, other: &Self) -> bool {
        let z1_zero = self.z == FieldElement::zero();
        let z2_zero = other.z == FieldElement::zero();
        if z1_zero || z2_zero {
            return z1_zero && z2_zero;
        }
        self.x * other.z == other.x * self.z
    }
}

impl<F: Field> Eq for MontgomeryPoint<F> {}

impl<F: Field> Hash for MontgomeryPoint<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.representation().hash(state);
    }
}

pub trait ExtensionMontgomeryCurve<E: ExtensionField>:
    fmt::Debug + Clone + Copy + PartialEq + Eq
{
    fn a(&self) -> ExtensionFieldElement<E>;
    fn b(&self) -> ExtensionFieldElement<E>;

    fn a24(&self) -> ExtensionFieldElement<E> {
        let two = ExtensionFieldElement::from_base(FieldElement::two());
        let four = ExtensionFieldElement::from_base(FieldElement::from_u64(4));
        (self.a() + two) * four.inv()
    }

    fn x_double(&self, point: ExtensionMontgomeryPoint<E>) -> ExtensionMontgomeryPoint<E> {
        point.x_double(self.a24())
    }

    fn x_add(
        &self,
        p: ExtensionMontgomeryPoint<E>,
        q: ExtensionMontgomeryPoint<E>,
        p_minus_q: ExtensionMontgomeryPoint<E>,
    ) -> ExtensionMontgomeryPoint<E> {
        p.x_add(&q, &p_minus_q)
    }

    fn x_double_and_add(
        &self,
        p: ExtensionMontgomeryPoint<E>,
        q: ExtensionMontgomeryPoint<E>,
        p_minus_q: ExtensionMontgomeryPoint<E>,
    ) -> (ExtensionMontgomeryPoint<E>, ExtensionMontgomeryPoint<E>) {
        p.x_double_and_add(&q, &p_minus_q, self.a24())
    }

    fn mult<G: Field>(
        &self,
        scalar: Scalar<G>,
        point: ExtensionMontgomeryPoint<E>,
    ) -> ExtensionMontgomeryPoint<E> {
        point.mult(scalar, self.a24())
    }

    fn j_invariant(&self) -> ExtensionFieldElement<E> {
        let a2 = self.a() * self.a();
        let three = ExtensionFieldElement::from_base(FieldElement::three());
        let four = ExtensionFieldElement::from_base(FieldElement::from_u64(4));
        let t = a2 - three;
        let num = ExtensionFieldElement::from_base(FieldElement::from_u64(256)) * t * t * t;
        let denom = a2 - four;
        num * denom.inv()
    }

    fn is_on_curve(&self, x: ExtensionFieldElement<E>) -> bool
    where
        E: NonResidueMinusOne,
        E::Base: Sqrt3Mod4,
    {
        let rhs = x * (x * x + self.a() * x + ExtensionFieldElement::one());
        let y2 = rhs * self.b().inv();
        let y = y2.sqrt();
        y * y == y2
    }

    fn lift(&self, x: ExtensionFieldElement<E>) -> Option<ExtensionMontgomeryPoint<E>>
    where
        E: NonResidueMinusOne,
        E::Base: Sqrt3Mod4,
    {
        if self.is_on_curve(x) {
            Some(ExtensionMontgomeryPoint::from_affine(x))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ExtensionMontgomeryPoint<E: ExtensionField> {
    x: ExtensionFieldElement<E>,
    z: ExtensionFieldElement<E>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub enum ExtensionMontgomeryPointRepresentation<E: ExtensionField> {
    Affine(ExtensionFieldElement<E>),
    Infinity,
}

impl<E: ExtensionField> ExtensionMontgomeryPoint<E> {
    pub fn infinity() -> Self {
        Self {
            x: ExtensionFieldElement::one(),
            z: ExtensionFieldElement::zero(),
        }
    }

    pub fn from_projective_unchecked(
        x: ExtensionFieldElement<E>,
        z: ExtensionFieldElement<E>,
    ) -> Self {
        Self { x, z }
    }

    pub fn from_affine(x: ExtensionFieldElement<E>) -> Self {
        Self::from_projective_unchecked(x, ExtensionFieldElement::one())
    }

    pub fn x(&self) -> ExtensionFieldElement<E> {
        self.x
    }

    pub fn z(&self) -> ExtensionFieldElement<E> {
        self.z
    }

    pub fn is_infinity(&self) -> bool {
        self.z == ExtensionFieldElement::zero()
    }

    pub fn representation(&self) -> ExtensionMontgomeryPointRepresentation<E> {
        if self.is_infinity() {
            ExtensionMontgomeryPointRepresentation::Infinity
        } else {
            ExtensionMontgomeryPointRepresentation::Affine(self.x * self.z.inv())
        }
    }

    pub fn x_double(&self, a24: ExtensionFieldElement<E>) -> Self {
        let a = self.x + self.z;
        let aa = a * a;
        let b = self.x - self.z;
        let bb = b * b;
        let x3 = aa * bb;
        let e = aa - bb;
        let z3 = e * (bb + a24 * e);
        Self { x: x3, z: z3 }
    }

    pub fn x_add(&self, other: &Self, p_minus_q: &Self) -> Self {
        let a = self.x + self.z;
        let b = self.x - self.z;
        let c = other.x + other.z;
        let d = other.x - other.z;
        let da = d * a;
        let bc = b * c;
        let sum = da + bc;
        let diff = da - bc;
        Self {
            x: p_minus_q.z * sum * sum,
            z: p_minus_q.x * diff * diff,
        }
    }

    pub fn x_double_and_add(
        &self,
        other: &Self,
        p_minus_q: &Self,
        a24: ExtensionFieldElement<E>,
    ) -> (Self, Self) {
        (self.x_double(a24), self.x_add(other, p_minus_q))
    }

    pub fn mult<G: Field>(&self, scalar: Scalar<G>, a24: ExtensionFieldElement<E>) -> Self {
        if self.is_infinity() {
            return Self::infinity();
        }
        let mut r0 = Self::infinity();
        let mut r1 = *self;
        let base = *self;
        let limbs = scalar.0.as_ref();
        for &limb in limbs.iter().rev() {
            for bit_idx in (0..u64::BITS).rev() {
                let bit = (limb >> bit_idx) & 1 == 1;
                ext_cswap(&mut r0, &mut r1, bit);
                let new_r1 = r0.x_add(&r1, &base);
                let new_r0 = r0.x_double(a24);
                r0 = new_r0;
                r1 = new_r1;
                ext_cswap(&mut r0, &mut r1, bit);
            }
        }
        r0
    }
}

fn ext_cswap<E: ExtensionField>(
    a: &mut ExtensionMontgomeryPoint<E>,
    b: &mut ExtensionMontgomeryPoint<E>,
    swap: bool,
) {
    if swap {
        core::mem::swap(a, b);
    }
}

impl<E: ExtensionField> PartialEq for ExtensionMontgomeryPoint<E> {
    fn eq(&self, other: &Self) -> bool {
        let z1_zero = self.z == ExtensionFieldElement::zero();
        let z2_zero = other.z == ExtensionFieldElement::zero();
        if z1_zero || z2_zero {
            return z1_zero && z2_zero;
        }
        self.x * other.z == other.x * self.z
    }
}

impl<E: ExtensionField> Eq for ExtensionMontgomeryPoint<E> {}

impl<E: ExtensionField> Hash for ExtensionMontgomeryPoint<E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.representation().hash(state);
    }
}

/// CSIDH-512 supersingular base curve E_0: y² = x³ + x (A = 0, B = 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, std::hash::Hash)]
pub struct Csidh512BaseCurve;

impl MontgomeryCurve<Csidh512FieldOrder> for Csidh512BaseCurve {
    fn a(&self) -> FieldElement<Csidh512FieldOrder> {
        FieldElement::zero()
    }
    fn b(&self) -> FieldElement<Csidh512FieldOrder> {
        FieldElement::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::MontgomeryParams;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct Fp13;

    impl Field for Fp13 {
        type Limbs = [u64; 1];
        const MODULUS: [u64; 1] = [13];
        const PARAMS: MontgomeryParams<[u64; 1]> = MontgomeryParams::new([9], 0xB13B13B13B13B13B);
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    struct Fr7;

    impl Field for Fr7 {
        type Limbs = [u64; 1];
        const MODULUS: [u64; 1] = [7];
        const PARAMS: MontgomeryParams<[u64; 1]> = MontgomeryParams::new([4], 0x9249249249249249);
    }

    type Fe13 = FieldElement<Fp13>;
    type Pt13 = MontgomeryPoint<Fp13>;
    type Sc = Scalar<Fr7>;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct TinyMont;

    impl MontgomeryCurve<Fp13> for TinyMont {
        fn a(&self) -> Fe13 {
            Fe13::zero()
        }
        fn b(&self) -> Fe13 {
            Fe13::one()
        }
    }

    fn fe(x: u64) -> Fe13 {
        Fe13::from_u64(x)
    }

    fn pt(x: u64) -> Pt13 {
        Pt13::from_affine(fe(x))
    }

    #[test]
    fn a24_of_e0_is_one_half() {
        assert_eq!(TinyMont.a24(), fe(7));
    }

    #[test]
    fn x_double_of_g_matches_2g() {
        let g = pt(2);
        assert_eq!(TinyMont.x_double(g), pt(9));
    }

    #[test]
    fn x_add_matches_hand_computation() {
        let g = pt(2);
        let two_g = pt(9);
        assert_eq!(TinyMont.x_add(two_g, g, g), pt(6));
    }

    #[test]
    fn x_add_is_symmetric_in_p_and_q() {
        let g = pt(2);
        let two_g = pt(9);
        let a = TinyMont.x_add(two_g, g, g);
        let b = TinyMont.x_add(g, two_g, g);
        assert_eq!(a, b);
    }

    #[test]
    fn x_add_infinity_and_p_with_diff_p_is_p() {
        let g = pt(2);
        assert_eq!(TinyMont.x_add(Pt13::infinity(), g, g), g);
    }

    #[test]
    fn x_double_of_infinity_is_infinity() {
        assert!(TinyMont.x_double(Pt13::infinity()).is_infinity());
    }

    #[test]
    fn x_double_of_two_torsion_is_infinity() {
        let two_torsion = pt(8);
        assert!(TinyMont.x_double(two_torsion).is_infinity());
    }

    #[test]
    fn x_double_and_add_matches_separate_ops() {
        let g = pt(2);
        let two_g = pt(9);
        let (dbl_g, add) = TinyMont.x_double_and_add(g, two_g, g);
        assert_eq!(dbl_g, TinyMont.x_double(g));
        assert_eq!(add, TinyMont.x_add(g, two_g, g));
    }

    #[test]
    fn mult_by_zero_is_infinity() {
        assert!(TinyMont.mult(Sc::from_u64(0), pt(2)).is_infinity());
    }

    #[test]
    fn mult_by_one_is_identity() {
        assert_eq!(TinyMont.mult(Sc::from_u64(1), pt(2)), pt(2));
    }

    #[test]
    fn mult_by_two_matches_x_double() {
        assert_eq!(TinyMont.mult(Sc::from_u64(2), pt(2)), pt(9));
    }

    #[test]
    fn mult_by_three_matches_hand_computation() {
        assert_eq!(TinyMont.mult(Sc::from_u64(3), pt(2)), pt(6));
    }

    #[test]
    fn mult_by_four_matches_hand_computation() {
        assert_eq!(TinyMont.mult(Sc::from_u64(4), pt(2)), pt(4));
    }

    #[test]
    fn mult_by_five_lands_on_two_torsion() {
        let result = TinyMont.mult(Sc::from_u64(5), pt(2));
        assert_eq!(result, pt(8));
    }

    #[test]
    fn mult_by_group_order_is_infinity() {
        assert!(TinyMont.mult(Sc::from_u64(10), pt(2)).is_infinity());
    }

    #[test]
    fn mult_wraps_symmetrically() {
        for k in 1..10u64 {
            let a = TinyMont.mult(Sc::from_u64(k), pt(2));
            let b = TinyMont.mult(Sc::from_u64(10 - k), pt(2));
            assert_eq!(a, b);
        }
    }

    #[test]
    fn mult_on_infinity_is_infinity() {
        assert!(
            TinyMont
                .mult(Sc::from_u64(12345), Pt13::infinity())
                .is_infinity()
        );
    }

    #[test]
    fn j_invariant_of_e0_matches_1728() {
        assert_eq!(TinyMont.j_invariant(), fe(1728));
    }

    #[test]
    fn representation_of_infinity() {
        assert_eq!(
            Pt13::infinity().representation(),
            MontgomeryPointRepresentation::Infinity
        );
    }

    #[test]
    fn representation_of_scaled_point_normalizes() {
        let scaled = Pt13::from_projective_unchecked(fe(4), fe(2));
        assert_eq!(
            scaled.representation(),
            MontgomeryPointRepresentation::Affine(fe(2))
        );
    }

    #[test]
    fn equality_respects_projective_scaling() {
        let a = Pt13::from_projective_unchecked(fe(2), fe(1));
        let b = Pt13::from_projective_unchecked(fe(4), fe(2));
        assert_eq!(a, b);
    }

    #[test]
    fn csidh512_e0_has_j_1728() {
        assert_eq!(
            Csidh512BaseCurve.j_invariant(),
            FieldElement::<Csidh512FieldOrder>::from_u64(1728)
        );
    }

    #[test]
    fn csidh512_e0_a24_is_half() {
        let a24 = Csidh512BaseCurve.a24();
        let two = FieldElement::<Csidh512FieldOrder>::two();
        let four = FieldElement::<Csidh512FieldOrder>::from_u64(4);
        assert_eq!(a24 * four, two);
    }

    #[test]
    fn csidh512_is_on_curve_zero() {
        assert!(Csidh512BaseCurve.is_on_curve(FieldElement::zero()));
    }

    #[test]
    fn csidh512_is_on_curve_x_one_is_false() {
        assert!(!Csidh512BaseCurve.is_on_curve(FieldElement::one()));
    }

    #[test]
    fn csidh512_lift_zero_gives_two_torsion() {
        let p = Csidh512BaseCurve
            .lift(FieldElement::zero())
            .expect("x=0 is on E_0");
        assert_eq!(
            p.representation(),
            MontgomeryPointRepresentation::Affine(FieldElement::zero())
        );
    }

    #[test]
    fn csidh512_lift_x_one_gives_none() {
        assert!(Csidh512BaseCurve.lift(FieldElement::one()).is_none());
    }

    use field::Csidh512Fp2;

    type F2 = ExtensionFieldElement<Csidh512Fp2>;
    type ExtPt = ExtensionMontgomeryPoint<Csidh512Fp2>;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct Csidh512ExtBaseCurve;

    impl ExtensionMontgomeryCurve<Csidh512Fp2> for Csidh512ExtBaseCurve {
        fn a(&self) -> F2 {
            F2::zero()
        }
        fn b(&self) -> F2 {
            F2::one()
        }
    }

    fn ext_from_u64(x: u64) -> F2 {
        F2::from_base(FieldElement::from_u64(x))
    }

    #[test]
    fn ext_a24_of_e0_over_fp2_matches_half() {
        let a24 = Csidh512ExtBaseCurve.a24();
        let two = ext_from_u64(2);
        let four = ext_from_u64(4);
        assert_eq!(a24 * four, two);
    }

    #[test]
    fn ext_j_invariant_of_e0_over_fp2_is_1728() {
        assert_eq!(Csidh512ExtBaseCurve.j_invariant(), ext_from_u64(1728));
    }

    #[test]
    fn ext_x_double_of_infinity_is_infinity() {
        assert!(
            Csidh512ExtBaseCurve
                .x_double(ExtPt::infinity())
                .is_infinity()
        );
    }

    #[test]
    fn ext_mult_by_zero_is_infinity() {
        let p = ExtPt::from_affine(ext_from_u64(5));
        assert!(Csidh512ExtBaseCurve.mult(Sc::from_u64(0), p).is_infinity());
    }

    #[test]
    fn ext_mult_by_one_is_identity() {
        let p = ExtPt::from_affine(ext_from_u64(5));
        assert_eq!(Csidh512ExtBaseCurve.mult(Sc::from_u64(1), p), p);
    }

    #[test]
    fn ext_mult_by_two_matches_x_double() {
        let x = F2::new(FieldElement::from_u64(3), FieldElement::from_u64(7));
        let p = ExtPt::from_affine(x);
        let via_mult = Csidh512ExtBaseCurve.mult(Sc::from_u64(2), p);
        let via_double = Csidh512ExtBaseCurve.x_double(p);
        assert_eq!(via_mult, via_double);
    }

    #[test]
    fn ext_mult_matches_base_on_rational_point() {
        let x_base = FieldElement::<Csidh512FieldOrder>::from_u64(9);
        let p_base = MontgomeryPoint::<Csidh512FieldOrder>::from_affine(x_base);
        let p_ext = ExtPt::from_affine(F2::from_base(x_base));
        for k in 1..8u64 {
            let base_result = Csidh512BaseCurve.mult(Sc::from_u64(k), p_base);
            let ext_result = Csidh512ExtBaseCurve.mult(Sc::from_u64(k), p_ext);
            match (base_result.representation(), ext_result.representation()) {
                (
                    MontgomeryPointRepresentation::Affine(xb),
                    ExtensionMontgomeryPointRepresentation::Affine(xe),
                ) => {
                    assert_eq!(xe, F2::from_base(xb), "k={k}");
                }
                (
                    MontgomeryPointRepresentation::Infinity,
                    ExtensionMontgomeryPointRepresentation::Infinity,
                ) => {}
                _ => panic!("representation mismatch at k={k}"),
            }
        }
    }

    #[test]
    fn ext_x_add_symmetric() {
        let x_a = F2::new(FieldElement::from_u64(3), FieldElement::from_u64(1));
        let p = ExtPt::from_affine(x_a);
        let two_p = Csidh512ExtBaseCurve.x_double(p);
        let a = Csidh512ExtBaseCurve.x_add(two_p, p, p);
        let b = Csidh512ExtBaseCurve.x_add(p, two_p, p);
        assert_eq!(a, b);
    }

    #[test]
    fn ext_mult_by_seven_matches_iterated_add() {
        let x_a = F2::new(FieldElement::from_u64(3), FieldElement::from_u64(1));
        let p = ExtPt::from_affine(x_a);
        let two_p = Csidh512ExtBaseCurve.x_double(p);
        let three_p = Csidh512ExtBaseCurve.x_add(two_p, p, p);
        let four_p = Csidh512ExtBaseCurve.x_add(three_p, p, two_p);
        let five_p = Csidh512ExtBaseCurve.x_add(four_p, p, three_p);
        let six_p = Csidh512ExtBaseCurve.x_add(five_p, p, four_p);
        let seven_p = Csidh512ExtBaseCurve.x_add(six_p, p, five_p);
        assert_eq!(Csidh512ExtBaseCurve.mult(Sc::from_u64(7), p), seven_p);
    }
}

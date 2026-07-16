import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CartanBasis
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantitative Cartan Symanzik restoration for the Wilson plaquette action

This module starts from the actual normalized `SU(2)` Wilson plaquette
potential on the exact Cartan link-field chart.  It proves its eighth
amplitude jet and a quantitative small-field comparison with the continuum
quadratic density.  Orthogonal invariance of the latter is proved from the
literal rank-two tensor action.

The resulting theorem is a tree-level, constant-Cartan statement.  It does
not assert quantum `O(4)` restoration, control an interacting continuum
measure, or enumerate the full noncommutative `F,D` quotient.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Topology

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicWilsonSymanzikRestoration

open SU2LatticeFDCensusNoGo
open SU2WilsonBlockPilot
open HypercubicDimension16CartanCensus
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

/-! ## The normalized actual Wilson density -/

/-- The sum of the six actual Wilson plaquette potentials at the origin. -/
def su2OriginWilsonPlaquetteSum (U : BlockLinkField) : ℝ :=
  ∑ plane : OrientedPlane,
    plaquettePotential U (originPlaquette plane)

/-- Four-dimensional tree-level normalization of the local Wilson action
density.  The link field is the exact `SU(2)` Cartan chart at plaquette angle
`a² F`. -/
def normalizedSU2CartanWilsonDensity
    (a : ℝ) (F : CartanCurvature) : ℝ :=
  (2 / a ^ 4) *
    su2OriginWilsonPlaquetteSum (cartanLinkChart (a ^ 2) F)

/-- Closed scalar form of the normalized actual density. -/
def normalizedCartanWilsonDensity
    (a : ℝ) (F : CartanCurvature) : ℝ :=
  ∑ plane : OrientedPlane,
    (2 / a ^ 4) *
      (1 - Real.cos (a ^ 2 * F plane.first plane.second))

theorem normalizedSU2CartanWilsonDensity_eq
    (a : ℝ) (F : CartanCurvature) :
    normalizedSU2CartanWilsonDensity a F =
      normalizedCartanWilsonDensity a F := by
  unfold normalizedSU2CartanWilsonDensity
    normalizedCartanWilsonDensity su2OriginWilsonPlaquetteSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro plane _
  rw [plaquettePotential_cartanLinkChart]

/-- The continuum quadratic density on the six independent components of an
antisymmetric two-form. -/
def cartanQuadraticDensity (F : CartanCurvature) : ℝ :=
  ∑ plane : OrientedPlane, F plane.first plane.second ^ 2

/-! ## Exact dimension-sixteen jet -/

/-- The eighth amplitude derivative of one normalized Wilson plaquette.  Its
coefficient is derived directly from cosine and the four-dimensional
normalization. -/
theorem normalizedWilsonPlaquette_eighthJet
    (a x : ℝ) (ha : a ≠ 0) :
    iteratedDeriv 8
        (fun t : ℝ =>
          (2 / a ^ 4) * (1 - Real.cos (a ^ 2 * (t * x)))) 0 =
      -2 * a ^ 12 * x ^ 8 := by
  have hscale (t : ℝ) : a ^ 2 * (t * x) = (a ^ 2 * x) * t := by ring
  simp_rw [hscale]
  rw [iteratedDeriv_const_mul_field]
  have hcos := iteratedDeriv_comp_const_mul
    (n := 8) Real.contDiff_cos (a ^ 2 * x)
  have hcos0 := congrFun hcos 0
  simp only [show (8 : ℕ) = 2 * 4 by norm_num,
    Real.iteratedDeriv_even_cos] at hcos0
  norm_num at hcos0
  have hcos0' :
      iteratedDeriv 8 (fun t : ℝ => Real.cos ((a ^ 2 * x) * t)) 0 =
        (a ^ 2 * x) ^ 8 := by
    simpa using hcos0
  rw [iteratedDeriv_const_sub (n := 8) (x := (0 : ℝ))
    (f := fun t : ℝ => Real.cos ((a ^ 2 * x) * t)) (by norm_num) 1]
  simp only [iteratedDeriv_neg, hcos0']
  field_simp

/-- The exact actual local Wilson density has a pure componentwise-octic
eighth jet. -/
theorem normalizedSU2CartanWilsonDensity_eighthJet
    (a : ℝ) (ha : a ≠ 0) (F : CartanCurvature) :
    iteratedDeriv 8
        (fun t : ℝ =>
          normalizedSU2CartanWilsonDensity a (fun mu nu =>
            t * F mu nu)) 0 =
      -2 * a ^ 12 *
        (∑ plane : OrientedPlane,
          F plane.first plane.second ^ 8) := by
  have hfun :
      (fun t : ℝ =>
        normalizedSU2CartanWilsonDensity a (fun mu nu => t * F mu nu)) =
      (fun t : ℝ =>
        ∑ plane : OrientedPlane,
          (2 / a ^ 4) *
            (1 - Real.cos (a ^ 2 *
              (t * F plane.first plane.second)))) := by
    funext t
    rw [normalizedSU2CartanWilsonDensity_eq]
    rfl
  rw [hfun, iteratedDeriv_fun_sum]
  · simp_rw [normalizedWilsonPlaquette_eighthJet a _ ha]
    rw [← Finset.mul_sum]
  · intro plane _
    fun_prop

/-! ### Coordinates on the honest 1,287-element octic carrier -/

/-- A pure eighth power in the standard unpadded monomial carrier. -/
def pureOcticMonomial (plane : OrientedPlane) : OcticMonomial :=
  octicOfPlanes plane plane plane plane plane plane plane plane

def IsPureOcticMonomial (monomial : OcticMonomial) : Prop :=
  ∃ plane : OrientedPlane, monomial = pureOcticMonomial plane

instance (monomial : OcticMonomial) :
    Decidable (IsPureOcticMonomial monomial) := by
  unfold IsPureOcticMonomial
  infer_instance

theorem octicRepresentative_zero_eq_pure :
    octicRepresentative 0 = pureOcticMonomial 5 := by
  rfl

theorem pureOcticMonomial_act
    (h : Hypercubic4) (plane : OrientedPlane) :
    (pureOcticMonomial plane).act h =
      pureOcticMonomial (planeEquiv h plane) := by
  apply Sym.ext
  simp [pureOcticMonomial, octicOfPlanes, OcticMonomial.act, Sym.map,
    Sym.ofVector, Sym.toMultiset]

/-- Every coordinate two-plane is reached from plane `23` by the literal
hypercubic action.  This finite transitivity check is on the standard action,
not on an invented orbit relation. -/
def pureOcticTransportCode : OrientedPlane → Fin 24
  | 0 => 16
  | 1 => 10
  | 2 => 8
  | 3 => 4
  | 4 => 2
  | 5 => 0

theorem pureOcticMonomial_reachable (plane : OrientedPlane) :
    InSignedOcticOrbit (octicRepresentative 0)
      (pureOcticMonomial plane) := by
  refine ⟨decodeHypercubic (pureOcticTransportCode plane) 0, ?_⟩
  fin_cases plane <;> decide

theorem representativeZeroOrbit_iff_pure
    (monomial : OcticMonomial) :
    InSignedOcticOrbit (octicRepresentative 0) monomial ↔
      IsPureOcticMonomial monomial := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨planeEquiv h 5, ?_⟩
    rw [← hh, octicRepresentative_zero_eq_pure,
      pureOcticMonomial_act]
  · rintro ⟨plane, rfl⟩
    exact pureOcticMonomial_reachable plane

theorem octicRepresentative_zero_tensorSign
    (h : Hypercubic4) :
    (octicRepresentative 0).tensorSign h = 1 := by
  rw [octicRepresentative_zero_eq_pure]
  rcases planeTensorSign_eq_one_or_neg_one h 5 with hsign | hsign <;>
    simp [pureOcticMonomial, octicOfPlanes, OcticMonomial.tensorSign,
      Sym.ofVector, Sym.toMultiset, hsign]

/-- The first certified signed-orbit basis vector is exactly the indicator of
the six pure eighth powers. -/
theorem octicOrbitBasis_zero_eq_pureIndicator
    (monomial : OcticMonomial) :
    octicOrbitBasis 0 monomial =
      if IsPureOcticMonomial monomial then 1 else 0 := by
  classical
  by_cases hpure : IsPureOcticMonomial monomial
  · obtain ⟨h, hh⟩ :=
      (representativeZeroOrbit_iff_pure monomial).mpr hpure
    rw [octicOrbitBasis_of_transport 0 monomial h hh]
    simp [octicRepresentative_zero_tensorSign, hpure]
  · have hnotOrbit :
        ¬InSignedOcticOrbit (octicRepresentative 0) monomial :=
      mt (representativeZeroOrbit_iff_pure monomial).mp hpure
    rw [octicOrbitBasis_eq_zero_of_not_orbit 0 monomial hnotOrbit]
    simp [hpure]

/-- Standard-monomial coefficients of the actual eighth amplitude jet.  The
support and scalar come from the direct cosine derivative above. -/
def actualWilsonOcticJetCoefficient
    (a : ℝ) (monomial : OcticMonomial) : ℝ :=
  if IsPureOcticMonomial monomial then -2 * a ^ 12 else 0

theorem actualWilsonOcticJetCoefficient_eq_basis
    (a : ℝ) (monomial : OcticMonomial) :
    actualWilsonOcticJetCoefficient a monomial =
      (-2 * a ^ 12) * (octicOrbitBasis 0 monomial : ℝ) := by
  rw [octicOrbitBasis_zero_eq_pureIndicator]
  by_cases hpure : IsPureOcticMonomial monomial <;>
    simp [actualWilsonOcticJetCoefficient, hpure]

/-- The direct eighth-derivative formula, now written using the coefficients
on the standard pure monomials. -/
theorem normalizedSU2CartanWilsonDensity_eighthJet_as_octicCoefficients
    (a : ℝ) (ha : a ≠ 0) (F : CartanCurvature) :
    iteratedDeriv 8
        (fun t : ℝ =>
          normalizedSU2CartanWilsonDensity a (fun mu nu =>
            t * F mu nu)) 0 =
      ∑ plane : OrientedPlane,
        actualWilsonOcticJetCoefficient a (pureOcticMonomial plane) *
          F plane.first plane.second ^ 8 := by
  rw [normalizedSU2CartanWilsonDensity_eighthJet a ha F,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro plane _
  simp [actualWilsonOcticJetCoefficient, IsPureOcticMonomial]

/-- Representative evaluation is the exact real extension of the certified
octic dual chart. -/
def honestOcticDualReal (coordinate : Fin 17)
    (coefficients : OcticMonomial → ℝ) : ℝ :=
  coefficients (octicRepresentative coordinate)

theorem octicRepresentative_isPure_iff (coordinate : Fin 17) :
    IsPureOcticMonomial (octicRepresentative coordinate) ↔
      coordinate = 0 := by
  constructor
  · intro hpure
    by_contra hcoordinate
    have hbasisOne :
        octicOrbitBasis 0 (octicRepresentative coordinate) = 1 := by
      rw [octicOrbitBasis_zero_eq_pureIndicator]
      simp [hpure]
    have hbasisZero :
        octicOrbitBasis 0 (octicRepresentative coordinate) = 0 := by
      rw [octicOrbitBasis_at_representative]
      simp [Ne.symm hcoordinate]
    rw [hbasisZero] at hbasisOne
    norm_num at hbasisOne
  · intro hcoordinate
    subst coordinate
    exact ⟨5, octicRepresentative_zero_eq_pure⟩

/-- Actual eighth-jet coordinates on the honest basis: only coordinate zero
is populated. -/
theorem honestOcticDualReal_actualWilsonOcticJetCoefficient
    (a : ℝ) (coordinate : Fin 17) :
    honestOcticDualReal coordinate
        (actualWilsonOcticJetCoefficient a) =
      if coordinate = 0 then -2 * a ^ 12 else 0 := by
  unfold honestOcticDualReal actualWilsonOcticJetCoefficient
  by_cases hcoordinate : coordinate = 0
  · rw [if_pos hcoordinate,
      if_pos ((octicRepresentative_isPure_iff coordinate).2 hcoordinate)]
  · rw [if_neg hcoordinate,
      if_neg (mt (octicRepresentative_isPure_iff coordinate).1 hcoordinate)]

/-- Taylor/Symanzik coefficient obtained by dividing the eighth jet by `8!`.
The exact populated coordinate is `-a¹² / 20160`. -/
def actualWilsonDimension16SymanzikCoordinate
    (a : ℝ) (coordinate : Fin 17) : ℝ :=
  honestOcticDualReal coordinate
    (actualWilsonOcticJetCoefficient a) / (Nat.factorial 8 : ℝ)

theorem actualWilsonDimension16SymanzikCoordinate_eq
    (a : ℝ) (coordinate : Fin 17) :
    actualWilsonDimension16SymanzikCoordinate a coordinate =
      if coordinate = 0 then -(a ^ 12) / 20160 else 0 := by
  unfold actualWilsonDimension16SymanzikCoordinate
  rw [honestOcticDualReal_actualWilsonOcticJetCoefficient]
  norm_num [Nat.factorial]
  split_ifs <;> ring

/-- Exact dimension-sixteen Wilson-coordinate packet on the honest Cartan
carrier.  It combines the actual link-field jet, its derived coordinate, and
the independently certified sharp conditioning constant. -/
theorem actualWilsonDimension16_packet
    (a : ℝ) (ha : a ≠ 0) (F : CartanCurvature) :
    (iteratedDeriv 8
        (fun t : ℝ =>
          normalizedSU2CartanWilsonDensity a (fun mu nu =>
            t * F mu nu)) 0 =
      -2 * a ^ 12 *
        (∑ plane : OrientedPlane,
          F plane.first plane.second ^ 8)) ∧
    (∀ coordinate : Fin 17,
      actualWilsonDimension16SymanzikCoordinate a coordinate =
        if coordinate = 0 then -(a ^ 12) / 20160 else 0) ∧
    octicConditioningConstant = 1 := by
  exact ⟨normalizedSU2CartanWilsonDensity_eighthJet a ha F,
    actualWilsonDimension16SymanzikCoordinate_eq a, rfl⟩

/-! ## Quantitative small-field estimate -/

/-- One normalized plaquette differs from its quadratic continuum term by at
most the explicit fourth-order cosine remainder. -/
theorem normalizedWilsonPlaquette_error
    {a x : ℝ} (ha : 0 < a) (hsmall : |a ^ 2 * x| ≤ 1) :
    |(2 / a ^ 4) * (1 - Real.cos (a ^ 2 * x)) - x ^ 2| ≤
      (5 / 48 : ℝ) * a ^ 4 * |x| ^ 4 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hfactor : 0 ≤ 2 / a ^ 4 := by positivity
  have hremainder := Real.cos_bound hsmall
  have hrearrange :
      (2 / a ^ 4) * (1 - Real.cos (a ^ 2 * x)) - x ^ 2 =
        -(2 / a ^ 4) *
          (Real.cos (a ^ 2 * x) -
            (1 - (a ^ 2 * x) ^ 2 / 2)) := by
    field_simp
    ring
  rw [hrearrange, abs_mul, abs_neg, abs_of_nonneg hfactor]
  calc
    (2 / a ^ 4) *
        |Real.cos (a ^ 2 * x) - (1 - (a ^ 2 * x) ^ 2 / 2)| ≤
      (2 / a ^ 4) * (|a ^ 2 * x| ^ 4 * (5 / 96)) :=
        mul_le_mul_of_nonneg_left hremainder hfactor
    _ = (5 / 48 : ℝ) * a ^ 4 * |x| ^ 4 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
      field_simp
      ring

/-- Uniform six-plaquette comparison with the continuum quadratic density. -/
theorem normalizedCartanWilsonDensity_error
    {a M : ℝ} (ha : 0 < a) (_hM : 0 ≤ M)
    (F : CartanCurvature)
    (hcomponent : ∀ plane : OrientedPlane,
      |F plane.first plane.second| ≤ M)
    (hsmall : ∀ plane : OrientedPlane,
      |a ^ 2 * F plane.first plane.second| ≤ 1) :
    |normalizedCartanWilsonDensity a F - cartanQuadraticDensity F| ≤
      (5 / 8 : ℝ) * a ^ 4 * M ^ 4 := by
  rw [normalizedCartanWilsonDensity, cartanQuadraticDensity,
    ← Finset.sum_sub_distrib]
  calc
    |∑ plane : OrientedPlane,
        ((2 / a ^ 4) *
          (1 - Real.cos (a ^ 2 * F plane.first plane.second)) -
            F plane.first plane.second ^ 2)| ≤
      ∑ plane : OrientedPlane,
        |(2 / a ^ 4) *
          (1 - Real.cos (a ^ 2 * F plane.first plane.second)) -
            F plane.first plane.second ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _plane : OrientedPlane,
        (5 / 48 : ℝ) * a ^ 4 * M ^ 4 := by
      apply Finset.sum_le_sum
      intro plane _
      calc
        |(2 / a ^ 4) *
            (1 - Real.cos (a ^ 2 * F plane.first plane.second)) -
              F plane.first plane.second ^ 2| ≤
            (5 / 48 : ℝ) * a ^ 4 *
              |F plane.first plane.second| ^ 4 :=
          normalizedWilsonPlaquette_error ha (hsmall plane)
        _ ≤ (5 / 48 : ℝ) * a ^ 4 * M ^ 4 := by
          gcongr
          exact hcomponent plane
    _ = (5 / 8 : ℝ) * a ^ 4 * M ^ 4 := by
      simp
      ring

/-- The same six-plaquette estimate on the actual link-field observable. -/
theorem normalizedSU2CartanWilsonDensity_error
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (F : CartanCurvature)
    (hcomponent : ∀ plane : OrientedPlane,
      |F plane.first plane.second| ≤ M)
    (hsmall : ∀ plane : OrientedPlane,
      |a ^ 2 * F plane.first plane.second| ≤ 1) :
    |normalizedSU2CartanWilsonDensity a F - cartanQuadraticDensity F| ≤
      (5 / 8 : ℝ) * a ^ 4 * M ^ 4 := by
  rw [normalizedSU2CartanWilsonDensity_eq]
  exact normalizedCartanWilsonDensity_error ha hM F hcomponent hsmall

/-- Quantitative scaling limit along any positive lattice-spacing net tending
to zero.  The fixed component bound supplies the eventually valid small-field
chart; the rate is the explicit `O(a⁴)` estimate above. -/
theorem normalizedSU2CartanWilsonDensity_tendsto_quadratic
    {ι : Type*} {l : Filter ι} (a : ι → ℝ)
    (ha : Filter.Tendsto a l (𝓝 0))
    (hpositive : ∀ᶠ i in l, 0 < a i)
    {M : ℝ} (hM : 0 ≤ M) (F : CartanCurvature)
    (hcomponent : ∀ plane : OrientedPlane,
      |F plane.first plane.second| ≤ M) :
    Filter.Tendsto
      (fun i => normalizedSU2CartanWilsonDensity (a i) F) l
      (𝓝 (cartanQuadraticDensity F)) := by
  have hscaleT : Filter.Tendsto (fun i => a i ^ 2 * M) l (𝓝 0) := by
    simpa using Filter.Tendsto.mul_const M (ha.pow 2)
  have hscale : ∀ᶠ i in l, a i ^ 2 * M ≤ 1 :=
    ((tendsto_order.1 hscaleT).2 1 zero_lt_one).mono fun _ hi => hi.le
  have hboundT :
      Filter.Tendsto (fun i => (5 / 8 : ℝ) * a i ^ 4 * M ^ 4) l
        (𝓝 0) := by
    have ht : Filter.Tendsto
        (fun i => ((5 / 8 : ℝ) * M ^ 4) * a i ^ 4) l (𝓝 0) := by
      simpa using
        Filter.Tendsto.const_mul ((5 / 8 : ℝ) * M ^ 4) (ha.pow 4)
    exact ht.congr' (Filter.Eventually.of_forall fun i => by ring)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have habsT : Filter.Tendsto
      (fun i =>
        |normalizedSU2CartanWilsonDensity (a i) F -
          cartanQuadraticDensity F|) l (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [hpositive, hscale] with i hpos hsmallScale
      exact normalizedSU2CartanWilsonDensity_error hpos hM F hcomponent
        (fun plane => by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (a i))]
          exact (mul_le_mul_of_nonneg_left (hcomponent plane)
            (sq_nonneg (a i))).trans hsmallScale)
    · exact hboundT
  simpa [Real.norm_eq_abs] using habsT

/-! ## Orthogonal invariance of the continuum term -/

/-- The coordinate-free Frobenius presentation of the two-form quadratic
density. -/
abbrev cartanMatrix (F : CartanCurvature) :
    Matrix (Fin 4) (Fin 4) ℝ := F

def cartanFrobeniusDensity (F : CartanCurvature) : ℝ :=
  (1 / 2 : ℝ) *
    Matrix.trace ((cartanMatrix F).transpose * cartanMatrix F)

/-- On an antisymmetric curvature tensor, the six-plane quadratic density is
exactly half its Frobenius square. -/
theorem cartanQuadraticDensity_eq_frobenius
    (F : CartanCurvature)
    (hantisymmetric : ∀ mu nu, F mu nu = -F nu mu) :
    cartanQuadraticDensity F = cartanFrobeniusDensity F := by
  have h00 : F 0 0 = 0 := by
    have h := hantisymmetric 0 0
    linarith
  have h11 : F 1 1 = 0 := by
    have h := hantisymmetric 1 1
    linarith
  have h22 : F 2 2 = 0 := by
    have h := hantisymmetric 2 2
    linarith
  have h33 : F 3 3 = 0 := by
    have h := hantisymmetric 3 3
    linarith
  have h10 := hantisymmetric 1 0
  have h20 := hantisymmetric 2 0
  have h30 := hantisymmetric 3 0
  have h21 := hantisymmetric 2 1
  have h31 := hantisymmetric 3 1
  have h32 := hantisymmetric 3 2
  simp [cartanQuadraticDensity, cartanFrobeniusDensity, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_succ, OrientedPlane.first,
    OrientedPlane.second, h00, h11, h22, h33, h10, h20, h30, h21, h31,
    h32]
  ring

/-- The literal double-sum tensor action is matrix conjugation by `R` and
`Rᵀ`. -/
theorem rotateCurvature_eq_matrix_mul
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature) :
    rotateCurvature R F = R * cartanMatrix F * R.transpose := by
  funext mu nu
  simp only [rotateCurvature, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro beta _
  apply Finset.sum_congr rfl
  intro alpha _
  ring

/-- Orthogonal tensor rotation preserves the Frobenius density. -/
theorem cartanFrobeniusDensity_rotate
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature)
    (horthogonal : R.transpose * R = 1) :
    cartanFrobeniusDensity (rotateCurvature R F) =
      cartanFrobeniusDensity F := by
  rw [rotateCurvature_eq_matrix_mul]
  unfold cartanFrobeniusDensity
  congr 1
  calc
    Matrix.trace
        ((R * cartanMatrix F * R.transpose).transpose *
          (R * cartanMatrix F * R.transpose)) =
      Matrix.trace (R *
        ((cartanMatrix F).transpose * cartanMatrix F) * R.transpose) := by
        congr 1
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc R.transpose R, horthogonal, one_mul]
    _ = Matrix.trace (R.transpose * R *
        ((cartanMatrix F).transpose * cartanMatrix F)) := by
      exact Matrix.trace_mul_cycle R
        ((cartanMatrix F).transpose * cartanMatrix F) R.transpose
    _ = Matrix.trace ((cartanMatrix F).transpose * cartanMatrix F) := by
      rw [horthogonal, one_mul]

/-- Orthogonal tensor rotation preserves antisymmetry. -/
theorem rotateCurvature_antisymmetric
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature)
    (hantisymmetric : ∀ mu nu, F mu nu = -F nu mu) :
    ∀ mu nu,
      rotateCurvature R F mu nu = -rotateCurvature R F nu mu := by
  have htranspose :
      (cartanMatrix F).transpose = -(cartanMatrix F) := by
    ext mu nu
    simp [Matrix.transpose_apply, hantisymmetric nu mu]
  have hrotTranspose :
      (R * cartanMatrix F * R.transpose).transpose =
        -(R * cartanMatrix F * R.transpose) := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, htranspose]
  intro mu nu
  rw [rotateCurvature_eq_matrix_mul]
  have hentry := congrFun (congrFun hrotTranspose nu) mu
  simpa [Matrix.transpose_apply] using hentry

/-- The continuum quadratic density is invariant under every orthogonal
rotation, with no invariance premise imposed on the density itself. -/
theorem cartanQuadraticDensity_rotate
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature)
    (horthogonal : R.transpose * R = 1)
    (hantisymmetric : ∀ mu nu, F mu nu = -F nu mu) :
    cartanQuadraticDensity (rotateCurvature R F) =
      cartanQuadraticDensity F := by
  rw [cartanQuadraticDensity_eq_frobenius
      (rotateCurvature R F)
      (rotateCurvature_antisymmetric R F hantisymmetric),
    cartanQuadraticDensity_eq_frobenius F hantisymmetric]
  exact cartanFrobeniusDensity_rotate R F horthogonal

theorem scaled_component_small
    {a M x : ℝ} (_hM : 0 ≤ M) (hx : |x| ≤ M)
    (hscale : a ^ 2 * M ≤ 1) :
    |a ^ 2 * x| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
  exact (mul_le_mul_of_nonneg_left hx (sq_nonneg a)).trans hscale

/-! ## Quantitative `O(4)` restoration -/

/-- The normalized Wilson density becomes rotation invariant at the explicit
rate `O(a⁴)` on a uniformly bounded small-field Cartan chart. -/
theorem normalizedCartanWilsonDensity_rotation_error
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature)
    (horthogonal : R.transpose * R = 1)
    (hantisymmetric : ∀ mu nu, F mu nu = -F nu mu)
    (hcomponent : ∀ plane : OrientedPlane,
      |F plane.first plane.second| ≤ M)
    (hrotatedComponent : ∀ plane : OrientedPlane,
      |rotateCurvature R F plane.first plane.second| ≤ M)
    (hscale : a ^ 2 * M ≤ 1) :
    |normalizedCartanWilsonDensity a (rotateCurvature R F) -
        normalizedCartanWilsonDensity a F| ≤
      (5 / 4 : ℝ) * a ^ 4 * M ^ 4 := by
  have hsmall : ∀ plane : OrientedPlane,
      |a ^ 2 * F plane.first plane.second| ≤ 1 :=
    fun plane => scaled_component_small hM (hcomponent plane) hscale
  have hrotatedSmall : ∀ plane : OrientedPlane,
      |a ^ 2 * rotateCurvature R F plane.first plane.second| ≤ 1 :=
    fun plane => scaled_component_small hM (hrotatedComponent plane) hscale
  have hF := normalizedCartanWilsonDensity_error ha hM F
    hcomponent hsmall
  have hRF := normalizedCartanWilsonDensity_error ha hM
    (rotateCurvature R F) hrotatedComponent hrotatedSmall
  have hquadratic := cartanQuadraticDensity_rotate R F
    horthogonal hantisymmetric
  calc
    |normalizedCartanWilsonDensity a (rotateCurvature R F) -
        normalizedCartanWilsonDensity a F| ≤
      |normalizedCartanWilsonDensity a (rotateCurvature R F) -
          cartanQuadraticDensity (rotateCurvature R F)| +
        |cartanQuadraticDensity (rotateCurvature R F) -
          normalizedCartanWilsonDensity a F| :=
      abs_sub_le _ _ _
    _ = |normalizedCartanWilsonDensity a (rotateCurvature R F) -
          cartanQuadraticDensity (rotateCurvature R F)| +
        |normalizedCartanWilsonDensity a F - cartanQuadraticDensity F| := by
      rw [hquadratic]
      rw [abs_sub_comm
          (cartanQuadraticDensity F)
          (normalizedCartanWilsonDensity a F)]
    _ ≤ (5 / 8 : ℝ) * a ^ 4 * M ^ 4 +
        (5 / 8 : ℝ) * a ^ 4 * M ^ 4 :=
      add_le_add hRF hF
    _ = (5 / 4 : ℝ) * a ^ 4 * M ^ 4 := by ring

/-- Same theorem stated on the actual `SU(2)` link-field Wilson observable. -/
theorem normalizedSU2CartanWilsonDensity_rotation_error
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (F : CartanCurvature)
    (horthogonal : R.transpose * R = 1)
    (hantisymmetric : ∀ mu nu, F mu nu = -F nu mu)
    (hcomponent : ∀ plane : OrientedPlane,
      |F plane.first plane.second| ≤ M)
    (hrotatedComponent : ∀ plane : OrientedPlane,
      |rotateCurvature R F plane.first plane.second| ≤ M)
    (hscale : a ^ 2 * M ≤ 1) :
    |normalizedSU2CartanWilsonDensity a (rotateCurvature R F) -
        normalizedSU2CartanWilsonDensity a F| ≤
      (5 / 4 : ℝ) * a ^ 4 * M ^ 4 := by
  rw [normalizedSU2CartanWilsonDensity_eq,
    normalizedSU2CartanWilsonDensity_eq]
  exact normalizedCartanWilsonDensity_rotation_error ha hM R F
    horthogonal hantisymmetric hcomponent hrotatedComponent hscale

end HypercubicWilsonSymanzikRestoration
end YangMills
end QuantumTheory
end Mettapedia

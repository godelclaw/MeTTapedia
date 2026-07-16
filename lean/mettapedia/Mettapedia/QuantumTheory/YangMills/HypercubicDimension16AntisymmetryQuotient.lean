import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ShuffleQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Module

/-!
# Exact field-strength antisymmetry quotient

The raw field-strength letter carries an ordered coordinate-axis pair.  This
module constructs the standard rational normalization

* a diagonal pair is zero;
* an increasing pair is the corresponding oriented two-plane;
* a decreasing pair is minus that oriented two-plane.

The kernel is proved to be exactly the span of the literal rows
`e_(a,b) + e_(b,a)`.  An explicit ten-coordinate complement (four diagonal
coordinates and six symmetric off-diagonal coordinates) gives a checked
linear decomposition of the sixteen-dimensional ordered-pair space.  Thus
the quotient by the actual antisymmetry rows is linearly equivalent to the
six-dimensional oriented-plane space.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16AntisymmetryQuotient

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo

abbrev AxisPair := Axis × Axis
abbrev AxisPairSpace := AxisPair →₀ ℚ
abbrev OrientedPlaneSpace := OrientedPlane →₀ ℚ
abbrev AntisymmetryRelationIndex := Axis ⊕ OrientedPlane
abbrev AntisymmetryRelationCoordinateSpace :=
  AntisymmetryRelationIndex →₀ ℚ

/-! ## Normalization and complementary coordinates -/

/-- Coefficient of an ordered pair in the standard oriented-plane basis. -/
def axisPairOrientationCoefficient (pair : AxisPair) : ℚ :=
  if pair.1 = pair.2 then 0
  else if pair.1 < pair.2 then 1 else -1

/-- Image of one ordered axis-pair basis vector in the oriented-plane
normal form. -/
def normalizeAxisPairBasis (pair : AxisPair) : OrientedPlaneSpace :=
  axisPairOrientationCoefficient pair •
    Finsupp.single (planeLookup pair.1 pair.2) 1

/-- Linear extension of ordered-pair antisymmetrization. -/
def normalizeAxisPair : AxisPairSpace →ₗ[ℚ] OrientedPlaneSpace :=
  Finsupp.linearCombination ℚ normalizeAxisPairBasis

@[simp] theorem normalizeAxisPair_single (pair : AxisPair)
    (coefficient : ℚ) :
    normalizeAxisPair (Finsupp.single pair coefficient) =
      coefficient • normalizeAxisPairBasis pair := by
  simp [normalizeAxisPair]

/-- Complementary coordinate attached to one ordered pair.  Diagonal pairs
record one of four diagonal coordinates; among a distinct pair and its
reverse, only the decreasing ordering records the shared symmetric
coordinate. -/
def axisPairRelationCoordinateBasis (pair : AxisPair) :
    AntisymmetryRelationCoordinateSpace :=
  if pair.1 = pair.2 then
    Finsupp.single (Sum.inl pair.1) 1
  else if pair.1 < pair.2 then 0
  else Finsupp.single (Sum.inr (planeLookup pair.1 pair.2)) 1

def axisPairRelationCoordinates :
    AxisPairSpace →ₗ[ℚ] AntisymmetryRelationCoordinateSpace :=
  Finsupp.linearCombination ℚ axisPairRelationCoordinateBasis

@[simp] theorem axisPairRelationCoordinates_single (pair : AxisPair)
    (coefficient : ℚ) :
    axisPairRelationCoordinates (Finsupp.single pair coefficient) =
      coefficient • axisPairRelationCoordinateBasis pair := by
  simp [axisPairRelationCoordinates]

/-- Ordered representative of one oriented plane. -/
def orientedPlaneEmbedBasis (plane : OrientedPlane) : AxisPairSpace :=
  Finsupp.single (plane.first, plane.second) 1

def orientedPlaneEmbed : OrientedPlaneSpace →ₗ[ℚ] AxisPairSpace :=
  Finsupp.linearCombination ℚ orientedPlaneEmbedBasis

@[simp] theorem orientedPlaneEmbed_single (plane : OrientedPlane)
    (coefficient : ℚ) :
    orientedPlaneEmbed (Finsupp.single plane coefficient) =
      coefficient • orientedPlaneEmbedBasis plane := by
  simp [orientedPlaneEmbed]

/-- Ten canonical kernel vectors: one diagonal basis vector for each axis and
one symmetric pair for each oriented plane. -/
def canonicalAntisymmetryRelation :
    AntisymmetryRelationIndex → AxisPairSpace
  | Sum.inl axis => Finsupp.single (axis, axis) 1
  | Sum.inr plane =>
      Finsupp.single (plane.first, plane.second) 1 +
        Finsupp.single (plane.second, plane.first) 1

def antisymmetryRelationSynthesis :
    AntisymmetryRelationCoordinateSpace →ₗ[ℚ] AxisPairSpace :=
  Finsupp.linearCombination ℚ canonicalAntisymmetryRelation

@[simp] theorem antisymmetryRelationSynthesis_single
    (index : AntisymmetryRelationIndex) (coefficient : ℚ) :
    antisymmetryRelationSynthesis (Finsupp.single index coefficient) =
      coefficient • canonicalAntisymmetryRelation index := by
  simp [antisymmetryRelationSynthesis]

theorem normalizeAxisPair_orientedPlaneEmbed
    (value : OrientedPlaneSpace) :
    normalizeAxisPair (orientedPlaneEmbed value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single plane coefficient =>
      fin_cases plane <;>
        simp [orientedPlaneEmbedBasis, normalizeAxisPairBasis,
          axisPairOrientationCoefficient, planeLookup,
          OrientedPlane.first, OrientedPlane.second]

theorem normalizeAxisPair_antisymmetryRelationSynthesis
    (value : AntisymmetryRelationCoordinateSpace) :
    normalizeAxisPair (antisymmetryRelationSynthesis value) = 0 := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single index coefficient =>
      cases index with
      | inl axis =>
          fin_cases axis <;>
            simp [canonicalAntisymmetryRelation, normalizeAxisPairBasis,
              axisPairOrientationCoefficient]
      | inr plane =>
          fin_cases plane <;>
            simp [canonicalAntisymmetryRelation, normalizeAxisPairBasis,
              axisPairOrientationCoefficient, planeLookup,
              OrientedPlane.first, OrientedPlane.second]

theorem axisPairRelationCoordinates_orientedPlaneEmbed
    (value : OrientedPlaneSpace) :
    axisPairRelationCoordinates (orientedPlaneEmbed value) = 0 := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single plane coefficient =>
      fin_cases plane <;>
        simp [orientedPlaneEmbedBasis, axisPairRelationCoordinateBasis,
          OrientedPlane.first, OrientedPlane.second]

theorem axisPairRelationCoordinates_antisymmetryRelationSynthesis
    (value : AntisymmetryRelationCoordinateSpace) :
    axisPairRelationCoordinates (antisymmetryRelationSynthesis value) =
      value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single index coefficient =>
      cases index with
      | inl axis =>
          fin_cases axis <;>
            simp [canonicalAntisymmetryRelation,
              axisPairRelationCoordinateBasis]
      | inr plane =>
          fin_cases plane <;>
            simp [canonicalAntisymmetryRelation,
              axisPairRelationCoordinateBasis, planeLookup,
              OrientedPlane.first, OrientedPlane.second]

/-- Literal sparse relation `e_(a,b) + e_(b,a)`. -/
def axisPairAntisymmetryRow (pair : AxisPair) : AxisPairSpace :=
  Finsupp.single pair 1 + Finsupp.single (pair.2, pair.1) 1

/-! ## Signed hypercubic equivariance of the normalization -/

/-- Signed action on one ordered-pair basis vector. -/
def signedAxisPairActionBasis (h : Hypercubic4)
    (pair : AxisPair) : AxisPairSpace :=
  (Hypercubic4.axisSign h pair.1 *
      Hypercubic4.axisSign h pair.2) •
    Finsupp.single (h.perm pair.1, h.perm pair.2) 1

def signedAxisPairAction (h : Hypercubic4) :
    AxisPairSpace →ₗ[ℚ] AxisPairSpace :=
  Finsupp.linearCombination ℚ (signedAxisPairActionBasis h)

@[simp] theorem signedAxisPairAction_single (h : Hypercubic4)
    (pair : AxisPair) (coefficient : ℚ) :
    signedAxisPairAction h (Finsupp.single pair coefficient) =
      coefficient • signedAxisPairActionBasis h pair := by
  simp [signedAxisPairAction]

/-- Signed two-form action on one oriented-plane basis vector. -/
def signedOrientedPlaneActionBasis (h : Hypercubic4)
    (plane : OrientedPlane) : OrientedPlaneSpace :=
  (planeTensorSign h plane : ℚ) •
    Finsupp.single (planeAction h plane) 1

def signedOrientedPlaneAction (h : Hypercubic4) :
    OrientedPlaneSpace →ₗ[ℚ] OrientedPlaneSpace :=
  Finsupp.linearCombination ℚ (signedOrientedPlaneActionBasis h)

@[simp] theorem signedOrientedPlaneAction_single (h : Hypercubic4)
    (plane : OrientedPlane) (coefficient : ℚ) :
    signedOrientedPlaneAction h (Finsupp.single plane coefficient) =
      coefficient • signedOrientedPlaneActionBasis h plane := by
  simp [signedOrientedPlaneAction]

/-- The lookup table is symmetric. -/
@[simp] theorem planeLookup_comm (first second : Axis) :
    planeLookup first second = planeLookup second first := by
  fin_cases first <;> fin_cases second <;> rfl

theorem planeLookup_endpoints_of_lt (first second : Axis)
    (hordered : first < second) :
    (planeLookup first second).first = first ∧
      (planeLookup first second).second = second := by
  fin_cases first <;> fin_cases second <;>
    simp_all [planeLookup, OrientedPlane.first, OrientedPlane.second]

theorem planeLookup_endpoints_of_gt (first second : Axis)
    (hordered : second < first) :
    (planeLookup first second).first = second ∧
      (planeLookup first second).second = first := by
  fin_cases first <;> fin_cases second <;>
    simp_all [planeLookup, OrientedPlane.first, OrientedPlane.second]

/-- The unsigned plane lookup commutes with every coordinate permutation on
distinct pairs. -/
theorem planeLookup_permuted_certificate (h : Hypercubic4)
    (first second : Axis) (hdifferent : first ≠ second) :
    planeLookup (h.perm first) (h.perm second) =
      planeAction h (planeLookup first second) := by
  unfold planeAction planeActionPerm
  by_cases hordered : first < second
  · obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_lt first second hordered
    rw [hfirst, hsecond]
  · have hle : second ≤ first := le_of_not_gt hordered
    have hreverse : second < first :=
      lt_of_le_of_ne hle hdifferent.symm
    obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_gt first second hreverse
    rw [hfirst, hsecond, planeLookup_comm]

theorem axisPairOrientationCoefficient_swap (first second : Axis)
    (hdifferent : first ≠ second) :
    axisPairOrientationCoefficient (second, first) =
      -axisPairOrientationCoefficient (first, second) := by
  by_cases hordered : first < second
  · have hreverse : ¬ second < first :=
      not_lt_of_ge (le_of_lt hordered)
    simp [axisPairOrientationCoefficient, hdifferent, hdifferent.symm,
      hordered, hreverse]
  · have hle : second ≤ first := le_of_not_gt hordered
    have hreverse : second < first :=
      lt_of_le_of_ne hle hdifferent.symm
    simp [axisPairOrientationCoefficient, hdifferent, hdifferent.symm,
      hordered, hreverse]

theorem axisPairOrientationCoefficient_permuted_ordered
    (h : Hypercubic4) (plane : OrientedPlane) :
    axisPairOrientationCoefficient
        (h.perm plane.first, h.perm plane.second) =
      (planeReorderSign h plane : ℚ) := by
  have hdifferent : h.perm plane.first ≠ h.perm plane.second :=
    h.perm.injective.ne (ne_of_lt plane.ordered)
  by_cases hordered : h.perm plane.first < h.perm plane.second <;>
    simp [axisPairOrientationCoefficient, planeReorderSign,
      hdifferent, hordered]

theorem axisPairOrientationCoefficient_permuted_reverse
    (h : Hypercubic4) (plane : OrientedPlane) :
    axisPairOrientationCoefficient
        (h.perm plane.second, h.perm plane.first) =
      -(planeReorderSign h plane : ℚ) := by
  rw [axisPairOrientationCoefficient_swap]
  · rw [axisPairOrientationCoefficient_permuted_ordered]
  · exact h.perm.injective.ne (ne_of_lt plane.ordered)

theorem axisPairOrientationCoefficient_permuted
    (h : Hypercubic4) (first second : Axis)
    (hdifferent : first ≠ second) :
    axisPairOrientationCoefficient (h.perm first, h.perm second) =
      axisPairOrientationCoefficient (first, second) *
        (planeReorderSign h (planeLookup first second) : ℚ) := by
  by_cases hordered : first < second
  · obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_lt first second hordered
    have hforward := axisPairOrientationCoefficient_permuted_ordered
      h (planeLookup first second)
    rw [hfirst, hsecond] at hforward
    simpa [axisPairOrientationCoefficient, hdifferent, hordered] using hforward
  · have hle : second ≤ first := le_of_not_gt hordered
    have hreverse : second < first :=
      lt_of_le_of_ne hle hdifferent.symm
    obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_gt first second hreverse
    have hbackward := axisPairOrientationCoefficient_permuted_reverse
      h (planeLookup first second)
    rw [hfirst, hsecond] at hbackward
    simpa [axisPairOrientationCoefficient, hdifferent, hordered] using hbackward

theorem axisSign_pair_eq_planeLookup (h : Hypercubic4)
    (first second : Axis) (hdifferent : first ≠ second) :
    Hypercubic4.axisSign h first * Hypercubic4.axisSign h second =
      Hypercubic4.axisSign h (planeLookup first second).first *
        Hypercubic4.axisSign h (planeLookup first second).second := by
  by_cases hordered : first < second
  · obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_lt first second hordered
    rw [hfirst, hsecond]
  · have hle : second ≤ first := le_of_not_gt hordered
    have hreverse : second < first :=
      lt_of_le_of_ne hle hdifferent.symm
    obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_gt first second hreverse
    rw [hfirst, hsecond, mul_comm]

/-- The pair-orientation coefficient, reflection signs, and reordering sign
obey the exact two-form tensor-sign law. -/
theorem axisPairOrientationCoefficient_tensorSign_certificate
    (h : Hypercubic4) (first second : Axis)
    (hdifferent : first ≠ second) :
    (Hypercubic4.axisSign h first *
        Hypercubic4.axisSign h second) *
        axisPairOrientationCoefficient
          (h.perm first, h.perm second) =
      axisPairOrientationCoefficient (first, second) *
        (planeTensorSign h (planeLookup first second) : ℚ) := by
  rw [axisSign_pair_eq_planeLookup h first second hdifferent,
    axisPairOrientationCoefficient_permuted h first second hdifferent]
  unfold planeTensorSign Hypercubic4.axisSign
  simp only [Int.cast_mul]
  cases hfirst : h.reflected (planeLookup first second).first <;>
    cases hsecond : h.reflected (planeLookup first second).second <;>
      simp

/-- Finite-data proof of the basis-level signed intertwining law. -/
theorem normalizeAxisPairBasis_equivariant_certificate
    (h : Hypercubic4) (pair : AxisPair) :
    normalizeAxisPair (signedAxisPairActionBasis h pair) =
      signedOrientedPlaneAction h (normalizeAxisPairBasis pair) := by
  rcases pair with ⟨first, second⟩
  simp only [signedAxisPairActionBasis, map_smul,
    normalizeAxisPair_single, normalizeAxisPairBasis,
    signedOrientedPlaneActionBasis,
    signedOrientedPlaneAction, Finsupp.linearCombination_single,
    smul_smul, one_mul]
  by_cases hequal : first = second
  · subst second
    simp [axisPairOrientationCoefficient]
  · rw [planeLookup_permuted_certificate h first second hequal,
      axisPairOrientationCoefficient_tensorSign_certificate
        h first second hequal]

/-- The standard antisymmetry normal form intertwines the complete signed
hypercubic actions. -/
theorem normalizeAxisPair_equivariant (h : Hypercubic4)
    (value : AxisPairSpace) :
    normalizeAxisPair (signedAxisPairAction h value) =
      signedOrientedPlaneAction h (normalizeAxisPair value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single pair coefficient =>
      simp only [signedAxisPairAction_single,
        normalizeAxisPair_single, map_smul]
      rw [normalizeAxisPairBasis_equivariant_certificate h pair]

/-- A literal pair-antisymmetry row is transported to the corresponding
literal row at the permuted axes with the expected tensor sign. -/
theorem signedAxisPairAction_antisymmetryRow (h : Hypercubic4)
    (pair : AxisPair) :
    signedAxisPairAction h (axisPairAntisymmetryRow pair) =
      (Hypercubic4.axisSign h pair.1 *
        Hypercubic4.axisSign h pair.2) •
          axisPairAntisymmetryRow
            (h.perm pair.1, h.perm pair.2) := by
  simp [axisPairAntisymmetryRow, signedAxisPairActionBasis,
    map_add, smul_add, mul_comm]

/-! ## Explicit sixteen = six plus ten decomposition -/

def axisPairDecompose : AxisPairSpace →ₗ[ℚ]
    OrientedPlaneSpace × AntisymmetryRelationCoordinateSpace :=
  normalizeAxisPair.prod axisPairRelationCoordinates

def axisPairRecompose :
    (OrientedPlaneSpace × AntisymmetryRelationCoordinateSpace) →ₗ[ℚ]
      AxisPairSpace :=
  orientedPlaneEmbed.comp
      (LinearMap.fst ℚ OrientedPlaneSpace
        AntisymmetryRelationCoordinateSpace) +
    antisymmetryRelationSynthesis.comp
      (LinearMap.snd ℚ OrientedPlaneSpace
        AntisymmetryRelationCoordinateSpace)

theorem axisPairRecompose_decompose (value : AxisPairSpace) :
    axisPairRecompose (axisPairDecompose value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp [axisPairRecompose, axisPairDecompose]
  | add left right hleft hright =>
      simp [map_add, hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨first, second⟩
      fin_cases first <;> fin_cases second <;>
        simp [axisPairRecompose, axisPairDecompose,
          normalizeAxisPairBasis, axisPairRelationCoordinateBasis,
          axisPairOrientationCoefficient,
          orientedPlaneEmbedBasis, canonicalAntisymmetryRelation,
          antisymmetryRelationSynthesis, orientedPlaneEmbed,
          planeLookup, OrientedPlane.first, OrientedPlane.second]

theorem axisPairDecompose_recompose
    (value : OrientedPlaneSpace × AntisymmetryRelationCoordinateSpace) :
    axisPairDecompose (axisPairRecompose value) = value := by
  apply Prod.ext
  · change normalizeAxisPair
      (orientedPlaneEmbed value.1 +
        antisymmetryRelationSynthesis value.2) = value.1
    rw [map_add, normalizeAxisPair_orientedPlaneEmbed,
      normalizeAxisPair_antisymmetryRelationSynthesis, add_zero]
  · change axisPairRelationCoordinates
      (orientedPlaneEmbed value.1 +
        antisymmetryRelationSynthesis value.2) = value.2
    rw [map_add, axisPairRelationCoordinates_orientedPlaneEmbed,
      axisPairRelationCoordinates_antisymmetryRelationSynthesis, zero_add]

theorem axisPairDecompose_comp_recompose :
    axisPairDecompose.comp axisPairRecompose = LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact axisPairDecompose_recompose value

theorem axisPairRecompose_comp_decompose :
    axisPairRecompose.comp axisPairDecompose = LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact axisPairRecompose_decompose value

def axisPairDecompositionEquiv :
    AxisPairSpace ≃ₗ[ℚ]
      OrientedPlaneSpace × AntisymmetryRelationCoordinateSpace :=
  LinearEquiv.ofLinear axisPairDecompose axisPairRecompose
    axisPairDecompose_comp_recompose axisPairRecompose_comp_decompose

/-! ## Literal row span and exact kernel -/

def axisPairAntisymmetrySubmodule : Submodule ℚ AxisPairSpace :=
  Submodule.span ℚ (Set.range axisPairAntisymmetryRow)

theorem span_canonicalAntisymmetryRelation_eq_literal :
    Submodule.span ℚ (Set.range canonicalAntisymmetryRelation) =
      axisPairAntisymmetrySubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro relation ⟨index, rfl⟩
    cases index with
    | inl axis =>
        have hrow : axisPairAntisymmetryRow (axis, axis) ∈
            axisPairAntisymmetrySubmodule :=
          Submodule.subset_span (Set.mem_range_self (axis, axis))
        have hhalf := axisPairAntisymmetrySubmodule.smul_mem
          (1 / 2 : ℚ) hrow
        have heq : (1 / 2 : ℚ) •
            axisPairAntisymmetryRow (axis, axis) =
              canonicalAntisymmetryRelation (Sum.inl axis) := by
          simp only [axisPairAntisymmetryRow,
            canonicalAntisymmetryRelation]
          rw [← two_smul ℚ (Finsupp.single (axis, axis) (1 : ℚ)),
            ← mul_smul]
          norm_num
        rw [← heq]
        exact hhalf
    | inr plane =>
        exact Submodule.subset_span
          ⟨(plane.first, plane.second), by
            simp [axisPairAntisymmetryRow,
              canonicalAntisymmetryRelation]⟩
  · unfold axisPairAntisymmetrySubmodule
    rw [Submodule.span_le]
    rintro relation ⟨pair, rfl⟩
    rcases pair with ⟨first, second⟩
    by_cases hequal : first = second
    · subst second
      have hcanonical : canonicalAntisymmetryRelation (Sum.inl first) ∈
          Submodule.span ℚ (Set.range canonicalAntisymmetryRelation) :=
        Submodule.subset_span (Set.mem_range_self (Sum.inl first))
      have htwice := (Submodule.span ℚ
        (Set.range canonicalAntisymmetryRelation)).smul_mem
          (2 : ℚ) hcanonical
      have heq : axisPairAntisymmetryRow (first, first) =
          (2 : ℚ) • canonicalAntisymmetryRelation (Sum.inl first) := by
        simp only [axisPairAntisymmetryRow,
          canonicalAntisymmetryRelation]
        exact (two_smul ℚ
          (Finsupp.single (first, first) (1 : ℚ))).symm
      rw [heq]
      exact htwice
    · have hcanonical :
          canonicalAntisymmetryRelation
              (Sum.inr (planeLookup first second)) ∈
            Submodule.span ℚ (Set.range canonicalAntisymmetryRelation) :=
        Submodule.subset_span
          (Set.mem_range_self (Sum.inr (planeLookup first second)))
      fin_cases first <;> fin_cases second <;>
        simp_all [axisPairAntisymmetryRow,
          canonicalAntisymmetryRelation, planeLookup,
          OrientedPlane.first, OrientedPlane.second]
      all_goals (convert hcanonical using 1; abel)

theorem range_antisymmetryRelationSynthesis :
    LinearMap.range antisymmetryRelationSynthesis =
      axisPairAntisymmetrySubmodule := by
  rw [antisymmetryRelationSynthesis,
    Finsupp.range_linearCombination,
    span_canonicalAntisymmetryRelation_eq_literal]

theorem ker_normalizeAxisPair_eq_range_antisymmetryRelationSynthesis :
    LinearMap.ker normalizeAxisPair =
      LinearMap.range antisymmetryRelationSynthesis := by
  apply le_antisymm
  · intro value hkernel
    rw [LinearMap.mem_range]
    refine ⟨axisPairRelationCoordinates value, ?_⟩
    have hrecompose := axisPairRecompose_decompose value
    change orientedPlaneEmbed (normalizeAxisPair value) +
        antisymmetryRelationSynthesis
          (axisPairRelationCoordinates value) = value at hrecompose
    simpa [LinearMap.mem_ker.mp hkernel] using hrecompose
  · rintro value ⟨coordinates, rfl⟩
    exact LinearMap.mem_ker.mpr
      (normalizeAxisPair_antisymmetryRelationSynthesis coordinates)

/-- Exact row-span theorem for one field-strength pair. -/
theorem ker_normalizeAxisPair_eq_antisymmetrySubmodule :
    LinearMap.ker normalizeAxisPair = axisPairAntisymmetrySubmodule := by
  rw [ker_normalizeAxisPair_eq_range_antisymmetryRelationSynthesis,
    range_antisymmetryRelationSynthesis]

theorem normalizeAxisPair_surjective :
    Function.Surjective normalizeAxisPair := by
  intro value
  exact ⟨orientedPlaneEmbed value,
    normalizeAxisPair_orientedPlaneEmbed value⟩

/-- Quotient by the literal antisymmetry rows, with no oriented-plane normal
form assumed in the source carrier. -/
def axisPairAntisymmetryQuotientEquiv :
    (AxisPairSpace ⧸ axisPairAntisymmetrySubmodule) ≃ₗ[ℚ]
      OrientedPlaneSpace :=
  (Submodule.quotEquivOfEq axisPairAntisymmetrySubmodule
      (LinearMap.ker normalizeAxisPair)
      ker_normalizeAxisPair_eq_antisymmetrySubmodule.symm).trans
    (normalizeAxisPair.quotKerEquivOfSurjective
      normalizeAxisPair_surjective)

theorem axisPairAntisymmetryQuotientEquiv_mk (value : AxisPairSpace) :
    axisPairAntisymmetryQuotientEquiv
        (Submodule.Quotient.mk value) = normalizeAxisPair value := by
  simp [axisPairAntisymmetryQuotientEquiv,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-! ## Exact simultaneous quotient for any finite family of fields -/

abbrev FieldAxisAssignment (fieldCount : ℕ) := Fin fieldCount → AxisPair
abbrev OrientedFieldAssignment (fieldCount : ℕ) :=
  Fin fieldCount → OrientedPlane
abbrev FieldAxisAssignmentSpace (fieldCount : ℕ) :=
  FieldAxisAssignment fieldCount →₀ ℚ
abbrev OrientedFieldAssignmentSpace (fieldCount : ℕ) :=
  OrientedFieldAssignment fieldCount →₀ ℚ

def fieldAxisOrientationCoefficient {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) : ℚ :=
  ∏ slot, axisPairOrientationCoefficient (assignment slot)

def fieldAxisPlanes {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) :
    OrientedFieldAssignment fieldCount :=
  fun slot => planeLookup (assignment slot).1 (assignment slot).2

def normalizeFieldAxisBasis {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) :
    OrientedFieldAssignmentSpace fieldCount :=
  fieldAxisOrientationCoefficient assignment •
    Finsupp.single (fieldAxisPlanes assignment) 1

def normalizeFieldAxes (fieldCount : ℕ) :
    FieldAxisAssignmentSpace fieldCount →ₗ[ℚ]
      OrientedFieldAssignmentSpace fieldCount :=
  Finsupp.linearCombination ℚ normalizeFieldAxisBasis

@[simp] theorem normalizeFieldAxes_single {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (coefficient : ℚ) :
    normalizeFieldAxes fieldCount (Finsupp.single assignment coefficient) =
      coefficient • normalizeFieldAxisBasis assignment := by
  simp [normalizeFieldAxes]

def orderedFieldAxisAssignment {fieldCount : ℕ}
    (assignment : OrientedFieldAssignment fieldCount) :
    FieldAxisAssignment fieldCount :=
  fun slot => ((assignment slot).first, (assignment slot).second)

def orientedFieldAssignmentEmbedBasis {fieldCount : ℕ}
    (assignment : OrientedFieldAssignment fieldCount) :
    FieldAxisAssignmentSpace fieldCount :=
  Finsupp.single (orderedFieldAxisAssignment assignment) 1

def orientedFieldAssignmentEmbed (fieldCount : ℕ) :
    OrientedFieldAssignmentSpace fieldCount →ₗ[ℚ]
      FieldAxisAssignmentSpace fieldCount :=
  Finsupp.linearCombination ℚ orientedFieldAssignmentEmbedBasis

@[simp] theorem orientedFieldAssignmentEmbed_single {fieldCount : ℕ}
    (assignment : OrientedFieldAssignment fieldCount) (coefficient : ℚ) :
    orientedFieldAssignmentEmbed fieldCount
        (Finsupp.single assignment coefficient) =
      coefficient • orientedFieldAssignmentEmbedBasis assignment := by
  simp [orientedFieldAssignmentEmbed]

@[simp] theorem planeLookup_orientedPlane (plane : OrientedPlane) :
    planeLookup plane.first plane.second = plane := by
  fin_cases plane <;> rfl

@[simp] theorem axisPairOrientationCoefficient_orientedPlane
    (plane : OrientedPlane) :
    axisPairOrientationCoefficient (plane.first, plane.second) = 1 := by
  fin_cases plane <;>
    simp [axisPairOrientationCoefficient, OrientedPlane.first,
      OrientedPlane.second]

theorem normalizeFieldAxisBasis_ordered {fieldCount : ℕ}
    (assignment : OrientedFieldAssignment fieldCount) :
    normalizeFieldAxisBasis (orderedFieldAxisAssignment assignment) =
      Finsupp.single assignment 1 := by
  have hcoefficient : fieldAxisOrientationCoefficient
      (orderedFieldAxisAssignment assignment) = 1 := by
    simp [fieldAxisOrientationCoefficient, orderedFieldAxisAssignment]
  have hplanes : fieldAxisPlanes
      (orderedFieldAxisAssignment assignment) = assignment := by
    funext slot
    simp [fieldAxisPlanes, orderedFieldAxisAssignment]
  simp [normalizeFieldAxisBasis, hcoefficient, hplanes]

theorem normalizeFieldAxes_orientedFieldAssignmentEmbed
    (fieldCount : ℕ) (value : OrientedFieldAssignmentSpace fieldCount) :
    normalizeFieldAxes fieldCount
        (orientedFieldAssignmentEmbed fieldCount value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single assignment coefficient =>
      rw [orientedFieldAssignmentEmbed_single, map_smul]
      simp [orientedFieldAssignmentEmbedBasis,
        normalizeFieldAxisBasis_ordered]

/-- Reverse one ordered pair while keeping every other field slot fixed. -/
def swapFieldAxisAt {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    FieldAxisAssignment fieldCount :=
  Function.update assignment slot
    ((assignment slot).2, (assignment slot).1)

def fieldAxisAntisymmetryRow {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    FieldAxisAssignmentSpace fieldCount :=
  Finsupp.single assignment 1 +
    Finsupp.single (swapFieldAxisAt assignment slot) 1

abbrev FieldAxisAntisymmetrySite (fieldCount : ℕ) :=
  FieldAxisAssignment fieldCount × Fin fieldCount

def fieldAxisAntisymmetrySubmodule (fieldCount : ℕ) :
    Submodule ℚ (FieldAxisAssignmentSpace fieldCount) :=
  Submodule.span ℚ (Set.range fun site : FieldAxisAntisymmetrySite fieldCount =>
    fieldAxisAntisymmetryRow site.1 site.2)

theorem axisPairOrientationCoefficient_swap_all (pair : AxisPair) :
    axisPairOrientationCoefficient (pair.2, pair.1) =
      -axisPairOrientationCoefficient pair := by
  by_cases hequal : pair.1 = pair.2
  · rcases pair with ⟨first, second⟩
    change first = second at hequal
    subst second
    simp [axisPairOrientationCoefficient]
  · exact axisPairOrientationCoefficient_swap pair.1 pair.2 hequal

theorem fieldAxisPlanes_swapFieldAxisAt {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    fieldAxisPlanes (swapFieldAxisAt assignment slot) =
      fieldAxisPlanes assignment := by
  funext current
  by_cases hcurrent : current = slot
  · subst current
    simp [fieldAxisPlanes, swapFieldAxisAt, planeLookup_comm]
  · simp [fieldAxisPlanes, swapFieldAxisAt, hcurrent]

theorem fieldAxisOrientationCoefficient_swapFieldAxisAt {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    fieldAxisOrientationCoefficient (swapFieldAxisAt assignment slot) =
      -fieldAxisOrientationCoefficient assignment := by
  unfold fieldAxisOrientationCoefficient
  rw [Fintype.prod_eq_mul_prod_compl slot,
    Fintype.prod_eq_mul_prod_compl slot]
  have hslot : swapFieldAxisAt assignment slot slot =
      ((assignment slot).2, (assignment slot).1) := by
    simp [swapFieldAxisAt]
  rw [hslot, axisPairOrientationCoefficient_swap_all]
  have hrest :
      (∏ current ∈ {slot}ᶜ,
          axisPairOrientationCoefficient
            (swapFieldAxisAt assignment slot current)) =
        ∏ current ∈ {slot}ᶜ,
          axisPairOrientationCoefficient (assignment current) := by
    apply Finset.prod_congr rfl
    intro current hcurrent
    have hne : current ≠ slot := by simpa using hcurrent
    simp [swapFieldAxisAt, hne]
  rw [hrest]
  ring

theorem normalizeFieldAxisBasis_swapFieldAxisAt {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    normalizeFieldAxisBasis (swapFieldAxisAt assignment slot) =
      -normalizeFieldAxisBasis assignment := by
  rw [normalizeFieldAxisBasis, normalizeFieldAxisBasis,
    fieldAxisOrientationCoefficient_swapFieldAxisAt,
    fieldAxisPlanes_swapFieldAxisAt]
  module

theorem normalizeFieldAxes_fieldAxisAntisymmetryRow {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    normalizeFieldAxes fieldCount
        (fieldAxisAntisymmetryRow assignment slot) = 0 := by
  simp [fieldAxisAntisymmetryRow, map_add,
    normalizeFieldAxisBasis_swapFieldAxisAt]

/-! ### A telescoping normal-form proof -/

def orientAxisPair (pair : AxisPair) : AxisPair :=
  if pair.1 < pair.2 then pair else (pair.2, pair.1)

def orientFieldAxisAt {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    FieldAxisAssignment fieldCount :=
  Function.update assignment slot (orientAxisPair (assignment slot))

def orientFieldAxesOn {fieldCount : ℕ} (slots : Finset (Fin fieldCount))
    (assignment : FieldAxisAssignment fieldCount) :
    FieldAxisAssignment fieldCount :=
  fun slot => if slot ∈ slots then orientAxisPair (assignment slot)
    else assignment slot

theorem orientAxisPair_eq_orderedLookup (pair : AxisPair)
    (hdifferent : pair.1 ≠ pair.2) :
    orientAxisPair pair =
      ((planeLookup pair.1 pair.2).first,
        (planeLookup pair.1 pair.2).second) := by
  by_cases hordered : pair.1 < pair.2
  · obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_lt pair.1 pair.2 hordered
    simp [orientAxisPair, hordered, hfirst, hsecond]
  · have hle : pair.2 ≤ pair.1 := le_of_not_gt hordered
    have hreverse : pair.2 < pair.1 :=
      lt_of_le_of_ne hle hdifferent.symm
    obtain ⟨hfirst, hsecond⟩ :=
      planeLookup_endpoints_of_gt pair.1 pair.2 hreverse
    simp [orientAxisPair, hordered, hfirst, hsecond]

theorem orientFieldAxisAt_orientFieldAxesOn {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount)
    (slots : Finset (Fin fieldCount)) (slot : Fin fieldCount)
    (hslot : slot ∉ slots) :
    orientFieldAxisAt (orientFieldAxesOn slots assignment) slot =
      orientFieldAxesOn (insert slot slots) assignment := by
  funext current
  by_cases hcurrent : current = slot
  · subst current
    simp [orientFieldAxisAt, orientFieldAxesOn, hslot]
  · simp [orientFieldAxisAt, orientFieldAxesOn, hcurrent]

theorem fieldAxisAntisymmetry_oneStep {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) (slot : Fin fieldCount) :
    Finsupp.single assignment 1 -
        axisPairOrientationCoefficient (assignment slot) •
          Finsupp.single (orientFieldAxisAt assignment slot) 1 ∈
      fieldAxisAntisymmetrySubmodule fieldCount := by
  rcases hpair : assignment slot with ⟨first, second⟩
  by_cases hequal : first = second
  · subst second
    have hrow : fieldAxisAntisymmetryRow assignment slot ∈
        fieldAxisAntisymmetrySubmodule fieldCount :=
      Submodule.subset_span ⟨(assignment, slot), rfl⟩
    have hhalf := (fieldAxisAntisymmetrySubmodule fieldCount).smul_mem
      (1 / 2 : ℚ) hrow
    have hswap : swapFieldAxisAt assignment slot = assignment := by
      funext current
      by_cases hcurrent : current = slot
      · subst current
        simp [swapFieldAxisAt, hpair]
      · simp [swapFieldAxisAt, hcurrent]
    have horient : orientFieldAxisAt assignment slot = assignment := by
      funext current
      by_cases hcurrent : current = slot
      · subst current
        simp [orientFieldAxisAt, orientAxisPair, hpair]
      · simp [orientFieldAxisAt, hcurrent]
    simp only [axisPairOrientationCoefficient]
    simp
    change Finsupp.single assignment 1 ∈
      fieldAxisAntisymmetrySubmodule fieldCount
    have heq : (1 / 2 : ℚ) • fieldAxisAntisymmetryRow assignment slot =
        Finsupp.single assignment 1 := by
      ext key
      by_cases hkey : key = assignment
      · subst key
        norm_num [fieldAxisAntisymmetryRow, hswap]
      · simp [fieldAxisAntisymmetryRow, hswap, hkey]
    rw [← heq]
    exact hhalf
  · by_cases hordered : first < second
    · have horient : orientFieldAxisAt assignment slot = assignment := by
        funext current
        by_cases hcurrent : current = slot
        · subst current
          simp [orientFieldAxisAt, orientAxisPair, hpair, hordered]
        · simp [orientFieldAxisAt, hcurrent]
      simp [axisPairOrientationCoefficient, hequal, hordered, horient]
    · have horient : orientFieldAxisAt assignment slot =
          swapFieldAxisAt assignment slot := by
        funext current
        by_cases hcurrent : current = slot
        · subst current
          simp [orientFieldAxisAt, swapFieldAxisAt, orientAxisPair,
            hpair, hordered]
        · simp [orientFieldAxisAt, swapFieldAxisAt, hcurrent]
      have hrow : fieldAxisAntisymmetryRow assignment slot ∈
          fieldAxisAntisymmetrySubmodule fieldCount :=
        Submodule.subset_span ⟨(assignment, slot), rfl⟩
      simpa [axisPairOrientationCoefficient, hequal, hordered, horient,
        fieldAxisAntisymmetryRow] using hrow

theorem fieldAxisAntisymmetry_telescoping {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) :
    ∀ slots : Finset (Fin fieldCount),
      Finsupp.single assignment 1 -
          (∏ slot ∈ slots,
            axisPairOrientationCoefficient (assignment slot)) •
            Finsupp.single (orientFieldAxesOn slots assignment) 1 ∈
        fieldAxisAntisymmetrySubmodule fieldCount := by
  intro slots
  induction slots using Finset.induction_on with
  | empty =>
      have hempty : orientFieldAxesOn ∅ assignment = assignment := by
        funext slot
        simp [orientFieldAxesOn]
      simp [hempty]
  | @insert slot slots hslot ih =>
      have hstep := fieldAxisAntisymmetry_oneStep
        (orientFieldAxesOn slots assignment) slot
      have hcoefficient : axisPairOrientationCoefficient
          (orientFieldAxesOn slots assignment slot) =
            axisPairOrientationCoefficient (assignment slot) := by
        simp [orientFieldAxesOn, hslot]
      have horient := orientFieldAxisAt_orientFieldAxesOn
        assignment slots slot hslot
      rw [hcoefficient, horient] at hstep
      have hscaled := (fieldAxisAntisymmetrySubmodule fieldCount).smul_mem
        (∏ current ∈ slots,
          axisPairOrientationCoefficient (assignment current)) hstep
      have hadd := (fieldAxisAntisymmetrySubmodule fieldCount).add_mem
        ih hscaled
      rw [Finset.prod_insert hslot]
      convert hadd using 1
      module

theorem orientFieldAxesOn_univ_eq_ordered {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount)
    (hdifferent : ∀ slot, (assignment slot).1 ≠ (assignment slot).2) :
    orientFieldAxesOn Finset.univ assignment =
      orderedFieldAxisAssignment (fieldAxisPlanes assignment) := by
  funext slot
  simp only [orientFieldAxesOn, Finset.mem_univ, if_true,
    orderedFieldAxisAssignment, fieldAxisPlanes]
  exact orientAxisPair_eq_orderedLookup (assignment slot)
    (hdifferent slot)

theorem fieldAxisBasis_residual_mem {fieldCount : ℕ}
    (assignment : FieldAxisAssignment fieldCount) :
    Finsupp.single assignment 1 -
        orientedFieldAssignmentEmbed fieldCount
          (normalizeFieldAxisBasis assignment) ∈
      fieldAxisAntisymmetrySubmodule fieldCount := by
  by_cases hdiagonal : ∃ slot, (assignment slot).1 = (assignment slot).2
  · rcases hdiagonal with ⟨slot, hslot⟩
    have hzero : fieldAxisOrientationCoefficient assignment = 0 := by
      unfold fieldAxisOrientationCoefficient
      apply Finset.prod_eq_zero (Finset.mem_univ slot)
      simp [axisPairOrientationCoefficient, hslot]
    have hstep := fieldAxisAntisymmetry_oneStep assignment slot
    simp [normalizeFieldAxisBasis, hzero,
      axisPairOrientationCoefficient, hslot] at hstep ⊢
    exact hstep
  · have hdifferent : ∀ slot,
        (assignment slot).1 ≠ (assignment slot).2 := by
      intro slot hequal
      exact hdiagonal ⟨slot, hequal⟩
    have htelescoping := fieldAxisAntisymmetry_telescoping assignment
      Finset.univ
    rw [orientFieldAxesOn_univ_eq_ordered assignment hdifferent] at htelescoping
    simpa [normalizeFieldAxisBasis, orientedFieldAssignmentEmbed,
      orientedFieldAssignmentEmbedBasis,
      fieldAxisOrientationCoefficient] using htelescoping

theorem fieldAxis_residual_mem {fieldCount : ℕ}
    (value : FieldAxisAssignmentSpace fieldCount) :
    value - orientedFieldAssignmentEmbed fieldCount
        (normalizeFieldAxes fieldCount value) ∈
      fieldAxisAntisymmetrySubmodule fieldCount := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      have hadd := (fieldAxisAntisymmetrySubmodule fieldCount).add_mem
        hleft hright
      convert hadd using 1
      simp [map_add]
      module
  | single assignment coefficient =>
      have hscaled := (fieldAxisAntisymmetrySubmodule fieldCount).smul_mem
        coefficient (fieldAxisBasis_residual_mem assignment)
      simpa [smul_sub] using hscaled

theorem ker_normalizeFieldAxes_eq_fieldAxisAntisymmetrySubmodule
    (fieldCount : ℕ) :
    LinearMap.ker (normalizeFieldAxes fieldCount) =
      fieldAxisAntisymmetrySubmodule fieldCount := by
  apply le_antisymm
  · intro value hkernel
    have hresidual := fieldAxis_residual_mem value
    rw [LinearMap.mem_ker.mp hkernel] at hresidual
    simpa using hresidual
  · unfold fieldAxisAntisymmetrySubmodule
    rw [Submodule.span_le]
    rintro value ⟨site, rfl⟩
    exact LinearMap.mem_ker.mpr
      (normalizeFieldAxes_fieldAxisAntisymmetryRow site.1 site.2)

theorem normalizeFieldAxes_surjective (fieldCount : ℕ) :
    Function.Surjective (normalizeFieldAxes fieldCount) := by
  intro value
  exact ⟨orientedFieldAssignmentEmbed fieldCount value,
    normalizeFieldAxes_orientedFieldAssignmentEmbed fieldCount value⟩

def fieldAxisAntisymmetryQuotientEquiv (fieldCount : ℕ) :
    (FieldAxisAssignmentSpace fieldCount ⧸
        fieldAxisAntisymmetrySubmodule fieldCount) ≃ₗ[ℚ]
      OrientedFieldAssignmentSpace fieldCount :=
  (Submodule.quotEquivOfEq (fieldAxisAntisymmetrySubmodule fieldCount)
      (LinearMap.ker (normalizeFieldAxes fieldCount))
      (ker_normalizeFieldAxes_eq_fieldAxisAntisymmetrySubmodule
        fieldCount).symm).trans
    ((normalizeFieldAxes fieldCount).quotKerEquivOfSurjective
      (normalizeFieldAxes_surjective fieldCount))

end HypercubicDimension16AntisymmetryQuotient
end YangMills
end QuantumTheory
end Mettapedia

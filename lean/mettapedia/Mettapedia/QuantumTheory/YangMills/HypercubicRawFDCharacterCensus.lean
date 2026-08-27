import Mettapedia.QuantumTheory.YangMills.HypercubicUnpaddedFDSyntax
import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCensus
import Mathlib.LinearAlgebra.Trace

/-!
# Character census on the unpadded raw `F,D` carrier

This module equips the existing concrete signed-permutation carrier `H(4)`
with its group structure and constructs its standard four-dimensional signed
representation over `ℚ`.  Character averaging then gives the exact number of
invariant tensor contractions before field antisymmetry, Bianchi, EOM, IBP,
trace, or Cayley--Hamilton rows are imposed.

These are raw-carrier multiplicities, not dimensions of either physical
relation quotient.  Keeping that distinction explicit prevents a finite
character computation from being presented as the full operator basis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicUnpaddedFDSyntax

/-! ## The concrete `H(4)` group -/

instance : Group Hypercubic4 where
  mul := Hypercubic4.compose
  one := Hypercubic4.one
  inv := Hypercubic4.inverse
  mul_assoc left middle right :=
    (Hypercubic4.compose_assoc left middle right).symm
  one_mul := Hypercubic4.one_compose
  mul_one := Hypercubic4.compose_one
  inv_mul_cancel := Hypercubic4.inverse_compose

@[simp] theorem hypercubic_mul_def (left right : Hypercubic4) :
    left * right = Hypercubic4.compose left right := rfl

@[simp] theorem hypercubic_one_def :
    (1 : Hypercubic4) = Hypercubic4.one := rfl

@[simp] theorem hypercubic_inv_def (h : Hypercubic4) :
    h⁻¹ = Hypercubic4.inverse h := rfl

/-! ## Standard signed axis representation -/

/-- Pullback action on rational covectors. -/
def signedAxisLinear (h : Hypercubic4) :
    (Axis → ℚ) →ₗ[ℚ] (Axis → ℚ) where
  toFun vector axis :=
    Hypercubic4.axisSign h (h⁻¹.perm axis) * vector (h⁻¹.perm axis)
  map_add' := by
    intro left right
    funext axis
    simp
    ring
  map_smul' := by
    intro scalar vector
    funext axis
    simp
    ring

/-- The standard signed four-vector representation of the literal lattice
hypercubic group. -/
def signedAxisRepresentation :
    Hypercubic4 →* Module.End ℚ (Axis → ℚ) where
  toFun := signedAxisLinear
  map_one' := by
    ext vector axis
    simp [signedAxisLinear, Hypercubic4.inverse, Hypercubic4.one,
      Hypercubic4.axisSign]
  map_mul' := by
    intro left right
    apply LinearMap.ext
    intro vector
    funext axis
    change Hypercubic4.axisSign (Hypercubic4.compose left right)
          ((Hypercubic4.inverse
            (Hypercubic4.compose left right)).perm axis) *
          vector ((Hypercubic4.inverse
            (Hypercubic4.compose left right)).perm axis) =
      Hypercubic4.axisSign left
          ((Hypercubic4.inverse left).perm axis) *
        (Hypercubic4.axisSign right
            ((Hypercubic4.inverse right).perm
              ((Hypercubic4.inverse left).perm axis)) *
          vector ((Hypercubic4.inverse right).perm
            ((Hypercubic4.inverse left).perm axis)))
    have hinvPerm :
        (Hypercubic4.inverse
            (Hypercubic4.compose left right)).perm axis =
          (Hypercubic4.inverse right).perm
            ((Hypercubic4.inverse left).perm axis) := by
      simp [Hypercubic4.inverse, Hypercubic4.compose]
    rw [hinvPerm]
    rw [Hypercubic4.axisSign_compose]
    have hcancel :
        right.perm
            ((Hypercubic4.inverse right).perm
              ((Hypercubic4.inverse left).perm axis)) =
          (Hypercubic4.inverse left).perm axis := by
      simp [Hypercubic4.inverse]
    rw [hcancel]
    ring

/-- Signed trace of a concrete hypercubic element in the standard
four-vector representation. -/
def signedAxisTrace (h : Hypercubic4) : ℚ :=
  ∑ axis : Axis,
    if h.perm axis = axis then Hypercubic4.axisSign h axis else 0

theorem signedAxisTrace_four_terms (h : Hypercubic4) :
    signedAxisTrace h =
      (if h.perm 0 = 0 then Hypercubic4.axisSign h 0 else 0) +
      (if h.perm 1 = 1 then Hypercubic4.axisSign h 1 else 0) +
      (if h.perm 2 = 2 then Hypercubic4.axisSign h 2 else 0) +
      (if h.perm 3 = 3 then Hypercubic4.axisSign h 3 else 0) := by
  simp [signedAxisTrace, Fin.sum_univ_succ]
  ring

theorem orientationSign_four_factors (h : Hypercubic4) :
    Hypercubic4.orientationSign h =
      ((Equiv.Perm.sign h.perm : ℤ) : ℚ) *
        (Hypercubic4.axisSign h 0 *
          (Hypercubic4.axisSign h 1 *
            (Hypercubic4.axisSign h 2 * Hypercubic4.axisSign h 3))) := by
  simp [Hypercubic4.orientationSign, Fin.prod_univ_succ]

theorem signedAxisRepresentation_character (h : Hypercubic4) :
    LinearMap.trace ℚ (Axis → ℚ) (signedAxisRepresentation h) =
      signedAxisTrace h := by
  unfold signedAxisTrace
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ Axis)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro axis _
  change Hypercubic4.axisSign h (h⁻¹.perm axis) *
      (Pi.single axis (1 : ℚ) : Axis → ℚ) (h⁻¹.perm axis) =
    if h.perm axis = axis then Hypercubic4.axisSign h axis else 0
  by_cases hfixed : h.perm axis = axis
  · have hinvFixed : h⁻¹.perm axis = axis := by
      have h := congrArg h.perm.symm hfixed
      simpa [Hypercubic4.inverse] using h.symm
    rw [if_pos hfixed, hinvFixed]
    simp
  · have hinvNotFixed : h⁻¹.perm axis ≠ axis := by
      intro hinv
      apply hfixed
      have := congrArg h.perm hinv
      simpa [Hypercubic4.inverse] using this.symm
    rw [if_neg hfixed]
    have hsingle :
        (Pi.single axis (1 : ℚ) : Axis → ℚ) (h⁻¹.perm axis) = 0 := by
      rw [Pi.single_apply, if_neg hinvNotFixed]
    rw [hsingle, mul_zero]

/-! ## Tensor-coefficient representations -/

abbrev AxisTensorAssignment (rank : ℕ) := Fin rank → Axis

def axisTensorAssignmentAct {rank : ℕ} (h : Hypercubic4)
    (assignment : AxisTensorAssignment rank) : AxisTensorAssignment rank :=
  fun slot => h.perm (assignment slot)

@[simp] theorem axisTensorAssignmentAct_one {rank : ℕ}
    (assignment : AxisTensorAssignment rank) :
    axisTensorAssignmentAct 1 assignment = assignment := by
  rfl

theorem axisTensorAssignmentAct_mul {rank : ℕ}
    (left right : Hypercubic4) (assignment : AxisTensorAssignment rank) :
    axisTensorAssignmentAct (left * right) assignment =
      axisTensorAssignmentAct left (axisTensorAssignmentAct right assignment) := by
  rfl

def axisTensorAssignmentSign {rank : ℕ} (h : Hypercubic4)
    (assignment : AxisTensorAssignment rank) : ℚ :=
  ∏ slot : Fin rank, Hypercubic4.axisSign h (assignment slot)

theorem axisTensorAssignmentSign_mul {rank : ℕ}
    (left right : Hypercubic4) (assignment : AxisTensorAssignment rank) :
    axisTensorAssignmentSign (left * right) assignment =
      axisTensorAssignmentSign right assignment *
        axisTensorAssignmentSign left
          (axisTensorAssignmentAct right assignment) := by
  classical
  unfold axisTensorAssignmentSign axisTensorAssignmentAct
  simp only [hypercubic_mul_def, Hypercubic4.axisSign_compose]
  rw [Finset.prod_mul_distrib]

def axisTensorWeight (parity : ContractionParity) {rank : ℕ}
    (h : Hypercubic4) (assignment : AxisTensorAssignment rank) : ℚ :=
  parity.character h * axisTensorAssignmentSign h assignment

theorem axisTensorWeight_mul (parity : ContractionParity) {rank : ℕ}
    (left right : Hypercubic4) (assignment : AxisTensorAssignment rank) :
    axisTensorWeight parity (left * right) assignment =
      axisTensorWeight parity right assignment *
        axisTensorWeight parity left
          (axisTensorAssignmentAct right assignment) := by
  unfold axisTensorWeight
  rw [axisTensorAssignmentSign_mul,
    show parity.character (left * right) =
        parity.character (Hypercubic4.compose left right) by rfl,
    ContractionParity.character_compose]
  ring

/-- Pullback representation on rank-`n` coefficient tensors.  Its fixed
vectors are exactly the scalar or pseudoscalar covariance equations on the
axis-assignment carrier. -/
def axisTensorCoefficientLinear (parity : ContractionParity) {rank : ℕ}
    (h : Hypercubic4) :
    (AxisTensorAssignment rank → ℚ) →ₗ[ℚ]
      (AxisTensorAssignment rank → ℚ) where
  toFun coefficients assignment :=
    axisTensorWeight parity h
        (axisTensorAssignmentAct h⁻¹ assignment) *
      coefficients (axisTensorAssignmentAct h⁻¹ assignment)
  map_add' := by
    intro left right
    funext assignment
    simp
    ring
  map_smul' := by
    intro scalar coefficients
    funext assignment
    simp
    ring

def axisTensorCoefficientRepresentation
    (parity : ContractionParity) (rank : ℕ) :
    Hypercubic4 →* Module.End ℚ
      (AxisTensorAssignment rank → ℚ) where
  toFun := axisTensorCoefficientLinear parity
  map_one' := by
    apply LinearMap.ext
    intro coefficients
    funext assignment
    change axisTensorWeight parity 1
          (axisTensorAssignmentAct (1 : Hypercubic4)⁻¹ assignment) *
        coefficients (axisTensorAssignmentAct (1 : Hypercubic4)⁻¹ assignment) =
      coefficients assignment
    have hact :
        axisTensorAssignmentAct (1 : Hypercubic4)⁻¹ assignment = assignment := by
      rfl
    rw [hact]
    cases parity <;>
      simp [axisTensorWeight, axisTensorAssignmentSign,
        ContractionParity.character, Hypercubic4.orientationSign,
        Hypercubic4.one, Hypercubic4.axisSign]
  map_mul' := by
    intro left right
    apply LinearMap.ext
    intro coefficients
    funext assignment
    let pulled : AxisTensorAssignment rank :=
      axisTensorAssignmentAct right⁻¹
        (axisTensorAssignmentAct left⁻¹ assignment)
    have hpulled :
        axisTensorAssignmentAct (left * right)⁻¹ assignment = pulled := by
      funext slot
      simp [pulled, axisTensorAssignmentAct, Hypercubic4.inverse,
        Hypercubic4.compose]
    have hforward :
        axisTensorAssignmentAct right pulled =
          axisTensorAssignmentAct left⁻¹ assignment := by
      funext slot
      simp [pulled, axisTensorAssignmentAct, Hypercubic4.inverse]
    change axisTensorWeight parity (left * right)
          (axisTensorAssignmentAct (left * right)⁻¹ assignment) *
        coefficients
          (axisTensorAssignmentAct (left * right)⁻¹ assignment) =
      axisTensorWeight parity left
          (axisTensorAssignmentAct left⁻¹ assignment) *
        (axisTensorWeight parity right pulled * coefficients pulled)
    rw [hpulled, axisTensorWeight_mul, hforward]
    ring

theorem axisTensorCoefficient_fixed_iff_covariant
    (parity : ContractionParity) (rank : ℕ)
    (coefficients : AxisTensorAssignment rank → ℚ) :
    (∀ h, axisTensorCoefficientRepresentation parity rank h coefficients =
        coefficients) ↔
      ∀ h assignment,
        coefficients (axisTensorAssignmentAct h assignment) =
          axisTensorWeight parity h assignment * coefficients assignment := by
  constructor
  · intro hinvariant h assignment
    have hfixed := congrFun (hinvariant h)
      (axisTensorAssignmentAct h assignment)
    have hsource :
        axisTensorAssignmentAct h⁻¹
            (axisTensorAssignmentAct h assignment) = assignment := by
      funext slot
      simp [axisTensorAssignmentAct, Hypercubic4.inverse]
    change axisTensorWeight parity h
          (axisTensorAssignmentAct h⁻¹
            (axisTensorAssignmentAct h assignment)) *
        coefficients
          (axisTensorAssignmentAct h⁻¹
            (axisTensorAssignmentAct h assignment)) =
      coefficients (axisTensorAssignmentAct h assignment) at hfixed
    rw [hsource] at hfixed
    exact hfixed.symm
  · intro hcovariant h
    funext assignment
    let source := axisTensorAssignmentAct h⁻¹ assignment
    have htarget : axisTensorAssignmentAct h source = assignment := by
      funext slot
      simp [source, axisTensorAssignmentAct, Hypercubic4.inverse]
    change axisTensorWeight parity h source * coefficients source =
      coefficients assignment
    rw [← htarget]
    exact (hcovariant h source).symm

/-! ## Exact tensor-power character -/

theorem axisTensorAssignmentAct_inv_fixed_iff {rank : ℕ}
    (h : Hypercubic4) (assignment : AxisTensorAssignment rank) :
    axisTensorAssignmentAct h⁻¹ assignment = assignment ↔
      ∀ slot, h.perm (assignment slot) = assignment slot := by
  constructor
  · intro hfixed slot
    have hinv := congrFun hfixed slot
    have := congrArg h.perm hinv
    simpa [axisTensorAssignmentAct, Hypercubic4.inverse] using this.symm
  · intro hfixed
    funext slot
    have hslot := hfixed slot
    have := congrArg h.perm.symm hslot
    simpa [axisTensorAssignmentAct, Hypercubic4.inverse] using this.symm

theorem axisTensorCoefficient_diagonal
    (parity : ContractionParity) (rank : ℕ)
    (h : Hypercubic4) (assignment : AxisTensorAssignment rank) :
    (axisTensorCoefficientRepresentation parity rank h
        (Pi.single assignment (1 : ℚ))) assignment =
      parity.character h *
        ∏ slot : Fin rank,
          (if h.perm (assignment slot) = assignment slot then
            Hypercubic4.axisSign h (assignment slot) else 0) := by
  classical
  change axisTensorWeight parity h
        (axisTensorAssignmentAct h⁻¹ assignment) *
      (Pi.single assignment (1 : ℚ) :
        AxisTensorAssignment rank → ℚ)
          (axisTensorAssignmentAct h⁻¹ assignment) = _
  by_cases hfixed : ∀ slot, h.perm (assignment slot) = assignment slot
  · have hinvFixed :
        axisTensorAssignmentAct h⁻¹ assignment = assignment :=
      (axisTensorAssignmentAct_inv_fixed_iff h assignment).2 hfixed
    rw [hinvFixed]
    simp [axisTensorWeight, axisTensorAssignmentSign, hfixed]
  · have hinvNotFixed :
        axisTensorAssignmentAct h⁻¹ assignment ≠ assignment :=
      mt (axisTensorAssignmentAct_inv_fixed_iff h assignment).1 hfixed
    have hsingle :
        (Pi.single assignment (1 : ℚ) :
          AxisTensorAssignment rank → ℚ)
            (axisTensorAssignmentAct h⁻¹ assignment) = 0 := by
      rw [Pi.single_apply, if_neg hinvNotFixed]
    rw [hsingle, mul_zero]
    push Not at hfixed
    obtain ⟨slot, hslot⟩ := hfixed
    have hprod :
        (∏ slot : Fin rank,
          if h.perm (assignment slot) = assignment slot then
            Hypercubic4.axisSign h (assignment slot) else 0) = 0 := by
      apply (Finset.prod_eq_zero (Finset.mem_univ slot))
      rw [if_neg hslot]
    rw [hprod, mul_zero]

theorem axisTensorCoefficient_trace
    (parity : ContractionParity) (rank : ℕ) (h : Hypercubic4) :
    LinearMap.trace ℚ (AxisTensorAssignment rank → ℚ)
        (axisTensorCoefficientRepresentation parity rank h) =
      parity.character h * signedAxisTrace h ^ rank := by
  rw [LinearMap.trace_eq_matrix_trace ℚ
    (Pi.basisFun ℚ (AxisTensorAssignment rank))]
  unfold Matrix.trace
  calc
    (∑ assignment : AxisTensorAssignment rank,
        LinearMap.toMatrix (Pi.basisFun ℚ (AxisTensorAssignment rank))
          (Pi.basisFun ℚ (AxisTensorAssignment rank))
          (axisTensorCoefficientRepresentation parity rank h)
          assignment assignment) =
      ∑ assignment : AxisTensorAssignment rank,
        parity.character h *
          ∏ slot : Fin rank,
            (if h.perm (assignment slot) = assignment slot then
              Hypercubic4.axisSign h (assignment slot) else 0) := by
        apply Finset.sum_congr rfl
        intro assignment _
        exact axisTensorCoefficient_diagonal parity rank h assignment
    _ = parity.character h *
        ∑ assignment : AxisTensorAssignment rank,
          ∏ slot : Fin rank,
            (if h.perm (assignment slot) = assignment slot then
              Hypercubic4.axisSign h (assignment slot) else 0) := by
        rw [Finset.mul_sum]
    _ = parity.character h *
        (∑ axis : Axis,
          if h.perm axis = axis then Hypercubic4.axisSign h axis else 0) ^
            rank := by
        rw [Fintype.sum_pow]
    _ = parity.character h * signedAxisTrace h ^ rank := by
        rfl

/-! ## Transparent finite character code -/

/-- Proof-irrelevant literal table behind the sixteen coordinate-reflection
choices. -/
def characterReflectionEntry : ℕ → ℕ → Bool
  | 0, _ => false
  | 1, 0 => true
  | 1, _ => false
  | 2, 1 => true
  | 2, _ => false
  | 3, 0 | 3, 1 => true
  | 3, _ => false
  | 4, 2 => true
  | 4, _ => false
  | 5, 0 | 5, 2 => true
  | 5, _ => false
  | 6, 1 | 6, 2 => true
  | 6, _ => false
  | 7, 0 | 7, 1 | 7, 2 => true
  | 7, _ => false
  | 8, 3 => true
  | 8, _ => false
  | 9, 0 | 9, 3 => true
  | 9, _ => false
  | 10, 1 | 10, 3 => true
  | 10, _ => false
  | 11, 0 | 11, 1 | 11, 3 => true
  | 11, _ => false
  | 12, 2 | 12, 3 => true
  | 12, _ => false
  | 13, 0 | 13, 2 | 13, 3 => true
  | 13, _ => false
  | 14, 1 | 14, 2 | 14, 3 => true
  | 14, _ => false
  | 15, 0 | 15, 1 | 15, 2 | 15, 3 => true
  | _, _ => false

/-- Literal enumeration of the sixteen coordinate-reflection choices.  An
explicit table keeps kernel replay independent of an opaque bit-operation
evaluator. -/
def characterReflectionCode (mask : Fin 16) (axis : Axis) : Bool :=
  characterReflectionEntry mask.1 axis.1

/-- The compact `24 × 16` code used by the finite certificates.  This is the
same literal unsigned-permutation table used by the earlier quartic and octic
censuses, paired with the transparent reflection table above. -/
def decodedHypercubicCharacterElement
    (permutation : Fin 24) (reflectionMask : Fin 16) : Hypercubic4 :=
  { perm := permutationCode permutation
    reflected := characterReflectionCode reflectionMask }

theorem characterReflectionCode_injective :
    Function.Injective characterReflectionCode := by
  decide

theorem characterPermutationCode_injective :
    Function.Injective permutationCode := by
  decide

theorem decodedHypercubicCharacterElement_injective :
    Function.Injective
      (fun code : Fin 24 × Fin 16 =>
        decodedHypercubicCharacterElement code.1 code.2) := by
  rintro ⟨leftPermutation, leftReflection⟩
    ⟨rightPermutation, rightReflection⟩ heq
  apply Prod.ext
  · exact characterPermutationCode_injective
      (congrArg Hypercubic4.perm heq)
  · exact characterReflectionCode_injective
      (congrArg Hypercubic4.reflected heq)

/-- The transparent finite code enumerates every element of the actual
signed-permutation group exactly once. -/
theorem decodedHypercubicCharacterElement_bijective :
    Function.Bijective
      (fun code : Fin 24 × Fin 16 =>
        decodedHypercubicCharacterElement code.1 code.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨decodedHypercubicCharacterElement_injective, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Hypercubic4.card_hypercubic4]

noncomputable def hypercubicCharacterCodeEquiv :
    Fin 24 × Fin 16 ≃ Hypercubic4 :=
  Equiv.ofBijective
    (fun code : Fin 24 × Fin 16 =>
      decodedHypercubicCharacterElement code.1 code.2)
    decodedHypercubicCharacterElement_bijective

/-- Contribution of all sixteen reflection masks above one unsigned
permutation to a rank-`n` scalar or pseudoscalar character moment. -/
def encodedReflectionCharacterMoment
    (parity : ContractionParity) (permutation : Fin 24) (rank : ℕ) : ℚ :=
  ∑ reflectionMask : Fin 16,
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    parity.character h * signedAxisTrace h ^ rank

/-- Character moment over all `24 × 16` transparent codes. -/
def encodedCharacterMoment
    (parity : ContractionParity) (rank : ℕ) : ℚ :=
  ∑ permutation : Fin 24,
    encodedReflectionCharacterMoment parity permutation rank

theorem hypercubic_character_sum_eq_encoded
    (parity : ContractionParity) (rank : ℕ) :
    (∑ h : Hypercubic4,
        parity.character h * signedAxisTrace h ^ rank) =
      encodedCharacterMoment parity rank := by
  let summand : Hypercubic4 → ℚ := fun h =>
    parity.character h * signedAxisTrace h ^ rank
  calc
    (∑ h : Hypercubic4, summand h) =
        ∑ code : Fin 24 × Fin 16,
          summand (hypercubicCharacterCodeEquiv code) := by
      exact (Equiv.sum_comp hypercubicCharacterCodeEquiv summand).symm
    _ = encodedCharacterMoment parity rank := by
      simp [summand, hypercubicCharacterCodeEquiv,
        encodedCharacterMoment, encodedReflectionCharacterMoment,
        Fintype.sum_prod_type]

/-! ## Reynolds projection and invariant dimension -/

def axisTensorInvariantSubmodule
    (parity : ContractionParity) (rank : ℕ) :
    Submodule ℚ (AxisTensorAssignment rank → ℚ) where
  carrier := {coefficients |
    ∀ h, axisTensorCoefficientRepresentation parity rank h coefficients =
      coefficients}
  zero_mem' := by
    intro h
    exact LinearMap.map_zero _
  add_mem' := by
    intro left right hleft hright h
    rw [LinearMap.map_add, hleft h, hright h]
  smul_mem' := by
    intro scalar coefficients hcoefficients h
    rw [LinearMap.map_smul, hcoefficients h]

/-- Reynolds average over the literal 384-element hypercubic group. -/
def axisTensorReynolds
    (parity : ContractionParity) (rank : ℕ) :
    (AxisTensorAssignment rank → ℚ) →ₗ[ℚ]
      (AxisTensorAssignment rank → ℚ) :=
  (1 / 384 : ℚ) •
    ∑ h : Hypercubic4,
      axisTensorCoefficientRepresentation parity rank h

theorem axisTensorReynolds_invariant
    (parity : ContractionParity) (rank : ℕ)
    (coefficients : AxisTensorAssignment rank → ℚ) :
    axisTensorReynolds parity rank coefficients ∈
      axisTensorInvariantSubmodule parity rank := by
  intro left
  have hsum :
      axisTensorCoefficientRepresentation parity rank left *
          (∑ h : Hypercubic4,
            axisTensorCoefficientRepresentation parity rank h) =
        ∑ h : Hypercubic4,
          axisTensorCoefficientRepresentation parity rank h := by
    rw [Finset.mul_sum]
    simp_rw [← MonoidHom.map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft left)
      (axisTensorCoefficientRepresentation parity rank)
  change axisTensorCoefficientRepresentation parity rank left
      (axisTensorReynolds parity rank coefficients) =
    axisTensorReynolds parity rank coefficients
  unfold axisTensorReynolds
  change
    (axisTensorCoefficientRepresentation parity rank left *
        ((1 / 384 : ℚ) •
          ∑ h : Hypercubic4,
            axisTensorCoefficientRepresentation parity rank h))
      coefficients =
    (((1 / 384 : ℚ) •
      ∑ h : Hypercubic4,
        axisTensorCoefficientRepresentation parity rank h) coefficients)
  rw [mul_smul_comm, hsum]

set_option maxRecDepth 10000 in
theorem axisTensorReynolds_fixes_invariant
    (parity : ContractionParity) (rank : ℕ)
    (coefficients : AxisTensorAssignment rank → ℚ)
    (hinvariant : coefficients ∈ axisTensorInvariantSubmodule parity rank) :
    axisTensorReynolds parity rank coefficients = coefficients := by
  unfold axisTensorReynolds
  change (1 / 384 : ℚ) •
      (∑ h : Hypercubic4,
        axisTensorCoefficientRepresentation parity rank h coefficients) =
    coefficients
  have hsum :
      (∑ h : Hypercubic4,
        axisTensorCoefficientRepresentation parity rank h coefficients) =
      ∑ _h : Hypercubic4, coefficients := by
    apply Finset.sum_congr rfl
    intro h _
    exact hinvariant h
  rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  funext assignment
  change (1 / 384 : ℚ) * (384 * coefficients assignment) =
    coefficients assignment
  ring

theorem axisTensorReynolds_isProj
    (parity : ContractionParity) (rank : ℕ) :
    LinearMap.IsProj (axisTensorInvariantSubmodule parity rank)
      (axisTensorReynolds parity rank) :=
  ⟨axisTensorReynolds_invariant parity rank,
    axisTensorReynolds_fixes_invariant parity rank⟩

/-- Character average on the rank-`n` tensor power. -/
def rawTensorInvariantCharacterMultiplicity
    (parity : ContractionParity) (rank : ℕ) : ℚ :=
  (1 / 384 : ℚ) *
    ∑ h : Hypercubic4,
      parity.character h * signedAxisTrace h ^ rank

/-- The character average is exactly the dimension of the invariant
coefficient-tensor subspace. -/
theorem finrank_axisTensorInvariantSubmodule
    (parity : ContractionParity) (rank : ℕ) :
    (Module.finrank ℚ (axisTensorInvariantSubmodule parity rank) : ℚ) =
      rawTensorInvariantCharacterMultiplicity parity rank := by
  rw [← (axisTensorReynolds_isProj parity rank).trace]
  unfold axisTensorReynolds rawTensorInvariantCharacterMultiplicity
  rw [map_smul, map_sum]
  simp_rw [axisTensorCoefficient_trace]
  norm_num

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia

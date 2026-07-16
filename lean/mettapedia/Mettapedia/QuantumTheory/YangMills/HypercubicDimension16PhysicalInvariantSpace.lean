import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ConjugacyCompression
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSemanticBridge
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalOrbitOperator

/-!
# Reynolds dimension on the honest field-orbit carrier

The signed hypercubic permutation of genuine field-label orbits is realized
as a finite-dimensional rational representation.  Its Reynolds projector has
trace equal to the literal signed fixed-orbit character.  Combining this with
the exact conjugacy-compression bridge identifies the scalar invariant space
in the eight-field, zero-derivative sector with a space of dimension `11654`.

No physical relation rank is asserted in this file.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalInvariantSpace

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCharacter
open HypercubicDimension16CompressionCensus
open HypercubicDimension16ConjugacyCompression

/-! ## Signed orbit representation in one field sector -/

abbrev SectorFieldOrbitSpace (fieldCount derivativeCount : ℕ) :=
  FieldRelabelOrbitCarrier fieldCount derivativeCount →₀ ℚ

def signedSectorFieldOrbitActionBasis (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (target : FieldRelabelOrbitCarrier fieldCount derivativeCount) :
    SectorFieldOrbitSpace fieldCount derivativeCount :=
  target.tensorSign h • Finsupp.single (target.hypercubicAct h) 1

def signedSectorFieldOrbitAction (h : Hypercubic4)
    (fieldCount derivativeCount : ℕ) :
    SectorFieldOrbitSpace fieldCount derivativeCount →ₗ[ℚ]
      SectorFieldOrbitSpace fieldCount derivativeCount :=
  Finsupp.linearCombination ℚ (signedSectorFieldOrbitActionBasis h)

@[simp] theorem signedSectorFieldOrbitAction_single (h : Hypercubic4)
    {fieldCount derivativeCount : ℕ}
    (target : FieldRelabelOrbitCarrier fieldCount derivativeCount)
    (coefficient : ℚ) :
    signedSectorFieldOrbitAction h fieldCount derivativeCount
        (Finsupp.single target coefficient) =
      Finsupp.single (target.hypercubicAct h)
        (coefficient * target.tensorSign h) := by
  simp [signedSectorFieldOrbitAction, signedSectorFieldOrbitActionBasis]

@[simp] theorem signedSectorFieldOrbitAction_one
    {fieldCount derivativeCount : ℕ}
    (value : SectorFieldOrbitSpace fieldCount derivativeCount) :
    signedSectorFieldOrbitAction 1 fieldCount derivativeCount value = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [LinearMap.map_add, hleft, hright]
  | single target coefficient =>
      rw [signedSectorFieldOrbitAction_single,
        FieldRelabelOrbitCarrier.hypercubicAct_one,
        FieldRelabelOrbitCarrier.tensorSign_one]
      simp

theorem signedSectorFieldOrbitAction_mul
    (left right : Hypercubic4) {fieldCount derivativeCount : ℕ}
    (value : SectorFieldOrbitSpace fieldCount derivativeCount) :
    signedSectorFieldOrbitAction (left * right) fieldCount derivativeCount value =
      signedSectorFieldOrbitAction left fieldCount derivativeCount
        (signedSectorFieldOrbitAction right fieldCount derivativeCount value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond =>
      simp only [LinearMap.map_add, hfirst, hsecond]
  | single target coefficient =>
      rw [signedSectorFieldOrbitAction_single,
        signedSectorFieldOrbitAction_single,
        signedSectorFieldOrbitAction_single,
        FieldRelabelOrbitCarrier.hypercubicAct_mul,
        FieldRelabelOrbitCarrier.tensorSign_mul]
      congr 1
      change coefficient *
          (target.tensorSign right *
            (target.hypercubicAct right).tensorSign left) =
        coefficient * target.tensorSign right *
          (target.hypercubicAct right).tensorSign left
      ring

def signedSectorFieldOrbitRepresentation (fieldCount derivativeCount : ℕ) :
    Representation ℚ Hypercubic4
      (SectorFieldOrbitSpace fieldCount derivativeCount) where
  toFun := fun h =>
    signedSectorFieldOrbitAction h fieldCount derivativeCount
  map_one' := by
    apply LinearMap.ext
    exact signedSectorFieldOrbitAction_one
  map_mul' left right := by
    apply LinearMap.ext
    exact signedSectorFieldOrbitAction_mul left right

/-! ## Literal trace and Reynolds projection -/

theorem signedSectorFieldOrbitAction_trace (h : Hypercubic4)
    (fieldCount derivativeCount : ℕ) :
    LinearMap.trace ℚ (SectorFieldOrbitSpace fieldCount derivativeCount)
        (signedSectorFieldOrbitAction h fieldCount derivativeCount) =
      actualOrbitCharacter h fieldCount derivativeCount := by
  rw [LinearMap.trace_eq_matrix_trace ℚ
    (Finsupp.basisSingleOne : Module.Basis
      (FieldRelabelOrbitCarrier fieldCount derivativeCount) ℚ
      (SectorFieldOrbitSpace fieldCount derivativeCount))]
  unfold Matrix.trace actualOrbitCharacter
  apply Finset.sum_congr rfl
  intro target _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change (signedSectorFieldOrbitAction h fieldCount derivativeCount
      (Finsupp.single target 1)) target =
    if target.hypercubicAct h = target then target.tensorSign h else 0
  rw [signedSectorFieldOrbitAction_single]
  change (Finsupp.single (target.hypercubicAct h)
      (1 * target.tensorSign h)) target =
    if target.hypercubicAct h = target then target.tensorSign h else 0
  by_cases hfixed : target.hypercubicAct h = target
  · rw [if_pos hfixed, hfixed]
    simp
  · rw [if_neg hfixed, Finsupp.single_apply]
    simp [hfixed]

def sectorFieldOrbitInvariantSubmodule (fieldCount derivativeCount : ℕ) :
    Submodule ℚ (SectorFieldOrbitSpace fieldCount derivativeCount) where
  carrier := {value |
    ∀ h, signedSectorFieldOrbitAction h fieldCount derivativeCount value = value}
  zero_mem' := by
    intro h
    exact LinearMap.map_zero _
  add_mem' := by
    intro left right hleft hright h
    rw [LinearMap.map_add, hleft h, hright h]
  smul_mem' := by
    intro scalar value hvalue h
    rw [LinearMap.map_smul, hvalue h]

def sectorFieldOrbitReynolds (fieldCount derivativeCount : ℕ) :
    SectorFieldOrbitSpace fieldCount derivativeCount →ₗ[ℚ]
      SectorFieldOrbitSpace fieldCount derivativeCount :=
  (1 / 384 : ℚ) •
    ∑ h : Hypercubic4,
      signedSectorFieldOrbitAction h fieldCount derivativeCount

theorem sectorFieldOrbitReynolds_invariant
    (fieldCount derivativeCount : ℕ)
    (value : SectorFieldOrbitSpace fieldCount derivativeCount) :
    sectorFieldOrbitReynolds fieldCount derivativeCount value ∈
      sectorFieldOrbitInvariantSubmodule fieldCount derivativeCount := by
  intro left
  have hsum :
      signedSectorFieldOrbitAction left fieldCount derivativeCount *
          (∑ h : Hypercubic4,
            signedSectorFieldOrbitAction h fieldCount derivativeCount) =
        ∑ h : Hypercubic4,
          signedSectorFieldOrbitAction h fieldCount derivativeCount := by
    rw [Finset.mul_sum]
    have hmul (h : Hypercubic4) :
        signedSectorFieldOrbitAction left fieldCount derivativeCount *
            signedSectorFieldOrbitAction h fieldCount derivativeCount =
          signedSectorFieldOrbitAction (left * h)
            fieldCount derivativeCount := by
      apply LinearMap.ext
      intro input
      exact (signedSectorFieldOrbitAction_mul left h input).symm
    simp_rw [hmul]
    exact Equiv.sum_comp (Equiv.mulLeft left)
      (signedSectorFieldOrbitRepresentation fieldCount derivativeCount)
  change signedSectorFieldOrbitAction left fieldCount derivativeCount
      (sectorFieldOrbitReynolds fieldCount derivativeCount value) =
    sectorFieldOrbitReynolds fieldCount derivativeCount value
  unfold sectorFieldOrbitReynolds
  change
    (signedSectorFieldOrbitAction left fieldCount derivativeCount *
        ((1 / 384 : ℚ) •
          ∑ h : Hypercubic4,
            signedSectorFieldOrbitAction h fieldCount derivativeCount)) value =
      (((1 / 384 : ℚ) •
        ∑ h : Hypercubic4,
          signedSectorFieldOrbitAction h fieldCount derivativeCount) value)
  rw [mul_smul_comm, hsum]

set_option maxRecDepth 10000 in
theorem sectorFieldOrbitReynolds_fixes_invariant
    (fieldCount derivativeCount : ℕ)
    (value : SectorFieldOrbitSpace fieldCount derivativeCount)
    (hinvariant : value ∈
      sectorFieldOrbitInvariantSubmodule fieldCount derivativeCount) :
    sectorFieldOrbitReynolds fieldCount derivativeCount value = value := by
  unfold sectorFieldOrbitReynolds
  change (1 / 384 : ℚ) •
      (∑ h : Hypercubic4,
        signedSectorFieldOrbitAction h fieldCount derivativeCount value) =
    value
  have hsum :
      (∑ h : Hypercubic4,
        signedSectorFieldOrbitAction h fieldCount derivativeCount value) =
      ∑ _h : Hypercubic4, value := by
    apply Finset.sum_congr rfl
    intro h _
    exact hinvariant h
  rw [hsum, Finset.sum_const, Finset.card_univ,
    Hypercubic4.card_hypercubic4]
  ext target
  change (1 / 384 : ℚ) * (384 * value target) = value target
  ring

theorem sectorFieldOrbitReynolds_isProj
    (fieldCount derivativeCount : ℕ) :
    LinearMap.IsProj
      (sectorFieldOrbitInvariantSubmodule fieldCount derivativeCount)
      (sectorFieldOrbitReynolds fieldCount derivativeCount) :=
  ⟨sectorFieldOrbitReynolds_invariant fieldCount derivativeCount,
    sectorFieldOrbitReynolds_fixes_invariant fieldCount derivativeCount⟩

theorem finrank_sectorFieldOrbitInvariantSubmodule
    (fieldCount derivativeCount : ℕ) :
    (Module.finrank ℚ
        (sectorFieldOrbitInvariantSubmodule fieldCount derivativeCount) : ℚ) =
      (1 / 384 : ℚ) *
        ∑ h : Hypercubic4,
          actualOrbitCharacter h fieldCount derivativeCount := by
  rw [← (sectorFieldOrbitReynolds_isProj
    fieldCount derivativeCount).trace]
  unfold sectorFieldOrbitReynolds
  rw [map_smul, map_sum]
  simp_rw [signedSectorFieldOrbitAction_trace]
  norm_num

/-! ## The honest eight-field scalar dimension -/

theorem fieldEightActualOrbitCharacter_eq_compressed
    (h : Hypercubic4) :
    actualOrbitCharacter h 8 0 = compressedSectorCharacter h 8 := by
  simpa [derivativeCountForFields] using
    (actualOrbitCharacter_eq_compressedSectorCharacter h (7 : Fin 8))

theorem fieldEightActualOrbitCharacter_sum_eq_encoded :
    (∑ h : Hypercubic4, actualOrbitCharacter h 8 0) =
      encodedCompressionMoment ContractionParity.scalar 8 := by
  let summand : Hypercubic4 → ℚ := fun h =>
    actualOrbitCharacter h 8 0
  calc
    (∑ h : Hypercubic4, actualOrbitCharacter h 8 0) =
        ∑ code : Fin 24 × Fin 16,
          summand (hypercubicCharacterCodeEquiv code) := by
      exact (Equiv.sum_comp hypercubicCharacterCodeEquiv summand).symm
    _ = encodedCompressionMoment ContractionParity.scalar 8 := by
      simp [summand, hypercubicCharacterCodeEquiv,
        encodedCompressionMoment, encodedCompressionReflectionMoment,
        Fintype.sum_prod_type,
        fieldEightActualOrbitCharacter_eq_compressed,
        ContractionParity.character]

theorem fieldEightScalarCharacterAverage :
    (1 / 384 : ℚ) *
        ∑ h : Hypercubic4, actualOrbitCharacter h 8 0 =
      11654 := by
  calc
    (1 / 384 : ℚ) *
          ∑ h : Hypercubic4, actualOrbitCharacter h 8 0 =
        encodedCompressionMoment ContractionParity.scalar 8 / 384 := by
      rw [fieldEightActualOrbitCharacter_sum_eq_encoded]
      ring
    _ = compressedInvariantMultiplicity ContractionParity.scalar 8 := rfl
    _ = expectedCompressedInvariantMultiplicity
          ContractionParity.scalar 8 :=
      compressedInvariantMultiplicity_certificate
        ContractionParity.scalar (7 : Fin 8)
    _ = 11654 := rfl

/-- The exact scalar invariant dimension on the genuine eight-field,
zero-derivative orbit carrier. -/
theorem fieldEightScalarInvariantDimension :
    Module.finrank ℚ (sectorFieldOrbitInvariantSubmodule 8 0) = 11654 := by
  have hdimension := finrank_sectorFieldOrbitInvariantSubmodule 8 0
  rw [fieldEightScalarCharacterAverage] at hdimension
  exact_mod_cast hdimension

end HypercubicDimension16PhysicalInvariantSpace
end YangMills
end QuantumTheory
end Mettapedia

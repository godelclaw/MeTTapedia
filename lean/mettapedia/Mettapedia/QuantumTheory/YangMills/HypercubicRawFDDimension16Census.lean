import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificate

/-!
# Exact dimension-sixteen census on the unpadded raw `F,D` carrier

The hypercubic group acts on spacetime indices and leaves trace order,
derivative order, and derivative ownership fixed.  This module counts those
active layout copies exactly, identifies the invariant coefficient space with
one rank-sixteen invariant tensor space per layout, and derives the complete
raw scalar and pseudoscalar counts.

No Bianchi, EOM, IBP, trace, or Cayley--Hamilton relation is imposed here.
Consequently these are exact dimensions of the raw hypercubic-invariant
carrier, not dimensions of the physical operator quotient.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDDimension16Census

open V14HypercubicFDCensus
open HypercubicUnpaddedFDSyntax
open HypercubicRawFDCharacterCensus

def dimension16DerivativeCount (fieldCount : Fin 9) : ℕ :=
  16 - 2 * fieldCount.1

/-- The exact-dimension-sixteen subtype of the previously constructed
unpadded raw syntax. -/
abbrev ExactDimension16UnpaddedRawFDMonomial :=
  {monomial : UnpaddedRawFDMonomial //
    monomial.canonicalDimension = 16}

/-- The unique exact-dimension-sixteen shape with the prescribed number of
field strengths. -/
def dimension16Shape (fieldCount : Fin 9) : FDShape where
  fieldCount := fieldCount
  derivativeCount := ⟨dimension16DerivativeCount fieldCount, by
    dsimp [dimension16DerivativeCount]
    omega⟩
  dimension_le := by
    dsimp [dimension16DerivativeCount]
    omega

@[simp] theorem dimension16Shape_canonicalDimension
    (fieldCount : Fin 9) :
    (dimension16Shape fieldCount).canonicalDimension = 16 := by
  dsimp [dimension16Shape, FDShape.canonicalDimension,
    dimension16DerivativeCount]
  omega

/-- Exact-dimension-sixteen shapes are classified by their field count; the
derivative count is forced to be `16 - 2f`. -/
def dimension16ShapeEquiv :
    Fin 9 ≃ {shape : FDShape // shape.canonicalDimension = 16} where
  toFun fieldCount :=
    ⟨dimension16Shape fieldCount,
      dimension16Shape_canonicalDimension fieldCount⟩
  invFun shape := shape.1.fieldCount
  left_inv fieldCount := rfl
  right_inv shape := by
    rcases shape with ⟨⟨fieldCount, derivativeCount, dimension_le⟩, hexact⟩
    apply Subtype.ext
    have hderivative :
        (dimension16Shape fieldCount).derivativeCount =
          derivativeCount := by
      apply Fin.ext
      change 2 * fieldCount.1 + derivativeCount.1 = 16 at hexact
      dsimp [dimension16Shape, dimension16DerivativeCount]
      omega
    cases hderivative
    rfl

/-- Splitting the exact-dimension subtype into its exact shape and active
sector changes no data. -/
def exactDimension16MonomialShapeSectorEquiv :
    ExactDimension16UnpaddedRawFDMonomial ≃
      (shape : {shape : FDShape // shape.canonicalDimension = 16}) ×'
        UnpaddedFDSector shape.1.fieldCount.1
          shape.1.derivativeCount.1 where
  toFun monomial :=
    ⟨⟨monomial.1.1, monomial.2⟩, monomial.1.2⟩
  invFun data :=
    ⟨⟨data.1.1, data.2⟩, data.1.2⟩
  left_inv monomial := by
    cases monomial with
    | mk monomial exact =>
        cases monomial
        rfl
  right_inv data := by
    cases data with
    | mk shape sector =>
        cases shape
        rfl

/-- Reindex the exact shapes by their field count. -/
def exactDimension16MonomialSectorEquiv :
    ExactDimension16UnpaddedRawFDMonomial ≃
      (fieldCount : Fin 9) ×'
        UnpaddedFDSector fieldCount.1
          (dimension16DerivativeCount fieldCount) :=
  exactDimension16MonomialShapeSectorEquiv |>.trans <|
    (Equiv.psigmaEquivSigma fun shape :
        {shape : FDShape // shape.canonicalDimension = 16} =>
          UnpaddedFDSector shape.1.fieldCount.1
            shape.1.derivativeCount.1) |>.trans <|
      (Equiv.sigmaCongr dimension16ShapeEquiv fun fieldCount =>
        Equiv.refl (UnpaddedFDSector fieldCount.1
          (dimension16DerivativeCount fieldCount))).symm |>.trans <|
        (Equiv.psigmaEquivSigma fun fieldCount : Fin 9 =>
          UnpaddedFDSector fieldCount.1
            (dimension16DerivativeCount fieldCount)).symm

/-- Three active axis families as one disjoint family. -/
def unpaddedAxisAssignmentEquivSum
    (fieldCount derivativeCount : ℕ) :
    UnpaddedAxisAssignment fieldCount derivativeCount ≃
      (((Fin fieldCount ⊕ Fin fieldCount) ⊕ Fin derivativeCount) → Axis) where
  toFun assignment
    | Sum.inl (Sum.inl slot) => assignment.fieldFirst slot
    | Sum.inl (Sum.inr slot) => assignment.fieldSecond slot
    | Sum.inr slot => assignment.derivativeAxis slot
  invFun assignment :=
    { fieldFirst := fun slot => assignment (Sum.inl (Sum.inl slot))
      fieldSecond := fun slot => assignment (Sum.inl (Sum.inr slot))
      derivativeAxis := fun slot => assignment (Sum.inr slot) }
  left_inv assignment := by
    cases assignment
    rfl
  right_inv assignment := by
    funext slot
    rcases slot with (slot | slot) <;>
      rcases slot with (slot | slot) <;> rfl

/-- The two indices of every field strength followed by all derivative
indices give exactly sixteen active spacetime slots. -/
def dimension16AxisSlotEquiv (fieldCount : Fin 9) :
    ((Fin fieldCount.1 ⊕ Fin fieldCount.1) ⊕
        Fin (dimension16DerivativeCount fieldCount)) ≃ Fin 16 :=
  ((Equiv.sumCongr finSumFinEquiv
      (Equiv.refl (Fin (dimension16DerivativeCount fieldCount)))).trans
    finSumFinEquiv).trans
      (finCongr (by
        dsimp [dimension16DerivativeCount]
        omega))

/-- The active axis payload of every exact sector is canonically a rank-16
axis tensor assignment. -/
def dimension16AxisAssignmentEquiv (fieldCount : Fin 9) :
    UnpaddedAxisAssignment fieldCount.1
        (dimension16DerivativeCount fieldCount) ≃
      AxisTensorAssignment 16 :=
  (unpaddedAxisAssignmentEquivSum fieldCount.1
    (dimension16DerivativeCount fieldCount)).trans
      (Equiv.piCongrLeft (fun _ : Fin 16 => Axis)
        (dimension16AxisSlotEquiv fieldCount))

/-- Trace order, derivative order, and derivative ownership at exact
canonical dimension sixteen. -/
abbrev Dimension16FDLayout :=
  (fieldCount : Fin 9) ×'
    (UnpaddedTraceLayout fieldCount.1 ×
      UnpaddedDerivativeLayout fieldCount.1
        (dimension16DerivativeCount fieldCount))

def dimension16LayoutMultiplicityFor (fieldCount : Fin 9) : ℕ :=
  Nat.factorial fieldCount.1 *
    (Nat.factorial (dimension16DerivativeCount fieldCount) *
      fieldCount.1 ^ dimension16DerivativeCount fieldCount)

def dimension16LayoutMultiplicity : ℕ :=
  ∑ fieldCount : Fin 9, dimension16LayoutMultiplicityFor fieldCount

def unpaddedTraceLayoutEquiv (fieldCount : ℕ) :
    UnpaddedTraceLayout fieldCount ≃ Equiv.Perm (Fin fieldCount) where
  toFun layout := layout.traceOrder
  invFun traceOrder := ⟨traceOrder⟩
  left_inv layout := by cases layout; rfl
  right_inv traceOrder := rfl

def unpaddedDerivativeLayoutEquiv
    (fieldCount derivativeCount : ℕ) :
    UnpaddedDerivativeLayout fieldCount derivativeCount ≃
      Equiv.Perm (Fin derivativeCount) ×
        (Fin derivativeCount → Fin fieldCount) where
  toFun layout := (layout.derivativeOrder, layout.derivativeOwner)
  invFun data := ⟨data.1, data.2⟩
  left_inv layout := by cases layout; rfl
  right_inv data := by cases data; rfl

theorem card_unpaddedTraceLayout (fieldCount : ℕ) :
    Fintype.card (UnpaddedTraceLayout fieldCount) =
      Nat.factorial fieldCount := by
  rw [Fintype.card_congr (unpaddedTraceLayoutEquiv fieldCount),
    Fintype.card_perm, Fintype.card_fin]

theorem card_unpaddedDerivativeLayout
    (fieldCount derivativeCount : ℕ) :
    Fintype.card (UnpaddedDerivativeLayout fieldCount derivativeCount) =
      Nat.factorial derivativeCount * fieldCount ^ derivativeCount := by
  rw [Fintype.card_congr
      (unpaddedDerivativeLayoutEquiv fieldCount derivativeCount),
    Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

theorem card_dimension16FDLayout :
    Fintype.card Dimension16FDLayout =
      dimension16LayoutMultiplicity := by
  rw [Fintype.card_congr (Equiv.psigmaEquivSigma fun fieldCount : Fin 9 =>
      UnpaddedTraceLayout fieldCount.1 ×
        UnpaddedDerivativeLayout fieldCount.1
          (dimension16DerivativeCount fieldCount)),
    Fintype.card_sigma]
  unfold dimension16LayoutMultiplicity
  apply Finset.sum_congr rfl
  intro fieldCount _
  rw [Fintype.card_prod, card_unpaddedTraceLayout,
    card_unpaddedDerivativeLayout]
  rfl

theorem dimension16LayoutMultiplicity_exact :
    dimension16LayoutMultiplicity = 5361612271200 := by
  norm_num [dimension16LayoutMultiplicity,
    dimension16LayoutMultiplicityFor, dimension16DerivativeCount,
    Nat.factorial, Fin.sum_univ_succ]

/-! ## One invariant tensor fiber per active layout -/

abbrev Dimension16RawAxisCarrier :=
  Dimension16FDLayout × AxisTensorAssignment 16

/-- The separated layout--tensor presentation is an actual equivalence of
the earlier unpadded exact-dimension carrier, not a replacement syntax. -/
def exactDimension16UnpaddedCarrierEquiv :
    ExactDimension16UnpaddedRawFDMonomial ≃
      Dimension16RawAxisCarrier :=
  exactDimension16MonomialSectorEquiv.trans
    { toFun := fun sector =>
        (⟨sector.1, (sector.2.trace, sector.2.derivatives)⟩,
          dimension16AxisAssignmentEquiv sector.1 sector.2.axes)
      invFun := fun carrier =>
        ⟨carrier.1.1,
          { trace := carrier.1.2.1
            derivatives := carrier.1.2.2
            axes := (dimension16AxisAssignmentEquiv carrier.1.1).symm
              carrier.2 }⟩
      left_inv := by
        intro sector
        cases sector with
        | mk fieldCount sector =>
            cases sector
            simp
      right_inv := by
        intro carrier
        rcases carrier with ⟨⟨fieldCount, layout⟩, axes⟩
        rcases layout with ⟨trace, derivatives⟩
        simp }

abbrev Dimension16RawCoefficients :=
  Dimension16RawAxisCarrier → ℚ

/-- Invariant coefficient tensors on every exact active layout.  Since the
layout data carry the trivial `H(4)` action, invariance is imposed separately
on the rank-sixteen axis tensor in each fiber. -/
def dimension16RawInvariantSubmodule
    (parity : ContractionParity) :
    Submodule ℚ Dimension16RawCoefficients where
  carrier := {coefficients |
    ∀ layout : Dimension16FDLayout,
      (fun assignment => coefficients (layout, assignment)) ∈
        axisTensorInvariantSubmodule parity 16}
  zero_mem' := by
    intro layout
    exact Submodule.zero_mem _
  add_mem' := by
    intro left right hleft hright layout
    exact Submodule.add_mem _ (hleft layout) (hright layout)
  smul_mem' := by
    intro scalar coefficients hcoefficients layout
    exact Submodule.smul_mem _ scalar (hcoefficients layout)

/-- Currying by the inert layout coordinate is an exact linear equivalence
between the full raw invariant space and a finite product of tensor-invariant
fibers. -/
def dimension16RawInvariantEquiv
    (parity : ContractionParity) :
    dimension16RawInvariantSubmodule parity ≃ₗ[ℚ]
      (Dimension16FDLayout → axisTensorInvariantSubmodule parity 16) where
  toFun coefficients layout :=
    ⟨fun assignment => coefficients.1 (layout, assignment),
      coefficients.2 layout⟩
  invFun fibers :=
    ⟨fun carrier => (fibers carrier.1).1 carrier.2,
      fun layout => (fibers layout).2⟩
  left_inv coefficients := by
    ext carrier
    rfl
  right_inv fibers := by
    funext layout
    apply Subtype.ext
    rfl
  map_add' left right := by
    funext layout
    apply Subtype.ext
    rfl
  map_smul' scalar coefficients := by
    funext layout
    apply Subtype.ext
    rfl

theorem finrank_dimension16RawInvariantSubmodule
    (parity : ContractionParity) :
    Module.finrank ℚ (dimension16RawInvariantSubmodule parity) =
      Fintype.card Dimension16FDLayout *
        Module.finrank ℚ (axisTensorInvariantSubmodule parity 16) := by
  rw [(dimension16RawInvariantEquiv parity).finrank_eq,
    Module.finrank_pi_fintype]
  simp

theorem scalar_rank16_tensorMultiplicity :
    Module.finrank ℚ
      (axisTensorInvariantSubmodule ContractionParity.scalar 16) =
      22379179 := by
  have certified := finrank_axisTensorInvariantSubmodule_certificate
    ContractionParity.scalar (16 : Fin 17)
  have hrank : ((16 : Fin 17) : ℕ) = 16 := rfl
  rw [hrank] at certified
  norm_num [certifiedTensorInvariantMultiplicity] at certified
  exact certified

theorem pseudoscalar_rank16_tensorMultiplicity :
    Module.finrank ℚ
      (axisTensorInvariantSubmodule ContractionParity.pseudoscalar 16) =
      22368256 := by
  have certified := finrank_axisTensorInvariantSubmodule_certificate
    ContractionParity.pseudoscalar (16 : Fin 17)
  have hrank : ((16 : Fin 17) : ℕ) = 16 := rfl
  rw [hrank] at certified
  norm_num [certifiedTensorInvariantMultiplicity] at certified
  exact certified

/-- Complete exact scalar count before the relation quotient. -/
theorem scalar_dimension16_rawInvariantCount :
    Module.finrank ℚ
      (dimension16RawInvariantSubmodule ContractionParity.scalar) =
      119988480745781344800 := by
  rw [finrank_dimension16RawInvariantSubmodule,
    card_dimension16FDLayout, dimension16LayoutMultiplicity_exact,
    scalar_rank16_tensorMultiplicity]

/-- Complete exact pseudoscalar count before the relation quotient. -/
theorem pseudoscalar_dimension16_rawInvariantCount :
    Module.finrank ℚ
      (dimension16RawInvariantSubmodule ContractionParity.pseudoscalar) =
      119929915854943027200 := by
  rw [finrank_dimension16RawInvariantSubmodule,
    card_dimension16FDLayout, dimension16LayoutMultiplicity_exact,
    pseudoscalar_rank16_tensorMultiplicity]

/-- The exact dimension-sixteen raw monomial carrier count, before taking
hypercubic invariants or imposing relations. -/
theorem dimension16_rawCarrierCount :
    Fintype.card Dimension16RawAxisCarrier =
      23027949358636282675200 := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, card_dimension16FDLayout,
    dimension16LayoutMultiplicity_exact]
  norm_num

/-- The same carrier count on the literal exact-dimension subtype of the
unpadded syntax. -/
theorem exactDimension16_unpaddedRawCarrierCount :
    Fintype.card ExactDimension16UnpaddedRawFDMonomial =
      23027949358636282675200 := by
  rw [Fintype.card_congr exactDimension16UnpaddedCarrierEquiv]
  exact dimension16_rawCarrierCount

end HypercubicRawFDDimension16Census
end YangMills
end QuantumTheory
end Mettapedia

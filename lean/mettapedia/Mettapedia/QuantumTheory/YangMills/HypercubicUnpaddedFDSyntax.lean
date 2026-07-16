import Mettapedia.QuantumTheory.YangMills.V14HypercubicFDCensus

/-!
# Unpadded finite `F,D` syntax through canonical dimension sixteen

This module replaces fixed-width inactive slots by dependent active index
types.  A sector with `f` field strengths and `d` covariant derivatives uses
exactly `Fin f` field slots and `Fin d` derivative slots.  Trace cycles and
derivative order are permutations of those active types; ownership and all
spacetime indices are likewise defined only on active slots.

The construction is the raw finite syntax on which a relation census can be
built.  It does not identify Bianchi, equation-of-motion, integration-by-parts,
trace, or Cayley--Hamilton relations by declaration.  In particular, its
finiteness and hypercubic action do not themselves assert a quotient basis.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicUnpaddedFDSyntax

open V14HypercubicFDCensus

/-! ## Active, dependent sectors -/

/-- Trace cycles on exactly the active field factors. -/
structure UnpaddedTraceLayout (fieldCount : ℕ) where
  traceOrder : Equiv.Perm (Fin fieldCount)
deriving DecidableEq, Fintype

/-- Derivative order and ownership on exactly the active derivative factors. -/
structure UnpaddedDerivativeLayout
    (fieldCount derivativeCount : ℕ) where
  derivativeOrder : Equiv.Perm (Fin derivativeCount)
  derivativeOwner : Fin derivativeCount → Fin fieldCount
deriving DecidableEq, Fintype

/-- Concrete spacetime indices on exactly the active factors. -/
structure UnpaddedAxisAssignment
    (fieldCount derivativeCount : ℕ) where
  fieldFirst : Fin fieldCount → Axis
  fieldSecond : Fin fieldCount → Axis
  derivativeAxis : Fin derivativeCount → Axis
deriving DecidableEq, Fintype

/-- Raw data in the sector with exactly `fieldCount` field strengths and
`derivativeCount` covariant derivatives.  There are no inactive slots.

`traceOrder` encodes the disjoint cyclic trace words.  `derivativeOrder`
retains the derivative ordering data of the earlier finite surface, while
`derivativeOwner` records which field factor each derivative acts on. -/
structure UnpaddedFDSector (fieldCount derivativeCount : ℕ) where
  trace : UnpaddedTraceLayout fieldCount
  derivatives : UnpaddedDerivativeLayout fieldCount derivativeCount
  axes : UnpaddedAxisAssignment fieldCount derivativeCount
deriving DecidableEq, Fintype

namespace UnpaddedFDSector

def traceOrder {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.trace.traceOrder

def derivativeOrder {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.derivatives.derivativeOrder

def derivativeOwner {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.derivatives.derivativeOwner

def fieldFirst {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.axes.fieldFirst

def fieldSecond {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.axes.fieldSecond

def derivativeAxis {fieldCount derivativeCount : ℕ}
    (sector : UnpaddedFDSector fieldCount derivativeCount) :=
  sector.axes.derivativeAxis

end UnpaddedFDSector

/-- The honest raw carrier through canonical dimension sixteen.  Its shape
proof supplies the bound; its payload contains only active syntax.  Sectors
with derivatives but no field strength are empty because their ownership
function would have codomain `Fin 0`. -/
abbrev UnpaddedRawFDMonomial :=
  (shape : FDShape) ×' UnpaddedFDSector
    shape.fieldCount.1 shape.derivativeCount.1

noncomputable instance : Fintype UnpaddedRawFDMonomial := Fintype.ofFinite _

def UnpaddedRawFDMonomial.shape
    (monomial : UnpaddedRawFDMonomial) : FDShape := monomial.1

def UnpaddedRawFDMonomial.sector
    (monomial : UnpaddedRawFDMonomial) :
    UnpaddedFDSector monomial.shape.fieldCount.1
      monomial.shape.derivativeCount.1 := monomial.2

def UnpaddedRawFDMonomial.canonicalDimension
    (monomial : UnpaddedRawFDMonomial) : ℕ :=
  monomial.shape.canonicalDimension

theorem UnpaddedRawFDMonomial.canonicalDimension_le_sixteen
    (monomial : UnpaddedRawFDMonomial) :
    monomial.canonicalDimension ≤ 16 :=
  monomial.shape.canonicalDimension_le_sixteen

/-! ## Signed hypercubic action -/

/-- Signed coordinate permutations rename only spacetime axes.  Trace cycles,
derivative order, ownership, and the active dependent index types are
unchanged. -/
def UnpaddedRawFDMonomial.act (h : Hypercubic4)
    (monomial : UnpaddedRawFDMonomial) : UnpaddedRawFDMonomial :=
  ⟨monomial.shape,
    { trace := monomial.sector.trace
      derivatives := monomial.sector.derivatives
      axes :=
        { fieldFirst := fun i => h.perm (monomial.sector.fieldFirst i)
          fieldSecond := fun i => h.perm (monomial.sector.fieldSecond i)
          derivativeAxis := fun i => h.perm (monomial.sector.derivativeAxis i) } }⟩

@[simp] theorem UnpaddedRawFDMonomial.act_shape
    (h : Hypercubic4) (monomial : UnpaddedRawFDMonomial) :
    (monomial.act h).shape = monomial.shape := rfl

@[simp] theorem UnpaddedRawFDMonomial.act_fieldFirst
    (h : Hypercubic4) (monomial : UnpaddedRawFDMonomial)
    (i : Fin monomial.shape.fieldCount.1) :
    (monomial.act h).sector.fieldFirst i =
      h.perm (monomial.sector.fieldFirst i) := rfl

@[simp] theorem UnpaddedRawFDMonomial.act_fieldSecond
    (h : Hypercubic4) (monomial : UnpaddedRawFDMonomial)
    (i : Fin monomial.shape.fieldCount.1) :
    (monomial.act h).sector.fieldSecond i =
      h.perm (monomial.sector.fieldSecond i) := rfl

@[simp] theorem UnpaddedRawFDMonomial.act_derivativeAxis
    (h : Hypercubic4) (monomial : UnpaddedRawFDMonomial)
    (i : Fin monomial.shape.derivativeCount.1) :
    (monomial.act h).sector.derivativeAxis i =
      h.perm (monomial.sector.derivativeAxis i) := rfl

@[simp] theorem UnpaddedRawFDMonomial.act_one
    (monomial : UnpaddedRawFDMonomial) :
    monomial.act Hypercubic4.one = monomial := by
  cases monomial with
  | mk shape sector =>
      cases sector
      rfl

theorem UnpaddedRawFDMonomial.act_compose
    (left right : Hypercubic4) (monomial : UnpaddedRawFDMonomial) :
    monomial.act (Hypercubic4.compose left right) =
      (monomial.act right).act left := by
  cases monomial with
  | mk shape sector =>
      cases sector
      rfl

/-- Tensor sign from precisely the active field and derivative indices. -/
def UnpaddedRawFDMonomial.tensorSign (h : Hypercubic4)
    (monomial : UnpaddedRawFDMonomial) : ℚ :=
  (∏ i, Hypercubic4.axisSign h (monomial.sector.fieldFirst i)) *
    (∏ i, Hypercubic4.axisSign h (monomial.sector.fieldSecond i)) *
      ∏ j, Hypercubic4.axisSign h (monomial.sector.derivativeAxis j)

@[simp] theorem UnpaddedRawFDMonomial.tensorSign_one
    (monomial : UnpaddedRawFDMonomial) :
    monomial.tensorSign Hypercubic4.one = 1 := by
  simp [UnpaddedRawFDMonomial.tensorSign]

theorem UnpaddedRawFDMonomial.tensorSign_compose
    (left right : Hypercubic4) (monomial : UnpaddedRawFDMonomial) :
    monomial.tensorSign (Hypercubic4.compose left right) =
      monomial.tensorSign right * (monomial.act right).tensorSign left := by
  classical
  simp only [UnpaddedRawFDMonomial.tensorSign,
    Hypercubic4.axisSign_compose,
    UnpaddedRawFDMonomial.act_fieldFirst,
    UnpaddedRawFDMonomial.act_fieldSecond,
    UnpaddedRawFDMonomial.act_derivativeAxis]
  repeat' rw [Finset.prod_mul_distrib]
  let rightFirst : ℚ :=
    ∏ i, Hypercubic4.axisSign right (monomial.sector.fieldFirst i)
  let leftFirst : ℚ :=
    ∏ i, Hypercubic4.axisSign left
      (right.perm (monomial.sector.fieldFirst i))
  let rightSecond : ℚ :=
    ∏ i, Hypercubic4.axisSign right (monomial.sector.fieldSecond i)
  let leftSecond : ℚ :=
    ∏ i, Hypercubic4.axisSign left
      (right.perm (monomial.sector.fieldSecond i))
  let rightDerivative : ℚ :=
    ∏ i, Hypercubic4.axisSign right (monomial.sector.derivativeAxis i)
  let leftDerivative : ℚ :=
    ∏ i, Hypercubic4.axisSign left
      (right.perm (monomial.sector.derivativeAxis i))
  change
    (rightFirst * leftFirst) * (rightSecond * leftSecond) *
        (rightDerivative * leftDerivative) =
      (rightFirst * rightSecond * rightDerivative) *
        (leftFirst * leftSecond * leftDerivative)
  ring

/-- Exact rational coefficient tensors on the unpadded raw carrier. -/
abbrev UnpaddedRawFDCoefficients := UnpaddedRawFDMonomial → ℚ

/-- Scalar and pseudoscalar covariance on the actual active syntax. -/
def IsHypercubicCoefficientTensor
    (parity : ContractionParity)
    (coefficients : UnpaddedRawFDCoefficients) : Prop :=
  ∀ h monomial,
    coefficients (monomial.act h) =
      parity.character h * monomial.tensorSign h * coefficients monomial

theorem unpaddedRawFDCensus_finite : Finite UnpaddedRawFDMonomial :=
  inferInstance

theorem unpaddedRawFDCensus_card_finite :
    ∃ count : ℕ, Fintype.card UnpaddedRawFDMonomial = count :=
  ⟨Fintype.card UnpaddedRawFDMonomial, rfl⟩

/-! ## Exact sector size -/

/-- Product presentation used to count one active sector. -/
def unpaddedFDSectorEquivProduct (fieldCount derivativeCount : ℕ) :
    UnpaddedFDSector fieldCount derivativeCount ≃
      (Equiv.Perm (Fin fieldCount)) ×
        ((Equiv.Perm (Fin derivativeCount)) ×
          (Fin derivativeCount → Fin fieldCount)) ×
        ((Fin fieldCount → Axis) × (Fin fieldCount → Axis) ×
          (Fin derivativeCount → Axis)) where
  toFun sector :=
    (sector.traceOrder, (sector.derivativeOrder, sector.derivativeOwner),
      (sector.fieldFirst, sector.fieldSecond, sector.derivativeAxis))
  invFun data :=
    { trace := ⟨data.1⟩
      derivatives := ⟨data.2.1.1, data.2.1.2⟩
      axes := ⟨data.2.2.1, data.2.2.2.1, data.2.2.2.2⟩ }
  left_inv := by
    intro sector
    cases sector
    rfl
  right_inv := by
    intro data
    rcases data with ⟨trace, ⟨order, owner⟩, ⟨first, second, axis⟩⟩
    rfl

/-- The exact size of a raw active sector.  Each factor is structural:
trace cycles, derivative order, derivative ownership, and the three families
of spacetime indices. -/
theorem card_unpaddedFDSector (fieldCount derivativeCount : ℕ) :
    Fintype.card (UnpaddedFDSector fieldCount derivativeCount) =
      Nat.factorial fieldCount *
        (Nat.factorial derivativeCount * fieldCount ^ derivativeCount) *
        (4 ^ fieldCount * 4 ^ fieldCount * 4 ^ derivativeCount) := by
  rw [Fintype.card_congr
    (unpaddedFDSectorEquivProduct fieldCount derivativeCount)]
  simp [Fintype.card_perm]
  ring

/-- A concrete canonical-dimension-sixteen sector with two field strengths
and twelve derivatives. -/
def twoFieldTwelveDerivativeShape : FDShape where
  fieldCount := 2
  derivativeCount := 12
  dimension_le := by decide

def embedTwoFieldTwelveDerivativeSector :
    UnpaddedFDSector 2 12 → UnpaddedRawFDMonomial :=
  fun sector => ⟨twoFieldTwelveDerivativeShape, sector⟩

theorem embedTwoFieldTwelveDerivativeSector_injective :
    Function.Injective embedTwoFieldTwelveDerivativeSector := by
  intro left right heq
  exact eq_of_heq (PSigma.mk.inj_iff.mp heq).2

/-- Even before any relation rows are imposed, one honest
canonical-dimension-sixteen sector already has more than `10^22` elements.
This is a certified raw-carrier size, not a quotient-basis count. -/
theorem card_unpaddedRawFDCensus_lower_bound :
    16853370525545870131200 ≤
      Fintype.card UnpaddedRawFDMonomial := by
  have hsector :
      Fintype.card (UnpaddedFDSector 2 12) =
        16853370525545870131200 := by
    rw [card_unpaddedFDSector]
    norm_num [Nat.factorial]
  rw [← hsector]
  exact Fintype.card_le_of_injective
    embedTwoFieldTwelveDerivativeSector
    embedTwoFieldTwelveDerivativeSector_injective

/-! ## No-padding fidelity -/

/-- Equality on the replacement carrier is equality of the shape and every
active datum; there is no additional padding-invariance premise to impose on
coefficient columns. -/
theorem ext_active
    (left right : UnpaddedRawFDMonomial)
    (hshape : left.shape = right.shape)
    (hsector : HEq left.sector right.sector) : left = right := by
  cases left with
  | mk leftShape leftSector =>
      cases right with
      | mk rightShape rightSector =>
          dsimp [UnpaddedRawFDMonomial.shape,
            UnpaddedRawFDMonomial.sector] at hshape hsector
          subst rightShape
          simp_all

end HypercubicUnpaddedFDSyntax
end YangMills
end QuantumTheory
end Mettapedia

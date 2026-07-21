import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16AlphaReduction
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RepresentationTheory.Basic

/-!
# Equivariant sparse relation rows on the dimension-sixteen carrier

This module puts sparse relation rows and the signed hypercubic action on the
same free rational module.  It treats three relations whose meaning is
independent of equations of motion or integration by parts:

* uniform renaming of active field labels;
* swapping adjacent ordered positions owned by different field factors;
* antisymmetry of every field-strength pair.

The first two are syntactic alpha relations.  The third is the standard
identity `F_{μν} = -F_{νμ}`.  Every row is proved equivariant before
any rank computation is attempted.  Swapping derivative positions owned by
the same field is deliberately excluded: covariant derivatives do not
commute, and their later relation must include the curvature commutator.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16RelationEquivariance

open V14HypercubicFDCensus
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction

abbrev RelationCarrier :=
  ExactDimension16DerivativeAlphaReducedCarrier

abbrev RelationSpace := RelationCarrier →₀ ℚ

/-! ## Signed hypercubic action on sparse rows -/

/-- Linear extension of the signed action on basis monomials. -/
def signedRelationAction (h : Hypercubic4) :
    RelationSpace →ₗ[ℚ] RelationSpace :=
  (Finsupp.lift RelationSpace ℚ RelationCarrier)
    (fun carrier =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        Finsupp.single
          (exactDimension16DerivativeAlphaReducedAct h carrier) 1)

@[simp] theorem signedRelationAction_single
    (h : Hypercubic4) (carrier : RelationCarrier) (coefficient : ℚ) :
    signedRelationAction h (Finsupp.single carrier coefficient) =
      Finsupp.single
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        (coefficient *
          exactDimension16DerivativeAlphaReducedTensorSign h carrier) := by
  simp [signedRelationAction, mul_comm]

@[simp] theorem exactDimension16DerivativeAlphaReducedAct_one
    (carrier : RelationCarrier) :
    exactDimension16DerivativeAlphaReducedAct 1 carrier = carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  apply congrArg (fun reduced : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount) =>
    (⟨fieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · funext slot
    simp [derivativeAlphaReducedSectorAct, hypercubic_one_def]
  · funext slot
    simp [derivativeAlphaReducedSectorAct, hypercubic_one_def]
  · apply OrderedDerivativeWord.ext
    · rfl
    · funext position
      simp [derivativeAlphaReducedSectorAct, orderedDerivativeWordAct,
        hypercubic_one_def]

theorem exactDimension16DerivativeAlphaReducedAct_mul
    (left right : Hypercubic4) (carrier : RelationCarrier) :
    exactDimension16DerivativeAlphaReducedAct (left * right) carrier =
      exactDimension16DerivativeAlphaReducedAct left
        (exactDimension16DerivativeAlphaReducedAct right carrier) := by
  rcases carrier with ⟨fieldCount, sector⟩
  apply congrArg (fun reduced : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount) =>
    (⟨fieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · funext slot
    rfl
  · funext slot
    rfl
  · apply OrderedDerivativeWord.ext
    · rfl
    · funext position
      rfl

@[simp] theorem exactDimension16DerivativeAlphaReducedTensorSign_one
    (carrier : RelationCarrier) :
    exactDimension16DerivativeAlphaReducedTensorSign 1 carrier = 1 := by
  rcases carrier with ⟨fieldCount, sector⟩
  simp [exactDimension16DerivativeAlphaReducedTensorSign,
    derivativeAlphaReducedSectorTensorSign, hypercubic_one_def]

theorem exactDimension16DerivativeAlphaReducedTensorSign_mul
    (left right : Hypercubic4) (carrier : RelationCarrier) :
    exactDimension16DerivativeAlphaReducedTensorSign (left * right) carrier =
      exactDimension16DerivativeAlphaReducedTensorSign right carrier *
        exactDimension16DerivativeAlphaReducedTensorSign left
          (exactDimension16DerivativeAlphaReducedAct right carrier) := by
  rcases carrier with ⟨fieldCount, sector⟩
  simp only [exactDimension16DerivativeAlphaReducedTensorSign,
    derivativeAlphaReducedSectorTensorSign, hypercubic_mul_def,
    Hypercubic4.axisSign_compose, Finset.prod_mul_distrib,
    exactDimension16DerivativeAlphaReducedAct,
    derivativeAlphaReducedSectorAct, orderedDerivativeWordAct]
  ac_rfl

@[simp] theorem signedRelationAction_one (value : RelationSpace) :
    signedRelationAction 1 value = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      calc
        signedRelationAction 1 (left + right) =
            signedRelationAction 1 left +
              signedRelationAction 1 right :=
          (signedRelationAction 1).map_add left right
        _ = left + right := congrArg₂ (fun x y => x + y) hleft hright
  | single carrier coefficient =>
      rw [signedRelationAction_single,
        exactDimension16DerivativeAlphaReducedAct_one,
        exactDimension16DerivativeAlphaReducedTensorSign_one]
      simp

theorem signedRelationAction_mul (left right : Hypercubic4)
    (value : RelationSpace) :
    signedRelationAction (left * right) value =
      signedRelationAction left (signedRelationAction right value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond =>
      calc
        signedRelationAction (left * right) (first + second) =
            signedRelationAction (left * right) first +
              signedRelationAction (left * right) second :=
          (signedRelationAction (left * right)).map_add first second
        _ = signedRelationAction left (signedRelationAction right first) +
              signedRelationAction left
                (signedRelationAction right second) :=
          congrArg₂ (fun x y => x + y) hfirst hsecond
        _ = signedRelationAction left
              (signedRelationAction right first +
                signedRelationAction right second) :=
          ((signedRelationAction left).map_add
            (signedRelationAction right first)
            (signedRelationAction right second)).symm
        _ = signedRelationAction left
              (signedRelationAction right (first + second)) := by
          rw [(signedRelationAction right).map_add]
  | single carrier coefficient =>
      rw [signedRelationAction_single, signedRelationAction_single,
        signedRelationAction_single,
        exactDimension16DerivativeAlphaReducedAct_mul,
        exactDimension16DerivativeAlphaReducedTensorSign_mul]
      congr 1
      ring

/-- The signed action on the exact carrier is a rational representation of
the literal hypercubic group. -/
def signedRelationRepresentation :
    Representation ℚ Hypercubic4 RelationSpace where
  toFun := signedRelationAction
  map_one' := by
    apply LinearMap.ext
    exact signedRelationAction_one
  map_mul' left right := by
    apply LinearMap.ext
    exact signedRelationAction_mul left right

/-! ## Field antisymmetry -/

def swapFieldAxes
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (slot : Fin fieldCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := sector.trace
  fieldFirst := Function.update sector.fieldFirst slot
    (sector.fieldSecond slot)
  fieldSecond := Function.update sector.fieldSecond slot
    (sector.fieldFirst slot)
  derivativeWord := sector.derivativeWord

def swapExactFieldAxes (carrier : RelationCarrier)
    (slot : Fin carrier.1.1) : RelationCarrier :=
  ⟨carrier.1, swapFieldAxes carrier.2 slot⟩

theorem swapExactFieldAxes_act (h : Hypercubic4)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) :
    exactDimension16DerivativeAlphaReducedAct h
        (swapExactFieldAxes carrier slot) =
      swapExactFieldAxes
        (exactDimension16DerivativeAlphaReducedAct h carrier) slot := by
  rcases carrier with ⟨fieldCount, sector⟩
  apply congrArg (fun reduced : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount) =>
    (⟨fieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · funext index
    change h.perm
        (Function.update sector.fieldFirst slot
          (sector.fieldSecond slot) index) =
      Function.update (fun source => h.perm (sector.fieldFirst source))
        slot (h.perm (sector.fieldSecond slot)) index
    by_cases hindex : index = slot
    · subst index
      simp [Function.update]
    · simp only [Function.update]
      split <;> simp_all
  · funext index
    change h.perm
        (Function.update sector.fieldSecond slot
          (sector.fieldFirst slot) index) =
      Function.update (fun source => h.perm (sector.fieldSecond source))
        slot (h.perm (sector.fieldFirst slot)) index
    by_cases hindex : index = slot
    · subst index
      simp [Function.update]
    · simp only [Function.update]
      split <;> simp_all
  · rfl

theorem swapExactFieldAxes_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (swapExactFieldAxes carrier slot) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign swapExactFieldAxes swapFieldAxes
  have hfields :
      (∏ index, Hypercubic4.axisSign h
          (Function.update sector.fieldFirst slot
            (sector.fieldSecond slot) index)) *
        (∏ index, Hypercubic4.axisSign h
          (Function.update sector.fieldSecond slot
            (sector.fieldFirst slot) index)) =
      (∏ index, Hypercubic4.axisSign h (sector.fieldFirst index)) *
        ∏ index, Hypercubic4.axisSign h (sector.fieldSecond index) := by
    repeat' rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro index _
    by_cases hindex : index = slot
    · subst index
      simp [Function.update, mul_comm]
    · simp [Function.update, hindex]
  rw [hfields]

/-- Sparse row for `F_{μν} + F_{νμ} = 0` in one field context. -/
def fieldAntisymmetryRow (carrier : RelationCarrier)
    (slot : Fin carrier.1.1) : RelationSpace :=
  Finsupp.single carrier 1 +
    Finsupp.single (swapExactFieldAxes carrier slot) 1

/-- Field antisymmetry is stable under the full signed `H(4)` action. -/
theorem fieldAntisymmetryRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier) (slot : Fin carrier.1.1) :
    signedRelationAction h (fieldAntisymmetryRow carrier slot) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fieldAntisymmetryRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) slot := by
  simp [fieldAntisymmetryRow, swapExactFieldAxes_act,
    swapExactFieldAxes_tensorSign, mul_comm]

/-! ## Derivative shuffles between different field factors -/

def swapDerivativePositions
    {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (left right : Fin derivativeCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace := sector.trace
  fieldFirst := sector.fieldFirst
  fieldSecond := sector.fieldSecond
  derivativeWord :=
    { ownerAtPosition := sector.derivativeWord.ownerAtPosition ∘
        Equiv.swap left right
      axisAtPosition := sector.derivativeWord.axisAtPosition ∘
        Equiv.swap left right }

def swapExactDerivativePositions (carrier : RelationCarrier)
    (left right : Fin (dimension16DerivativeCount carrier.1)) :
    RelationCarrier :=
  ⟨carrier.1, swapDerivativePositions carrier.2 left right⟩

theorem swapExactDerivativePositions_act (h : Hypercubic4)
    (carrier : RelationCarrier)
    (left right : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (swapExactDerivativePositions carrier left right) =
      swapExactDerivativePositions
        (exactDimension16DerivativeAlphaReducedAct h carrier) left right := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

theorem swapExactDerivativePositions_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier)
    (left right : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (swapExactDerivativePositions carrier left right) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign swapExactDerivativePositions
    swapDerivativePositions
  change
    ((∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
        ∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
        (∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition
            ((Equiv.swap left right) position))) =
      ((∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
        ∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
        ∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition position)
  rw [Equiv.prod_comp (Equiv.swap left right)
    (fun position => Hypercubic4.axisSign h
      (sector.derivativeWord.axisAtPosition position))]

/-- Literal adjacency in the global ordered derivative word.  The condition is
essential: exchanging nonadjacent different-owner positions can reverse two
same-owner derivatives lying between them. -/
def AreAdjacentDerivativePositions {count : ℕ}
    (left right : Fin count) : Prop :=
  left.1 + 1 = right.1 ∨ right.1 + 1 = left.1

/-- A valid shuffle site consists of adjacent positions owned by different
field factors. -/
structure DerivativeShuffleSite (carrier : RelationCarrier) where
  left : Fin (dimension16DerivativeCount carrier.1)
  right : Fin (dimension16DerivativeCount carrier.1)
  adjacent : AreAdjacentDerivativePositions left right
  different :
    carrier.2.derivativeWord.ownerAtPosition left ≠
      carrier.2.derivativeWord.ownerAtPosition right

def DerivativeShuffleSite.act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    DerivativeShuffleSite
      (exactDimension16DerivativeAlphaReducedAct h carrier) where
  left := site.left
  right := site.right
  adjacent := site.adjacent
  different := site.different

@[simp] theorem DerivativeShuffleSite.act_left (h : Hypercubic4)
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    (site.act h).left = site.left := rfl

@[simp] theorem DerivativeShuffleSite.act_right (h : Hypercubic4)
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    (site.act h).right = site.right := rfl

/-- Sparse row exchanging one valid adjacent different-owner pair. -/
def derivativeShuffleRow {carrier : RelationCarrier}
    (site : DerivativeShuffleSite carrier) : RelationSpace :=
  Finsupp.single carrier 1 -
    Finsupp.single
      (swapExactDerivativePositions carrier site.left site.right) 1

/-- Every valid adjacent different-owner derivative shuffle is equivariant. -/
theorem derivativeShuffleRow_equivariant (h : Hypercubic4)
    {carrier : RelationCarrier} (site : DerivativeShuffleSite carrier) :
    signedRelationAction h (derivativeShuffleRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        derivativeShuffleRow (site.act h) := by
  simp [derivativeShuffleRow, swapExactDerivativePositions_act,
    swapExactDerivativePositions_tensorSign]
  rw [smul_sub]
  simp

/-! ## Uniform field-label alpha renaming -/

def relabelFields
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    DerivativeAlphaReducedSector fieldCount derivativeCount where
  trace :=
    { traceOrder := rename.symm.trans
        (sector.trace.traceOrder.trans rename) }
  fieldFirst := sector.fieldFirst ∘ rename.symm
  fieldSecond := sector.fieldSecond ∘ rename.symm
  derivativeWord :=
    { ownerAtPosition := rename ∘
        sector.derivativeWord.ownerAtPosition
      axisAtPosition := sector.derivativeWord.axisAtPosition }

def relabelExactFields (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) : RelationCarrier :=
  ⟨carrier.1, relabelFields rename carrier.2⟩

theorem relabelExactFields_act (h : Hypercubic4)
    (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (relabelExactFields carrier rename) =
      relabelExactFields
        (exactDimension16DerivativeAlphaReducedAct h carrier) rename := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

theorem relabelExactFields_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (relabelExactFields carrier rename) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign relabelExactFields relabelFields
  change
    ((∏ slot, Hypercubic4.axisSign h
          (sector.fieldFirst (rename.symm slot))) *
        ∏ slot, Hypercubic4.axisSign h
          (sector.fieldSecond (rename.symm slot))) *
        ∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition position) =
      ((∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
        ∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
        ∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition position)
  rw [Equiv.prod_comp rename.symm
      (fun slot => Hypercubic4.axisSign h (sector.fieldFirst slot)),
    Equiv.prod_comp rename.symm
      (fun slot => Hypercubic4.axisSign h (sector.fieldSecond slot))]

def fieldAlphaRow (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) : RelationSpace :=
  Finsupp.single carrier 1 -
    Finsupp.single (relabelExactFields carrier rename) 1

/-- Uniform field-label alpha rows are equivariant. -/
theorem fieldAlphaRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier)
    (rename : Equiv.Perm (Fin carrier.1.1)) :
    signedRelationAction h (fieldAlphaRow carrier rename) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fieldAlphaRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) rename := by
  simp [fieldAlphaRow, relabelExactFields_act,
    relabelExactFields_tensorSign]
  rw [smul_sub]
  simp

end HypercubicDimension16RelationEquivariance
end YangMills
end QuantumTheory
end Mettapedia

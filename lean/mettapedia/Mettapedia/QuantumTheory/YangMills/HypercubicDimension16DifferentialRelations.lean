import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEquivariance

/-!
# Equivariant Bianchi and equation-of-motion rows

Ordered derivative positions are read from outermost to innermost.  The
Bianchi and equation-of-motion identities are therefore applied only at a
position which is innermost among the derivatives owned by the selected field
factor.  Applying either identity through deeper covariant derivatives would
require commutator correction terms and is intentionally not asserted here.

The Bianchi row is the cyclic sum
`D_a F_{bc} + D_b F_{ca} + D_c F_{ab}`.  The on-shell EOM row is
`∑_μ D_μ F_{μν}`.  Both are constructed as sparse rational rows and
proved equivariant for the same signed `H(4)` action as the alpha and
antisymmetry rows.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16DifferentialRelations

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance

/-! ## A distinguished innermost derivative -/

def IsInnermostDerivative (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) : Prop :=
  carrier.2.derivativeWord.ownerAtPosition position = field ∧
    ∀ deeper, position < deeper →
      carrier.2.derivativeWord.ownerAtPosition deeper ≠ field

theorem isInnermostDerivative_act_iff (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    IsInnermostDerivative
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position ↔
      IsInnermostDerivative carrier field position := by
  rfl

/-! ## Updating one `D F` index triple -/

theorem comp_update
    {index source target : Type*} [DecidableEq index]
    (map : source → target) (values : index → source)
    (slot : index) (value : source) :
    map ∘ Function.update values slot value =
      Function.update (map ∘ values) slot (map value) := by
  funext index
  by_cases hindex : index = slot
  · subst index
    simp [Function.update]
  · simp only [Function.update]
    split <;> simp_all

/-- Replace the derivative axis and the two field-strength axes in one
distinguished `D F` triple. -/
def setFieldDerivativeAxes (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (derivativeAxis fieldFirst fieldSecond : Axis) : RelationCarrier :=
  ⟨carrier.1,
    { trace := carrier.2.trace
      fieldFirst := Function.update carrier.2.fieldFirst field fieldFirst
      fieldSecond := Function.update carrier.2.fieldSecond field fieldSecond
      derivativeWord :=
        { ownerAtPosition := carrier.2.derivativeWord.ownerAtPosition
          axisAtPosition := Function.update
            carrier.2.derivativeWord.axisAtPosition position
              derivativeAxis } }⟩

theorem setFieldDerivativeAxes_act (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (derivativeAxis fieldFirst fieldSecond : Axis) :
    exactDimension16DerivativeAlphaReducedAct h
        (setFieldDerivativeAxes carrier field position
          derivativeAxis fieldFirst fieldSecond) =
      setFieldDerivativeAxes
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position (h.perm derivativeAxis) (h.perm fieldFirst)
          (h.perm fieldSecond) := by
  rcases carrier with ⟨fieldCount, sector⟩
  apply congrArg (fun reduced : DerivativeAlphaReducedSector fieldCount.1
      (dimension16DerivativeCount fieldCount) =>
    (⟨fieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · exact comp_update h.perm sector.fieldFirst field fieldFirst
  · exact comp_update h.perm sector.fieldSecond field fieldSecond
  · apply OrderedDerivativeWord.ext
    · rfl
    · exact comp_update h.perm sector.derivativeWord.axisAtPosition
        position derivativeAxis

theorem prod_axisSign_update (h : Hypercubic4)
    {index : Type*} [Fintype index] [DecidableEq index]
    (values : index → Axis) (slot : index) (value : Axis) :
    (∏ index, Hypercubic4.axisSign h
        (Function.update values slot value index)) =
      Hypercubic4.axisSign h value *
        ∏ index ∈ (Finset.univ.erase slot),
          Hypercubic4.axisSign h (values index) := by
  have hfunctions :
      (fun index => Hypercubic4.axisSign h
          (Function.update values slot value index)) =
        Function.update (fun index => Hypercubic4.axisSign h (values index))
          slot (Hypercubic4.axisSign h value) := by
    exact comp_update (Hypercubic4.axisSign h) values slot value
  rw [hfunctions]
  simpa [Finset.sdiff_singleton_eq_erase] using
    (Finset.prod_update_of_mem (Finset.mem_univ slot)
      (fun index => Hypercubic4.axisSign h (values index))
      (Hypercubic4.axisSign h value))

/-- Product of tensor signs outside the distinguished derivative and field
pair. -/
def fieldDerivativeContextSign (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) : ℚ :=
  (∏ index ∈ (Finset.univ.erase field),
      Hypercubic4.axisSign h (carrier.2.fieldFirst index)) *
    (∏ index ∈ (Finset.univ.erase field),
      Hypercubic4.axisSign h (carrier.2.fieldSecond index)) *
    ∏ index ∈ (Finset.univ.erase position),
      Hypercubic4.axisSign h
        (carrier.2.derivativeWord.axisAtPosition index)

theorem setFieldDerivativeAxes_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (derivativeAxis fieldFirst fieldSecond : Axis) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (setFieldDerivativeAxes carrier field position
          derivativeAxis fieldFirst fieldSecond) =
      Hypercubic4.axisSign h derivativeAxis *
        Hypercubic4.axisSign h fieldFirst *
        Hypercubic4.axisSign h fieldSecond *
          fieldDerivativeContextSign h carrier field position := by
  rcases carrier with ⟨fieldCount, sector⟩
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign setFieldDerivativeAxes
    fieldDerivativeContextSign
  rw [prod_axisSign_update h sector.fieldFirst field fieldFirst,
    prod_axisSign_update h sector.fieldSecond field fieldSecond,
    prod_axisSign_update h sector.derivativeWord.axisAtPosition
      position derivativeAxis]
  ring

theorem tensorSign_eq_triple_mul_context (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h carrier =
      Hypercubic4.axisSign h
          (carrier.2.derivativeWord.axisAtPosition position) *
        Hypercubic4.axisSign h (carrier.2.fieldFirst field) *
        Hypercubic4.axisSign h (carrier.2.fieldSecond field) *
          fieldDerivativeContextSign h carrier field position := by
  rcases carrier with ⟨fieldCount, sector⟩
  have hfirst := Finset.mul_prod_erase Finset.univ
    (fun index => Hypercubic4.axisSign h (sector.fieldFirst index))
    (Finset.mem_univ field)
  have hsecond := Finset.mul_prod_erase Finset.univ
    (fun index => Hypercubic4.axisSign h (sector.fieldSecond index))
    (Finset.mem_univ field)
  have hderivative := Finset.mul_prod_erase Finset.univ
    (fun index => Hypercubic4.axisSign h
      (sector.derivativeWord.axisAtPosition index))
    (Finset.mem_univ position)
  unfold exactDimension16DerivativeAlphaReducedTensorSign
    derivativeAlphaReducedSectorTensorSign fieldDerivativeContextSign
  calc
    ((∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
          ∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
        ∏ index, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition index) =
      (Hypercubic4.axisSign h (sector.fieldFirst field) *
          ∏ index ∈ Finset.univ.erase field,
            Hypercubic4.axisSign h (sector.fieldFirst index)) *
        (Hypercubic4.axisSign h (sector.fieldSecond field) *
          ∏ index ∈ Finset.univ.erase field,
            Hypercubic4.axisSign h (sector.fieldSecond index)) *
        (Hypercubic4.axisSign h
            (sector.derivativeWord.axisAtPosition position) *
          ∏ index ∈ Finset.univ.erase position,
            Hypercubic4.axisSign h
              (sector.derivativeWord.axisAtPosition index)) := by
        rw [hfirst, hsecond, hderivative]
    _ = _ := by ring

theorem axisSign_square (h : Hypercubic4) (axis : Axis) :
    Hypercubic4.axisSign h axis * Hypercubic4.axisSign h axis = 1 := by
  unfold Hypercubic4.axisSign
  split <;> norm_num

/-! ## Bianchi rows -/

def bianchiRotateOne (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    RelationCarrier :=
  setFieldDerivativeAxes carrier field position
    (carrier.2.fieldFirst field)
    (carrier.2.fieldSecond field)
    (carrier.2.derivativeWord.axisAtPosition position)

def bianchiRotateTwo (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    RelationCarrier :=
  setFieldDerivativeAxes carrier field position
    (carrier.2.fieldSecond field)
    (carrier.2.derivativeWord.axisAtPosition position)
    (carrier.2.fieldFirst field)

theorem bianchiRotateOne_act (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (bianchiRotateOne carrier field position) =
      bianchiRotateOne
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position := by
  exact setFieldDerivativeAxes_act h carrier field position
    (carrier.2.fieldFirst field)
    (carrier.2.fieldSecond field)
    (carrier.2.derivativeWord.axisAtPosition position)

theorem bianchiRotateTwo_act (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (bianchiRotateTwo carrier field position) =
      bianchiRotateTwo
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position := by
  exact setFieldDerivativeAxes_act h carrier field position
    (carrier.2.fieldSecond field)
    (carrier.2.derivativeWord.axisAtPosition position)
    (carrier.2.fieldFirst field)

theorem bianchiRotateOne_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (bianchiRotateOne carrier field position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  unfold bianchiRotateOne
  rw [setFieldDerivativeAxes_tensorSign]
  rw [tensorSign_eq_triple_mul_context]
  ring

theorem bianchiRotateTwo_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (bianchiRotateTwo carrier field position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  unfold bianchiRotateTwo
  rw [setFieldDerivativeAxes_tensorSign]
  rw [tensorSign_eq_triple_mul_context]
  ring

def bianchiRow (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    RelationSpace :=
  Finsupp.single carrier 1 +
    Finsupp.single (bianchiRotateOne carrier field position) 1 +
      Finsupp.single (bianchiRotateTwo carrier field position) 1

theorem bianchiRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (_hinnermost : IsInnermostDerivative carrier field position) :
    signedRelationAction h (bianchiRow carrier field position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        bianchiRow
          (exactDimension16DerivativeAlphaReducedAct h carrier)
          field position := by
  simp [bianchiRow, bianchiRotateOne_act, bianchiRotateTwo_act,
    bianchiRotateOne_tensorSign, bianchiRotateTwo_tensorSign,
    smul_add]

/-! ## On-shell equation-of-motion rows -/

def eomTerm (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (contractedAxis : Axis) : RelationCarrier :=
  setFieldDerivativeAxes carrier field position contractedAxis
    contractedAxis (carrier.2.fieldSecond field)

def eomContextSign (h : Hypercubic4) (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) : ℚ :=
  Hypercubic4.axisSign h (carrier.2.fieldSecond field) *
    fieldDerivativeContextSign h carrier field position

theorem eomTerm_act (h : Hypercubic4) (carrier : RelationCarrier)
    (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (contractedAxis : Axis) :
    exactDimension16DerivativeAlphaReducedAct h
        (eomTerm carrier field position contractedAxis) =
      eomTerm (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position (h.perm contractedAxis) := by
  exact setFieldDerivativeAxes_act h carrier field position
    contractedAxis contractedAxis (carrier.2.fieldSecond field)

theorem eomTerm_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (contractedAxis : Axis) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (eomTerm carrier field position contractedAxis) =
      eomContextSign h carrier field position := by
  unfold eomTerm
  rw [setFieldDerivativeAxes_tensorSign]
  unfold eomContextSign
  rw [axisSign_square]
  ring

def eomRow (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    RelationSpace :=
  ∑ contractedAxis : Axis,
    Finsupp.single (eomTerm carrier field position contractedAxis) 1

theorem eomRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (_hinnermost : IsInnermostDerivative carrier field position) :
    signedRelationAction h (eomRow carrier field position) =
      eomContextSign h carrier field position •
        eomRow (exactDimension16DerivativeAlphaReducedAct h carrier)
          field position := by
  rcases carrier with ⟨fieldCount, sector⟩
  change signedRelationAction h
      (eomRow (⟨fieldCount, sector⟩ : RelationCarrier)
        field position) =
    eomContextSign h (⟨fieldCount, sector⟩ : RelationCarrier)
        field position •
      eomRow
        (⟨fieldCount, derivativeAlphaReducedSectorAct h sector⟩ :
          RelationCarrier) field position
  unfold eomRow
  rw [map_sum, Finset.smul_sum]
  let acted : RelationCarrier :=
    ⟨fieldCount, derivativeAlphaReducedSectorAct h sector⟩
  let context : ℚ :=
    eomContextSign h (⟨fieldCount, sector⟩ : RelationCarrier)
      field position
  calc
    ∑ contractedAxis : Axis,
        signedRelationAction h
          (Finsupp.single
            (eomTerm (⟨fieldCount, sector⟩ : RelationCarrier)
              field position contractedAxis) 1) =
      ∑ contractedAxis : Axis,
        Finsupp.single
          (eomTerm acted field position (h.perm contractedAxis))
          context := by
            apply Finset.sum_congr rfl
            intro contractedAxis _
            have hact := eomTerm_act h
              (⟨fieldCount, sector⟩ : RelationCarrier)
              field position contractedAxis
            change exactDimension16DerivativeAlphaReducedAct h
                (eomTerm (⟨fieldCount, sector⟩ : RelationCarrier)
                  field position contractedAxis) =
              eomTerm acted field position (h.perm contractedAxis) at hact
            have hsign := eomTerm_tensorSign h
              (⟨fieldCount, sector⟩ : RelationCarrier)
              field position contractedAxis
            change exactDimension16DerivativeAlphaReducedTensorSign h
                (eomTerm (⟨fieldCount, sector⟩ : RelationCarrier)
                  field position contractedAxis) = context at hsign
            rw [signedRelationAction_single, hact, hsign]
            simp
    _ = ∑ contractedAxis : Axis,
        Finsupp.single (eomTerm acted field position contractedAxis)
          context :=
      Equiv.sum_comp h.perm
        (fun contractedAxis =>
          Finsupp.single (eomTerm acted field position contractedAxis)
            context)
    _ = ∑ contractedAxis : Axis,
        context •
          Finsupp.single (eomTerm acted field position contractedAxis) 1 := by
      apply Finset.sum_congr rfl
      intro contractedAxis _
      simp

end HypercubicDimension16DifferentialRelations
end YangMills
end QuantumTheory
end Mettapedia

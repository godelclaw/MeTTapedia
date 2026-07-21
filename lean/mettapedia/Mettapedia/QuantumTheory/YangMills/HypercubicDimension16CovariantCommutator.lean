import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IBPTraceRelations
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.Fin

/-!
# The equivariant covariant-derivative commutator row

For two adjacent derivative positions owned by the same field letter, this
module constructs the exact cross-sector relation

`D_a D_b X - D_b D_a X - F_ab X + X F_ab = 0`.

The two derivatives are removed in their original relative-order complement,
a new field letter is added, and that curvature letter is inserted immediately
before or after `X` in the same trace cycle.  Thus the relation preserves
canonical dimension and does not replace the curvature commutator by a
same-sector derivative swap.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CovariantCommutator

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance

/-! ## Extending a trace cycle by one last field label -/

def finCastSuccEquivNotLast (count : ℕ) :
    Fin count ≃ {index : Fin (count + 1) // index ≠ Fin.last count} where
  toFun index := ⟨index.castSucc, by
    exact Fin.castSucc_ne_last index⟩
  invFun index :=
    ⟨index.1.1, Fin.val_lt_last index.2⟩
  left_inv index := by
    apply Fin.ext
    rfl
  right_inv index := by
    apply Subtype.ext
    apply Fin.ext
    rfl

def extendFinPermutation {count : ℕ} (permutation : Equiv.Perm (Fin count)) :
    Equiv.Perm (Fin (count + 1)) :=
  permutation.extendDomain (finCastSuccEquivNotLast count)

@[simp] theorem extendFinPermutation_apply_castSucc {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) (index : Fin count) :
    extendFinPermutation permutation index.castSucc =
      (permutation index).castSucc := by
  simpa [extendFinPermutation, finCastSuccEquivNotLast] using
    (Equiv.Perm.extendDomain_apply_image permutation
      (finCastSuccEquivNotLast count) index)

@[simp] theorem extendFinPermutation_apply_last {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) :
    extendFinPermutation permutation (Fin.last count) = Fin.last count := by
  apply Equiv.Perm.extendDomain_apply_not_subtype
  intro hnotlast
  exact hnotlast rfl

/-- Insert the new last label immediately after `after` in its trace cycle. -/
def insertTraceAfter {count : ℕ} (permutation : Equiv.Perm (Fin count))
    (after : Fin count) : Equiv.Perm (Fin (count + 1)) :=
  (extendFinPermutation permutation).trans
    (Equiv.swap (Fin.castSucc (permutation after)) (Fin.last count))

/-- Insert the new last label immediately before `before` in its trace cycle. -/
def insertTraceBefore {count : ℕ} (permutation : Equiv.Perm (Fin count))
    (before : Fin count) : Equiv.Perm (Fin (count + 1)) :=
  insertTraceAfter permutation (permutation.symm before)

theorem insertTraceAfter_apply_after {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) (after : Fin count) :
    insertTraceAfter permutation after after.castSucc = Fin.last count := by
  simp [insertTraceAfter]

theorem insertTraceAfter_apply_last {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) (after : Fin count) :
    insertTraceAfter permutation after (Fin.last count) =
      Fin.castSucc (permutation after) := by
  simp [insertTraceAfter]

theorem insertTraceBefore_apply_last {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) (before : Fin count) :
    insertTraceBefore permutation before (Fin.last count) =
      before.castSucc := by
  simp [insertTraceBefore, insertTraceAfter_apply_last]

theorem insertTraceBefore_apply_predecessor {count : ℕ}
    (permutation : Equiv.Perm (Fin count)) (before : Fin count) :
    insertTraceBefore permutation before
        (permutation.symm before).castSucc = Fin.last count := by
  exact insertTraceAfter_apply_after permutation (permutation.symm before)

/-! ## A valid adjacent same-owner derivative pair -/

structure CovariantCommutatorSite (carrier : RelationCarrier) where
  field : Fin carrier.1.1
  outer : Fin (dimension16DerivativeCount carrier.1)
  inner : Fin (dimension16DerivativeCount carrier.1)
  outer_lt_inner : outer < inner
  owner_outer : carrier.2.derivativeWord.ownerAtPosition outer = field
  owner_inner : carrier.2.derivativeWord.ownerAtPosition inner = field
  no_same_owner_between : ∀ position,
    outer < position → position < inner →
      carrier.2.derivativeWord.ownerAtPosition position ≠ field

def CovariantCommutatorSite.act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    CovariantCommutatorSite
      (exactDimension16DerivativeAlphaReducedAct h carrier) where
  field := site.field
  outer := site.outer
  inner := site.inner
  outer_lt_inner := site.outer_lt_inner
  owner_outer := site.owner_outer
  owner_inner := site.owner_inner
  no_same_owner_between := site.no_same_owner_between

@[simp] theorem CovariantCommutatorSite.act_outer (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    (site.act h).outer = site.outer := rfl

@[simp] theorem CovariantCommutatorSite.act_inner (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    (site.act h).inner = site.inner := rfl

theorem CovariantCommutatorSite.fieldCount_lt_eight
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    carrier.1.1 < 8 := by
  have htwo : 2 ≤ dimension16DerivativeCount carrier.1 := by
    have horder : site.outer.1 < site.inner.1 := site.outer_lt_inner
    have hinner : site.inner.1 <
        dimension16DerivativeCount carrier.1 := site.inner.isLt
    omega
  dsimp [dimension16DerivativeCount] at htwo
  omega

def successorFieldCount (fieldCount : Fin 9) (hlt : fieldCount.1 < 8) :
    Fin 9 :=
  ⟨fieldCount.1 + 1, by omega⟩

@[simp] theorem successorFieldCount_val (fieldCount : Fin 9)
    (hlt : fieldCount.1 < 8) :
    (successorFieldCount fieldCount hlt).1 = fieldCount.1 + 1 := rfl

theorem successorFieldCount_derivativeCount (fieldCount : Fin 9)
    (hlt : fieldCount.1 < 8) :
    dimension16DerivativeCount (successorFieldCount fieldCount hlt) =
      dimension16DerivativeCount fieldCount - 2 := by
  dsimp [dimension16DerivativeCount, successorFieldCount]
  omega

/-! ## Removing the two derivative positions in relative order -/

def retainedDerivativePositions {derivativeCount : ℕ}
    (outer inner : Fin derivativeCount) : Finset (Fin derivativeCount) :=
  (Finset.univ.erase outer).erase inner

theorem card_retainedDerivativePositions {derivativeCount : ℕ}
    (outer inner : Fin derivativeCount) (hne : outer ≠ inner) :
    (retainedDerivativePositions outer inner).card = derivativeCount - 2 := by
  classical
  have hinner : inner ∈ Finset.univ.erase outer := by
    simp [hne.symm]
  unfold retainedDerivativePositions
  rw [Finset.card_erase_of_mem hinner,
    Finset.card_erase_of_mem (Finset.mem_univ outer)]
  simp
  omega

def retainedDerivativeOrderEmbedding {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    Fin (dimension16DerivativeCount
      (successorFieldCount carrier.1 site.fieldCount_lt_eight)) ↪o
      Fin (dimension16DerivativeCount carrier.1) :=
  (retainedDerivativePositions site.outer site.inner).orderEmbOfFin (by
    rw [card_retainedDerivativePositions site.outer site.inner
      (ne_of_lt site.outer_lt_inner)]
    exact (successorFieldCount_derivativeCount carrier.1
      site.fieldCount_lt_eight).symm)

theorem retainedDerivativeOrderEmbedding_mem {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (position : Fin (dimension16DerivativeCount
      (successorFieldCount carrier.1 site.fieldCount_lt_eight))) :
    retainedDerivativeOrderEmbedding site position ∈
      retainedDerivativePositions site.outer site.inner := by
  exact Finset.orderEmbOfFin_mem
    (retainedDerivativePositions site.outer site.inner) _ position

/-! ## The two curvature-insertion targets -/

inductive CurvatureInsertionSide where
  | before
  | after
deriving DecidableEq, Fintype, Repr

def insertedTraceOrder {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide) :
    Equiv.Perm (Fin (carrier.1.1 + 1)) :=
  match side with
  | .before => insertTraceBefore carrier.2.trace.traceOrder site.field
  | .after => insertTraceAfter carrier.2.trace.traceOrder site.field

def insertCurvatureCarrier {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide) : RelationCarrier :=
  let targetFieldCount :=
    successorFieldCount carrier.1 site.fieldCount_lt_eight
  let curvatureFirst :=
    carrier.2.derivativeWord.axisAtPosition site.outer
  let curvatureSecond :=
    carrier.2.derivativeWord.axisAtPosition site.inner
  ⟨targetFieldCount,
    { trace := ⟨insertedTraceOrder site side⟩
      fieldFirst := Fin.lastCases curvatureFirst carrier.2.fieldFirst
      fieldSecond := Fin.lastCases curvatureSecond carrier.2.fieldSecond
      derivativeWord :=
        { ownerAtPosition := fun position =>
            Fin.castSucc (carrier.2.derivativeWord.ownerAtPosition
              (retainedDerivativeOrderEmbedding site position))
          axisAtPosition := fun position =>
            carrier.2.derivativeWord.axisAtPosition
              (retainedDerivativeOrderEmbedding site position) } }⟩

/-! ## Hypercubic naturality of the cross-sector construction -/

theorem comp_lastCases {count : ℕ} {source target : Type*}
    (map : source → target) (lastValue : source)
    (initial : Fin count → source) :
    map ∘ Fin.lastCases lastValue initial =
      Fin.lastCases (map lastValue) (map ∘ initial) := by
  funext index
  cases index using Fin.lastCases <;> simp

theorem insertCurvatureCarrier_act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide) :
    exactDimension16DerivativeAlphaReducedAct h
        (insertCurvatureCarrier site side) =
      insertCurvatureCarrier (site.act h) side := by
  let targetFieldCount :=
    successorFieldCount carrier.1 site.fieldCount_lt_eight
  change (⟨targetFieldCount,
      derivativeAlphaReducedSectorAct h
        (insertCurvatureCarrier site side).2⟩ : RelationCarrier) =
    ⟨targetFieldCount, (insertCurvatureCarrier (site.act h) side).2⟩
  apply congrArg (fun reduced =>
    (⟨targetFieldCount, reduced⟩ : RelationCarrier))
  apply DerivativeAlphaReducedSector.ext
  · rfl
  · exact comp_lastCases h.perm
      (carrier.2.derivativeWord.axisAtPosition site.outer)
      carrier.2.fieldFirst
  · exact comp_lastCases h.perm
      (carrier.2.derivativeWord.axisAtPosition site.inner)
      carrier.2.fieldSecond
  · apply OrderedDerivativeWord.ext
    · rfl
    · rfl

/-! ## Tensor-sign preservation -/

theorem prod_lastCases {count : ℕ} {monoid : Type*}
    [CommMonoid monoid] (lastValue : monoid)
    (initial : Fin count → monoid) :
    (∏ index, Fin.lastCases lastValue initial index) =
      (∏ index, initial index) * lastValue := by
  rw [Fin.prod_univ_castSucc]
  simp

theorem prod_retainedDerivativeOrderEmbedding
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (values : Fin (dimension16DerivativeCount carrier.1) → ℚ) :
    (∏ position, values (retainedDerivativeOrderEmbedding site position)) =
      ∏ position ∈ retainedDerivativePositions site.outer site.inner,
        values position := by
  let retained := retainedDerivativePositions site.outer site.inner
  let hcard : retained.card =
      dimension16DerivativeCount
        (successorFieldCount carrier.1 site.fieldCount_lt_eight) := by
    dsimp [retained]
    rw [card_retainedDerivativePositions site.outer site.inner
      (ne_of_lt site.outer_lt_inner)]
    exact (successorFieldCount_derivativeCount carrier.1
      site.fieldCount_lt_eight).symm
  change (∏ position, values (retained.orderEmbOfFin hcard position)) = _
  calc
    (∏ position, values (retained.orderEmbOfFin hcard position)) =
        ∏ position : retained, values position := by
      exact Equiv.prod_comp (retained.orderIsoOfFin hcard).toEquiv
        (fun position : retained => values position)
    _ = ∏ position ∈ retained, values position := by
      exact Finset.prod_finset_coe values retained

theorem derivativeSign_decompose_at_commutator
    (h : Hypercubic4) {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) :
    (∏ position, Hypercubic4.axisSign h
        (carrier.2.derivativeWord.axisAtPosition position)) =
      Hypercubic4.axisSign h
          (carrier.2.derivativeWord.axisAtPosition site.outer) *
        Hypercubic4.axisSign h
          (carrier.2.derivativeWord.axisAtPosition site.inner) *
        ∏ position ∈ retainedDerivativePositions site.outer site.inner,
          Hypercubic4.axisSign h
            (carrier.2.derivativeWord.axisAtPosition position) := by
  let values := fun position => Hypercubic4.axisSign h
    (carrier.2.derivativeWord.axisAtPosition position)
  have hinner : site.inner ∈ Finset.univ.erase site.outer := by
    simp [ne_of_lt site.outer_lt_inner |>.symm]
  have houterProduct := Finset.mul_prod_erase Finset.univ values
    (Finset.mem_univ site.outer)
  have hinnerProduct := Finset.mul_prod_erase
    (Finset.univ.erase site.outer) values hinner
  change (∏ position, values position) =
    values site.outer * values site.inner *
      ∏ position ∈ retainedDerivativePositions site.outer site.inner,
        values position
  unfold retainedDerivativePositions
  rw [← houterProduct, ← hinnerProduct]
  ring

theorem insertCurvatureCarrier_tensorSign (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier)
    (side : CurvatureInsertionSide) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (insertCurvatureCarrier site side) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  let curvatureFirst := sector.derivativeWord.axisAtPosition site.outer
  let curvatureSecond := sector.derivativeWord.axisAtPosition site.inner
  change
    ((∏ slot : Fin (fieldCount.1 + 1), Hypercubic4.axisSign h
          (Fin.lastCases curvatureFirst sector.fieldFirst slot)) *
        ∏ slot : Fin (fieldCount.1 + 1), Hypercubic4.axisSign h
          (Fin.lastCases curvatureSecond sector.fieldSecond slot)) *
        (∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition
            (retainedDerivativeOrderEmbedding site position))) =
      ((∏ slot, Hypercubic4.axisSign h (sector.fieldFirst slot)) *
        ∏ slot, Hypercubic4.axisSign h (sector.fieldSecond slot)) *
        ∏ position, Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition position)
  have hfirstFunction :
      (fun slot : Fin (fieldCount.1 + 1) => Hypercubic4.axisSign h
        (Fin.lastCases curvatureFirst sector.fieldFirst slot)) =
      Fin.lastCases (Hypercubic4.axisSign h curvatureFirst)
        (fun slot => Hypercubic4.axisSign h (sector.fieldFirst slot)) :=
    comp_lastCases (Hypercubic4.axisSign h) curvatureFirst
      sector.fieldFirst
  have hsecondFunction :
      (fun slot : Fin (fieldCount.1 + 1) => Hypercubic4.axisSign h
        (Fin.lastCases curvatureSecond sector.fieldSecond slot)) =
      Fin.lastCases (Hypercubic4.axisSign h curvatureSecond)
        (fun slot => Hypercubic4.axisSign h (sector.fieldSecond slot)) :=
    comp_lastCases (Hypercubic4.axisSign h) curvatureSecond
      sector.fieldSecond
  have hretained := prod_retainedDerivativeOrderEmbedding site
    (fun position => Hypercubic4.axisSign h
      (sector.derivativeWord.axisAtPosition position))
  change
    (∏ position, Hypercubic4.axisSign h
        (sector.derivativeWord.axisAtPosition
          (retainedDerivativeOrderEmbedding site position))) =
      ∏ position ∈ retainedDerivativePositions site.outer site.inner,
        Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition position) at hretained
  have hdecompose := derivativeSign_decompose_at_commutator h site
  change
    (∏ position, Hypercubic4.axisSign h
        (sector.derivativeWord.axisAtPosition position)) =
      Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition site.outer) *
        Hypercubic4.axisSign h
          (sector.derivativeWord.axisAtPosition site.inner) *
        ∏ position ∈ retainedDerivativePositions site.outer site.inner,
          Hypercubic4.axisSign h
            (sector.derivativeWord.axisAtPosition position) at hdecompose
  rw [hfirstFunction, hsecondFunction, prod_lastCases, prod_lastCases,
    hretained, hdecompose]
  dsimp [curvatureFirst, curvatureSecond]
  ring

/-! ## The four-term commutator row -/

def covariantCommutatorRow {carrier : RelationCarrier}
    (site : CovariantCommutatorSite carrier) : RelationSpace :=
  Finsupp.single carrier 1 -
      Finsupp.single
        (swapExactDerivativePositions carrier site.outer site.inner) 1 -
    Finsupp.single (insertCurvatureCarrier site .before) 1 +
      Finsupp.single (insertCurvatureCarrier site .after) 1

/-- The genuine cross-sector commutator row is stable under the signed
hypercubic action. -/
theorem covariantCommutatorRow_equivariant (h : Hypercubic4)
    {carrier : RelationCarrier} (site : CovariantCommutatorSite carrier) :
    signedRelationAction h (covariantCommutatorRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        covariantCommutatorRow (site.act h) := by
  unfold covariantCommutatorRow
  simp only [map_add, map_sub, signedRelationAction_single, one_mul,
    swapExactDerivativePositions_act,
    swapExactDerivativePositions_tensorSign,
    insertCurvatureCarrier_act, insertCurvatureCarrier_tensorSign,
    smul_add, smul_sub, Finsupp.smul_single]
  simp [CovariantCommutatorSite.act]

end HypercubicDimension16CovariantCommutator
end YangMills
end QuantumTheory
end Mettapedia

import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.Logic.TheoryModel.ExpectedWeakness
import Mathlib.Data.ENat.Lattice

/-!
# Observers as obligations: admissible implementations and their best cost

An implementation is anything that emits an observation stream.  An observer
reads a stream; the obligation it places on an implementation is to observe
what the reference implementation observes.  The implementations meeting that
obligation are its admissible class (`admissible`).

**The weakness order.**  An observer that sees no more than another
(`Coarser`) places a weaker obligation: its admissible class contains the
other's (`admissible_mono`).  In the theory–model reading the admissible class
is exactly the model class of the reference's observed theory in the full
predicate language (`admissible_eq_models`); that theory is the weakest
obligation whose models all preserve the observer
(`isWeakestAdmissible_observed`), and every monotone measure of its weakness
grows when the observer coarsens (`weakness_mono`).
The collapse algebras form such a chain: the bag is a function of the ordered
collection, the count a function of the bag, existence a function of the count
(`bag_eq_coe_collect`, `count_eq_card_bag`, `any_eq_count_ne_zero`), so their
admissible classes are nested (`admissible_chain`).

**Certificates are inclusions.**  The capability certificates of a collapse
algebra name implementations that are admissible for it: with associativity and
commutativity, every implementation emitting a permutation of the reference
stream (`perm_admissible`, the per-implementation form of
`CollapseObservationContract.completeBag_adequate`); with idempotence, one that
omits an adjacent duplicate (`dedup_admissible`); with counted-row coherence,
one that emits a counted row instead of its unit rows (`counted_admissible`);
for existence, one that stops after any prefix containing a witness
(`any_prefix_admissible`, which extends the first-answer readout of
`CollapseObservationContract.any_first_adequate`).  Completion demands, how
much of a producer must be observed, stay in that module; this one compares
observers by the implementations they admit.

**Best cost.**  For any cost of implementations in a complete lattice, the best
admissible cost under a coarser observer is at most the best under the finer
one (`bestCost_anti`).  A weaker obligation bounds the achievable optimum from
above; it says nothing about any particular implementation.  The controls
separate the three cases: the weaker obligation can lower the optimum
(`bag_strictly_cheaper`), leave it unchanged (`bag_no_cheaper_under_flat_cost`),
and admit an implementation costlier than the reference
(`weaker_admits_costlier`).

Scope: implementations are compared by their completed emission streams, as in
`CollapseAlgebra`; effects, interleavings, partial runs and resource lifetimes
are not observed here, and costs are supplied, not derived from a machine.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.CollapseObligation

open Set
open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.Logic.TheoryModel

universe uO uRes uRes' uImpl uW

section Obligation

variable {O : Type uO} {Res : Type uRes} {Res' : Type uRes'} {Impl : Type uImpl}

/-- The implementations whose emissions an observer cannot tell from the
reference's. -/
def admissible (obs : List O → Res) (emits : Impl → List O) (reference : Impl) : Set Impl :=
  {impl | obs (emits impl) = obs (emits reference)}

theorem reference_admissible (obs : List O → Res) (emits : Impl → List O) (reference : Impl) :
    reference ∈ admissible obs emits reference :=
  rfl

/-- `coarse` sees no more than `fine`: streams that `fine` identifies,
`coarse` identifies too. -/
def Coarser (fine : List O → Res) (coarse : List O → Res') : Prop :=
  ∀ l l' : List O, fine l = fine l' → coarse l = coarse l'

theorem coarser_of_factor {fine : List O → Res} {coarse : List O → Res'} (g : Res → Res')
    (factors : ∀ l, coarse l = g (fine l)) : Coarser fine coarse := by
  intro l l' same
  rw [factors l, factors l', same]

theorem Coarser.trans {Res'' : Type uRes} {fine : List O → Res} {middle : List O → Res'}
    {coarse : List O → Res''} (first : Coarser fine middle) (second : Coarser middle coarse) :
    Coarser fine coarse :=
  fun l l' same => second l l' (first l l' same)

/-- **A coarser observer places a weaker obligation**: it admits every
implementation the finer one admits. -/
theorem admissible_mono {fine : List O → Res} {coarse : List O → Res'} (coarser : Coarser fine coarse)
    (emits : Impl → List O) (reference : Impl) :
    admissible fine emits reference ⊆ admissible coarse emits reference :=
  fun _ same => coarser _ _ same

/-- The indistinguishability an observer induces on implementations. -/
def kernel (obs : List O → Res) (emits : Impl → List O) : Setoid Impl :=
  Setoid.ker fun impl => obs (emits impl)

theorem admissible_eq_saturation (obs : List O → Res) (emits : Impl → List O) (reference : Impl) :
    admissible obs emits reference = saturation (kernel obs emits) {reference} := by
  ext impl
  rw [ExpectedWeakness.mem_saturation_singleton]
  exact ⟨fun same => same.symm, fun same => same.symm⟩

/-- **The admissible class is the model class of the obligation**: the models,
in the full predicate language, of what the observer can say about the
reference. -/
theorem admissible_eq_models (obs : List O → Res) (emits : Impl → List O) (reference : Impl) :
    admissible obs emits reference =
      models predicateSat (observedTheory predicateSat (kernel obs emits) {reference}) := by
  rw [admissible_eq_saturation,
    ExpectedWeakness.Control.predicate_class_eq_models (kernel obs emits)
      (fun _ _ notNot => Classical.byContradiction notNot) reference]

/-- **The weakest obligation that preserves an observer is the observer's own
theory of the reference**: it is a weakest theory among those whose models are
all admissible. -/
theorem isWeakestAdmissible_observed (obs : List O → Res) (emits : Impl → List O)
    (reference : Impl) :
    IsWeakestAdmissible predicateSat (within (admissible obs emits reference))
      (observedTheory predicateSat (kernel obs emits) {reference}) := by
  constructor
  · show models predicateSat (observedTheory predicateSat (kernel obs emits) {reference}) ⊆
      admissible obs emits reference
    rw [← admissible_eq_models]
  · intro other inside φ member impl model
    have admitted : impl ∈ models predicateSat
        (observedTheory predicateSat (kernel obs emits) {reference}) := by
      rw [← admissible_eq_models]
      exact inside model
    exact admitted member

/-- **Bennett-style weakness of the obligation grows when the observer
coarsens**, for every monotone measure of model classes. -/
theorem weakness_mono {W : Type uW} [Preorder W] {μ : Set Impl → W} (monotone : MonotoneMeasure μ)
    {fine : List O → Res} {coarse : List O → Res'} (coarser : Coarser fine coarse)
    (emits : Impl → List O) (reference : Impl) :
    weaknessOf predicateSat μ (observedTheory predicateSat (kernel fine emits) {reference}) ≤
      weaknessOf predicateSat μ (observedTheory predicateSat (kernel coarse emits) {reference}) := by
  unfold weaknessOf
  rw [← admissible_eq_models, ← admissible_eq_models]
  exact monotone (admissible_mono coarser emits reference)

/-! ## Best cost -/

section Cost

variable {W : Type uW} [CompleteLattice W]

/-- The best cost of an admissible implementation. -/
noncomputable def bestCost (obs : List O → Res) (emits : Impl → List O) (cost : Impl → W)
    (reference : Impl) : W :=
  ⨅ impl ∈ admissible obs emits reference, cost impl

theorem bestCost_le (obs : List O → Res) (emits : Impl → List O) (cost : Impl → W)
    {reference impl : Impl} (member : impl ∈ admissible obs emits reference) :
    bestCost obs emits cost reference ≤ cost impl :=
  biInf_le cost member

/-- The reference itself bounds the best cost. -/
theorem bestCost_le_reference (obs : List O → Res) (emits : Impl → List O) (cost : Impl → W)
    (reference : Impl) : bestCost obs emits cost reference ≤ cost reference :=
  bestCost_le obs emits cost (reference_admissible obs emits reference)

/-- **Weakening the obligation cannot raise the best achievable cost.** -/
theorem bestCost_anti {fine : List O → Res} {coarse : List O → Res'} (coarser : Coarser fine coarse)
    (emits : Impl → List O) (cost : Impl → W) (reference : Impl) :
    bestCost coarse emits cost reference ≤ bestCost fine emits cost reference :=
  biInf_mono fun _ member => admissible_mono coarser emits reference member

end Cost

end Obligation

/-! ## The collapse chain: collection, bag, count, existence -/

section Chain

variable {Ans Receipt : Type}

theorem bag_eq_coe_collect (l : List (Obs Ans Receipt)) :
    collapseWith (BagAlg Ans Receipt) l =
      ((collapseWith (Collect Ans Receipt) l : List Ans) : Multiset Ans) := by
  show foldStream (BagAlg Ans Receipt) l =
    ((foldStream (Collect Ans Receipt) l : List Ans) : Multiset Ans)
  induction l with
  | nil => rfl
  | cons o rest ih =>
      rw [foldStream_cons, foldStream_cons, ih]
      show Multiset.replicate o.multiplicity o.answer + _ =
        ((List.replicate o.multiplicity o.answer ++ _ : List Ans) : Multiset Ans)
      rw [← Multiset.coe_add, Multiset.coe_replicate]

theorem count_eq_card_bag (l : List (Obs Ans Receipt)) :
    collapseWith (CountAlg Ans Receipt) l = Multiset.card (collapseWith (BagAlg Ans Receipt) l) := by
  show foldStream (CountAlg Ans Receipt) l = Multiset.card (foldStream (BagAlg Ans Receipt) l)
  induction l with
  | nil => rfl
  | cons o rest ih =>
      simp only [foldStream_cons, ih]
      simp [CountAlg, BagAlg]

theorem any_eq_count_ne_zero (l : List (Obs Ans Receipt)) :
    collapseWith (AnyAlg Ans Receipt) l = decide (collapseWith (CountAlg Ans Receipt) l ≠ 0) := by
  show foldStream (AnyAlg Ans Receipt) l = decide (foldStream (CountAlg Ans Receipt) l ≠ 0)
  induction l with
  | nil => rfl
  | cons o rest ih =>
      rw [foldStream_cons, foldStream_cons, ih]
      show (decide (o.multiplicity ≠ 0) || decide (foldStream (CountAlg Ans Receipt) rest ≠ 0)) =
        decide (o.multiplicity + foldStream (CountAlg Ans Receipt) rest ≠ 0)
      by_cases first : o.multiplicity = 0 <;>
        by_cases second : foldStream (CountAlg Ans Receipt) rest = 0 <;> simp [first, second]

theorem collect_coarser_bag :
    Coarser (collapseWith (Collect Ans Receipt)) (collapseWith (BagAlg Ans Receipt)) :=
  coarser_of_factor (fun l => (l : Multiset Ans)) bag_eq_coe_collect

theorem bag_coarser_count :
    Coarser (collapseWith (BagAlg Ans Receipt)) (collapseWith (CountAlg Ans Receipt)) :=
  coarser_of_factor Multiset.card count_eq_card_bag

theorem count_coarser_any :
    Coarser (collapseWith (CountAlg Ans Receipt)) (collapseWith (AnyAlg Ans Receipt)) :=
  coarser_of_factor (fun n => decide (n ≠ 0)) any_eq_count_ne_zero

/-- **The admissible classes of the collapse chain are nested.** -/
theorem admissible_chain {Impl : Type uImpl} (emits : Impl → List (Obs Ans Receipt))
    (reference : Impl) :
    admissible (collapseWith (Collect Ans Receipt)) emits reference ⊆
        admissible (collapseWith (BagAlg Ans Receipt)) emits reference ∧
      admissible (collapseWith (BagAlg Ans Receipt)) emits reference ⊆
        admissible (collapseWith (CountAlg Ans Receipt)) emits reference ∧
      admissible (collapseWith (CountAlg Ans Receipt)) emits reference ⊆
        admissible (collapseWith (AnyAlg Ans Receipt)) emits reference :=
  ⟨admissible_mono collect_coarser_bag emits reference,
    admissible_mono bag_coarser_count emits reference,
    admissible_mono count_coarser_any emits reference⟩

end Chain

/-! ## Certificates name admissible implementations -/

section Certificates

variable {O R Result : Type} {Impl : Type uImpl} {emits : Impl → List O}

/-- **Reordering.**  With associativity and commutativity, an implementation
emitting a permutation of the reference stream is admissible. -/
theorem perm_admissible (A : CollapseAlgebra O R Result) (monoid : MonoidCert A) (comm : CommCert A)
    {impl reference : Impl} (perm : (emits impl).Perm (emits reference)) :
    impl ∈ admissible (collapseWith A) emits reference :=
  CollapseObservationContract.completeBag_adequate A monoid comm (emits reference) (emits impl) perm

/-- **Deduplication.**  With associativity and idempotence, an implementation
that omits an adjacent duplicate is admissible. -/
theorem dedup_admissible (A : CollapseAlgebra O R Result) (monoid : MonoidCert A) (idem : IdemCert A)
    {impl reference : Impl} (o : O) (rest : List O) (deduplicated : emits impl = o :: rest)
    (duplicated : emits reference = o :: o :: rest) :
    impl ∈ admissible (collapseWith A) emits reference := by
  show A.finish (foldStream A (emits impl)) = A.finish (foldStream A (emits reference))
  rw [deduplicated, duplicated, fold_dedup_adjacent A monoid idem o rest]

/-- **Counted rows.**  With associativity and counted-row coherence, an
implementation that emits one counted row where the reference emits its unit
rows is admissible. -/
theorem counted_admissible {Ans Receipt : Type} {emits : Impl → List (Obs Ans Receipt)}
    (A : CollapseAlgebra (Obs Ans Receipt) R Result) (monoid : MonoidCert A)
    (coherent : MultCoherenceCert A) (zero : ∀ a ρ, A.emit ⟨a, 0, ρ⟩ = A.zero)
    {impl reference : Impl} (o : Obs Ans Receipt) (rest : List (Obs Ans Receipt))
    (counted : emits impl = o :: rest) (expanded : emits reference = expandObs o ++ rest) :
    impl ∈ admissible (collapseWith A) emits reference := by
  show A.finish (foldStream A (emits impl)) = A.finish (foldStream A (emits reference))
  rw [counted, expanded, foldStream_append A monoid, foldStream_cons,
    fold_counted_row A coherent zero o]

/-- Existence is decided by any witness. -/
theorem any_true_of_witness {Ans Receipt : Type} :
    ∀ (l : List (Obs Ans Receipt)), (∃ o ∈ l, o.multiplicity ≠ 0) →
      collapseWith (AnyAlg Ans Receipt) l = true
  | [], ⟨_, member, _⟩ => absurd member (List.not_mem_nil)
  | o :: rest, ⟨witness, member, nonzero⟩ => by
      show foldStream (AnyAlg Ans Receipt) (o :: rest) = true
      rw [foldStream_cons]
      rcases List.mem_cons.mp member with same | later
      · subst same
        simp [AnyAlg, nonzero]
      · have tail := any_true_of_witness rest ⟨witness, later, nonzero⟩
        change foldStream (AnyAlg Ans Receipt) rest = true at tail
        show (AnyAlg Ans Receipt).combine ((AnyAlg Ans Receipt).emit o)
          (foldStream (AnyAlg Ans Receipt) rest) = true
        rw [tail]
        simp [AnyAlg]

/-- **Early stopping.**  For existence, an implementation that stops after a
prefix containing a witness is admissible. -/
theorem any_prefix_admissible {Ans Receipt : Type} {emits : Impl → List (Obs Ans Receipt)}
    {impl reference : Impl} (pre suffix : List (Obs Ans Receipt))
    (witness : ∃ o ∈ pre, o.multiplicity ≠ 0) (stopped : emits impl = pre)
    (full : emits reference = pre ++ suffix) :
    impl ∈ admissible (collapseWith (AnyAlg Ans Receipt)) emits reference := by
  show collapseWith (AnyAlg Ans Receipt) (emits impl) =
    collapseWith (AnyAlg Ans Receipt) (emits reference)
  obtain ⟨o, member, nonzero⟩ := witness
  rw [stopped, full, any_true_of_witness pre ⟨o, member, nonzero⟩,
    any_true_of_witness (pre ++ suffix) ⟨o, List.mem_append_left suffix member, nonzero⟩]

end Certificates

/-! ## Controls: weakness bounds the optimum, cost evidence decides it -/

namespace Control

/-- Three implementations of a query with two answers: in the reference order,
reversed, and reversed by a slower route. -/
inductive Plan
  | inOrder
  | reversed
  | slowReversed
  deriving DecidableEq

open Plan

def emits : Plan → List (Obs Nat Unit)
  | inOrder => [⟨0, 1, ()⟩, ⟨1, 1, ()⟩]
  | reversed => [⟨1, 1, ()⟩, ⟨0, 1, ()⟩]
  | slowReversed => [⟨1, 1, ()⟩, ⟨0, 1, ()⟩]

/-- A declared cost in which emitting the second answer first is cheaper, for
instance because an index finds it first. -/
def selectiveCost : Plan → ℕ∞
  | inOrder => 2
  | reversed => 1
  | slowReversed => 5

/-- A cost that does not depend on the order. -/
def flatCost : Plan → ℕ∞ :=
  fun _ => 1

theorem reversed_not_collect : reversed ∉ admissible (collapseWith (Collect Nat Unit)) emits inOrder := by
  intro same
  change collapseWith (Collect Nat Unit) [⟨1, 1, ()⟩, ⟨0, 1, ()⟩] =
    collapseWith (Collect Nat Unit) [⟨0, 1, ()⟩, ⟨1, 1, ()⟩] at same
  simp [collapseWith, Collect, foldStream] at same

theorem slowReversed_not_collect :
    slowReversed ∉ admissible (collapseWith (Collect Nat Unit)) emits inOrder := by
  intro same
  change collapseWith (Collect Nat Unit) [⟨1, 1, ()⟩, ⟨0, 1, ()⟩] =
    collapseWith (Collect Nat Unit) [⟨0, 1, ()⟩, ⟨1, 1, ()⟩] at same
  simp [collapseWith, Collect, foldStream] at same

theorem collect_admissible_eq :
    admissible (collapseWith (Collect Nat Unit)) emits inOrder = {inOrder} := by
  ext plan
  constructor
  · intro member
    cases plan with
    | inOrder => rfl
    | reversed => exact (reversed_not_collect member).elim
    | slowReversed => exact (slowReversed_not_collect member).elim
  · rintro rfl
    rfl

theorem swap_perm : (emits reversed).Perm (emits inOrder) :=
  List.Perm.swap _ _ []

theorem bag_admissible_eq :
    admissible (collapseWith (BagAlg Nat Unit)) emits inOrder = univ := by
  refine eq_univ_of_forall fun plan => ?_
  cases plan with
  | inOrder => rfl
  | reversed => exact perm_admissible _ bag_monoid bag_comm swap_perm
  | slowReversed => exact perm_admissible _ bag_monoid bag_comm (List.Perm.swap _ _ [])

theorem bestCost_collect_selective :
    bestCost (collapseWith (Collect Nat Unit)) emits selectiveCost inOrder = 2 := by
  unfold bestCost
  rw [collect_admissible_eq]
  simp [selectiveCost]

theorem bestCost_bag_selective :
    bestCost (collapseWith (BagAlg Nat Unit)) emits selectiveCost inOrder = 1 := by
  unfold bestCost
  rw [bag_admissible_eq]
  apply le_antisymm
  · exact biInf_le selectiveCost (mem_univ reversed)
  · refine le_iInf₂ fun plan _ => ?_
    cases plan <;> simp [selectiveCost]

/-- **The weaker obligation can lower the best cost**, under a cost model that
rewards the order it frees. -/
theorem bag_strictly_cheaper :
    bestCost (collapseWith (BagAlg Nat Unit)) emits selectiveCost inOrder <
      bestCost (collapseWith (Collect Nat Unit)) emits selectiveCost inOrder := by
  rw [bestCost_bag_selective, bestCost_collect_selective]
  decide

/-- **It need not**: under an order-independent cost the best costs agree. -/
theorem bag_no_cheaper_under_flat_cost :
    bestCost (collapseWith (BagAlg Nat Unit)) emits flatCost inOrder =
      bestCost (collapseWith (Collect Nat Unit)) emits flatCost inOrder := by
  have bag : bestCost (collapseWith (BagAlg Nat Unit)) emits flatCost inOrder = 1 :=
    le_antisymm (bestCost_le _ emits flatCost (reference_admissible _ emits inOrder))
      (le_iInf₂ fun _ _ => le_rfl)
  have collect : bestCost (collapseWith (Collect Nat Unit)) emits flatCost inOrder = 1 :=
    le_antisymm (bestCost_le _ emits flatCost (reference_admissible _ emits inOrder))
      (le_iInf₂ fun _ _ => le_rfl)
  rw [bag, collect]

/-- **A weaker obligation admits implementations costlier than the reference**:
the slow reversed route is admissible for the bag, excluded by the ordered
collection, and costs more than the reference. -/
theorem weaker_admits_costlier :
    slowReversed ∈ admissible (collapseWith (BagAlg Nat Unit)) emits inOrder ∧
      slowReversed ∉ admissible (collapseWith (Collect Nat Unit)) emits inOrder ∧
      selectiveCost inOrder < selectiveCost slowReversed := by
  refine ⟨?_, slowReversed_not_collect, ?_⟩
  · rw [bag_admissible_eq]
    exact mem_univ _
  · decide

end Control

end Mettapedia.GSLT.Dynamics.CollapseObligation

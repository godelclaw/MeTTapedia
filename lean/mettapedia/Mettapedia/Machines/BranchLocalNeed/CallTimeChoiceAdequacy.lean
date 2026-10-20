import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceForward

/-!
# Adequacy of the reference Need machine for call-time choice

Completed source evaluations are realized by the unchanged reference machine
`NeedReference` on `machineSpec`, retaining related leaves and their worlds.
Consumer normalization is a separate construction: the existing `Observes`
and `machineAnswers` theorems specialize these direct evaluation laws.

* `observe_forward`: a specified observation is realized by a completed run of
  the machine from its initial configuration, leaf by leaf.
* `answers_forward`: from some fuel on, the machine's answer list is the
  specified outcome list, outcome by outcome, in order and with multiplicity;
  a value outcome is related to the specified value by a renaming of cells
  (`OutRel`), which is the identity on values without cells
  (`ValRel.cellFree_eq`).
* `observations_forward`: the same ordered leaves retain the emitted-event
  sequence of each specified branch, including repeated emissions and failures.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference NeedReturningRuns

theorem corr_initial : Corr [] Store.empty initialWorld where
  length := rfl
  nodup := List.nodup_nil
  events := rfl
  cells := by intro ℓ s hs; simp [Store.empty] at hs
  slot := by intro c rec h; simp [initialWorld, Heap.empty, Heap.lookup] at h

/-- A complete direct evaluation reaches actual returned machine leaves,
with their branch-local heaps, cache choices and effects still related. -/
theorem eval_forward {P : Program} {M : Comp} {L : List Result}
    (h : Derives P (.eval Store.empty [] M) L) :
    ∃ n leaves, Returns (machineSpec P) [] n [initialMachine M] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) L leaves :=
  (forward P _ _ h).1 [] [] (initialMachine M) corr_initial .nil rfl

/-- Complete source evidence supplies an actually closed frontier, not only
an answer projection which might have omitted unfinished work. The retained
leaves still carry their heap, cache and effect correspondence. -/
theorem eval_frontier_forward {P : Program} {M : Comp} {L : List Result}
    (source : Derives P (.eval Store.empty [] M) L) :
    ∃ threshold count leaves,
      Returns (machineSpec P) [] count [initialMachine M] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) L leaves ∧
      ∀ fuel, threshold ≤ fuel →
        runFrontier (machineSpec P) fuel [initialMachine M] = leaves.map haltOf := by
  obtain ⟨count, leaves, completed, related⟩ := eval_forward source
  obtain ⟨threshold, stable⟩ := frontier_eq_haltOf completed
  refine ⟨threshold, count, leaves, completed, related, ?_⟩
  intro fuel enough
  rw [NeedFrontierLaws.runFrontier_eq_flatMap]
  exact stable fuel enough

/-- **Forward adequacy for observations.** -/
theorem observe_forward {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ n leaves, Returns (machineSpec (observed P)) [] n [initialMachine (observe M)] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) L leaves :=
  eval_forward h

/-- The machine outcome of a returned leaf. -/
def leafOutcome (m : MMachine) : Option MOutcome :=
  match m.control with
  | .returned o [] => some o
  | _ => none

/-- A returned leaf retains its own effect trace, including failed outcomes. -/
def leafObservation (m : MMachine) : Option (MOutcome × List Nat) :=
  (leafOutcome m).map fun outcome => (outcome, m.world.receipts.effects)

/-- Returned leaves retain every source outcome, including failures. -/
theorem leafOutcomes_rel {φ : List CellId} {w : MWorld} {L : List Result}
    {leaves : List MMachine} (related : List.Forall₂ (ResRel φ w []) L leaves) :
    List.Forall₂ OutcomeRel L (leaves.filterMap leafOutcome) := by
  induction related with
  | nil => exact .nil
  | @cons result leaf rest leaves head tail ih =>
      obtain ⟨names, _, _, _, _, outcome, returned, paired⟩ := head
      have observed : leafOutcome leaf = some outcome := by simp [leafOutcome, returned]
      simp only [List.filterMap_cons, observed]
      exact .cons ⟨names, paired⟩ ih

/-- The existing leaf correspondence also preserves each branch's emitted
events; equal values alone do not establish this relation. -/
theorem leafObservations_rel {φ : List CellId} {w : MWorld} {L : List Result}
    {leaves : List MMachine} (h : List.Forall₂ (ResRel φ w []) L leaves) :
    List.Forall₂ ObservationRel L
      (leaves.filterMap leafObservation) := by
  induction h with
  | nil => exact .nil
  | @cons r l L' ls hr _ ih =>
      obtain ⟨φ', _, _, hc, _, o, ho, hor⟩ := hr
      have observed : leafObservation l = some (o, l.world.receipts.effects) := by
        simp [leafObservation, leafOutcome, ho]
      simp only [List.filterMap_cons, observed]
      exact .cons ⟨⟨φ', hor⟩, hc.events⟩ ih

theorem observations_of_frontier {P : Program} {m : MMachine} {n : Nat}
    {leaves : List MMachine} (h : Returns (machineSpec P) [] n [m] leaves)
    {fuel : Nat} (hfr : runFrontier (machineSpec P) fuel [m] = leaves.map haltOf) :
    (runFrontier (machineSpec P) fuel [m]).filterMap haltedObservation =
      leaves.filterMap leafObservation := by
  rw [hfr, List.filterMap_map]
  apply List.filterMap_congr
  intro l hl
  obtain ⟨o, ho⟩ := h.leaves_returned l hl
  simp [Function.comp_apply, haltedObservation, haltedOutcome,
    leafObservation, leafOutcome, ho, haltOf]

/-- Forward adequacy for ordered answer-and-effect observations. Every completed
branch retains its own event order and multiplicity. -/
theorem eval_observations_forward {P : Program} {M : Comp} {L : List Result}
    (h : Derives P (.eval Store.empty [] M) L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ ObservationRel L
        ((runFrontier (machineSpec P) fuel [initialMachine M]).filterMap haltedObservation) := by
  obtain ⟨n, leaves, hrun, hrel⟩ := eval_forward h
  obtain ⟨N, hN⟩ := frontier_eq_haltOf hrun
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hfr : runFrontier (machineSpec P) fuel [initialMachine M] =
      leaves.map haltOf := by
    rw [NeedFrontierLaws.runFrontier_eq_flatMap]
    exact hN fuel hfuel
  rw [observations_of_frontier hrun hfr]
  exact leafObservations_rel hrel

/-- Normalizing observation retains the same branch-local effect accounting. -/
theorem observations_forward {P : Program} {M : Comp} {L : List Result}
    (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ ObservationRel L (machineObservations P fuel M) :=
  eval_observations_forward h

theorem answers_of_frontier {P : Program} {m : MMachine} {n : Nat} {leaves : List MMachine}
    (h : Returns (machineSpec P) [] n [m] leaves) {fuel : Nat}
    (hfr : runFrontier (machineSpec P) fuel [m] = leaves.map haltOf) :
    answers (machineSpec P) fuel m = leaves.filterMap leafOutcome := by
  unfold answers
  rw [hfr, List.filterMap_map]
  apply List.filterMap_congr
  intro l hl
  obtain ⟨o, ho⟩ := h.leaves_returned l hl
  simp [Function.comp_apply, haltedOutcome_haltOf l o ho, leafOutcome, ho]

theorem answers_of_returns {P : Program} {m : MMachine} {n : Nat} {leaves : List MMachine}
    (h : Returns (machineSpec P) [] n [m] leaves) :
    ∃ N, ∀ fuel, N ≤ fuel →
      answers (machineSpec P) fuel m = leaves.filterMap leafOutcome := by
  obtain ⟨N, hN⟩ := frontier_eq_haltOf h
  refine ⟨N, fun fuel hfuel => answers_of_frontier h ?_⟩
  rw [NeedFrontierLaws.runFrontier_eq_flatMap]
  exact hN fuel hfuel

/-- **Adequacy for answers (forward).** From some fuel on, the reference
machine's answers for the observation of `M` are the specified outcomes, one by
one, in order and with multiplicity. -/
theorem eval_answers_forward {P : Program} {M : Comp} {L : List Result}
    (h : Derives P (.eval Store.empty [] M) L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
        (answers (machineSpec P) fuel (initialMachine M)) := by
  obtain ⟨n, leaves, hrun, hrel⟩ := eval_forward h
  obtain ⟨N, hN⟩ := answers_of_returns hrun
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [hN fuel hfuel]
  exact leafOutcomes_rel hrel

/-- Normalizing answer observation specializes direct evaluation adequacy. -/
theorem answers_forward {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
        (machineAnswers P fuel M) :=
  eval_answers_forward h

/-- The actual machine's multiplicity of a ground value agrees with that of
the source list. Other outcomes and cell-bearing values remain represented by
the original relation; no cell identities are erased to obtain this count. -/
theorem ground_value_count {L : List Result} {outcomes : List MOutcome}
    {names : List CellId} {ground : Val Nat} {expected : MVal}
    (related : List.Forall₂ OutcomeRel L outcomes)
    (groundRelated : ValRel names ground expected) (free : ground.cellFree = true) :
    (machineValues outcomes).count expected = (values L).count ground := by
  induction related with
  | nil => rfl
  | @cons result outcome rest outcomes head tail ih =>
      obtain ⟨map, paired⟩ := head
      rcases result with ⟨source, world⟩
      cases paired with
      | @ok value actual valueRelated =>
          change (actual :: machineValues outcomes).count expected =
            (value :: values rest).count ground
          have same := valueRelated.eq_cellFree_iff groundRelated free
          by_cases equal : value = ground
          · have target := same.mpr equal
            simp [equal, target, ih]
          · have target : actual ≠ expected := fun accepted => equal (same.mp accepted)
            simp [equal, target, ih]
      | failDomain => exact ih
      | failNoRule _ => exact ih
      | blackhole _ => exact ih

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

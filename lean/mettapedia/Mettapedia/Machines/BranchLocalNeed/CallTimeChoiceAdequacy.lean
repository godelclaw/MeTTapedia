import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceForward

/-!
# Adequacy of the reference Need machine for call-time choice

The observation of a closed computation in the specification (`Observes`) and
the answers of the unchanged reference machine `NeedReference.answers` on the
instance `machineSpec` (`machineAnswers`) agree.

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

/-- **Forward adequacy for observations.** -/
theorem observe_forward {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ n leaves, Returns (machineSpec (observed P)) [] n [initialMachine (observe M)] leaves ∧
      List.Forall₂ (ResRel [] initialWorld []) L leaves :=
  (forward (observed P) _ _ h).1 [] [] (initialMachine (observe M)) corr_initial .nil rfl

/-- The machine outcome of a returned leaf. -/
def leafOutcome (m : MMachine) : Option MOutcome :=
  match m.control with
  | .returned o [] => some o
  | _ => none

/-- A returned leaf retains its own effect trace, including failed outcomes. -/
def leafObservation (m : MMachine) : Option (MOutcome × List Nat) :=
  (leafOutcome m).map fun outcome => (outcome, m.world.receipts.effects)

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
theorem observations_forward {P : Program} {M : Comp} {L : List Result}
    (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ ObservationRel L
        (machineObservations P fuel M) := by
  obtain ⟨n, leaves, hrun, hrel⟩ := observe_forward h
  obtain ⟨N, hN⟩ := frontier_eq_haltOf hrun
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hfr : runFrontier (machineSpec (observed P)) fuel [initialMachine (observe M)] =
      leaves.map haltOf := by
    rw [NeedFrontierLaws.runFrontier_eq_flatMap]
    exact hN fuel hfuel
  unfold machineObservations
  rw [observations_of_frontier hrun hfr]
  exact leafObservations_rel hrel

theorem answers_of_returns {P : Program} {m : MMachine} {n : Nat} {leaves : List MMachine}
    (h : Returns (machineSpec P) [] n [m] leaves) :
    ∃ N, ∀ fuel, N ≤ fuel →
      answers (machineSpec P) fuel m = leaves.filterMap leafOutcome := by
  obtain ⟨N, hN⟩ := frontier_eq_haltOf h
  refine ⟨N, fun fuel hfuel => ?_⟩
  have hfr : runFrontier (machineSpec P) fuel [m] = leaves.map haltOf := by
    rw [NeedFrontierLaws.runFrontier_eq_flatMap]
    exact hN fuel hfuel
  unfold answers
  rw [hfr, List.filterMap_map]
  apply List.filterMap_congr
  intro l hl
  obtain ⟨o, ho⟩ := h.leaves_returned l hl
  simp [Function.comp_apply, haltedOutcome_haltOf l o ho, leafOutcome, ho]

/-- **Adequacy for answers (forward).** From some fuel on, the reference
machine's answers for the observation of `M` are the specified outcomes, one by
one, in order and with multiplicity. -/
theorem answers_forward {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ (fun (r : Result) (o : MOutcome) => ∃ φ, OutRel φ r.1 o) L
        (machineAnswers P fuel M) := by
  obtain ⟨n, leaves, hrun, hrel⟩ := observe_forward h
  obtain ⟨N, hN⟩ := answers_of_returns hrun
  refine ⟨N, fun fuel hfuel => ?_⟩
  unfold machineAnswers
  rw [hN fuel hfuel]
  clear hN hrun h
  induction hrel with
  | nil => exact .nil
  | @cons r l L' ls hr _ ih =>
      obtain ⟨φ', _, _, _, _, o, ho, hor⟩ := hr
      have : leafOutcome l = some o := by simp [leafOutcome, ho]
      simp only [List.filterMap_cons, this]
      exact .cons ⟨φ', hor⟩ ih

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

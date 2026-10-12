import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceOrdered
import Mettapedia.GSLT.Distinction.OrderedSimulationSpans

/-!
# Several queries on scheduled frontiers

The scheduled-frontier layer gives each slot its own boundary clock, the case of
a target that spends a varying number of transitions per answer. With one slot
per query and the clock that adequacy provides, every schedule that serves each
slot its clock presents the specified outcomes of all queries in slot order, with
multiplicity, whatever the order in which the slots completed
(`scheduled_answers`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference
open Mettapedia.GSLT.Distinction
open Mettapedia.Machines.Cursor

/-- **Several queries under any sufficient schedule.** There are boundary clocks
such that every schedule serving each query its clock presents, in slot order,
the specified outcomes of all queries. -/
theorem scheduled_answers {n : Nat} (P : Program) (Ms : Fin n → Comp)
    (Ls : Fin n → List Result) (hL : ∀ id, Observes P (Ms id) (Ls id)) :
    ∃ clocks : Fin n → Nat, ∀ schedule : List (ScheduledFrontier.Command n),
      (∀ id, clocks id ≤ Scheduling.allocation id schedule) →
      List.Forall₂ OutcomeRel (List.ofFn Ls).flatten
        ((ScheduledFrontier.view (ScheduledFrontier.execute (orderedMachine P) schedule
          (ScheduledFrontier.reserve clocks fun id => [initialMachine (observe (Ms id))]))).filterMap
          haltedOutcome) := by
  have hN := fun id => ordered_answers (hL id)
  choose clocks hclocks using hN
  refine ⟨clocks, fun schedule enough => ?_⟩
  rw [ScheduledFrontier.view_enough _ schedule clocks _ enough, List.filterMap_flatten,
    List.map_ofFn]
  exact List.rel_flatten (ScheduledFrontier.ofFn_related _ _
    (fun id => hclocks id (clocks id) le_rfl))

/-- Serving each independent query its boundary clock preserves ordered
answer-and-effect observations, regardless of the order of slot completion.
This is a scheduling law; it does not grant shared mutable-heap authority. -/
theorem scheduled_observations {n : Nat} (P : Program) (Ms : Fin n → Comp)
    (Ls : Fin n → List Result) (hL : ∀ id, Observes P (Ms id) (Ls id)) :
    ∃ clocks : Fin n → Nat, ∀ schedule : List (ScheduledFrontier.Command n),
      (∀ id, clocks id ≤ Scheduling.allocation id schedule) →
      List.Forall₂ ObservationRel (List.ofFn Ls).flatten
        ((ScheduledFrontier.view (ScheduledFrontier.execute (orderedMachine P) schedule
          (ScheduledFrontier.reserve clocks fun id => [initialMachine (observe (Ms id))]))).filterMap
          haltedObservation) := by
  have hN := fun id => ordered_observations (hL id)
  choose clocks hclocks using hN
  refine ⟨clocks, fun schedule enough => ?_⟩
  rw [ScheduledFrontier.view_enough _ schedule clocks _ enough, List.filterMap_flatten,
    List.map_ofFn]
  exact List.rel_flatten (ScheduledFrontier.ofFn_related _ _
    (fun id => hclocks id (clocks id) le_rfl))

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

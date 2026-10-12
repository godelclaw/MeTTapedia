import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceBackward
import Mettapedia.Machines.BranchLocalNeed.RepresentationRelation

/-!
# Adequacy on the ordered-system layer

The reference machine is an ordered system (`NeedRepresentation.needSystem`),
whose frontier runner is the machine's own. Adequacy therefore reads directly on
that layer (`ordered_answers`).

A lockstep ordered simulation between the specification and the machine does not
exist: the specification has no transition relation, and the machine spends a
varying number of transitions per alternative (`Controls.machine_partial`). The
relation is stated at halted frontiers instead, which is the boundary at which
answers are compared.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

open NeedReference
open Mettapedia.GSLT.Distinction

/-- The reference machine of an observed program as an ordered system. -/
abbrev orderedMachine (P : Program) : OrderedSystem MMachine :=
  NeedRepresentation.needSystem (machineSpec (observed P))

/-- **Adequacy on the ordered system.** From some fuel on, the halted frontier of
the observation of `M` presents the specified outcomes, one by one. -/
theorem ordered_answers {P : Program} {M : Comp} {L : List Result} (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ OutcomeRel L
        (((orderedMachine P).runFrontier fuel [initialMachine (observe M)]).filterMap
          haltedOutcome) := by
  obtain ⟨N, hN⟩ := (adequacy P M).1 L h
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [NeedRepresentation.needSystem_runFrontier]
  exact (hN fuel hfuel).2

/-- Ordered-system adequacy also retains the event sequence of every answer. -/
theorem ordered_observations {P : Program} {M : Comp} {L : List Result}
    (h : Observes P M L) :
    ∃ N, ∀ fuel, N ≤ fuel →
      List.Forall₂ ObservationRel L
        (((orderedMachine P).runFrontier fuel [initialMachine (observe M)]).filterMap
          haltedObservation) := by
  obtain ⟨N, hN⟩ := observations_forward h
  refine ⟨N, fun fuel hfuel => ?_⟩
  rw [NeedRepresentation.needSystem_runFrontier]
  exact hN fuel hfuel

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

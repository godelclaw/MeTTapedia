import Mettapedia.OSLF.MeTTaIL.Complete.Deep
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledFootprint

/-!
# A deepening search stays within a footprint

When a family's goal at every depth mentions only names of a footprint, and the payload read from
a result within the footprint is within it, every level a deepening search runs stays within the
footprint and so does every payload it publishes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Deep

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise
open StructuralDescent
open StructuralDescent.Scheduled (Goal Result Obligation)

variable (family : Family) (footprint : List String) (within : family.Payload → Prop)

/-- The level and the published payloads are within the footprint. -/
structure Covered (state : State family) : Prop where
  level : Scheduled.stateFreeWithin footprint family.environment (family.goal state.depth) state.level
  published : ∀ payload ∈ state.published, within payload

/-- What a family needs for its searches to stay within a footprint. -/
structure Footprinted : Prop where
  goals : ∀ depth, Scheduled.goalFreeWithin footprint (family.goal depth)
  reads : ∀ {depth : Nat} (result : Result family.environment (family.goal depth)),
    Scheduled.resultFreeWithin footprint result → within (family.read result)
  provider : ∀ row ∈ family.environment.provider.rows, RuleBinding.patternsFreeWithin footprint row.values
  dynamic : Query.DynamicOutputsFreeWithin footprint family.environment

variable {family footprint within}

theorem publication_covered {state : State family} (fits : Footprinted family footprint within)
    (covered : Covered family footprint within state) : ∀ payload ∈ state.publication, within payload := by
  intro payload member
  rcases List.mem_append.mp member with published | fresh
  · exact covered.published payload published
  · obtain ⟨found, _⟩ := (mem_fresh family).mp fresh
    obtain ⟨result, answered, rfl⟩ := List.mem_map.mp found
    exact fits.reads result (covered.level.2 result answered)

theorem levelStart_covered (fits : Footprinted family footprint within) (depth : Nat)
    {published : List family.Payload} (inside : ∀ payload ∈ published, within payload) :
    Covered family footprint within (levelStart family depth published) where
  level := Scheduled.start_free_within footprint family.environment (family.goal depth) (fits.goals depth)
  published := inside

theorem start_covered (fits : Footprinted family footprint within) :
    Covered family footprint within (start family) :=
  levelStart_covered fits 0 (by simp)

theorem tick_covered (fits : Footprinted family footprint within) {state : State family}
    (covered : Covered family footprint within state) : Covered family footprint within (tick family state) := by
  unfold tick
  split
  · exact levelStart_covered fits (state.depth + 1) (publication_covered fits covered)
  · exact ⟨Scheduled.tick_free_within footprint family.environment (family.goal state.depth) fits.provider
      fits.dynamic state.level covered.level, covered.published⟩

theorem run_covered (fits : Footprinted family footprint within) :
    ∀ (work : Nat) {state : State family}, Covered family footprint within state →
      Covered family footprint within (run family work state)
  | 0, _, covered => covered
  | work + 1, _, covered => run_covered fits work (tick_covered fits covered)

end Mettapedia.OSLF.MeTTaIL.Complete.Deep

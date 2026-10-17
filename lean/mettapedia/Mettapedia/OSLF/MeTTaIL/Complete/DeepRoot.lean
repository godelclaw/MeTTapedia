import Mettapedia.OSLF.MeTTaIL.Complete.Deep
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseEventEquality

/-!
# One rule at one focus, by iterative deepening

The deepening search of `Complete.Deep` for the root goal of one rule at one source. Its payloads
are firings: matcher trace, both assignments, premise history and target. Recursive premises may
use any rule.

A drained level is certified when no branch was cut by depth, or when the environment passes the
structural admission check and the depth reaches the source's size, which bounds every
derivation (`firing_depth_bound`).

- `sound`: every published firing is a firing of the rule at the source;
- `complete_in_limit`: every firing is published after finitely much work, for every environment;
- `exact_of_complete`: a certified, drained search has published every firing;
- `eventually_complete`: for admitted environments the search is certified after finitely much work.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise PatternTreeSize
open StructuralDescent (checkEnvironment eventsDepth)
open StructuralDescent.Scheduled (Goal Result)

/-- One rule, by its declaration index, at one source of one environment. -/
structure Request where
  environment : Environment
  bound : List TypeExpr
  type : TypeExpr
  source : Pattern
  index : Nat

/-- The rule's root goal at a depth. -/
abbrev Request.goal (request : Request) (depth : Nat) : Goal :=
  .root depth request.bound request.type request.source request.index

/-- What a firing records: matcher trace, both assignments, premise history and target. -/
structure Firing where
  trace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  history : List Event
  target : Pattern
  deriving DecidableEq

/-- The firing is a firing of the rule at the source. -/
def Firing.Valid (request : Request) (firing : Firing) : Prop :=
  RootFiring request.environment request.bound request.type request.source request.index
    firing.trace firing.captured firing.completed firing.history firing.target

/-- The depth a firing's derivation needs. -/
def Firing.requiredDepth (firing : Firing) : Nat := 1 + eventsDepth firing.history

/-- The record of a root result. -/
def read {request : Request} {depth : Nat} : Result request.environment (request.goal depth) → Firing
  | .root trace captured completed events target _ => ⟨trace, captured, completed, events, target⟩

theorem read_valid {request : Request} {depth : Nat} (result : Result request.environment (request.goal depth)) :
    (read result).Valid request := by
  cases result with
  | root trace captured completed events target valid => exact valid

/-- The firings of the rule at the source as a deepening family. -/
abbrev family (request : Request) : Deep.Family where
  environment := request.environment
  goal := request.goal
  Payload := Firing
  read := read
  Valid := Firing.Valid request
  read_valid := read_valid
  build firing valid _ := .root firing.trace firing.captured firing.completed firing.history firing.target valid
  read_build _ _ _ := rfl
  required := Firing.requiredDepth
  build_ordered firing _ depth enough := by
    change decide (1 + eventsDepth firing.history ≤ depth) = true
    exact decide_eq_true enough
  bound := if checkEnvironment request.environment then some (nodes request.source) else none
  bound_sound limit bounded firing valid := by
    split at bounded
    · rename_i admitted
      cases bounded
      exact StructuralDescent.firing_depth_bound request.environment admitted request.source
        request.bound request.type ⟨request.index, firing.trace, firing.captured, firing.completed, firing.history,
          firing.target, valid⟩
    · cases bounded

abbrev State (request : Request) := Deep.State (family request)
abbrev start (request : Request) : State request := Deep.start (family request)
abbrev tick (request : Request) (state : State request) : State request := Deep.tick (family request) state
abbrev run (request : Request) (work : Nat) (state : State request) : State request :=
  Deep.run (family request) work state

theorem run_succ (request : Request) (work : Nat) (state : State request) :
    run request (work + 1) state = tick request (run request work state) :=
  Deep.run_succ (family request) work state

theorem tick_publication_prefix (request : Request) (state : State request) :
    state.publication <+: (tick request state).publication :=
  Deep.tick_publication_prefix (family request) state

/-- **Sound.** -/
theorem sound (request : Request) (work : Nat) :
    ∀ firing ∈ (run request work (start request)).publication, firing.Valid request :=
  Deep.sound (family request) work

/-- **Complete in the limit**, for every environment. -/
theorem complete_in_limit {request : Request} {firing : Firing} (valid : firing.Valid request) :
    ∃ work, firing ∈ (run request work (start request)).publication :=
  Deep.complete_in_limit (family request) (payload := firing) valid

/-- **A complete search is exact.** -/
theorem exact_of_complete (request : Request) (work : Nat)
    (done : (run request work (start request)).complete = true) {firing : Firing} (valid : firing.Valid request) :
    firing ∈ (run request work (start request)).publication :=
  Deep.exact_of_complete (family request) work done (payload := firing) valid

theorem complete_mono (request : Request) {work : Nat}
    (done : (run request work (start request)).complete = true) {later : Nat} (after : work ≤ later) :
    (run request later (start request)).complete = true :=
  Deep.complete_mono (family request) done after

/-- **Admitted searches finish.** -/
theorem eventually_complete (request : Request) (admitted : checkEnvironment request.environment = true) :
    ∃ work, (run request work (start request)).complete = true :=
  Deep.eventually_complete (family request) (limit := nodes request.source) (by simp [admitted])

end Mettapedia.OSLF.MeTTaIL.Complete.DeepRoot

import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Isolation
import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-!
# The two modes are the two handlers of one free computation

`GSLT.Dynamics.ContextualEffectHandlers` has one free computation with choice and
state and two handlers of it: `runWorlds` gives every alternative its parent
state and keeps each private result, and `runShared` runs the alternatives in
their authored order against one shared state.  Its controls separate the two
and show that under the shared handler the order of the alternatives is
observable.

A region of this development is such a computation (`Region.toProgram`): a leaf
reads the state and answers, a step reads the state and writes the state its
rule instance fires to, and a step that does not fire answers with nothing and
leaves the state alone.  Read so,

* `Region.runShared_toProgram`: the committed run is the shared handler: the
  same answers in the same order, the same state;
* `Region.runWorlds_toProgram`: the branch-local run is the isolated handler:
  the same answers in the same order, each with the private state that
  publishing its proposal on the snapshot gives
  (`Region.runWorlds_toProgram_answers` for the answers alone).

What a region adds to the free computation is the footprint of each write: a
step is an instance of a local rule.  The laws of `Regions.Isolation`,
`Regions.Validation` and `Regions.Waves` are about that.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Dynamics

universe u v w x

variable {Location : Type u} {Value : Type v} {Answer : Type w} {Intent : Type x}
  [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **A region as a free computation with choice and state.**  The answer of an
alternative that failed is `none`. -/
def Region.toProgram : Region Location Value Answer →
    ContextualEffectHandlers.Program (Location → Value) (Option Answer) Intent
  | .fail => .pure none
  | .answer readout => .read fun state => .pure (some (readout.value state))
  | .step first rest => .read fun state =>
      match first.fire state with
      | none => .pure none
      | some next => .write next rest.toProgram
  | .orElse left right => .choose left.toProgram right.toProgram

/-- **The committed run is the shared handler**: the answers of the alternatives
that answered, in order, and the state. -/
theorem Region.runShared_toProgram (region : Region Location Value Answer)
    (world : Location → Value) :
    (ContextualEffectHandlers.runShared (region.toProgram (Intent := Intent))
        world).answers.filterMap id = (region.committed world).1 ∧
      (ContextualEffectHandlers.runShared (region.toProgram (Intent := Intent)) world).state =
        (region.committed world).2 := by
  induction region generalizing world with
  | fail => exact ⟨rfl, rfl⟩
  | answer readout => exact ⟨rfl, rfl⟩
  | step first rest ih =>
      cases fired : first.fire world with
      | none =>
          have shared : ContextualEffectHandlers.runShared
              ((Region.step first rest).toProgram (Intent := Intent)) world =
              ContextualEffectHandlers.runShared (.pure none) world := by
            simp only [Region.toProgram, ContextualEffectHandlers.runShared, fired]
          have committed : (Region.step first rest).committed world = ([], world) := by
            simp only [Region.committed, fired]
          rw [shared, committed]
          exact ⟨rfl, rfl⟩
      | some next =>
          have shared : ContextualEffectHandlers.runShared
              ((Region.step first rest).toProgram (Intent := Intent)) world =
              ContextualEffectHandlers.runShared (rest.toProgram (Intent := Intent)) next := by
            simp only [Region.toProgram, ContextualEffectHandlers.runShared, fired]
          have committed : (Region.step first rest).committed world = rest.committed next := by
            simp only [Region.committed, fired]
          rw [shared, committed]
          exact ih next
  | orElse left right ihLeft ihRight =>
      obtain ⟨leftAnswers, leftState⟩ := ihLeft world
      simp only [Region.toProgram, ContextualEffectHandlers.runShared, Region.committed,
        List.filterMap_append, leftAnswers, leftState]
      obtain ⟨rightAnswers, rightState⟩ := ihRight (left.committed world).2
      rw [rightAnswers, rightState]
      exact ⟨rfl, rfl⟩

/-- The isolated handler from any branch trace: each alternative that answered,
with its private state, is an outcome with the state that publishing its
proposal on the snapshot gives. -/
theorem Region.runWorldsAt_toProgram (region : Region Location Value Answer)
    (view : Location → Value) (branch : ContextualEffectHandlers.BranchTrace) :
    (ContextualEffectHandlers.runWorldsAt (region.toProgram (Intent := Intent)) view
        branch).filterMap (fun world => world.answer.map fun answer => (answer, world.state)) =
      (region.branchLocal view).filterMap fun outcome =>
        (publish outcome.2.steps view).map fun final => (outcome.1, final) := by
  induction region generalizing view branch with
  | fail => rfl
  | answer readout => rfl
  | step first rest ih =>
      cases fired : first.fire view with
      | none =>
          simp only [Region.toProgram, ContextualEffectHandlers.runWorldsAt, Region.branchLocal,
            fired]
          rfl
      | some next =>
          simp only [Region.toProgram, ContextualEffectHandlers.runWorldsAt, Region.branchLocal,
            fired, List.filterMap_map]
          rw [ih next branch]
          apply List.filterMap_congr
          intro outcome _
          simp [Proposal.cons, fired]
  | orElse left right ihLeft ihRight =>
      simp only [Region.toProgram, ContextualEffectHandlers.runWorldsAt, Region.branchLocal,
        List.filterMap_append, ihLeft, ihRight]

/-- **The branch-local run is the isolated handler**: the answers of the
alternatives that answered, in order, each with the private state that
publishing its proposal on the snapshot gives. -/
theorem Region.runWorlds_toProgram (region : Region Location Value Answer)
    (view : Location → Value) :
    (ContextualEffectHandlers.runWorlds (region.toProgram (Intent := Intent)) view).filterMap
        (fun world => world.answer.map fun answer => (answer, world.state)) =
      (region.branchLocal view).filterMap fun outcome =>
        (publish outcome.2.steps view).map fun final => (outcome.1, final) :=
  region.runWorldsAt_toProgram view []

/-- The same for the answers alone. -/
theorem Region.runWorlds_toProgram_answers (region : Region Location Value Answer)
    (view : Location → Value) :
    (ContextualEffectHandlers.runWorlds (region.toProgram (Intent := Intent)) view).filterMap
        (fun world => world.answer) = (region.branchLocal view).map Prod.fst := by
  have pairs := congrArg (List.map Prod.fst) (region.runWorlds_toProgram (Intent := Intent) view)
  rw [List.map_filterMap, List.map_filterMap] at pairs
  have left : (fun world : ContextualEffectHandlers.WorldResult (Location → Value) (Option Answer)
      Intent => (world.answer.map fun answer => (answer, world.state)).map Prod.fst) =
      fun world => world.answer := by
    funext world
    cases world.answer <;> rfl
  rw [left] at pairs
  rw [pairs, ← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro outcome member
  obtain ⟨final, published, -⟩ := Region.committed_of_mem_branchLocal member
  rw [published]
  rfl

/-! ## Controls -/

namespace Handlers

open SharedSpace

/-- **Positive**: under the shared handler the two siblings that add an atom to
one space and read it give the answers of the committed run. -/
theorem shared_handler_of_siblings :
    (ContextualEffectHandlers.runShared
        ((Region.alternatives [sibling .a, sibling .b]).toProgram (Intent := Unit))
        empty).answers.filterMap id = [{.a}, {.a, .b}] := by
  rw [(Region.runShared_toProgram _ _).1]
  exact committed_answers.1

/-- Under the isolated handler they give the answers of the branch-local run. -/
theorem isolated_handler_of_siblings :
    (ContextualEffectHandlers.runWorlds
        ((Region.alternatives [sibling .a, sibling .b]).toProgram (Intent := Unit))
        empty).filterMap (fun world => world.answer) = [{.a}, {.b}] := by
  rw [Region.runWorlds_toProgram_answers]
  exact branchLocal_answers.1

/-- **Negative**: the two handlers disagree on these siblings. -/
theorem handlers_disagree_on_siblings :
    (ContextualEffectHandlers.runWorlds
        ((Region.alternatives [sibling .a, sibling .b]).toProgram (Intent := Unit))
        empty).filterMap (fun world => world.answer) ≠
      (ContextualEffectHandlers.runShared
        ((Region.alternatives [sibling .a, sibling .b]).toProgram (Intent := Unit))
        empty).answers.filterMap id := by
  rw [isolated_handler_of_siblings, shared_handler_of_siblings]
  decide

end Handlers

#print axioms Region.runShared_toProgram
#print axioms Region.runWorlds_toProgram
#print axioms Region.runWorlds_toProgram_answers
#print axioms Handlers.shared_handler_of_siblings
#print axioms Handlers.isolated_handler_of_siblings
#print axioms Handlers.handlers_disagree_on_siblings

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

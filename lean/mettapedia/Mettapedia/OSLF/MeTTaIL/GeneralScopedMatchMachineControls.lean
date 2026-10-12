import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCertified

/-!
# Structural suspension and occurrence controls

The duplicate bag example suspends before its first tree match and retains
two actual residual choices with identical final assignments. Ordered vectors
and unequal binder arities provide rejection controls.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralScopedMatchMachine

private def schema : Pattern := .collection .hashBag [.bvar 0, .bvar 0] none

private def rule : RewriteRule where
  name := "BagChoiceControl"
  typeContext := []
  premises := []
  left := schema
  right := schema

private def request : Request where
  rule := rule
  spec := { dependencies := [] }
  ambient := 1
  site := .left
  path := []
  depth := 0
  initial := []
  schema := schema
  target := schema

private def first : Answer :=
  { assignment := [], trace := [{ path := [0], selected := 0 }, { path := [1], selected := 0 }] }
private def second : Answer :=
  { assignment := [], trace := [{ path := [0], selected := 1 }, { path := [1], selected := 0 }] }

/-- Three ticks expose a pending first tree and a separate next-choice cursor.
No complete tree match or collection search has been evaluated at this pause. -/
theorem suspension_inside_bag_choices :
    (run request 3 (start request)).answers = [] ∧
    complete (run request 3 (start request)) = false ∧
    (run request 3 (start request)).agenda = [
      { assignment := [], tasks := [
          .tree [0] 0 (.bvar 0) (.bvar 0),
          .bag [] 0 1 [.bvar 0] none .hashBag [.bvar 0]],
        trace := [{ path := [0], selected := 0 }] },
      { assignment := [], tasks := [.bagSelect [] 0 0 (.bvar 0) [.bvar 0] none .hashBag [.bvar 0, .bvar 0] 1] }] := by
  exact ⟨rfl, rfl, rfl⟩

theorem duplicate_origins_emitted :
    complete (run request 40 (start request)) = true ∧
    (run request 40 (start request)).answers = [first, second] ∧
    first.assignment = second.assignment ∧ first.trace ≠ second.trace := by
  exact ⟨rfl, rfl, rfl, by decide⟩

theorem actual_duplicate_derivations : first.Valid request ∧ second.Valid request := by
  have reached := reachable_run (request := request) 40 Reachable.start
  have outputs := duplicate_origins_emitted.2.1
  constructor
  · exact answers_sound reached (by rw [outputs]; exact List.mem_cons_self)
  · exact answers_sound reached (by rw [outputs]; exact List.mem_cons_of_mem _ List.mem_cons_self)

private def vectorMismatch : Request :=
  { request with
    ambient := 2
    schema := .collection .vec [.bvar 0, .bvar 1] none
    target := .collection .vec [.bvar 1, .bvar 0] none }

private def arityMismatch : Request :=
  { request with schema := .multiLambda 2 [] (.bvar 0), target := .multiLambda 1 [] (.bvar 0) }

theorem ordered_and_arity_rejections :
    complete (run vectorMismatch 10 (start vectorMismatch)) = true ∧
    (run vectorMismatch 10 (start vectorMismatch)).answers = [] ∧
    complete (run arityMismatch 10 (start arityMismatch)) = true ∧
    (run arityMismatch 10 (start arityMismatch)).answers = [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms suspension_inside_bag_choices
#print axioms duplicate_origins_emitted
#print axioms actual_duplicate_derivations
#print axioms ordered_and_arity_rejections

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineControls

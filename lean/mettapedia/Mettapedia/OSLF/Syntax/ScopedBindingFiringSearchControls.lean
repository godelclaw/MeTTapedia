import Mettapedia.OSLF.Syntax.ScopedBindingFiringSearchReceipts
import Mettapedia.OSLF.Syntax.ScopedBindingFactorSubstitution

/-!
# Complete scoped search and additional-match controls

Two equal binder-body children retain distinct selected positions and
complete targets. Duplicate authored origins remain separate list entries.
Literal scopes and actual minimality exclude false candidates. A genuine
noninjective substitution creates a new fixed-label match; old-factor
preservation consequently does not provide behavioral reflection.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding.FiringSearchControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath

inductive Operation where
  | number (value : Nat)
  | pair
  | binder
  deriving DecidableEq

abbrev language : Binding.Signature where
  Srt := Unit
  Op := fun _ => Operation
  arity := fun operator => match operator with
    | .number _ => []
    | .pair => [([], ()), ([], ())]
    | .binder => [([()], ())]

local instance firingSearchControlQuiver : Quiver (Scope language) := bindingFrameQuiver language

def number {context : Binding.Ctx language} (value : Nat) : Binding.Term language context () :=
  .op (.number value) .nil

def pair {context : Binding.Ctx language} (first second : Binding.Term language context ()) :
    Binding.Term language context () := .op .pair (.cons first (.cons second .nil))

def abstraction {context : Binding.Ctx language}
    (body : Binding.Term language (() :: context) ()) : Binding.Term language context () :=
  .op .binder (.cons body .nil)

def leftFrame (context : Binding.Ctx language) (sibling : Binding.Term language context ()) :
    BindingFrame language (context, ()) (context, ()) :=
  .slot context () .pair 0 (Fin.cases (fun absent => False.elim (absent rfl))
    (fun previous _ => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact sibling))

def rightFrame (context : Binding.Ctx language) (sibling : Binding.Term language context ()) :
    BindingFrame language (context, ()) (context, ()) :=
  .slot context () .pair 1 (Fin.cases (fun _ => sibling)
    (fun previous absent => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact False.elim (absent rfl)))

def binderFrame : BindingFrame language ([()], ()) ([], ()) :=
  .slot (S := language) [] () Operation.binder 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def leftReaction : BindingContext language ([()], ()) ([], ()) :=
  ((.nil : BindingContext language ([()], ()) ([()], ())).cons (leftFrame [()] (number 7))).cons binderFrame

def agent : Binding.Term language [] () := abstraction (pair (number 7) (number 7))
def leftResult : Binding.Term language [] () := abstraction (pair (.var .zero) (number 7))
def rightResult : Binding.Term language [] () := abstraction (pair (number 7) (.var .zero))
def identityLabel : BindingContext language ([], ()) ([], ()) := .nil

def declaration (origin : Nat) : FramePermission.Declaration (bindingAction language) Nat where
  origin := origin
  scope := ([()], ())
  redex := number 7
  reactum := .var .zero

def declarations := [declaration 3, declaration 9]
def results := bindingFiringSearch agent identityLabel declarations

theorem every_literal_position_is_counted : (bindingFactors agent).length = 4 := rfl
theorem every_rule_position_is_tested :
    (bindingFiringCandidates agent identityLabel declarations).length = 8 := rfl
theorem both_child_positions_and_both_origins_are_retained : results.length = 4 := by decide
theorem original_list_occurrences_are_retained :
    results.map (fun candidate => candidate.position.val) = [0, 0, 1, 1] := by decide
theorem authored_origins_are_retained :
    results.map (fun candidate => candidate.declaration.origin) = [3, 3, 9, 9] := by decide

theorem equal_declarations_still_retain_different_list_occurrences :
    (bindingFiringSearch agent identityLabel [declaration 3, declaration 3]).map
      (fun candidate => candidate.position.val) = [0, 0, 1, 1] := by decide

theorem complete_receipts_count_every_success :
    (bindingFiringSearchReceipts agent identityLabel declarations).length = 4 := by
  exact (bindingFiringSearchReceipts_length (S := language) (source := ([], ()))
    agent identityLabel declarations).trans both_child_positions_and_both_origins_are_retained

def first : BindingFiringCandidate language Nat ([], ()) declarations :=
  results.get ⟨0, by decide⟩
def second : BindingFiringCandidate language Nat ([], ()) declarations :=
  results.get ⟨1, by decide⟩
def third : BindingFiringCandidate language Nat ([], ()) declarations :=
  results.get ⟨2, by decide⟩

theorem first_member : first ∈ bindingFiringSearch agent identityLabel declarations :=
  List.get_mem results _
theorem second_member : second ∈ bindingFiringSearch agent identityLabel declarations :=
  List.get_mem results _
theorem third_member : third ∈ bindingFiringSearch agent identityLabel declarations :=
  List.get_mem results _

def firstFiring := bindingFiringSearchSelected agent identityLabel first first_member
def secondFiring := bindingFiringSearchSelected agent identityLabel second second_member
def thirdFiring := bindingFiringSearchSelected agent identityLabel third third_member

theorem complete_first_target : first.result identityLabel
    ((mem_bindingFiringSearch agent identityLabel first).mp first_member).2 = leftResult := rfl
theorem complete_second_target : second.result identityLabel
    ((mem_bindingFiringSearch agent identityLabel second).mp second_member).2 = rightResult := rfl
theorem complete_third_target : third.result identityLabel
    ((mem_bindingFiringSearch agent identityLabel third).mp third_member).2 = leftResult := rfl
theorem entire_binder_and_selected_pair_path :
    (rawFiringReactionPath firstFiring).length = 2 := rfl
theorem protected_bound_reactum : firstFiring.declaration.reactum =
    (Binding.Term.var .zero : Binding.Term language [()] ()) := rfl
theorem distinct_positions_have_distinct_whole_targets : leftResult ≠ rightResult := by
  intro same
  cases same
theorem distinct_origins_have_distinct_complete_firings : firstFiring ≠ thirdFiring := by
  intro same
  have impossible : (3 : Nat) = 9 := congrArg (fun firing => firing.declaration.origin) same
  cases impossible

def independentLeftFiring : FramePermission.RawFiring
    (admitted := fun selected => selected ∈ declarations)
    (source := ([], ())) (target := ([], ()))
    agent (bindingContextArrow identityLabel) leftResult where
  declaration := declaration 3
  admitted := List.mem_cons_self
  reaction := bindingContextArrow leftReaction
  square := rfl
  minimal := by
    change Mettapedia.GSLT.RelativePushout.IsIdemPushout
      (bindingTermArrow (S := language) (scope := ([], ())) agent)
      (bindingTermArrow (S := language) (scope := ([()], ())) (declaration 3).redex)
      (bindingContextArrow identityLabel) (bindingContextArrow leftReaction) rfl
    exact binding_ipo_of_no_shared_outer_slot (S := language)
      (first := ([], ())) (second := ([()], ())) (target := ([], ()))
      agent (declaration 3).redex identityLabel leftReaction rfl
      (by rintro ⟨_, impossible, _⟩; cases impossible)
  target_readout := rfl

theorem independently_defined_firing_is_recovered_completely :
    ∃ candidate : BindingFiringCandidate language Nat ([], ()) declarations,
      ∃ member : candidate ∈ bindingFiringSearch agent identityLabel declarations,
        candidate.declaration = independentLeftFiring.declaration ∧
        HEq (candidate.reaction identityLabel
          ((mem_bindingFiringSearch (source := ([], ())) agent identityLabel candidate).mp member).2)
          (rawFiringReactionPath independentLeftFiring) ∧
        candidate.result identityLabel
          ((mem_bindingFiringSearch (source := ([], ())) agent identityLabel candidate).mp member).2 = leftResult :=
  bindingFiringSearch_complete agent identityLabel leftResult independentLeftFiring

theorem independently_defined_firing_has_a_complete_receipt :
    ∃ receipt : BindingFiringSearchReceipt (S := language) (source := ([], ()))
        agent identityLabel declarations,
      receipt ∈ bindingFiringSearchReceipts agent identityLabel declarations ∧
      receipt.firing.declaration = independentLeftFiring.declaration ∧
      HEq (rawFiringReactionPath receipt.firing) (rawFiringReactionPath independentLeftFiring) ∧
      receipt.result = leftResult :=
  bindingFiringSearchReceipts_complete (S := language) (source := ([], ()))
    agent identityLabel leftResult independentLeftFiring

def wrongScopeDeclaration : FramePermission.Declaration (bindingAction language) Nat where
  origin := 3
  scope := ([], ())
  redex := number 7
  reactum := number 9

theorem equal_scalar_reading_does_not_erase_the_binder_scope :
    (bindingFiringSearch agent identityLabel [wrongScopeDeclaration]).length = 0 := by decide

def collisionLabel : BindingContext language ([], ()) ([], ()) :=
  (.nil : BindingContext language ([], ()) ([], ())).cons (leftFrame [] (number 7))

theorem same_outer_slot_is_rejected_but_other_position_is_minimal :
    (bindingFiringSearch (number (context := []) 7) collisionLabel [wrongScopeDeclaration]).length = 1 := by decide

theorem no_authored_origin_supplies_no_firing :
    bindingFiringSearch agent identityLabel
      ([] : List (FramePermission.Declaration (bindingAction language) Empty)) = [] := rfl

def closePair : Binding.Sub language [()] [] := fun sort position => by
  cases sort
  cases position with
  | zero => exact pair (number 7) (number 7)
  | succ impossible => cases impossible

def oldVariable : Binding.Term language [()] () := .var .zero

theorem closing_adds_literal_constructor_factors :
    (bindingFactors oldVariable).length = 1 ∧
      (bindingFactors (Binding.bind closePair oldVariable)).length = 3 := ⟨rfl, rfl⟩

theorem substituted_old_factors_do_not_exhaust_new_factors :
    (bindingFactors oldVariable).map (fun factor => factor.substitute [] closePair) ≠
      bindingFactors (Binding.bind closePair oldVariable) := by
  intro same
  have impossible : (1 : Nat) = 3 := congrArg List.length same
  cases impossible

def variableDeclaration : FramePermission.Declaration (bindingAction language) Nat where
  origin := 5
  scope := ([(), ()], ())
  redex := .var (.succ .zero)
  reactum := .var .zero

def variableAgent : Binding.Term language [(), ()] () := .var .zero
def variableLabel : BindingContext language ([(), ()], ()) ([(), ()], ()) := .nil
def mergeVariables : Binding.Sub language [(), ()] [] := fun sort position => by
  cases sort
  cases position with
  | zero => exact number 7
  | succ next =>
    cases next with
    | zero => exact number 7
    | succ impossible => cases impossible

def mergedInstance : BindingDeclarationInstance language Nat where
  original := variableDeclaration
  destination := []
  substitution := mergeVariables

theorem no_original_identity_match :
    bindingFiringSearch variableAgent variableLabel [variableDeclaration] = [] := by decide

theorem actual_noninjective_substitution_creates_a_match :
    (bindingFiringSearch (Binding.bind mergeVariables variableAgent) identityLabel
      [mergedInstance.realized]).length = 1 := by decide

theorem new_match_retains_original_origin_and_complete_target :
    mergedInstance.realized.origin = 5 ∧
      mergedInstance.realized.redex = number 7 ∧ mergedInstance.realized.reactum = number 7 :=
  ⟨rfl, rfl, rfl⟩

end Mettapedia.OSLF.Binding.ScopedEncoding.FiringSearchControls

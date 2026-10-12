import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaFocus

/-!
# Total finite checking of an authored instantiated focus

The traversal follows the authored rule position, including binder scopes.
It evaluates the selected authored subpattern with the actual completed
assignment and emits its independent FocusInstance evidence. It never
substitutes a raw endpoint position for the authored context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFocusChecking

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.OSLF.Framework.RedexPosition
open Instantiation

variable (operation : Pattern → Pattern → Pattern) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) (site : RulePatternSite) (assignment : Assignment)

abbrev Focus (path : List Nat) (depth : Nat) (pattern : Pattern) (position : Position) :=
  {focus : Pattern | FocusInstance operation rule spec ambient site assignment path depth pattern position focus}

def focusAt? (path : List Nat) (depth : Nat) (pattern : Pattern) :
    (position : Position) → Option (Focus operation rule spec ambient site assignment path depth pattern position)
  | [] => (instantiateWith? operation rule spec ambient site path depth assignment pattern).attach.map
      (fun focus => ⟨focus.val, .here focus.property⟩)
  | index :: rest => match pattern with
    | .apply label arguments => do
        let argument ← arguments[index]?.attach
        let focus ← focusAt? (path ++ [index]) depth argument.val rest
        pure ⟨focus.val, .application argument.property focus.property⟩
    | .lambda binder body =>
        if same : index = 0 then by
          subst index
          exact (focusAt? (path ++ [0]) (depth + 1) body rest).map
            (fun focus => ⟨focus.val, .lambda focus.property⟩)
        else none
    | .multiLambda arity binders body =>
        if same : index = 0 then by
          subst index
          exact (focusAt? (path ++ [0]) (depth + arity) body rest).map
            (fun focus => ⟨focus.val, .multiLambda focus.property⟩)
        else none
    | .subst body replacement =>
        if same : index = 0 then by
          subst index
          exact (focusAt? (path ++ [0]) (depth + 1) body rest).map
            (fun focus => ⟨focus.val, .substitutionBody focus.property⟩)
        else if same : index = 1 then by
          subst index
          exact (focusAt? (path ++ [1]) depth replacement rest).map
            (fun focus => ⟨focus.val, .substitutionArgument focus.property⟩)
        else none
    | .collection kind elements restVariable => do
        let element ← elements[index]?.attach
        let focus ← focusAt? (path ++ [index]) depth element.val rest
        pure ⟨focus.val, .collection element.property focus.property⟩
    | _ => none

variable {operation rule spec ambient site assignment}

theorem focusAt?_complete {path : List Nat} {depth : Nat} {pattern : Pattern} {position : Position}
    {focus : Pattern}
    (selected : FocusInstance operation rule spec ambient site assignment path depth pattern position focus) :
    ∃ found, focusAt? operation rule spec ambient site assignment path depth pattern position = some found ∧
      found.val = focus := by
  induction selected with
  | @here path depth pattern actual instantiated =>
      unfold focusAt?
      rw [Option.attach_eq_some _ ⟨actual, instantiated⟩]
      exact ⟨_, rfl, rfl⟩
  | @application path depth label arguments index argument focus rest located selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      unfold focusAt?
      dsimp only
      rw [Option.attach_eq_some _ ⟨argument, located⟩]
      dsimp only [Bind.bind, Option.bind]
      rw [checked]
      exact ⟨_, rfl, same⟩
  | lambda selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      simp only [focusAt?, ↓reduceDIte, checked, Option.map_some]
      exact ⟨_, rfl, same⟩
  | multiLambda selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      simp only [focusAt?, ↓reduceDIte, checked, Option.map_some]
      exact ⟨_, rfl, same⟩
  | substitutionBody selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      simp only [focusAt?, ↓reduceDIte, checked, Option.map_some]
      exact ⟨_, rfl, same⟩
  | substitutionArgument selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      simp only [focusAt?, Nat.one_ne_zero, ↓reduceDIte, checked, Option.map_some]
      exact ⟨_, rfl, same⟩
  | @collection path depth kind elements restVariable index element focus rest located selected ih =>
      obtain ⟨found, checked, same⟩ := ih
      unfold focusAt?
      dsimp only
      rw [Option.attach_eq_some _ ⟨element, located⟩]
      dsimp only [Bind.bind, Option.bind]
      rw [checked]
      exact ⟨_, rfl, same⟩

theorem focusAt?_exact (path : List Nat) (depth : Nat) (pattern : Pattern) (position : Position) (focus : Pattern) :
    (∃ found, focusAt? operation rule spec ambient site assignment path depth pattern position = some found ∧
      found.val = focus) ↔ FocusInstance operation rule spec ambient site assignment path depth pattern position focus := by
  constructor
  · rintro ⟨found, _, same⟩
    exact same ▸ found.property
  · exact focusAt?_complete

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingFocusChecking

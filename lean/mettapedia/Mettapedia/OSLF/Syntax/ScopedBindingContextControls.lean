import Mettapedia.OSLF.Syntax.ScopedBindingContextComparison
import Mettapedia.OSLF.Syntax.ScopedBindingSubstitutionCoherence

/-!
# Positional, capture and relative-pushout binding controls

The signature has genuine unary binding and binary constructors. Nested
binding substitution retains two fresh variables and moves the enclosing
variable to its independently specified destination. Separate hole positions
can have the same ground filling, while remaining distinct context arrows.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedEncoding.Controls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RelativePushout

inductive Operation where
  | number (value : Nat)
  | pair
  | binder

abbrev toy : Binding.Signature where
  Srt := Unit
  Op := fun _ => Operation
  arity := fun operator => match operator with
    | .number _ => []
    | .pair => [([], ()), ([], ())]
    | .binder => [([()], ())]

local instance : Quiver (Scope toy) := bindingFrameQuiver toy

def number {context : Binding.Ctx toy} (value : Nat) : Binding.Term toy context () :=
  .op (.number value) .nil

def pair {context : Binding.Ctx toy} (first second : Binding.Term toy context ()) :
    Binding.Term toy context () := .op .pair (.cons first (.cons second .nil))

def abstraction {context : Binding.Ctx toy} (body : Binding.Term toy (() :: context) ()) :
    Binding.Term toy context () := .op .binder (.cons body .nil)

def leftFrame (context : Binding.Ctx toy) (sibling : Binding.Term toy context ()) :
    BindingFrame toy (context, ()) (context, ()) :=
  .slot context () .pair 0 (Fin.cases (fun absent => False.elim (absent rfl))
    (fun previous _ => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact sibling))

def rightFrame (context : Binding.Ctx toy) (sibling : Binding.Term toy context ()) :
    BindingFrame toy (context, ()) (context, ()) :=
  .slot context () .pair 1 (Fin.cases (fun _ => sibling)
    (fun previous absent => by
      have only : previous = 0 := @Subsingleton.elim (Fin 1) inferInstance previous 0
      subst previous
      exact False.elim (absent rfl)))

def binderFrame (context : Binding.Ctx toy) :
    BindingFrame toy (() :: context, ()) (context, ()) :=
  .slot context () .binder 0 (fun other absent =>
    False.elim (absent (@Subsingleton.elim (Fin 1) inferInstance other 0)))

def single {source target : Scope toy} (frame : BindingFrame toy source target) :
    BindingContext toy source target := (.nil : BindingContext toy source source).cons frame

def nested : BindingContext toy ([(), (), ()], ()) ([()], ()) :=
  (single (binderFrame [(), ()])).comp (single (binderFrame [()]))

def body : Binding.Term toy [(), (), ()] () :=
  pair (.var .zero) (pair (.var (.succ .zero)) (.var (.succ (.succ .zero))))

def moveEnclosing : Binding.Sub toy [()] [(), ()] := fun sort position => by
  cases sort
  cases position with
  | zero => exact .var (.succ .zero)
  | succ impossible => cases impossible

def expectedBody : Binding.Term toy [(), (), (), ()] () :=
  pair (.var .zero) (pair (.var (.succ .zero)) (.var (.succ (.succ (.succ .zero)))))

def capturedBody : Binding.Term toy [(), (), (), ()] () :=
  pair (.var .zero) (pair (.var (.succ .zero)) (.var (.succ (.succ .zero))))

theorem nested_hole_scope : (substituteContext nested [(), ()] moveEnclosing).holeContext =
    [(), (), (), ()] := rfl

theorem first_fresh_variable : (substituteContext nested [(), ()] moveEnclosing).holeVariables
    () .zero = .var .zero := rfl

theorem second_fresh_variable : (substituteContext nested [(), ()] moveEnclosing).holeVariables
    () (.succ .zero) = .var (.succ .zero) := rfl

theorem enclosing_variable : (substituteContext nested [(), ()] moveEnclosing).holeVariables
    () (.succ (.succ .zero)) = .var (.succ (.succ (.succ .zero))) := rfl

theorem actual_nested_substitution : Binding.bind moveEnclosing (fillContext nested body) =
    abstraction (abstraction expectedBody) := rfl

theorem full_path_substitution :
    fillContext (substituteContext nested [(), ()] moveEnclosing).path
      (Binding.bind (substituteContext nested [(), ()] moveEnclosing).holeVariables body) =
      abstraction (abstraction expectedBody) :=
  (substituteContext_fill nested [(), ()] moveEnclosing body).symm.trans actual_nested_substitution

theorem capture_changes_body : expectedBody ≠ capturedBody := by
  intro same
  cases same

theorem capture_changes_result : Binding.bind moveEnclosing (fillContext nested body) ≠
    abstraction (abstraction capturedBody) := by
  rw [actual_nested_substitution]
  intro same
  cases same

theorem nested_whole_identity :
    substituteContext nested [()] (fun _ value => .var value) =
      (⟨[(), (), ()], fun _ value => .var value, nested⟩ :
        SubstitutedContext toy ([(), (), ()], ()) () [()]) :=
  substituteContext_identity nested

theorem nested_whole_composition (second : Binding.Sub toy [(), ()] [()]) :
    substituteContext nested [()] (fun sort value => Binding.bind second (moveEnclosing sort value)) =
      twiceSubstitutedContext nested [(), ()] [()] moveEnclosing second :=
  substituteContext_composition nested [(), ()] [()] moveEnclosing second

def leftContext : BindingContext toy ([], ()) ([], ()) := single (leftFrame [] (number 7))
def rightContext : BindingContext toy ([], ()) ([], ()) := single (rightFrame [] (number 7))

theorem equal_ground_readout : fillContext leftContext (number 7) = fillContext rightContext (number 7) := rfl

def selectedPosition {source target : Scope toy} (frame : BindingFrame toy source target) : Nat :=
  match frame with
  | .slot _ _ _ position _ => position.val

theorem different_positions : leftFrame [] (number 7) ≠ rightFrame [] (number 7) := by
  intro same
  have position : (0 : Nat) = 1 := congrArg selectedPosition same
  cases position

theorem different_contexts : leftContext ≠ rightContext := by
  intro same
  exact different_positions (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons same))

theorem different_context_arrows : bindingContextArrow leftContext ≠ bindingContextArrow rightContext := by
  intro same
  exact different_contexts (Arrow.context.inj same)

theorem complete_comparison_retains_positions :
    (contextFunctor toy).map (bindingContextArrow leftContext) ≠
      (contextFunctor toy).map (bindingContextArrow rightContext) :=
  fun same => different_context_arrows
    (@Functor.Faithful.map_injective _ _ _ _ (contextFunctor toy)
      (contextFunctor_faithful (S := toy)) _ _ _ _ same)

theorem collision_bound_has_relativePushouts :
    HasRelativePushouts (bindingTermArrow (S := toy) (scope := ([], ())) (number (context := []) 7))
      (bindingTermArrow (S := toy) (scope := ([], ())) (number (context := []) 7)) :=
  binding_redex_relativePushouts (S := toy) (first := ([], ())) (second := ([], ())) _ _

theorem collision_square : bindingTermArrow (number (context := []) 7) ≫ bindingContextArrow leftContext =
    bindingTermArrow (number (context := []) 7) ≫ bindingContextArrow rightContext :=
  congrArg bindingTermArrow equal_ground_readout

/-- Equal filled terms at different positions still give a genuine minimal
bound: no candidate can remove their different final context frames. -/
theorem collision_bound_is_idemPushout :
    IsIdemPushout (bindingTermArrow (number (context := []) 7))
      (bindingTermArrow (number (context := []) 7)) (bindingContextArrow leftContext)
      (bindingContextArrow rightContext) collision_square := by
  let candidate : PathCandidate (bindingAction toy) (number (context := []) 7)
      (first := ([], ())) (second := ([], ())) (target := ([], ()))
      (number (context := []) 7) leftContext rightContext :=
    PathCandidate.self equal_ground_readout
  have maximal : ∀ other : PathCandidate (bindingAction toy) (number (context := []) 7)
      (first := ([], ())) (second := ([], ())) (target := ([], ()))
      (number (context := []) 7) leftContext rightContext,
      other.down.length ≤ candidate.down.length := by
    intro other
    rcases other with ⟨apex, left, right, down, commutes, leftFactors, rightFactors⟩
    cases down with
    | nil => exact Nat.le_refl _
    | cons previous frame =>
      change (left.comp previous).cons frame =
        (.nil : BindingContext toy ([], ()) ([], ())).cons (leftFrame [] (number 7)) at leftFactors
      change (right.comp previous).cons frame =
        (.nil : BindingContext toy ([], ()) ([], ())).cons (rightFrame [] (number 7)) at rightFactors
      have sameFrames := (Quiver.Path.hom_heq_of_cons_eq_cons leftFactors).symm.trans
        (Quiver.Path.hom_heq_of_cons_eq_cons rightFactors)
      exact False.elim (different_positions (eq_of_heq sameFrames))
  exact PathCandidate.categorical_isRelativePushout candidate maximal

def duplicatedHole : Binding.Term toy [()] () := pair (.var .zero) (.var .zero)

theorem duplicated_occurrences : Binding.holeCount duplicatedHole = 2 := rfl

theorem duplicated_is_not_linear : Binding.holeCount duplicatedHole ≠ 1 := by
  rw [duplicated_occurrences]
  decide

end Mettapedia.OSLF.Binding.ScopedEncoding.Controls

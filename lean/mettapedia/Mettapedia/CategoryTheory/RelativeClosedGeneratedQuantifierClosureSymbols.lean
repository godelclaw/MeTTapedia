import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierIteration

/-!
# Authored names in the quantifier closure

The closure retains the initial object names. Each newly declared operator
or equation retains its stage and complete typed route. Passing an old name
through a successor stage does not create a second authored occurrence.
The actual finite-stage object and arrow expressions are mapped recursively;
their complete expressions commute with every successor inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def symbols : Symbols.{k} where
  ObjectName := initial.symbols.ObjectName
  ArrowName := initial.symbols.ArrowName ⊕
    (Σ depth : Nat, Operation (stages initial depth).presentation)
  EquationName := initial.symbols.EquationName ⊕
    (Σ depth : Nat, Law (stages initial depth).presentation)

def objects : (depth : Nat) → (stages initial depth).symbols.ObjectName → (symbols initial).ObjectName
  | 0, origin => origin
  | depth + 1, origin => objects depth origin

def arrows : (depth : Nat) → (stages initial depth).symbols.ArrowName → (symbols initial).ArrowName
  | 0, origin => .inl origin
  | depth + 1, .inl origin => arrows depth origin
  | depth + 1, .inr origin => .inr ⟨depth, origin⟩

def equations : (depth : Nat) → (stages initial depth).symbols.EquationName → (symbols initial).EquationName
  | 0, origin => .inl origin
  | depth + 1, .inl origin => equations depth origin
  | depth + 1, .inr origin => .inr ⟨depth, origin⟩

def objectCode (depth : Nat) (code : ObjectCode C (stages initial depth).symbols) :
    ObjectCode C (symbols initial) :=
  code.map (Functor.id C) (objects initial depth) (arrows initial depth)

def arrowCode (depth : Nat) (code : ArrowCode C (stages initial depth).symbols) :
    ArrowCode C (symbols initial) :=
  code.map (Functor.id C) (objects initial depth) (arrows initial depth)

theorem objects_step (depth : Nat) (origin : (stages initial depth).symbols.ObjectName) :
    objects initial (depth + 1) ((stages initial depth).inclusion.objects origin) =
      objects initial depth origin := rfl

theorem arrows_step (depth : Nat) (origin : (stages initial depth).symbols.ArrowName) :
    arrows initial (depth + 1) ((stages initial depth).inclusion.arrows origin) =
      arrows initial depth origin := rfl

theorem equations_step (depth : Nat) (origin : (stages initial depth).symbols.EquationName) :
    equations initial (depth + 1) ((stages initial depth).inclusion.equations origin) =
      equations initial depth origin := rfl

theorem new_arrow (depth : Nat) (origin : Operation (stages initial depth).presentation) :
    arrows initial (depth + 1) (.inr origin) = .inr ⟨depth, origin⟩ := rfl

theorem new_equation (depth : Nat) (origin : Law (stages initial depth).presentation) :
    equations initial (depth + 1) (.inr origin) = .inr ⟨depth, origin⟩ := rfl

theorem objectCode_step (depth : Nat) (code : ObjectCode C (stages initial depth).symbols) :
    objectCode initial (depth + 1)
      (code.map (stages initial depth).inclusion.base
        (stages initial depth).inclusion.objects (stages initial depth).inclusion.arrows) =
      objectCode initial depth code := by
  exact ObjectCode.map_compose (stages initial depth).inclusion.base (Functor.id C)
    (stages initial depth).inclusion.objects (objects initial (depth + 1))
    (stages initial depth).inclusion.arrows (arrows initial (depth + 1)) code

theorem arrowCode_step (depth : Nat) (code : ArrowCode C (stages initial depth).symbols) :
    arrowCode initial (depth + 1)
      (code.map (stages initial depth).inclusion.base
        (stages initial depth).inclusion.objects (stages initial depth).inclusion.arrows) =
      arrowCode initial depth code := by
  exact ArrowCode.map_compose (stages initial depth).inclusion.base (Functor.id C)
    (stages initial depth).inclusion.objects (objects initial (depth + 1))
    (stages initial depth).inclusion.arrows (arrows initial (depth + 1)) code

theorem new_arrow_is_not_an_initial_origin (depth : Nat)
    (origin : Operation (stages initial depth).presentation) (old : initial.symbols.ArrowName) :
    arrows initial (depth + 1) (.inr origin) ≠ .inl old := by
  intro impossible
  cases impossible

theorem new_equation_is_not_an_initial_origin (depth : Nat)
    (origin : Law (stages initial depth).presentation) (old : initial.symbols.EquationName) :
    equations initial (depth + 1) (.inr origin) ≠ .inl old := by
  intro impossible
  cases impossible

theorem new_arrow_stage_retained (depth later : Nat)
    (origin : Operation (stages initial depth).presentation)
    (other : Operation (stages initial later).presentation)
    (same : (Sum.inr ⟨depth, origin⟩ : (symbols initial).ArrowName) = .inr ⟨later, other⟩) :
    depth = later := congrArg Sigma.fst (Sum.inr.inj same)

theorem new_equation_stage_retained (depth later : Nat)
    (origin : Law (stages initial depth).presentation)
    (other : Law (stages initial later).presentation)
    (same : (Sum.inr ⟨depth, origin⟩ : (symbols initial).EquationName) = .inr ⟨later, other⟩) :
    depth = later := congrArg Sigma.fst (Sum.inr.inj same)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

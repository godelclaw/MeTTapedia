import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureFiniteOrigin
import Mettapedia.CategoryTheory.RelativeClosedSyntaxCodeMapInjective

/-!
# Exact stage images of names and complete expressions

The stage of birth is retained by each new authored name. A finite-stage
name map is injective and covers precisely the names born by that stage.
Consequently its whole object and arrow code maps reflect equality. This
does not claim that adjoining equations is faithful on quotient arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def arrowBirth : (symbols initial).ArrowName → Nat
  | .inl _ => 0
  | .inr ⟨depth, _⟩ => depth + 1

def equationBirth : (symbols initial).EquationName → Nat
  | .inl _ => 0
  | .inr ⟨depth, _⟩ => depth + 1

theorem arrows_birth_bound : (depth : Nat) → (origin : (stages initial depth).symbols.ArrowName) →
    arrowBirth initial (arrows initial depth origin) ≤ depth
  | 0, _ => Nat.le_refl _
  | depth + 1, .inl origin => (arrows_birth_bound depth origin).trans (Nat.le_succ depth)
  | _ + 1, .inr _ => Nat.le_refl _

theorem equations_birth_bound : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    equationBirth initial (equations initial depth origin) ≤ depth
  | 0, _ => Nat.le_refl _
  | depth + 1, .inl origin => (equations_birth_bound depth origin).trans (Nat.le_succ depth)
  | _ + 1, .inr _ => Nat.le_refl _

theorem objects_injective : (depth : Nat) → Function.Injective (objects initial depth)
  | 0 => fun {_ _} same => same
  | depth + 1 => objects_injective depth

theorem arrows_injective : (depth : Nat) → Function.Injective (arrows initial depth)
  | 0 => fun {_ _} same => Sum.inl.inj same
  | depth + 1 => by
      intro first second same
      cases first with
      | inl first =>
        cases second with
        | inl second => exact congrArg Sum.inl (arrows_injective depth same)
        | inr second =>
          have before := arrows_birth_bound initial depth first
          have reading := congrArg (arrowBirth initial) same
          change arrowBirth initial (arrows initial depth first) = depth + 1 at reading
          rw [reading] at before
          omega
      | inr first =>
        cases second with
        | inl second =>
          have before := arrows_birth_bound initial depth second
          have reading := congrArg (arrowBirth initial) same
          change depth + 1 = arrowBirth initial (arrows initial depth second) at reading
          rw [← reading] at before
          omega
        | inr second =>
          exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj same)).2)

theorem equations_injective : (depth : Nat) → Function.Injective (equations initial depth)
  | 0 => fun {_ _} same => Sum.inl.inj same
  | depth + 1 => by
      intro first second same
      cases first with
      | inl first =>
        cases second with
        | inl second => exact congrArg Sum.inl (equations_injective depth same)
        | inr second =>
          have before := equations_birth_bound initial depth first
          have reading := congrArg (equationBirth initial) same
          change equationBirth initial (equations initial depth first) = depth + 1 at reading
          rw [reading] at before
          omega
      | inr first =>
        cases second with
        | inl second =>
          have before := equations_birth_bound initial depth second
          have reading := congrArg (equationBirth initial) same
          change depth + 1 = equationBirth initial (equations initial depth second) at reading
          rw [← reading] at before
          omega
        | inr second =>
          exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj same)).2)

theorem arrows_preimage : (depth : Nat) → (origin : (symbols initial).ArrowName) →
    (∃ previous : (stages initial depth).symbols.ArrowName, arrows initial depth previous = origin) ↔
      arrowBirth initial origin ≤ depth
  | 0, .inl origin => ⟨fun _ => Nat.le_refl _, fun _ => ⟨origin, rfl⟩⟩
  | 0, .inr ⟨born, origin⟩ => by
      constructor
      · rintro ⟨previous, impossible⟩
        cases impossible
      · intro impossible
        change born + 1 ≤ 0 at impossible
        omega
  | depth + 1, origin => by
      constructor
      · rintro ⟨previous, read⟩
        exact read ▸ arrows_birth_bound initial (depth + 1) previous
      · intro admitted
        cases origin with
        | inl origin =>
          obtain ⟨previous, read⟩ := (arrows_preimage depth (.inl origin)).mpr (Nat.zero_le _)
          exact ⟨.inl previous, read⟩
        | inr origin =>
          obtain ⟨born, origin⟩ := origin
          by_cases same : born = depth
          · subst born
            exact ⟨.inr origin, rfl⟩
          · have previousBound : arrowBirth initial (.inr ⟨born, origin⟩) ≤ depth := by
              change born + 1 ≤ depth
              change born + 1 ≤ depth + 1 at admitted
              omega
            obtain ⟨previous, read⟩ := (arrows_preimage depth (.inr ⟨born, origin⟩)).mpr previousBound
            exact ⟨.inl previous, read⟩

theorem equations_preimage : (depth : Nat) → (origin : (symbols initial).EquationName) →
    (∃ previous : (stages initial depth).symbols.EquationName, equations initial depth previous = origin) ↔
      equationBirth initial origin ≤ depth
  | 0, .inl origin => ⟨fun _ => Nat.le_refl _, fun _ => ⟨origin, rfl⟩⟩
  | 0, .inr ⟨born, origin⟩ => by
      constructor
      · rintro ⟨previous, impossible⟩
        cases impossible
      · intro impossible
        change born + 1 ≤ 0 at impossible
        omega
  | depth + 1, origin => by
      constructor
      · rintro ⟨previous, read⟩
        exact read ▸ equations_birth_bound initial (depth + 1) previous
      · intro admitted
        cases origin with
        | inl origin =>
          obtain ⟨previous, read⟩ := (equations_preimage depth (.inl origin)).mpr (Nat.zero_le _)
          exact ⟨.inl previous, read⟩
        | inr origin =>
          obtain ⟨born, origin⟩ := origin
          by_cases same : born = depth
          · subst born
            exact ⟨.inr origin, rfl⟩
          · have previousBound : equationBirth initial (.inr ⟨born, origin⟩) ≤ depth := by
              change born + 1 ≤ depth
              change born + 1 ≤ depth + 1 at admitted
              omega
            obtain ⟨previous, read⟩ := (equations_preimage depth (.inr ⟨born, origin⟩)).mpr previousBound
            exact ⟨.inl previous, read⟩

theorem objectCode_injective (depth : Nat) : Function.Injective (objectCode initial depth) :=
  fun first second same => ObjectCode.map_injective (objects initial depth) (arrows initial depth)
    (objects_injective initial depth) (arrows_injective initial depth) first second same

theorem arrowCode_injective (depth : Nat) : Function.Injective (arrowCode initial depth) :=
  fun first second same => ArrowCode.map_injective (objects initial depth) (arrows initial depth)
    (objects_injective initial depth) (arrows_injective initial depth) first second same

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

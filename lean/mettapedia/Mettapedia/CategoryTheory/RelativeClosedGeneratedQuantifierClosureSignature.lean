import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureSymbols
import Mettapedia.CategoryTheory.RelativeClosedSyntaxDeclarationBounds

/-!
# The rank-ordered signature of quantifier closure

Every initial declaration and every stage-tagged new declaration supplies
its actual complete header or equation. Declaration ranks are inherited
from those independently formed finite stages. Complete expression mapping
preserves these ranks, so the merged signature's earlier-name obligations
are proved from the original local obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def objectRank : (symbols initial).ObjectName → Nat := initial.presentation.objectRank

def arrowRank : (symbols initial).ArrowName → Nat
  | .inl origin => initial.presentation.arrowRank origin
  | .inr ⟨depth, origin⟩ => (stages initial (depth + 1)).presentation.arrowRank (.inr origin)

def equationRank : (symbols initial).EquationName → Nat
  | .inl origin => initial.presentation.equationRank origin
  | .inr ⟨depth, origin⟩ => (stages initial (depth + 1)).presentation.equationRank (.inr origin)

theorem objectRank_read : (depth : Nat) → (origin : (stages initial depth).symbols.ObjectName) →
    objectRank initial (objects initial depth origin) = (stages initial depth).presentation.objectRank origin
  | 0, _ => rfl
  | depth + 1, origin => objectRank_read depth origin

theorem arrowRank_read : (depth : Nat) → (origin : (stages initial depth).symbols.ArrowName) →
    arrowRank initial (arrows initial depth origin) = (stages initial depth).presentation.arrowRank origin
  | 0, _ => rfl
  | depth + 1, .inl origin => arrowRank_read depth origin
  | _ + 1, .inr _ => rfl

theorem equationRank_read : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    equationRank initial (equations initial depth origin) = (stages initial depth).presentation.equationRank origin
  | 0, _ => rfl
  | depth + 1, .inl origin => equationRank_read depth origin
  | _ + 1, .inr _ => rfl

theorem object_before (depth : Nat) (code : ObjectCode C (stages initial depth).symbols) (bound : Nat) :
    (objectCode initial depth code).before (objectRank initial) (arrowRank initial) bound ↔
      code.before (stages initial depth).presentation.objectRank (stages initial depth).presentation.arrowRank bound :=
  DeclarationBounds.object_before_map (stages initial depth).presentation.objectRank
    (stages initial depth).presentation.arrowRank (Functor.id C) (objects initial depth) (arrows initial depth)
    (objectRank initial) (arrowRank initial) (objectRank_read initial depth) (arrowRank_read initial depth) bound code

theorem arrow_before (depth : Nat) (code : ArrowCode C (stages initial depth).symbols) (bound : Nat) :
    (arrowCode initial depth code).before (objectRank initial) (arrowRank initial) bound ↔
      code.before (stages initial depth).presentation.objectRank (stages initial depth).presentation.arrowRank bound :=
  DeclarationBounds.arrow_before_map (stages initial depth).presentation.objectRank
    (stages initial depth).presentation.arrowRank (Functor.id C) (objects initial depth) (arrows initial depth)
    (objectRank initial) (arrowRank initial) (objectRank_read initial depth) (arrowRank_read initial depth) bound code

def source : (symbols initial).ArrowName → ObjectCode C (symbols initial)
  | .inl origin => objectCode initial 0 (initial.presentation.source origin)
  | .inr ⟨depth, origin⟩ =>
      objectCode initial (depth + 1) ((stages initial (depth + 1)).presentation.source (.inr origin))

def target : (symbols initial).ArrowName → ObjectCode C (symbols initial)
  | .inl origin => objectCode initial 0 (initial.presentation.target origin)
  | .inr ⟨depth, origin⟩ =>
      objectCode initial (depth + 1) ((stages initial (depth + 1)).presentation.target (.inr origin))

def equationSource : (symbols initial).EquationName → ObjectCode C (symbols initial)
  | .inl origin => objectCode initial 0 (initial.presentation.equationSource origin)
  | .inr ⟨depth, origin⟩ =>
      objectCode initial (depth + 1) ((stages initial (depth + 1)).presentation.equationSource (.inr origin))

def equationTarget : (symbols initial).EquationName → ObjectCode C (symbols initial)
  | .inl origin => objectCode initial 0 (initial.presentation.equationTarget origin)
  | .inr ⟨depth, origin⟩ =>
      objectCode initial (depth + 1) ((stages initial (depth + 1)).presentation.equationTarget (.inr origin))

def left : (symbols initial).EquationName → ArrowCode C (symbols initial)
  | .inl origin => arrowCode initial 0 (initial.presentation.left origin)
  | .inr ⟨depth, origin⟩ =>
      arrowCode initial (depth + 1) ((stages initial (depth + 1)).presentation.left (.inr origin))

def right : (symbols initial).EquationName → ArrowCode C (symbols initial)
  | .inl origin => arrowCode initial 0 (initial.presentation.right origin)
  | .inr ⟨depth, origin⟩ =>
      arrowCode initial (depth + 1) ((stages initial (depth + 1)).presentation.right (.inr origin))

theorem source_read : (depth : Nat) → (origin : (stages initial depth).symbols.ArrowName) →
    source initial (arrows initial depth origin) = objectCode initial depth ((stages initial depth).presentation.source origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change source initial (arrows initial depth origin) = objectCode initial (depth + 1)
        ((stages initial depth).next.presentation.source ((stages initial depth).inclusion.arrows origin))
      rw [(stages initial depth).inclusion.source origin]
      exact (source_read depth origin).trans (objectCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

theorem target_read : (depth : Nat) → (origin : (stages initial depth).symbols.ArrowName) →
    target initial (arrows initial depth origin) = objectCode initial depth ((stages initial depth).presentation.target origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change target initial (arrows initial depth origin) = objectCode initial (depth + 1)
        ((stages initial depth).next.presentation.target ((stages initial depth).inclusion.arrows origin))
      rw [(stages initial depth).inclusion.target origin]
      exact (target_read depth origin).trans (objectCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

theorem equationSource_read : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    equationSource initial (equations initial depth origin) =
      objectCode initial depth ((stages initial depth).presentation.equationSource origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change equationSource initial (equations initial depth origin) = objectCode initial (depth + 1)
        ((stages initial depth).next.presentation.equationSource ((stages initial depth).inclusion.equations origin))
      rw [(stages initial depth).inclusion.equationSource origin]
      exact (equationSource_read depth origin).trans (objectCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

theorem equationTarget_read : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    equationTarget initial (equations initial depth origin) =
      objectCode initial depth ((stages initial depth).presentation.equationTarget origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change equationTarget initial (equations initial depth origin) = objectCode initial (depth + 1)
        ((stages initial depth).next.presentation.equationTarget ((stages initial depth).inclusion.equations origin))
      rw [(stages initial depth).inclusion.equationTarget origin]
      exact (equationTarget_read depth origin).trans (objectCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

theorem left_read : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    left initial (equations initial depth origin) = arrowCode initial depth ((stages initial depth).presentation.left origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change left initial (equations initial depth origin) = arrowCode initial (depth + 1)
        ((stages initial depth).next.presentation.left ((stages initial depth).inclusion.equations origin))
      rw [(stages initial depth).inclusion.left origin]
      exact (left_read depth origin).trans (arrowCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

theorem right_read : (depth : Nat) → (origin : (stages initial depth).symbols.EquationName) →
    right initial (equations initial depth origin) = arrowCode initial depth ((stages initial depth).presentation.right origin)
  | 0, _ => rfl
  | depth + 1, .inl origin => by
      change right initial (equations initial depth origin) = arrowCode initial (depth + 1)
        ((stages initial depth).next.presentation.right ((stages initial depth).inclusion.equations origin))
      rw [(stages initial depth).inclusion.right origin]
      exact (right_read depth origin).trans (arrowCode_step initial depth _).symm
  | _ + 1, .inr _ => rfl

def signature : Signature (C := C) (symbols := symbols initial) where
  objectRank := objectRank initial
  arrowRank := arrowRank initial
  source := source initial
  target := target initial
  source_before
    | .inl origin => (object_before initial 0 _ _).mpr (initial.presentation.source_before origin)
    | .inr ⟨depth, origin⟩ =>
        (object_before initial (depth + 1) _ _).mpr
          ((stages initial (depth + 1)).presentation.source_before (.inr origin))
  target_before
    | .inl origin => (object_before initial 0 _ _).mpr (initial.presentation.target_before origin)
    | .inr ⟨depth, origin⟩ =>
        (object_before initial (depth + 1) _ _).mpr
          ((stages initial (depth + 1)).presentation.target_before (.inr origin))
  equationRank := equationRank initial
  equationSource := equationSource initial
  equationTarget := equationTarget initial
  left := left initial
  right := right initial
  equation_before
    | .inl origin => by
        obtain ⟨first, last, before, after⟩ := initial.presentation.equation_before origin
        exact ⟨(object_before initial 0 _ _).mpr first, (object_before initial 0 _ _).mpr last,
          (arrow_before initial 0 _ _).mpr before, (arrow_before initial 0 _ _).mpr after⟩
    | .inr ⟨depth, origin⟩ => by
        obtain ⟨first, last, before, after⟩ :=
          (stages initial (depth + 1)).presentation.equation_before (.inr origin)
        exact ⟨(object_before initial (depth + 1) _ _).mpr first,
          (object_before initial (depth + 1) _ _).mpr last,
          (arrow_before initial (depth + 1) _ _).mpr before,
          (arrow_before initial (depth + 1) _ _).mpr after⟩

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

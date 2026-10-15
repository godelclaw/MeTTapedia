import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureStages
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierNativeIteration

/-!
# Independent native meanings for the complete closure signature

Initial generator meanings are retained. Each tagged new operator takes its
complete actual classifier meaning from the independently constructed finite
stage at which it was authored. Recursion on local declaration names earns
the exact assignment restriction at every stage. The existing all-expression
parser theorem then derives both successful and rejected closure readings.
No final realization or whole-expression equality is an input field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z p
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D} {stage : Stage C}

def nativeAssignment (initial : NativeModel doctrine stage) :
    RelativeClosedSyntax.Interpretation.Assignment C (symbols stage) D where
  base := initial.meanings.base
  object := initial.meanings.object
  arrow
    | .inl origin => initial.meanings.arrow origin
    | .inr ⟨depth, origin⟩ => (nativeModels initial (depth + 1)).meanings.arrow (.inr origin)

variable (initial : NativeModel doctrine stage)

theorem native_base_read : (depth : Nat) →
    (nativeModels initial depth).meanings.base = initial.meanings.base
  | 0 => rfl
  | depth + 1 => native_base_read depth

theorem native_object_read : (depth : Nat) → (origin : (stages stage depth).symbols.ObjectName) →
    (nativeAssignment initial).object (objects stage depth origin) =
      (nativeModels initial depth).meanings.object origin
  | 0, _ => rfl
  | depth + 1, origin => native_object_read depth origin

theorem native_arrow_read : (depth : Nat) → (origin : (stages stage depth).symbols.ArrowName) →
    (nativeAssignment initial).arrow (arrows stage depth origin) =
      (nativeModels initial depth).meanings.arrow origin
  | 0, _ => rfl
  | depth + 1, .inl origin => native_arrow_read depth origin
  | _ + 1, .inr _ => rfl

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_extensionality
    {names : Symbols.{k}}
    {first second : RelativeClosedSyntax.Interpretation.Assignment C names D}
    (bases : first.base = second.base)
    (objects : ∀ origin, first.object origin = second.object origin)
    (arrows : ∀ origin, first.arrow origin = second.arrow origin) : first = second := by
  rcases first with ⟨firstBase, firstObjects, firstArrows⟩
  rcases second with ⟨secondBase, secondObjects, secondArrows⟩
  dsimp only at bases objects arrows
  subst secondBase
  have sameObjects := funext objects
  have sameArrows := funext arrows
  subst secondObjects secondArrows
  rfl

theorem native_assignment_restriction (depth : Nat) :
    (stageMap stage depth).precompose (nativeAssignment initial) =
      (nativeModels initial depth).meanings :=
  assignment_extensionality
    ((Functor.id_comp initial.meanings.base).trans (native_base_read initial depth).symm)
    (native_object_read initial depth) (native_arrow_read initial depth)

theorem native_object_readout (depth : Nat) (code : ObjectCode C (stages stage depth).symbols) :
    (nativeAssignment initial).evaluateObject (objectCode stage depth code) =
      (nativeModels initial depth).meanings.evaluateObject code :=
  ((stageMap stage depth).evaluateObject_precompose (nativeAssignment initial) code).trans
    (congrArg (fun assignment => assignment.evaluateObject code) (native_assignment_restriction initial depth))

theorem native_arrow_readout (depth : Nat) (code : ArrowCode C (stages stage depth).symbols) :
    (nativeAssignment initial).evaluateArrow (arrowCode stage depth code) =
      (nativeModels initial depth).meanings.evaluateArrow code :=
  ((stageMap stage depth).evaluateArrow_precompose (nativeAssignment initial) code).trans
    (congrArg (fun assignment => assignment.evaluateArrow code) (native_assignment_restriction initial depth))

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

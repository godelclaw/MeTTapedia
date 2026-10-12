import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierSourceOperations

/-!
# Iterated quantifier admission with one retained proposition object

A stage retains an independently formed presentation, truth and conjunction
with their four finite source diagrams. Its successor adjoins quantifiers
for every complete typed old raw arrow, deriving the new header admission
and inherited diagrams. All raw contexts are retained. The same proposition
object is transported through the actual inclusions; no new proposition
generator is introduced by iteration.

Each finite stage has genuine all-context quantifier adjunctions at the
previous stage's routes. Forming a final closure category and proving its
universal interpretation are separate from these finite-stage theorems.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k
variable (C : Type k) [Category.{k} C]

structure Stage where
  symbols : Symbols.{k}
  presentation : Signature (C := C) (symbols := symbols)
  formed : HeaderFormation presentation
  language : PredicateSyntax presentation
  truth : RawHom (terminal presentation) language.proposition
  laws : (SourceOperations.operations language truth).Laws

variable {C}

def Stage.next (previous : Stage C) : Stage C where
  symbols := EquationExtension.extendedSymbols
    (ArrowExtension.extendedSymbols previous.symbols (Operation previous.presentation))
    (Law previous.presentation)
  presentation := signature previous.presentation previous.language
  formed := headers previous.presentation previous.language previous.formed
  language := retainedSyntax previous.presentation previous.language
  truth := SourceOperations.stageTruth previous.presentation previous.language previous.truth
  laws := SourceOperations.stage_laws previous.presentation previous.language previous.truth previous.laws

def Stage.inclusion (previous : Stage C) :
    SignatureMap previous.presentation previous.next.presentation :=
  SourceOperations.stageInclusion previous.presentation previous.language

theorem Stage.proposition_retained (previous : Stage C) :
    previous.next.language.proposition = previous.inclusion.object previous.language.proposition :=
  SignatureMap.object_compose (arrowInclusion previous.presentation previous.language)
    (equationInclusion previous.presentation previous.language) previous.language.proposition

def Stage.mappedRoute (previous : Stage C) (route : Route previous.presentation) :
    Route previous.next.presentation :=
  SourceOperations.stageRoute previous.presentation previous.language route

def Stage.quantifierRoute (previous : Stage C) (kind : Kind) (route : Route previous.presentation) :
    Route previous.next.presentation where
  source := previous.next.language.power (previous.mappedRoute route).source
  target := previous.next.language.power (previous.mappedRoute route).target
  arrow := named previous.presentation previous.language kind route

theorem Stage.quantifier_is_an_actual_added_name (previous : Stage C) (kind : Kind)
    (route : Route previous.presentation) :
    (previous.quantifierRoute kind route).arrow.code = .name (Sum.inr ⟨kind, route⟩) := rfl

theorem Stage.quantifier_name_is_distinct_from_every_old_primitive (previous : Stage C)
    (kind : Kind) (route : Route previous.presentation) (origin : previous.symbols.ArrowName) :
    (previous.quantifierRoute kind route).arrow.code ≠ .name (Sum.inl origin) := by
  intro impossible
  have origins : (Sum.inr ⟨kind, route⟩ : previous.next.symbols.ArrowName) = Sum.inl origin :=
    ArrowCode.name.inj impossible
  cases origins

def stages (initial : Stage C) : Nat → Stage C
  | 0 => initial
  | depth + 1 => (stages initial depth).next

def initialInclusion (initial : Stage C) : (depth : Nat) →
    SignatureMap initial.presentation (stages initial depth).presentation
  | 0 => SignatureMap.identity initial.presentation
  | depth + 1 => (initialInclusion initial depth).compose (stages initial depth).inclusion

theorem proposition_retained (initial : Stage C) (depth : Nat) :
    (stages initial depth).language.proposition = (initialInclusion initial depth).object initial.language.proposition := by
  induction depth with
  | zero =>
    apply Object.ext
    exact (ObjectCode.map_identity initial.language.proposition.code).symm
  | succ depth inductionHypothesis =>
    exact ((stages initial depth).proposition_retained).trans
      ((congrArg (stages initial depth).inclusion.object inductionHypothesis).trans
        (SignatureMap.object_compose (initialInclusion initial depth) (stages initial depth).inclusion
          initial.language.proposition))

def universalQualification (initial : Stage C) (depth : Nat)
    (route : Route (stages initial depth).presentation) :
    InternalPredicateQuantifier.Universal
      (SourceOperations.operations (stages initial (depth + 1)).language (stages initial (depth + 1)).truth)
      (classOf ((stages initial depth).mappedRoute route).arrow) :=
  SourceOperations.universalQualification (stages initial depth).presentation
    (stages initial depth).language (stages initial depth).truth route

def existentialQualification (initial : Stage C) (depth : Nat)
    (route : Route (stages initial depth).presentation) :
    InternalPredicateExistential.Existential
      (SourceOperations.operations (stages initial (depth + 1)).language (stages initial (depth + 1)).truth)
      (classOf ((stages initial depth).mappedRoute route).arrow) :=
  SourceOperations.existentialQualification (stages initial depth).presentation
    (stages initial depth).language (stages initial depth).truth route

theorem universal_galois (initial : Stage C) (depth : Nat)
    (route : Route (stages initial depth).presentation)
    (context : Object (stages initial (depth + 1)).presentation) :
    let operations := SourceOperations.operations (stages initial (depth + 1)).language (stages initial (depth + 1)).truth
    let actual := (stages initial depth).mappedRoute route
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power operations actual.target) :=
      (InternalPredicateFunctionObject.operations operations actual.target).semilattice
        (InternalPredicateFunctionObject.function_laws operations (stages initial (depth + 1)).laws _) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power operations actual.source) :=
      (InternalPredicateFunctionObject.operations operations actual.source).semilattice
        (InternalPredicateFunctionObject.function_laws operations (stages initial (depth + 1)).laws _) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power operations actual.target =>
        predicate ≫ InternalPredicateQuantifier.precomposition operations (classOf actual.arrow))
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power operations actual.source =>
        predicate ≫ (universalQualification initial depth route).operation) :=
  SourceOperations.universal_galois (stages initial depth).presentation (stages initial depth).language
    (stages initial depth).truth (stages initial (depth + 1)).laws route context

theorem existential_galois (initial : Stage C) (depth : Nat)
    (route : Route (stages initial depth).presentation)
    (context : Object (stages initial (depth + 1)).presentation) :
    let operations := SourceOperations.operations (stages initial (depth + 1)).language (stages initial (depth + 1)).truth
    let actual := (stages initial depth).mappedRoute route
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power operations actual.source) :=
      (InternalPredicateFunctionObject.operations operations actual.source).semilattice
        (InternalPredicateFunctionObject.function_laws operations (stages initial (depth + 1)).laws _) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power operations actual.target) :=
      (InternalPredicateFunctionObject.operations operations actual.target).semilattice
        (InternalPredicateFunctionObject.function_laws operations (stages initial (depth + 1)).laws _) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power operations actual.source =>
        predicate ≫ (existentialQualification initial depth route).operation)
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power operations actual.target =>
        predicate ≫ InternalPredicateQuantifier.precomposition operations (classOf actual.arrow)) :=
  SourceOperations.existential_galois (stages initial depth).presentation (stages initial depth).language
    (stages initial depth).truth (stages initial (depth + 1)).laws route context

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Iteration

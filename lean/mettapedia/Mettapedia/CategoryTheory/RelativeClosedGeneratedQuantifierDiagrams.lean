import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierSourceOperations

/-!
# Local raw quantifier diagrams and their actual transport

An operator retains its complete supplied raw arrow. Three finite equations
on the actual ordered-function presentation, unit and counit earn its full
quantifier qualification. Generated signature maps transport those equations
through the independently constructed quotient functor. No all-context
adjunction or expression compatibility is assumed by this local interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory

universe k l
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {original : Signature (C := C) (symbols := symbols)}
variable (language : PredicateSyntax original) (route : Route original)

structure UniversalDiagrams where
  operation : RawHom (language.power route.source) (language.power route.target)
  monotonicity :
    classOf (language.powerMeet route.target
      ((language.larger route.source).compose operation)
      ((language.smaller route.source).compose operation)) =
        classOf ((language.smaller route.source).compose operation)
  unit :
    classOf (language.powerMeet route.target
      ((language.precomposition route).compose operation)
      (RawHom.identity (language.power route.target))) =
        classOf (RawHom.identity (language.power route.target))
  counit :
    classOf (language.powerMeet route.source
      (RawHom.identity (language.power route.source))
      (operation.compose (language.precomposition route))) =
        classOf (operation.compose (language.precomposition route))

structure ExistentialDiagrams where
  operation : RawHom (language.power route.source) (language.power route.target)
  monotonicity :
    classOf (language.powerMeet route.target
      ((language.larger route.source).compose operation)
      ((language.smaller route.source).compose operation)) =
        classOf ((language.smaller route.source).compose operation)
  unit :
    classOf (language.powerMeet route.source
      (operation.compose (language.precomposition route))
      (RawHom.identity (language.power route.source))) =
        classOf (RawHom.identity (language.power route.source))
  counit :
    classOf (language.powerMeet route.target
      (RawHom.identity (language.power route.target))
      ((language.precomposition route).compose operation)) =
        classOf ((language.precomposition route).compose operation)

variable {language route}
variable {E : Type l} [Category.{l} E] {nextSymbols : Symbols.{l}}
variable {next : Signature (C := E) (symbols := nextSymbols)}

def UniversalDiagrams.translate (diagrams : UniversalDiagrams language route)
    (mapping : SignatureMap original next) :
    UniversalDiagrams (language.translate mapping) (route.translate mapping) where
  operation := mapping.rawArrow diagrams.operation
  monotonicity := congrArg mapping.functor.map diagrams.monotonicity
  unit := congrArg mapping.functor.map diagrams.unit
  counit := congrArg mapping.functor.map diagrams.counit

def ExistentialDiagrams.translate (diagrams : ExistentialDiagrams language route)
    (mapping : SignatureMap original next) :
    ExistentialDiagrams (language.translate mapping) (route.translate mapping) where
  operation := mapping.rawArrow diagrams.operation
  monotonicity := congrArg mapping.functor.map diagrams.monotonicity
  unit := congrArg mapping.functor.map diagrams.unit
  counit := congrArg mapping.functor.map diagrams.counit

def UniversalDiagrams.qualification (diagrams : UniversalDiagrams language route)
    (truth : RawHom (terminal original) language.proposition) :
    InternalPredicateQuantifier.Universal (SourceOperations.operations language truth)
      (classOf route.arrow) where
  operation := classOf diagrams.operation
  monotonicity := SourceOperations.monotonicity_comparison language truth _
    ((SourceOperations.powerMeet_read language truth route.target _ _).symm.trans diagrams.monotonicity)
  unit := by
    have read := (SourceOperations.powerMeet_read language truth route.target _ _).symm.trans diagrams.unit
    change (SourceOperations.functions language truth route.target).meet
      (classOf (language.precomposition route) ≫ classOf diagrams.operation) (𝟙 _) = 𝟙 _ at read
    rw [SourceOperations.precomposition_read] at read
    exact read
  counit := by
    have read := (SourceOperations.powerMeet_read language truth route.source _ _).symm.trans diagrams.counit
    change (SourceOperations.functions language truth route.source).meet (𝟙 _)
      (classOf diagrams.operation ≫ classOf (language.precomposition route)) =
        classOf diagrams.operation ≫ classOf (language.precomposition route) at read
    rw [SourceOperations.precomposition_read] at read
    exact read

def ExistentialDiagrams.qualification (diagrams : ExistentialDiagrams language route)
    (truth : RawHom (terminal original) language.proposition) :
    InternalPredicateExistential.Existential (SourceOperations.operations language truth)
      (classOf route.arrow) where
  operation := classOf diagrams.operation
  monotonicity := SourceOperations.monotonicity_comparison language truth _
    ((SourceOperations.powerMeet_read language truth route.target _ _).symm.trans diagrams.monotonicity)
  unit := by
    have read := (SourceOperations.powerMeet_read language truth route.source _ _).symm.trans diagrams.unit
    change (SourceOperations.functions language truth route.source).meet
      (classOf diagrams.operation ≫ classOf (language.precomposition route)) (𝟙 _) = 𝟙 _ at read
    rw [SourceOperations.precomposition_read] at read
    exact read
  counit := by
    have read := (SourceOperations.powerMeet_read language truth route.target _ _).symm.trans diagrams.counit
    change (SourceOperations.functions language truth route.target).meet (𝟙 _)
      (classOf (language.precomposition route) ≫ classOf diagrams.operation) =
        classOf (language.precomposition route) ≫ classOf diagrams.operation at read
    rw [SourceOperations.precomposition_read] at read
    exact read

variable (original language)

def stageUniversalDiagrams (route : Route original) :
    UniversalDiagrams (retainedSyntax original language) (SourceOperations.stageRoute original language route) where
  operation := named original language .universal route
  monotonicity := declared_law original language ⟨.universalMonotonicity, route⟩
  unit := declared_law original language ⟨.universalUnit, route⟩
  counit := declared_law original language ⟨.universalCounit, route⟩

def stageExistentialDiagrams (route : Route original) :
    ExistentialDiagrams (retainedSyntax original language) (SourceOperations.stageRoute original language route) where
  operation := named original language .existential route
  monotonicity := declared_law original language ⟨.existentialMonotonicity, route⟩
  unit := declared_law original language ⟨.existentialUnit, route⟩
  counit := declared_law original language ⟨.existentialCounit, route⟩

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureTranslation
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierDiagrams
import Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness

/-!
# Quantifier adjunctions at every actual closure arrow

Complete finite-stage proof recovery supplies the entire typed route. The
next stage's independently authored local diagrams transport into closure
with its single retained proposition and conjunction. Consequently every
raw route, and every arrow of the actual equation quotient, has both
quantifier adjunctions in every closure parameter context. Their complete
operation arrows are independent of the chosen finite-stage presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

theorem stage_route_map (depth : Nat) (route : Route (stages initial depth).presentation) :
    ((stages initial depth).mappedRoute route).translate (stageMap initial (depth + 1)) =
      route.translate (stageMap initial depth) := by
  apply Route.eq_of_read
  · exact (congrArg (stageMap initial (depth + 1)).object
      (SignatureMap.object_compose
        (arrowInclusion (stages initial depth).presentation (stages initial depth).language)
        (equationInclusion (stages initial depth).presentation (stages initial depth).language)
        route.source)).trans (whole_object_successor initial depth route.source)
  · exact (congrArg (stageMap initial (depth + 1)).object
      (SignatureMap.object_compose
        (arrowInclusion (stages initial depth).presentation (stages initial depth).language)
        (equationInclusion (stages initial depth).presentation (stages initial depth).language)
        route.target)).trans (whole_object_successor initial depth route.target)
  · exact (congrArg (arrowCode initial (depth + 1))
      (SignatureMap.arrow_code_compose
        (arrowInclusion (stages initial depth).presentation (stages initial depth).language)
        (equationInclusion (stages initial depth).presentation (stages initial depth).language)
        route.arrow)).trans (whole_arrow_successor initial depth route.arrow)

def stageUniversalDiagrams (depth : Nat) (route : Route (stages initial depth).presentation) :
    UniversalDiagrams (language initial) (route.translate (stageMap initial depth)) := by
  have actual := (RelativeClosedGeneratedQuantifier.stageUniversalDiagrams
    (stages initial depth).presentation (stages initial depth).language route).translate
      (stageMap initial (depth + 1))
  change UniversalDiagrams
    ((stages initial (depth + 1)).language.translate (stageMap initial (depth + 1)))
    (((stages initial depth).mappedRoute route).translate (stageMap initial (depth + 1))) at actual
  rw [language_retained, stage_route_map] at actual
  exact actual

def stageExistentialDiagrams (depth : Nat) (route : Route (stages initial depth).presentation) :
    ExistentialDiagrams (language initial) (route.translate (stageMap initial depth)) := by
  have actual := (RelativeClosedGeneratedQuantifier.stageExistentialDiagrams
    (stages initial depth).presentation (stages initial depth).language route).translate
      (stageMap initial (depth + 1))
  change ExistentialDiagrams
    ((stages initial (depth + 1)).language.translate (stageMap initial (depth + 1)))
    (((stages initial depth).mappedRoute route).translate (stageMap initial (depth + 1))) at actual
  rw [language_retained, stage_route_map] at actual
  exact actual

theorem universalDiagrams_nonempty (route : Route (signature initial)) :
    Nonempty (UniversalDiagrams (language initial) route) := by
  obtain ⟨depth, previous, read⟩ := route_finite initial route
  have actual := stageUniversalDiagrams initial depth previous
  rw [read] at actual
  exact ⟨actual⟩

theorem existentialDiagrams_nonempty (route : Route (signature initial)) :
    Nonempty (ExistentialDiagrams (language initial) route) := by
  obtain ⟨depth, previous, read⟩ := route_finite initial route
  have actual := stageExistentialDiagrams initial depth previous
  rw [read] at actual
  exact ⟨actual⟩

def universalDiagrams (route : Route (signature initial)) : UniversalDiagrams (language initial) route :=
  Classical.choice (universalDiagrams_nonempty initial route)

def existentialDiagrams (route : Route (signature initial)) : ExistentialDiagrams (language initial) route :=
  Classical.choice (existentialDiagrams_nonempty initial route)

def universalQualification (route : Route (signature initial)) :
    InternalPredicateQuantifier.Universal (operations initial) (classOf route.arrow) :=
  (universalDiagrams initial route).qualification (truth initial)

def existentialQualification (route : Route (signature initial)) :
    InternalPredicateExistential.Existential (operations initial) (classOf route.arrow) :=
  (existentialDiagrams initial route).qualification (truth initial)

def universal {source target : Object (signature initial)} (route : source ⟶ target) :
    InternalPredicateQuantifier.Universal (operations initial) route := by
  have actual := universalQualification initial ⟨source, target, representative route⟩
  change InternalPredicateQuantifier.Universal (operations initial) (classOf (representative route)) at actual
  simpa only [classOf_representative] using actual

def existential {source target : Object (signature initial)} (route : source ⟶ target) :
    InternalPredicateExistential.Existential (operations initial) route := by
  have actual := existentialQualification initial ⟨source, target, representative route⟩
  change InternalPredicateExistential.Existential (operations initial) (classOf (representative route)) at actual
  simpa only [classOf_representative] using actual

theorem universal_galois {source target : Object (signature initial)} (route : source ⟶ target)
    (context : Object (signature initial)) :
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power (operations initial) target) :=
      (InternalPredicateFunctionObject.operations (operations initial) target).semilattice
        (InternalPredicateFunctionObject.function_laws (operations initial) (laws initial) target) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power (operations initial) source) :=
      (InternalPredicateFunctionObject.operations (operations initial) source).semilattice
        (InternalPredicateFunctionObject.function_laws (operations initial) (laws initial) source) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power (operations initial) target =>
        predicate ≫ InternalPredicateQuantifier.precomposition (operations initial) route)
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power (operations initial) source =>
        predicate ≫ (universal initial route).operation) :=
  InternalPredicateQuantifier.Universal.adjunction (operations initial) (laws initial) route
    (universal initial route) context

theorem existential_galois {source target : Object (signature initial)} (route : source ⟶ target)
    (context : Object (signature initial)) :
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power (operations initial) source) :=
      (InternalPredicateFunctionObject.operations (operations initial) source).semilattice
        (InternalPredicateFunctionObject.function_laws (operations initial) (laws initial) source) context
    letI : SemilatticeInf (context ⟶ InternalPredicateFunctionObject.power (operations initial) target) :=
      (InternalPredicateFunctionObject.operations (operations initial) target).semilattice
        (InternalPredicateFunctionObject.function_laws (operations initial) (laws initial) target) context
    GaloisConnection
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power (operations initial) source =>
        predicate ≫ (existential initial route).operation)
      (fun predicate : context ⟶ InternalPredicateFunctionObject.power (operations initial) target =>
        predicate ≫ InternalPredicateQuantifier.precomposition (operations initial) route) :=
  InternalPredicateExistential.Existential.adjunction (operations initial) (laws initial) route
    (existential initial route) context

theorem universal_operation_unique {source target : Object (signature initial)} (route : source ⟶ target)
    (candidate : InternalPredicateQuantifier.Universal (operations initial) route) :
    candidate.operation = (universal initial route).operation :=
  InternalPredicateLogicalUniqueness.universal_operation_unique (operations initial) (laws initial)
    route candidate (universal initial route)

theorem existential_operation_unique {source target : Object (signature initial)} (route : source ⟶ target)
    (candidate : InternalPredicateExistential.Existential (operations initial) route) :
    candidate.operation = (existential initial route).operation :=
  InternalPredicateLogicalUniqueness.existential_operation_unique (operations initial) (laws initial)
    route candidate (existential initial route)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

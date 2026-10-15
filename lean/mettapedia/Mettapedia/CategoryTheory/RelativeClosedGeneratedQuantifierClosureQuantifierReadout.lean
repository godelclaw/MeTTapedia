import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureNativeInterpretation

/-!
# Complete native readout of the closure's unique quantifier arrows

Changing the retained predicate or route presentation transports the local
diagrams while keeping their whole authored operator code. The actual
finite-stage named operator therefore has its independently supplied native
classifier readout. Complete-operation uniqueness compares it with the
closure quantifier, retaining the full mapped arrow and both endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory Iteration

universe k w z p
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {original : Signature (C := C) (symbols := symbols)}

def UniversalDiagrams.retype {before after : PredicateSyntax original} {first second : Route original}
    (supplied : UniversalDiagrams before first) (languages : before = after) (routes : first = second) :
    UniversalDiagrams after second := by
  cases languages
  cases routes
  exact supplied

theorem UniversalDiagrams.retype_code {before after : PredicateSyntax original} {first second : Route original}
    (supplied : UniversalDiagrams before first) (languages : before = after) (routes : first = second) :
    (supplied.retype languages routes).operation.code = supplied.operation.code := by
  cases languages
  cases routes
  rfl

def ExistentialDiagrams.retype {before after : PredicateSyntax original} {first second : Route original}
    (supplied : ExistentialDiagrams before first) (languages : before = after) (routes : first = second) :
    ExistentialDiagrams after second := by
  cases languages
  cases routes
  exact supplied

theorem ExistentialDiagrams.retype_code {before after : PredicateSyntax original} {first second : Route original}
    (supplied : ExistentialDiagrams before first) (languages : before = after) (routes : first = second) :
    (supplied.retype languages routes).operation.code = supplied.operation.code := by
  cases languages
  cases routes
  rfl

namespace Closure

variable (stage : Stage C)

def namedUniversalDiagrams (depth : Nat) (route : Route (stages stage depth).presentation) :
    UniversalDiagrams (language stage) (route.translate (stageMap stage depth)) :=
  ((RelativeClosedGeneratedQuantifier.stageUniversalDiagrams
    (stages stage depth).presentation (stages stage depth).language route).translate
      (stageMap stage (depth + 1))).retype
        (language_retained stage (depth + 1)) (stage_route_map stage depth route)

def namedExistentialDiagrams (depth : Nat) (route : Route (stages stage depth).presentation) :
    ExistentialDiagrams (language stage) (route.translate (stageMap stage depth)) :=
  ((RelativeClosedGeneratedQuantifier.stageExistentialDiagrams
    (stages stage depth).presentation (stages stage depth).language route).translate
      (stageMap stage (depth + 1))).retype
        (language_retained stage (depth + 1)) (stage_route_map stage depth route)

theorem named_universal_code (depth : Nat) (route : Route (stages stage depth).presentation) :
    (namedUniversalDiagrams stage depth route).operation.code =
      arrowCode stage (depth + 1) ((stages stage depth).quantifierRoute .universal route).arrow.code :=
  UniversalDiagrams.retype_code _ _ _

theorem named_existential_code (depth : Nat) (route : Route (stages stage depth).presentation) :
    (namedExistentialDiagrams stage depth route).operation.code =
      arrowCode stage (depth + 1) ((stages stage depth).quantifierRoute .existential route).arrow.code :=
  ExistentialDiagrams.retype_code _ _ _

variable {stage}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D}
variable (initial : NativeModel doctrine stage)

def nativeOperatorValue (route : Route (signature stage))
    (operation : InternalPredicateFunctionObject.power (operations stage) route.source ⟶
      InternalPredicateFunctionObject.power (operations stage) route.target) :
    RelativeClosedSyntax.Interpretation.ArrowValue D :=
  ⟨(nativeDiagram initial).obj (InternalPredicateFunctionObject.power (operations stage) route.source),
    (nativeDiagram initial).obj (InternalPredicateFunctionObject.power (operations stage) route.target),
    (nativeDiagram initial).map operation⟩

theorem named_universal_native_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (nativeModels initial depth).meanings route.arrow arrow) :
    (nativeAssignment initial).evaluateArrow (namedUniversalDiagrams stage depth route).operation.code =
      some (NativeMeaning.operationValue doctrine .universal ⟨source, target, arrow⟩) :=
  (congrArg (nativeAssignment initial).evaluateArrow (named_universal_code stage depth route)).trans
    ((native_arrow_readout initial (depth + 1)
      ((stages stage depth).quantifierRoute .universal route).arrow.code).trans
        ((nativeModels initial depth).new_operator_readout .universal route arrow reading))

theorem named_existential_native_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (nativeModels initial depth).meanings route.arrow arrow) :
    (nativeAssignment initial).evaluateArrow (namedExistentialDiagrams stage depth route).operation.code =
      some (NativeMeaning.operationValue doctrine .existential ⟨source, target, arrow⟩) :=
  (congrArg (nativeAssignment initial).evaluateArrow (named_existential_code stage depth route)).trans
    ((native_arrow_readout initial (depth + 1)
      ((stages stage depth).quantifierRoute .existential route).arrow.code).trans
        ((nativeModels initial depth).new_operator_readout .existential route arrow reading))

theorem unique_universal_native_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (nativeModels initial depth).meanings route.arrow arrow) :
    nativeOperatorValue initial (route.translate (stageMap stage depth))
      (universal stage (classOf (route.translate (stageMap stage depth)).arrow)).operation =
        NativeMeaning.operationValue doctrine .universal ⟨source, target, arrow⟩ := by
  have unique := universal_operation_unique stage (classOf (route.translate (stageMap stage depth)).arrow)
    ((namedUniversalDiagrams stage depth route).qualification (truth stage))
  have supplied := Option.some.inj
    ((native_complete_readout initial (namedUniversalDiagrams stage depth route).operation).symm.trans
      (named_universal_native_read initial depth route arrow reading))
  exact (congrArg (nativeOperatorValue initial (route.translate (stageMap stage depth))) unique.symm).trans supplied

theorem unique_existential_native_read (depth : Nat) (route : Route (stages stage depth).presentation)
    {source target : D} (arrow : source ⟶ target)
    (reading : RawInterpretation.Reads (nativeModels initial depth).meanings route.arrow arrow) :
    nativeOperatorValue initial (route.translate (stageMap stage depth))
      (existential stage (classOf (route.translate (stageMap stage depth)).arrow)).operation =
        NativeMeaning.operationValue doctrine .existential ⟨source, target, arrow⟩ := by
  have unique := existential_operation_unique stage (classOf (route.translate (stageMap stage depth)).arrow)
    ((namedExistentialDiagrams stage depth route).qualification (truth stage))
  have supplied := Option.some.inj
    ((native_complete_readout initial (namedExistentialDiagrams stage depth route).operation).symm.trans
      (named_existential_native_read initial depth route arrow reading))
  exact (congrArg (nativeOperatorValue initial (route.translate (stageMap stage depth))) unique.symm).trans supplied

end Closure

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier

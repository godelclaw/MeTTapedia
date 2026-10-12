import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureNativeAssignment
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureQuantifiers
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationClosed

/-!
# Earned independent classifier interpretation of quantifier closure

Every local closure header and equation is read through its actual finite
authored stage. Exact assignment and parser restrictions earn the final
realization, the whole quotient functor and its complete stage restrictions.
Truth, conjunction and the single proposition retain the initial meanings.
Finite-limit preservation holds at independent target size levels; the
canonical closed-map comparison uses the explicit common hom universe.
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
variable (initial : NativeModel doctrine stage)

theorem nativeRealization :
    RelativeClosedSyntax.Interpretation.Realization (signature stage) (nativeAssignment initial) where
  source
    | .inl origin =>
        (native_object_readout initial 0 (stage.presentation.source origin)).trans (initial.admitted.source origin)
    | .inr ⟨depth, origin⟩ =>
        (native_object_readout initial (depth + 1)
          ((stages stage (depth + 1)).presentation.source (.inr origin))).trans
            ((nativeModels initial (depth + 1)).admitted.source (.inr origin))
  target
    | .inl origin =>
        (native_object_readout initial 0 (stage.presentation.target origin)).trans (initial.admitted.target origin)
    | .inr ⟨depth, origin⟩ =>
        (native_object_readout initial (depth + 1)
          ((stages stage (depth + 1)).presentation.target (.inr origin))).trans
            ((nativeModels initial (depth + 1)).admitted.target (.inr origin))
  equation
    | .inl origin => by
        obtain ⟨value, first, last, before, after⟩ := initial.admitted.equation origin
        exact ⟨value,
          (native_object_readout initial 0 (stage.presentation.equationSource origin)).trans first,
          (native_object_readout initial 0 (stage.presentation.equationTarget origin)).trans last,
          (native_arrow_readout initial 0 (stage.presentation.left origin)).trans before,
          (native_arrow_readout initial 0 (stage.presentation.right origin)).trans after⟩
    | .inr ⟨depth, origin⟩ => by
        obtain ⟨value, first, last, before, after⟩ :=
          (nativeModels initial (depth + 1)).admitted.equation (.inr origin)
        exact ⟨value,
          (native_object_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.equationSource (.inr origin))).trans first,
          (native_object_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.equationTarget (.inr origin))).trans last,
          (native_arrow_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.left (.inr origin))).trans before,
          (native_arrow_readout initial (depth + 1)
            ((stages stage (depth + 1)).presentation.right (.inr origin))).trans after⟩

def completedStage (original : Stage C) : Stage C where
  symbols := symbols original
  presentation := signature original
  formed := headers original
  language := language original
  truth := truth original
  laws := laws original

def nativeModel : NativeModel doctrine (completedStage stage) where
  meanings := nativeAssignment initial
  admitted := nativeRealization initial
  proposition := (native_object_readout initial 0 stage.language.proposition.code).trans initial.proposition
  conjunction := (native_arrow_readout initial 0 stage.language.conjunction.code).trans initial.conjunction
  truth := (native_arrow_readout initial 0 stage.truth.code).trans initial.truth

def nativeDiagram : Object (signature stage) ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor (nativeAssignment initial) (nativeRealization initial)

instance nativeDiagram_preservesFiniteLimits : PreservesFiniteLimits (nativeDiagram initial) :=
  RelativeClosedSyntax.Interpretation.functor_preservesFiniteLimits
    (nativeAssignment initial) (nativeRealization initial)

theorem native_whole_stage_restriction (depth : Nat) :
    (stageMap stage depth).functor ⋙ nativeDiagram initial = stageDiagram initial depth := by
  change (stageMap stage depth).functor ⋙
    RelativeClosedSyntax.Interpretation.functor (nativeAssignment initial) (nativeRealization initial) =
      RelativeClosedSyntax.Interpretation.functor
        (nativeModels initial depth).meanings (nativeModels initial depth).admitted
  have complete := (stageMap stage depth).functor_precompose
    (nativeAssignment initial) (nativeRealization initial)
  simpa only [native_assignment_restriction] using complete

theorem native_complete_readout {source target : Object (signature stage)} (arrow : RawHom source target) :
    (nativeAssignment initial).evaluateArrow arrow.code =
      some ⟨(nativeDiagram initial).obj source, (nativeDiagram initial).obj target,
        (nativeDiagram initial).map (classOf arrow)⟩ :=
  RelativeClosedSyntax.Interpretation.functor_complete_readout
    (nativeAssignment initial) (nativeRealization initial) arrow

theorem native_truth_readout :
    RawInterpretation.Reads (nativeAssignment initial) (truth stage)
      (HigherOrderInternalPredicateObject.operations doctrine).truth :=
  (nativeModel initial).truth

theorem native_conjunction_readout :
    RawInterpretation.Reads (nativeAssignment initial) (language stage).conjunction
      (HigherOrderInternalPredicateObject.operations doctrine).conjunction :=
  (nativeModel initial).conjunction

theorem native_proposition_readout :
    RawInterpretation.ObjectReads (nativeAssignment initial) (language stage).proposition
      (HigherOrderInternalPredicateObject.operations doctrine).proposition :=
  (nativeModel initial).proposition

section CommonHomUniverse

variable {H : Type w} [Category.{k} H]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable {higher : PredicateDoctrine.HigherOrder.{w,k,p} H}

def nativeTheoryMap (native : NativeModel higher stage) :
    Mettapedia.GSLT.Core.LambdaTheoryMap (theory stage)
      (Mettapedia.GSLT.Core.LambdaTheory.ofCategory H) where
  functor := nativeDiagram native
  preservesFiniteLimits := nativeDiagram_preservesFiniteLimits native
  preservesExponentials := RelativeClosedSyntax.Interpretation.functor_closed
    (nativeAssignment native) (nativeRealization native)

end CommonHomUniverse

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

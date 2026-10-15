import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierClosureSignature

/-!
# Actual finite-stage maps into quantifier closure

Local declaration comparisons construct a genuine signature map from each
stage. Those maps transport every generated rule and the independently
formed headers. The merged category therefore has earned finite limits and
function objects, and each stage inclusion is a finite-limit and closed map.
Whole source objects and arrows agree along the successor inclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

open _root_.CategoryTheory
open RelativeClosedSyntax GeneratedCategory Iteration

universe k
variable {C : Type k} [Category.{k} C] (initial : Stage C)

def stageMap (depth : Nat) : SignatureMap (stages initial depth).presentation (signature initial) where
  base := Functor.id C
  objects := objects initial depth
  arrows := arrows initial depth
  equations := equations initial depth
  source := source_read initial depth
  target := target_read initial depth
  equationSource := equationSource_read initial depth
  equationTarget := equationTarget_read initial depth
  left := left_read initial depth
  right := right_read initial depth

def headers : HeaderFormation (signature initial) where
  source
    | .inl origin => (stageMap initial 0).derivation (initial.formed.source origin)
    | .inr ⟨depth, origin⟩ =>
        (stageMap initial (depth + 1)).derivation ((stages initial (depth + 1)).formed.source (.inr origin))
  target
    | .inl origin => (stageMap initial 0).derivation (initial.formed.target origin)
    | .inr ⟨depth, origin⟩ =>
        (stageMap initial (depth + 1)).derivation ((stages initial (depth + 1)).formed.target (.inr origin))
  left
    | .inl origin => (stageMap initial 0).derivation (initial.formed.left origin)
    | .inr ⟨depth, origin⟩ =>
        (stageMap initial (depth + 1)).derivation ((stages initial (depth + 1)).formed.left (.inr origin))
  right
    | .inl origin => (stageMap initial 0).derivation (initial.formed.right origin)
    | .inr ⟨depth, origin⟩ =>
        (stageMap initial (depth + 1)).derivation ((stages initial (depth + 1)).formed.right (.inr origin))

def theory : Mettapedia.GSLT.Core.LambdaTheory.{k,k} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (signature initial))

def theoryMap (depth : Nat) : Mettapedia.GSLT.Core.LambdaTheoryMap
    (Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (stages initial depth).presentation))
    (theory initial) where
  functor := (stageMap initial depth).functor
  preservesFiniteLimits := SignatureMap.functor_preservesFiniteLimits (stageMap initial depth)
  preservesExponentials := SignatureMap.functor_closed (stageMap initial depth)

theorem whole_object_successor (depth : Nat) (object : Object (stages initial depth).presentation) :
    (stageMap initial (depth + 1)).object ((stages initial depth).inclusion.object object) =
      (stageMap initial depth).object object :=
  Object.ext (objectCode_step initial depth object.code)

theorem whole_arrow_successor (depth : Nat)
    {first last : Object (stages initial depth).presentation} (arrow : RawHom first last) :
    ((stageMap initial (depth + 1)).rawArrow ((stages initial depth).inclusion.rawArrow arrow)).code =
      ((stageMap initial depth).rawArrow arrow).code :=
  arrowCode_step initial depth arrow.code

theorem initial_objectCode_read (depth : Nat) (code : ObjectCode C initial.symbols) :
    objectCode initial depth
      (code.map (initialInclusion initial depth).base
        (initialInclusion initial depth).objects (initialInclusion initial depth).arrows) =
      objectCode initial 0 code := by
  induction depth with
  | zero => exact congrArg (objectCode initial 0) (ObjectCode.map_identity code)
  | succ depth inductionHypothesis =>
      have decomposed := ObjectCode.map_compose (initialInclusion initial depth).base
        (stages initial depth).inclusion.base (initialInclusion initial depth).objects
        (stages initial depth).inclusion.objects (initialInclusion initial depth).arrows
        (stages initial depth).inclusion.arrows code
      exact (congrArg (objectCode initial (depth + 1)) decomposed.symm).trans
        ((objectCode_step initial depth _).trans inductionHypothesis)

theorem initial_arrowCode_read (depth : Nat) (code : ArrowCode C initial.symbols) :
    arrowCode initial depth
      (code.map (initialInclusion initial depth).base
        (initialInclusion initial depth).objects (initialInclusion initial depth).arrows) =
      arrowCode initial 0 code := by
  induction depth with
  | zero => exact congrArg (arrowCode initial 0) (ArrowCode.map_identity code)
  | succ depth inductionHypothesis =>
      have decomposed := ArrowCode.map_compose (initialInclusion initial depth).base
        (stages initial depth).inclusion.base (initialInclusion initial depth).objects
        (stages initial depth).inclusion.objects (initialInclusion initial depth).arrows
        (stages initial depth).inclusion.arrows code
      exact (congrArg (arrowCode initial (depth + 1)) decomposed.symm).trans
        ((arrowCode_step initial depth _).trans inductionHypothesis)

def language : PredicateSyntax (signature initial) := initial.language.translate (stageMap initial 0)

def truth : RawHom (terminal (signature initial)) (language initial).proposition :=
  (stageMap initial 0).rawArrow initial.truth

def operations := SourceOperations.operations (language initial) (truth initial)

theorem laws : (operations initial).Laws :=
  SourceOperations.translated_laws initial.language initial.truth (stageMap initial 0) initial.laws

theorem proposition_retained (depth : Nat) :
    (stageMap initial depth).object (stages initial depth).language.proposition =
      (language initial).proposition := by
  apply Object.ext
  exact (congrArg (objectCode initial depth)
    (congrArg Object.code (Iteration.proposition_retained initial depth))).trans
      (initial_objectCode_read initial depth initial.language.proposition.code)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Closure

import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgramComparison

/-!+# Universal correspondence for quantified program maps

Both the independently supplied target reduction relation and the local
predicate declarations participate in the same universal construction.
Restriction remembers the program and complete event arrow. Every arbitrary
candidate extending a supplied local map has a canonical compatible
comparison with its generated extension. The comparison is unique when
its complete base reading is fixed; no equality of raw context objects is
required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedQuantified RelativeClosedQuantifiedRuleFrames

universe k
variable {source target : Theory.{k,k}}
variable {predicates : InternalConjunctiveObject.Operations source.closed.Obj} {laws : predicates.Laws}
variable {quantified : InternalPredicateQuantifiedObject.Operations target.closed.Obj}

structure Comparison (first second : Supplied source target predicates laws quantified) where
  declarations : ConjunctiveClosedTheory.MapIso first.declarations second.declarations
  program : declarations.comparison.hom.app source.program ≫ second.program.hom = first.program.hom

namespace Comparison

variable {first second third : Supplied source target predicates laws quantified}

def original (comparison : Comparison first second) :
    ProgramReductionTheoryIsoClasses.MapIso first.original second.original where
  comparison := comparison.declarations.comparison
  program := comparison.program

theorem event_reading (comparison : Comparison first second) :
    comparison.declarations.comparison.hom.app source.Event ≫ second.event = first.event :=
  comparison.original.reduction_square

def refl (mapping : Supplied source target predicates laws quantified) : Comparison mapping mapping where
  declarations := ConjunctiveClosedTheory.MapIso.refl mapping.declarations
  program := Category.id_comp _

def symm (comparison : Comparison first second) : Comparison second first where
  declarations := comparison.declarations.symm
  program := comparison.original.symm.program

def trans (before : Comparison first second) (after : Comparison second third) : Comparison first third where
  declarations := before.declarations.trans after.declarations
  program := (before.original.trans after.original).program

theorem ext (before after : Comparison first second)
    (same : before.declarations.comparison = after.declarations.comparison) : before = after := by
  cases before with
  | mk before beforeProgram =>
    cases after with
    | mk after afterProgram =>
      cases before with
      | mk before beforeProposition =>
        cases after with
        | mk after afterProposition =>
          dsimp only at same
          cases same
          rfl

end Comparison

abbrev Generated := Supplied (generatedTheory source predicates laws) target
  (freeObject (conjunctive source predicates laws)).operations.predicates
  (freeObject (conjunctive source predicates laws)).operations.laws quantified

def extend (mapping : Supplied source target predicates laws quantified) :
    Generated (source := source) (target := target) (predicates := predicates)
      (laws := laws) (quantified := quantified) where
  declarations := mapping.extension
  program := mapping.extendedProgram
  event := mapping.extendedEvent
  sourceEquation := mapping.extended_source
  targetEquation := mapping.extended_target

def restrict (candidate : Generated (source := source) (target := target)
    (predicates := predicates) (laws := laws) (quantified := quantified)) :
    Supplied source target predicates laws quantified where
  declarations := Extension.restrictMap candidate.declarations
  program := (Map.compose (generatedInclusion source predicates laws) candidate.original).program
  event := (Map.compose (generatedInclusion source predicates laws) candidate.original).reduction
  sourceEquation := (Map.compose (generatedInclusion source predicates laws) candidate.original).source
  targetEquation := (Map.compose (generatedInclusion source predicates laws) candidate.original).target

def restrict_extend (mapping : Supplied source target predicates laws quantified) :
    Comparison (restrict (extend mapping)) mapping where
  declarations := mapping.baseComparison
  program := mapping.restrictionComparison.program

def completeComparison (mapping : Supplied source target predicates laws quantified)
    (candidate : Generated (source := source) (target := target) (predicates := predicates)
      (laws := laws) (quantified := quantified))
    (localComparison : Comparison (restrict candidate) mapping) :
    Comparison candidate (extend mapping) where
  declarations := Universal.completeComparison mapping.declarations candidate.declarations
    localComparison.declarations
  program := by
    change (Universal.completeComparison mapping.declarations candidate.declarations
      localComparison.declarations).comparison.hom.app
        ((Extension.unitMap (conjunctive source predicates laws)).functor.obj source.program) ≫
          (mapping.baseComparison.comparison.hom.app source.program ≫ mapping.program.hom) = candidate.program.hom
    have localSquare := localComparison.program
    change localComparison.declarations.comparison.hom.app source.program ≫ mapping.program.hom =
      candidate.declarations.functor.map
        (𝟙 ((Extension.unitMap (conjunctive source predicates laws)).functor.obj source.program)) ≫
          candidate.program.hom at localSquare
    have localProgram : localComparison.declarations.comparison.hom.app source.program ≫
        mapping.program.hom = candidate.program.hom := by
      simpa only [candidate.declarations.functor.map_id, Category.id_comp] using localSquare
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun arrow => arrow ≫ mapping.program.hom)
        (ProgramComparison.complete_base_component mapping.declarations candidate.declarations
          localComparison.declarations source.program)).trans localProgram)

theorem complete_base_reading (mapping : Supplied source target predicates laws quantified)
    (candidate : Generated (source := source) (target := target) (predicates := predicates)
      (laws := laws) (quantified := quantified))
    (localComparison : Comparison (restrict candidate) mapping) (object : source.closed.Obj) :
    (completeComparison mapping candidate localComparison).declarations.comparison.hom.app
        ((Extension.unitMap (conjunctive source predicates laws)).functor.obj object) ≫
      mapping.baseComparison.comparison.hom.app object =
        localComparison.declarations.comparison.hom.app object :=
  ProgramComparison.complete_base_component mapping.declarations candidate.declarations
    localComparison.declarations object

theorem comparison_unique (mapping : Supplied source target predicates laws quantified)
    (candidate : Generated (source := source) (target := target) (predicates := predicates)
      (laws := laws) (quantified := quantified))
    (localComparison : Comparison (restrict candidate) mapping)
    (other : Comparison candidate (extend mapping))
    (base : ∀ object : source.closed.Obj,
      other.declarations.comparison.hom.app
        ((Extension.unitMap (conjunctive source predicates laws)).functor.obj object) ≫
          mapping.baseComparison.comparison.hom.app object =
            localComparison.declarations.comparison.hom.app object) :
    other = completeComparison mapping candidate localComparison :=
  Comparison.ext other (completeComparison mapping candidate localComparison)
    (ProgramComparison.comparison_unique mapping.declarations candidate.declarations
      localComparison.declarations other.declarations.comparison base)

def extend_restrict (candidate : Generated (source := source) (target := target)
    (predicates := predicates) (laws := laws) (quantified := quantified)) :
    Comparison candidate (extend (restrict candidate)) :=
  completeComparison (restrict candidate) candidate (Comparison.refl _)

def restrictComparison
    {first second : Generated (source := source) (target := target) (predicates := predicates)
      (laws := laws) (quantified := quantified)}
    (comparison : Comparison first second) : Comparison (restrict first) (restrict second) where
  declarations := ConjunctiveClosedTheory.MapIso.precompose
    (Extension.unitMap (conjunctive source predicates laws)) comparison.declarations
  program := (ProgramReductionTheoryIsoClasses.MapIso.precompose
    (generatedInclusion source predicates laws) comparison.original).program

def extendComparison {first second : Supplied source target predicates laws quantified}
    (comparison : Comparison first second) : Comparison (extend first) (extend second) :=
  completeComparison second (extend first) ((restrict_extend first).trans comparison)

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramMaps

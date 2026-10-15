import Mettapedia.CategoryTheory.QuantifiedProgramTheory
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedProgramUniversality

/-!
# Complete program hom equivalence for quantified completion

The existing category of conjunctive program theories is used unchanged.
Its maps are compared with the actual independently supplied maps of the
program-extension construction. Both hom roundtrips preserve the complete
predicate, program and event data, through compatible natural isomorphisms.
Restriction is actual composition with the installed program theory unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open RelativeClosedQuantifiedProgramMaps RelativeClosedQuantifiedRuleFrames

universe k

def freeObject (source : ConjunctiveProgramTheory.{k}) : QuantifiedProgramTheory.{k} where
  programTheory := generatedTheory source.programTheory source.operations source.laws
  operations := (RelativeClosedQuantified.freeObject source.conjunctive).operations

def unitMap (source : ConjunctiveProgramTheory.{k}) :
    ConjunctiveProgramTheory.Map source (freeObject source).conjunctive where
  conjunctive := RelativeClosedQuantified.Extension.unitMap source.conjunctive
  program := (generatedInclusion source.programTheory source.operations source.laws).program
  reduction := (generatedInclusion source.programTheory source.operations source.laws).reduction
  source := (generatedInclusion source.programTheory source.operations source.laws).source
  target := (generatedInclusion source.programTheory source.operations source.laws).target

namespace HomEquivalence

variable (source : ConjunctiveProgramTheory.{k}) (target : QuantifiedProgramTheory.{k})

abbrev Local := Supplied source.programTheory target.programTheory source.operations source.laws target.operations

def localMap (mapping : ConjunctiveProgramTheory.Map source target.conjunctive) : Local source target where
  declarations := mapping.conjunctive
  program := mapping.program
  event := mapping.reduction
  sourceEquation := mapping.source
  targetEquation := mapping.target

def categoryMap (mapping : Local source target) : ConjunctiveProgramTheory.Map source target.conjunctive where
  conjunctive := mapping.declarations
  program := mapping.program
  reduction := mapping.event
  source := mapping.sourceEquation
  target := mapping.targetEquation

def categoryComparison {first second : Local source target} (comparison : Comparison first second) :
    ConjunctiveProgramTheory.MapIso (categoryMap source target first) (categoryMap source target second) where
  conjunctive := comparison.declarations
  program := comparison.program

def extension (mapping : ConjunctiveProgramTheory.Map source target.conjunctive) :
    QuantifiedProgramTheory.Map (freeObject source) target :=
  categoryMap (freeObject source).conjunctive target (extend (localMap source target mapping))

def restriction (mapping : QuantifiedProgramTheory.Map (freeObject source) target) :
    ConjunctiveProgramTheory.Map source target.conjunctive :=
  ConjunctiveProgramTheory.Map.compose (unitMap source) mapping

def extension_restriction (mapping : ConjunctiveProgramTheory.Map source target.conjunctive) :
    ConjunctiveProgramTheory.MapIso (restriction source target (extension source target mapping)) mapping :=
  categoryComparison source target (restrict_extend (localMap source target mapping))

def completeComparison (mapping : ConjunctiveProgramTheory.Map source target.conjunctive)
    (candidate : QuantifiedProgramTheory.Map (freeObject source) target)
    (localComparison : ConjunctiveProgramTheory.MapIso (restriction source target candidate) mapping) :
    QuantifiedProgramTheory.MapIso candidate (extension source target mapping) :=
  categoryComparison (freeObject source).conjunctive target
    (RelativeClosedQuantifiedProgramMaps.completeComparison (localMap source target mapping)
      (localMap (freeObject source).conjunctive target candidate)
      { declarations := localComparison.conjunctive, program := localComparison.program })

theorem unique_comparison (mapping : ConjunctiveProgramTheory.Map source target.conjunctive)
    (candidate : QuantifiedProgramTheory.Map (freeObject source) target)
    (localComparison : ConjunctiveProgramTheory.MapIso (restriction source target candidate) mapping) :
    ∃! comparison : QuantifiedProgramTheory.MapIso candidate (extension source target mapping),
      ∀ object : source.closed.Obj,
        comparison.comparison.hom.app ((unitMap source).functor.obj object) ≫
          (extension_restriction source target mapping).comparison.hom.app object =
            localComparison.comparison.hom.app object := by
  refine ⟨completeComparison source target mapping candidate localComparison, ?_, ?_⟩
  · intro object
    exact RelativeClosedQuantifiedProgramMaps.complete_base_reading (localMap source target mapping)
      (localMap (freeObject source).conjunctive target candidate)
      { declarations := localComparison.conjunctive, program := localComparison.program } object
  · intro other base
    exact congrArg (categoryComparison (freeObject source).conjunctive target)
      (RelativeClosedQuantifiedProgramMaps.comparison_unique (localMap source target mapping)
        (localMap (freeObject source).conjunctive target candidate)
        { declarations := localComparison.conjunctive, program := localComparison.program }
        { declarations := other.conjunctive, program := other.program } base)

def mapIsoOfRestriction {first second : QuantifiedProgramTheory.Map (freeObject source) target}
    (comparison : ConjunctiveProgramTheory.MapIso (restriction source target first)
      (restriction source target second)) : QuantifiedProgramTheory.MapIso first second :=
  (completeComparison source target (restriction source target second) first comparison).trans
    (completeComparison source target (restriction source target second) second
      (ConjunctiveProgramTheory.MapIso.refl _)).symm

def restriction_comparison {first second : QuantifiedProgramTheory.Map (freeObject source) target}
    (comparison : QuantifiedProgramTheory.MapIso first second) :
    ConjunctiveProgramTheory.MapIso (restriction source target first) (restriction source target second) :=
  ConjunctiveProgramTheory.MapIso.precompose (unitMap source) comparison

def extension_comparison {first second : ConjunctiveProgramTheory.Map source target.conjunctive}
    (comparison : ConjunctiveProgramTheory.MapIso first second) :
    QuantifiedProgramTheory.MapIso (extension source target first) (extension source target second) :=
  mapIsoOfRestriction source target ((extension_restriction source target first).trans
    (comparison.trans (extension_restriction source target second).symm))

def restrict : (freeObject source ⟶ target) → (source ⟶ target.conjunctive) :=
  Quotient.map (restriction source target) (fun _ _ ⟨comparison⟩ =>
    ⟨restriction_comparison source target comparison⟩)

def extend : (source ⟶ target.conjunctive) → (freeObject source ⟶ target) :=
  Quotient.map (extension source target) (fun _ _ ⟨comparison⟩ =>
    ⟨extension_comparison source target comparison⟩)

theorem restrict_classOf (mapping : QuantifiedProgramTheory.Map (freeObject source) target) :
    restrict source target (QuantifiedProgramTheory.classOf mapping) =
      ConjunctiveProgramTheory.classOf (restriction source target mapping) := rfl

theorem extend_classOf (mapping : ConjunctiveProgramTheory.Map source target.conjunctive) :
    extend source target (ConjunctiveProgramTheory.classOf mapping) =
      QuantifiedProgramTheory.classOf (extension source target mapping) := rfl

theorem restrict_extend (mapping : source ⟶ target.conjunctive) :
    restrict source target (extend source target mapping) = mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  exact Quotient.sound ⟨extension_restriction source target mapping⟩

theorem restrict_injective : Function.Injective (restrict source target) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun first second same => ?_
  obtain ⟨comparison⟩ := (ConjunctiveProgramTheory.classOf_equal_iff
    (restriction source target first) (restriction source target second)).mp same
  exact Quotient.sound ⟨mapIsoOfRestriction source target comparison⟩

theorem extend_restrict (mapping : freeObject source ⟶ target) :
    extend source target (restrict source target mapping) = mapping :=
  restrict_injective source target (restrict_extend source target (restrict source target mapping))

def homEquiv : (freeObject source ⟶ target) ≃ (source ⟶ target.conjunctive) where
  toFun := restrict source target
  invFun := extend source target
  left_inv := extend_restrict source target
  right_inv := restrict_extend source target

theorem restrict_as_base_composition (mapping : freeObject source ⟶ target) :
    restrict source target mapping =
      ConjunctiveProgramTheory.classOf (unitMap source) ≫ QuantifiedProgramTheory.forget.map mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  rfl

theorem restrict_postcompose {later : QuantifiedProgramTheory.{k}}
    (before : freeObject source ⟶ target) (after : target ⟶ later) :
    restrict source later (before ≫ after) =
      restrict source target before ≫ QuantifiedProgramTheory.forget.map after := by
  rw [restrict_as_base_composition, restrict_as_base_composition,
    QuantifiedProgramTheory.forget.map_comp, Category.assoc]

end HomEquivalence

end Mettapedia.CategoryTheory.RelativeClosedQuantifiedProgram

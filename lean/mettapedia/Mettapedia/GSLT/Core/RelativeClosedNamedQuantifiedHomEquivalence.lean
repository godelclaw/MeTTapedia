import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedBareComparison
import Mettapedia.CategoryTheory.QuantifiedImplicativeProgramForget

/-!
# Bare program maps classify the complete named logical extension

The complete comparisons descend extension and restriction to compatible
map classes. Both roundtrips are proved from the earned concrete program
comparisons. No primitive-admission premise is supplied by the caller.
The hom correspondence retains arbitrary original theories, chosen modal
and constructor origins, and independently supplied complete targets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedHomEquivalence

open _root_.CategoryTheory
open Mettapedia.CategoryTheory ProgramReductionTheory
open RelativeClosedNamedQuantifiedPresentation RelativeClosedNamedQuantifiedRestriction

universe k
variable (source : Theory.{k,k}) {Index Origins : Type k}
variable (selected : Index → RelativeClosedPositionedModalPresentation.Selection source)
variable (constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source)

def freeObject : QuantifiedImplicativeProgramTheory.{k} where
  quantified := completed source selected constructors
  implication := completeImplication source selected constructors

variable (target : QuantifiedImplicativeProgramTheory.{k})

def restriction (mapping : QuantifiedImplicativeProgramTheory.Map (freeObject source selected constructors) target) :
    Map source target.quantified.programTheory :=
  original target mapping

def extension (mapping : Map source target.quantified.programTheory) :
    QuantifiedImplicativeProgramTheory.Map (freeObject source selected constructors) target :=
  extendOriginal selected constructors target mapping

def restrictionComparison {first second : QuantifiedImplicativeProgramTheory.Map
    (freeObject source selected constructors) target}
    (comparison : QuantifiedImplicativeProgramTheory.MapIso first second) :
    ProgramReductionTheoryIsoClasses.MapIso
      (restriction source selected constructors target first)
      (restriction source selected constructors target second) :=
  ProgramReductionTheoryIsoClasses.MapIso.precompose (programInclusion source selected constructors)
    comparison.underlying

def mapIsoOfRestriction {first second : QuantifiedImplicativeProgramTheory.Map
    (freeObject source selected constructors) target}
    (comparison : ProgramReductionTheoryIsoClasses.MapIso
      (restriction source selected constructors target first)
      (restriction source selected constructors target second)) :
    QuantifiedImplicativeProgramTheory.MapIso first second :=
  (completeComparisonWithOriginal target first (restriction source selected constructors target second) comparison).trans
    (completeComparison target second).symm

def restrict : (freeObject source selected constructors ⟶ target) →
    (ProgramReductionTheoryIsoClasses.of source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :=
  Quotient.map (restriction source selected constructors target) (fun _ _ ⟨comparison⟩ =>
    ⟨restrictionComparison source selected constructors target comparison⟩)

def extend : (ProgramReductionTheoryIsoClasses.of source ⟶
    QuantifiedImplicativeProgramTheory.forgetProgram.obj target) →
    (freeObject source selected constructors ⟶ target) :=
  Quotient.map (extension source selected constructors target) (fun _ _ ⟨comparison⟩ =>
    ⟨extensionComparison (selected := selected) (constructors := constructors) target comparison⟩)

theorem restrict_classOf (mapping : QuantifiedImplicativeProgramTheory.Map
    (freeObject source selected constructors) target) :
    restrict source selected constructors target (QuantifiedImplicativeProgramTheory.classOf mapping) =
      ProgramReductionTheoryIsoClasses.classOf (restriction source selected constructors target mapping) := rfl

theorem extend_classOf (mapping : Map source target.quantified.programTheory) :
    extend source selected constructors target (ProgramReductionTheoryIsoClasses.classOf mapping) =
      QuantifiedImplicativeProgramTheory.classOf (extension source selected constructors target mapping) := rfl

theorem restrict_extend (mapping : ProgramReductionTheoryIsoClasses.of source ⟶
    QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :
    restrict source selected constructors target (extend source selected constructors target mapping) = mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  exact Quotient.sound ⟨recoverOriginal selected constructors target mapping⟩

theorem restrict_injective : Function.Injective (restrict source selected constructors target) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun first second same => ?_
  obtain ⟨comparison⟩ := (ProgramReductionTheoryIsoClasses.classOf_equal_iff
    (restriction source selected constructors target first)
    (restriction source selected constructors target second)).mp same
  exact Quotient.sound ⟨mapIsoOfRestriction source selected constructors target comparison⟩

theorem extend_restrict (mapping : freeObject source selected constructors ⟶ target) :
    extend source selected constructors target (restrict source selected constructors target mapping) = mapping :=
  restrict_injective source selected constructors target
    (restrict_extend source selected constructors target (restrict source selected constructors target mapping))

def homEquiv : (freeObject source selected constructors ⟶ target) ≃
    (ProgramReductionTheoryIsoClasses.of source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) where
  toFun := restrict source selected constructors target
  invFun := extend source selected constructors target
  left_inv := extend_restrict source selected constructors target
  right_inv := restrict_extend source selected constructors target

theorem restrict_as_base_composition (mapping : freeObject source selected constructors ⟶ target) :
    restrict source selected constructors target mapping =
      ProgramReductionTheoryIsoClasses.classOf (programInclusion source selected constructors) ≫
        QuantifiedImplicativeProgramTheory.forgetProgram.map mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  rfl

theorem restrict_postcompose {later : QuantifiedImplicativeProgramTheory.{k}}
    (before : freeObject source selected constructors ⟶ target) (after : target ⟶ later) :
    restrict source selected constructors later (before ≫ after) =
      restrict source selected constructors target before ≫
        QuantifiedImplicativeProgramTheory.forgetProgram.map after := by
  rw [restrict_as_base_composition, restrict_as_base_composition,
    QuantifiedImplicativeProgramTheory.forgetProgram.map_comp, Category.assoc]

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedHomEquivalence

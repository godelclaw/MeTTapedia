import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedHomEquivalence

/-!
# The free complete logical extension of bare program theories

Each bare theory receives the actual relative closed predicate syntax,
every admitted positioned-rule modality and every structural constructor
image, followed by complete quantification. Names retain their authored
origins and defining equations. The map action follows from the earned
hom correspondence, with no chosen source proposition or supplied
primitive-admission field. The target carries finite implication and
complete quantifier qualifications; stronger logical capabilities are
separate structures.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedBareLogical

open _root_.CategoryTheory
open Mettapedia.CategoryTheory

universe k

def selections (source : ProgramReductionTheoryIsoClasses.{k}) :
    RelativeClosedPositionedModalPresentation.Selection source.original →
      RelativeClosedPositionedModalPresentation.Selection source.original := id

def constructors (source : ProgramReductionTheoryIsoClasses.{k}) :
    RelativeClosedStructuralImagePresentation.Constructor source.original →
      RelativeClosedStructuralImagePresentation.Constructor source.original := id

def freeObject (source : ProgramReductionTheoryIsoClasses.{k}) : QuantifiedImplicativeProgramTheory.{k} :=
  RelativeClosedNamedQuantifiedHomEquivalence.freeObject source.original
    (selections source) (constructors source)

def unitMap (source : ProgramReductionTheoryIsoClasses.{k}) :
    ProgramReductionTheory.Map source.original (freeObject source).quantified.programTheory :=
  RelativeClosedNamedQuantifiedPresentation.programInclusion source.original
    (selections source) (constructors source)

def unit (source : ProgramReductionTheoryIsoClasses.{k}) :
    source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj (freeObject source) :=
  ProgramReductionTheoryIsoClasses.classOf (unitMap source)

def extension (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : ProgramReductionTheory.Map source.original target.quantified.programTheory) :
    QuantifiedImplicativeProgramTheory.Map (freeObject source) target :=
  RelativeClosedNamedQuantifiedHomEquivalence.extension source.original
    (selections source) (constructors source) target mapping

def restriction (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : QuantifiedImplicativeProgramTheory.Map (freeObject source) target) :
    ProgramReductionTheory.Map source.original target.quantified.programTheory :=
  RelativeClosedNamedQuantifiedHomEquivalence.restriction source.original
    (selections source) (constructors source) target mapping

def extensionRestriction (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : ProgramReductionTheory.Map source.original target.quantified.programTheory) :
    ProgramReductionTheoryIsoClasses.MapIso (restriction source target (extension source target mapping)) mapping :=
  RelativeClosedNamedQuantifiedRestriction.recoverOriginal (selections source) (constructors source) target mapping

def restrict (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k}) :
    (freeObject source ⟶ target) → (source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :=
  RelativeClosedNamedQuantifiedHomEquivalence.restrict source.original
    (selections source) (constructors source) target

def extend (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k}) :
    (source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) → (freeObject source ⟶ target) :=
  RelativeClosedNamedQuantifiedHomEquivalence.extend source.original
    (selections source) (constructors source) target

theorem restrict_extend (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k})
    (mapping : source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :
    restrict source target (extend source target mapping) = mapping :=
  RelativeClosedNamedQuantifiedHomEquivalence.restrict_extend source.original
    (selections source) (constructors source) target mapping

theorem restrict_injective (source : ProgramReductionTheoryIsoClasses.{k})
    (target : QuantifiedImplicativeProgramTheory.{k}) : Function.Injective (restrict source target) :=
  RelativeClosedNamedQuantifiedHomEquivalence.restrict_injective source.original
    (selections source) (constructors source) target

theorem restrict_as_base_composition (source : ProgramReductionTheoryIsoClasses.{k})
    (target : QuantifiedImplicativeProgramTheory.{k}) (mapping : freeObject source ⟶ target) :
    restrict source target mapping = unit source ≫ QuantifiedImplicativeProgramTheory.forgetProgram.map mapping :=
  RelativeClosedNamedQuantifiedHomEquivalence.restrict_as_base_composition source.original
    (selections source) (constructors source) target mapping

theorem restrict_postcompose (source : ProgramReductionTheoryIsoClasses.{k})
    (target : QuantifiedImplicativeProgramTheory.{k}) {later : QuantifiedImplicativeProgramTheory.{k}}
    (before : freeObject source ⟶ target) (after : target ⟶ later) :
    restrict source later (before ≫ after) =
      restrict source target before ≫ QuantifiedImplicativeProgramTheory.forgetProgram.map after :=
  RelativeClosedNamedQuantifiedHomEquivalence.restrict_postcompose source.original
    (selections source) (constructors source) target before after

def freeMap {source target : ProgramReductionTheoryIsoClasses.{k}} (mapping : source ⟶ target) :
    freeObject source ⟶ freeObject target := extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_restriction {source target : ProgramReductionTheoryIsoClasses.{k}} (mapping : source ⟶ target) :
    restrict source (freeObject target) (freeMap mapping) = mapping ≫ unit target :=
  restrict_extend source (freeObject target) (mapping ≫ unit target)

theorem freeMap_identity (source : ProgramReductionTheoryIsoClasses.{k}) :
    freeMap (𝟙 source) = 𝟙 (freeObject source) := by
  apply restrict_injective source (freeObject source)
  rw [freeMap_restriction, restrict_as_base_composition, QuantifiedImplicativeProgramTheory.forgetProgram.map_id]
  rw [Category.id_comp, Category.comp_id]

theorem freeMap_compose {source middle target : ProgramReductionTheoryIsoClasses.{k}}
    (before : source ⟶ middle) (after : middle ⟶ target) :
    freeMap (before ≫ after) = freeMap before ≫ freeMap after := by
  apply restrict_injective source (freeObject target)
  rw [freeMap_restriction, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := freeMap_restriction after
  rw [restrict_as_base_composition] at complete
  change unit middle ≫ QuantifiedImplicativeProgramTheory.forgetProgram.map (freeMap after) =
    after ≫ unit target at complete
  exact (congrArg (fun value => before ≫ value) complete.symm).trans
    (Category.assoc before (unit middle) (QuantifiedImplicativeProgramTheory.forgetProgram.map (freeMap after))).symm

def free : ProgramReductionTheoryIsoClasses.{k} ⥤ QuantifiedImplicativeProgramTheory.{k} where
  obj := freeObject
  map := freeMap
  map_id := freeMap_identity
  map_comp := freeMap_compose

def homEquiv (source : ProgramReductionTheoryIsoClasses.{k}) (target : QuantifiedImplicativeProgramTheory.{k}) :
    (free.obj source ⟶ target) ≃ (source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :=
  RelativeClosedNamedQuantifiedHomEquivalence.homEquiv source.original
    (selections source) (constructors source) target

theorem homEquiv_natural_left_symm
    {before source : ProgramReductionTheoryIsoClasses.{k}} {target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : before ⟶ source) (value : source ⟶ QuantifiedImplicativeProgramTheory.forgetProgram.obj target) :
    (homEquiv before target).symm (mapping ≫ value) = free.map mapping ≫ (homEquiv source target).symm value := by
  apply restrict_injective before target
  change restrict before target (extend before target (mapping ≫ value)) =
    restrict before target (freeMap mapping ≫ extend source target value)
  rw [restrict_extend, restrict_postcompose, freeMap_restriction, Category.assoc]
  have complete := restrict_extend source target value
  rw [restrict_as_base_composition] at complete
  exact congrArg (fun result => mapping ≫ result) complete.symm

theorem homEquiv_natural_right
    {source : ProgramReductionTheoryIsoClasses.{k}} {before target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : free.obj source ⟶ before) (after : before ⟶ target) :
    homEquiv source target (mapping ≫ after) =
      homEquiv source before mapping ≫ QuantifiedImplicativeProgramTheory.forgetProgram.map after :=
  restrict_postcompose source before mapping after

def adjunction : free.{k} ⊣ QuantifiedImplicativeProgramTheory.forgetProgram :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := homEquiv_natural_left_symm
    homEquiv_naturality_right := homEquiv_natural_right }

theorem unit_app (source : ProgramReductionTheoryIsoClasses.{k}) : adjunction.unit.app source = unit source := by
  change restrict source (freeObject source) (𝟙 (freeObject source)) = unit source
  rw [restrict_as_base_composition, QuantifiedImplicativeProgramTheory.forgetProgram.map_id]
  exact Category.comp_id _

def counitMap (target : QuantifiedImplicativeProgramTheory.{k}) :
    QuantifiedImplicativeProgramTheory.Map
      (freeObject (QuantifiedImplicativeProgramTheory.forgetProgram.obj target)) target :=
  extension (QuantifiedImplicativeProgramTheory.forgetProgram.obj target) target
    (ProgramReductionTheory.Map.identity target.quantified.programTheory)

theorem counit_app (target : QuantifiedImplicativeProgramTheory.{k}) :
    adjunction.counit.app target = QuantifiedImplicativeProgramTheory.classOf (counitMap target) := rfl

theorem left_triangle (source : ProgramReductionTheoryIsoClasses.{k}) :
    free.map (adjunction.unit.app source) ≫ adjunction.counit.app (free.obj source) = 𝟙 (free.obj source) :=
  adjunction.left_triangle_components source

theorem right_triangle (target : QuantifiedImplicativeProgramTheory.{k}) :
    adjunction.unit.app (QuantifiedImplicativeProgramTheory.forgetProgram.obj target) ≫
      QuantifiedImplicativeProgramTheory.forgetProgram.map (adjunction.counit.app target) =
        𝟙 (QuantifiedImplicativeProgramTheory.forgetProgram.obj target) := adjunction.right_triangle_components target

end Mettapedia.GSLT.Core.RelativeClosedBareLogical

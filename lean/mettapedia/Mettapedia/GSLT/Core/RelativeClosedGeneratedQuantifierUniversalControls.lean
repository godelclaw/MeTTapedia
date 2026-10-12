import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierUniversalCells
import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierModelReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCanonicalExtension
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicNativeMeaning
import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicOperations
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls
import Mettapedia.CategoryTheory.PositionedRewritePredicatePower

/-!
# A nonidentity weak comparison of the complete quantifier closure

An independently realized logical presentation is
conjugated by a Boolean automorphism at its named predicate object. Other
raw constructor objects keep their chosen presentations. The resulting
closed functor has genuinely changed arrow values. Independently supplied
primitive comparisons restore the original declaration values, and the
closure theorem then determines every later quantifier and the whole cell.
Complete function inputs, future parameters and empty-input rejection are
read through this actual comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierUniversalControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization
open RelativeClosedGeneratedQuantifier Iteration Closure UniversalReadout UniversalCells
open MonoidalCategory CartesianMonoidalCategory

abbrev baseCategory := Discrete PUnit.{1}
def base : baseCategory ⥤ Type := (Functor.const baseCategory).obj PUnit.{1}
abbrev logic := ElementaryTypePredicateReadout.doctrine
def quantifiers := HigherOrderInternalPredicateQuantifiedObject.operations logic
abbrev initialSignature := RelativeClosedPredicateLogic.lawfulSignature (C := baseCategory)

def initialLanguage : PredicateSyntax initialSignature where
  proposition := RelativeClosedPredicateLogic.equationInclusion.object RelativeClosedPredicateLogic.omega
  conjunction := RelativeClosedPredicateLogic.equationInclusion.rawArrow RelativeClosedPredicateLogic.conjunctionRaw

def initialTruth := (RelativeClosedPredicateLogic.equationInclusion (C := baseCategory)).rawArrow
  RelativeClosedPredicateLogic.truthRaw

def initial : Stage baseCategory where
  symbols := _
  presentation := initialSignature
  formed := RelativeClosedPredicateLogic.lawfulHeaders
  language := initialLanguage
  truth := initialTruth
  laws := RelativeClosedPredicateLogic.SourceOperations.laws

def suppliedModel : Model quantifiers initial where
  meanings := RelativeClosedPredicateLogic.Interpretation.lawfulAssignment base
    (RelativeClosedPredicateLogic.NativeMeaning.meaning base logic)
  admitted := RelativeClosedPredicateLogic.NativeMeaning.realized base logic
  proposition := rfl
  conjunction := rfl
  truth := rfl

abbrev targetMeanings := modelAssignment suppliedModel
abbrev targetRealization := modelRealization suppliedModel
abbrev target := Closure.modelDiagram suppliedModel
abbrev targetSignature := Closure.signature initial

instance target_closed : MonoidalClosedFunctor target :=
  RelativeClosedSyntax.Interpretation.functor_closed targetMeanings targetRealization

def negate : Bool ≅ Bool where
  hom := TypeCat.ofHom Bool.not
  inv := TypeCat.ofHom Bool.not
  hom_inv_id := by ext value; exact Bool.not_not value
  inv_hom_id := by ext value; exact Bool.not_not value

theorem predicate_object_read (origin : initial.symbols.ObjectName) :
    targetMeanings.object origin = Bool := by
  rcases origin with ⟨⟨⟩⟩
  rfl

def objectChange (origin : initial.symbols.ObjectName) :
    target.obj (namedObject origin) ≅ target.obj (namedObject origin) :=
  eqToIso (CoherentExtension.target_named_object targetMeanings targetRealization origin) ≪≫
    eqToIso (predicate_object_read origin) ≪≫ negate ≪≫
      (eqToIso (predicate_object_read origin)).symm ≪≫
        (eqToIso (CoherentExtension.target_named_object targetMeanings targetRealization origin)).symm

def presentationChange (source : Object targetSignature) : target.obj source ≅ target.obj source := by
  rcases source with ⟨code, formed⟩
  cases code with
  | name origin => exact objectChange origin
  | base _ => exact Iso.refl _
  | terminal => exact Iso.refl _
  | product _ _ => exact Iso.refl _
  | exponential _ _ => exact Iso.refl _
  | equalizer _ _ _ _ => exact Iso.refl _

def candidate : Object targetSignature ⥤ Type :=
  target.copyObj target.obj presentationChange

def choiceComparison : candidate ≅ target :=
  (target.isoCopyObj target.obj presentationChange).symm

instance candidate_finite : PreservesFiniteLimits candidate :=
  preservesFiniteLimits_of_natIso choiceComparison.symm

instance candidate_closed : MonoidalClosedFunctor candidate :=
  CartesianClosedFunctorCoherence.closed_of_naturalIso choiceComparison

def images : AtomicPresentation.PrimitiveImages candidate targetMeanings where
  base := Functor.isoWhiskerLeft (baseFunctor targetSignature) choiceComparison ≪≫
    (CanonicalExtension.images targetMeanings targetRealization).base
  object origin := choiceComparison.app (namedObject origin) ≪≫
    (CanonicalExtension.images targetMeanings targetRealization).object origin

theorem selected_image (source : Object targetSignature) :
    AtomicPresentation.image candidate targetMeanings images source =
      ⟨target.obj source, (presentationChange source).symm⟩ := by
  rcases source with ⟨code, formed⟩
  cases code with
  | base object =>
      have calibrated := CanonicalExtension.atomic_image targetMeanings targetRealization
        (baseObject targetSignature object)
      change (⟨targetMeanings.base.obj object,
        (presentationChange (baseObject targetSignature object)).symm ≪≫
          (CanonicalExtension.images targetMeanings targetRealization).base.app object⟩ :
          FunctorNormalization.ObjectImage candidate (baseObject targetSignature object)) = _
      have value := congrArg FunctorNormalization.ObjectImage.value calibrated
      cases value
      congr 1
  | name origin =>
      have calibrated := CanonicalExtension.atomic_image targetMeanings targetRealization (namedObject origin)
      change (⟨targetMeanings.object origin,
        (presentationChange (namedObject origin)).symm ≪≫
          (CanonicalExtension.images targetMeanings targetRealization).object origin⟩ :
          FunctorNormalization.ObjectImage candidate (namedObject origin)) = _
      have value := congrArg FunctorNormalization.ObjectImage.value calibrated
      cases value
      congr 1
  | terminal => rfl
  | product _ _ => rfl
  | exponential _ _ => rfl
  | equalizer _ _ _ _ => rfl

private theorem calibrated_map {source targetObject : Object targetSignature}
    (input : ObjectImage candidate source) (output : ObjectImage candidate targetObject)
    (before : input = ⟨target.obj source, (presentationChange source).symm⟩)
    (after : output = ⟨target.obj targetObject, (presentationChange targetObject).symm⟩)
    (arrow : source ⟶ targetObject) :
    input.comparison.inv ≫ candidate.map arrow ≫ output.comparison.hom =
      eqToHom (congrArg ObjectImage.value before) ≫ target.map arrow ≫
        eqToHom (congrArg ObjectImage.value after).symm := by
  cases before
  cases after
  change (presentationChange source).hom ≫
    ((presentationChange source).inv ≫ target.map arrow ≫ (presentationChange targetObject).hom) ≫
      (presentationChange targetObject).inv = 𝟙 _ ≫ target.map arrow ≫ 𝟙 _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp]

theorem selected_is_independent_target : selected suppliedModel candidate images = target := by
  refine _root_.CategoryTheory.Functor.ext
    (fun source => congrArg FunctorNormalization.ObjectImage.value (selected_image source)) ?_
  intro source targetObject arrow
  exact calibrated_map _ _ (selected_image source) (selected_image targetObject) arrow

theorem original_arrow_admission : InitialArrowImages suppliedModel candidate images where
  arrow origin := congrArg (fun meanings : RelativeClosedSyntax.Interpretation.Assignment
      baseCategory (symbols initial) Type => meanings.arrow (.inl origin))
    ((CanonicalExtension.assignment_congr selected_is_independent_target (Closure.headers initial)).trans
      (InterpretationNormalization.normalized_assignment targetMeanings targetRealization
        (Closure.headers initial)))

def wholeComparison : candidate ≅ target :=
  UniversalReadout.comparison suppliedModel candidate images original_arrow_admission

theorem choice_comparison_admitted : CellAdmission suppliedModel candidate images choiceComparison.hom where
  base object := by
    have fixed := (CanonicalExtension.identity_admitted targetMeanings targetRealization).base object
    change 𝟙 _ = (CanonicalExtension.images targetMeanings targetRealization).base.hom.app object ≫
      eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object targetMeanings targetRealization object).symm at fixed
    change choiceComparison.hom.app (baseObject targetSignature object) =
      (choiceComparison.hom.app (baseObject targetSignature object) ≫
        (CanonicalExtension.images targetMeanings targetRealization).base.hom.app object) ≫ _
    rw [Category.assoc, ← fixed]
    exact (Category.comp_id (choiceComparison.hom.app (baseObject targetSignature object))).symm
  object origin := by
    have fixed := (CanonicalExtension.identity_admitted targetMeanings targetRealization).object origin
    change 𝟙 _ = ((CanonicalExtension.images targetMeanings targetRealization).object origin).hom ≫
      eqToHom (CoherentExtension.target_named_object targetMeanings targetRealization origin).symm at fixed
    change choiceComparison.hom.app (namedObject origin) =
      (choiceComparison.hom.app (namedObject origin) ≫
        ((CanonicalExtension.images targetMeanings targetRealization).object origin).hom) ≫ _
    rw [Category.assoc, ← fixed]
    exact (Category.comp_id (choiceComparison.hom.app (namedObject origin))).symm

theorem complete_comparison_is_choice : wholeComparison = choiceComparison :=
  Iso.ext (UniversalCells.admitted_cell_unique suppliedModel candidate images original_arrow_admission
    choiceComparison.hom choice_comparison_admitted).symm

def predicateOrigin : initial.symbols.ObjectName := ULift.up ()
def predicateObject : Object targetSignature := namedObject predicateOrigin
def predicateComparison : target.obj predicateObject ≅ Bool :=
  eqToIso (CoherentExtension.target_named_object targetMeanings targetRealization predicateOrigin) ≪≫
    eqToIso (predicate_object_read predicateOrigin)

def completePredicateCell : Bool ⟶ Bool :=
  predicateComparison.inv ≫ wholeComparison.hom.app predicateObject ≫ predicateComparison.hom

theorem completePredicateCell_read : completePredicateCell = negate.inv := by
  rw [completePredicateCell, complete_comparison_is_choice]
  change predicateComparison.inv ≫
    ((predicateComparison ≪≫ negate ≪≫ predicateComparison.symm).inv) ≫ predicateComparison.hom = _
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem the_actual_comparison_retains_a_nonidentity_value :
    completePredicateCell false = true ∧ completePredicateCell true = false := by
  rw [completePredicateCell_read]
  exact ⟨rfl, rfl⟩

theorem identity_component_cannot_replace_the_complete_cell :
    wholeComparison.hom.app predicateObject ≠ 𝟙 (target.obj predicateObject) := by
  intro same
  have identityRead : completePredicateCell = 𝟙 Bool := by
    change predicateComparison.inv ≫ wholeComparison.hom.app predicateObject ≫ predicateComparison.hom = _
    rw [same, Category.id_comp, Iso.inv_hom_id]
  have impossible := congrArg (fun arrow : Bool ⟶ Bool => arrow false) identityRead
  rw [completePredicateCell_read] at impossible
  exact Bool.false_ne_true impossible.symm

theorem all_added_primitive_values_are_recovered :
    extracted suppliedModel candidate images = targetMeanings :=
  UniversalReadout.all_primitive_meanings_recovered suppliedModel candidate images original_arrow_admission

def originalRoute : Route initial.presentation where
  source := initial.language.proposition
  target := terminal initial.presentation
  arrow := RawHom.toTerminal initial.language.proposition

def completeRoute := originalRoute.translate (stageMap initial 0)

theorem original_route_read : RawInterpretation.Reads suppliedModel.meanings originalRoute.arrow
    HigherOrderInternalPredicateControls.forgetBoolean := rfl

def completeUniversal := (Closure.universal initial (classOf completeRoute.arrow)).operation
def completeExistential := (Closure.existential initial (classOf completeRoute.arrow)).operation

def candidateOperatorValue (operation : InternalPredicateFunctionObject.power (operations initial) completeRoute.source ⟶
    InternalPredicateFunctionObject.power (operations initial) completeRoute.target) :
    RelativeClosedSyntax.Interpretation.ArrowValue Type :=
  ⟨candidate.obj (InternalPredicateFunctionObject.power (operations initial) completeRoute.source),
    candidate.obj (InternalPredicateFunctionObject.power (operations initial) completeRoute.target),
    candidate.map operation⟩

theorem complete_operator_comparison
    (operation : InternalPredicateFunctionObject.power (operations initial) completeRoute.source ⟶
      InternalPredicateFunctionObject.power (operations initial) completeRoute.target) :
    candidateOperatorValue operation = modelOperatorValue suppliedModel completeRoute operation := by
  change (⟨_, _, 𝟙 _ ≫ target.map operation ≫ 𝟙 _⟩ : RelativeClosedSyntax.Interpretation.ArrowValue Type) = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

theorem complete_universal_value : candidateOperatorValue completeUniversal =
    (⟨InternalPredicateFunctionObject.power quantifiers.predicates Bool,
      InternalPredicateFunctionObject.power quantifiers.predicates PUnit,
      HigherOrderInternalPredicateControls.quantifier.operation⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue Type) :=
  (complete_operator_comparison completeUniversal).trans
    (unique_universal_model_read suppliedModel 0 originalRoute
      HigherOrderInternalPredicateControls.forgetBoolean original_route_read)

theorem complete_existential_value : candidateOperatorValue completeExistential =
    (⟨InternalPredicateFunctionObject.power quantifiers.predicates Bool,
      InternalPredicateFunctionObject.power quantifiers.predicates PUnit,
      HigherOrderInternalPredicateControls.existential.operation⟩ :
      RelativeClosedSyntax.Interpretation.ArrowValue Type) :=
  (complete_operator_comparison completeExistential).trans
    (unique_existential_model_read suppliedModel 0 originalRoute
      HigherOrderInternalPredicateControls.forgetBoolean original_route_read)

abbrev functionInput := InternalPredicateFunctionObject.power quantifiers.predicates Bool
abbrev functionOutput := InternalPredicateFunctionObject.power quantifiers.predicates PUnit

def checkedUniversal : Option (functionInput ⟶ functionOutput) :=
  RelativeClosedSyntax.Interpretation.ArrowValue.readAt (some (candidateOperatorValue completeUniversal))
    functionInput functionOutput

def checkedExistential : Option (functionInput ⟶ functionOutput) :=
  RelativeClosedSyntax.Interpretation.ArrowValue.readAt (some (candidateOperatorValue completeExistential))
    functionInput functionOutput

theorem checkedUniversal_read : checkedUniversal =
    some HigherOrderInternalPredicateControls.quantifier.operation := by
  rw [checkedUniversal, complete_universal_value]
  exact RelativeClosedSyntax.Interpretation.ArrowValue.readAt_supplied _

theorem checkedExistential_read : checkedExistential =
    some HigherOrderInternalPredicateControls.existential.operation := by
  rw [checkedExistential, complete_existential_value]
  exact RelativeClosedSyntax.Interpretation.ArrowValue.readAt_supplied _

def actualUniversal : functionInput ⟶ functionOutput :=
  checkedUniversal.get (by rw [checkedUniversal_read]; rfl)

def actualExistential : functionInput ⟶ functionOutput :=
  checkedExistential.get (by rw [checkedExistential_read]; rfl)

theorem actualUniversal_read : actualUniversal = HigherOrderInternalPredicateControls.quantifier.operation :=
  Option.some.inj ((Option.some_get (by rw [checkedUniversal_read]; rfl)).trans checkedUniversal_read)

theorem actualExistential_read : actualExistential = HigherOrderInternalPredicateControls.existential.operation :=
  Option.some.inj ((Option.some_get (by rw [checkedExistential_read]; rfl)).trans checkedExistential_read)

def suppliedOutput : Subobject (PUnit ⊗ Nat) :=
  HigherOrderInternalPredicateObject.family logic
    (HigherOrderInternalPredicateControls.suppliedName ≫ actualUniversal)

theorem complete_function_reads_both_coordinates (parameter : Nat) :
    ElementaryTypePredicateReadout.Contains suppliedOutput (PUnit.unit, parameter) ↔ parameter > 1 := by
  rw [suppliedOutput, actualUniversal_read]
  exact HigherOrderInternalPredicateControls.complete_output_read parameter

theorem existential_and_universal_separate_the_supplied_input :
    ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family logic
        (HigherOrderInternalPredicateControls.suppliedName ≫ actualExistential)) (PUnit.unit, 1) ∧
      ¬ElementaryTypePredicateReadout.Contains suppliedOutput (PUnit.unit, 1) := by
  rw [suppliedOutput, actualExistential_read, actualUniversal_read]
  exact HigherOrderInternalPredicateControls.the_existential_keeps_an_actual_supplied_coordinate

theorem a_single_child_is_not_the_complete_universal :
    ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family logic HigherOrderInternalPredicateControls.suppliedName) (false, 1) ∧
      ¬ElementaryTypePredicateReadout.Contains suppliedOutput (PUnit.unit, 1) := by
  rw [suppliedOutput, actualUniversal_read]
  exact HigherOrderInternalPredicateControls.a_single_coordinate_cannot_replace_the_native_quantifier

theorem a_future_parameter_changes_the_actual_answer (parameter : Nat) :
    ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family logic
        ((HigherOrderInternalPredicateControls.future ≫ HigherOrderInternalPredicateControls.suppliedName) ≫
          actualUniversal)) (PUnit.unit, parameter) ↔ parameter + 1 > 1 := by
  rw [actualUniversal_read]
  exact HigherOrderInternalPredicateControls.complete_future_read parameter

def emptyPredicate : Subobject (Bool ⊗ Nat) :=
  ElementaryTypePredicateReadout.fromSet (∅ : Set (Bool ⊗ Nat))

def emptyName : Nat ⟶ functionInput := PositionedRewritePredicatePower.name logic emptyPredicate

theorem actual_existential_rejects_empty_input (parameter : Nat) :
    ¬ElementaryTypePredicateReadout.Contains
      (HigherOrderInternalPredicateObject.family logic (emptyName ≫ actualExistential))
        (PUnit.unit, parameter) := by
  rw [actualExistential_read]
  have complete := (HigherOrderInternalPredicateQuantifier.exists_supplied logic
    HigherOrderInternalPredicateControls.forgetBoolean emptyName).trans
      (congrArg (logic.existsAlong (HigherOrderInternalPredicateControls.forgetBoolean ▷ Nat))
        (PositionedRewritePredicatePower.family_name logic emptyPredicate))
  change ¬ElementaryTypePredicateReadout.Contains
    (HigherOrderInternalPredicateObject.family logic
      (emptyName ≫ HigherOrderInternalPredicateQuantifier.existsOperation logic
        HigherOrderInternalPredicateControls.forgetBoolean)) (PUnit.unit, parameter)
  rw [complete, ElementaryTypePredicateReadout.contains_exists]
  rintro ⟨point, held, _⟩
  exact (ElementaryTypePredicateReadout.contains_fromSet (∅ : Set (Bool ⊗ Nat)) point).mp held

end Mettapedia.GSLT.Core.RelativeClosedGeneratedQuantifierUniversalControls

import Mettapedia.CategoryTheory.InternalPredicateImplicationFunctionMaps
import Mettapedia.CategoryTheory.RelativeClosedQuantifiedImplication
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectTransport
import Mettapedia.GSLT.Core.RelativeClosedQuantifiedAdjunctionControls

/-!
# Complete implication transport and lossy predicate controls

A nonidentity Boolean proposition presentation carries two independent,
number-dependent predicates into the actual native implication. A future
parameter changes the resulting answer. The actual free completion and its
supplied weak map satisfy the same complete-operation comparison.

An independent two-coordinate predicate readout preserves truth and meet
while losing implication. It has no proposition-object isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.InternalPredicateImplicationMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open HigherOrderInternalPredicateObject ElementaryTypePredicateReadout

abbrev logic := HigherOrderInternalPredicateControls.logic
def nativeOperations := HigherOrderInternalPredicateQuantifiedObject.operations logic

def changedPresentation : nativeOperations.predicates.proposition ≅ nativeOperations.predicates.proposition := by
  change Bool ≅ Bool
  exact {
    hom := TypeCat.ofHom Bool.not
    inv := TypeCat.ofHom Bool.not
    hom_inv_id := by ext predicate; exact Bool.not_not predicate
    inv_hom_id := by ext predicate; exact Bool.not_not predicate }

def sourceOperations := InternalPredicateQuantifiedObject.Transport.operations nativeOperations changedPresentation
abbrev forward := InternalPredicateQuantifiedObject.Transport.forward nativeOperations changedPresentation
abbrev backward := InternalPredicateQuantifiedObject.Transport.backward nativeOperations changedPresentation

def sourceImplication : InternalPredicateImplication.Qualification sourceOperations.predicates :=
  InternalPredicateImplicationMaps.qualificationImage backward HigherOrderInternalPredicateControls.implication

def firstInput : Nat ⟶ sourceOperations.predicates.proposition :=
  backward.image HigherOrderInternalPredicateControls.antecedentName
def secondInput : Nat ⟶ sourceOperations.predicates.proposition :=
  backward.image HigherOrderInternalPredicateControls.consequentName

def output : Nat ⟶ nativeOperations.predicates.proposition :=
  forward.image (sourceImplication.implies sourceOperations.predicates firstInput secondInput)

theorem complete_native_meaning : output = HigherOrderInternalPredicateControls.implicationName := by
  have complete := InternalPredicateImplicationMaps.implication_supplied forward nativeOperations.laws
    sourceImplication HigherOrderInternalPredicateControls.implication firstInput secondInput
  exact complete.trans
    (congrArg₂ (HigherOrderInternalPredicateControls.implication.implies nativeOperations.predicates)
      (InternalPredicateQuantifiedObject.Transport.predicate_recovered nativeOperations changedPresentation
        HigherOrderInternalPredicateControls.antecedentName)
      (InternalPredicateQuantifiedObject.Transport.predicate_recovered nativeOperations changedPresentation
        HigherOrderInternalPredicateControls.consequentName))

theorem complete_number_read (parameter : Nat) :
    Contains (decode logic output) parameter ↔ (parameter > 0 → parameter > 1) := by
  rw [complete_native_meaning]
  exact HigherOrderInternalPredicateControls.complete_implication_read parameter

theorem the_actual_implication_retains_both_inputs :
    Contains (decode logic output) 0 ∧ ¬ Contains (decode logic output) 1 ∧
      Contains (decode logic output) 2 := by
  rw [complete_number_read, complete_number_read, complete_number_read]
  exact ⟨by omega, by omega, by omega⟩

theorem the_proposition_comparison_is_not_identity : changedPresentation.hom ≠ 𝟙 _ := by
  intro same
  have reading := congrArg (fun arrow : Bool ⟶ Bool => arrow true) same
  change false = true at reading
  cases reading

def futureOutput : Nat ⟶ nativeOperations.predicates.proposition :=
  forward.image (HigherOrderInternalPredicateControls.future ≫
    sourceImplication.implies sourceOperations.predicates firstInput secondInput)

theorem future_output_read : futureOutput =
    HigherOrderInternalPredicateControls.future ≫ HigherOrderInternalPredicateControls.implicationName := by
  have complete := forward.image_reindex HigherOrderInternalPredicateControls.future
    (sourceImplication.implies sourceOperations.predicates firstInput secondInput)
  exact complete.trans (congrArg (fun arrow => HigherOrderInternalPredicateControls.future ≫ arrow)
    complete_native_meaning)

theorem complete_future_read (parameter : Nat) :
    Contains (decode logic futureOutput) parameter ↔ (parameter + 1 > 0 → parameter + 1 > 1) := by
  rw [future_output_read, decode_substitution]
  exact (contains_reindex HigherOrderInternalPredicateControls.future _ parameter).trans
    (HigherOrderInternalPredicateControls.complete_implication_read (parameter + 1))

theorem the_actual_future_changes_the_implication :
    Contains (decode logic output) 0 ∧ ¬ Contains (decode logic futureOutput) 0 := by
  rw [complete_number_read, complete_future_read]
  exact ⟨by omega, by omega⟩

def firstWhole : Bool ⊗ Nat ⟶ nativeOperations.predicates.proposition :=
  InternalPredicateFunctionObject.read nativeOperations.predicates
    HigherOrderInternalPredicateControls.suppliedName
def secondWholePredicate : Subobject (Bool ⊗ Nat) :=
  fromSet {point | if point.1 then point.2 > 0 else point.2 > 1}
def secondWhole : Bool ⊗ Nat ⟶ nativeOperations.predicates.proposition :=
  logic.generic.characteristic _ secondWholePredicate

def firstSection : Nat ⟶ InternalPredicateFunctionObject.power sourceOperations.predicates Bool :=
  InternalPredicateFunctionObject.quote sourceOperations.predicates (backward.image firstWhole)
def secondSection : Nat ⟶ InternalPredicateFunctionObject.power sourceOperations.predicates Bool :=
  InternalPredicateFunctionObject.quote sourceOperations.predicates (backward.image secondWhole)

private theorem identity_product_inverse (value parameter : Type) :
    inv (CartesianMonoidalCategory.prodComparison (𝟭 Type) value parameter) = 𝟙 (value ⊗ parameter) :=
  IsIso.inv_eq_of_hom_inv_id
    ((Category.comp_id _).trans (CartesianMonoidalCategory.prodComparison_id (A := value) (B := parameter)))

theorem first_complete_function_read :
    InternalPredicateFunctionObject.read nativeOperations.predicates
        (InternalPredicateFunctionObjectMaps.sectionImage forward firstSection) = firstWhole := by
  have sourceRead : InternalPredicateFunctionObject.read sourceOperations.predicates firstSection =
      backward.image firstWhole := InternalPredicateFunctionObject.read_quote _ _
  have predicateRead := (congrArg forward.image sourceRead).trans
    (InternalPredicateQuantifiedObject.Transport.predicate_recovered nativeOperations changedPresentation firstWhole)
  have complete := (InternalPredicateFunctionObjectMaps.sectionImage_read forward firstSection).trans
    (congrArg (fun arrow => inv (CartesianMonoidalCategory.prodComparison (𝟭 Type) Bool Nat) ≫ arrow) predicateRead)
  refine complete.trans ?_
  exact (congrArg (fun arrow => arrow ≫ firstWhole)
    (identity_product_inverse Bool Nat)).trans (Category.id_comp _)

theorem second_complete_function_read :
    InternalPredicateFunctionObject.read nativeOperations.predicates
        (InternalPredicateFunctionObjectMaps.sectionImage forward secondSection) = secondWhole := by
  have sourceRead : InternalPredicateFunctionObject.read sourceOperations.predicates secondSection =
      backward.image secondWhole := InternalPredicateFunctionObject.read_quote _ _
  have predicateRead := (congrArg forward.image sourceRead).trans
    (InternalPredicateQuantifiedObject.Transport.predicate_recovered nativeOperations changedPresentation secondWhole)
  have complete := (InternalPredicateFunctionObjectMaps.sectionImage_read forward secondSection).trans
    (congrArg (fun arrow => inv (CartesianMonoidalCategory.prodComparison (𝟭 Type) Bool Nat) ≫ arrow) predicateRead)
  refine complete.trans ?_
  exact (congrArg (fun arrow => arrow ≫ secondWhole)
    (identity_product_inverse Bool Nat)).trans (Category.id_comp _)

def functionOutput : Bool ⊗ Nat ⟶ nativeOperations.predicates.proposition :=
  forward.image (sourceImplication.implies sourceOperations.predicates
    (InternalPredicateFunctionObject.read sourceOperations.predicates firstSection)
    (InternalPredicateFunctionObject.read sourceOperations.predicates secondSection))

theorem the_canonical_function_comparison_retains_both_complete_inputs :
    functionOutput = HigherOrderInternalPredicateControls.implication.implies
      nativeOperations.predicates firstWhole secondWhole := by
  have complete := InternalPredicateImplicationFunctionMaps.supplied_read forward nativeOperations.laws
    sourceImplication HigherOrderInternalPredicateControls.implication firstSection secondSection
  have identityRead : functionOutput =
      inv (CartesianMonoidalCategory.prodComparison (𝟭 Type) Bool Nat) ≫ functionOutput := by
    exact ((congrArg (fun arrow => arrow ≫ functionOutput)
      (identity_product_inverse Bool Nat)).trans (Category.id_comp _)).symm
  exact identityRead.trans (complete.trans
    (congrArg₂ (HigherOrderInternalPredicateControls.implication.implies nativeOperations.predicates)
      first_complete_function_read second_complete_function_read))

theorem complete_value_parameter_read (value : Bool) (parameter : Nat) :
    Contains (decode logic functionOutput) (value, parameter) ↔
      ((if value then parameter > 1 else parameter > 0) →
        (if value then parameter > 0 else parameter > 1)) := by
  have interpreted := HigherOrderInternalPredicateImplication.applied_read logic firstWhole secondWhole
  change decode logic
    (HigherOrderInternalPredicateControls.implication.implies nativeOperations.predicates firstWhole secondWhole) =
      (logic.algebra (Bool ⊗ Nat)).himp (decode logic firstWhole) (decode logic secondWhole) at interpreted
  have firstReading := HigherOrderInternalPredicateControls.supplied_family
  change decode logic firstWhole = HigherOrderInternalPredicateControls.suppliedPredicate at firstReading
  have secondReading : decode logic secondWhole = secondWholePredicate := decode_characteristic logic _
  have complete := (congrArg (decode logic)
    the_canonical_function_comparison_retains_both_complete_inputs).trans
      (interpreted.trans (congrArg₂ (logic.algebra (Bool ⊗ Nat)).himp firstReading secondReading))
  refine (Iff.of_eq (congrArg (fun predicate : Subobject (Bool ⊗ Nat) =>
      Contains predicate (value, parameter)) complete)).trans ?_
  refine (contains_implication _ _ (value, parameter)).trans ?_
  simp only [HigherOrderInternalPredicateControls.suppliedPredicate, secondWholePredicate,
    contains_fromSet]
  rfl

theorem the_complete_function_depends_on_the_value_and_parameter :
    Contains (decode logic functionOutput) (true, 1) ∧
      ¬ Contains (decode logic functionOutput) (false, 1) ∧
      Contains (decode logic functionOutput) (false, 2) := by
  rw [complete_value_parameter_read, complete_value_parameter_read, complete_value_parameter_read]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact ⟨by omega, by omega, by omega⟩

def coordinateMeet (first second : Bool × Bool) : Bool × Bool :=
  (first.1 && second.1, first.2 && second.2)
def coordinateImplication (first second : Bool × Bool) : Bool × Bool :=
  (!first.1 || second.1, !first.2 || second.2)
def coordinateOrder (first second : Bool × Bool) : Prop :=
  (first.1 = true → second.1 = true) ∧ (first.2 = true → second.2 = true)
def collapsed (predicate : Bool × Bool) : Bool := predicate.1 && predicate.2

theorem the_independent_coordinate_implication_has_its_adjunction :
    ∀ first second argument : Bool × Bool,
      coordinateOrder (coordinateMeet first argument) second ↔
        coordinateOrder argument (coordinateImplication first second) := by
  unfold coordinateOrder coordinateMeet coordinateImplication
  decide

theorem the_readout_preserves_truth : collapsed (true, true) = true := rfl

theorem the_readout_preserves_meet :
    ∀ first second : Bool × Bool,
      collapsed (coordinateMeet first second) = (collapsed first && collapsed second) := by decide

theorem the_readout_loses_implication :
    collapsed (coordinateImplication (false, true) (false, false)) ≠
      (!collapsed (false, true) || collapsed (false, false)) := by decide

theorem the_readout_cannot_be_a_proposition_isomorphism : ¬ Function.Injective collapsed := by
  intro injective
  have same := injective (a₁ := (false, true)) (a₂ := (true, false)) rfl
  have read := congrArg Prod.fst same
  cases read

namespace Completion

open RelativeClosedQuantifiedAdjunctionControls
open InternalConjunctiveOrderComparison

def targetImplication := HigherOrderInternalPredicateImplication.qualification nativeLogic
def originalImplication : InternalPredicateImplication.Qualification source.operations.predicates :=
  InternalPredicateImplicationMaps.qualificationImage
    (InternalPredicateQuantifiedObject.Transport.backward
      RelativeClosedQuantifiedAdjunctionControls.nativeOperations propositionNegation) targetImplication

def completedQualification :=
  RelativeClosedQuantified.Implication.freeQualification source.conjunctive originalImplication

theorem the_actual_completion_retains_the_whole_implication :
    InternalPredicateImplicationMaps.operationImage extended.declarations completedQualification.operation =
      targetImplication.operation :=
  InternalPredicateImplicationMaps.implication_image extended.declarations target.operations.laws
    completedQualification targetImplication

end Completion

end Mettapedia.GSLT.Core.InternalPredicateImplicationMapControls

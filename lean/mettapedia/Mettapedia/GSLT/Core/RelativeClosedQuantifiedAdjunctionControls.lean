import Mettapedia.CategoryTheory.RelativeClosedQuantifiedMonad
import Mettapedia.CategoryTheory.AsSmallPredicateDoctrine
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls

/-!+# Complete quantified extension through an independently changed predicate presentation

The native set doctrine is transported through the actual category universe
equivalence. A negated proposition presentation has an identity base functor
but a nonidentity complete proposition comparison. Its generated extension
recovers the full supplied number predicate and the changing future input.
Both weak-map hom roundtrips and the complete second-completion fold apply
to these actual data. Independent native quantifier fibres distinguish
existential and universal answers on the same proper Boolean/number input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedQuantifiedAdjunctionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory
open RelativeClosedQuantified
open RelativeClosedSyntax GeneratedCategory
open ElementaryTypePredicateReadout

abbrev nativeCategory := AsSmallYoneda.Small Type
abbrev upward : Type ⥤ nativeCategory := AsSmallYoneda.up Type
abbrev nativeLogic := AsSmallPredicateDoctrine.higherOrder ElementaryTypePredicateReadout.doctrine
def nativeOperations := HigherOrderInternalPredicateQuantifiedObject.operations nativeLogic

abbrev target : QuantifiedClosedTheory.{1} where
  closed := LambdaTheory.ofCategory nativeCategory
  operations := nativeOperations

def propositionNegation : nativeOperations.predicates.proposition ≅ nativeOperations.predicates.proposition := by
  change upward.obj Bool ≅ upward.obj Bool
  exact {
    hom := upward.map (TypeCat.ofHom Bool.not)
    inv := upward.map (TypeCat.ofHom Bool.not)
    hom_inv_id := by apply ULift.ext; ext predicate; exact Bool.not_not predicate
    inv_hom_id := by apply ULift.ext; ext predicate; exact Bool.not_not predicate }

abbrev source : QuantifiedClosedTheory.{1} where
  closed := target.closed
  operations := InternalPredicateQuantifiedObject.Transport.operations nativeOperations propositionNegation

def supplied : ConjunctiveClosedTheory.Map source.conjunctive target.conjunctive where
  declarations := InternalPredicateQuantifiedObject.Transport.forward nativeOperations propositionNegation
  finite := InternalPredicateQuantifiedObject.Transport.forward_finite nativeOperations propositionNegation
  closed := InternalPredicateQuantifiedObject.Transport.forward_closed nativeOperations propositionNegation

abbrev extended := Extension.extendMap supplied

def numberPredicate : upward.obj Nat ⟶ source.operations.predicates.proposition := by
  change upward.obj Nat ⟶ upward.obj Bool
  exact upward.map (TypeCat.ofHom (fun number : Nat => decide (number > 0)))

def independentlyNegatedPredicate : upward.obj Nat ⟶ target.operations.predicates.proposition := by
  change upward.obj Nat ⟶ upward.obj Bool
  exact upward.map (TypeCat.ofHom (fun number : Nat => decide (number = 0)))

theorem supplied_complete_predicate :
    supplied.declarations.image numberPredicate = independentlyNegatedPredicate := by
  apply ULift.ext
  change TypeCat.ofHom (fun number : Nat => !(decide (number > 0))) =
    TypeCat.ofHom (fun number : Nat => decide (number = 0))
  ext number
  change Bool.not (decide (number > 0)) = decide (number = 0)
  cases number <;> simp

theorem contextRecovery :
    (Extension.restrictMap extended).functor.obj (upward.obj Nat) = upward.obj Nat :=
  congrArg (fun functor => functor.obj (upward.obj Nat)) (Extension.complete_base_recovered supplied)

def extendedPredicate : upward.obj Nat ⟶ target.operations.predicates.proposition :=
  eqToHom contextRecovery.symm ≫ (Extension.restrictMap extended).declarations.image numberPredicate

theorem entire_extension_readout : extendedPredicate = independentlyNegatedPredicate := by
  let comparison := HomEquivalence.extension_restriction source.conjunctive target supplied
  have natural := comparison.comparison.hom.naturality numberPredicate
  change (Extension.restrictMap extended).functor.map numberPredicate ≫
      comparison.comparison.hom.app source.operations.predicates.proposition =
    comparison.comparison.hom.app (upward.obj Nat) ≫ supplied.functor.map numberPredicate at natural
  change eqToHom contextRecovery.symm ≫
      ((Extension.restrictMap extended).functor.map numberPredicate ≫
        (Extension.restrictMap extended).declarations.proposition.hom) = independentlyNegatedPredicate
  have rewritten := congrArg (fun arrow => eqToHom contextRecovery.symm ≫
    ((Extension.restrictMap extended).functor.map numberPredicate ≫ arrow)) comparison.proposition.symm
  have transported := congrArg (fun arrow => eqToHom contextRecovery.symm ≫
    (arrow ≫ supplied.declarations.proposition.hom)) natural
  apply rewritten.trans
  rw [← Category.assoc]
  apply transported.trans
  simp only [Category.assoc]
  dsimp only [comparison, HomEquivalence.extension_restriction, eqToIso.hom, eqToHom_app]
  simp only [eqToHom_app]
  change eqToHom contextRecovery.symm ≫
      (eqToHom contextRecovery ≫ supplied.declarations.image numberPredicate) = independentlyNegatedPredicate
  rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact supplied_complete_predicate

theorem complete_number_readings :
    extendedPredicate.down (0 : Nat) = (true : Bool) ∧
      extendedPredicate.down (1 : Nat) = (false : Bool) := by
  rw [entire_extension_readout]
  exact ⟨rfl, rfl⟩

theorem the_extension_does_not_discard_the_proposition_comparison :
    extendedPredicate ≠ numberPredicate := by
  intro same
  have collided := congrArg (fun arrow : upward.obj Nat ⟶ upward.obj Bool => arrow.down (0 : Nat)) same
  have rejected : numberPredicate.down (0 : Nat) = (false : Bool) := rfl
  exact Bool.false_ne_true (complete_number_readings.1.symm.trans (collided.trans rejected)).symm

def future : upward.obj Nat ⟶ upward.obj Nat := upward.map (TypeCat.ofHom Nat.succ)

theorem the_complete_future_changes_admission :
    extendedPredicate.down (0 : Nat) = (true : Bool) ∧
      (future ≫ extendedPredicate).down (0 : Nat) = (false : Bool) := by
  constructor
  · exact complete_number_readings.1
  · change extendedPredicate.down (1 : Nat) = (false : Bool)
    exact complete_number_readings.2

theorem the_supplied_base_hom_roundtrip :
    HomEquivalence.restrict source.conjunctive target
      (HomEquivalence.extend source.conjunctive target (ConjunctiveClosedTheory.classOf supplied)) =
        ConjunctiveClosedTheory.classOf supplied :=
  HomEquivalence.restrict_extend source.conjunctive target (ConjunctiveClosedTheory.classOf supplied)

theorem the_complete_candidate_hom_roundtrip :
    HomEquivalence.extend source.conjunctive target
      (HomEquivalence.restrict source.conjunctive target (QuantifiedClosedTheory.classOf extended)) =
        QuantifiedClosedTheory.classOf extended :=
  HomEquivalence.extend_restrict source.conjunctive target (QuantifiedClosedTheory.classOf extended)

def secondFold := Construction.multiplicationMap source.conjunctive

theorem the_second_fold_retains_the_whole_first_predicate :
    secondFold.functor.map
        (baseArrow (signature := RelativeClosedGeneratedQuantifier.Closure.signature
          (stage (freeObject source.conjunctive).conjunctive))
          ((Extension.unitMap source.conjunctive).declarations.image numberPredicate)) ≫
      eqToHom (Construction.retains_old_object source.conjunctive
        (freeObject source.conjunctive).operations.predicates.proposition) =
    eqToHom (Construction.retains_old_object source.conjunctive
        ((Extension.unitMap source.conjunctive).functor.obj (upward.obj Nat))) ≫
      (Extension.unitMap source.conjunctive).declarations.image numberPredicate :=
  Construction.retains_old_arrow source.conjunctive
    ((Extension.unitMap source.conjunctive).declarations.image numberPredicate)

def generatedBooleanRoute := (Extension.unitMap source.conjunctive).functor.map
  (upward.map HigherOrderInternalPredicateControls.forgetBoolean)

theorem both_complete_generated_operations_are_preserved :
    InternalPredicateFunctionObjectMaps.arrowImage extended.declarations
        ((freeObject source.conjunctive).operations.universal generatedBooleanRoute).operation =
      (target.operations.universal (extended.functor.map generatedBooleanRoute)).operation ∧
    InternalPredicateFunctionObjectMaps.arrowImage extended.declarations
        ((freeObject source.conjunctive).operations.existential generatedBooleanRoute).operation =
      (target.operations.existential (extended.functor.map generatedBooleanRoute)).operation :=
  QuantifiedClosedTheory.every_weak_map_preserves_both_quantifiers extended generatedBooleanRoute

def nativeInput : nativeLogic.Fiber (upward.obj (Bool × Nat)) :=
  HigherOrderInternalPredicateControls.suppliedPredicate

def nativeRoute : upward.obj (Bool × Nat) ⟶ upward.obj (PUnit × Nat) :=
  upward.map (HigherOrderInternalPredicateControls.forgetBoolean ▷ Nat)

def nativeUniversal := nativeLogic.forallAlong nativeRoute nativeInput
def nativeExistential := nativeLogic.existsAlong nativeRoute nativeInput

theorem both_native_quantifiers_retain_the_independent_supplied_fibre :
    nativeExistential = HigherOrderInternalPredicateControls.existentialOutput ∧
      nativeUniversal = HigherOrderInternalPredicateControls.output :=
  ⟨HigherOrderInternalPredicateControls.existential_output_evaluation.symm,
    HigherOrderInternalPredicateControls.output_evaluation.symm⟩

theorem the_native_quantifiers_give_different_complete_answers :
    Contains nativeExistential (PUnit.unit, 1) ∧ ¬ Contains nativeUniversal (PUnit.unit, 1) := by
  rw [both_native_quantifiers_retain_the_independent_supplied_fibre.1,
    both_native_quantifiers_retain_the_independent_supplied_fibre.2]
  exact HigherOrderInternalPredicateControls.the_existential_keeps_an_actual_supplied_coordinate

theorem a_constant_answer_loses_the_complete_native_input :
    Contains nativeUniversal (PUnit.unit, 2) ∧ ¬ Contains nativeUniversal (PUnit.unit, 1) := by
  rw [both_native_quantifiers_retain_the_independent_supplied_fibre.2]
  exact HigherOrderInternalPredicateControls.the_complete_native_answer_is_not_constant

end Mettapedia.GSLT.Core.RelativeClosedQuantifiedAdjunctionControls

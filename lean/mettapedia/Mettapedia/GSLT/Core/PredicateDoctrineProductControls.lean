import Mettapedia.CategoryTheory.PredicateDoctrineProduct
import Mettapedia.CategoryTheory.PredicateDoctrineProductAgreement
import Mettapedia.CategoryTheory.ElementaryTypePredicateReadout
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateObject
import Mettapedia.CategoryTheory.PositionedRewritePredicateLogic

/-!
# Classification and witness controls for paired predicates

The actual product of two elementary predicate doctrines has a four-valued
generic predicate. It classifies its complete declared fibre, while ordinary
truth comprehension can forget which coordinate failed. Quantifying the
coordinates separately does not supply an input satisfying both coordinates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.PredicateDoctrineProductControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory
open ElementaryTypePredicateReadout

abbrev pairedLogic := PredicateDoctrineProduct.higherOrder doctrine doctrine

def name {X : Type} (predicate : pairedLogic.Fiber X) : X ⟶ pairedLogic.generic.object :=
  pairedLogic.generic.characteristic X predicate

theorem complete_classification {X : Type} (predicate : pairedLogic.Fiber X) :
    pairedLogic.reindex (name predicate) pairedLogic.generic.truth = predicate :=
  pairedLogic.generic.classifies X predicate

theorem complete_classification_unique {X : Type} (predicate : pairedLogic.Fiber X)
    (candidate : X ⟶ pairedLogic.generic.object)
    (reading : pairedLogic.reindex candidate pairedLogic.generic.truth = predicate) :
    candidate = name predicate := pairedLogic.generic.unique X predicate candidate reading

theorem name_substitution {X Y : Type} (incoming : X ⟶ Y) (predicate : pairedLogic.Fiber Y) :
    name (pairedLogic.reindex incoming predicate) = incoming ≫ name predicate :=
  pairedLogic.generic.characteristic_reindex incoming predicate

private theorem native_name_true_iff {X : Type} (predicate : Subobject X) (value : X) :
    doctrine.generic.characteristic X predicate value = true ↔ Contains predicate value :=
  TypeSubobjectClassifier.characteristic_true_iff predicate.arrow value

theorem first_name_read {X : Type} (predicate : pairedLogic.Fiber X) (value : X) :
    (name predicate value).1 = true ↔ Contains predicate.1 value := by
  have coordinate := congrArg (fun arrow : X ⟶ Bool => arrow value)
    (PredicateDoctrineProduct.characteristic_first doctrine doctrine predicate)
  change (name predicate value).1 = doctrine.generic.characteristic X predicate.1 value at coordinate
  rw [coordinate]
  exact native_name_true_iff _ _

theorem second_name_read {X : Type} (predicate : pairedLogic.Fiber X) (value : X) :
    (name predicate value).2 = true ↔ Contains predicate.2 value := by
  have coordinate := congrArg (fun arrow : X ⟶ Bool => arrow value)
    (PredicateDoctrineProduct.characteristic_second doctrine doctrine predicate)
  change (name predicate value).2 = doctrine.generic.characteristic X predicate.2 value at coordinate
  rw [coordinate]
  exact native_name_true_iff _ _

def supplied : pairedLogic.Fiber Nat :=
  (fromSet {value | value > 0}, fromSet {value | value > 1})

theorem supplied_complete_read (value : Nat) :
    ((name supplied value).1 = true ↔ value > 0) ∧
      ((name supplied value).2 = true ↔ value > 1) := by
  rw [first_name_read, second_name_read]
  exact ⟨contains_fromSet _ _, contains_fromSet _ _⟩

theorem supplied_has_distinct_intermediate_reading : name supplied 1 = (true, false) := by
  apply Prod.ext
  · exact (supplied_complete_read 1).1.mpr (by decide)
  · apply Bool.eq_false_iff.mpr
    exact (supplied_complete_read 1).2.not.mpr (by decide)

theorem supplied_has_true_reading : name supplied 2 = (true, true) := by
  apply Prod.ext
  · exact (supplied_complete_read 2).1.mpr (by decide)
  · exact (supplied_complete_read 2).2.mpr (by decide)

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem complete_future_read (value : Nat) :
    ((name (pairedLogic.reindex future supplied) value).1 = true ↔ value + 1 > 0) ∧
      ((name (pairedLogic.reindex future supplied) value).2 = true ↔ value + 1 > 1) := by
  rw [name_substitution]
  exact supplied_complete_read (value + 1)

theorem future_changes_the_second_coordinate :
    (name supplied 1).2 = false ∧ (name (pairedLogic.reindex future supplied) 1).2 = true := by
  constructor
  · exact congrArg Prod.snd supplied_has_distinct_intermediate_reading
  · exact (complete_future_read 1).2.mpr (by decide)

def scope {X : Type} (predicate : pairedLogic.Fiber X) : Subobject X :=
  predicate.1 ⊓ predicate.2

theorem scope_read {X : Type} (predicate : pairedLogic.Fiber X) (value : X) :
    Contains (scope predicate) value ↔
      (name predicate value).1 = true ∧ (name predicate value).2 = true :=
  (contains_inf _ _ _).trans (and_congr (first_name_read _ _).symm (second_name_read _ _).symm)

def firstFailure : pairedLogic.Fiber PUnit := (fromSet ∅, fromSet Set.univ)
def secondFailure : pairedLogic.Fiber PUnit := (fromSet Set.univ, fromSet ∅)

theorem failures_are_distinct : firstFailure ≠ secondFailure := by
  intro same
  have firstCoordinate : fromSet (∅ : Set PUnit) = fromSet Set.univ := congrArg Prod.fst same
  have held : Contains (fromSet (Set.univ : Set PUnit)) PUnit.unit :=
    (contains_fromSet _ _).mpr (Set.mem_univ _)
  rw [← firstCoordinate] at held
  exact (contains_fromSet _ _).mp held

theorem truth_scopes_forget_the_failed_coordinate : scope firstFailure = scope secondFailure :=
  inf_comm _ _

theorem scope_does_not_reflect_entailment :
    scope firstFailure ≤ scope secondFailure ∧ ¬ firstFailure ≤ secondFailure := by
  refine ⟨le_of_eq truth_scopes_forget_the_failed_coordinate, ?_⟩
  intro ordered
  have held : Contains (fromSet (Set.univ : Set PUnit)) PUnit.unit :=
    (contains_fromSet _ _).mpr (Set.mem_univ _)
  have lost := (le_iff_contains _ _).mp ordered.2 PUnit.unit held
  exact (contains_fromSet (∅ : Set PUnit) PUnit.unit).mp lost

theorem classified_failures_remain_distinct : name firstFailure ≠ name secondFailure := by
  intro same
  apply failures_are_distinct
  exact (complete_classification firstFailure).symm.trans
    ((congrArg (fun arrow => pairedLogic.reindex arrow pairedLogic.generic.truth) same).trans
      (complete_classification secondFailure))

def pairTruth : PUnit ⟶ (Bool × Bool) := TypeCat.ofHom fun _ => (true, true)

theorem native_truth_is_pair_truth :
    (HigherOrderInternalPredicateObject.operations pairedLogic).truth = pairTruth := by
  ext value
  apply Prod.ext
  · exact (first_name_read (⊤ : pairedLogic.Fiber PUnit) value).mpr (contains_top _)
  · exact (second_name_read (⊤ : pairedLogic.Fiber PUnit) value).mpr (contains_top _)

def emptyInclusion : PEmpty ⟶ PUnit := TypeCat.ofHom PEmpty.elim
def emptyToTruth : PEmpty ⟶ PUnit := TypeCat.ofHom PEmpty.elim
def firstEmptyName : PUnit ⟶ (Bool × Bool) := TypeCat.ofHom fun _ => (false, true)
def secondEmptyName : PUnit ⟶ (Bool × Bool) := TypeCat.ofHom fun _ => (true, false)

instance emptyInclusion_mono : Mono emptyInclusion :=
  (mono_iff_injective _).mpr (fun value => PEmpty.elim value)

theorem first_empty_pullback : IsPullback emptyInclusion emptyToTruth firstEmptyName pairTruth := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext value <;> exact PEmpty.elim value
  · intro value
    exact PEmpty.elim value
  · intro value point same
    have impossible : false = true := congrArg Prod.fst same
    exact Bool.noConfusion impossible

theorem second_empty_pullback : IsPullback emptyInclusion emptyToTruth secondEmptyName pairTruth := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext value <;> exact PEmpty.elim value
  · intro value
    exact PEmpty.elim value
  · intro value point same
    have impossible : false = true := congrArg Prod.snd same
    exact Bool.noConfusion impossible

theorem empty_names_differ : firstEmptyName ≠ secondEmptyName := by
  intro same
  have impossible : false = true := congrArg (fun arrow : PUnit ⟶ (Bool × Bool) =>
    (arrow PUnit.unit).1) same
  exact Bool.noConfusion impossible

/-- The actual native truth has two different characteristic candidates
for one ordinary monomorphism, each with a checked pullback square. -/
theorem native_truth_has_no_unique_empty_characteristic :
    ¬ ∃ characteristic : PUnit ⟶ (Bool × Bool),
      ∀ candidate : PUnit ⟶ (Bool × Bool),
        IsPullback emptyInclusion emptyToTruth candidate
          (HigherOrderInternalPredicateObject.operations pairedLogic).truth →
            candidate = characteristic := by
  rintro ⟨characteristic, unique⟩
  apply empty_names_differ
  rw [native_truth_is_pair_truth] at unique
  exact (unique firstEmptyName first_empty_pullback).trans
    (unique secondEmptyName second_empty_pullback).symm

def opposing : pairedLogic.Fiber Bool :=
  (fromSet {value | value = false}, fromSet {value | value = true})

def forgetBoolean : Bool ⟶ PUnit := TypeCat.ofHom fun _ => PUnit.unit

theorem quantified_coordinates_have_actual_separate_witnesses :
    Contains (pairedLogic.existsAlong forgetBoolean opposing).1 PUnit.unit ∧
      Contains (pairedLogic.existsAlong forgetBoolean opposing).2 PUnit.unit := by
  constructor
  · apply (contains_exists _ _ _).mpr
    exact ⟨false, (contains_fromSet _ _).mpr rfl, rfl⟩
  · apply (contains_exists _ _ _).mpr
    exact ⟨true, (contains_fromSet _ _).mpr rfl, rfl⟩

theorem there_is_no_common_input : ¬ ∃ value, Contains (scope opposing) value := by
  rintro ⟨value, held⟩
  obtain ⟨left, right⟩ := (contains_inf _ _ _).mp held
  have first : value = false := (contains_fromSet {input : Bool | input = false} value).mp left
  have second : value = true := (contains_fromSet {input : Bool | input = true} value).mp right
  exact Bool.noConfusion (first.symm.trans second)

theorem paired_quantification_does_not_create_a_common_witness :
    Contains (scope (pairedLogic.existsAlong forgetBoolean opposing)) PUnit.unit ∧
      ¬ Contains (doctrine.existsAlong forgetBoolean (scope opposing)) PUnit.unit := by
  constructor
  · exact (contains_inf _ _ _).mpr quantified_coordinates_have_actual_separate_witnesses
  · intro held
    obtain ⟨value, witness, _⟩ := (contains_exists _ _ _).mp held
    exact there_is_no_common_input ⟨value, witness⟩

def separateModality : pairedLogic.Fiber PUnit :=
  PositionedRewritePredicateLogic.modality pairedLogic.toFirstOrder (𝟙 Bool) forgetBoolean opposing

def commonModality : Subobject PUnit :=
  PositionedRewritePredicateLogic.modality doctrine.toFirstOrder (𝟙 Bool) forgetBoolean (scope opposing)

theorem separate_modality_evaluation :
    separateModality = pairedLogic.existsAlong forgetBoolean opposing :=
  congrArg (pairedLogic.existsAlong forgetBoolean)
    (pairedLogic.toFirstOrder.forallAlong_id Bool opposing)

theorem common_modality_evaluation :
    commonModality = doctrine.existsAlong forgetBoolean (scope opposing) :=
  congrArg (doctrine.existsAlong forgetBoolean)
    (doctrine.toFirstOrder.forallAlong_id Bool (scope opposing))

theorem the_positioned_modality_comparison_can_be_strict :
    Contains (scope separateModality) PUnit.unit ∧ ¬ Contains commonModality PUnit.unit := by
  rw [separate_modality_evaluation, common_modality_evaluation]
  exact paired_quantification_does_not_create_a_common_witness

def retainedFocus : Bool ⟶ (Bool × Nat) := TypeCat.ofHom fun value => (value, 3)

instance retainedFocus_mono : Mono retainedFocus :=
  (mono_iff_injective _).mpr fun _ _ same => congrArg Prod.fst same

def sharedCondition : pairedLogic.Fiber Bool :=
  (fromSet Set.univ, fromSet {value | value = true})

def pairedRetainedModality : pairedLogic.Fiber (Bool × Nat) :=
  PositionedRewritePredicateLogic.modality pairedLogic.toFirstOrder (𝟙 Bool) retainedFocus sharedCondition

def commonRetainedModality : Subobject (Bool × Nat) :=
  PositionedRewritePredicateLogic.modality doctrine.toFirstOrder (𝟙 Bool) retainedFocus (scope sharedCondition)

theorem common_retained_modality_evaluation :
    commonRetainedModality = doctrine.existsAlong retainedFocus (scope sharedCondition) :=
  congrArg (doctrine.existsAlong retainedFocus)
    (doctrine.toFirstOrder.forallAlong_id Bool (scope sharedCondition))

theorem the_injective_focus_retains_the_common_input :
    commonRetainedModality = scope pairedRetainedModality :=
  PredicateDoctrineProductAgreement.modality_simultaneous_eq_of_mono
    doctrine.toFirstOrder (𝟙 Bool) retainedFocus sharedCondition

theorem the_common_input_has_a_proper_native_postcondition :
    Contains commonRetainedModality (true, 3) ∧
      ¬ Contains commonRetainedModality (false, 3) := by
  rw [common_retained_modality_evaluation]
  constructor
  · apply (contains_exists _ _ _).mpr
    refine ⟨true, (contains_inf _ _ _).mpr ?_, rfl⟩
    exact ⟨(contains_fromSet _ _).mpr (Set.mem_univ _),
      (contains_fromSet {input : Bool | input = true} true).mpr rfl⟩
  · intro held
    obtain ⟨value, witness, reaches⟩ := (contains_exists _ _ _).mp held
    have positive : value = true :=
      (contains_fromSet {input : Bool | input = true} value).mp
        ((contains_inf _ _ _).mp witness).2
    have negative : value = false := congrArg Prod.fst reaches
    exact Bool.noConfusion (negative.symm.trans positive)

end Mettapedia.GSLT.Core.PredicateDoctrineProductControls

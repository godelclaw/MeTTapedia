import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateControls

/-!
# Whole quantified functions through a nonidentity weak closed map

The actual lift functor has wrapped objects and distinct product/function
presentations. Its finite-limit and canonical closed comparisons transport
the complete proper Boolean/number predicate. Universal and existential
readings, a changing future parameter and double composition retain their
independent inputs. A constant-truth operation fails the local universal
format by an actual rejected value and complete operation uniqueness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.InternalPredicateQuantifiedMapControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Mettapedia.CategoryTheory
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps
open HigherOrderInternalPredicateObject ElementaryTypePredicateReadout
open HigherOrderInternalPredicateControls (forgetBoolean suppliedName quantifier existential future)

abbrev logic := ElementaryTypePredicateReadout.doctrine
def quantifiers := HigherOrderInternalPredicateQuantifiedObject.operations logic

private instance identity_closed : MonoidalClosedFunctor (𝟭 Type) :=
  (InternalPredicateQuantifiedObject.Map.identity quantifiers).closed

private instance raised_lex : PreservesFiniteLimits uliftFunctor.{0, 0} :=
  preservesFiniteLimits_of_natIso uliftFunctorTrivial.symm

private instance raised_closed : MonoidalClosedFunctor uliftFunctor.{0, 0} :=
  CartesianClosedFunctorCoherence.closed_of_naturalIso uliftFunctorTrivial

def raisedPredicates : InternalConjunctiveObject.Map quantifiers.predicates quantifiers.predicates where
  functor := uliftFunctor.{0, 0}
  proposition := uliftFunctorTrivial.app quantifiers.predicates.proposition
  truth := by
    have natural := uliftFunctorTrivial.hom.naturality quantifiers.predicates.truth
    exact natural.trans (congrArg (fun arrow => arrow ≫ quantifiers.predicates.truth)
      (toUnit_unique (uliftFunctorTrivial.hom.app (𝟙_ Type)) (toUnit _)))
  conjunction := by
    have tuple : uliftFunctorTrivial.hom.app
        (quantifiers.predicates.proposition ⊗ quantifiers.predicates.proposition) =
      CartesianMonoidalCategory.lift
        (uliftFunctor.map (fst quantifiers.predicates.proposition quantifiers.predicates.proposition) ≫
          uliftFunctorTrivial.hom.app quantifiers.predicates.proposition)
        (uliftFunctor.map (snd quantifiers.predicates.proposition quantifiers.predicates.proposition) ≫
          uliftFunctorTrivial.hom.app quantifiers.predicates.proposition) := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (uliftFunctorTrivial.hom.naturality (fst _ _)).symm.trans
          (CartesianMonoidalCategory.lift_fst _ _).symm
      · exact (uliftFunctorTrivial.hom.naturality (snd _ _)).symm.trans
          (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (uliftFunctorTrivial.hom.naturality quantifiers.predicates.conjunction).trans
      (congrArg (fun arrow => arrow ≫ quantifiers.predicates.conjunction) tuple)

def raised : InternalPredicateQuantifiedObject.Map quantifiers quantifiers where
  predicates := raisedPredicates
  finite := raised_lex
  closed := raised_closed

def suppliedImage : ULift.{0} Nat ⟶ power quantifiers.predicates (ULift.{0} Bool) :=
  sectionImage raised.predicates suppliedName

def universalOutput : ULift.{0} Nat ⟶ power quantifiers.predicates (ULift.{0} PUnit) :=
  suppliedImage ≫ (quantifiers.universal (uliftFunctor.map forgetBoolean)).operation

def existentialOutput : ULift.{0} Nat ⟶ power quantifiers.predicates (ULift.{0} PUnit) :=
  suppliedImage ≫ (quantifiers.existential (uliftFunctor.map forgetBoolean)).operation

theorem universalOutput_compared :
    universalOutput = sectionImage raised.predicates (suppliedName ≫ quantifier.operation) :=
  (raised.universal_section forgetBoolean suppliedName).symm

theorem existentialOutput_compared :
    existentialOutput = sectionImage raised.predicates (suppliedName ≫ existential.operation) :=
  (raised.existential_section forgetBoolean suppliedName).symm

private theorem productInverse (first second : Type) :
    inv (CartesianMonoidalCategory.prodComparison uliftFunctor.{0, 0} first second) =
      TypeCat.ofHom (fun point : ULift first × ULift second =>
        ULift.up (point.1.down, point.2.down)) := by
  apply (cancel_mono (CartesianMonoidalCategory.prodComparison uliftFunctor first second)).mp
  rw [IsIso.inv_hom_id]
  ext point <;> rfl

theorem sectionImage_point {value parameter : Type}
    (predicate : parameter ⟶ power quantifiers.predicates value) (input : value) (argument : parameter) :
    uncurry (sectionImage raised.predicates predicate)
        (ULift.up input, ULift.up argument) =
      uncurry predicate (input, argument) := by
  have complete := congrArg
    (fun arrow : ULift.{0} value ⊗ ULift.{0} parameter ⟶ quantifiers.predicates.proposition =>
      arrow (ULift.up input, ULift.up argument)) (sectionImage_read raised.predicates predicate)
  change uncurry (sectionImage raised.predicates predicate)
      (ULift.up input, ULift.up argument) =
    (inv (CartesianMonoidalCategory.prodComparison uliftFunctor value parameter) ≫
      uliftFunctor.map (read quantifiers.predicates predicate) ≫
        (uliftFunctorTrivial.app quantifiers.predicates.proposition).hom)
      (ULift.up input, ULift.up argument) at complete
  rw [productInverse] at complete
  exact complete

theorem sectionImage_family {value parameter : Type}
    (predicate : parameter ⟶ power quantifiers.predicates value) (input : value) (argument : parameter) :
    Contains (family logic (sectionImage raised.predicates predicate))
        (ULift.up input, ULift.up argument) ↔
      Contains (family logic predicate) (input, argument) := by
  change Contains (logic.reindex (read quantifiers.predicates
      (sectionImage raised.predicates predicate)) logic.generic.truth) (ULift.up input, ULift.up argument) ↔
    Contains (logic.reindex (read quantifiers.predicates predicate) logic.generic.truth) (input, argument)
  rw [contains_reindex, contains_reindex]
  exact Iff.of_eq (congrArg (fun point : logic.generic.object =>
    Contains logic.generic.truth point) (sectionImage_point predicate input argument))

theorem whole_universal_read (parameter : Nat) :
    Contains (family logic universalOutput) (ULift.up PUnit.unit, ULift.up parameter) ↔ parameter > 1 := by
  rw [universalOutput_compared, sectionImage_family]
  exact HigherOrderInternalPredicateControls.complete_output_read parameter

theorem whole_existential_differs :
    Contains (family logic existentialOutput) (ULift.up PUnit.unit, ULift.up 1) ∧
      ¬ Contains (family logic universalOutput) (ULift.up PUnit.unit, ULift.up 1) := by
  rw [existentialOutput_compared, universalOutput_compared, sectionImage_family, sectionImage_family]
  exact HigherOrderInternalPredicateControls.the_existential_keeps_an_actual_supplied_coordinate

theorem the_whole_predicate_is_not_a_single_child :
    Contains (family logic suppliedImage) (ULift.up false, ULift.up 1) ∧
      ¬ Contains (family logic universalOutput) (ULift.up PUnit.unit, ULift.up 1) := by
  change Contains (family logic (sectionImage raised.predicates suppliedName))
      (ULift.up false, ULift.up 1) ∧ ¬ Contains (family logic universalOutput) _
  rw [sectionImage_family, universalOutput_compared, sectionImage_family]
  exact HigherOrderInternalPredicateControls.a_single_coordinate_cannot_replace_the_native_quantifier

def futureImage : ULift.{0} Nat ⟶ ULift.{0} Nat := uliftFunctor.map future

theorem actual_future_read (parameter : Nat) :
    Contains (family logic (futureImage ≫ universalOutput))
      (ULift.up PUnit.unit, ULift.up parameter) ↔ parameter + 1 > 1 := by
  rw [family_substitution, contains_reindex]
  change Contains (family logic universalOutput)
    (ULift.up PUnit.unit, ULift.up (parameter + 1)) ↔ parameter + 1 > 1
  exact whole_universal_read (parameter + 1)

theorem actual_future_changes_admission :
    ¬ Contains (family logic universalOutput) (ULift.up PUnit.unit, ULift.up 1) ∧
      Contains (family logic (futureImage ≫ universalOutput)) (ULift.up PUnit.unit, ULift.up 1) := by
  rw [whole_universal_read, actual_future_read]
  exact ⟨Nat.lt_irrefl 1, by omega⟩

def twice := InternalPredicateQuantifiedObject.Map.comp raised raised

def doubleOutput : ULift.{0} (ULift.{0} Nat) ⟶ power quantifiers.predicates (ULift.{0} (ULift.{0} PUnit)) :=
  sectionImage twice.predicates suppliedName ≫
    (quantifiers.universal (twice.functor.map forgetBoolean)).operation

theorem double_complete_read (parameter : Nat) :
    Contains (family logic doubleOutput)
        (ULift.up (ULift.up PUnit.unit), ULift.up (ULift.up parameter)) ↔ parameter > 1 := by
  have compared : doubleOutput = sectionImage twice.predicates
      (suppliedName ≫ quantifier.operation) := (twice.universal_section forgetBoolean suppliedName).symm
  rw [compared]
  change Contains (family logic (sectionImage
    (InternalPredicateQuantifiedObject.Map.comp raised raised).predicates
      (suppliedName ≫ quantifier.operation))) _ ↔ _
  rw [InternalPredicateQuantifiedObject.Map.sectionImage_comp,
    sectionImage_family, sectionImage_family]
  exact HigherOrderInternalPredicateControls.complete_output_read parameter

def constantTruth : power quantifiers.predicates (ULift.{0} Bool) ⟶
    power quantifiers.predicates (ULift.{0} PUnit) :=
  curry (logic.generic.characteristic _ ⊤)

theorem constantTruth_family : family logic constantTruth = ⊤ := by
  change logic.reindex (uncurry (curry (logic.generic.characteristic _ ⊤))) logic.generic.truth = ⊤
  rw [uncurry_curry]
  exact logic.generic.classifies _ _

theorem constantTruth_applied : family logic (suppliedImage ≫ constantTruth) = ⊤ := by
  rw [family_substitution, constantTruth_family, logic.reindex_top]

theorem constantTruth_is_not_the_actual_quantifier :
    constantTruth ≠ (quantifiers.universal (uliftFunctor.map forgetBoolean)).operation := by
  intro same
  have admitted : Contains (family logic (suppliedImage ≫ constantTruth))
      (ULift.up PUnit.unit, ULift.up 1) :=
    constantTruth_applied.symm ▸ contains_top (ULift.up PUnit.unit, ULift.up 1)
  have complete := congrArg (fun arrow =>
    Contains (family logic (suppliedImage ≫ arrow)) (ULift.up PUnit.unit, ULift.up 1)) same
  exact ((whole_universal_read 1).not.mpr (Nat.lt_irrefl 1)) (complete.mp admitted)

theorem constantTruth_fails_the_three_local_diagrams :
    ¬ ∃ candidate : InternalPredicateQuantifier.Universal quantifiers.predicates
        (uliftFunctor.map forgetBoolean), candidate.operation = constantTruth := by
  rintro ⟨candidate, reading⟩
  exact constantTruth_is_not_the_actual_quantifier
    (reading.symm.trans (quantifiers.universal_unique (uliftFunctor.map forgetBoolean) candidate))

end Mettapedia.GSLT.Core.InternalPredicateQuantifiedMapControls

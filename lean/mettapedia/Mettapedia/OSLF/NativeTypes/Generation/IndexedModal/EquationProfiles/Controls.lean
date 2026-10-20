import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Tests
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Families
import Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls
import Mettapedia.OSLF.MeTTaIL.Complete.RhoPresented

/-! # Equation-profile response and collection-classifier controls -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Controls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralOccurrenceFrontier Complete
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

private theorem law_neither_nullary {laws : List CollectionLaws.Laws} {source target : Pattern}
    (step : CanonicalBags.LawStep laws source target) :
    (∀ label, source ≠ .apply label []) ∧ (∀ label, target ≠ .apply label []) := by
  cases step <;> constructor <;> intro label equal <;> simp_all

private theorem standard_neither_nullary {laws : List CollectionLaws.Laws} {source target : Pattern}
    (step : CanonicalBags.StandardStep laws [] source target) :
    (∀ label, source ≠ .apply label []) ∧ (∀ label, target ≠ .apply label []) := by
  cases step with
  | law move => exact law_neither_nullary move
  | extrude member => cases member
  | apply inner => constructor <;> intro label equal <;> simp_all
  | lambda inner => constructor <;> intro label equal <;> cases equal
  | multiLambda inner => constructor <;> intro label equal <;> cases equal
  | substBody inner => constructor <;> intro label equal <;> cases equal
  | substReplacement inner => constructor <;> intro label equal <;> cases equal
  | element inner => constructor <;> intro label equal <;> cases equal

open GeneralCompletedFrontierControls

private theorem nullary_of_typed {enabled : Bool} {value : Pattern}
    (object : isObjectPattern value = true)
    (typed : HasType (GeneralPlanEnvironment.environment (request enabled).plan).language
      (request enabled).plan.snapshot.free [] value term) : ∃ label, value = .apply label [] := by
  generalize expectedEq : term = expected at typed
  cases typed with
  | bvar found => simp at found
  | fvar found =>
    change (none : Option TypeExpr) = some _ at found
    cases found
  | constructor member ordinary arguments =>
    have declared : _ ∈ language.terms := member
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl <;> cases arguments <;> exact ⟨_, rfl⟩
  | lambda body => cases expectedEq
  | multiLambda body => cases expectedEq
  | collection elements => cases expectedEq
  | subst body replacement => cases object
  | collectionConstructor member parameters elements =>
    have declared : _ ∈ language.terms := member
    simp only [language, List.mem_cons, List.not_mem_nil, or_false] at declared
    rcases declared with rfl | rfl | rfl <;> cases parameters

private theorem no_law_at_typed {enabled : Bool} {value changed : Pattern}
    (object : isObjectPattern value = true)
    (typed : HasType (GeneralPlanEnvironment.environment (request enabled).plan).language
      (request enabled).plan.snapshot.free [] value term)
    (move : Relation.SymmGen (CanonicalBags.StandardStep [] []) value changed) : False := by
  obtain ⟨label, rfl⟩ := nullary_of_typed object typed
  rcases move with forward | backward
  · exact (standard_neither_nullary forward).1 _ rfl
  · exact (standard_neither_nullary backward).2 _ rfl

theorem conditional_law_impossible (enabled : Bool) {first second : Pattern}
    {receipt : GeneralRuleJobs.Receipt}
    (move : Relation.SymmGen (CanonicalBags.StandardStep
      (Normalized.laws (request enabled).plan) (Normalized.extrusions (request enabled).plan)) first second)
    (fired : GeneralOccurrenceSemantics.Primitive (request enabled).plan [] term first receipt) : False :=
  no_law_at_typed fired.1.2.source_object fired.1.2.source_typed move

/-- Conditional equations and both distinct rule origins are genuine. The
collection laws have no applicable site in these nullary source terms. -/
theorem conditionalCertificate (enabled : Bool) : LocalCertificate (request enabled) where
  commute first second third move equation := by
    rcases equation with ⟨receipt, complete, same⟩ | ⟨receipt, complete, same⟩
    · exact (no_law_at_typed complete.job.2.source_object complete.job.2.source_typed move).elim
    · have targetSorted : OpenPatternWellSorted
          (GeneralPlanEnvironment.environment (request enabled).plan).language
          (request enabled).plan.snapshot.free [] term first := by
        rw [← same, complete.endpoint]
        exact complete.accepted.2.2
      exact (no_law_at_typed targetSorted.2.2.1 targetSorted.1 move).elim
  firing first second receipt move valid := by
    exact (no_law_at_typed valid.1.2.source_object valid.1.2.source_typed move).elim

def allTest (enabled : Bool) : Test (request enabled) :=
  ⟨fun _ => true, fun _ _ _ => rfl⟩

def inputFamily (enabled : Bool) : FamilyParameters Bool where
  inputs := [false, true]
  request _ := request enabled
  target _ := allTest enabled

def completedFamily (enabled : Bool) : (inputFamily enabled).States := fun _ => completed enabled

theorem conditional_family_verified :
    (inputFamily true).check (completedFamily true) = true := by
  apply List.all_eq_true.mpr
  intro input member
  apply ((inputFamily true).response?_exact (completedFamily true) input).mpr
  exact outgoing_modal_separation.1

theorem conditional_family_member : (inputFamily true).Meaning :=
  (inputFamily true).check_sound (completedFamily true) conditional_family_verified

theorem empty_provider_family_refuted : ¬ (inputFamily false).Meaning := by
  apply (inputFamily false).counterexample_sound (completedFamily false)
    (fun _ _ => conditionalCertificate false) (fun _ _ => rfl)
  apply List.any_eq_true.mpr
  refine ⟨false, by simp [inputFamily], ?_⟩
  apply beq_iff_eq.mpr
  change modalReadout .possibility (request false) (completed false) (fun _ => true) = .decided false
  simp only [modalReadout, targets, no_rows_no_answers, List.map_nil, List.any_nil,
    Bool.false_eq_true, if_false, completed_certificate, Bool.and_true]
  have admission : sourceAdmission (request false) = true := by
    simp only [sourceAdmission, Bool.and_eq_true]
    exact ⟨(admitted false).accepted,
      checkOpenPatternWellSorted_complete (admitted false).rootSorted⟩
  rw [admission]
  rfl

/-- Equal targets do not erase the selected authored rule: verification
selects one retained answer but the execution state keeps both origins. -/
theorem equal_target_origins_retained :
    ∃ first ∈ (completed true).answers, ∃ second ∈ (completed true).answers,
      first ≠ second ∧ first.val.target = done ∧ second.val.target = done :=
  distinct_actual_origins

def rhoRequest : Request := ⟨GeneralRho.Standard.plan, [], .base "Proc", .apply "PZero" []⟩

def zero : Pattern := .apply "PZero" []
def output : Pattern := .apply "POutput" [.apply "NQuote" [zero], zero]
def forwardBag : Pattern := .collection .hashBag [zero, output] none
def reverseBag : Pattern := .collection .hashBag [output, zero] none

def collectionClassifier : Test rhoRequest :=
  collectionTest RhoPresented.extrusions_eq
    (fun first second equation => (RhoPresented.noEquations [] (.base "Proc") first second equation).elim)
    (fun value => value == CanonicalBags.lawNormal (Normalized.laws GeneralRho.Standard.plan) forwardBag)

theorem reordered_bags_equal :
    Presented.ModelEquiv rhoRequest.plan [] (.base "Proc") forwardBag reverseBag := by
  apply Relation.EqvGen.rel
  apply Or.inr
  apply CanonicalBags.StandardStep.law
  exact CanonicalBags.LawStep.permute rfl (List.Perm.swap _ _ [])

theorem classifier_ignores_bag_order :
    collectionClassifier.accepts forwardBag = collectionClassifier.accepts reverseBag :=
  collectionClassifier.invariant _ _ reordered_bags_equal

def rawFirstZero : Pattern → Bool
  | .collection .hashBag elements _ => elements.head? == some zero
  | _ => false

theorem raw_shape_does_not_descend :
    ¬ ∀ first second, Presented.ModelEquiv rhoRequest.plan [] (.base "Proc") first second →
      rawFirstZero first = rawFirstZero second := by
  intro invariant
  have wrong := invariant _ _ reordered_bags_equal
  change true = false at wrong
  cases wrong

#guard collectionClassifier.accepts forwardBag
#guard collectionClassifier.accepts reverseBag
#guard rawFirstZero forwardBag
#guard !rawFirstZero reverseBag

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.Controls

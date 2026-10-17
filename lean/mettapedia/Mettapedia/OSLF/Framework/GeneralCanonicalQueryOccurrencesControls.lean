import Mettapedia.OSLF.Framework.GeneralCanonicalQueryOccurrences
import Mettapedia.OSLF.Framework.GeneralCanonicalAgreementControls

/-!
# Controls for ordered query occurrences

The control language has one rule, `Go x ~> y if next(x, y)`. The query runs
from the state after matching `Go a`, where `x` is `a`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.Controls

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.ScopedRuleMatching MeTTaIL.RuleBinding
open MeTTaIL.GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents (RecordedEvent recordedEvents)

def followRule : RewriteRule :=
  { name := "Follow", typeContext := [("x", .base "T"), ("y", .base "T")],
    premises := [.relationQuery "next" [.fvar "x", .fvar "y"]],
    left := .apply "Go" [.fvar "x"], right := .fvar "y",
    bindings := some { dependencies := [("x", []), ("y", [])] } }

def nextSignature : GeneralPremise.Signature := ⟨"next", [.base "T", .base "T"], [.input, .output]⟩

def atom (label : String) : Pattern := .apply label []

/-- Two equal rows from `A`, then a row from `B`. -/
def duplicateProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[nextSignature], [⟨"next", [atom "A", atom "B"]⟩, ⟨"next", [atom "A", atom "B"]⟩,
    ⟨"next", [atom "B", atom "C"]⟩]⟩

theorem duplicate_profile : checkFirstOrderProfile followLanguage duplicateProvider = true := by
  cbv

theorem duplicate_declared :
    (environment followLanguage duplicateProvider).language.rewrites[0]? = some followRule := by
  cbv


/-! ## The state after matching `Go a` -/

def startAssignment (value : Pattern) : Assignment := [("x", ⟨[], 0, value⟩)]

def startBindings (value : Pattern) : Bindings := [("x", value)]

theorem start_state (provider : GeneralPremise.ProviderSnapshot) (value : Pattern)
    (typed : checkOpenPatternWellSorted (environment followLanguage provider).language
      (environment followLanguage provider).free [] (.base "T") value = true) :
    QueryInvariant followLanguage provider followRule [] ["x"] (startAssignment value) (startBindings value) where
  compatible := by
    intro entry member
    simp only [startAssignment, List.mem_singleton] at member
    subst member
    exact ⟨rfl, rfl, by simp [startBindings, Bindings.lookup]⟩
  typed := by
    intro entry member
    simp only [startBindings, List.mem_singleton] at member
    subst member
    exact ⟨.base "T", rfl, checkOpenPatternWellSorted_sound typed⟩
  bound := by
    intro name member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨_, rfl⟩
  names := by
    intro name member
    simpa [startBindings] using member
  unique := by simp [startBindings]

abbrev followArguments : List Pattern := [.fvar "x", .fvar "y"]

abbrev requestFrom (value : Pattern) : GeneralPremise.Query.Request :=
  queryRequest 0 0 followRule [] "next" followArguments (startAssignment value)

/-- The ordered correspondence for the query of `Follow`, from the state after
matching `Go value`. -/
theorem follow_occurrences (provider : GeneralPremise.ProviderSnapshot) (value : Pattern)
    (profile : checkFirstOrderProfile followLanguage provider = true)
    (declared : (environment followLanguage provider).language.rewrites[0]? = some followRule)
    (signatureFound : GeneralPremise.signature? (environment followLanguage provider).provider "next"
      followArguments.length = some nextSignature)
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment followLanguage provider).language followRule []
      followArguments nextSignature.argumentTypes = true)
    (typed : checkOpenPatternWellSorted (environment followLanguage provider).language
      (environment followLanguage provider).free [] (.base "T") value = true) :
    List.Forall₂ (SameOccurrence followLanguage provider followRule [] "next"
        (queryAvailable followArguments nextSignature ["x"]) (request := requestFrom value))
      (GeneralPremise.Query.eventual (environment followLanguage provider) (requestFrom value) .start)
      (recordedEvents (providerRelEnv provider) followLanguage (startBindings value) "next" followArguments) :=
  query_occurrences (FirstOrderProfile.of_check profile) declared rfl signatureFound (by cbv) schemasChecked
    (start_state provider value typed)

theorem follow_results (provider : GeneralPremise.ProviderSnapshot) (value : Pattern)
    (profile : checkFirstOrderProfile followLanguage provider = true)
    (declared : (environment followLanguage provider).language.rewrites[0]? = some followRule)
    (signatureFound : GeneralPremise.signature? (environment followLanguage provider).provider "next"
      followArguments.length = some nextSignature)
    (schemasChecked : GeneralPremise.schemaValuesChecked (environment followLanguage provider).language followRule []
      followArguments nextSignature.argumentTypes = true)
    (typed : checkOpenPatternWellSorted (environment followLanguage provider).language
      (environment followLanguage provider).free [] (.base "T") value = true) :
    List.Forall₂ (fun answer final =>
        QueryInvariant followLanguage provider followRule [] (queryAvailable followArguments nextSignature ["x"])
          (GeneralPremise.Query.Answer.assignment answer) final)
      (GeneralPremise.Query.eventual (environment followLanguage provider) (requestFrom value) .start)
      (Engine.relationQueryStep (providerRelEnv provider) followLanguage (startBindings value) "next"
        followArguments) :=
  query_results (FirstOrderProfile.of_check profile) declared rfl signatureFound (by cbv) schemasChecked
    (start_state provider value typed)

/-! ## Equal rows remain two occurrences -/

theorem duplicate_occurrences :
    List.Forall₂ (SameOccurrence followLanguage duplicateProvider followRule [] "next"
        (queryAvailable followArguments nextSignature ["x"]) (request := requestFrom (atom "A")))
      (GeneralPremise.Query.eventual (environment followLanguage duplicateProvider) (requestFrom (atom "A")) .start)
      (recordedEvents (providerRelEnv duplicateProvider) followLanguage (startBindings (atom "A")) "next"
        followArguments) :=
  follow_occurrences duplicateProvider (atom "A") duplicate_profile duplicate_declared (by cbv) (by cbv) (by cbv)

/-- The event of a row `value` from `A`, at a tuple position. -/
def eventFrom (position : Nat) (value : Pattern) : RecordedEvent :=
  { tuplePosition := position, tuple := [atom "A", value], matchPosition := 0,
    extension := [("y", value)], final := [("y", value), ("x", atom "A")] }

/-- The canonical engine records the two equal rows at tuple positions 0 and 1. -/
theorem duplicate_events :
    recordedEvents (providerRelEnv duplicateProvider) followLanguage (startBindings (atom "A")) "next"
      followArguments = [eventFrom 0 (atom "B"), eventFrom 1 (atom "B")] := by
  cbv

theorem duplicate_position (index : Nat) (within : index < 3) :
    relationPosition duplicateProvider.rows "next" index = index := by
  interval_cases index <;> rfl

/-- **Equal rows stay two occurrences.** The general query machine emits two
answers, for rows 0 and 1. -/
theorem duplicate_answers :
    (GeneralPremise.Query.eventual (environment followLanguage duplicateProvider) (requestFrom (atom "A"))
      .start).map (·.rowIndex) = [0, 1] := by
  have occurrences := duplicate_occurrences
  rw [duplicate_events] at occurrences
  obtain ⟨first, rest, firstSame, restSame, listEq⟩ := List.forall₂_cons_right_iff.mp occurrences
  obtain ⟨second, others, secondSame, othersSame, restEq⟩ := List.forall₂_cons_right_iff.mp restSame
  rw [List.forall₂_nil_right_iff.mp othersSame] at restEq
  rw [listEq, restEq]
  obtain ⟨_, firstFound, _⟩ := firstSame.row
  obtain ⟨_, secondFound, _⟩ := secondSame.row
  have firstPosition := firstSame.position
  have secondPosition := secondSame.position
  rw [duplicate_position _ (List.getElem?_eq_some_iff.mp firstFound).1] at firstPosition
  rw [duplicate_position _ (List.getElem?_eq_some_iff.mp secondFound).1] at secondPosition
  simp only [eventFrom] at firstPosition secondPosition
  simp [← firstPosition, ← secondPosition]

/-! ## Original row positions and filtered tuple positions -/

def otherSignature : GeneralPremise.Signature := ⟨"other", [.base "T", .base "T"], [.input, .output]⟩

/-- A row of another relation precedes the only row of `next`. -/
def interleavedProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[nextSignature, otherSignature], [⟨"other", [atom "A", atom "B"]⟩, ⟨"next", [atom "A", atom "C"]⟩]⟩

theorem interleaved_profile : checkFirstOrderProfile followLanguage interleavedProvider = true := by
  cbv

theorem interleaved_occurrences :
    List.Forall₂ (SameOccurrence followLanguage interleavedProvider followRule [] "next"
        (queryAvailable followArguments nextSignature ["x"]) (request := requestFrom (atom "A")))
      (GeneralPremise.Query.eventual (environment followLanguage interleavedProvider) (requestFrom (atom "A")) .start)
      (recordedEvents (providerRelEnv interleavedProvider) followLanguage (startBindings (atom "A")) "next"
        followArguments) :=
  follow_occurrences interleavedProvider (atom "A") interleaved_profile (by cbv) (by cbv) (by cbv) (by cbv)

theorem interleaved_events :
    recordedEvents (providerRelEnv interleavedProvider) followLanguage (startBindings (atom "A")) "next"
      followArguments = [eventFrom 0 (atom "C")] := by
  cbv

/-- **Positions are translated, not copied.** The canonical tuple position is 0,
while the general answer belongs to provider row 1. -/
theorem interleaved_answers :
    (GeneralPremise.Query.eventual (environment followLanguage interleavedProvider) (requestFrom (atom "A"))
      .start).map (·.rowIndex) = [1] := by
  have occurrences := interleaved_occurrences
  rw [interleaved_events] at occurrences
  obtain ⟨answer, others, same, othersSame, listEq⟩ := List.forall₂_cons_right_iff.mp occurrences
  rw [listEq, List.forall₂_nil_right_iff.mp othersSame]
  obtain ⟨row, found, tuple⟩ := same.row
  have within : answer.rowIndex < 2 := (List.getElem?_eq_some_iff.mp found).1
  have atRow : answer.rowIndex = 1 := by
    rcases (by omega : answer.rowIndex = 0 ∨ answer.rowIndex = 1) with zero | one
    · rw [zero] at found
      cases Option.some.inj found
      simp [eventFrom, atom] at tuple
    · exact one
  simp [atRow]

/-! ## Row order is answer order -/

def forwardProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[nextSignature], [⟨"next", [atom "A", atom "B"]⟩, ⟨"next", [atom "A", atom "C"]⟩]⟩

def backwardProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[nextSignature], [⟨"next", [atom "A", atom "C"]⟩, ⟨"next", [atom "A", atom "B"]⟩]⟩

theorem forward_profile : checkFirstOrderProfile followLanguage forwardProvider = true := by
  cbv

theorem backward_profile : checkFirstOrderProfile followLanguage backwardProvider = true := by
  cbv

theorem y_available : "y" ∈ queryAvailable followArguments nextSignature ["x"] := by
  simp [queryAvailable, followArguments, nextSignature, GeneralPremise.queryOutputNames, Pattern.freeFvarNames]

/-- The value each general answer gives `y`. -/
def outputs {environment : GeneralPremise.Environment} {request : GeneralPremise.Query.Request}
    (answers : List (GeneralPremise.Query.Answer environment request)) : List (Option Pattern) :=
  answers.map fun answer => (lookup answer.assignment "y").map ContextualValue.body

theorem forward_outputs :
    outputs (GeneralPremise.Query.eventual (environment followLanguage forwardProvider) (requestFrom (atom "A"))
      .start) = [some (atom "B"), some (atom "C")] := by
  have results := follow_results forwardProvider (atom "A") forward_profile (by cbv) (by cbv) (by cbv) (by cbv)
  have canonical : Engine.relationQueryStep (providerRelEnv forwardProvider) followLanguage
      (startBindings (atom "A")) "next" followArguments =
        [[("y", atom "B"), ("x", atom "A")], [("y", atom "C"), ("x", atom "A")]] := by
    cbv
  rw [canonical] at results
  obtain ⟨first, rest, firstState, restResults, listEq⟩ := List.forall₂_cons_right_iff.mp results
  obtain ⟨second, others, secondState, othersResults, restEq⟩ := List.forall₂_cons_right_iff.mp restResults
  rw [List.forall₂_nil_right_iff.mp othersResults] at restEq
  rw [listEq, restEq]
  simp only [outputs, List.map_cons, List.map_nil, firstState.lookup_eq y_available,
    secondState.lookup_eq y_available]
  rfl

/-- **Reordering the rows reorders the answers.** -/
theorem backward_outputs :
    outputs (GeneralPremise.Query.eventual (environment followLanguage backwardProvider) (requestFrom (atom "A"))
      .start) = [some (atom "C"), some (atom "B")] := by
  have results := follow_results backwardProvider (atom "A") backward_profile (by cbv) (by cbv) (by cbv) (by cbv)
  have canonical : Engine.relationQueryStep (providerRelEnv backwardProvider) followLanguage
      (startBindings (atom "A")) "next" followArguments =
        [[("y", atom "C"), ("x", atom "A")], [("y", atom "B"), ("x", atom "A")]] := by
    cbv
  rw [canonical] at results
  obtain ⟨first, rest, firstState, restResults, listEq⟩ := List.forall₂_cons_right_iff.mp results
  obtain ⟨second, others, secondState, othersResults, restEq⟩ := List.forall₂_cons_right_iff.mp restResults
  rw [List.forall₂_nil_right_iff.mp othersResults] at restEq
  rw [listEq, restEq]
  simp only [outputs, List.map_cons, List.map_nil, firstState.lookup_eq y_available,
    secondState.lookup_eq y_available]
  rfl

/-! ## An incompatible row is skipped -/

/-- Both `x` and `y` are already bound: `x` to `A`, `y` to `C`. -/
def boundAssignment : Assignment := [("y", ⟨[], 0, atom "C"⟩), ("x", ⟨[], 0, atom "A"⟩)]

def boundBindings : Bindings := [("y", atom "C"), ("x", atom "A")]

theorem bound_state :
    QueryInvariant followLanguage forwardProvider followRule [] ["y", "x"] boundAssignment boundBindings where
  compatible := by
    intro entry member
    simp only [boundAssignment, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl, rfl, by cbv⟩
  typed := by
    intro entry member
    simp only [boundBindings, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨.base "T", rfl, checkOpenPatternWellSorted_sound (by cbv)⟩
    · exact ⟨.base "T", rfl, checkOpenPatternWellSorted_sound (by cbv)⟩
  bound := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_, rfl⟩
  names := by
    intro name member
    simpa [boundBindings] using member
  unique := by simp [boundBindings]

abbrev boundRequest : GeneralPremise.Query.Request :=
  queryRequest 0 0 followRule [] "next" followArguments boundAssignment

theorem bound_occurrences :
    List.Forall₂ (SameOccurrence followLanguage forwardProvider followRule [] "next"
        (queryAvailable followArguments nextSignature ["y", "x"]) (request := boundRequest))
      (GeneralPremise.Query.eventual (environment followLanguage forwardProvider) boundRequest .start)
      (recordedEvents (providerRelEnv forwardProvider) followLanguage boundBindings "next" followArguments) :=
  query_occurrences (FirstOrderProfile.of_check forward_profile) (index := 0) (position := 0) (rule := followRule)
    (relation := "next") (arguments := followArguments) (bound := []) (available := ["y", "x"])
    (signature := nextSignature) (by cbv) rfl (by cbv) (by cbv) (by cbv) bound_state

theorem bound_events :
    recordedEvents (providerRelEnv forwardProvider) followLanguage boundBindings "next" followArguments =
      [{ tuplePosition := 1, tuple := [atom "A", atom "C"], matchPosition := 0, extension := [],
         final := boundBindings }] := by
  cbv

theorem forward_position (index : Nat) (within : index < 2) :
    relationPosition forwardProvider.rows "next" index = index := by
  interval_cases index <;> rfl

/-- **The row that conflicts with `y` contributes nothing; the compatible row is
kept, at its own position.** -/
theorem bound_answers :
    (GeneralPremise.Query.eventual (environment followLanguage forwardProvider) boundRequest .start).map
      (·.rowIndex) = [1] := by
  have occurrences := bound_occurrences
  rw [bound_events] at occurrences
  obtain ⟨answer, others, same, othersSame, listEq⟩ := List.forall₂_cons_right_iff.mp occurrences
  rw [listEq, List.forall₂_nil_right_iff.mp othersSame]
  obtain ⟨_, found, _⟩ := same.row
  have position := same.position
  rw [forward_position _ (List.getElem?_eq_some_iff.mp found).1] at position
  simp [← position]

/-! ## No row, no answer -/

/-- **No row starts at `C`, so neither side has an occurrence.** -/
theorem stuck_answers :
    GeneralPremise.Query.eventual (environment followLanguage forwardProvider) (requestFrom (atom "C")) .start =
      [] := by
  have occurrences := follow_occurrences forwardProvider (atom "C") forward_profile (by cbv) (by cbv) (by cbv)
    (by cbv)
  have none : recordedEvents (providerRelEnv forwardProvider) followLanguage (startBindings (atom "C")) "next"
      followArguments = [] := by
    cbv
  rw [none] at occurrences
  exact List.forall₂_nil_right_iff.mp occurrences

/-! ## Membership agreement is not enough -/

/-- **Negative.** The duplicated environment reads the same provider, yet it
records two events where the general machine emits one answer, so no
one-for-one correspondence exists. -/
theorem membership_admits_no_correspondence :
    ReadsProvider duplicatedFollowEnv followProvider ∧
      ∀ related : GeneralPremise.Query.Answer (environment followLanguage followProvider) (requestFrom (atom "A")) →
          RecordedEvent → Prop,
        ¬ List.Forall₂ related
          (GeneralPremise.Query.eventual (environment followLanguage followProvider) (requestFrom (atom "A")) .start)
          (recordedEvents duplicatedFollowEnv followLanguage (startBindings (atom "A")) "next" followArguments) := by
  refine ⟨duplicated_provider_reads, fun related corresponds => ?_⟩
  have own := follow_occurrences followProvider (atom "A") follow_profile (by cbv) (by cbv) (by cbv) (by cbv)
  have ownEvents : (recordedEvents (providerRelEnv followProvider) followLanguage (startBindings (atom "A")) "next"
      followArguments).length = 1 := by
    cbv
  have doubled : (recordedEvents duplicatedFollowEnv followLanguage (startBindings (atom "A")) "next"
      followArguments).length = 2 := by
    cbv
  have ownLength := own.length_eq
  have otherLength := corresponds.length_eq
  omega

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.Controls

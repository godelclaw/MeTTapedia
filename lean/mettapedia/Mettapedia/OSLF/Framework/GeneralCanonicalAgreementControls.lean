import Mettapedia.OSLF.Framework.GeneralCanonicalNativeTransport
import Mettapedia.OSLF.Framework.GeneralCanonicalQueryOccurrences
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend

/-!
# Controls for the root agreement

Positive: the partial-recursive machine's nineteen rows pass the root profile,
so the general theorem yields, for that language, the agreement that
`Partrec.Comparison` proves by hand.

Negative: a language whose second rule reduces under `F` through a congruence
premise fails the root profile, because its step is not root reduction.

The congruence profile admits that language, and Partrec, so the general and
canonical steps agree for both. A language with a rule whose left side is a bare
metavariable fails the congruence profile: the canonical engine would apply that
rule to terms of every sort, while the general semantics types its captures. A
rule guarded by a freshness premise is admitted.

Queries: a rule guarded by a query of a provided relation is admitted, and the
step it takes in the canonical engine over the provider's rows is a step of the
general semantics. A query of `eq` is refused, because the canonical engine
answers `eq` itself, and so is a provider with a row its signature does not type.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.Controls

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.PartrecMachine (partrecMachine)

theorem partrec_profile : checkRootProfile partrecMachine (.base "Cfg") = true := by
  cbv

theorem partrec_root_plan :
    rootPlan partrecMachine = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan := rfl

/-- The general theorem, instantiated: Partrec's generated step from a
well-sorted configuration is its canonical step. -/
theorem partrec_agreement (bound : List TypeExpr) {source target : Pattern}
    (typed : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound source) :
    (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory bound).Step source target ↔
      (TypeSynthesis.langGSLT partrecMachine).Step source target :=
  (RootProfile.of_check partrec_profile).general_step_iff_canonical
    Engine.RelationEnv.empty bound typed

def congruenceTerms : List GrammarRule := [
  { label := "A", category := "T", params := [], syntaxPattern := [] },
  { label := "B", category := "T", params := [], syntaxPattern := [] },
  { label := "F", category := "T", params := [.simple "x" (.base "T")],
    syntaxPattern := [.nonTerminal "x"] }]

def congruenceRewrites : List RewriteRule := [
  { name := "AB", typeContext := [], premises := [],
    left := .apply "A" [], right := .apply "B" [] },
  { name := "UnderF", typeContext := [("x", .base "T"), ("y", .base "T")],
    premises := [.congruence (.fvar "x") (.fvar "y")],
    left := .apply "F" [.fvar "x"], right := .apply "F" [.fvar "y"] }]

def congruenceLanguage : LanguageDef :=
  LanguageDef.ofCore "UnderF" ["T"] congruenceTerms [] congruenceRewrites

/-- The profile refuses a step that descends through a premise. -/
theorem congruence_refused : checkRootProfile congruenceLanguage (.base "T") = false := by
  cbv

theorem congruence_profile : checkFirstOrderProfile congruenceLanguage = true := by
  cbv

theorem partrec_congruence_profile : checkFirstOrderProfile partrecMachine = true := by
  cbv

/-- The general theorem, instantiated: a step under `F` is the same step in both
semantics. -/
theorem congruence_agreement (bound : List TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan congruenceLanguage).snapshot.language
      (rootPlan congruenceLanguage).snapshot.free bound (.base "T") source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan congruenceLanguage) bound (.base "T")).Step source target ↔
      (TypeSynthesis.langGSLT congruenceLanguage).Step source target :=
  (FirstOrderProfile.of_check congruence_profile).general_step_iff_canonical
    Engine.RelationEnv.empty (ReadsProvider.empty _) bound (.base "T") typed

def bareRewrites : List RewriteRule := [
  { name := "AnyToA", typeContext := [("x", .base "T")], premises := [],
    left := .fvar "x", right := .apply "A" [] }]

def bareLanguage : LanguageDef :=
  LanguageDef.ofCore "Bare" ["T"] congruenceTerms [] bareRewrites

/-- A rule whose left side is a bare metavariable is refused. -/
theorem bare_refused : checkFirstOrderProfile bareLanguage = false := by
  cbv

def freshTerms : List GrammarRule := congruenceTerms ++ [
  { label := "Forget", category := "T", params := [.simple "t" (.base "T")],
    syntaxPattern := [.nonTerminal "t"] }]

/-- `Forget t` reduces to `t` when the name `z` does not occur free in `t`. -/
def freshRewrites : List RewriteRule := [
  { name := "ForgetFresh", typeContext := [("t", .base "T")],
    premises := [.freshness { varName := "z", term := .fvar "t" }],
    left := .apply "Forget" [.fvar "t"], right := .fvar "t" }]

def freshLanguage : LanguageDef :=
  LanguageDef.ofCore "Forget" ["T"] freshTerms [] freshRewrites

/-- A freshness premise with a first-order subject is admitted. -/
theorem fresh_profile : checkFirstOrderProfile freshLanguage = true := by
  cbv

/-- Every Hennessy--Milner native type of the language with a step under `F` is
the same in the general semantics and in the sorted canonical semantics. -/
theorem congruence_native_types (bound : List TypeExpr) {Atom : Type}
    (observes : Atom → Pattern → Prop) (formula : Mettapedia.GSLT.HennessyMilner.Formula Atom Unit)
    (term : Pattern) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (sortedCanonical (FirstOrderProfile.of_check congruence_profile) Engine.RelationEnv.empty
          bound (.base "T"))).satisfies (S := ()) term
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          (canonicalSystem (FirstOrderProfile.of_check congruence_profile) Engine.RelationEnv.empty
            bound (.base "T") observes) formula).pred ↔
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (general congruenceLanguage ⟨[], [], []⟩ bound (.base "T"))).satisfies (S := ()) term
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          (generalSystem (FirstOrderProfile.of_check congruence_profile) bound (.base "T") observes)
          formula).pred :=
  nativeType_iff (FirstOrderProfile.of_check congruence_profile) Engine.RelationEnv.empty
    (ReadsProvider.empty _) bound (.base "T") observes formula term

/-! ## Relation queries -/

def followTerms : List GrammarRule := congruenceTerms ++ [
  { label := "C", category := "T", params := [], syntaxPattern := [] },
  { label := "Go", category := "T", params := [.simple "x" (.base "T")],
    syntaxPattern := [.nonTerminal "x"] }]

/-- `Go x` reduces to `y` when the provider relates `x` to `y`. -/
def followRewrites : List RewriteRule := [
  { name := "Follow", typeContext := [("x", .base "T"), ("y", .base "T")],
    premises := [.relationQuery "next" [.fvar "x", .fvar "y"]],
    left := .apply "Go" [.fvar "x"], right := .fvar "y" }]

def followLanguage : LanguageDef :=
  LanguageDef.ofCore "Follow" ["T"] followTerms [] followRewrites

/-- The provided relation: `A` is followed by `B`, and `B` by `C`. The first
position is an input and the second an output. -/
def followProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"next", [.base "T", .base "T"], [.input, .output]⟩],
    [⟨"next", [.apply "A" [], .apply "B" []]⟩, ⟨"next", [.apply "B" [], .apply "C" []]⟩], []⟩

theorem follow_profile : checkFirstOrderProfile followLanguage followProvider = true := by
  cbv

/-- The general theorem, instantiated: a step guarded by a query is the same step
in both semantics, over the provider's rows. -/
theorem follow_agreement (bound : List TypeExpr) {source target : Pattern}
    (typed : OpenPatternWellSorted (rootPlan followLanguage followProvider).snapshot.language
      (rootPlan followLanguage followProvider).snapshot.free bound (.base "T") source) :
    (GeneralOccurrenceSemantics.gslt (rootPlan followLanguage followProvider) bound (.base "T")).Step
        source target ↔
      (TypeSynthesis.langGSLTUsing (providerRelEnv followProvider) followLanguage).Step source target :=
  (FirstOrderProfile.of_check follow_profile).general_step_iff_canonical (providerRelEnv followProvider)
    (providerRelEnv_reads followProvider) bound (.base "T") typed

/-- The canonical engine follows the row from `A`. -/
theorem follow_reducts :
    ContextualStep.reductsUsing (providerRelEnv followProvider) followLanguage 1
      (.apply "Go" [.apply "A" []]) = [.apply "B" []] := by
  cbv

/-- No row starts at `C`, so `Go C` has no reduct. -/
theorem follow_stuck :
    ContextualStep.reductsUsing (providerRelEnv followProvider) followLanguage 1
      (.apply "Go" [.apply "C" []]) = [] := by
  cbv

/-- Membership agreement admits duplicate rows; it does not imply ordered
enumeration agreement. The canonical engine retains those occurrences. -/
def duplicatedFollowEnv : Engine.RelationEnv where
  tuples relation arguments :=
    let rows := (providerRelEnv followProvider).tuples relation arguments
    rows ++ rows

theorem duplicated_provider_reads : ReadsProvider duplicatedFollowEnv followProvider := by
  intro signature declared arguments tuple
  change tuple ∈ (providerRelEnv followProvider).tuples signature.relation arguments ++
      (providerRelEnv followProvider).tuples signature.relation arguments ↔ _
  simpa only [List.mem_append, or_self] using
    providerRelEnv_reads followProvider signature declared arguments tuple

theorem duplicated_follow_reducts :
    ContextualStep.reductsUsing duplicatedFollowEnv followLanguage 1
      (.apply "Go" [.apply "A" []]) = [.apply "B" [], .apply "B" []] := by
  cbv

/-- Negative: identical relational membership is insufficient to transport
the number of answer occurrences. -/
theorem membership_agreement_does_not_preserve_multiplicity :
    ReadsProvider duplicatedFollowEnv followProvider ∧
      ContextualStep.reductsUsing duplicatedFollowEnv followLanguage 1
        (.apply "Go" [.apply "A" []]) ≠
      ContextualStep.reductsUsing (providerRelEnv followProvider) followLanguage 1
        (.apply "Go" [.apply "A" []]) := by
  refine ⟨duplicated_provider_reads, ?_⟩
  rw [duplicated_follow_reducts, follow_reducts]
  decide

/-- Hence the general semantics, which reads the provider snapshot directly, takes
the step from `Go A` to `B`. -/
theorem follow_general_step :
    (GeneralOccurrenceSemantics.gslt (rootPlan followLanguage followProvider) [] (.base "T")).Step
      (.apply "Go" [.apply "A" []]) (.apply "B" []) := by
  have typed : OpenPatternWellSorted (rootPlan followLanguage followProvider).snapshot.language
      (rootPlan followLanguage followProvider).snapshot.free [] (.base "T") (.apply "Go" [.apply "A" []]) :=
    checkOpenPatternWellSorted_sound (by cbv)
  apply (follow_agreement [] typed).mpr
  apply (TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free _
    (FirstOrderProfile.of_check follow_profile).equationFree _ _).mpr
  refine ⟨1, ContextualStep.mem_rewriteAt_iff_stepAt.mp ?_⟩
  have reducts := follow_reducts
  unfold ContextualStep.reductsUsing at reducts
  rw [reducts]
  exact List.mem_singleton_self _

/-- A query of `eq` is refused. -/
def eqRewrites : List RewriteRule := [
  { name := "Same", typeContext := [("x", .base "T"), ("y", .base "T")],
    premises := [.relationQuery "eq" [.fvar "x", .fvar "y"]],
    left := .apply "Go" [.fvar "x"], right := .fvar "y" }]

def eqLanguage : LanguageDef :=
  LanguageDef.ofCore "Same" ["T"] followTerms [] eqRewrites

def eqProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"eq", [.base "T", .base "T"], [.input, .output]⟩], [⟨"eq", [.apply "A" [], .apply "B" []]⟩], []⟩

theorem eq_refused : checkFirstOrderProfile eqLanguage eqProvider = false := by
  cbv

/-- A row that its signature does not type is refused. -/
def badProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[⟨"next", [.base "T", .base "T"], [.input, .output]⟩],
    [⟨"next", [.apply "A" [], .apply "Missing" []]⟩], []⟩

theorem bad_row_refused : checkFirstOrderProfile followLanguage badProvider = false := by
  cbv

/-- Every Hennessy--Milner native type of the query language is the same in the
general semantics and in the sorted canonical semantics over the provider's rows. -/
theorem follow_native_types (bound : List TypeExpr) {Atom : Type}
    (observes : Atom → Pattern → Prop) (formula : Mettapedia.GSLT.HennessyMilner.Formula Atom Unit)
    (term : Pattern) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (sortedCanonical (FirstOrderProfile.of_check follow_profile) (providerRelEnv followProvider)
          bound (.base "T"))).satisfies (S := ()) term
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          (canonicalSystem (FirstOrderProfile.of_check follow_profile) (providerRelEnv followProvider)
            bound (.base "T") observes) formula).pred ↔
      (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
          (general followLanguage followProvider bound (.base "T"))).satisfies (S := ()) term
        (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
          (generalSystem (FirstOrderProfile.of_check follow_profile) bound (.base "T") observes)
          formula).pred :=
  nativeType_iff (FirstOrderProfile.of_check follow_profile) (providerRelEnv followProvider)
    (providerRelEnv_reads followProvider) bound (.base "T") observes formula term


/-! ## Ordered query occurrences

The rule `Follow` runs its query from the state after matching `Go a`, where `x`
is `a`. The general query machine and the canonical engine produce the same
occurrences, one for one and in order.
-/

section QueryOccurrences

open MeTTaIL.Match MeTTaIL.ScopedRuleMatching MeTTaIL.RuleBinding MeTTaIL.GeneralFirstOrderProjection
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
    ⟨"next", [atom "B", atom "C"]⟩], []⟩

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
  ⟨[nextSignature, otherSignature], [⟨"other", [atom "A", atom "B"]⟩, ⟨"next", [atom "A", atom "C"]⟩], []⟩

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
  ⟨[nextSignature], [⟨"next", [atom "A", atom "B"]⟩, ⟨"next", [atom "A", atom "C"]⟩], []⟩

def backwardProvider : GeneralPremise.ProviderSnapshot :=
  ⟨[nextSignature], [⟨"next", [atom "A", atom "C"]⟩, ⟨"next", [atom "A", atom "B"]⟩], []⟩

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


/-! ### The query machine as a block simulation -/

open Mettapedia.GSLT.Distinction in
/-- **Negative.** The canonical query reaches its two events in one step, while
the query machine's first step reaches a single task. No lockstep simulation
relates the two queries. -/
theorem duplicate_not_lockstep :
    ¬ ∃ related : CanonicalNode →
        QueryNode (environment followLanguage duplicateProvider) (requestFrom (atom "A")) → Prop,
      OrderedSimulation
          (canonicalMachine (recordedEvents (providerRelEnv duplicateProvider) followLanguage
            (startBindings (atom "A")) "next" followArguments))
          (queryMachine (environment followLanguage duplicateProvider) (requestFrom (atom "A"))) related ∧
        related .query .query := by
  rintro ⟨related, simulation, start⟩
  have lengths := (simulation.step start).length_eq
  rw [duplicate_events] at lengths
  simp [canonicalMachine, queryMachine] at lengths

open Mettapedia.GSLT.Distinction in
/-- **Positive.** The saturated query machine is an ordered simulation of the
canonical query, relating the two queries. -/
theorem duplicate_saturated :
    ∃ related, OrderedSimulation
        (canonicalMachine (recordedEvents (providerRelEnv duplicateProvider) followLanguage
          (startBindings (atom "A")) "next" followArguments))
        ((queryMachine (environment followLanguage duplicateProvider) (requestFrom (atom "A"))).saturate
          QueryNode.stable QueryNode.rank) related ∧
      related .query .query := by
  obtain ⟨simulation, start⟩ := admitted_query_saturated (FirstOrderProfile.of_check duplicate_profile)
    duplicate_declared rfl (index := 0) (position := 0) (rule := followRule) (relation := "next")
    (arguments := followArguments) (bound := []) (available := ["x"]) (signature := nextSignature)
    (by cbv) (by cbv) (by cbv) (start_state duplicateProvider (atom "A") (by cbv)) (by cbv)
  exact ⟨_, simulation, start⟩

/-- One saturated step from the query reaches both answers, where one primitive
step reaches one task. -/
theorem duplicate_saturated_step :
    (((queryMachine (environment followLanguage duplicateProvider) (requestFrom (atom "A"))).saturate
      QueryNode.stable QueryNode.rank).step .query).length = 2 := by
  obtain ⟨related, simulation, start⟩ := duplicate_saturated
  rw [← (simulation.step start).length_eq, duplicate_events]
  rfl


/-! ## Rule firings of the root plan, in order -/

theorem duplicate_query_profile : checkQueryProfile followLanguage duplicateProvider = true := by
  cbv

theorem forward_query_profile : checkQueryProfile followLanguage forwardProvider = true := by
  cbv

theorem backward_query_profile : checkQueryProfile followLanguage backwardProvider = true := by
  cbv

theorem go_typed (provider : GeneralPremise.ProviderSnapshot) :
    OpenPatternWellSorted (environment followLanguage provider).language
      (environment followLanguage provider).free [] (.base "T") (.apply "Go" [atom "A"]) :=
  checkOpenPatternWellSorted_sound (by cbv)

/-- The canonical engine fires `Follow` once for each of the two equal rows. -/
theorem duplicate_reducts :
    ContextualStep.reductsUsing (providerRelEnv duplicateProvider) followLanguage 1
      (.apply "Go" [atom "A"]) = [atom "B", atom "B"] := by
  cbv

/-- **Equal firings stay two receipts.** The root plan reads out both firings. -/
theorem duplicate_receipt_targets :
    (GeneralRuleJobExecution.completedReceipts (rootPlan followLanguage duplicateProvider) []
        (.base "T") (.apply "Go" [atom "A"])).map GeneralRuleJobs.Receipt.target =
      [atom "B", atom "B"] := by
  rw [completedReceipts_targets (QueryProfile.of_check duplicate_query_profile) (go_typed _) 0]
  exact duplicate_reducts

/-- **Receipts follow the rows.** Reversing the rows reverses the receipts. -/
theorem forward_receipt_targets :
    (GeneralRuleJobExecution.completedReceipts (rootPlan followLanguage forwardProvider) []
        (.base "T") (.apply "Go" [atom "A"])).map GeneralRuleJobs.Receipt.target =
      [atom "B", atom "C"] := by
  rw [completedReceipts_targets (QueryProfile.of_check forward_query_profile) (go_typed _) 0]
  cbv

theorem backward_receipt_targets :
    (GeneralRuleJobExecution.completedReceipts (rootPlan followLanguage backwardProvider) []
        (.base "T") (.apply "Go" [atom "A"])).map GeneralRuleJobs.Receipt.target =
      [atom "C", atom "B"] := by
  rw [completedReceipts_targets (QueryProfile.of_check backward_query_profile) (go_typed _) 0]
  cbv

/-- **Negative.** A rule that descends through a congruence premise is outside
the query profile. Its child search reads only earlier declarations, while the
canonical engine reads all of them. -/
theorem congruence_query_refused : checkQueryProfile congruenceLanguage ⟨[], [], []⟩ = false := by
  cbv

end QueryOccurrences

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement.Controls

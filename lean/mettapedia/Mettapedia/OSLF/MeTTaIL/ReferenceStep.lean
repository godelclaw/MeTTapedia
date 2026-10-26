import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# The reference step relation

One step of a language is a finite derivation: an authored rule fires on a term, and each of its
premises has evidence. The evidence is data (`Witness`), so steps can be told apart, stored and
checked by computation. The relation (`Step`) is the existence of a valid witness (`StepValid`), and
`checkStep` decides validity (`checkStep_eq_some_iff`).

A witness records:
- for a rule step: the position of the rule in the language, the bindings from matching its left
  side, and the evidence for its premises, in order;
- for a freshness or relation premise: the bindings it produces, which the language's evaluator
  (`premiseStepWithEnv`) must offer;
- for a step premise (a congruence, or a step under premise-local binders): the witness of the step
  of the instantiated source, its target, the bindings from matching the premise target against it,
  and the merged bindings;
- for a quantified premise: the evidence for its body at each element of the collection.

**Scopes.** Every instantiation is scope-correct. A metavariable has a capture depth: the number of
binders above its first binding site, in the rule's left side or in an earlier premise target
(`captureSites`). A value is shifted from its capture depth to the depth where it is used
(`applyBindingsScoped`). A step premise steps at depth `max k c` (`stepDepth`), where `k` is the
number of its local binders and `c` the capture depth of its source metavariable:
- when `c ≤ k`, the source moves under the local binders and is lifted by `k - c`;
- when `c > k`, the source is stepped where it was captured, as an open term.
A congruence premise is the case `k = 0`, and so is a scoped premise without binders. The target's
metavariables are captured at the step depth.

**Quantified premises.** `forAll collection parameter body` holds when the metavariable `collection`
is bound to a closed collection and, at each element, the body holds with `parameter` bound to it.
What the body binds stays inside it: the premise passes its bindings on unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStep

open Syntax Match Engine ContextualStep ReflectiveCanonical ReflectiveSubstitution

/-- **Evidence for a step or a premise**, as data. -/
inductive Witness where
  /-- A freshness or relation premise, with the bindings it produces. -/
  | base (result : Bindings)
  /-- A step premise: the witness of the step of the instantiated source to `candidate`, the bindings
  from matching the premise target against it, and the merged bindings. -/
  | premiseStep (step : Witness) (candidate : Pattern) (matched result : Bindings)
  /-- A rule step: the rule's position in the language, the bindings from matching its left side, and
  the evidence for its premises. -/
  | rule (index : ℕ) (initial : Bindings) (premises : List Witness)
  /-- A quantified premise: evidence for its body at each element of the collection, in order. -/
  | forAll (bodies : List Witness)
  deriving Repr

/-- The premises the language's evaluator decides. -/
def isBase : Premise → Bool
  | .freshness _ | .relationQuery _ _ => true
  | _ => false

/-- Bind a quantified parameter to an element, shadowing any earlier binding of its name. -/
def bindParameter (bindings : Bindings) (parameter : String) (element : Pattern) : Bindings :=
  (parameter, element) :: bindings.filter (·.1 != parameter)

/-! ## Scopes -/

/-- The depth at which a step premise's source is stepped in place: the capture depth of its source
metavariable, or zero for any other source. -/
def inPlaceDepth (sites : Pattern) : Pattern → ℕ
  | .fvar x => (captureDepth x 0 sites).getD 0
  | _ => 0

/-- **The depth at which a step premise steps**: the larger of its number of local binders and the
in-place depth of its source. -/
def stepDepth (sites : Pattern) : Premise → ℕ
  | .congruence source _ => inPlaceDepth sites source
  | .scopedStep premise => max premise.binders.length (inPlaceDepth sites premise.source)
  | _ => 0

/-- The binding sites a premise adds after the ones in `sites`: a step premise's target at its step
depth, and a relation query's arguments. -/
def premiseSites (sites : List Pattern) : Premise → List Pattern
  | .congruence source target =>
      [.multiLambda (stepDepth (.apply "" sites) (.congruence source target)) [] target]
  | .scopedStep premise => [.multiLambda (stepDepth (.apply "" sites) (.scopedStep premise)) [] premise.target]
  | .relationQuery _ arguments => arguments
  | _ => []

/-- **Where a schema binds its metavariables**: the side it matches, then each premise's binding
sites, in order. A metavariable's capture depth is read at its first binding site. -/
def captureSitesOf (matched : Pattern) (premises : List Premise) : Pattern :=
  .apply "" (premises.foldl (fun sites premise => sites ++ premiseSites sites premise) [matched])

/-- Where a rule binds its metavariables. -/
def captureSites (rule : RewriteRule) : Pattern := captureSitesOf rule.left rule.premises

/-- The source and target of a step premise. -/
def stepEndpoints : Premise → Option (Pattern × Pattern)
  | .congruence source target => some (source, target)
  | .scopedStep premise => some (premise.source, premise.target)
  | _ => none

/-! ## Internal boundary policies -/

/-- The presentation policy keeps the literal internal premise boundaries. An equational policy
licenses ordinary matching at an explicitly equivalent presentation; it does not authorize a
normalizer, a typing transport, or a change to the outer rule matcher. -/
inductive InternalBoundaryPolicy where
  | presentation
  | equational (theory : Setoid Pattern)

/-- Ordinary target matching at a presentation related by the selected source theory. -/
def PresentedMatch (theory : Setoid Pattern) (schema value : Pattern) (bindings : Bindings) : Prop :=
  ∃ presented, theory.r value presented ∧ bindings ∈ matchPattern schema presented

/-- A relation query takes an actual provider or builtin tuple, chooses an equivalent tuple
presentation, and uses the ordinary argument matcher and binding merge. Provider dispatch still
receives the original instantiated request. -/
def PresentedQuery (theory : Setoid Pattern) (relEnv : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (relation : String) (arguments : List Pattern) (result : Bindings) : Prop :=
  ∃ tuple ∈ builtinRelationTuples language relation (arguments.map (applyBindings bindings)) ++
      relEnv.tuples relation (arguments.map (applyBindings bindings)),
    ∃ presented, List.Forall₂ theory.r tuple presented ∧
      ∃ extension ∈ matchRelationArgs bindings arguments presented,
        mergeBindings bindings extension = some result

/-! ## Validity -/

mutual
/-- **A valid premise witness**: in a rule with binding sites `sites`, the premise holds from
`bindings`, producing `result`. -/
inductive PremiseValid (relEnv : RelationEnv) (language : LanguageDef) :
    Pattern → Bindings → Premise → Witness → Bindings →
      optParam InternalBoundaryPolicy .presentation → Prop
  | base {sites : Pattern} {bindings result : Bindings} {premise : Premise} :
      isBase premise = true → result ∈ premiseStepWithEnv relEnv language bindings premise →
      PremiseValid relEnv language sites bindings premise (.base result) result
  | step {sites : Pattern} {bindings matched result : Bindings} {premise : Premise}
      {source target candidate : Pattern} {step : Witness} :
      stepEndpoints premise = some (source, target) →
      StepValid relEnv language (applyBindingsScoped sites bindings (stepDepth sites premise) source) step candidate →
      matched ∈ matchPattern target candidate → mergeBindings bindings matched = some result →
      PremiseValid relEnv language sites bindings premise (.premiseStep step candidate matched result) result
  | forAll {sites : Pattern} {bindings : Bindings} {collection parameter : String} {body : Premise}
      {kind : CollType} {elements : List Pattern} {bodies : List Witness} :
      bindings.lookup collection = some (.collection kind elements none) →
      ForAllValid relEnv language sites bindings parameter body elements bodies →
      PremiseValid relEnv language sites bindings (.forAll collection parameter body) (.forAll bodies) bindings
  | equationalFreshness {theory : Setoid Pattern} {sites : Pattern} {bindings result : Bindings}
      {condition : FreshnessCondition} :
      result ∈ premiseStepWithEnv relEnv language bindings (.freshness condition) →
      PremiseValid relEnv language sites bindings (.freshness condition) (.base result) result
        (.equational theory)
  | equationalQuery {theory : Setoid Pattern} {sites : Pattern} {bindings result : Bindings}
      {relation : String} {arguments : List Pattern} :
      PresentedQuery theory relEnv language bindings relation arguments result →
      PremiseValid relEnv language sites bindings (.relationQuery relation arguments) (.base result) result
        (.equational theory)
  | equationalStep {theory : Setoid Pattern} {sites : Pattern} {bindings matched result : Bindings}
      {premise : Premise} {source target redex contractum candidate : Pattern} {step : Witness} :
      stepEndpoints premise = some (source, target) →
      theory.r (applyBindingsScoped sites bindings (stepDepth sites premise) source) redex →
      StepValid relEnv language redex step contractum (.equational theory) →
      theory.r contractum candidate →
      PresentedMatch theory target candidate matched →
      mergeBindings bindings matched = some result →
      PremiseValid relEnv language sites bindings premise (.premiseStep step candidate matched result) result
        (.equational theory)
  | equationalForAll {theory : Setoid Pattern} {sites : Pattern} {bindings : Bindings}
      {collection parameter : String} {body : Premise} {kind : CollType} {elements : List Pattern}
      {bodies : List Witness} :
      bindings.lookup collection = some (.collection kind elements none) →
      ForAllValid relEnv language sites bindings parameter body elements bodies (.equational theory) →
      PremiseValid relEnv language sites bindings (.forAll collection parameter body) (.forAll bodies) bindings
        (.equational theory)

/-- **Valid evidence for a quantified body at each element**: the body holds once the parameter is
bound to the element. What the body binds stays inside it. -/
inductive ForAllValid (relEnv : RelationEnv) (language : LanguageDef) :
    Pattern → Bindings → String → Premise → List Pattern → List Witness →
      optParam InternalBoundaryPolicy .presentation → Prop
  | nil {sites : Pattern} {bindings : Bindings} {parameter : String} {body : Premise} :
      ForAllValid relEnv language sites bindings parameter body [] []
  | cons {sites : Pattern} {bindings result : Bindings} {parameter : String} {body : Premise}
      {element : Pattern} {elements : List Pattern} {witness : Witness} {witnesses : List Witness} :
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result →
      ForAllValid relEnv language sites bindings parameter body elements witnesses →
      ForAllValid relEnv language sites bindings parameter body (element :: elements) (witness :: witnesses)
  | equationalNil {theory : Setoid Pattern} {sites : Pattern} {bindings : Bindings} {parameter : String}
      {body : Premise} :
      ForAllValid relEnv language sites bindings parameter body [] [] (.equational theory)
  | equationalCons {theory : Setoid Pattern} {sites : Pattern} {bindings result : Bindings}
      {parameter : String} {body : Premise} {element : Pattern} {elements : List Pattern}
      {witness : Witness} {witnesses : List Witness} :
      PremiseValid relEnv language sites (bindParameter bindings parameter element) body witness result
        (.equational theory) →
      ForAllValid relEnv language sites bindings parameter body elements witnesses (.equational theory) →
      ForAllValid relEnv language sites bindings parameter body (element :: elements) (witness :: witnesses)
        (.equational theory)

/-- **Valid witnesses for a list of premises**, threading the bindings. -/
inductive PremisesValid (relEnv : RelationEnv) (language : LanguageDef) :
    Pattern → Bindings → List Premise → List Witness → Bindings →
      optParam InternalBoundaryPolicy .presentation → Prop
  | nil {sites : Pattern} (bindings : Bindings) : PremisesValid relEnv language sites bindings [] [] bindings
  | cons {sites : Pattern} {initial middle final : Bindings} {premise : Premise} {premises : List Premise}
      {witness : Witness} {witnesses : List Witness} :
      PremiseValid relEnv language sites initial premise witness middle →
      PremisesValid relEnv language sites middle premises witnesses final →
      PremisesValid relEnv language sites initial (premise :: premises) (witness :: witnesses) final
  | equationalNil {theory : Setoid Pattern} {sites : Pattern} (bindings : Bindings) :
      PremisesValid relEnv language sites bindings [] [] bindings (.equational theory)
  | equationalCons {theory : Setoid Pattern} {sites : Pattern} {initial middle final : Bindings}
      {premise : Premise} {premises : List Premise} {witness : Witness} {witnesses : List Witness} :
      PremiseValid relEnv language sites initial premise witness middle (.equational theory) →
      PremisesValid relEnv language sites middle premises witnesses final (.equational theory) →
      PremisesValid relEnv language sites initial (premise :: premises) (witness :: witnesses) final
        (.equational theory)

/-- **A valid step witness**: the rule at `index` matches the source, its premises hold, and the
target is its right side under the final bindings, instantiated scope-correctly. -/
inductive StepValid (relEnv : RelationEnv) (language : LanguageDef) :
    Pattern → Witness → Pattern → optParam InternalBoundaryPolicy .presentation → Prop
  | rule {source : Pattern} {index : ℕ} {rule : RewriteRule} {initial final : Bindings}
      {witnesses : List Witness} :
      language.rewrites[index]? = some rule →
      initial ∈ matchPatternForRule language rule source →
      PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final →
      StepValid relEnv language source (.rule index initial witnesses)
        (applyBindingsScoped (captureSites rule) final 0 rule.right)
  | equationalRule {theory : Setoid Pattern} {source : Pattern} {index : ℕ} {rule : RewriteRule}
      {initial final : Bindings} {witnesses : List Witness} :
      language.rewrites[index]? = some rule →
      initial ∈ matchPatternForRule language rule source →
      PremisesValid relEnv language (captureSites rule) initial rule.premises witnesses final
        (.equational theory) →
      StepValid relEnv language source (.rule index initial witnesses)
        (applyBindingsScoped (captureSites rule) final 0 rule.right) (.equational theory)
end

/-- The same reference source family with an explicitly selected internal boundary policy. -/
def StepWith (policy : InternalBoundaryPolicy) (relEnv : RelationEnv) (language : LanguageDef)
    (source target : Pattern) : Prop :=
  ∃ witness, StepValid relEnv language source witness target policy

/-- **The reference step relation**: some witness is valid. -/
def Step (relEnv : RelationEnv) (language : LanguageDef) (source target : Pattern) : Prop :=
  ∃ witness, StepValid relEnv language source witness target

theorem stepWith_presentation (relEnv : RelationEnv) (language : LanguageDef) (source target : Pattern) :
    StepWith .presentation relEnv language source target ↔ Step relEnv language source target := Iff.rfl

/-! ## Checking a witness -/

variable (relEnv : RelationEnv) (language : LanguageDef)

mutual
/-- Check a step witness at a source, computing its target. -/
def checkStep (source : Pattern) : Witness → Option Pattern
  | .rule index initial witnesses =>
      match language.rewrites[index]? with
      | none => none
      | some rule =>
          if initial ∈ matchPatternForRule language rule source then
            (checkPremises (captureSites rule) initial rule.premises witnesses).map
              (fun final => applyBindingsScoped (captureSites rule) final 0 rule.right)
          else none
  | _ => none

/-- Check the witnesses of a list of premises, computing the final bindings. -/
def checkPremises (sites : Pattern) (bindings : Bindings) : List Premise → List Witness → Option Bindings
  | [], [] => some bindings
  | premise :: premises, witness :: witnesses =>
      match checkPremise sites bindings premise witness with
      | none => none
      | some middle => checkPremises sites middle premises witnesses
  | _, _ => none

/-- Check a premise witness, computing the bindings it produces. -/
def checkPremise (sites : Pattern) (bindings : Bindings) : Premise → Witness → Option Bindings
  | premise, .base result =>
      if isBase premise = true ∧ result ∈ premiseStepWithEnv relEnv language bindings premise then some result
      else none
  | premise, .premiseStep step candidate matched result =>
      match stepEndpoints premise with
      | none => none
      | some (source, target) =>
          if checkStep (applyBindingsScoped sites bindings (stepDepth sites premise) source) step = some candidate ∧
              matched ∈ matchPattern target candidate ∧ mergeBindings bindings matched = some result then
            some result
          else none
  | .forAll collection parameter body, .forAll bodies =>
      match bindings.lookup collection with
      | some (.collection _ elements none) =>
          if checkForAll sites bindings parameter body elements bodies = true then some bindings else none
      | _ => none
  | _, _ => none

/-- Check the evidence for a quantified body at each element. -/
def checkForAll (sites : Pattern) (bindings : Bindings) (parameter : String) (body : Premise) :
    List Pattern → List Witness → Bool
  | [], [] => true
  | element :: elements, witness :: witnesses =>
      (checkPremise sites (bindParameter bindings parameter element) body witness).isSome &&
        checkForAll sites bindings parameter body elements witnesses
  | _, _ => false
end

/-! ## The checker decides validity -/

mutual
theorem checkStep_eq_some_iff : ∀ (witness : Witness) {source target : Pattern},
    checkStep relEnv language source witness = some target ↔ StepValid relEnv language source witness target
  | .rule index initial witnesses, source, target => by
    constructor
    · intro checked
      simp only [checkStep] at checked
      split at checked
      · cases checked
      · rename_i rule found
        split at checked
        · rename_i matched
          obtain ⟨final, premisesChecked, rfl⟩ := Option.map_eq_some_iff.mp checked
          exact .rule found matched ((checkPremises_eq_some_iff witnesses).mp premisesChecked)
        · cases checked
    · intro valid
      cases valid with
      | rule found matched premises =>
        simp only [checkStep, found, matched, ↓reduceIte,
          (checkPremises_eq_some_iff witnesses).mpr premises, Option.map_some]
  | .base _, _, _ => by
    simp only [checkStep, reduceCtorEq, false_iff]
    intro valid
    cases valid
  | .premiseStep _ _ _ _, _, _ => by
    simp only [checkStep, reduceCtorEq, false_iff]
    intro valid
    cases valid
  | .forAll _, _, _ => by
    simp only [checkStep, reduceCtorEq, false_iff]
    intro valid
    cases valid

theorem checkPremises_eq_some_iff : ∀ (witnesses : List Witness) {sites : Pattern} {bindings final : Bindings}
    {premises : List Premise},
    checkPremises relEnv language sites bindings premises witnesses = some final ↔
      PremisesValid relEnv language sites bindings premises witnesses final
  | [], sites, bindings, final, premises => by
    cases premises with
    | nil =>
      simp only [checkPremises, Option.some.injEq]
      constructor
      · rintro rfl
        exact .nil bindings
      · intro valid
        cases valid
        rfl
    | cons premise premises =>
      simp only [checkPremises, reduceCtorEq, false_iff]
      intro valid
      cases valid
  | witness :: witnesses, sites, bindings, final, premises => by
    cases premises with
    | nil =>
      simp only [checkPremises, reduceCtorEq, false_iff]
      intro valid
      cases valid
    | cons premise premises =>
      simp only [checkPremises]
      constructor
      · intro checked
        split at checked
        · cases checked
        · rename_i middle premiseChecked
          exact .cons ((checkPremise_eq_some_iff witness).mp premiseChecked)
            ((checkPremises_eq_some_iff witnesses).mp checked)
      · intro valid
        cases valid with
        | cons first rest =>
          rw [(checkPremise_eq_some_iff witness).mpr first]
          exact (checkPremises_eq_some_iff witnesses).mpr rest

theorem checkPremise_eq_some_iff : ∀ (witness : Witness) {sites : Pattern} {bindings result : Bindings}
    {premise : Premise},
    checkPremise relEnv language sites bindings premise witness = some result ↔
      PremiseValid relEnv language sites bindings premise witness result
  | .base produced, sites, bindings, result, premise => by
    simp only [checkPremise]
    constructor
    · intro checked
      split at checked
      · rename_i holds
        cases checked
        exact .base holds.1 holds.2
      · cases checked
    · intro valid
      cases valid with
      | base baseCase member => simp [baseCase, member]
  | .premiseStep step candidate matched produced, sites, bindings, result, premise => by
    simp only [checkPremise]
    constructor
    · intro checked
      split at checked
      · cases checked
      · rename_i source target endpoints
        split at checked
        · rename_i holds
          cases checked
          exact .step endpoints ((checkStep_eq_some_iff step).mp holds.1) holds.2.1 holds.2.2
        · cases checked
    · intro valid
      cases valid with
      | step endpoints stepped matchedMember merged =>
        rw [endpoints]
        simp only
        rw [if_pos ⟨(checkStep_eq_some_iff step).mpr stepped, matchedMember, merged⟩]
  | .rule _ _ _, sites, bindings, result, premise => by
    cases premise <;> simp only [checkPremise, reduceCtorEq, false_iff] <;> intro valid <;> cases valid
  | .forAll bodies, sites, bindings, result, premise => by
    cases premise with
    | forAll collection parameter body =>
      simp only [checkPremise]
      constructor
      · intro checked
        split at checked
        · rename_i kind elements found
          split at checked
          · rename_i bodiesChecked
            cases checked
            exact .forAll found ((checkForAll_eq_true_iff bodies).mp bodiesChecked)
          · cases checked
        · cases checked
      · intro valid
        cases valid with
        | forAll found bodiesValid =>
          rw [found]
          simp only [(checkForAll_eq_true_iff bodies).mpr bodiesValid, ↓reduceIte]
    | freshness _ =>
      simp only [checkPremise, reduceCtorEq, false_iff]
      intro valid
      cases valid
    | relationQuery _ _ =>
      simp only [checkPremise, reduceCtorEq, false_iff]
      intro valid
      cases valid
    | congruence _ _ =>
      simp only [checkPremise, reduceCtorEq, false_iff]
      intro valid
      cases valid
    | scopedStep _ =>
      simp only [checkPremise, reduceCtorEq, false_iff]
      intro valid
      cases valid

theorem checkForAll_eq_true_iff : ∀ (bodies : List Witness) {sites : Pattern} {bindings : Bindings}
    {parameter : String} {body : Premise} {elements : List Pattern},
    checkForAll relEnv language sites bindings parameter body elements bodies = true ↔
      ForAllValid relEnv language sites bindings parameter body elements bodies
  | [], sites, bindings, parameter, body, elements => by
    cases elements with
    | nil =>
      simp only [checkForAll, true_iff]
      exact .nil
    | cons _ _ =>
      simp only [checkForAll, Bool.false_eq_true, false_iff]
      intro valid
      cases valid
  | witness :: witnesses, sites, bindings, parameter, body, elements => by
    cases elements with
    | nil =>
      simp only [checkForAll, Bool.false_eq_true, false_iff]
      intro valid
      cases valid
    | cons element elements =>
      simp only [checkForAll, Bool.and_eq_true, Option.isSome_iff_exists]
      constructor
      · rintro ⟨⟨result, checked⟩, rest⟩
        exact .cons ((checkPremise_eq_some_iff witness).mp checked) ((checkForAll_eq_true_iff witnesses).mp rest)
      · intro valid
        cases valid with
        | cons head tail =>
          exact ⟨⟨_, (checkPremise_eq_some_iff witness).mpr head⟩, (checkForAll_eq_true_iff witnesses).mpr tail⟩
end

/-- **A step is decided by checking its witness.** -/
theorem step_iff_exists_check {source target : Pattern} :
    Step relEnv language source target ↔ ∃ witness, checkStep relEnv language source witness = some target :=
  ⟨fun ⟨witness, valid⟩ => ⟨witness, (checkStep_eq_some_iff relEnv language witness).mpr valid⟩,
    fun ⟨witness, checked⟩ => ⟨witness, (checkStep_eq_some_iff relEnv language witness).mp checked⟩⟩

/-! ## Literal specialization and explicit equation boundaries -/

variable {relEnv language}

private theorem tuple_presented_refl (theory : Setoid Pattern) (tuple : List Pattern) :
    List.Forall₂ theory.r tuple tuple := by
  induction tuple with
  | nil => exact .nil
  | cons value rest ih => exact .cons (theory.iseqv.refl value) ih

private theorem tuple_eq_of_presented {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second)
    {first second : List Pattern} (related : List.Forall₂ theory.r first second) : first = second := by
  induction related with
  | nil => rfl
  | cons same rest ih => exact congrArg₂ List.cons ((literal _ _).mp same) ih

theorem PresentedMatch.of_literal (theory : Setoid Pattern) {schema value : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern schema value) : PresentedMatch theory schema value bindings :=
  ⟨value,theory.iseqv.refl value,matched⟩

theorem PresentedMatch.iff_literal {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second)
    {schema value : Pattern} {bindings : Bindings} :
    PresentedMatch theory schema value bindings ↔ bindings ∈ matchPattern schema value := by
  constructor
  · rintro ⟨presented,same,matched⟩
    cases (literal _ _).mp same
    exact matched
  · exact PresentedMatch.of_literal theory

theorem PresentedQuery.of_literal (theory : Setoid Pattern) {bindings result : Bindings}
    {relation : String} {arguments : List Pattern}
    (member : result ∈ relationQueryStep relEnv language bindings relation arguments) :
    PresentedQuery theory relEnv language bindings relation arguments result := by
  simp only [relationQueryStep,List.mem_flatMap,List.mem_filterMap] at member
  obtain ⟨tuple,provided,extension,matched,merged⟩ := member
  exact ⟨tuple,provided,tuple,tuple_presented_refl theory tuple,extension,matched,merged⟩

theorem PresentedQuery.iff_literal {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second)
    {bindings result : Bindings} {relation : String} {arguments : List Pattern} :
    PresentedQuery theory relEnv language bindings relation arguments result ↔
      result ∈ relationQueryStep relEnv language bindings relation arguments := by
  constructor
  · rintro ⟨tuple,provided,presented,same,extension,matched,merged⟩
    cases tuple_eq_of_presented literal same
    simp only [relationQueryStep,List.mem_flatMap,List.mem_filterMap]
    exact ⟨tuple,provided,extension,matched,merged⟩
  · exact PresentedQuery.of_literal theory

mutual
/-- A literal witness remains valid for an explicit equational internal policy. The original
provider dispatch, witnesses, final bindings and outer rule match are retained. -/
theorem stepValid_equational_of_presentation (theory : Setoid Pattern) :
    ∀ (witness : Witness) {source target : Pattern},
    StepValid relEnv language source witness target →
      StepValid relEnv language source witness target (.equational theory)
  | .rule _ _ witnesses, _, _, valid => by
      cases valid with
      | rule found matched premises =>
          exact .equationalRule found matched (premisesValid_equational_of_presentation theory witnesses premises)
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premiseValid_equational_of_presentation (theory : Setoid Pattern) :
    ∀ (witness : Witness) {sites : Pattern} {initial final : Bindings} {premise : Premise},
    PremiseValid relEnv language sites initial premise witness final →
      PremiseValid relEnv language sites initial premise witness final (.equational theory)
  | .base _, _, _, _, premise, valid => by
      cases valid with
      | base baseCase member =>
          cases premise with
          | freshness condition => exact .equationalFreshness member
          | relationQuery relation arguments =>
              exact .equationalQuery (PresentedQuery.of_literal theory member)
          | _ => cases baseCase
  | .premiseStep step candidate _ _, _, _, _, _, valid => by
      cases valid with
      | step endpoints stepped matched merged =>
          exact .equationalStep endpoints (theory.iseqv.refl _)
            (stepValid_equational_of_presentation theory step stepped) (theory.iseqv.refl _)
            (PresentedMatch.of_literal theory matched) merged
  | .forAll bodies, _, _, _, _, valid => by
      cases valid with
      | forAll selected body =>
          exact .equationalForAll selected (forAllValid_equational_of_presentation theory bodies body)
  | .rule _ _ _, _, _, _, _, valid => by cases valid

theorem premisesValid_equational_of_presentation (theory : Setoid Pattern) :
    ∀ (witnesses : List Witness) {sites : Pattern} {initial final : Bindings} {premises : List Premise},
    PremisesValid relEnv language sites initial premises witnesses final →
      PremisesValid relEnv language sites initial premises witnesses final (.equational theory)
  | [], _, _, _, _, valid => by
      cases valid
      exact .equationalNil _
  | witness :: witnesses, _, _, _, _, valid => by
      cases valid with
      | cons first rest =>
          exact .equationalCons (premiseValid_equational_of_presentation theory witness first)
            (premisesValid_equational_of_presentation theory witnesses rest)

theorem forAllValid_equational_of_presentation (theory : Setoid Pattern) :
    ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings} {parameter : String}
      {body : Premise} {elements : List Pattern},
    ForAllValid relEnv language sites bindings parameter body elements witnesses →
      ForAllValid relEnv language sites bindings parameter body elements witnesses (.equational theory)
  | [], _, _, _, _, _, valid => by
      cases valid
      exact .equationalNil
  | witness :: witnesses, _, _, _, _, _, valid => by
      cases valid with
      | cons first rest =>
          exact .equationalCons (premiseValid_equational_of_presentation theory witness first)
            (forAllValid_equational_of_presentation theory witnesses rest)
end

mutual
/-- If the selected source theory is equality, the equational policy has exactly the literal
witnesses. This includes recursive child steps and local quantifier rebinding. -/
theorem stepValid_presentation_of_equational {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second) :
    ∀ (witness : Witness) {source target : Pattern},
    StepValid relEnv language source witness target (.equational theory) →
      StepValid relEnv language source witness target
  | .rule _ _ witnesses, _, _, valid => by
      cases valid with
      | equationalRule found matched premises =>
          exact .rule found matched (premisesValid_presentation_of_equational literal witnesses premises)
  | .base _, _, _, valid => by cases valid
  | .premiseStep _ _ _ _, _, _, valid => by cases valid
  | .forAll _, _, _, valid => by cases valid

theorem premiseValid_presentation_of_equational {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second) :
    ∀ (witness : Witness) {sites : Pattern} {initial final : Bindings} {premise : Premise},
    PremiseValid relEnv language sites initial premise witness final (.equational theory) →
      PremiseValid relEnv language sites initial premise witness final
  | .base _, _, _, _, _, valid => by
      cases valid with
      | equationalFreshness member => exact .base rfl member
      | equationalQuery query => exact .base rfl ((PresentedQuery.iff_literal literal).mp query)
  | .premiseStep step candidate _ _, _, _, _, _, valid => by
      cases valid with
      | equationalStep endpoints before stepped after matched merged =>
          have ordinaryStep := stepValid_presentation_of_equational literal step stepped
          rw [← (literal _ _).mp before,(literal _ _).mp after] at ordinaryStep
          exact .step endpoints ordinaryStep ((PresentedMatch.iff_literal literal).mp matched) merged
  | .forAll bodies, _, _, _, _, valid => by
      cases valid with
      | equationalForAll selected body =>
          exact .forAll selected (forAllValid_presentation_of_equational literal bodies body)
  | .rule _ _ _, _, _, _, _, valid => by cases valid

theorem premisesValid_presentation_of_equational {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second) :
    ∀ (witnesses : List Witness) {sites : Pattern} {initial final : Bindings} {premises : List Premise},
    PremisesValid relEnv language sites initial premises witnesses final (.equational theory) →
      PremisesValid relEnv language sites initial premises witnesses final
  | [], _, _, _, _, valid => by
      cases valid
      exact .nil _
  | witness :: witnesses, _, _, _, _, valid => by
      cases valid with
      | equationalCons first rest =>
          exact .cons (premiseValid_presentation_of_equational literal witness first)
            (premisesValid_presentation_of_equational literal witnesses rest)

theorem forAllValid_presentation_of_equational {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second) :
    ∀ (witnesses : List Witness) {sites : Pattern} {bindings : Bindings} {parameter : String}
      {body : Premise} {elements : List Pattern},
    ForAllValid relEnv language sites bindings parameter body elements witnesses (.equational theory) →
      ForAllValid relEnv language sites bindings parameter body elements witnesses
  | [], _, _, _, _, _, valid => by
      cases valid
      exact .nil
  | witness :: witnesses, _, _, _, _, _, valid => by
      cases valid with
      | equationalCons first rest =>
          exact .cons (premiseValid_presentation_of_equational literal witness first)
            (forAllValid_presentation_of_equational literal witnesses rest)
end

theorem stepWith_equational_of_presentation (theory : Setoid Pattern) {source target : Pattern}
    (stepped : Step relEnv language source target) : StepWith (.equational theory) relEnv language source target := by
  obtain ⟨witness,valid⟩ := stepped
  exact ⟨witness,stepValid_equational_of_presentation theory witness valid⟩

theorem stepWith_equational_iff_presentation {theory : Setoid Pattern}
    (literal : ∀ first second, theory.r first second ↔ first = second) {source target : Pattern} :
    StepWith (.equational theory) relEnv language source target ↔ Step relEnv language source target :=
  ⟨fun ⟨witness,valid⟩ => ⟨witness,stepValid_presentation_of_equational literal witness valid⟩,
    stepWith_equational_of_presentation theory⟩

#print axioms stepWith_presentation
#print axioms PresentedMatch.of_literal
#print axioms PresentedMatch.iff_literal
#print axioms PresentedQuery.of_literal
#print axioms PresentedQuery.iff_literal
#print axioms stepValid_equational_of_presentation
#print axioms premiseValid_equational_of_presentation
#print axioms premisesValid_equational_of_presentation
#print axioms forAllValid_equational_of_presentation
#print axioms stepValid_presentation_of_equational
#print axioms premiseValid_presentation_of_equational
#print axioms premisesValid_presentation_of_equational
#print axioms forAllValid_presentation_of_equational
#print axioms stepWith_equational_of_presentation
#print axioms stepWith_equational_iff_presentation

end Mettapedia.OSLF.MeTTaIL.ReferenceStep

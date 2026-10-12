import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# Root relation queries with the complete scoped capture retained

A root query needs only the metavariables occurring in its argument
schemas. Projecting every captured value would wrongly reject an unused
continuation that depends on a local input binder. This interpreter
projects precisely the already-bound names used by the query. Unbound
query names remain available to the existing relation matcher as outputs.
The existing root reconciliation retains the original contextual capture.

Other premise cases use the existing contextual interpreter. Rule and
premise histories, duplicate result positions, binding admission and
target scope checks remain explicit. This is a separate interpreter with
a changed relation-query case, not a reinterpretation of the old adapter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.FocusedRelationQueryExecution

open Syntax RuleBinding ScopedRuleMatching Engine
open ScopedPremiseExecution (StepOracle PremiseEvent RuleFiring RuleHistory)
open Match (Bindings)

def projectNames? (ambient : Nat) (assignment : Assignment) : List String → Option Bindings
  | [] => some []
  | name :: names =>
      match lookup assignment name with
      | none => projectNames? ambient assignment names
      | some value => do
          let projected ← instantiateValue? value ambient 0 []
          let remaining ← projectNames? ambient assignment names
          some ((name, projected) :: remaining)

theorem projectNames?_one_bound (ambient : Nat) (assignment : Assignment)
    (name : String) (value : ContextualValue) (projected : Pattern)
    (found : lookup assignment name = some value)
    (readout : instantiateValue? value ambient 0 [] = some projected) :
    projectNames? ambient assignment [name] = some [(name, projected)] := by
  simp only [projectNames?, found, readout]
  rfl

theorem projectNames?_one_unbound (ambient : Nat) (assignment : Assignment)
    (name : String) (missing : lookup assignment name = none) :
    projectNames? ambient assignment [name] = some [] := by
  simp only [projectNames?, missing]

def queryResults {Evidence : Type} (relEnv : RelationEnv) (language : LanguageDef)
    (spec : RuleBindingSpec) (ambient index : Nat) (relation : String)
    (arguments : List Pattern) (assignment : Assignment) :
    List (PremiseEvent Evidence × Assignment) :=
  if ScopedPremiseExecution.hasOccurrenceAt spec index then [] else
  match projectNames? ambient assignment (arguments.flatMap Pattern.freeFvarNames).eraseDups with
  | none => []
  | some root =>
      (relationQueryStep relEnv language root relation arguments).zipIdx.filterMap fun
        (result, resultIndex) => do
          let completed ← extendRoot? spec ambient assignment result
          some (.root index resultIndex, completed)

theorem queryResults_readout {Evidence : Type} (relEnv : RelationEnv)
    (language : LanguageDef) (spec : RuleBindingSpec) (ambient index : Nat)
    (relation : String) (arguments : List Pattern) (assignment completed : Assignment)
    (event : PremiseEvent Evidence)
    (present : (event, completed) ∈ queryResults relEnv language spec ambient index
      relation arguments assignment) :
    ∃ root result resultIndex,
      projectNames? ambient assignment (arguments.flatMap Pattern.freeFvarNames).eraseDups = some root ∧
      (result, resultIndex) ∈ (relationQueryStep relEnv language root relation arguments).zipIdx ∧
      extendRoot? spec ambient assignment result = some completed ∧ event = .root index resultIndex := by
  unfold queryResults at present
  split at present
  · simp at present
  · split at present
    · simp at present
    · rename_i root projected
      obtain ⟨⟨result, resultIndex⟩, member, represented⟩ := List.mem_filterMap.mp present
      change (extendRoot? spec ambient assignment result).bind
        (fun actual => some (PremiseEvent.root index resultIndex, actual)) =
          some (event, completed) at represented
      cases reconciliation : extendRoot? spec ambient assignment result with
      | none => simp [reconciliation] at represented
      | some actual =>
        rw [reconciliation] at represented
        change some (PremiseEvent.root index resultIndex, actual) = some (event, completed) at represented
        have represented := Prod.mk.inj (Option.some.inj represented)
        exact ⟨root, result, resultIndex, projected, member,
          represented.2 ▸ reconciliation, represented.1.symm⟩

def premiseResults {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat) (premise : Premise)
    (assignment : Assignment) : List (PremiseEvent Evidence × Assignment) :=
  match premise with
  | .relationQuery relation arguments =>
      queryResults relEnv language spec ambient index relation arguments assignment
  | other => ScopedPremiseExecution.premiseResults oracle relEnv language rule spec
      ambient index other assignment

def runPremises {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) :
    Nat → List Premise → Assignment → List (Assignment × List (PremiseEvent Evidence))
  | _, [], assignment => [(assignment, [])]
  | index, premise :: rest, assignment =>
      (premiseResults oracle relEnv language rule spec ambient index premise assignment).flatMap fun
        (event, completed) =>
          (runPremises oracle relEnv language rule spec ambient (index + 1) rest completed).map fun
            (final, history) => (final, event :: history)

theorem runPremises_history_length {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat) (premises : List Premise)
    (initial final : Assignment) (history : List (PremiseEvent Evidence))
    (present : (final, history) ∈ runPremises oracle relEnv language rule spec
      ambient index premises initial) : history.length = premises.length := by
  induction premises generalizing index initial final history with
  | nil =>
    simp only [runPremises, List.mem_singleton, Prod.mk.injEq] at present
    exact present.2.symm ▸ rfl
  | cons premise rest inductionHypothesis =>
    simp only [runPremises, List.mem_flatMap, List.mem_map] at present
    obtain ⟨⟨event, completed⟩, _, ⟨next, tail⟩, tailPresent, represented⟩ := present
    cases represented
    simp [inductionHypothesis (index := index + 1) (initial := completed)
      (final := next) (history := tail) tailPresent]

/-- A singleton premise run exposes the selected query event and its whole
completed contextual assignment. -/
theorem runPremises_singleton_iff {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat) (premise : Premise)
    (initial final : Assignment) (history : List (PremiseEvent Evidence)) :
    (final, history) ∈ runPremises oracle relEnv language rule spec ambient index [premise] initial ↔
      ∃ event, (event, final) ∈ premiseResults oracle relEnv language rule spec
        ambient index premise initial ∧ history = [event] := by
  simp only [runPremises, List.mem_flatMap, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨⟨event, completed⟩, present, ⟨actual, tail⟩, equal, represented⟩
    cases equal
    cases represented
    exact ⟨event, present, rfl⟩
  · rintro ⟨event, present, rfl⟩
    exact ⟨(event, final), present, (final, []), rfl, rfl⟩

/-- Finishing does not alter the capture, completed assignment, or ordered
history supplied by the interpreter. -/
theorem finish_readout {Evidence : Type} (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) (captured completed : Assignment)
    (history : List (PremiseEvent Evidence)) (firing : RuleFiring Evidence)
    (finished : ScopedPremiseExecution.finish? rule spec ambient captured completed history = some firing) :
    firing.captured = captured ∧ firing.completed = completed ∧ firing.history = history ∧
      reduct? rule spec ambient completed = some firing.target := by
  unfold ScopedPremiseExecution.finish? at finished
  cases reading : reduct? rule spec ambient completed with
  | none => simp [reading] at finished
  | some target =>
      by_cases wellScoped : target.isWellScopedAt ambient = true
      · simp [reading, wellScoped] at finished
        cases finished
        exact ⟨rfl, rfl, rfl, rfl⟩
      · simp [reading, wellScoped] at finished

def applyRuleWithOracle {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (ambient : Nat)
    (rule : RewriteRule) (source : Pattern) : List (RuleFiring Evidence) :=
  match rule.bindings with
  | none => []
  | some spec =>
      if admittedFor rule spec then
        (matchRuleAt rule spec ambient source).flatMap fun captured =>
          (runPremises oracle relEnv language rule spec ambient 0 rule.premises captured).filterMap fun
            (completed, history) =>
              ScopedPremiseExecution.finish? rule spec ambient captured completed history
      else []

theorem mem_applyRuleWithOracle_iff {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (source : Pattern) (firing : RuleFiring Evidence) :
    firing ∈ applyRuleWithOracle oracle relEnv language ambient rule source ↔
      ∃ spec captured completed history,
        rule.bindings = some spec ∧ admittedFor rule spec = true ∧
        captured ∈ matchRuleAt rule spec ambient source ∧
        (completed, history) ∈ runPremises oracle relEnv language rule spec ambient 0 rule.premises captured ∧
        ScopedPremiseExecution.finish? rule spec ambient captured completed history = some firing := by
  cases declared : rule.bindings with
  | none => simp [applyRuleWithOracle, declared]
  | some spec =>
    by_cases admitted : admittedFor rule spec = true
    · simp only [applyRuleWithOracle, declared, admitted, if_true, List.mem_flatMap, List.mem_filterMap]
      constructor
      · rintro ⟨captured, matched, ⟨completed, history⟩, ran, finished⟩
        exact ⟨spec, captured, completed, history, rfl, admitted, matched, ran, finished⟩
      · rintro ⟨chosen, captured, completed, history, declaration, _, matched, ran, finished⟩
        cases Option.some.inj declaration
        exact ⟨captured, matched, (completed, history), ran, finished⟩
    · have rejected : admittedFor rule spec = false := Bool.eq_false_iff.mpr admitted
      simp [applyRuleWithOracle, declared, rejected]

theorem applyRuleWithOracle_scoped {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef) (ambient : Nat) (rule : RewriteRule)
    (source : Pattern) (firing : RuleFiring Evidence)
    (present : firing ∈ applyRuleWithOracle oracle relEnv language ambient rule source) :
    firing.target.isWellScopedAt ambient = true := by
  obtain ⟨spec, captured, completed, history, _, _, _, _, finished⟩ :=
    (mem_applyRuleWithOracle_iff oracle relEnv language ambient rule source firing).mp present
  exact ScopedPremiseExecution.finish?_scoped rule spec ambient captured completed history firing finished

def rewriteAt (relEnv : RelationEnv) (language : LanguageDef) : Nat → StepOracle RuleHistory
  | 0, _, _ => []
  | fuel + 1, ambient, source =>
      language.rewrites.zipIdx.flatMap fun (rule, ruleIndex) =>
        (applyRuleWithOracle (rewriteAt relEnv language fuel) relEnv language ambient rule source).map fun
          firing => (.fire ruleIndex firing.history, firing.target)

theorem mem_rewriteAt_succ_iff (relEnv : RelationEnv) (language : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern) (history : RuleHistory) :
    (history, target) ∈ rewriteAt relEnv language (fuel + 1) ambient source ↔
      ∃ rule ruleIndex, (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧
        ∃ firing ∈ applyRuleWithOracle (rewriteAt relEnv language fuel) relEnv language ambient rule source,
          history = .fire ruleIndex firing.history ∧ target = firing.target := by
  simp only [rewriteAt, List.mem_flatMap, List.mem_map]
  aesop

end Mettapedia.OSLF.MeTTaIL.FocusedRelationQueryExecution

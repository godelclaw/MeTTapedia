import Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire
import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
import Mettapedia.Languages.MeTTa.MeTTaZeroStagedAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.PatternRewrite.Space

/-!
# PeTTa interprets and extends the query-first MeTTa Zero kernel

PeTTa's existing atomspace semantics supplies an exact occurrence-bag model of
the query-first kernel:

* the reflective medium is `PeTTaSpace.storedAtoms`;
* public query is the multiset quotient of `PeTTaSpace.spaceMatch`;
* the matcher is the existing `matchPattern`;
* the grounding portal remains a parameter, because PeTTa grounding is a
  larger library boundary than the pure space semantics in this module.

The query correspondence is exact modulo enumeration order.  For evaluation we
prove the direction justified by the current PeTTa specification: every
premise-free `PeTTaEval.ruleApp` result is produced by the Zero evaluator after
the corresponding equation atom has been obtained through public query.
PeTTa adds `superpose`, `collapse`, effects, typing, and further evaluation
cases, so no converse for the whole dialect is asserted.

The existing MORK/MM2 theorem then receives the same arbitrary-atom query
fragment.  Its workspace is set-valued, so that bridge preserves query
support, not occurrence multiplicity.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-! ## Exact PeTTa model -/

/-- PeTTa's real stored-atom list and matcher instantiate the kernel. -/
abbrev model (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    MeTTaZero.Model where
  Space := PeTTaSpace
  contents := fun space => space.storedAtoms
  matchAtoms := fun pattern atom => matchPattern pattern atom
  groundApply := groundApply

theorem model_lawful (groundApply : Pattern → Multiset Pattern) :
    MeTTaZero.Lawful (model groundApply) := by
  constructor
  intro name atom
  simp [matchPattern]

/-- **Exact occurrence-bag query interpretation.**  The only quotient forgets
PeTTa's enumeration order; it preserves every occurrence and uses the same
matcher. -/
@[simp] theorem query_eq_spaceMatch (groundApply : Pattern → Multiset Pattern)
    (space : PeTTaSpace) (pattern template : Pattern) :
    MeTTaZero.query (model groundApply) space pattern template =
      (space.spaceMatch pattern template : Multiset Pattern) := by
  simp [MeTTaZero.query, PeTTaSpace.spaceMatch]

/-- Enumerating the public query recovers exactly PeTTa's reflective medium,
including ordinary facts and premise-free equations. -/
@[simp] theorem queryAll_eq_storedAtoms
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace) :
    MeTTaZero.queryAll (model groundApply) space =
      (space.storedAtoms : Multiset Pattern) :=
  MeTTaZero.queryAll_eq_contents _ (model_lawful groundApply) space

/-- PeTTa's declarative `match &self` case computes a list whose occurrence
bag is exactly the Zero query result. -/
theorem petta_spaceQuery_realizes_zero_query
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace)
    (pattern template : Pattern) :
    PeTTaEval space
      (.apply "match" [.apply "&self" [], pattern, template])
      (space.spaceMatch pattern template) ∧
        (space.spaceMatch pattern template : Multiset Pattern) =
          MeTTaZero.query (model groundApply) space pattern template := by
  exact ⟨petta_eval_spaceQuery_correct space pattern template,
    (query_eq_spaceMatch groundApply space pattern template).symm⟩

/-! ## PeTTa query as a certified realization

The theorem above is packaged here in the generic realization class.  The
request indexes both the executable artifact and its observation, so the
artifact carries an actual `PeTTaEval` derivation rather than merely the list
that PeTTa happens to compute. -/

/-- One public query request interpreted by PeTTa. -/
structure QueryRequest where
  space : PeTTaSpace
  /-- The authored term naming this concrete space for relation dispatch. -/
  spaceTerm : Pattern
  pattern : Pattern
  template : Pattern

/-- The executable PeTTa result together with its declarative evaluation
witness. -/
structure QueryArtifact (request : QueryRequest) where
  results : List Pattern
  evaluated : PeTTaEval request.space
    (.apply "match" [.apply "&self" [], request.pattern, request.template])
    results

/-- **PeTTa is a certified realization of Zero's public query operation.**
The named observation forgets only answer enumeration order; coercion to a
multiset retains every occurrence. -/
def queryRealization (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    Realization (fun _ : QueryRequest => Unit) QueryArtifact
      (fun _ => Multiset Pattern) where
  compile := fun request _ =>
    { results := request.space.spaceMatch request.pattern request.template
      evaluated := petta_eval_spaceQuery_correct request.space
        request.pattern request.template }
  observeSource := fun request _ =>
    MeTTaZero.query (model groundApply) request.space
      request.pattern request.template
  observeArtifact := fun _ artifact => artifact.results
  adequate := by
    intro request _
    exact (query_eq_spaceMatch groundApply request.space
      request.pattern request.template).symm

@[simp] theorem queryRealization_observation
    (groundApply : Pattern → Multiset Pattern) (request : QueryRequest) :
    (queryRealization groundApply).observeArtifact request
        ((queryRealization groundApply).compile request ()) =
      MeTTaZero.query (model groundApply) request.space
        request.pattern request.template :=
  (queryRealization groundApply).observe_compile request ()

/-- In particular, PeTTa realizes the complete occurrence count, not merely
the support of the Zero query. -/
theorem queryRealization_preserves_count
    (groundApply : Pattern → Multiset Pattern) (request : QueryRequest)
    (answer : Pattern) :
    Multiset.count answer
        ((queryRealization groundApply).observeArtifact request
          ((queryRealization groundApply).compile request ())) =
      Multiset.count answer
        (MeTTaZero.query (model groundApply) request.space
          request.pattern request.template) := by
  rw [queryRealization_observation]

/-! ## Certified backend choice -/

/-- Remove the public query-result constructor emitted by the authored
five-field executor.  The fallback branch makes this an observation on every
artifact, while the adequacy theorem below uses only constructor-shaped
artifacts produced by that executor. -/
def unwrapQueryAnswer : Pattern → Pattern
  | .apply "zero-query-answer" [answer] => answer
  | artifact => artifact

@[simp] theorem unwrapQueryAnswer_queryAnswerPattern (answer : Pattern) :
    unwrapQueryAnswer (queryAnswerPattern answer) = answer :=
  rfl

/-- The generic premise-aware interpreter over Zero's five-field root,
restricted to PeTTa query requests. -/
noncomputable def authoredQueryRealization
    (groundApply : Pattern → Multiset Pattern := fun _ => 0) :
    Realization (fun _ : QueryRequest => Unit)
      (fun _ => Multiset Pattern) (fun _ => Multiset Pattern) where
  compile := fun request _ =>
    (MeTTaZeroLanguageAdequacy.authoredRealization (model groundApply)).compile ()
      (.query request.space request.spaceTerm request.pattern request.template)
  observeSource := fun request _ =>
    MeTTaZero.query (model groundApply) request.space
      request.pattern request.template
  observeArtifact := fun _ answers => answers.map unwrapQueryAnswer
  adequate := by
    intro request _
    have realized := MeTTaZeroLanguageAdequacy.authoredRealization_query
      (model groundApply) request.space request.spaceTerm request.pattern request.template
    refine (congrArg (Multiset.map unwrapQueryAnswer) realized).trans ?_
    rw [Multiset.map_map]
    have roundtrip : unwrapQueryAnswer ∘ queryAnswerPattern = id :=
      funext unwrapQueryAnswer_queryAnswerPattern
    rw [roundtrip, Multiset.map_id]

/-- Select the generic authored executor or PeTTa's native query evaluator per
request.  The selector is deliberately unconstrained: correctness follows
from the two realization certificates, not from the plan heuristic. -/
noncomputable def hybridQueryRealization
    (groundApply : Pattern → Multiset Pattern := fun _ => 0)
    (useAuthoredExecutor : QueryRequest → Bool) :
    Realization (fun _ : QueryRequest => Unit)
      (fun request => Multiset Pattern ⊕ QueryArtifact request)
      (fun _ => Multiset Pattern) :=
  (authoredQueryRealization groundApply).select
    (queryRealization groundApply)
    (by intro request _; rfl)
    (fun request _ => useAuthoredExecutor request)

theorem hybridQueryRealization_observation
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest) :
    (hybridQueryRealization groundApply useAuthoredExecutor).observeArtifact
        request
        ((hybridQueryRealization groundApply useAuthoredExecutor).compile
          request ()) =
      MeTTaZero.query (model groundApply) request.space
        request.pattern request.template :=
  (hybridQueryRealization groundApply useAuthoredExecutor).observe_compile
    request ()

/-- Positive selection canary: a true plan selects the generic authored
executor artifact. -/
theorem hybridQueryRealization_selects_authored
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest)
    (selected : useAuthoredExecutor request = true) :
    (hybridQueryRealization groundApply useAuthoredExecutor).compile request () =
      .inl ((authoredQueryRealization groundApply).compile request ()) := by
  exact Realization.select_compile_left
    (authoredQueryRealization groundApply) (queryRealization groundApply)
    (by intro indexed _; rfl) (fun indexed _ => useAuthoredExecutor indexed)
    request () selected

/-- Symmetric selection canary for PeTTa's native artifact, which retains its
declarative `PeTTaEval` witness. -/
theorem hybridQueryRealization_selects_petta
    (groundApply : Pattern → Multiset Pattern)
    (useAuthoredExecutor : QueryRequest → Bool) (request : QueryRequest)
    (selected : useAuthoredExecutor request = false) :
    (hybridQueryRealization groundApply useAuthoredExecutor).compile request () =
      .inr ((queryRealization groundApply).compile request ()) := by
  exact Realization.select_compile_right
    (authoredQueryRealization groundApply) (queryRealization groundApply)
    (by intro indexed _; rfl) (fun indexed _ => useAuthoredExecutor indexed)
    request () selected

/-- Every occurrence returned by PeTTa's query is exactly one rewrite of the
Zero query GSLT. -/
theorem petta_query_member_iff_zero_step
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace)
    (pattern template result : Pattern) :
    result ∈ (space.spaceMatch pattern template : Multiset Pattern) ↔
      ∃ occurrence,
        (MeTTaZero.queryGSLT (model groundApply)).Step
          (.request space pattern template)
          (.answer space pattern template occurrence result) := by
  rw [← query_eq_spaceMatch]
  exact MeTTaZero.mem_query_iff_exists_step _ _ _ _ _

/-! ## PeTTa rule application is derived from reflective query -/

/-- A premise-free PeTTa rule is publicly visible as an equation atom. -/
theorem rule_atom_mem_queryAll
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = []) :
    .apply "=" [rule.left, rule.right] ∈
      MeTTaZero.queryAll (model groundApply) space := by
  rw [queryAll_eq_storedAtoms]
  exact PeTTaSpace.mem_storedAtoms_of_premiseFreeRule ruleMember premiseFree

/-- The result of every premise-free PeTTa rule application occurs in the
query-derived equation results.  This is the load-bearing fact: evaluation
does not consult a hidden rule table. -/
theorem ruleApplication_mem_equationResults
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    result ∈
      MeTTaZero.equationResults (model groundApply) space subject := by
  rw [MeTTaZero.mem_equationResults_iff]
  exact
    ⟨.apply "=" [rule.left, rule.right],
      rule_atom_mem_queryAll groundApply ruleMember premiseFree,
      rule.left, rule.right, rfl,
      bindings, matchMember, instantiates⟩

/-- Every PeTTa rule-application result is therefore an answer of the complete
Zero one-step evaluator (with the same optional grounding portal). -/
theorem ruleApplication_mem_evaluateOne
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    result ∈ MeTTaZero.evaluateOne (model groundApply) space subject := by
  have equationMember := ruleApplication_mem_equationResults groundApply
    ruleMember premiseFree matchMember instantiates
  have interpretedMember :
      result ∈ MeTTaZero.interpretedResults (model groundApply) space subject :=
    Multiset.mem_add.mpr (Or.inl equationMember)
  have interpretedNonempty :
      MeTTaZero.interpretedResults (model groundApply) space subject ≠ 0 :=
    by
      intro empty
      simp [empty] at interpretedMember
  rw [MeTTaZero.evaluateOne_of_interpreted _ _ _ interpretedNonempty]
  exact interpretedMember

/-- The same result is an actual rewrite occurrence in the composed Zero
evaluation GSLT. -/
theorem ruleApplication_has_zero_evaluation_step
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    ∃ occurrence,
      (MeTTaZero.evaluationGSLT (model groundApply)).Step
        (.request space subject) (.answer space subject occurrence result) := by
  exact (MeTTaZero.mem_evaluateOne_iff_exists_step _ _ _ _).1
    (ruleApplication_mem_evaluateOne groundApply ruleMember premiseFree
      matchMember instantiates)

/-- Bundled bridge from the actual PeTTa `ruleApp` constructor to the Zero
evaluation GSLT. -/
theorem petta_ruleApp_has_zero_step
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} {bindings : Bindings} {subject result : Pattern}
    (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = [])
    (matchMember : bindings ∈ matchPattern rule.left subject)
    (instantiates : applyBindings bindings rule.right = result) :
    PeTTaEval space subject [result] ∧
      ∃ occurrence,
        (MeTTaZero.evaluationGSLT (model groundApply)).Step
          (.request space subject) (.answer space subject occurrence result) := by
  exact
    ⟨PeTTaEval.ruleApp rule bindings subject result ruleMember premiseFree
        matchMember instantiates,
      ruleApplication_has_zero_evaluation_step groundApply ruleMember premiseFree
        matchMember instantiates⟩

/-! ## Reflection changes what is observable -/

/-- An ordinary fact remains observable through the same query used by
evaluation. -/
theorem fact_mem_public_query
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {fact : Pattern} (factMember : fact ∈ space.facts) :
    fact ∈ MeTTaZero.queryAll (model groundApply) space := by
  rw [queryAll_eq_storedAtoms]
  exact PeTTaSpace.mem_storedAtoms_of_fact factMember

/-- Positive reflection canary: a stored rule can be returned as data, not
merely fired privately. -/
theorem rule_mem_public_query
    (groundApply : Pattern → Multiset Pattern) {space : PeTTaSpace}
    {rule : RewriteRule} (ruleMember : rule ∈ space.rules)
    (premiseFree : rule.premises = []) :
    .apply "=" [rule.left, rule.right] ∈
      MeTTaZero.queryAll (model groundApply) space :=
  rule_atom_mem_queryAll groundApply ruleMember premiseFree

/-! ## The existing support-valued MM2 seam -/

/-- The already-proved PeTTa core-fragment theorem sends every arbitrary-atom
query witness into the MORK/MM2 source-query interface.  This corollary makes
the route from the Zero public query explicit while retaining its honest
scope: single-variable matching and support membership. -/
theorem zero_any_atom_query_to_mm2_support
    {space : PeTTaSpace} {name : String} {template atom result : Pattern}
    (atomMember : atom ∈ MeTTaZero.queryAll (model fun _ => 0) space)
    (templateTranslatable :
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable template = true)
    (instantiates : applyBindings [(name, atom)] template = result)
    {workspace :
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.CSpace}
    (workspaceMember :
      Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom atom ∈ workspace) :
    let source :=
      Mettapedia.Languages.MeTTa.RuntimeExec.morkRuntimeQueryExec0.baseSourceFactor
        (.fvar name)
    ∃ substitution translated,
      (substitution, translated) ∈
          Mettapedia.Languages.MeTTa.RuntimeExec.morkRuntimeQueryExec0.computableSourceFactorMatch
            [] workspace source ∧
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst substitution
            (Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom template) =
          Mettapedia.Languages.ProcessCalculi.MORK.morkPatternToAtom result := by
  have storedMember : atom ∈ space.storedAtoms := by
    simpa using atomMember
  exact
    Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery
      storedMember templateTranslatable instantiates workspaceMember


/-! ## Exact native rule enumeration at the shared pure boundary -/

/-- Apply a visible equation atom using the existing source matcher. -/
def applyStoredEquation (subject candidate : Pattern) : List Pattern :=
  match MeTTaZero.viewEquation? candidate with
  | none => []
  | some (left, right) =>
      (matchPattern left subject).map fun bindings => applyBindings bindings right

/-- Native enumeration of the actual premise-free PeTTa rule occurrences.
This computes matcher results and instantiated right sides rather than
accepting an externally supplied reduction trace. -/
def premiseFreeRuleResults (space : PeTTaSpace) (subject : Pattern) : List Pattern :=
  space.rules.flatMap fun rule =>
    if rule.premises = [] then
      (matchPattern rule.left subject).map fun bindings => applyBindings bindings rule.right
    else []

/-- Ordinary facts must not also be equations when comparing PeTTa's separate
rule table with Zero's unified reflective equation medium. -/
def NoFactEquations (space : PeTTaSpace) : Prop :=
  ∀ fact ∈ space.facts, MeTTaZero.viewEquation? fact = none

/-- Direct characterization against the independently existing rule-app
premises; no Zero evaluator occurs on the right side. -/
theorem mem_premiseFreeRuleResults (space : PeTTaSpace) (subject result : Pattern) :
    result ∈ premiseFreeRuleResults space subject ↔
      ∃ rule ∈ space.rules, rule.premises = [] ∧
        ∃ bindings ∈ matchPattern rule.left subject,
          applyBindings bindings rule.right = result := by
  simp only [premiseFreeRuleResults, List.mem_flatMap]
  constructor
  · rintro ⟨rule, member, resultMember⟩
    split at resultMember
    · exact ⟨rule, member, by assumption, List.mem_map.mp resultMember⟩
    · simp at resultMember
  · rintro ⟨rule, member, premiseFree, bindings, bindingMember, instantiates⟩
    refine ⟨rule, member, ?_⟩
    simp only [premiseFree, ↓reduceIte]
    exact List.mem_map.mpr ⟨bindings, bindingMember, instantiates⟩

/-- The native enumerator produces only actual selected-rule evaluations.
It is a one-step rule service, not a whole-program answer evaluator. -/
theorem premiseFreeRuleResults_sound (space : PeTTaSpace) (subject result : Pattern)
    (member : result ∈ premiseFreeRuleResults space subject) :
    PeTTaEval space subject [result] := by
  obtain ⟨rule, ruleMember, premiseFree, bindings, bindingMember, instantiates⟩ :=
    (mem_premiseFreeRuleResults space subject result).mp member
  exact PeTTaEval.ruleApp rule bindings subject result ruleMember premiseFree
    bindingMember instantiates

private theorem equationResults_stored (groundApply : Pattern → Multiset Pattern)
    (space : PeTTaSpace) (subject : Pattern) :
    MeTTaZero.equationResults (model groundApply) space subject =
      (space.storedAtoms.flatMap (applyStoredEquation subject) : Multiset Pattern) := by
  unfold MeTTaZero.equationResults
  rw [queryAll_eq_storedAtoms]
  trans ((space.storedAtoms : Multiset Pattern).bind fun candidate =>
    (applyStoredEquation subject candidate : Multiset Pattern))
  · apply Multiset.bind_congr
    intro candidate _
    cases equation : MeTTaZero.viewEquation? candidate with
    | none => simp [equation, applyStoredEquation]
    | some pair =>
        rcases pair with ⟨left, right⟩
        simp [equation, applyStoredEquation]
  · exact Multiset.coe_bind _ _

private theorem fact_equations_empty (space : PeTTaSpace) (subject : Pattern)
    (onlyFacts : NoFactEquations space) :
    space.facts.flatMap (applyStoredEquation subject) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro fact member
  simp [applyStoredEquation, onlyFacts fact member]

private theorem storedRuleResults (rules : List RewriteRule) (subject : Pattern) :
    (rules.filterMap PeTTaSpace.storedRuleAtom?).flatMap (applyStoredEquation subject) =
      rules.flatMap (fun rule =>
        if rule.premises = [] then
          (matchPattern rule.left subject).map fun bindings => applyBindings bindings rule.right
        else []) := by
  induction rules with
  | nil => rfl
  | cons rule rules ih =>
      cases premises : rule.premises with
      | nil =>
          simp [PeTTaSpace.storedRuleAtom?, premises, applyStoredEquation,
            MeTTaZero.viewEquation?, ih]
      | cons premise rest =>
          simp [PeTTaSpace.storedRuleAtom?, premises, ih]

/-- The exact bag equality preserves every rule and matcher occurrence. Only
PeTTa's enumeration order is forgotten. No grounding or fact equation is
silently added to the selected-rule boundary. -/
theorem equationResults_eq_premiseFreeRuleResults
    (groundApply : Pattern → Multiset Pattern) (space : PeTTaSpace)
    (subject : Pattern) (onlyFacts : NoFactEquations space) :
    MeTTaZero.equationResults (model groundApply) space subject =
      (premiseFreeRuleResults space subject : Multiset Pattern) := by
  rw [equationResults_stored]
  unfold PeTTaSpace.storedAtoms PeTTaSpace.storedRuleAtoms
  rw [List.flatMap_append, fact_equations_empty space subject onlyFacts,
    List.nil_append, storedRuleResults]
  rfl

/-- Native positive Zero articles are complete for the actual selected PeTTa
rule-app premises on this shared pure boundary. -/
theorem accepted_positive_iff_rule_application
    (space : PeTTaSpace) (subject result : Pattern) (onlyFacts : NoFactEquations space) :
    (∃ proof : MeTTaZeroStagedAdequacy.ProductionProof,
      MeTTaZeroStagedAdequacy.checkProductionProof (model (fun _ => 0))
        (.evaluate space subject) result proof = true) ↔
      ∃ rule ∈ space.rules, rule.premises = [] ∧
        ∃ bindings ∈ matchPattern rule.left subject,
          applyBindings bindings rule.right = result := by
  simp only [MeTTaZeroStagedAdequacy.checkProductionProof_exact]
  rw [← MeTTaZeroStagedAdequacy.production_mem_iff_exists_valid,
    MeTTaZeroStagedAdequacy.produce_evaluate_results]
  change result ∈ MeTTaZero.equationResults (model (fun _ => 0)) space subject + 0 ↔ _
  rw [add_zero, equationResults_eq_premiseFreeRuleResults _ space subject onlyFacts]
  simpa using mem_premiseFreeRuleResults space subject result


namespace NativeControls

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []
def rule : RewriteRule := { name := "a-to-b", left := a, right := b, typeContext := [], premises := [] }
def ordinaryFact : Pattern := .apply "fact" []
def duplicateRules : PeTTaSpace := { facts := [ordinaryFact], rules := [rule, rule] }
def factEquationOnly : PeTTaSpace := { facts := [.apply "=" [a, b]], rules := [] }

theorem duplicateRules_noFactEquations : NoFactEquations duplicateRules := by
  simp [NoFactEquations, duplicateRules, ordinaryFact, MeTTaZero.viewEquation?]

/-- Rule multiplicity is retained by the actual native enumerator. -/
theorem duplicate_rule_outputs : premiseFreeRuleResults duplicateRules a = [b, b] := by
  simp [premiseFreeRuleResults, duplicateRules, rule, a, b, matchPattern, matchArgs, applyBindings]

/-- The no-fact-equations restriction is substantive: Zero uses a reflected
fact equation even when PeTTa's selected-rule table is empty. -/
theorem fact_equation_is_not_selected_rule :
    MeTTaZero.equationResults (model (fun _ => 0)) factEquationOnly a = {b} ∧
    premiseFreeRuleResults factEquationOnly a = [] := by
  rw [equationResults_stored]
  simp [factEquationOnly, PeTTaSpace.storedAtoms, PeTTaSpace.storedRuleAtoms,
    premiseFreeRuleResults, applyStoredEquation, MeTTaZero.viewEquation?,
    a, b, matchPattern, matchArgs, applyBindings]

end NativeControls

end Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension


/-! ## Actual Atom quotation with incoming ambient binding -/

namespace Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension

open Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.MeTTa.MeTTaSupportIndexedABTWire.AmbientBinding

private theorem translatableList_of_forall (patterns : List Pattern)
    (all : ∀ pattern ∈ patterns, MORK.morkTranslatable pattern = true) :
    MORK.morkTranslatableList patterns = true := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    simp only [MORK.morkTranslatableList, Bool.and_eq_true]
    exact ⟨all first (by simp), ih (fun p hp => all p (by simp [hp]))⟩

theorem morkTranslatable_of_matchCorrect (pattern : Pattern)
    (plain : isMatchCorrectAux pattern = true) :
    MORK.morkTranslatable pattern = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ | hfvar _ => rfl
  | happly constructor arguments ih =>
    simp only [MORK.morkTranslatable]
    apply translatableList_of_forall
    intro argument member
    exact ih argument member
      ((Mettapedia.OSLF.MeTTaIL.MatchSpec.isMatchCorrectListAux_iff_forall _).mp plain _ member)
  | hlambda name body _ => simp [isMatchCorrectAux] at plain
  | hmultiLambda arity names body _ => simp [isMatchCorrectAux] at plain
  | hsubst body replacement _ _ => simp [isMatchCorrectAux] at plain
  | hcollection kind elements rest _ => simp [isMatchCorrectAux] at plain

/-- The actual Atom evaluator performs incoming binding before returning
quoted syntax. This is a finite source execution, not the older Pattern-rule
wrapper. The named translation remains explicit; no reader adequacy follows. -/
theorem petta_quote_ambient_preparation
    (program : SpaceSemantics.Program) (incoming : Bindings)
    (state : Effects.State) (payload : Pattern)
    (wellScoped : payload.isWellScopedAt 0 = true)
    (plain : isMatchCorrectAux payload = true) :
    Eval.PureReturns program (MORK.translateBindings incoming) state
      (.expression [.symbol "quote", MORK.morkPatternToAtom payload]) state
      (MORK.morkPatternToAtom (reopen incoming 0 (prepare incoming 0 payload))) := by
  have success := Eval.quote_returns program (MORK.translateBindings incoming) state
    (MORK.morkPatternToAtom payload)
  simpa only [reopen_prepare_applyBindings incoming payload wellScoped plain,
    MORK.applySubst_commutes incoming payload (morkTranslatable_of_matchCorrect payload plain)]
    using success

end Mettapedia.Languages.MeTTa.PeTTa.MeTTaZeroExtension

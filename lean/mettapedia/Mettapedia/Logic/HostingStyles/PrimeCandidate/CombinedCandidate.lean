import Mettapedia.Logic.HostingStyles.PrimeCandidate.LambdaPiUnion

/-!
# One candidate with both: a space that is matched, and the λΠ-calculus modulo

The matching evaluator hosts through the run rewrite, and the union with a
theory of the λΠ-calculus modulo hosts through rewrites of its own.  This
module puts both in one presentation, `spaceWithLambdaPi names rules`: the
probe with a run constructor, a space that is a term and a variable atom,
together with the language of the theory.  Under the matching evaluator it
hosts what each of the two hosts.

* It carries the calculus (`spaceWithLambdaPi_carries`), so under every
  evaluator it hosts the scopes of the theory, on terms
  (`CarriesLambdaPi.hostOf_scopes`).
* **No rewrite of the calculus fires on a term of a sort of the probe**
  (`spaceWithLambdaPi_step_iff`): its left sides are applications of
  constructors of the calculus (`dkLanguage_rewrite_head`), and the
  constructors of the sorts of the probe are those of the probe
  (`spaceWithLambdaPi_probeSorts_from`).  So a term of the sort of processes
  steps in the larger language as it does in the probe with a space, under
  every evaluator that answers alike in the two.
* Hence **under the matching evaluator it hosts the theories of first-order
  rule instances, on terms** (`spaceWithLambdaPi_hostsEvery_firstOrderInstances`),
  by the same reading as the probe with a space.
* The matching evaluator respects its static equivalence
  (`matchingEvaluator_respectsStatics_spaceWithLambdaPi`): the rewrites of the
  calculus carry congruence premises only, which the evaluator is not asked.
* The union with the pure calculus passes the declaration gate
  (`pureCombined_validate`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable FirstOrderTable)
open Mettapedia.GSLT.Dedukti.Language
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

variable {names : List String} {rules : List Dedukti.RewriteRule}

/-! ## Steps, from their rule -/

/-- **A step, from a rule, a match of its left side, its premises and the
instance of its right side.** -/
theorem step_of_matched {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) {fuel : Nat} {initial final : Bindings}
    {source target : Pattern} (matched : initial ∈ matchPattern rule.left source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (applied : applyRuleBindings rule final = target) : Step base lang source target := by
  refine ⟨fuel + 1, .rule (initialBindings := initial) (finalBindings := final) member ?_
    premises ?_⟩
  · rw [matchPatternForRule_eq_syntactic]
    exact matched
  · rw [applyBindingsForRule_eq_syntactic]
    exact applied

/-- **Premises that are queries are answered alike in two languages where the
evaluator answers alike.** -/
theorem premisesAt_of_queries {base base' : BasePremiseEvaluator} {lang lang' : LanguageDef}
    {fuel : Nat}
    (same : ∀ (bindings : Bindings) (premise : Premise),
      base lang bindings premise = base' lang' bindings premise) :
    ∀ {list : List Premise},
      (∀ premise ∈ list, ∃ relation arguments, premise = .relationQuery relation arguments) →
        ∀ {start finish : Bindings}, PremisesAt base lang fuel start list finish →
          PremisesAt base' lang' fuel start list finish := by
  intro list
  induction list with
  | nil =>
      intro _ start finish evidence
      cases evidence
      exact .nil _
  | cons premise rest ih =>
      intro queries start finish evidence
      cases evidence with
      | cons first others =>
          obtain ⟨relation, arguments, rfl⟩ := queries premise (List.mem_cons_self ..)
          refine .cons ?_
            (ih (fun other inRest => queries other (List.mem_cons_of_mem _ inRest)) others)
          cases first with
          | relationQuery answered =>
              refine .relationQuery ?_
              rw [← same]
              exact answered

/-! ## The presentation -/

/-- **The probe with a run constructor and a space that is a term, together
with the language of a theory of the λΠ-calculus modulo.** -/
def spaceWithLambdaPi (names : List String) (rules : List Dedukti.RewriteRule) : LanguageDef :=
  withLambdaPi probeWithSpace names rules

/-- No constructor of the probe with a space is of a sort of the calculus. -/
theorem probeWithSpace_category_not_lf :
    ∀ rule ∈ probeWithSpace.terms, rule.category ∉ lfSorts := by
  decide

/-- **It carries the calculus.** -/
theorem spaceWithLambdaPi_carries (names : List String) (rules : List Dedukti.RewriteRule) :
    CarriesLambdaPi (spaceWithLambdaPi names rules) names rules :=
  withLambdaPi_carries probeWithSpace_quoteDropOnly probeWithSpace_quoteDropSorted
    probeWithSpace_category_not_lf probeWithRun_rewrites_match_no_encoding

theorem spaceWithLambdaPi_quoteDropOnly : QuoteDropOnly (spaceWithLambdaPi names rules) :=
  withLambdaPi_quoteDropOnly probeWithSpace_quoteDropOnly

theorem spaceWithLambdaPi_quoteDropSorted : QuoteDropSorted (spaceWithLambdaPi names rules) :=
  withLambdaPi_quoteDropSorted probeWithSpace_quoteDropSorted

/-! ## The sorts of the probe, in the larger language -/

/-- The sorts of the probe with a space. -/
def probeSorts : List String :=
  ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt"]

theorem probeWithSpace_parameters_probe :
    ∀ rule ∈ probeWithSpace.terms, ∀ parameter ∈ rule.params,
      ∀ expected ∈ parameterType? parameter, resultIn probeSorts expected = true := by
  decide

theorem lfSorts_not_probe : ∀ sort ∈ lfSorts, sort ∉ probeSorts := by decide

theorem probeWithSpace_label_not_calculus :
    ∀ rule ∈ probeWithSpace.terms, rule.label ∉ ["App", "Pi", "Lam", "Con"] := by
  decide

/-- **The constructors of the sorts of the probe are those of the probe**, in
the larger language. -/
theorem spaceWithLambdaPi_probeSorts_from :
    SortsFrom (spaceWithLambdaPi names rules) probeWithSpace probeSorts := by
  intro rule member category
  rcases List.mem_append.mp member with inProbe | inCalculus
  · exact ⟨inProbe, probeWithSpace_parameters_probe rule inProbe⟩
  · exact absurd category (lfSorts_not_probe _ (dkLanguage_category_lf inCalculus))

/-- **Negative**: the sorts of the calculus are not sorts whose constructors
are those of the probe. -/
theorem spaceWithLambdaPi_lfSorts_not_from_probe :
    ¬ SortsFrom (spaceWithLambdaPi names rules) probeWithSpace lfSorts := by
  intro closed
  have declared : appRule ∈ (spaceWithLambdaPi names rules).terms :=
    List.mem_append_right _ (lfRule_mem (by simp [lfTermRules]))
  have inProbe := (closed appRule declared (by decide)).1
  revert inProbe
  decide

/-- A term of the probe with a space, as a term of the larger language. -/
def liftTerm (names : List String) (rules : List Dedukti.RewriteRule)
    (term : Contexts.Term probeWithSpace closedProcess) :
    Contexts.Term (spaceWithLambdaPi names rules) closedProcess :=
  ⟨term.1, term.2.1.weakenTerms fun _ member => List.mem_append_left _ member, term.2.2.1,
    term.2.2.2.1, term.2.2.2.2⟩

/-- A term of the larger language at the sort of processes is a term of the
probe with a space. -/
def lowerTerm (term : Contexts.Term (spaceWithLambdaPi names rules) closedProcess) :
    Contexts.Term probeWithSpace closedProcess :=
  ⟨term.1, hasType_of_sortsFrom spaceWithLambdaPi_probeSorts_from term.2.1 (by decide)
    term.2.2.2.1, term.2.2.1, term.2.2.2.1, term.2.2.2.2⟩

/-! ## No rewrite of the calculus fires on a term of a sort of the probe -/

/-- The pattern of an algebraic left side is an application of `App` or
`Con`. -/
theorem toPattern_head {term : LF.Term} (algebraicLeft : Dedukti.algebraic true term = true) :
    ∃ label parameters, toPattern 0 term = .apply label parameters ∧
      label ∈ ["App", "Pi", "Lam", "Con"] := by
  cases term with
  | var index => simp [Dedukti.algebraic] at algebraicLeft
  | srt sort => simp [Dedukti.algebraic] at algebraicLeft
  | con symbol => exact ⟨_, _, rfl, by decide⟩
  | pi domain body => simp [Dedukti.algebraic] at algebraicLeft
  | lam domain body => simp [Dedukti.algebraic] at algebraicLeft
  | app function argument => exact ⟨_, _, rfl, by decide⟩

/-- **The left side of a rewrite of the calculus is an application of a
constructor of the calculus.** -/
theorem dkLanguage_rewrite_head
    (algebraicLeft : ∀ rule ∈ rules, Dedukti.algebraic true rule.lhs = true) {rule : RewriteRule}
    (member : rule ∈ (dkLanguage names rules).rewrites) :
    ∃ label parameters, rule.left = .apply label parameters ∧
      label ∈ ["App", "Pi", "Lam", "Con"] := by
  rcases List.mem_append.mp member with fixed | declared
  · simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, by decide⟩
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp declared
    exact toPattern_head (algebraicLeft _ (List.getElem_mem bound))

/-- No term of a sort of the probe is an application of a constructor of the
calculus. -/
theorem not_hasType_calculus_head {free : FreeTypeContext} {bound : List TypeExpr}
    {label : String} {arguments : List Pattern} {sort : String}
    (typed : HasType (spaceWithLambdaPi names rules) free bound (.apply label arguments)
      (.base sort))
    (probe : sort ∈ probeSorts) (listed : label ∈ ["App", "Pi", "Lam", "Con"]) : False := by
  cases typed with
  | constructor member _ _ =>
      rcases List.mem_append.mp member with inProbe | inCalculus
      · exact probeWithSpace_label_not_calculus _ inProbe listed
      · exact lfSorts_not_probe _ (dkLanguage_category_lf inCalculus) probe

/-- The premises of the rewrites of the probe with a space are queries. -/
theorem probeWithSpace_premises_queries :
    ∀ rule ∈ probeWithSpace.rewrites, ∀ premise ∈ rule.premises,
      ∃ relation arguments, premise = .relationQuery relation arguments := by
  intro rule member premise inRule
  have listed : premise ∈ presentedPremises probeWithRun :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, inRule⟩)
  rw [presentedPremises_probeWithRun] at listed
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/-- **A term of a sort of the probe steps in the larger language as it does
in the probe with a space**, under an evaluator that answers alike in the
two. -/
theorem spaceWithLambdaPi_step_iff {base : BasePremiseEvaluator}
    (same : ∀ (bindings : Bindings) (premise : Premise),
      base (spaceWithLambdaPi names rules) bindings premise =
        base probeWithSpace bindings premise)
    (algebraicLeft : ∀ rule ∈ rules, Dedukti.algebraic true rule.lhs = true)
    {free : FreeTypeContext} {bound : List TypeExpr} {redex contractum : Pattern} {sort : String}
    (typed : HasType (spaceWithLambdaPi names rules) free bound redex (.base sort))
    (probe : sort ∈ probeSorts) :
    Step base (spaceWithLambdaPi names rules) redex contractum ↔
      Step base probeWithSpace redex contractum := by
  constructor
  · intro step
    obtain ⟨rule, member, fuel, initial, final, matched, premises, applied⟩ :=
      exists_rule_of_step step
    rcases List.mem_append.mp member with inProbe | inCalculus
    · exact step_of_matched inProbe matched
        (premisesAt_of_queries same (probeWithSpace_premises_queries rule inProbe) premises)
        applied
    · exfalso
      obtain ⟨label, parameters, leftShape, listed⟩ :=
        dkLanguage_rewrite_head algebraicLeft inCalculus
      rw [leftShape] at matched
      obtain ⟨arguments, rfl, -⟩ := eq_apply_of_matched matched
      exact not_hasType_calculus_head typed probe listed
  · intro step
    exact Step.transport (fun _ member => List.mem_append_left _ member)
      (fun _ _ _ _ bindings _ answered => by
        rw [same]
        exact answered) step

/-! ## The matching evaluator in the larger language -/

/-- The premises of the larger language are those of the probe with the run
constructor, and congruences. -/
theorem spaceWithLambdaPi_premises :
    ∀ premise ∈ presentedPremises (spaceWithLambdaPi names rules),
      premise ∈ presentedPremises probeWithRun ∨
        ∃ source target, premise = .congruence source target := by
  intro premise member
  rcases List.mem_append.mp member with inRewrites | inEquations
  · obtain ⟨rule, ruleMember, inRule⟩ := List.mem_flatMap.mp inRewrites
    rcases List.mem_append.mp ruleMember with inProbe | inCalculus
    · exact .inl (List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, inProbe, inRule⟩))
    · rcases List.mem_append.mp inCalculus with fixed | declared
      · simp only [fixedRules, List.mem_cons, List.not_mem_nil, or_false] at fixed
        rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · cases inRule
        all_goals exact .inr ⟨_, _, List.mem_singleton.mp inRule⟩
      · obtain ⟨index, _, rfl⟩ := List.mem_mapIdx.mp declared
        cases inRule
  · exact .inl (List.mem_append_right _ inEquations)

/-- **The matching evaluator respects the static equivalence of the larger
language.** -/
theorem matchingEvaluator_respectsStatics_spaceWithLambdaPi :
    RespectsStatics matchingEvaluator (spaceWithLambdaPi names rules) :=
  matchingEvaluator_respectsStatics_of_premises spaceWithLambdaPi_quoteDropOnly
    spaceWithLambdaPi_premises

/-- **Under the matching evaluator the larger language hosts the instances of
every first-order table whose right sides are bound**, by the reading of the
probe with a space. -/
theorem spaceWithLambdaPi_hosts_instances {table : RuleTable}
    (firstOrder : FirstOrderTable table) (bound : BoundTable table)
    (algebraicLeft : ∀ rule ∈ rules, Dedukti.algebraic true rule.lhs = true)
    (valid : (spaceWithLambdaPi names rules).validate = []) :
    HostedBy (instanceTheory table).termsAlone
      (contextTheory matchingEvaluator ⟨spaceWithLambdaPi names rules, valid⟩) := by
  obtain ⟨reflectsEquations, preserves, reflects⟩ :=
    (ContextMap.ofTerms_hosting_iff (source := instanceTheory table) (target := matchingCandidate)
      closedProcess (fun term => runTermOf table.toList term)
      (fun related => runTermOf_resp table related)).mp (matchingMap_hosting firstOrder bound)
  have smallIff : ∀ first second : Contexts.Term probeWithSpace closedProcess,
      (termSetoid matchingEvaluator probeWithSpace closedProcess).r first second ↔
        contract first.1 = contract second.1 := fun _ _ =>
    probeWithSpace_quoteDropOnly.termSetoid_iff probeWithSpace_quoteDropSorted
  have largeIff : ∀ first second : Contexts.Term (spaceWithLambdaPi names rules) closedProcess,
      (termSetoid matchingEvaluator (spaceWithLambdaPi names rules) closedProcess).r first
        second ↔ contract first.1 = contract second.1 := fun _ _ =>
    spaceWithLambdaPi_quoteDropOnly.termSetoid_iff spaceWithLambdaPi_quoteDropSorted
  have stepIff : ∀ {redex contractum : Contexts.Term (spaceWithLambdaPi names rules)
      closedProcess},
      Step matchingEvaluator (spaceWithLambdaPi names rules) redex.1 contractum.1 ↔
        Step matchingEvaluator probeWithSpace redex.1 contractum.1 := fun {redex} {_} =>
    spaceWithLambdaPi_step_iff (fun _ _ => rfl) algebraicLeft redex.2.1 (by decide)
  refine ⟨ContextMap.ofTerms (source := instanceTheory table)
    (target := contextTheory matchingEvaluator ⟨spaceWithLambdaPi names rules, valid⟩)
    closedProcess (fun term => liftTerm names rules (runTermOf table.toList term))
    (fun same => by subst same; exact Relation.EqvGen.refl _), ?_⟩
  refine (ContextMap.ofTerms_hosting_iff (source := instanceTheory table)
    (target := contextTheory matchingEvaluator ⟨spaceWithLambdaPi names rules, valid⟩)
    closedProcess (fun term => liftTerm names rules (runTermOf table.toList term))
    (fun same => by subst same; exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    exact reflectsEquations first second ((smallIff _ _).mpr ((largeIff _ _).mp related))
  · intro first next step
    obtain ⟨redex, contractum, before, fired, after⟩ := preserves first next step
    exact ⟨liftTerm names rules redex, liftTerm names rules contractum,
      (largeIff _ _).mpr ((smallIff _ _).mp before), stepIff.mpr fired,
      (largeIff _ _).mpr ((smallIff _ _).mp after)⟩
  · intro first next step
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    obtain ⟨target, sourceStep, related⟩ := reflects first (lowerTerm contractum)
      ⟨lowerTerm redex, lowerTerm contractum, (smallIff _ _).mpr ((largeIff _ _).mp before),
        stepIff.mp fired, Relation.EqvGen.refl _⟩
    exact ⟨target, sourceStep,
      (largeIff _ _).mpr (((largeIff _ _).mp after).symm.trans ((smallIff _ _).mp related))⟩

theorem spaceWithLambdaPi_hostsEvery_firstOrderInstances
    (algebraicLeft : ∀ rule ∈ rules, Dedukti.algebraic true rule.lhs = true)
    (valid : (spaceWithLambdaPi names rules).validate = []) :
    HostsEvery (contextTheory matchingEvaluator ⟨spaceWithLambdaPi names rules, valid⟩)
      FirstOrderInstances := by
  rintro source ⟨table, firstOrder, bound, rfl⟩
  exact spaceWithLambdaPi_hosts_instances firstOrder bound algebraicLeft valid

/-- **The sentence for the larger language under the matching evaluator**: it
is a host of the theories of first-order rule instances, on terms. -/
theorem spaceWithLambdaPi_hostOf_firstOrderInstances
    (algebraicLeft : ∀ rule ∈ rules, Dedukti.algebraic true rule.lhs = true)
    (valid : (spaceWithLambdaPi names rules).validate = []) :
    HostOf (contextTheory matchingEvaluator ⟨spaceWithLambdaPi names rules, valid⟩)
      FirstOrderInstances .terms .hosting :=
  HostOf.terms (hostOf_contexts_hosting_iff.mpr
    (spaceWithLambdaPi_hostsEvery_firstOrderInstances algebraicLeft valid))

/-! ## The union with the pure calculus passes the declaration gate -/

/-- **The probe with a space together with the pure calculus.** -/
def pureCombined : LanguageDef := spaceWithLambdaPi [] []

theorem pureCombined_typeNames : pureCombined.typeNames =
    ["Atom", "Space", "Process", "Alternatives", "CandidateName", "CandidateReceipt", "LFSort",
      "LFTerm", "LFName", "LFIndex"] := by
  decide

theorem pureCombined_signatures :
    RewriteValidationCertificate.constructorSignatures pureCombined =
      [("=", 2), ("zero-query", 3), ("zero-query-answer", 1), ("zero-evaluate", 2),
        ("zero-evaluate-answer", 1), ("prime-unit", 0), ("prime-quote", 1), ("prime-drop", 1),
        ("prime-evaluate-name", 2), ("prime-need", 2), ("prime-need-answer", 2),
        ("prime-need-key", 2), ("prime-request-dependency", 1),
        ("prime-space-atom-dependency", 2), ("prime-capability-dependency", 2),
        ("prime-inert-dependency", 1), ("prime-receipt", 1), ("prime-run", 2),
        ("prime-space-empty", 0), ("prime-space-add", 2), ("prime-variable", 1),
        ("SortType", 0), ("SortKind", 0), ("Srt", 1), ("Con", 1), ("Var", 1), ("Pi", 2),
        ("Lam", 2), ("App", 2)] := by
  decide

theorem pureCombined_labels :
    RewriteValidationCertificate.constructorLabels pureCombined =
      ["=", "zero-query", "zero-query-answer", "zero-evaluate", "zero-evaluate-answer",
        "prime-unit", "prime-quote", "prime-drop", "prime-evaluate-name", "prime-need",
        "prime-need-answer", "prime-need-key", "prime-request-dependency",
        "prime-space-atom-dependency", "prime-capability-dependency", "prime-inert-dependency",
        "prime-receipt", "prime-run", "prime-space-empty", "prime-space-add", "prime-variable",
        "SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App"] := by
  decide

theorem pureCombined_probe_checked :
    ∀ rewrite ∈ probeWithSpace.rewrites,
      RewriteValidationCertificate.check pureCombined rewrite = true := by
  intro rewrite member
  rw [probeWithSpace_rewrites, probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_probe_rewrite pureCombined_typeNames pureCombined_signatures pureCombined_labels

theorem pureCombined_calculus_checked :
    ∀ rewrite ∈ (dkLanguage [] []).rewrites,
      RewriteValidationCertificate.check pureCombined rewrite = true := by
  intro rewrite member
  simp only [dkLanguage, fixedRules, List.mapIdx_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    check_calculus_rewrite pureCombined_typeNames pureCombined_signatures pureCombined_labels

/-- **The probe with a space together with the pure calculus passes the
declaration gate.** -/
theorem pureCombined_validate : pureCombined.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          pureCombined.equations.all (LanguageDef.plainEquationOk pureCombined) = true)
        equation member)
  · intro rewrite member
    refine RewriteValidationCertificate.validateRewrite_eq_nil_of_check (by decide +kernel) ?_
    rcases List.mem_append.mp member with inProbe | inCalculus
    · exact pureCombined_probe_checked rewrite inProbe
    · exact pureCombined_calculus_checked rewrite inCalculus

/-- **Positive**: under the matching evaluator, the probe with a space
together with the pure calculus is a host of the theories of first-order rule
instances and of the scopes of the pure calculus, on terms. -/
theorem pureCombined_hostOf_both :
    HostOf (contextTheory matchingEvaluator ⟨spaceWithLambdaPi [] [], pureCombined_validate⟩)
        FirstOrderInstances .terms .hosting ∧
      HostOf (contextTheory matchingEvaluator ⟨spaceWithLambdaPi [] [], pureCombined_validate⟩)
        (ScopesOf Theory.empty [] []) .terms .hosting :=
  ⟨spaceWithLambdaPi_hostOf_firstOrderInstances
      (fun _ member => absurd member List.not_mem_nil) pureCombined_validate,
    (spaceWithLambdaPi_carries [] []).hostOf_scopes pure_presents pureCombined_validate
      matchingEvaluator⟩

#print axioms step_of_matched
#print axioms premisesAt_of_queries
#print axioms spaceWithLambdaPi_carries
#print axioms spaceWithLambdaPi_probeSorts_from
#print axioms spaceWithLambdaPi_lfSorts_not_from_probe
#print axioms dkLanguage_rewrite_head
#print axioms spaceWithLambdaPi_step_iff
#print axioms matchingEvaluator_respectsStatics_spaceWithLambdaPi
#print axioms spaceWithLambdaPi_hosts_instances
#print axioms spaceWithLambdaPi_hostsEvery_firstOrderInstances
#print axioms spaceWithLambdaPi_hostOf_firstOrderInstances
#print axioms pureCombined_validate
#print axioms pureCombined_hostOf_both

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

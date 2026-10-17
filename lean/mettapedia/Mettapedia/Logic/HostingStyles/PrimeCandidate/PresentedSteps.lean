import Mettapedia.Logic.HostingStyles.PrimeCandidate.AdmissibleEvaluators

/-!
# Steps of presented languages: moving them, and reading the seven rewrites

Three tools for the extensions of the probe.

* **A step moves to a language with more rewrites and to another evaluator**
  when the evaluator it is moved to answers the premises of the first
  language at least as the first evaluator does (`Step.transport`).  A
  language whose rewrites carry no premise satisfies the condition for every
  pair of evaluators (`Step.transport_of_premiseFree`): its steps do not
  consult the evaluator.
* An application of a declared constructor to terms is a term
  (`wellSorted_apply_zero`, `wellSorted_apply_one`, `wellSorted_apply_two`).
* In every language with the seven rewrites of the probe with the run
  constructor, a step goes along one of the six edges of the probe or is a
  step of running (`runRules_step_heads`); a step out of a run is a step of
  running, and it asks the evaluator once (`run_step_shape`).  So every
  transition lowers the rank of the probe or goes from a run to a run
  (`runRules_termStep_lowers_or_runs`), and under the evaluator that answers
  nothing the rank is a rank (`silentRankOfRules`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## Moving a step -/

/-- **A bounded step moves to a language with more rewrites and to another
evaluator**, when the second evaluator gives every answer of the first to the
premises of the first language. -/
theorem StepAt.transport {base base' : BasePremiseEvaluator} {lang lang' : LanguageDef}
    (rules : ∀ rule ∈ lang.rewrites, rule ∈ lang'.rewrites)
    (answers : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises, ∀ bindings result : Bindings,
      result ∈ base lang bindings premise → result ∈ base' lang' bindings premise) :
    ∀ {fuel : Nat} {source target : Pattern},
      StepAt base lang fuel source target → StepAt base' lang' fuel source target := by
  intro fuel
  induction fuel with
  | zero => intro source target evidence; cases evidence
  | succ fuel ih =>
      intro source target evidence
      cases evidence with
      | @rule _ _ _ authored initial final member matched premises targetEq =>
          have moved : ∀ {list : List Premise}, (∀ premise ∈ list, premise ∈ authored.premises) →
              ∀ {start finish : Bindings}, PremisesAt base lang fuel start list finish →
                PremisesAt base' lang' fuel start list finish := by
            intro list
            induction list with
            | nil =>
                intro _ start finish evidence
                cases evidence
                exact .nil _
            | cons premise rest inner =>
                intro within start finish evidence
                cases evidence with
                | cons first others =>
                    have here := within premise (List.mem_cons_self ..)
                    refine .cons ?_
                      (inner (fun other inRest => within other (List.mem_cons_of_mem _ inRest)) others)
                    cases first with
                    | freshness answered =>
                        exact .freshness (answers _ member _ here _ _ answered)
                    | relationQuery answered =>
                        exact .relationQuery (answers _ member _ here _ _ answered)
                    | forAll answered => exact .forAll (answers _ member _ here _ _ answered)
                    | congruence recursive matchedTarget merged =>
                        exact .congruence (ih recursive) matchedTarget merged
                    | scopedRoot empty recursive matchedTarget merged =>
                        exact .scopedRoot empty (ih recursive) matchedTarget merged
          refine .rule (rules _ member) ?_ (moved (fun _ inRule => inRule) premises) ?_
          · rw [matchPatternForRule_eq_syntactic] at matched ⊢
            exact matched
          · rw [applyBindingsForRule_eq_syntactic] at targetEq ⊢
            exact targetEq

/-- The same for steps. -/
theorem Step.transport {base base' : BasePremiseEvaluator} {lang lang' : LanguageDef}
    (rules : ∀ rule ∈ lang.rewrites, rule ∈ lang'.rewrites)
    (answers : ∀ rule ∈ lang.rewrites, ∀ premise ∈ rule.premises, ∀ bindings result : Bindings,
      result ∈ base lang bindings premise → result ∈ base' lang' bindings premise)
    {source target : Pattern} (step : Step base lang source target) :
    Step base' lang' source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact ⟨fuel, StepAt.transport rules answers bounded⟩

/-- **The steps of a language whose rewrites carry no premise do not consult
the evaluator**: they are steps of every language with those rewrites, under
every evaluator. -/
theorem Step.transport_of_premiseFree {base base' : BasePremiseEvaluator}
    {lang lang' : LanguageDef} (rules : ∀ rule ∈ lang.rewrites, rule ∈ lang'.rewrites)
    (free : ∀ rule ∈ lang.rewrites, rule.premises = []) {source target : Pattern}
    (step : Step base lang source target) : Step base' lang' source target :=
  Step.transport rules
    (fun rule member premise inRule => by
      rw [free rule member] at inRule
      cases inRule) step

/-! ## Applications of declared constructors -/

/-- A constructor that is applied as its label: plain parameters, no
notation, no evaluation policy and no algebra. -/
def plainConstructor (label category : String) (params : List TermParam) : GrammarRule :=
  { label := label, category := category, params := params, syntaxPattern := [] }

/-- A declared constant is a term. -/
theorem wellSorted_apply_zero {lang : LanguageDef} {bound : List TypeExpr} {label category : String}
    (declared : plainConstructor label category [] ∈ lang.terms) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base category) (.apply label []) := by
  refine ⟨.constructor (rule := plainConstructor label category []) declared (fun bare => ?_) .nil,
    by simp [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList],
    by simp [isObjectPattern, isObjectPatternList], ?_⟩
  · obtain ⟨_, _, _, shape⟩ := bare
    cases shape
  · show (Pattern.apply label []).isWellScopedAt bound.length = true
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt]

/-- A declared constructor of one argument, applied to a term, is a term. -/
theorem wellSorted_apply_one {lang : LanguageDef} {bound : List TypeExpr}
    {label category name sort : String} {argument : Pattern}
    (declared : plainConstructor label category [.simple name (.base sort)] ∈ lang.terms)
    (sorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base sort) argument) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base category)
      (.apply label [argument]) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := sorted
  refine ⟨.constructor (rule := plainConstructor label category [.simple name (.base sort)])
    declared (fun bare => ?_) (.cons trivial rfl typed .nil), ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, shape⟩ := bare
    simp [plainConstructor] at shape
  · simpa [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  · simpa [isObjectPattern, isObjectPatternList] using object
  · have here : argument.isWellScopedAt bound.length = true := scopeSafe
    show (Pattern.apply label [argument]).isWellScopedAt bound.length = true
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here]

/-- A declared constructor of two arguments, applied to terms, is a term. -/
theorem wellSorted_apply_two {lang : LanguageDef} {bound : List TypeExpr}
    {label category firstName firstSort secondName secondSort : String} {first second : Pattern}
    (declared : plainConstructor label category
      [.simple firstName (.base firstSort), .simple secondName (.base secondSort)] ∈ lang.terms)
    (firstSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base firstSort) first)
    (secondSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base secondSort)
      second) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base category)
      (.apply label [first, second]) := by
  obtain ⟨firstTyped, firstCanonical, firstObject, firstScope⟩ := firstSorted
  obtain ⟨secondTyped, secondCanonical, secondObject, secondScope⟩ := secondSorted
  refine ⟨.constructor (rule := plainConstructor label category
      [.simple firstName (.base firstSort), .simple secondName (.base secondSort)]) declared
    (fun bare => ?_) (.cons trivial rfl firstTyped (.cons trivial rfl secondTyped .nil)), ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, shape⟩ := bare
    simp [plainConstructor] at shape
  · simpa [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using ⟨firstCanonical, secondCanonical⟩
  · simpa [isObjectPattern, isObjectPatternList] using ⟨firstObject, secondObject⟩
  · have here : first.isWellScopedAt bound.length = true := firstScope
    have there : second.isWellScopedAt bound.length = true := secondScope
    show (Pattern.apply label [first, second]).isWellScopedAt bound.length = true
    simp [Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here, there]

/-! ## The seven rewrites -/

/-- **In a language with the seven rewrites, a step goes along an edge of the
probe or is a step of running.** -/
theorem runRules_step_heads {lang : LanguageDef} (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} {source target : Pattern} (step : Step base lang source target) :
    (∃ edge ∈ probeEdges, head? source = some edge.1 ∧ head? target = some edge.2) ∨
      (head? source = some "prime-run" ∧ head? target = some "prime-run") := by
  obtain ⟨rule, member, _, initial, final, matched, _, rfl⟩ := exists_rule_of_step step
  rw [rules, probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨("zero-query", "zero-query-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("zero-evaluate", "zero-evaluate-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("zero-evaluate", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-need", "prime-need-answer"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-need-answer", "zero-evaluate-answer"), by decide,
      head?_of_matched matched, head?_applyRuleBindings _ _ rfl⟩
  · exact .inl ⟨("prime-evaluate-name", "prime-need"), by decide, head?_of_matched matched,
      head?_applyRuleBindings _ _ rfl⟩
  · exact .inr ⟨head?_of_matched matched, head?_applyRuleBindings _ _ rfl⟩

/-- **A step out of a pattern that contracts to a run is a step of running**:
the redex is a run, the evaluator answered its premise once, and the
contractum is the right side under that answer. -/
theorem run_step_shape {lang : LanguageDef} (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} {redex contractum : Pattern}
    (runHead : head? (contract redex) = some "prime-run")
    (step : Step base lang redex contractum) :
    ∃ (space subject : Pattern) (final : Bindings), redex = runPattern space subject ∧
      final ∈ base lang [("subject", subject), ("space", space)] runPremise ∧
        contractum = applyBindings final runRewrite.right := by
  obtain ⟨rule, member, fuel, initial, final, matched, premises, rfl⟩ := exists_rule_of_step step
  rw [rules, probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · exact absurd ((head?_contract (head?_of_matched matched) (by decide)).symm.trans runHead)
      (by decide)
  · obtain ⟨arguments, rfl, length⟩ := eq_apply_of_matched matched
    obtain ⟨space, subject, rfl⟩ := List.length_eq_two.mp length
    have shape : initial = [("subject", subject), ("space", space)] := by
      simpa [runRewrite, matchPattern, matchArgs, mergeBindings] using matched
    subst shape
    change PremisesAt base lang fuel _ [runPremise] final at premises
    cases premises with
    | cons first rest =>
        cases rest
        cases first with
        | relationQuery answered =>
            exact ⟨space, subject, _, rfl, answered,
              applyRuleBindings_eq_applyBindings _ _ (by decide)⟩

/-- **Every transition lowers the rank of the probe, or goes from a run to a
run**, for every evaluator. -/
theorem runRules_termStep_lowers_or_runs {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) {base : BasePremiseEvaluator}
    {interface : Contexts.Interface} {source target : Contexts.Term lang interface}
    (step : TermStep base lang source target) :
    patternRank target.1 < patternRank source.1 ∨
      (head? (contract source.1) = some "prime-run" ∧
        head? (contract target.1) = some "prime-run") := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  rcases runRules_step_heads rules fired with ⟨edge, member, sourceHead, targetHead⟩ | runs
  · refine .inl ?_
    rw [patternRank_congr (only.contract_eq before), ← patternRank_congr (only.contract_eq after)]
    simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [patternRank_of_head? sourceHead (by decide), patternRank_of_head? targetHead (by decide)] <;>
      decide
  · refine .inr ⟨?_, ?_⟩
    · rw [only.contract_eq before]
      exact head?_contract runs.1 (by decide)
    · rw [← only.contract_eq after]
      exact head?_contract runs.2 (by decide)

/-- Under the evaluator that answers nothing, a step of a language with the
seven rewrites goes along an edge of the probe. -/
theorem silent_step_heads_of_rules {lang : LanguageDef}
    (rules : lang.rewrites = probeWithRun.rewrites) {source target : Pattern}
    (step : Step silentEvaluator lang source target) :
    ∃ edge ∈ probeEdges, head? source = some edge.1 ∧ head? target = some edge.2 := by
  rcases runRules_step_heads rules step with found | runs
  · exact found
  · obtain ⟨space, subject, final, -, answered, -⟩ :=
      run_step_shape rules (head?_contract runs.1 (by decide)) step
    cases answered

/-- **Under the evaluator that answers nothing a presentation with the seven
rewrites has a rank.** -/
def silentRankOfRules (presentation : ValidatedLanguageDef)
    (only : QuoteDropOnly presentation.language)
    (rules : presentation.language.rewrites = probeWithRun.rewrites) :
    (contextTheory silentEvaluator presentation).Rank where
  rank := fun term => patternRank term.1
  lowers := fun step => by
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    rw [patternRank_congr (only.contract_eq before), ← patternRank_congr (only.contract_eq after)]
    obtain ⟨edge, member, sourceHead, targetHead⟩ := silent_step_heads_of_rules rules fired
    simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [patternRank_of_head? sourceHead (by decide), patternRank_of_head? targetHead (by decide)] <;>
      decide

#print axioms StepAt.transport
#print axioms Step.transport_of_premiseFree
#print axioms wellSorted_apply_two
#print axioms runRules_step_heads
#print axioms run_step_shape
#print axioms runRules_termStep_lowers_or_runs
#print axioms silentRankOfRules

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

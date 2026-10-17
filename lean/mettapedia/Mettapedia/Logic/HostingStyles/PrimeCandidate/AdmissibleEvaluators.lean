import Mettapedia.Logic.HostingStyles.PrimeCandidate.DeterminedTables
import Mettapedia.Logic.HostingStyles.PrimeCandidate.ContractionComplete
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Evaluators that respect the static equivalence

The premises of the rewrites of a presented language are answered by an
evaluator that is given the bindings themselves, and the steps of the
language are taken up to its static equivalence.  This module defines the
evaluators whose answers do not depend on how the bound values are written,
and says what they can do for the probe with the run constructor.

* `RespectsStatics base lang`: for each premise of the language, bindings
  that differ by the static equivalence only get answers that differ by the
  static equivalence only.
* The evaluator that answers nothing respects it, and so does the evaluator
  of every listing (`stepEvaluator_respectsStatics`).  The evaluator that
  counts the droppings of its subject does not
  (`spellingEvaluator_not_respectsStatics`).
* **Under an evaluator that respects the static equivalence every term has
  finitely many reducts up to the static equivalence**
  (`finite_reducts_of_respectsStatics`), in every language with the seven
  rewrites of the probe with the run constructor.  Six of the seven left
  sides read their redex up to the static equivalence
  (`ReadsUpToContraction`); the seventh, the evaluation of a quoted name,
  does not (`reflectedDemand_not_readsUpToContraction`) and contributes two
  classes at most.
* So what such an evaluator hosts on terms is finitely branching
  (`finitelyBranching_of_hostedBy`); finite branching is image-finiteness
  modulo the equations for the system with one label
  (`finitelyBranching_iff_imageFiniteModulo`).  For the theories of the λΠ-calculus
  modulo the bound is exact: a theory is hosted on terms by the probe with
  the run constructor under some evaluator that respects the static
  equivalence **exactly when each of its terms has finitely many reducts**
  (`hostedBy_respecting_iff_finite`).  The theories given by a table are not
  all of that kind, so no such evaluator makes the presentation a host of
  them all (`not_hostOf_tabular_terms_of_respectsStatics`), and the evaluator
  that does is not one (`tableRunEvaluator_not_respectsStatics`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## Bindings whose values are written differently -/

/-- **Two lists of bindings bind the same names in the same order, to values
that a relation identifies.** -/
def BindingsRelated (relation : Pattern → Pattern → Prop) : Bindings → Bindings → Prop :=
  List.Forall₂ fun first second => first.1 = second.1 ∧ relation first.2 second.2

theorem BindingsRelated.mono {relation other : Pattern → Pattern → Prop}
    (weaker : ∀ left right, relation left right → other left right) {first second : Bindings}
    (related : BindingsRelated relation first second) : BindingsRelated other first second :=
  List.Forall₂.imp (fun _ _ pair => ⟨pair.1, weaker _ _ pair.2⟩) related

/-- **Positive**: a name and its quoted dropping, under one variable. -/
theorem bindingsRelated_quoted_dropped (name : Pattern) :
    BindingsRelated (fun left right => contract left = contract right)
      [("name", quoted (dropped name))] [("name", name)] :=
  .cons ⟨rfl, contract_quoted_dropped name⟩ .nil

/-- **Negative**: one value under two variables. -/
theorem not_bindingsRelated_of_names (relation : Pattern → Pattern → Prop) (value : Pattern) :
    ¬ BindingsRelated relation [("first", value)] [("second", value)] := by
  intro related
  cases related with
  | cons pair _ =>
      have names : "first" = "second" := pair.1
      exact absurd names (by decide)

theorem applyBindings_fvar_cons (entry : String × Pattern) (rest : Bindings) (name : String) :
    applyBindings (entry :: rest) (.fvar name) =
      if entry.1 = name then entry.2 else applyBindings rest (.fvar name) := by
  by_cases same : entry.1 = name
  · simp [applyBindings, same]
  · simp [applyBindings, same]

/-- Related bindings give related values to each variable. -/
theorem BindingsRelated.lookup {relation : Pattern → Pattern → Prop}
    (reflexive : ∀ pattern, relation pattern pattern) {first second : Bindings}
    (related : BindingsRelated relation first second) (name : String) :
    relation (applyBindings first (.fvar name)) (applyBindings second (.fvar name)) := by
  unfold BindingsRelated at related
  induction related with
  | nil => exact reflexive _
  | cons pair _ ih =>
      rw [applyBindings_fvar_cons, applyBindings_fvar_cons, ← pair.1]
      split_ifs
      · exact pair.2
      · exact ih

theorem isMatchCorrectAux_of_mem :
    ∀ {patterns : List Pattern}, isMatchCorrectListAux patterns = true →
      ∀ pattern ∈ patterns, isMatchCorrectAux pattern = true
  | [], _, _, member => by cases member
  | head :: tail, exact, pattern, member => by
      simp only [isMatchCorrectListAux, Bool.and_eq_true] at exact
      rcases List.mem_cons.mp member with rfl | inTail
      · exact exact.1
      · exact isMatchCorrectAux_of_mem exact.2 pattern inTail

/-- **The contraction of an instance of a first-order pattern is determined by
the contractions of the bound values.** -/
theorem contract_applyBindings_congr {first second : Bindings}
    (related : BindingsRelated (fun left right => contract left = contract right) first second) :
    ∀ pattern : Pattern, isMatchCorrectAux pattern = true →
      contract (applyBindings first pattern) = contract (applyBindings second pattern) := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp [applyBindings]
  | hfvar name =>
      intro _
      exact BindingsRelated.lookup (relation := fun left right => contract left = contract right)
        (fun _ => rfl) related name
  | happly label arguments ih =>
      intro exact
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      have same : (arguments.map (applyBindings first)).map contract =
          (arguments.map (applyBindings second)).map contract := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun argument member => ih argument member (each argument member)
      rw [show applyBindings first (.apply label arguments) =
          .apply label (arguments.map (applyBindings first)) by simp [applyBindings],
        show applyBindings second (.apply label arguments) =
          .apply label (arguments.map (applyBindings second)) by simp [applyBindings],
        contract, contract, contractList_eq_map, contractList_eq_map, same]
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-! ## Evaluators that respect the static equivalence -/

/-- The premises that the rewrites and the equations of a language hand to
the evaluator. -/
def presentedPremises (lang : LanguageDef) : List Premise :=
  lang.rewrites.flatMap (·.premises) ++ lang.equations.flatMap (·.premises)

/-- **An evaluator respects the static equivalence of a language**: its
answers to a premise of the language do not depend on how the bound values
are written.  Bindings that differ by the static equivalence only get answers
that differ by the static equivalence only. -/
def RespectsStatics (base : BasePremiseEvaluator) (lang : LanguageDef) : Prop :=
  ∀ premise ∈ presentedPremises lang, ∀ {first second : Bindings},
    BindingsRelated (EquationEquiv base lang) first second →
      ∀ result ∈ base lang first premise,
        ∃ other ∈ base lang second premise, BindingsRelated (EquationEquiv base lang) result other

/-- The premise of the run rewrite. -/
def runPremise : Premise :=
  .relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"]

theorem presentedPremises_probeWithRun :
    presentedPremises probeWithRun =
      [.relationQuery "ZeroQuery" [.fvar "space", .fvar "pattern", .fvar "template", .fvar "answer"],
        .relationQuery "ZeroEvaluate" [.fvar "space", .fvar "subject", .fvar "answer"],
        .relationQuery "CandidateNeed"
          [.fvar "space", .fvar "subject", .fvar "answer", .fvar "receipt"],
        runPremise] :=
  rfl

/-- A language with the rewrites and the equation of the probe with the run
constructor hands the same premises to the evaluator. -/
theorem presentedPremises_of_rules {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) :
    presentedPremises lang = presentedPremises probeWithRun := by
  unfold presentedPremises
  rw [rules, only.equations, probeWithRun_quoteDropOnly.equations]

/-- **Positive**: the evaluator that answers nothing. -/
theorem silentEvaluator_respectsStatics (lang : LanguageDef) :
    RespectsStatics silentEvaluator lang :=
  fun _ _ _ _ _ _ answered => by cases answered

/-- Two subjects with one contraction get the same answers from the
evaluator of a listing, each beside its own bindings. -/
theorem stepAnswers_related {Source : Type} (code : Source → Nat) (next : Source → List Source)
    {first second : Bindings} {subject : Pattern} (answer : String)
    (same : contract (applyBindings first subject) = contract (applyBindings second subject))
    {result : Bindings} (answered : result ∈ stepAnswers code next first subject answer) :
    ∃ reduct : Source, result = (answer, numeral (code reduct)) :: first ∧
      (answer, numeral (code reduct)) :: second ∈ stepAnswers code next second subject answer := by
  unfold stepAnswers at answered ⊢
  generalize contract (applyBindings first subject) = left at same answered
  generalize contract (applyBindings second subject) = right at same ⊢
  subst same
  split_ifs at answered ⊢ with known
  · obtain ⟨reduct, member, rfl⟩ := List.mem_map.mp answered
    exact ⟨reduct, rfl, List.mem_map.mpr ⟨reduct, member, rfl⟩⟩
  · cases answered

/-- **Positive**: the evaluator of every listing respects the static
equivalence of the probe with the run constructor. -/
theorem stepEvaluator_respectsStatics {Source : Type} (code : Source → Nat)
    (next : Source → List Source) : RespectsStatics (stepEvaluator code next) probeWithRun := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => (probeWithRun_quoteDropOnly.equiv equivalent).1
  rw [presentedPremises_probeWithRun] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp [stepEvaluator] at answered
  · simp [stepEvaluator] at answered
  · simp [stepEvaluator] at answered
  · have same := contract_applyBindings_congr contractions (.fvar "subject") rfl
    have answers : result ∈ stepAnswers code next first (.fvar "subject") "answer" := answered
    obtain ⟨reduct, rfl, other⟩ := stepAnswers_related code next "answer" same answers
    exact ⟨_, other, .cons ⟨rfl, .refl _⟩ related⟩

/-- **Negative**: the evaluator that counts the droppings of its subject
answers two spellings of one name differently. -/
theorem spellingEvaluator_not_respectsStatics :
    ¬ RespectsStatics (spellingEvaluator fanEnumeration.code fanEnumeration.reduct)
      probeWithRun := by
  intro respects
  have related : BindingsRelated
      (EquationEquiv (spellingEvaluator fanEnumeration.code fanEnumeration.reduct) probeWithRun)
      [("subject", spelledAtom 1 0)] [("subject", spelledAtom 0 0)] :=
    .cons ⟨rfl, probeWithRun_quoteDropOnly.equationEquiv_iff.mpr
      (by rw [contract_spelledAtom, contract_spelledAtom])⟩ .nil
  have answered : [("answer", spelledAtom 0 1), ("subject", spelledAtom 1 0)] ∈
      spellingEvaluator fanEnumeration.code fanEnumeration.reduct probeWithRun
        [("subject", spelledAtom 1 0)] runPremise := by
    show _ ∈ spellingAnswers fanEnumeration.code fanEnumeration.reduct _ (.fvar "subject") "answer"
    rw [spellingAnswers_eq fanEnumeration.injective fanEnumeration.reduct "answer"
      (term := (0 : Nat)) (by simp [applyBindings, contract_spelledAtom]; rfl)]
    have place : drops (applyBindings [("subject", spelledAtom 1 0)] (.fvar "subject")) - 1 = 1 := by
      simp [applyBindings, drops_spelledAtom]
    rw [place]
    refine List.mem_map.mpr ⟨(1 : Nat), ?_, rfl⟩
    show (1 : Nat) ∈ (some (1 : Nat)).toList
    exact List.mem_singleton.mpr rfl
  obtain ⟨other, otherAnswered, otherRelated⟩ :=
    respects runPremise (by rw [presentedPremises_probeWithRun]; simp) related _ answered
  have otherAnswers : other ∈ spellingAnswers fanEnumeration.code fanEnumeration.reduct
      [("subject", spelledAtom 0 0)] (.fvar "subject") "answer" := otherAnswered
  rw [spellingAnswers_eq fanEnumeration.injective fanEnumeration.reduct "answer"
    (term := (0 : Nat)) (by simp [applyBindings, contract_spelledAtom]; rfl)] at otherAnswers
  have place : drops (applyBindings [("subject", spelledAtom 0 0)] (.fvar "subject")) - 1 = 0 := by
    simp [applyBindings, drops_spelledAtom]
  rw [place] at otherAnswers
  obtain ⟨next, member, rfl⟩ := List.mem_map.mp otherAnswers
  simp only [fanEnumeration, if_true] at member
  have zero : next = (0 : Nat) := List.mem_singleton.mp member
  cases otherRelated with
  | cons pair _ =>
      have same := (probeWithRun_quoteDropOnly.equiv pair.2).1
      rw [contract_spelledAtom, contract_spelledAtom, zero] at same
      exact absurd (spelledAtom_injective same) (by decide)

/-! ## Left sides that read their redex up to the static equivalence -/

/-- What matches an application is an application of its label to as many
arguments. -/
theorem eq_apply_of_matched {label : String} {parameters : List Pattern} {redex : Pattern}
    {bindings : Bindings} (matched : bindings ∈ matchPattern (.apply label parameters) redex) :
    ∃ arguments, redex = .apply label arguments ∧ arguments.length = parameters.length := by
  cases matchPattern_sound matched with
  | apply _ length => exact ⟨_, rfl, length.symm⟩

/-- **A left side reads its redex up to the static equivalence**: two
redexes with one contraction are matched with bindings that differ by the
static equivalence only. -/
def ReadsUpToContraction (left : Pattern) : Prop :=
  ∀ {redex other : Pattern} {initial initial' : Bindings}, contract redex = contract other →
    initial ∈ matchPattern left redex → initial' ∈ matchPattern left other →
      BindingsRelated (fun first second => contract first = contract second) initial initial'

/-- **Positive**: a constructor other than quotation applied to two
variables. -/
theorem readsUpToContraction_two {label first second : String} (other : label ≠ "prime-quote")
    (distinct : first ≠ second) :
    ReadsUpToContraction (.apply label [.fvar first, .fvar second]) := by
  intro redex otherRedex initial initial' same matched matched'
  obtain ⟨arguments, rfl, length⟩ := eq_apply_of_matched matched
  obtain ⟨arguments', rfl, length'⟩ := eq_apply_of_matched matched'
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp length
  obtain ⟨a', b', rfl⟩ := List.length_eq_two.mp length'
  rw [contract_apply_of_ne other, contract_apply_of_ne other] at same
  simp only [List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, and_true,
    true_and] at same
  have shape : initial = [(second, b), (first, a)] := by
    simpa [matchPattern, matchArgs, mergeBindings, distinct] using matched
  have shape' : initial' = [(second, b'), (first, a')] := by
    simpa [matchPattern, matchArgs, mergeBindings, distinct] using matched'
  rw [shape, shape']
  exact .cons ⟨rfl, same.2⟩ (.cons ⟨rfl, same.1⟩ .nil)

/-- **Positive**: the same with three variables. -/
theorem readsUpToContraction_three {label first second third : String}
    (other : label ≠ "prime-quote") (firstSecond : first ≠ second) (firstThird : first ≠ third)
    (secondThird : second ≠ third) :
    ReadsUpToContraction (.apply label [.fvar first, .fvar second, .fvar third]) := by
  intro redex otherRedex initial initial' same matched matched'
  obtain ⟨arguments, rfl, length⟩ := eq_apply_of_matched matched
  obtain ⟨arguments', rfl, length'⟩ := eq_apply_of_matched matched'
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp length
  obtain ⟨a', b', c', rfl⟩ := List.length_eq_three.mp length'
  rw [contract_apply_of_ne other, contract_apply_of_ne other] at same
  simp only [List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq, and_true,
    true_and] at same
  have shape : initial = [(second, b), (third, c), (first, a)] := by
    simpa [matchPattern, matchArgs, mergeBindings, firstSecond, firstThird, secondThird,
      secondThird.symm] using matched
  have shape' : initial' = [(second, b'), (third, c'), (first, a')] := by
    simpa [matchPattern, matchArgs, mergeBindings, firstSecond, firstThird, secondThird,
      secondThird.symm] using matched'
  rw [shape, shape']
  exact .cons ⟨rfl, same.2.1⟩ (.cons ⟨rfl, same.2.2⟩ (.cons ⟨rfl, same.1⟩ .nil))

/-- **Negative**: the evaluation of a quoted name reads the atom beneath the
quotation, and one name is the quotation of two atoms that are apart. -/
theorem reflectedDemand_not_readsUpToContraction :
    ¬ ReadsUpToContraction reflectedDemandRewrite.left := by
  intro reads
  have related := reads (redex := evaluateName (.bvar 0) (quoted unitAtom))
    (other := evaluateName (.bvar 0) (quoted (dropped (quoted unitAtom))))
    (initial := [("subject", unitAtom), ("space", .bvar 0)])
    (initial' := [("subject", dropped (quoted unitAtom)), ("space", .bvar 0)])
    (by decide)
    (by simp [reflectedDemandRewrite, evaluateName, quoted, matchPattern, matchArgs, mergeBindings])
    (by simp [reflectedDemandRewrite, evaluateName, quoted, matchPattern, matchArgs, mergeBindings])
  cases related with
  | cons pair _ => exact absurd pair.2.symm dropped_quoted_ne_contract

/-! ## Finitely many reducts -/

/-- The answers to a list of premises, from bindings that differ from given
ones by the static equivalence only, lie in finitely many classes. -/
theorem exists_finals {base : BasePremiseEvaluator} {lang : LanguageDef}
    (respects : RespectsStatics base lang) :
    ∀ {premises : List Premise}, NoncontextualPremises premises →
      (∀ premise ∈ premises, premise ∈ presentedPremises lang) →
        ∀ start : Bindings, ∃ finals : List Bindings, ∀ {fuel : Nat} {initial final : Bindings},
          BindingsRelated (EquationEquiv base lang) initial start →
            PremisesAt base lang fuel initial premises final →
              ∃ other ∈ finals, BindingsRelated (EquationEquiv base lang) final other := by
  intro premises noncontextual
  induction noncontextual with
  | nil =>
      intro _ start
      refine ⟨[start], fun related evidence => ?_⟩
      cases evidence
      exact ⟨start, List.mem_singleton.mpr rfl, related⟩
  | @freshness condition premises _ ih =>
      intro presented start
      have tails := fun middle =>
        ih (fun premise member => presented premise (List.mem_cons_of_mem _ member)) middle
      refine ⟨(base lang start (.freshness condition)).flatMap fun middle =>
        Classical.choose (tails middle), fun related evidence => ?_⟩
      cases evidence with
      | cons head tail =>
          cases head with
          | freshness answered =>
              obtain ⟨middle, middleMember, middleRelated⟩ :=
                respects _ (presented _ (List.mem_cons_self ..)) related _ answered
              obtain ⟨other, otherMember, otherRelated⟩ :=
                Classical.choose_spec (tails middle) middleRelated tail
              exact ⟨other, List.mem_flatMap.mpr ⟨middle, middleMember, otherMember⟩, otherRelated⟩
  | @relationQuery relation arguments premises _ ih =>
      intro presented start
      have tails := fun middle =>
        ih (fun premise member => presented premise (List.mem_cons_of_mem _ member)) middle
      refine ⟨(base lang start (.relationQuery relation arguments)).flatMap fun middle =>
        Classical.choose (tails middle), fun related evidence => ?_⟩
      cases evidence with
      | cons head tail =>
          cases head with
          | relationQuery answered =>
              obtain ⟨middle, middleMember, middleRelated⟩ :=
                respects _ (presented _ (List.mem_cons_self ..)) related _ answered
              obtain ⟨other, otherMember, otherRelated⟩ :=
                Classical.choose_spec (tails middle) middleRelated tail
              exact ⟨other, List.mem_flatMap.mpr ⟨middle, middleMember, otherMember⟩, otherRelated⟩
  | @forAll collection parameter body premises _ ih =>
      intro presented start
      have tails := fun middle =>
        ih (fun premise member => presented premise (List.mem_cons_of_mem _ member)) middle
      refine ⟨(base lang start (.forAll collection parameter body)).flatMap fun middle =>
        Classical.choose (tails middle), fun related evidence => ?_⟩
      cases evidence with
      | cons head tail =>
          cases head with
          | forAll answered =>
              obtain ⟨middle, middleMember, middleRelated⟩ :=
                respects _ (presented _ (List.mem_cons_self ..)) related _ answered
              obtain ⟨other, otherMember, otherRelated⟩ :=
                Classical.choose_spec (tails middle) middleRelated tail
              exact ⟨other, List.mem_flatMap.mpr ⟨middle, middleMember, otherMember⟩, otherRelated⟩

/-- **A rule whose left side reads its redex up to the static equivalence
sends the redexes of one class to finitely many classes.** -/
theorem exists_contractions_of_reads {base : BasePremiseEvaluator} {lang : LanguageDef}
    (only : QuoteDropOnly lang) (respects : RespectsStatics base lang) {rule : RewriteRule}
    (member : rule ∈ lang.rewrites) (reads : ReadsUpToContraction rule.left)
    (noncontextual : NoncontextualPremises rule.premises) (aligned : ruleDepthAligned rule = true)
    (exact : isMatchCorrectAux rule.right = true) (redexClass : Pattern) :
    ∃ contractions : List Pattern, ∀ {redex : Pattern} {fuel : Nat} {initial final : Bindings},
      contract redex = redexClass → initial ∈ matchPattern rule.left redex →
        PremisesAt base lang fuel initial rule.premises final →
          contract (applyRuleBindings rule final) ∈ contractions := by
  by_cases inhabited : ∃ (redex : Pattern) (initial : Bindings),
      contract redex = redexClass ∧ initial ∈ matchPattern rule.left redex
  · obtain ⟨witness, start, witnessClass, witnessMatched⟩ := inhabited
    obtain ⟨finals, covered⟩ := exists_finals respects noncontextual
      (fun premise inRule => List.mem_append_left _ (List.mem_flatMap.mpr ⟨rule, member, inRule⟩))
      start
    refine ⟨finals.map fun final => contract (applyRuleBindings rule final),
      fun inClass matched premises => ?_⟩
    have related := reads (inClass.trans witnessClass.symm) matched witnessMatched
    obtain ⟨other, otherMember, otherRelated⟩ :=
      covered (related.mono fun _ _ same => only.equationEquiv_iff.mpr same) premises
    refine List.mem_map.mpr ⟨other, otherMember, ?_⟩
    rw [applyRuleBindings_eq_applyBindings _ _ aligned,
      applyRuleBindings_eq_applyBindings _ _ aligned]
    exact (contract_applyBindings_congr
      (otherRelated.mono fun _ _ equivalent => (only.equiv equivalent).1) _ exact).symm
  · exact ⟨[], fun inClass matched _ => (inhabited ⟨_, _, inClass, matched⟩).elim⟩

/-- The contraction of a quotation: what was dropped, or the quotation of the
contraction. -/
theorem contractRoot_quote_cases (inner : Pattern) :
    (∃ name, inner = .apply "prime-drop" [name] ∧ contractRoot "prime-quote" [inner] = name) ∨
      contractRoot "prime-quote" [inner] = .apply "prime-quote" [inner] := by
  cases inner with
  | apply label arguments =>
      rcases arguments with _ | ⟨name, _ | ⟨other, more⟩⟩
      · exact .inr (by simp [contractRoot])
      · by_cases isDrop : label = "prime-drop"
        · subst isDrop
          exact .inl ⟨name, rfl, by simp [contractRoot]⟩
        · exact .inr (by simp [contractRoot, isDrop])
      · exact .inr (by simp [contractRoot])
  | _ => exact .inr (by simp [contractRoot])

/-- What the evaluation of a quoted name matches, and what it rewrites to. -/
theorem reflectedDemand_shape {redex : Pattern} {initial : Bindings}
    (matched : initial ∈ matchPattern reflectedDemandRewrite.left redex) :
    ∃ space subject, redex = evaluateName space (quoted subject) ∧
      applyRuleBindings reflectedDemandRewrite initial = needRequest space subject := by
  have rebuilt : applyBindings initial reflectedDemandRewrite.left = redex :=
    matchPattern_correct matched (by decide)
  refine ⟨applyBindings initial (.fvar "space"), applyBindings initial (.fvar "subject"), ?_, ?_⟩
  · rw [← rebuilt]
    simp [reflectedDemandRewrite, evaluateName, quoted, applyBindings]
  · rw [applyRuleBindings_eq_applyBindings _ _ (by decide)]
    simp [reflectedDemandRewrite, needRequest, applyBindings]

/-- **The evaluation of a quoted name sends the redexes of one class to two
classes at most**: the Need for the dropping of the name, and the Need for
the atom that the name quotes, if it quotes one. -/
theorem exists_contractions_reflected (redexClass : Pattern) :
    ∃ contractions : List Pattern, ∀ {redex : Pattern} {initial : Bindings},
      contract redex = redexClass → initial ∈ matchPattern reflectedDemandRewrite.left redex →
        contract (applyRuleBindings reflectedDemandRewrite initial) ∈ contractions := by
  classical
  have unfolded : ∀ space subject : Pattern, contract (evaluateName space (quoted subject)) =
      .apply "prime-evaluate-name" [contract space, contractRoot "prime-quote" [contract subject]] := by
    intro space subject
    rw [evaluateName, contract_apply_of_ne (by decide)]
    simp [quoted, contract, contractList]
  have target : ∀ space subject : Pattern, contract (needRequest space subject) =
      needRequest (contract space) (contract subject) := by
    intro space subject
    rw [needRequest, contract_apply_of_ne (by decide)]
    rfl
  by_cases shape : ∃ space name, redexClass = .apply "prime-evaluate-name" [space, name]
  · obtain ⟨space, name, rfl⟩ := shape
    refine ⟨needRequest space (dropped name) ::
      (if quotation : ∃ atom, name = quoted atom then
        [needRequest space (Classical.choose quotation)] else []), ?_⟩
    intro redex initial inClass matched
    obtain ⟨spaceValue, subjectValue, rfl, applied⟩ := reflectedDemand_shape matched
    rw [applied, target]
    rw [unfolded] at inClass
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at inClass
    obtain ⟨rfl, nameEq⟩ := inClass
    rcases contractRoot_quote_cases (contract subjectValue) with ⟨dropName, isDrop, root⟩ | root
    · rw [root] at nameEq
      subst nameEq
      rw [isDrop]
      exact List.mem_cons_self ..
    · rw [root] at nameEq
      have quotation : ∃ atom, name = quoted atom := ⟨_, nameEq.symm⟩
      have chosen : Classical.choose quotation = contract subjectValue := by
        have spec := nameEq.trans (Classical.choose_spec quotation)
        simpa [quoted] using spec.symm
      refine List.mem_cons_of_mem _ ?_
      rw [dif_pos quotation, chosen]
      exact List.mem_singleton.mpr rfl
  · refine ⟨[], fun inClass matched => ?_⟩
    obtain ⟨spaceValue, subjectValue, rfl, -⟩ := reflectedDemand_shape matched
    rw [unfolded] at inClass
    exact (shape ⟨_, _, inClass.symm⟩).elim

/-- **Under an evaluator that respects the static equivalence, the redexes
of one class reduce into finitely many classes**, in every language with the
seven rewrites of the probe with the run constructor. -/
theorem exists_contractions {base : BasePremiseEvaluator} {lang : LanguageDef}
    (only : QuoteDropOnly lang) (rules : lang.rewrites = probeWithRun.rewrites)
    (respects : RespectsStatics base lang) (redexClass : Pattern) :
    ∃ contractions : List Pattern, ∀ {redex contractum : Pattern},
      contract redex = redexClass → Step base lang redex contractum →
        contract contractum ∈ contractions := by
  have inLang : ∀ {rule : RewriteRule}, rule ∈ probeWithRun.rewrites → rule ∈ lang.rewrites :=
    fun member => rules ▸ member
  obtain ⟨query, queryCovered⟩ := exists_contractions_of_reads only respects
    (rule := MeTTaZero.queryRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_three (by decide) (by decide) (by decide) (by decide))
    (.relationQuery .nil) (by decide) (by decide) redexClass
  obtain ⟨evaluation, evaluationCovered⟩ := exists_contractions_of_reads only respects
    (rule := MeTTaZero.evaluationRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_two (by decide) (by decide)) (.relationQuery .nil) (by decide)
    (by decide) redexClass
  obtain ⟨demand, demandCovered⟩ := exists_contractions_of_reads only respects
    (rule := evaluationDemandRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_two (by decide) (by decide)) .nil (by decide) (by decide) redexClass
  obtain ⟨need, needCovered⟩ := exists_contractions_of_reads only respects
    (rule := needRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_two (by decide) (by decide)) (.relationQuery .nil) (by decide)
    (by decide) redexClass
  obtain ⟨returned, returnedCovered⟩ := exists_contractions_of_reads only respects
    (rule := needReturnRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_two (by decide) (by decide)) .nil (by decide) (by decide) redexClass
  obtain ⟨reflected, reflectedCovered⟩ := exists_contractions_reflected redexClass
  obtain ⟨run, runCovered⟩ := exists_contractions_of_reads only respects
    (rule := runRewrite) (inLang (by rw [probeWithRun_rewrites]; simp))
    (readsUpToContraction_two (by decide) (by decide)) (.relationQuery .nil) (by decide)
    (by decide) redexClass
  refine ⟨query ++ evaluation ++ demand ++ need ++ returned ++ reflected ++ run,
    fun inClass step => ?_⟩
  obtain ⟨rule, member, fuel, initial, final, matched, premises, rfl⟩ := exists_rule_of_step step
  rw [rules, probeWithRun_rewrites] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have found := queryCovered inClass matched premises
    simp [found]
  · have found := evaluationCovered inClass matched premises
    simp [found]
  · have found := demandCovered inClass matched premises
    simp [found]
  · have found := needCovered inClass matched premises
    simp [found]
  · have found := returnedCovered inClass matched premises
    simp [found]
  · change PremisesAt base lang fuel initial [] final at premises
    cases premises
    have found := reflectedCovered inClass matched
    simp [found]
  · have found := runCovered inClass matched premises
    simp [found]

/-- **Under an evaluator that respects the static equivalence every term has
finitely many reducts up to the static equivalence**, in every language with
the equation, the sorts of quotation and the seven rewrites of the probe with
the run constructor. -/
theorem finite_reducts_of_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} (respects : RespectsStatics base lang)
    {interface : Contexts.Interface} (term : Contexts.Term lang interface) :
    ∃ reducts : List (Contexts.Term lang interface), ∀ next, TermStep base lang term next →
      ∃ reduct ∈ reducts, (termSetoid base lang interface).r next reduct := by
  classical
  obtain ⟨contractions, covered⟩ := exists_contractions only rules respects (contract term.1)
  refine ⟨contractions.filterMap fun contraction =>
    if known : ∃ candidate : Contexts.Term lang interface, contract candidate.1 = contraction then
      some (Classical.choose known) else none, ?_⟩
  rintro next ⟨redex, contractum, before, fired, after⟩
  have inList := covered (only.contract_eq before).symm fired
  have known : ∃ candidate : Contexts.Term lang interface,
      contract candidate.1 = contract contractum.1 := ⟨contractum, rfl⟩
  refine ⟨Classical.choose known, List.mem_filterMap.mpr ⟨_, inList, dif_pos known⟩, ?_⟩
  exact (only.termSetoid_iff sorted).mpr
    ((only.contract_eq after).symm.trans (Classical.choose_spec known).symm)

/-! ## What such an evaluator can host -/

/-- **A theory is finitely branching up to its static equivalence**: the
reducts of each term lie in finitely many classes. -/
def FinitelyBranching (theory : GSLT.{0}) : Prop :=
  ∀ term : theory.Term, ∃ reducts : List theory.Term, ∀ next, theory.rewrites term next →
    ∃ reduct ∈ reducts, theory.equations.r next reduct

/-- **Positive**: the successor theory. -/
theorem successorTheory_finitelyBranching : FinitelyBranching successorTheory := by
  intro term
  exact ⟨[(show Nat from term) + 1], fun next step => ⟨_, List.mem_singleton.mpr rfl, step⟩⟩

/-- **Negative**: the theory in which zero reduces to every number. -/
theorem fanTheory_not_finitelyBranching : ¬ FinitelyBranching fanTheory := by
  intro branching
  obtain ⟨found, covered⟩ := branching (0 : Nat)
  let reducts : List Nat := found
  have every : ∀ reduct : Nat, reduct ∈ reducts := fun reduct => by
    obtain ⟨other, member, same⟩ := covered reduct rfl
    exact (show reduct = other from same) ▸ member
  have bounded : ∀ reduct ∈ reducts, reduct ≤ reducts.sum := fun reduct member =>
    List.le_sum_of_mem member
  exact absurd (bounded _ (every (reducts.sum + 1))) (by omega)

/-- **Finite branching is image-finiteness modulo the equations**, for the
system with one label whose step is the step of the theory, whatever its
observations. -/
theorem finitelyBranching_iff_imageFiniteModulo {theory : GSLT.{0}}
    (observed : ObservedGSLT.{0} theory)
    (observes_resp : ∀ (atom : observed.Atom) {left right : theory.Term},
      theory.Equiv left right → (observed.observes atom left ↔ observed.observes atom right)) :
    FinitelyBranching theory ↔
      (HennessyMilner.System.ofObserved observed observes_resp).ImageFiniteModulo := by
  constructor
  · intro branching _ term
    obtain ⟨reducts, covered⟩ := branching term
    exact ⟨{reduct | reduct ∈ reducts}, List.finite_toSet reducts,
      fun target step => covered target step⟩
  · intro finite term
    obtain ⟨representatives, isFinite, covered⟩ := finite () term
    refine ⟨isFinite.toFinset.toList, fun next step => ?_⟩
    obtain ⟨representative, member, related⟩ := covered step
    exact ⟨representative, Finset.mem_toList.mpr (isFinite.mem_toFinset.mpr member), related⟩

/-- **Under an evaluator that respects the static equivalence the probe with
the run constructor is finitely branching at every interface.** -/
theorem runPresentation_finitelyBranching {base : BasePremiseEvaluator}
    (respects : RespectsStatics base probeWithRun) (interface : Contexts.Interface) :
    FinitelyBranching ((contextTheory base runPresentation).gslt interface) :=
  fun term => finite_reducts_of_respectsStatics probeWithRun_quoteDropOnly
    probeWithRun_quoteDropSorted rfl respects term

/-- **What a finitely branching candidate hosts on terms is finitely
branching.** -/
theorem finitelyBranching_of_hostedBy {source : GSLT.{0}} {candidate : ContextTheory.{0}}
    (branching : ∀ interface, FinitelyBranching (candidate.gslt interface))
    (hosted : HostedBy source.termsAlone candidate) : FinitelyBranching source := by
  classical
  obtain ⟨map, hosting⟩ := hosted
  obtain ⟨reflectsEquations, preserves, -⟩ := map.hosting_iff.mp hosting
  intro term
  obtain ⟨reducts, covered⟩ := branching (map.interface PUnit.unit) (map.term term)
  refine ⟨reducts.filterMap fun reduct =>
    if known : ∃ origin : source.Term,
        (candidate.equations (map.interface PUnit.unit)).r (map.term origin) reduct then
      some (Classical.choose known) else none, fun next step => ?_⟩
  obtain ⟨reduct, member, related⟩ :=
    covered _ (map.preservesRewrites_of_transitions preserves (interface := PUnit.unit) step)
  have known : ∃ origin : source.Term,
      (candidate.equations (map.interface PUnit.unit)).r (map.term origin) reduct :=
    ⟨next, related⟩
  refine ⟨Classical.choose known, List.mem_filterMap.mpr ⟨reduct, member, dif_pos known⟩, ?_⟩
  exact reflectsEquations (origin := PUnit.unit)
    ((candidate.equations _).iseqv.trans related
      ((candidate.equations _).iseqv.symm (Classical.choose_spec known)))

/-- **Exactly the finitely branching theories.**  A theory of the
λΠ-calculus modulo is hosted on terms by the probe with the run constructor,
under some evaluator that respects the static equivalence, exactly when each
of its terms has finitely many reducts. -/
theorem hostedBy_respecting_iff_finite (theory : Theory) :
    (∃ base : BasePremiseEvaluator, RespectsStatics base probeWithRun ∧
        HostedBy ((rewritingTheory theory).gslt ()).termsAlone
          (contextTheory base runPresentation)) ↔
      ∀ term : LF.Term, {next | Dedukti.Step theory term next}.Finite := by
  constructor
  · rintro ⟨base, respects, hosted⟩ term
    obtain ⟨reducts, covered⟩ :=
      finitelyBranching_of_hostedBy (runPresentation_finitelyBranching respects) hosted term
    refine (List.finite_toSet reducts).subset fun next step => ?_
    obtain ⟨reduct, member, same⟩ := covered next step
    exact (show next = reduct from same) ▸ member
  · intro finite
    let listing : StepListing ((rewritingTheory theory).gslt ()) :=
      StepListing.ofFinite _ (inferInstanceAs (Countable LF.Term)) finite fun _ _ same => same
    exact ⟨stepEvaluator listing.code listing.next, stepEvaluator_respectsStatics _ _,
      runMap listing, runMap_hosting listing⟩

/-- **Positive**: every theory given by a table whose rules determine their
right sides. -/
theorem determinedTabular_hostedBy_respecting {theory : Theory} {table : RuleTable}
    (tabular : theory.Tabular table) (determined : DeterminedTable table) :
    ∃ base : BasePremiseEvaluator, RespectsStatics base probeWithRun ∧
      HostedBy ((rewritingTheory theory).gslt ()).termsAlone
        (contextTheory base runPresentation) :=
  (hostedBy_respecting_iff_finite theory).mpr fun term =>
    (step_finite_of_rootStep_finite (rootStep_finite_of_rightDetermined determined) term).subset
      fun _ step => tabular.step_iff.mp step

/-- **Negative**: the theory of the table of the one rule `c ⟶ x`. -/
theorem freeTable_not_hostedBy_respecting {base : BasePremiseEvaluator}
    (respects : RespectsStatics base probeWithRun) :
    ¬ HostedBy ((rewritingTheory (Theory.ofTable {freeRule})).gslt ()).termsAlone
      (contextTheory base runPresentation) := by
  intro hosted
  have finite := (hostedBy_respecting_iff_finite (Theory.ofTable {freeRule})).mp
    ⟨base, respects, hosted⟩ (.con "c")
  exact Set.infinite_range_of_injective (fun first second same => LF.Term.var.inj same)
    (finite.subset (by
      rintro _ ⟨index, rfl⟩
      exact (evaluator_reduces_to_every (.var index)).2))

/-- **No evaluator that respects the static equivalence makes the probe with
the run constructor a host of the theories given by a table.** -/
theorem not_hostOf_tabular_terms_of_respectsStatics {base : BasePremiseEvaluator}
    (respects : RespectsStatics base probeWithRun) :
    ¬ HostOf (contextTheory base runPresentation) TabularTheory .terms .hosting :=
  fun hosts => freeTable_not_hostedBy_respecting respects
    (hosts _ ⟨rewritingTheory (Theory.ofTable {freeRule}),
      ⟨_, {freeRule}, Theory.ofTable_tabular _, rfl⟩, (), rfl⟩)

/-- **The evaluator under which the presentation hosts them all does not
respect the static equivalence.** -/
theorem tableRunEvaluator_not_respectsStatics : ¬ RespectsStatics tableRunEvaluator probeWithRun :=
  fun respects =>
    not_hostOf_tabular_terms_of_respectsStatics respects runPresentation_hostOf_tabular_terms

/-- The evaluator that hosts the tables whose rules determine their right
sides does. -/
theorem determinedEvaluator_respectsStatics : RespectsStatics determinedEvaluator probeWithRun :=
  stepEvaluator_respectsStatics _ _

#print axioms contract_applyBindings_congr
#print axioms silentEvaluator_respectsStatics
#print axioms stepEvaluator_respectsStatics
#print axioms spellingEvaluator_not_respectsStatics
#print axioms readsUpToContraction_two
#print axioms reflectedDemand_not_readsUpToContraction
#print axioms exists_contractions
#print axioms finite_reducts_of_respectsStatics
#print axioms fanTheory_not_finitelyBranching
#print axioms finitelyBranching_iff_imageFiniteModulo
#print axioms finitelyBranching_of_hostedBy
#print axioms hostedBy_respecting_iff_finite
#print axioms determinedTabular_hostedBy_respecting
#print axioms freeTable_not_hostedBy_respecting
#print axioms not_hostOf_tabular_terms_of_respectsStatics
#print axioms tableRunEvaluator_not_respectsStatics
#print axioms determinedEvaluator_respectsStatics

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

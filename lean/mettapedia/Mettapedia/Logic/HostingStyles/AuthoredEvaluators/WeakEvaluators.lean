import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.RunAnswers

/-!
# A notion of weak evaluator, tested

An authored evaluator is inspectable; that does not bound what it computes.
This module looks for a property of the *answers* of an evaluator to the run
premise that does bound what the run rewrite hosts.  Two notions are stated
and tested.

## The notion as first worded, and why it bounds nothing

`ReadsThroughRootMatches answers`: the answers at a subject depend on the
subject only through the matches, at its root, of the left sides that the
space stores (`rootMatches`).

* The matching evaluator has it (`matching_readsThroughRootMatches`).
* An evaluator that steps beneath the root does not
  (`beneath_not_readsThroughRootMatches`).
* **The bound fails for it.**  A stored equation whose left side is a variable
  matches every subject and binds the whole subject, so at a space that stores
  one, *every* function of the subject depends on the subject only through the
  matches at its root (`guarded_readsThroughRootMatches`).  Hence an evaluator
  with the property hosts, through one run rewrite, every listed theory
  (`guarded_hosts_listed`), the pure λ-calculus with beta at every position
  among them (`rootMatches_bound_fails`).  The notion says where the evaluator
  looks, and not what it does with what it finds.

## The corrected notion, and its bound

`AnswersByStoredRules answers`: the answers are the instances, at the root of
the subject, of rules that the stored atoms are read as, one rule for an atom
at most; the space and the subject are read up to the static equivalence.
The evaluator may choose how an atom is read; it only *places* what a match
binds.

* The matching evaluator has it (`matching_answersByStoredRules`); so its
  authored form does.
* An evaluator that steps beneath the root does not
  (`beneath_not_answersByStoredRules`), and neither does the evaluator of the
  counterexample (`guarded_not_answersByStoredRules`).
* **The bound**, for every evaluator that answers the run premise by such
  answers:
  * a subject has at most as many answers as the space stores atoms
    (`AnswersByStoredRules.length_le`);
  * a run has at most as many reducts, pairwise apart, as its space stores
    atoms (`storedRules_reducts_le_storeSize`), the general form of
    `matching_reducts_le_storeSize`;
  * a step out of a run is an instance at the root of a rule read off a
    stored atom (`storedRules_step_instance`);
  * so no theory that branches without bound along one reduction is hosted
    (`storedRules_not_hostedBy_of_unboundedBranching`): no theory of the
    λΠ-calculus modulo, and not one first-order rule applied at every
    position.
* The upper bound of `instances_hostedBy_matching_iff` needs less: under
  every evaluator that respects the static equivalence, the instances of a
  table are hosted only if its rules determine their right sides
  (`determinedTable_of_instances_hostedBy`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory FirstOrderTable)
open Mettapedia.GSLT.Dedukti.Language (metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## The matches at the root -/

/-- The match, at the root of a subject, of the left side of a stored
equation. -/
def leftMatch (subject atom : Pattern) : Option Bindings :=
  match atom with
  | .apply label arguments =>
      if label = "=" then
        match arguments with
        | [left, _] => if firstOrder left = true then ruleMatch left subject else none
        | _ => none
      else none
  | _ => none

/-- **The matches, at the root of a subject, of the left sides that a space
stores**, one for each stored atom. -/
def rootMatches (space subject : Pattern) : List (Option Bindings) :=
  (storedAtoms space).map (leftMatch subject)

/-- **Negative**: an atom that is no equation has no left side to match. -/
theorem leftMatch_unit (subject : Pattern) : leftMatch subject unitAtom = none := by
  simp [leftMatch, unitAtom]

/-- **Negative**: the empty space stores no left side. -/
theorem rootMatches_emptySpace (subject : Pattern) : rootMatches emptySpace subject = [] := by
  simp [rootMatches]

/-- What a match places: the instance of the right side of a stored
equation. -/
def placeRight (atom : Pattern) (found : Option Bindings) : Option Pattern :=
  match atom with
  | .apply _ arguments =>
      match arguments with
      | [_, right] =>
          if firstOrder right = true then found.map fun bindings => ruleInstance bindings right
          else none
      | _ => none
  | _ => none

/-- **The answer of a stored atom is what its match places.** -/
theorem atomResult_eq_placeRight (subject atom : Pattern) :
    atomResult subject atom = placeRight atom (leftMatch subject atom) := by
  cases atom with
  | apply label arguments =>
      rcases arguments with _ | ⟨left, _ | ⟨right, _ | ⟨third, rest⟩⟩⟩
      · by_cases equation : label = "=" <;> simp [atomResult, placeRight, equation]
      · by_cases equation : label = "=" <;> simp [atomResult, placeRight, equation]
      · by_cases equation : label = "="
        · cases leftSide : firstOrder left <;> cases rightSide : firstOrder right <;>
            simp [atomResult, placeRight, leftMatch, equation, leftSide, rightSide]
        · cases rightSide : firstOrder right <;>
            simp [atomResult, placeRight, leftMatch, equation, rightSide]
      · by_cases equation : label = "=" <;> simp [atomResult, placeRight, equation]
  | _ => simp [atomResult, placeRight]

/-- **The notion as first worded**: the answers at a subject depend on the
subject only through the matches, at its root, of the left sides that the
space stores. -/
def ReadsThroughRootMatches (answers : Pattern → Pattern → List Pattern) : Prop :=
  ∀ space subject other : Pattern,
    rootMatches (contract space) (contract subject) = rootMatches (contract space) (contract other) →
      answers space subject = answers space other

/-- **Positive**: the matching evaluator. -/
theorem matching_readsThroughRootMatches :
    ReadsThroughRootMatches fun space subject =>
      matchResults (contract space) (contract subject) := by
  intro space subject other same
  show matchResults (contract space) (contract subject) =
    matchResults (contract space) (contract other)
  rw [matchResults_eq_filterMap, matchResults_eq_filterMap]
  apply List.filterMap_congr
  intro atom member
  rw [atomResult_eq_placeRight, atomResult_eq_placeRight,
    List.map_inj_left.mp same atom member]

/-! ## Answers by stored rules -/

/-- **The instances, at the root of a subject, of a list of rules.** -/
def rootInstances (rules : List (Pattern × Pattern)) (subject : Pattern) : List Pattern :=
  rules.flatMap fun rule =>
    (matchPattern rule.1 subject).map fun bindings => applyBindings bindings rule.2

/-- **Positive**: the rule `x ⟶ x` has the subject as its one instance. -/
theorem rootInstances_identity (subject : Pattern) :
    rootInstances [(.fvar "x", .fvar "x")] subject = [subject] := by
  simp [rootInstances, matchPattern, applyBindings]

/-- **Negative**: no rule, no instance. -/
theorem rootInstances_nil (subject : Pattern) : rootInstances [] subject = [] := rfl

/-- **The corrected notion**: the answers are the instances, at the root of
the subject, of rules that the stored atoms are read as, one rule for an atom
at most, with first-order left sides; the space and the subject are read up to
the static equivalence. -/
def AnswersByStoredRules (answers : Pattern → Pattern → List Pattern) : Prop :=
  ∃ read : Pattern → Option (Pattern × Pattern),
    (∀ atom rule, read atom = some rule → isMatchCorrectAux rule.1 = true) ∧
      ∀ space subject : Pattern,
        answers space subject =
          rootInstances ((storedAtoms (contract space)).filterMap read) (contract subject)

/-- The rule that the matching evaluator reads a stored atom as. -/
def storedRule (atom : Pattern) : Option (Pattern × Pattern) :=
  match MeTTaZero.viewEquation? atom with
  | some (left, right) =>
      if isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right) then
        some (asRule left, asRule right)
      else none
  | none => none

/-- **Positive**: an equation between two variable atoms is read as a rule
between two pattern variables. -/
theorem storedRule_variables (index : Pattern) :
    storedRule (.apply "=" [variableAtom index, variableAtom index]) =
      some (asRule (variableAtom index), asRule (variableAtom index)) := by
  simp [storedRule, MeTTaZero.viewEquation?, variableAtom, asRule, isMatchCorrectAux]

/-- **Negative**: an atom that is no equation is read as no rule. -/
theorem storedRule_unit : storedRule unitAtom = none := by
  simp [storedRule, MeTTaZero.viewEquation?, unitAtom]

theorem atomResults_eq_storedRule (subject atom : Pattern) :
    atomResults subject atom = rootInstances (storedRule atom).toList subject := by
  unfold atomResults storedRule
  cases MeTTaZero.viewEquation? atom with
  | none => rfl
  | some sides =>
      obtain ⟨left, right⟩ := sides
      by_cases exact : (isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right)) = true
      · simp [exact, rootInstances]
      · simp [exact, rootInstances]

theorem rootInstances_filterMap {α : Type} (read : α → Option (Pattern × Pattern))
    (subject : Pattern) :
    ∀ items : List α, rootInstances (items.filterMap read) subject =
      items.flatMap fun item => rootInstances (read item).toList subject
  | [] => rfl
  | item :: items => by
      rw [List.filterMap_cons, List.flatMap_cons, ← rootInstances_filterMap read subject items]
      cases read item with
      | none => rfl
      | some rule => simp [rootInstances]

/-- **Positive**: the matching evaluator. -/
theorem matching_answersByStoredRules :
    AnswersByStoredRules fun space subject =>
      matchResults (contract space) (contract subject) := by
  refine ⟨storedRule, ?_, fun space subject => ?_⟩
  · intro atom rule found
    unfold storedRule at found
    cases sides : MeTTaZero.viewEquation? atom with
    | none => simp [sides] at found
    | some pair =>
        obtain ⟨left, right⟩ := pair
        by_cases exact :
            (isMatchCorrectAux (asRule left) && isMatchCorrectAux (asRule right)) = true
        · simp only [sides, exact, if_true, Option.some.injEq] at found
          subst found
          simp only [Bool.and_eq_true] at exact
          exact exact.1
        · simp [sides, exact] at found
  · show matchResults (contract space) (contract subject) = _
    rw [rootInstances_filterMap, matchResults]
    congr 1
    funext atom
    exact atomResults_eq_storedRule (contract subject) atom

/-- So the answers of the matching program to `PrimeStep` are answers by
stored rules: the authored form has the property of the function. -/
theorem matchingAuthored_answersByStoredRules :
    AnswersByStoredRules fun space subject =>
      matchingAuthored.answers "PrimeStep" [space, subject] := by
  have same : (fun space subject => matchingAuthored.answers "PrimeStep" [space, subject]) =
      fun space subject => matchResults (contract space) (contract subject) := by
    funext space subject
    rw [matchingAuthored_answers, matchingAnswers_run]
  rw [same]
  exact matching_answersByStoredRules

/-! ## The bound -/

theorem rootInstances_length_le {rules : List (Pattern × Pattern)}
    (exact : ∀ rule ∈ rules, isMatchCorrectAux rule.1 = true) (subject : Pattern) :
    (rootInstances rules subject).length ≤ rules.length := by
  unfold rootInstances
  induction rules with
  | nil => simp
  | cons rule rules ih =>
      rw [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      have one := matchPattern_length_le_one rule.1 (exact rule (List.mem_cons_self ..)) subject
      have rest := ih fun other member => exact other (List.mem_cons_of_mem _ member)
      omega

/-- The rules read off the stored atoms have first-order left sides. -/
theorem filterMap_read_exact {read : Pattern → Option (Pattern × Pattern)}
    (exact : ∀ atom rule, read atom = some rule → isMatchCorrectAux rule.1 = true)
    (atoms : List Pattern) : ∀ rule ∈ atoms.filterMap read, isMatchCorrectAux rule.1 = true := by
  intro rule member
  obtain ⟨atom, -, found⟩ := List.mem_filterMap.mp member
  exact exact atom rule found

/-- **A subject has at most as many answers as the space stores atoms.** -/
theorem AnswersByStoredRules.length_le {answers : Pattern → Pattern → List Pattern}
    (weak : AnswersByStoredRules answers) (space subject : Pattern) :
    (answers space subject).length ≤ (storedAtoms (contract space)).length := by
  obtain ⟨read, exact, shape⟩ := weak
  rw [shape]
  exact (rootInstances_length_le (filterMap_read_exact exact _) _).trans
    (List.length_filterMap_le _ _)

/-- Such answers read the space and the subject up to the static
equivalence. -/
theorem AnswersByStoredRules.reads {answers : Pattern → Pattern → List Pattern}
    (weak : AnswersByStoredRules answers) {space subject otherSpace otherSubject : Pattern}
    (spaces : contract space = contract otherSpace)
    (subjects : contract subject = contract otherSubject) :
    answers space subject = answers otherSpace otherSubject := by
  obtain ⟨read, -, shape⟩ := weak
  rw [shape, shape, spaces, subjects]

/-- So their evaluator respects the static equivalence. -/
theorem AnswersByStoredRules.respectsStatics {answers : Pattern → Pattern → List Pattern}
    (weak : AnswersByStoredRules answers) {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) : RespectsStatics (runEvaluator answers) lang :=
  runEvaluator_respectsStatics only rules fun _ _ _ _ spaces subjects => by
    rw [weak.reads spaces subjects]

/-- **A step out of a run is an instance, at the root of the subject, of a
rule read off a stored atom.** -/
theorem storedRules_step_instance {lang : LanguageDef}
    (rules : lang.rewrites = probeWithRun.rewrites) {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    {read : Pattern → Option (Pattern × Pattern)}
    (shape : ∀ space subject : Pattern, answers space subject =
      rootInstances ((storedAtoms (contract space)).filterMap read) (contract subject))
    {redex contractum : Pattern} (runHead : head? (contract redex) = some "prime-run")
    (step : Step base lang redex contractum) :
    ∃ (space subject atom : Pattern) (rule : Pattern × Pattern) (bindings : Bindings),
      redex = runPattern space subject ∧ atom ∈ storedAtoms (contract space) ∧
        read atom = some rule ∧ bindings ∈ matchPattern rule.1 (contract subject) ∧
          contractum = runPattern space (applyBindings bindings rule.2) := by
  obtain ⟨space, subject, result, rfl, found, rfl⟩ := answered_step_inv rules byRun runHead step
  rw [shape] at found
  obtain ⟨rule, inRules, instance_⟩ := List.mem_flatMap.mp found
  obtain ⟨atom, stored, readAs⟩ := List.mem_filterMap.mp inRules
  obtain ⟨bindings, matched, rfl⟩ := List.mem_map.mp instance_
  exact ⟨space, subject, atom, rule, bindings, rfl, stored, readAs, matched, rfl⟩

/-- A step out of a run keeps the size of its space, for every evaluator that
answers the run premise by a function. -/
theorem answered_step_storeSize {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    {interface : Contexts.Interface} {source target : Contexts.Term lang interface}
    (isRun : head? (contract source.1) = some "prime-run")
    (step : TermStep base lang source target) : storeSize target.1 = storeSize source.1 := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  have sourceClass := only.contract_eq before
  have targetClass := only.contract_eq after
  obtain ⟨space, subject, result, redexShape, -, contractumShape⟩ :=
    answered_step_inv rules byRun (by rw [← sourceClass]; exact isRun) fired
  have left : storeSize source.1 = storeSize redex.1 := by rw [storeSize, storeSize, sourceClass]
  have right : storeSize target.1 = storeSize contractum.1 := by
    rw [storeSize, storeSize, targetClass]
  rw [left, right, redexShape, contractumShape, storeSize_runPattern, storeSize_runPattern]

/-- **A run has at most as many reducts, pairwise apart, as its space stores
atoms**, under every evaluator whose answers to the run premise are answers by
stored rules. -/
theorem storedRules_reducts_le_storeSize {lang : LanguageDef} (only : QuoteDropOnly lang)
    (sorted : QuoteDropSorted lang) (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} {answers : Pattern → Pattern → List Pattern}
    (byRun : AnswersRunBy base answers) (weak : AnswersByStoredRules answers)
    {interface : Contexts.Interface} (term : Contexts.Term lang interface)
    (isRun : head? (contract term.1) = some "prime-run")
    (reducts : List (Contexts.Term lang interface))
    (each : ∀ reduct ∈ reducts, TermStep base lang term reduct)
    (apart : reducts.Pairwise fun first second =>
      ¬ (termSetoid base lang interface).r first second) :
    reducts.length ≤ storeSize term.1 := by
  obtain ⟨read, exact, shape⟩ := weak
  let listed : List Pattern :=
    (rootInstances ((storedAtoms (runSpaceOf (contract term.1))).filterMap read)
      (runSubjectOf (contract term.1))).map
        fun answer => runPattern (runSpaceOf (contract term.1)) (contract answer)
  have covered : ∀ reduct ∈ reducts, contract reduct.1 ∈ listed := by
    intro reduct member
    obtain ⟨redex, contractum, before, fired, after⟩ := each reduct member
    have sourceClass := only.contract_eq before
    obtain ⟨space, subject, result, redexShape, found, contractumShape⟩ :=
      answered_step_inv rules byRun (by rw [← sourceClass]; exact isRun) fired
    have termShape : contract term.1 = runPattern (contract space) (contract subject) := by
      rw [sourceClass, redexShape, contract_runPattern']
    have spaceEq : runSpaceOf (contract term.1) = contract space := by rw [termShape]; rfl
    have subjectEq : runSubjectOf (contract term.1) = contract subject := by rw [termShape]; rfl
    rw [← only.contract_eq after, contractumShape, contract_runPattern']
    refine List.mem_map.mpr ⟨result, ?_, ?_⟩
    · rw [spaceEq, subjectEq, ← shape]
      exact found
    · rw [spaceEq]
  have distinct : (reducts.map fun reduct => contract reduct.1).Nodup :=
    List.pairwise_map.mpr (apart.imp fun differ same =>
      differ ((only.termSetoid_iff sorted).mpr same))
  have bounded := (List.subperm_of_subset distinct (by
    intro contraction member
    obtain ⟨reduct, inReducts, rfl⟩ := List.mem_map.mp member
    exact covered reduct inReducts)).length_le
  rw [List.length_map] at bounded
  have short : listed.length ≤ storeSize term.1 := by
    show ((rootInstances _ _).map _).length ≤ _
    rw [List.length_map]
    exact (rootInstances_length_le (filterMap_read_exact exact _) _).trans
      (List.length_filterMap_le _ _)
  exact bounded.trans short

/-- **Through one run rewrite, answers by stored rules host no theory that
branches without bound along one reduction.**  The images of the terms of the
reduction are runs in one space, and a run has no more reducts apart than its
space stores atoms. -/
theorem storedRules_not_hostedBy_of_unboundedBranching {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    (weak : AnswersByStoredRules answers) {source : GSLT.{0}}
    (branching : UnboundedBranching source) :
    ¬ HostedBy source.termsAlone (contextTheory base spacePresentation) := by
  rintro ⟨map, hosting⟩
  obtain ⟨reflectsEquations, preserves, -⟩ := map.hosting_iff.mp hosting
  obtain ⟨term, chain, branches⟩ := branching
  have moves : ∀ {first second : source.Term}, source.rewrites first second →
      TermStep base probeWithSpace (map.term (origin := PUnit.unit) first) (map.term second) :=
    fun step => map.preservesRewrites_of_transitions preserves (interface := PUnit.unit) step
  have lower : ∀ {first second : Contexts.Term probeWithSpace (map.interface PUnit.unit)},
      TermStep base probeWithSpace first second →
        ¬ head? (contract first.1) = some "prime-run" →
          patternRank second.1 < patternRank first.1 ∧
            ¬ head? (contract second.1) = some "prime-run" :=
    fun step notRun =>
      ⟨(space_termStep_lowers_or_runs step).resolve_right fun runs => notRun runs.1,
        fun isRun => notRun ((runRules_termStep_run_iff probeWithSpace_quoteDropOnly
          probeWithSpace_rewrites step).mpr isRun)⟩
  have runs : ∀ index, head? (contract (map.term (origin := PUnit.unit) (term index)).1) =
      some "prime-run" := by
    intro index
    by_contra notRun
    have first := lower (moves (chain index)) notRun
    have second := lower (moves (chain (index + 1))) first.2
    have third := lower (moves (chain (index + 1 + 1))) second.2
    have fourth := lower (moves (chain (index + 1 + 1 + 1))) third.2
    have top := patternRank_le (map.term (origin := PUnit.unit) (term index)).1
    omega
  have sizes : ∀ index, storeSize (map.term (origin := PUnit.unit) (term index)).1 =
      storeSize (map.term (origin := PUnit.unit) (term 0)).1 := by
    intro index
    induction index with
    | zero => rfl
    | succ index ih =>
        rw [answered_step_storeSize probeWithSpace_quoteDropOnly probeWithSpace_rewrites byRun
          (runs index) (moves (chain index)), ih]
  obtain ⟨reducts, length, each, apart⟩ :=
    branches (storeSize (map.term (origin := PUnit.unit) (term 0)).1 + 1)
  let images : List (Contexts.Term probeWithSpace (map.interface PUnit.unit)) :=
    reducts.map fun reduct => map.term (origin := PUnit.unit) reduct
  have lengths : images.length = reducts.length := List.length_map _
  have bounded := storedRules_reducts_le_storeSize probeWithSpace_quoteDropOnly
    probeWithSpace_quoteDropSorted probeWithSpace_rewrites byRun weak _ (runs _) images
    (by
      intro image member
      obtain ⟨reduct, inReducts, rfl⟩ := List.mem_map.mp member
      exact moves (each reduct inReducts))
    (List.pairwise_map.mpr (apart.imp fun differ related =>
      differ (reflectsEquations (origin := PUnit.unit) related)))
  have size := sizes (storeSize (map.term (origin := PUnit.unit) (term 0)).1 + 1)
  omega

/-- In particular no theory of the λΠ-calculus modulo. -/
theorem storedRules_not_hostedBy_rewritingTheory {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    (weak : AnswersByStoredRules answers) (theory : Theory) :
    ¬ HostedBy ((rewritingTheory theory).gslt ()).termsAlone
      (contextTheory base spacePresentation) :=
  storedRules_not_hostedBy_of_unboundedBranching byRun weak
    (rewritingTheory_unboundedBranching theory)

/-- And not the one rule `c ⟶ c c` applied at every position. -/
theorem storedRules_not_hostedBy_doublingContextual {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    (weak : AnswersByStoredRules answers) :
    ¬ HostedBy (contextualTheory doublingTable).termsAlone
      (contextTheory base spacePresentation) :=
  storedRules_not_hostedBy_of_unboundedBranching byRun weak doublingContextual_unboundedBranching

/-- **The upper bound at the root needs less**: under every evaluator that
respects the static equivalence, the instances of a table are hosted only if
its rules determine their right sides. -/
theorem determinedTable_of_instances_hostedBy {base : BasePremiseEvaluator}
    (respects : RespectsStatics base probeWithSpace) {table : RuleTable}
    (hosted : HostedBy (instanceTheory table).termsAlone (contextTheory base spacePresentation)) :
    DeterminedTable table := by
  intro rule member
  by_contra free
  obtain ⟨term, infinite⟩ := infinite_instances_of_not_rightDetermined member free
  obtain ⟨reducts, covered⟩ := finitelyBranching_of_hostedBy
    (spacePresentation_finitelyBranching respects) hosted term
  refine infinite ((List.finite_toSet reducts).subset fun next step => ?_)
  obtain ⟨reduct, inReducts, same⟩ := covered next step
  exact (show next = reduct from same) ▸ inReducts

/-! ## An evaluator that steps beneath the root -/

/-- The answers of the stored atoms of a space, at the root of a subject. -/
def rootAnswers (space subject : Pattern) : List Pattern :=
  (storedAtoms space).filterMap (atomResult subject)

theorem rootAnswers_eq_matchResults (space subject : Pattern) :
    rootAnswers space subject = matchResults space subject :=
  (matchResults_eq_filterMap space subject).symm

mutual
  /-- **The answers at every position of a subject**: those at its root, and
  for an application those at every position of one of its arguments, in
  place. -/
  def everywhere (space : Pattern) : Pattern → List Pattern
    | .apply label arguments =>
        rootAnswers space (.apply label arguments) ++
          (everywhereList space arguments).map (Pattern.apply label)
    | .bvar index => rootAnswers space (.bvar index)
    | .fvar name => rootAnswers space (.fvar name)
    | .lambda binder body => rootAnswers space (.lambda binder body)
    | .multiLambda arity binders body => rootAnswers space (.multiLambda arity binders body)
    | .subst body replacement => rootAnswers space (.subst body replacement)
    | .collection kind elements rest => rootAnswers space (.collection kind elements rest)

  /-- The lists in which one element has stepped. -/
  def everywhereList (space : Pattern) : List Pattern → List (List Pattern)
    | [] => []
    | pattern :: patterns =>
        (everywhere space pattern).map (· :: patterns) ++
          (everywhereList space patterns).map (pattern :: ·)
end

/-- **An evaluator that steps beneath the root**: the matching evaluator,
applied at every position of the subject. -/
def beneathAnswers (space subject : Pattern) : List Pattern :=
  everywhere (contract space) (contract subject)

/-- A space that stores the one closed rule `unit ⟶ (unit = unit)`. -/
def oneRuleSpace : Pattern := spaceOfAtoms [.apply "=" [unitAtom, numeral 1]]

/-- **Positive**: at the root it answers as the matching evaluator. -/
theorem beneathAnswers_root : beneathAnswers oneRuleSpace unitAtom = [numeral 1] := by decide

/-- **Negative**: it does not read its subject through the matches at the
root.  Two subjects that the stored left side does not match at the root, with
different labels above the same redex, get different answers. -/
theorem beneath_not_readsThroughRootMatches : ¬ ReadsThroughRootMatches beneathAnswers := by
  intro reads
  have same := reads oneRuleSpace (.apply "prime-inert-dependency" [unitAtom])
    (.apply "prime-request-dependency" [unitAtom]) (by decide)
  revert same
  decide

/-- **Negative**: its answers are not answers by stored rules.  The numeral of
one, `(unit = unit)`, gets two answers in a space of one atom. -/
theorem beneath_not_answersByStoredRules : ¬ AnswersByStoredRules beneathAnswers := by
  intro weak
  have short := weak.length_le oneRuleSpace (numeral 1)
  revert short
  decide

/-! ## The bound fails for the notion as first worded -/

/-- An equation between two variable atoms of one index: its left side matches
every subject. -/
def catchAll : Pattern := .apply "=" [variableAtom unitAtom, variableAtom unitAtom]

/-- The space that stores it, and nothing else. -/
def guardSpace : Pattern := spaceOfAtoms [catchAll]

/-- **Any function of the subject, at the spaces that store the equation
first.**  Elsewhere it answers nothing. -/
def guarded (inner : Pattern → List Pattern) (space subject : Pattern) : List Pattern :=
  if (storedAtoms (contract space)).head? = some catchAll then inner (contract subject) else []

theorem leftMatch_catchAll (subject : Pattern) :
    leftMatch subject catchAll = some [(metaName (numeralValue unitAtom), subject)] := by
  simp [leftMatch, catchAll, variableAtom, firstOrder, ruleMatch, indexOf]

/-- **Every such function reads its subject through the matches at the root.**
At a space that stores the equation, the match of its left side binds the
whole subject. -/
theorem guarded_readsThroughRootMatches (inner : Pattern → List Pattern) :
    ReadsThroughRootMatches (guarded inner) := by
  intro space subject other same
  unfold guarded
  by_cases guard : (storedAtoms (contract space)).head? = some catchAll
  · rw [if_pos guard, if_pos guard]
    cases stored : storedAtoms (contract space) with
    | nil => simp [stored] at guard
    | cons first rest =>
        rw [stored] at guard
        obtain rfl : first = catchAll := by simpa using guard
        unfold rootMatches at same
        rw [stored, List.map_cons, List.map_cons, leftMatch_catchAll, leftMatch_catchAll] at same
        obtain ⟨subjects, -⟩ : contract subject = contract other ∧
            ∀ atom ∈ rest, leftMatch (contract subject) atom = leftMatch (contract other) atom := by
          simpa using same
        rw [subjects]
  · rw [if_neg guard, if_neg guard]

theorem guardSpace_sorted :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Space") guardSpace :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem guardSpace_contracted : contract guardSpace = guardSpace := by decide

theorem guarded_guardSpace (inner : Pattern → List Pattern) {written subject : Pattern}
    (spaces : contract written = guardSpace) :
    guarded inner written subject = inner (contract subject) := by
  unfold guarded
  rw [spaces, if_pos (by decide)]

/-- **Negative**: at the empty space it answers nothing. -/
theorem guarded_emptySpace (inner : Pattern → List Pattern) (subject : Pattern) :
    guarded inner emptySpace subject = [] := by
  unfold guarded
  rw [if_neg (by decide)]

/-- The answers that run a listed theory: at the numeral of a term, the
numerals of its reducts. -/
noncomputable def listingAnswers {source : GSLT.{0}} (listing : StepListing source)
    (subject : Pattern) : List Pattern :=
  open Classical in
  if known : ∃ term, subject = numeral (listing.code term) then
    (listing.next (Classical.choose known)).map fun reduct => numeral (listing.code reduct)
  else []

theorem listingAnswers_numeral {source : GSLT.{0}} (listing : StepListing source)
    (term : source.Term) :
    listingAnswers listing (numeral (listing.code term)) =
      (listing.next term).map fun reduct => numeral (listing.code reduct) := by
  have known : ∃ other, numeral (listing.code term) = numeral (listing.code other) := ⟨term, rfl⟩
  have chosen : Classical.choose known = term :=
    listing.injective (numeral_injective (Classical.choose_spec known)).symm
  unfold listingAnswers
  rw [dif_pos known, chosen]

/-- **Negative**: at a subject that is no numeral it answers nothing. -/
theorem listingAnswers_bvar {source : GSLT.{0}} (listing : StepListing source) (index : Nat) :
    listingAnswers listing (.bvar index) = [] := by
  unfold listingAnswers
  rw [dif_neg]
  rintro ⟨term, same⟩
  cases numeralCase : listing.code term with
  | zero => rw [numeralCase] at same; simp [numeral, unitAtom] at same
  | succ count => rw [numeralCase] at same; simp [numeral] at same

/-- **Through one run rewrite, an evaluator that reads its subject through
the matches at the root hosts every listed theory.** -/
theorem guarded_hosts_listed {source : GSLT.{0}} (listing : StepListing source) :
    HostedBy source.termsAlone
      (contextTheory (runEvaluator (guarded (listingAnswers listing))) spacePresentation) := by
  refine hostedBy_of_runAnswers (runEvaluator_answersRunBy _) guardSpace_sorted
    guardSpace_contracted (fun term => numeral (listing.code term))
    (fun term => numeral_closedAtom _) (fun term => contract_numeral _)
    (fun _ _ same => listing.injective (numeral_injective same)) listing.discrete ?_ ?_
  · intro term next step
    rw [guarded_guardSpace _ guardSpace_contracted, contract_numeral, listingAnswers_numeral]
    exact List.mem_map.mpr ⟨next, (listing.branches term next).mp step, rfl⟩
  · intro written subject term result spaces subjects found
    rw [guarded_guardSpace _ spaces, subjects, listingAnswers_numeral] at found
    obtain ⟨reduct, member, rfl⟩ := List.mem_map.mp found
    exact ⟨reduct, (listing.branches term reduct).mpr member, contract_numeral _⟩

/-- Its evaluator respects the static equivalence. -/
theorem guarded_respectsStatics (inner : Pattern → List Pattern) :
    RespectsStatics (runEvaluator (guarded inner)) probeWithSpace :=
  runEvaluator_respectsStatics probeWithSpace_quoteDropOnly probeWithSpace_rewrites
    fun _ _ _ _ spaces subjects => by simp only [guarded, spaces, subjects]

/-- The pure λ-calculus, as the theory of the empty table, is listed. -/
noncomputable def pureListing :
    StepListing ((rewritingTheory (Theory.ofTable ∅)).gslt ()) :=
  tableListing ∅ fun _ member => absurd member (Finset.notMem_empty _)

/-- **The bound fails for the notion as first worded.**  There are answers
that depend on the subject only through the matches at its root, whose
evaluator respects the static equivalence, and under which one run rewrite
hosts the pure λ-calculus with beta at every position: a theory that branches
without bound along one reduction, which no answers by stored rules host. -/
theorem rootMatches_bound_fails :
    ∃ answers : Pattern → Pattern → List Pattern,
      ReadsThroughRootMatches answers ∧
        RespectsStatics (runEvaluator answers) probeWithSpace ∧
          UnboundedBranching ((rewritingTheory (Theory.ofTable ∅)).gslt ()) ∧
            HostedBy ((rewritingTheory (Theory.ofTable ∅)).gslt ()).termsAlone
              (contextTheory (runEvaluator answers) spacePresentation) :=
  ⟨guarded (listingAnswers pureListing), guarded_readsThroughRootMatches _,
    guarded_respectsStatics _, rewritingTheory_unboundedBranching _,
    guarded_hosts_listed pureListing⟩

/-- **Negative**: those answers are not answers by stored rules. -/
theorem guarded_not_answersByStoredRules :
    ¬ AnswersByStoredRules (guarded (listingAnswers pureListing)) := fun weak =>
  storedRules_not_hostedBy_of_unboundedBranching (runEvaluator_answersRunBy _) weak
    (rewritingTheory_unboundedBranching _) (guarded_hosts_listed pureListing)

#print axioms atomResult_eq_placeRight
#print axioms matching_readsThroughRootMatches
#print axioms matching_answersByStoredRules
#print axioms matchingAuthored_answersByStoredRules
#print axioms AnswersByStoredRules.length_le
#print axioms AnswersByStoredRules.respectsStatics
#print axioms storedRules_step_instance
#print axioms storedRules_reducts_le_storeSize
#print axioms storedRules_not_hostedBy_of_unboundedBranching
#print axioms storedRules_not_hostedBy_rewritingTheory
#print axioms storedRules_not_hostedBy_doublingContextual
#print axioms determinedTable_of_instances_hostedBy
#print axioms beneath_not_readsThroughRootMatches
#print axioms beneath_not_answersByStoredRules
#print axioms guarded_readsThroughRootMatches
#print axioms guarded_hosts_listed
#print axioms rootMatches_bound_fails
#print axioms guarded_not_answersByStoredRules

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

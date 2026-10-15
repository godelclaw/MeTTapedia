import Mettapedia.Logic.HostingStyles.PrimeCandidate.MatchingEvaluator
import Mettapedia.Logic.HostingStyles.PrimeCandidate.DeterminedExactly

/-!
# What the matching evaluator cannot host: beta, and steps beneath the root

Under the matching evaluator the extended probe hosts the theories of
first-order rule instances.  This module gives the limit of that route with
a witness.

* **First-order matching is deterministic** (`matchPattern_length_le_one`):
  a first-order pattern matches a term in one way at most.  So a space
  answers a subject with at most as many atoms as it stores
  (`matchResults_length_le`).
* **The run rewrite keeps the space**, and a transition goes from a run to a
  run or between terms that are no runs (`runRules_termStep_run_iff`,
  `matching_step_storeSize`).  So along one reduction of runs the number of
  reducts that are pairwise apart is bounded by the size of the space of its
  first term (`matching_reducts_le_storeSize`).
* **A theory that branches without bound along one reduction is not hosted**
  (`UnboundedBranching`, `not_hostedBy_matching_of_unboundedBranching`).
* **Every theory of the λΠ-calculus modulo branches without bound along one
  reduction** (`rewritingTheory_unboundedBranching`): the term
  `(λx. x x (I I)) (λx. x x (I I))` reduces to itself applied to one more
  redex `I I`, and each of the redexes it has collected can be contracted
  alone.  Beta and steps beneath the root are all it takes.

Hence **the extended probe under the matching evaluator hosts no theory given
by a table, on terms** (`matchingCandidate_hosts_no_tabular_terms`), and with
all contexts it is no host of them under any evaluator
(`spacePresentation_not_hostOf_tabular_contexts`).  What beta needs is what
the candidate does not have: a step beneath a constructor, and a rewrite that
substitutes.

Steps beneath the root are an obstruction by themselves.  The one closed
first-order rule `c ⟶ c c`, applied at every position and without beta
(`contextualTheory`), branches without bound along one reduction
(`doublingContextual_unboundedBranching`), so it is not hosted
(`doublingContextual_not_hostedBy_matching`); the instances of the same rule
at the root are (`doublingInstances_hostedBy_matching`).

At the root the class is exact: for a first-order table, the instances of
its rules are hosted **exactly when the rules determine their right sides**
(`instances_hostedBy_matching_iff`), and that is the condition on the right
sides in the class of the hosting theorem (`boundTable_iff_determinedTable`).

Under the matching evaluator the extended probe has no rank
(`matchingCandidate_not_rank`): a stored rule `c ⟶ c` makes a run step to
itself.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.PrimeCandidate

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable RootStep rewritingTheory FirstOrderTable)
open Mettapedia.GSLT.LanguageDef.LFContextualBetaEta (Context)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## First-order matching is deterministic -/

theorem matchArgs_length_le_one :
    ∀ (patterns : List Pattern),
      (∀ pattern ∈ patterns, ∀ term, (matchPattern pattern term).length ≤ 1) →
        ∀ terms, (matchArgs patterns terms).length ≤ 1
  | [], _, [] => by simp [matchArgs]
  | [], _, _ :: _ => by simp [matchArgs]
  | _ :: _, _, [] => by simp [matchArgs]
  | pattern :: patterns, each, term :: terms => by
      have head := each pattern (List.mem_cons_self ..) term
      have tail := matchArgs_length_le_one patterns
        (fun other member => each other (List.mem_cons_of_mem _ member)) terms
      rw [matchArgs]
      rcases found : matchPattern pattern term with _ | ⟨first, _ | ⟨second, rest⟩⟩
      · simp
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact (List.length_filterMap_le _ _).trans tail
      · rw [found] at head
        simp at head

/-- **A first-order pattern matches a term in one way at most.** -/
theorem matchPattern_length_le_one :
    ∀ pattern : Pattern, isMatchCorrectAux pattern = true →
      ∀ term, (matchPattern pattern term).length ≤ 1 := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro _ term
      cases term with
      | bvar other =>
          rw [matchPattern]
          split_ifs <;> simp
      | _ => simp [matchPattern]
  | hfvar name => intro _ term; simp [matchPattern]
  | happly label arguments ih =>
      intro exact term
      have each := isMatchCorrectAux_of_mem (by simpa [isMatchCorrectAux] using exact)
      cases term with
      | apply other targs =>
          rw [matchPattern]
          split_ifs
          · exact matchArgs_length_le_one arguments
              (fun pattern member => ih pattern member (each pattern member)) targs
          · simp
      | _ => simp [matchPattern]
  | hlambda binder body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hmultiLambda arity binders body _ => intro exact; simp [isMatchCorrectAux] at exact
  | hsubst body replacement _ _ => intro exact; simp [isMatchCorrectAux] at exact
  | hcollection kind elements rest _ => intro exact; simp [isMatchCorrectAux] at exact

/-- **Negative**: a bag pattern matches in as many ways as the bag has
members. -/
theorem matchPattern_bag_two :
    (matchPattern (.collection .hashBag [.fvar "x"] (some "rest"))
      (.collection .hashBag [unitAtom, numeral 1] none)).length = 2 := by
  simp [matchPattern, matchBag, mergeBindings, List.zipIdx]

/-- A stored atom answers a subject once at most. -/
theorem atomResults_length_le_one (subject atom : Pattern) :
    (atomResults subject atom).length ≤ 1 := by
  unfold atomResults
  split
  · next left right _ =>
      split_ifs with exact
      · rw [List.length_map]
        simp only [Bool.and_eq_true] at exact
        exact matchPattern_length_le_one _ exact.1 subject
      · simp
  · simp

/-- **A space answers a subject with at most as many atoms as it stores.** -/
theorem matchResults_length_le (space subject : Pattern) :
    (matchResults space subject).length ≤ (storedAtoms space).length := by
  unfold matchResults
  induction storedAtoms space with
  | nil => simp
  | cons atom atoms ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have one := atomResults_length_le_one subject atom
      omega

/-! ## Runs stay runs, and keep their space -/

/-- **A transition goes from a run to a run, or between terms that are no
runs**, in every language with the seven rewrites and for every evaluator. -/
theorem runRules_termStep_run_iff {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) {base : BasePremiseEvaluator}
    {interface : Contexts.Interface} {source target : Contexts.Term lang interface}
    (step : TermStep base lang source target) :
    head? (contract source.1) = some "prime-run" ↔
      head? (contract target.1) = some "prime-run" := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  rw [only.contract_eq before, ← only.contract_eq after]
  rcases runRules_step_heads rules fired with ⟨edge, member, sourceHead, targetHead⟩ | runs
  · simp only [probeEdges, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [head?_contract sourceHead (by decide), head?_contract targetHead (by decide)]
        constructor <;> intro wrong <;> exact absurd wrong (by decide)
  · rw [head?_contract runs.1 (by decide), head?_contract runs.2 (by decide)]

/-- The space of a run; the unit atom for a pattern that is no run. -/
def runSpaceOf : Pattern → Pattern
  | .apply "prime-run" [space, _] => space
  | _ => unitAtom

/-- The subject of a run; the unit atom for a pattern that is no run. -/
def runSubjectOf : Pattern → Pattern
  | .apply "prime-run" [_, subject] => subject
  | _ => unitAtom

/-- **The size of the space of a term**: the number of atoms stored in the
space of the run that the term contracts to, and zero for a term that
contracts to no run. -/
def storeSize (pattern : Pattern) : Nat := (storedAtoms (runSpaceOf (contract pattern))).length

/-- **Positive**: the run of an atom in a space of two atoms. -/
theorem storeSize_run_two :
    storeSize (runPattern (spaceOfAtoms [unitAtom, numeral 1]) unitAtom) = 2 := by
  decide

/-- **Negative**: a term that is no run has size zero. -/
theorem storeSize_need : storeSize (needRequest emptySpace unitAtom) = 0 := by decide

theorem storeSize_runPattern (space subject : Pattern) :
    storeSize (runPattern space subject) = (storedAtoms (contract space)).length := by
  rw [storeSize, contract_runPattern']
  rfl

/-- **The run rewrite keeps the space**: under the matching evaluator a
transition out of a run does not change the size of its space. -/
theorem matching_step_storeSize {interface : Contexts.Interface}
    {source target : Contexts.Term probeWithSpace interface}
    (isRun : head? (contract source.1) = some "prime-run")
    (step : TermStep matchingEvaluator probeWithSpace source target) :
    storeSize target.1 = storeSize source.1 := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  have sourceClass := probeWithSpace_quoteDropOnly.contract_eq before
  have targetClass := probeWithSpace_quoteDropOnly.contract_eq after
  obtain ⟨space, subject, answer, redexShape, -, contractumShape⟩ :=
    matching_run_step_inv (by rw [← sourceClass]; exact isRun) fired
  have left : storeSize source.1 = storeSize redex.1 := by rw [storeSize, storeSize, sourceClass]
  have right : storeSize target.1 = storeSize contractum.1 := by
    rw [storeSize, storeSize, targetClass]
  rw [left, right, redexShape, contractumShape, storeSize_runPattern, storeSize_runPattern]

/-- **A run has at most as many reducts that are pairwise apart as its space
stores atoms.** -/
theorem matching_reducts_le_storeSize {interface : Contexts.Interface}
    (term : Contexts.Term probeWithSpace interface)
    (isRun : head? (contract term.1) = some "prime-run")
    (reducts : List (Contexts.Term probeWithSpace interface))
    (each : ∀ reduct ∈ reducts, TermStep matchingEvaluator probeWithSpace term reduct)
    (apart : reducts.Pairwise fun first second =>
      ¬ (termSetoid matchingEvaluator probeWithSpace interface).r first second) :
    reducts.length ≤ storeSize term.1 := by
  let answers : List Pattern :=
    (matchResults (runSpaceOf (contract term.1)) (runSubjectOf (contract term.1))).map
      fun answer => runPattern (runSpaceOf (contract term.1)) (contract answer)
  have covered : ∀ reduct ∈ reducts, contract reduct.1 ∈ answers := by
    intro reduct member
    obtain ⟨redex, contractum, before, fired, after⟩ := each reduct member
    have sourceClass := probeWithSpace_quoteDropOnly.contract_eq before
    obtain ⟨space, subject, answer, redexShape, found, contractumShape⟩ :=
      matching_run_step_inv (by rw [← sourceClass]; exact isRun) fired
    have shape : contract term.1 = runPattern (contract space) (contract subject) := by
      rw [sourceClass, redexShape, contract_runPattern']
    have spaceEq : runSpaceOf (contract term.1) = contract space := by rw [shape]; rfl
    have subjectEq : runSubjectOf (contract term.1) = contract subject := by rw [shape]; rfl
    rw [← probeWithSpace_quoteDropOnly.contract_eq after, contractumShape, contract_runPattern']
    refine List.mem_map.mpr ⟨answer, ?_, ?_⟩
    · rw [spaceEq, subjectEq]
      exact found
    · rw [spaceEq]
  have distinct : (reducts.map fun reduct => contract reduct.1).Nodup :=
    List.pairwise_map.mpr (apart.imp fun differ same =>
      differ ((probeWithSpace_quoteDropOnly.termSetoid_iff probeWithSpace_quoteDropSorted).mpr same))
  have bounded := (List.subperm_of_subset distinct (by
    intro contraction member
    obtain ⟨reduct, inReducts, rfl⟩ := List.mem_map.mp member
    exact covered reduct inReducts)).length_le
  rw [List.length_map] at bounded
  have listed : answers.length ≤ storeSize term.1 := by
    show ((matchResults _ _).map _).length ≤ _
    rw [List.length_map]
    exact matchResults_length_le _ _
  exact bounded.trans listed

/-! ## Branching without bound along one reduction -/

/-- **A theory branches without bound along one reduction**: a sequence of
terms, each reducing to the next, the term at each place with as many
reducts, pairwise apart, as the number of the place. -/
def UnboundedBranching (source : GSLT.{0}) : Prop :=
  ∃ term : Nat → source.Term, (∀ index, source.rewrites (term index) (term (index + 1))) ∧
    ∀ index, ∃ reducts : List source.Term, reducts.length = index ∧
      (∀ reduct ∈ reducts, source.rewrites (term index) reduct) ∧
        reducts.Pairwise fun first second => ¬ source.equations.r first second

/-- **Negative**: the successor theory, where every term has one reduct. -/
theorem successorTheory_not_unboundedBranching : ¬ UnboundedBranching successorTheory := by
  rintro ⟨term, -, branches⟩
  obtain ⟨reducts, length, each, apart⟩ := branches 2
  obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp length
  have firstStep := each first (List.mem_cons_self ..)
  have secondStep := each second (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  have differ := List.rel_of_pairwise_cons apart (List.mem_singleton.mpr rfl)
  exact differ (Eq.trans firstStep (Eq.symm secondStep))

/-- **The extended probe under the matching evaluator hosts no theory that
branches without bound along one reduction.**  The images of the terms of
the reduction are runs in one space, and a run has no more reducts apart than
its space stores atoms. -/
theorem not_hostedBy_matching_of_unboundedBranching {source : GSLT.{0}}
    (branching : UnboundedBranching source) : ¬ HostedBy source.termsAlone matchingCandidate := by
  rintro ⟨map, hosting⟩
  obtain ⟨reflectsEquations, preserves, -⟩ := map.hosting_iff.mp hosting
  obtain ⟨term, chain, branches⟩ := branching
  have moves : ∀ {first second : source.Term}, source.rewrites first second →
      TermStep matchingEvaluator probeWithSpace (map.term (origin := PUnit.unit) first)
        (map.term second) :=
    fun step => map.preservesRewrites_of_transitions preserves (interface := PUnit.unit) step
  have lower : ∀ {first second : Contexts.Term probeWithSpace (map.interface PUnit.unit)},
      TermStep matchingEvaluator probeWithSpace first second →
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
    | succ index ih => rw [matching_step_storeSize (runs index) (moves (chain index)), ih]
  obtain ⟨reducts, length, each, apart⟩ :=
    branches (storeSize (map.term (origin := PUnit.unit) (term 0)).1 + 1)
  let images : List (Contexts.Term probeWithSpace (map.interface PUnit.unit)) :=
    reducts.map fun reduct => map.term (origin := PUnit.unit) reduct
  have lengths : images.length = reducts.length := List.length_map _
  have bounded := matching_reducts_le_storeSize _ (runs _) images
    (by
      intro image member
      obtain ⟨reduct, inReducts, rfl⟩ := List.mem_map.mp member
      exact moves (each reduct inReducts))
    (List.pairwise_map.mpr (apart.imp fun differ related =>
      differ (reflectsEquations (origin := PUnit.unit) related)))
  have size := sizes (storeSize (map.term (origin := PUnit.unit) (term 0)).1 + 1)
  omega

/-! ## Every theory of the λΠ-calculus modulo branches without bound -/

/-- `λx : Type. x`. -/
def identityTerm : LF.Term := .lam (.srt .type) (.var 0)

/-- `(λx. x) (λx. x)`, a redex. -/
def selfIdentity : LF.Term := .app identityTerm identityTerm

/-- `x x (I I)`. -/
def growerBody : LF.Term := .app (.app (.var 0) (.var 0)) selfIdentity

/-- `λx. x x (I I)`. -/
def grower : LF.Term := .lam (.srt .type) growerBody

/-- The self-application of `λx. x x (I I)`, applied to `count` redexes
`I I`. -/
def grown : Nat → LF.Term
  | 0 => .app grower grower
  | count + 1 => .app (grown count) selfIdentity

/-- The term `grown count` with the redex of one place contracted. -/
def contractedAt : Nat → Nat → LF.Term
  | 0, _ => grown 0
  | count + 1, place =>
      if place = count then .app (grown count) identityTerm
      else .app (contractedAt count place) selfIdentity

theorem selfIdentity_step (theory : Theory) : Dedukti.Step theory selfIdentity identityTerm := by
  have contracted : LFTyping.subst0 identityTerm (.var 0) = identityTerm := by decide
  have root : RootStep theory selfIdentity (LFTyping.subst0 identityTerm (.var 0)) :=
    .beta (.srt .type) (.var 0) identityTerm
  rw [contracted] at root
  exact Dedukti.Step.root root

/-- **Each term of the sequence reduces to the next**: the self-application
reproduces itself beside one more redex. -/
theorem grown_step (theory : Theory) : ∀ count, Dedukti.Step theory (grown count) (grown (count + 1))
  | 0 => by
      have contracted : LFTyping.subst0 grower growerBody = .app (.app grower grower) selfIdentity := by
        decide
      have root : RootStep theory (.app grower grower) (LFTyping.subst0 grower growerBody) :=
        .beta (.srt .type) growerBody grower
      rw [contracted] at root
      exact Dedukti.Step.root root
  | count + 1 => (grown_step theory count).plug (.appFunction .hole selfIdentity)

/-- Each collected redex can be contracted alone. -/
theorem contractedAt_step (theory : Theory) :
    ∀ count place, place < count → Dedukti.Step theory (grown count) (contractedAt count place)
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, place, below => by
      by_cases last : place = count
      · rw [contractedAt, if_pos last]
        exact (selfIdentity_step theory).plug (.appArgument (grown count) .hole)
      · rw [contractedAt, if_neg last]
        exact (contractedAt_step theory count place (by omega)).plug (.appFunction .hole selfIdentity)

/-- Contracting the redexes of two places gives two terms. -/
theorem contractedAt_injective :
    ∀ count first second, first < count → second < count →
      contractedAt count first = contractedAt count second → first = second
  | 0, _, _, below, _, _ => absurd below (Nat.not_lt_zero _)
  | count + 1, first, second, firstBelow, secondBelow, same => by
      by_cases firstLast : first = count <;> by_cases secondLast : second = count
      · rw [firstLast, secondLast]
      · rw [contractedAt, contractedAt, if_pos firstLast, if_neg secondLast] at same
        exact absurd (LF.Term.app.inj same).2 (by decide)
      · rw [contractedAt, contractedAt, if_neg firstLast, if_pos secondLast] at same
        exact absurd (LF.Term.app.inj same).2.symm (by decide)
      · rw [contractedAt, contractedAt, if_neg firstLast, if_neg secondLast] at same
        exact contractedAt_injective count first second (by omega) (by omega)
          (LF.Term.app.inj same).1

/-- **Positive**: every theory of the λΠ-calculus modulo branches without
bound along one reduction.  It takes beta and steps beneath the root, which
each of them has. -/
theorem rewritingTheory_unboundedBranching (theory : Theory) :
    UnboundedBranching ((rewritingTheory theory).gslt ()) := by
  refine ⟨grown, fun index => grown_step theory index, fun index => ?_⟩
  have length : ((List.range index).map (contractedAt index)).length = index := by
    rw [List.length_map, List.length_range]
  refine ⟨(List.range index).map (contractedAt index), length, ?_, ?_⟩
  · intro reduct member
    have listed : reduct ∈ (List.range index).map (contractedAt index) := member
    obtain ⟨place, inRange, rfl⟩ := List.mem_map.mp listed
    exact contractedAt_step theory index place (List.mem_range.mp inRange)
  · have distinct : ((List.range index).map (contractedAt index)).Nodup :=
      List.Nodup.map_on (fun first firstMember second secondMember same =>
        contractedAt_injective index first second (List.mem_range.mp firstMember)
          (List.mem_range.mp secondMember) same) List.nodup_range
    exact distinct

/-! ## The limit of the route -/

/-- **The extended probe under the matching evaluator hosts no theory of the
λΠ-calculus modulo on terms.** -/
theorem matching_not_hostedBy_rewritingTheory (theory : Theory) :
    ¬ HostedBy ((rewritingTheory theory).gslt ()).termsAlone matchingCandidate :=
  not_hostedBy_matching_of_unboundedBranching (rewritingTheory_unboundedBranching theory)

/-- **It hosts no theory given by a table, on terms**: each of them has beta
beneath contexts. -/
theorem matchingCandidate_hosts_no_tabular_terms {source : ContextTheory.{0}}
    (tabular : TabularTheory source) (interface : source.Interface) :
    ¬ HostedBy (source.gslt interface).termsAlone matchingCandidate := by
  obtain ⟨theory, table, -, rfl⟩ := tabular
  exact matching_not_hostedBy_rewritingTheory theory

/-- So it is no host of the theories given by a table, nor of those whose
rules determine their right sides. -/
theorem matchingCandidate_not_hostOf_tabular_terms :
    ¬ HostOf matchingCandidate TabularTheory .terms .hosting :=
  fun hosts => matchingCandidate_hosts_no_tabular_terms pure_tabular ()
    (hosts _ ⟨_, pure_tabular, (), rfl⟩)

theorem matchingCandidate_not_hostOf_determinedTabular_terms :
    ¬ HostOf matchingCandidate DeterminedTabularTheory .terms .hosting :=
  fun hosts => matchingCandidate_hosts_no_tabular_terms pure_tabular ()
    (hosts _ ⟨_, pure_determinedTabular, (), rfl⟩)

/-- **With all contexts the extension is no host of the theories given by a
table, under any evaluator**: its contexts use each hole once. -/
theorem spacePresentation_not_hostOf_tabular_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (contextTheory base spacePresentation) TabularTheory .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_tabular
    ((QuoteDropOnly.linearSize spacePresentation probeWithSpace_quoteDropOnly
      base).isEmpty_contextMap_of_discards
      (rewritingTheory_discards Theory.empty) ⟨(.srt .type : LF.Term)⟩).false map

/-! ## Steps beneath the root, without beta -/

/-- **A step of a table beneath a context**: an instance of a rule of the
table at one position, and no beta. -/
def ContextualInstance (table : RuleTable) (source target : LF.Term) : Prop :=
  ∃ (context : Context) (redex contractum : LF.Term),
    RuleInstance table redex contractum ∧ source = context.plug redex ∧
      target = context.plug contractum

/-- **The theory of the instances of the rules of a table at every
position**: λΠ terms compared by identity; a term steps by an instance of a
rule beneath a context. -/
def contextualTheory (table : RuleTable) : GSLT.{0} where
  Term := LF.Term
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := ContextualInstance table
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- A step beneath a context stays one beneath a larger context. -/
theorem ContextualInstance.plug {table : RuleTable} (context : Context) {source target : LF.Term}
    (step : ContextualInstance table source target) :
    ContextualInstance table (context.plug source) (context.plug target) := by
  obtain ⟨inner, redex, contractum, fired, rfl, rfl⟩ := step
  exact ⟨context.comp inner, redex, contractum, fired, (Context.plug_comp ..).symm,
    (Context.plug_comp ..).symm⟩

/-- **Negative**: the empty table has no step. -/
theorem not_contextualInstance_empty {source target : LF.Term} :
    ¬ ContextualInstance ∅ source target := by
  rintro ⟨_, _, _, ⟨rule, member, _⟩, _⟩
  exact absurd member (Finset.notMem_empty rule)

/-- `c ⟶ c c`: one closed first-order rule. -/
def doublingRule : Dedukti.RewriteRule := ⟨.con "c", .app (.con "c") (.con "c")⟩

/-- The table of that rule. -/
def doublingTable : RuleTable := {doublingRule}

theorem doublingTable_firstOrder : FirstOrderTable doublingTable := by
  intro rule member
  rw [Finset.mem_singleton.mp member]
  decide

theorem doublingTable_bound : BoundTable doublingTable := by
  intro rule member
  rw [Finset.mem_singleton.mp member]
  decide

theorem doubling_instance :
    RuleInstance doublingTable (.con "c") (.app (.con "c") (.con "c")) :=
  ⟨doublingRule, Finset.mem_singleton_self _, fun _ => .srt .type, by simp [doublingRule],
    by simp [doublingRule]⟩

/-- `c c … c`, nested to the left, with one more `c` than `count`. -/
def doubled : Nat → LF.Term
  | 0 => .con "c"
  | count + 1 => .app (doubled count) (.con "c")

/-- The term `doubled count` with the `c` of one place doubled. -/
def doubledAt : Nat → Nat → LF.Term
  | 0, _ => .con "c"
  | count + 1, place =>
      if place = count then .app (doubled count) (.app (.con "c") (.con "c"))
      else .app (doubledAt count place) (.con "c")

/-- **Positive**: each term of the sequence steps to the next, at its
leftmost `c`. -/
theorem doubled_step :
    ∀ count, ContextualInstance doublingTable (doubled count) (doubled (count + 1))
  | 0 => ⟨.hole, _, _, doubling_instance, rfl, rfl⟩
  | count + 1 => (doubled_step count).plug (.appFunction .hole (.con "c"))

/-- Each `c` can be doubled alone. -/
theorem doubledAt_step :
    ∀ count place, place < count →
      ContextualInstance doublingTable (doubled count) (doubledAt count place)
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, place, below => by
      by_cases last : place = count
      · rw [doubledAt, if_pos last]
        exact ⟨.appArgument (doubled count) .hole, _, _, doubling_instance, rfl, rfl⟩
      · rw [doubledAt, if_neg last]
        exact (doubledAt_step count place (by omega)).plug (.appFunction .hole (.con "c"))

/-- Doubling at two places gives two terms. -/
theorem doubledAt_injective :
    ∀ count first second, first < count → second < count →
      doubledAt count first = doubledAt count second → first = second
  | 0, _, _, below, _, _ => absurd below (Nat.not_lt_zero _)
  | count + 1, first, second, firstBelow, secondBelow, same => by
      by_cases firstLast : first = count <;> by_cases secondLast : second = count
      · rw [firstLast, secondLast]
      · rw [doubledAt, doubledAt, if_pos firstLast, if_neg secondLast] at same
        exact absurd (LF.Term.app.inj same).2 (by decide)
      · rw [doubledAt, doubledAt, if_neg firstLast, if_pos secondLast] at same
        exact absurd (LF.Term.app.inj same).2.symm (by decide)
      · rw [doubledAt, doubledAt, if_neg firstLast, if_neg secondLast] at same
        exact doubledAt_injective count first second (by omega) (by omega)
          (LF.Term.app.inj same).1

/-- **One closed first-order rule, applied at every position, branches
without bound along one reduction.** -/
theorem doublingContextual_unboundedBranching :
    UnboundedBranching (contextualTheory doublingTable) := by
  refine ⟨doubled, fun index => doubled_step index, fun index => ?_⟩
  have length : ((List.range index).map (doubledAt index)).length = index := by
    rw [List.length_map, List.length_range]
  refine ⟨(List.range index).map (doubledAt index), length, ?_, ?_⟩
  · intro reduct member
    have listed : reduct ∈ (List.range index).map (doubledAt index) := member
    obtain ⟨place, inRange, rfl⟩ := List.mem_map.mp listed
    exact doubledAt_step index place (List.mem_range.mp inRange)
  · have distinct : ((List.range index).map (doubledAt index)).Nodup :=
      List.Nodup.map_on (fun first firstMember second secondMember same =>
        doubledAt_injective index first second (List.mem_range.mp firstMember)
          (List.mem_range.mp secondMember) same) List.nodup_range
    exact distinct

/-- **Steps beneath the root are not hosted, even without beta**: the
extended probe under the matching evaluator does not host the one rule
`c ⟶ c c` applied at every position. -/
theorem doublingContextual_not_hostedBy_matching :
    ¬ HostedBy (contextualTheory doublingTable).termsAlone matchingCandidate :=
  not_hostedBy_matching_of_unboundedBranching doublingContextual_unboundedBranching

/-- **Positive**: it hosts the instances of the same rule at the root. -/
theorem doublingInstances_hostedBy_matching :
    HostedBy (instanceTheory doublingTable).termsAlone matchingCandidate :=
  matchingCandidate_hostsEvery _
    ⟨doublingTable, doublingTable_firstOrder, doublingTable_bound, rfl⟩

/-! ## Which instances at the root are hosted -/

/-- **For a first-order table, "bound" is "its rules determine their right
sides".** -/
theorem boundTable_iff_determinedTable {table : RuleTable} (firstOrder : FirstOrderTable table) :
    BoundTable table ↔ DeterminedTable table :=
  forall_congr' fun rule => forall_congr' fun member =>
    usesOnly_patternVars_iff_rightDetermined (firstOrder rule member).1

/-- A table with a rule that does not determine its right side has a term
with infinitely many instances at the root. -/
theorem infinite_instances_of_not_rightDetermined {table : RuleTable}
    {rule : Dedukti.RewriteRule} (member : rule ∈ table) (free : ¬ RightDetermined rule) :
    ∃ term : LF.Term, {next | RuleInstance table term next}.Infinite := by
  obtain ⟨index, inRight, notLeft⟩ := exists_unbound_of_not_rightDetermined free
  exact ⟨Dedukti.inst (assignedAt index 0) rule.lhs,
    Set.infinite_of_injective_forall_mem (inst_assignedAt_injective inRight) fun value =>
      ⟨rule, member, assignedAt index value, inst_assignedAt_of_not_mentions notLeft 0 value,
        rfl⟩⟩

/-- **Exactly the tables whose rules determine their right sides.**  For a
first-order table, the extended probe under the matching evaluator hosts the
instances of its rules, on terms, exactly when the rules determine their
right sides. -/
theorem instances_hostedBy_matching_iff {table : RuleTable} (firstOrder : FirstOrderTable table) :
    HostedBy (instanceTheory table).termsAlone matchingCandidate ↔ DeterminedTable table := by
  constructor
  · intro hosted rule member
    by_contra free
    obtain ⟨term, infinite⟩ := infinite_instances_of_not_rightDetermined member free
    obtain ⟨reducts, covered⟩ := finitelyBranching_of_hostedBy
      (spacePresentation_finitelyBranching
        (matchingEvaluator_respectsStatics probeWithSpace_quoteDropOnly probeWithSpace_rewrites))
      hosted term
    refine infinite ((List.finite_toSet reducts).subset fun next step => ?_)
    obtain ⟨reduct, inReducts, same⟩ := covered next step
    exact (show next = reduct from same) ▸ inReducts
  · intro determined
    exact matchingCandidate_hostsEvery _
      ⟨table, firstOrder, (boundTable_iff_determinedTable firstOrder).mpr determined, rfl⟩

/-! ## No rank under the matching evaluator -/

/-- `c ⟶ c`. -/
def loopRule : Dedukti.RewriteRule := ⟨.con "c", .con "c"⟩

/-- **Under the matching evaluator the extended probe has no rank**: with the
rule `c ⟶ c` stored in the space, the run of `c` steps to itself.  Outside
running the rank of the probe still lowers
(`space_termStep_lowers_or_runs`). -/
theorem matchingCandidate_not_rank : IsEmpty matchingCandidate.Rank := by
  refine ⟨fun ranked => ?_⟩
  have firstOrder : FirstOrderTable {loopRule} := by
    intro rule member
    rw [Finset.mem_singleton.mp member]
    decide
  have bound : BoundTable {loopRule} := by
    intro rule member
    rw [Finset.mem_singleton.mp member]
    decide
  have step : (instanceTheory {loopRule}).rewrites (LF.Term.con "c") (LF.Term.con "c") :=
    ⟨loopRule, Finset.mem_singleton_self _, fun _ => .srt .type, by simp [loopRule],
      by simp [loopRule]⟩
  exact ranked.not_cycle (.single
    ((matchingMap {loopRule}).preservesRewrites_of_transitions
      (matchingMap_hosting firstOrder bound).preserves (interface := PUnit.unit) step))

#print axioms matchPattern_length_le_one
#print axioms matchResults_length_le
#print axioms runRules_termStep_run_iff
#print axioms matching_step_storeSize
#print axioms matching_reducts_le_storeSize
#print axioms successorTheory_not_unboundedBranching
#print axioms not_hostedBy_matching_of_unboundedBranching
#print axioms rewritingTheory_unboundedBranching
#print axioms matching_not_hostedBy_rewritingTheory
#print axioms matchingCandidate_hosts_no_tabular_terms
#print axioms matchingCandidate_not_hostOf_tabular_terms
#print axioms matchingCandidate_not_hostOf_determinedTabular_terms
#print axioms spacePresentation_not_hostOf_tabular_contexts
#print axioms not_contextualInstance_empty
#print axioms doublingContextual_unboundedBranching
#print axioms doublingContextual_not_hostedBy_matching
#print axioms doublingInstances_hostedBy_matching
#print axioms matchingCandidate_not_rank
#print axioms boundTable_iff_determinedTable
#print axioms instances_hostedBy_matching_iff

end Mettapedia.Logic.HostingStyles.PrimeCandidate

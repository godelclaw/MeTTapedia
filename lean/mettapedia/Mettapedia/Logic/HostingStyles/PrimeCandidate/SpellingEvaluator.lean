import Mettapedia.GSLT.Core.StepFree
import Mettapedia.Logic.HostingStyles.PrimeCandidate.HostSentence
import Mettapedia.Logic.HostingStyles.PrimeCandidate.RunExtension
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.DeriveCountable

/-!
# An evaluator that reads the spelling of its subject

The steps of a presented language are taken up to its static equivalence,
and the premises of its rewrites are answered by an evaluator that is given
the patterns themselves.  Nothing asks the evaluator to answer two equal
patterns alike.  This module shows what an evaluator that does not gives the
probe with the run constructor (`runPresentation`).

One name has infinitely many spellings: `prime-quote (prime-drop name)` is
equal to `name` (`spelledTerm_equiv`).  An evaluator that counts the
droppings of its subject (`spellingEvaluator`) reads a number off the
spelling, and answers with the reduct of that number in a sequence of the
reducts of the term it runs.  So, on terms,

* **the extended presentation hosts every theory with countably many terms,
  compared by identity**, under the evaluator that runs it
  (`spelledMap_hosting`, `StepEnumeration.ofCountable`); a term may have
  infinitely many reducts (`spelledFan_step`), although the evaluator answers
  every query with at most one binding;
* in particular **it hosts the rule-table evaluator, hence every theory given
  by a table** (`runPresentation_hostOf_tabular_terms`);
* neither this map nor the map of a finite listing is exhausting
  (`spelledMap_not_exhausting`, `runMap_not_exhausting`), and the extension
  that hosts keeps the two pinned defects of the probe
  (`probeWithRun_process_takes_no_process`,
  `probeWithRun_alternatives_no_constructor`).

The same presentation under the evaluator that answers nothing hosts none of
them (`silentRun_hosts_no_tabular_terms`), and with all contexts it is no
host of them under any evaluator
(`runPresentation_not_hostOf_tabular_contexts`).

The evaluator of a finite listing (`stepEvaluator`) reads its subject up to
the static equivalence (`stepAnswers_congr`); this one reads how the subject
is written.  A hosting statement on terms about a presented candidate
therefore has to fix its evaluator, and to say whether the evaluator may
tell apart what the static equivalence identifies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

open Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory tableEvaluator Tabled loadMap loadMap_hosting)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-! ## The spellings of one name -/

/-- **The quotation of a numeral, written with `depth` superfluous
quotations of droppings.** -/
def spelledName : Nat → Nat → Pattern
  | 0, count => quoted (numeral count)
  | depth + 1, count => quoted (dropped (spelledName depth count))

/-- The atom that drops such a name. -/
def spelledAtom (depth count : Nat) : Pattern := dropped (spelledName depth count)

theorem contract_spelledName (depth count : Nat) :
    contract (spelledName depth count) = quoted (numeral count) := by
  induction depth with
  | zero => exact contract_quoted_numeral count
  | succ depth ih => rw [spelledName, contract_quoted_dropped, ih]

/-- **All spellings have one contraction**: the shortest spelling. -/
theorem contract_spelledAtom (depth count : Nat) :
    contract (spelledAtom depth count) = spelledAtom 0 count := by
  rw [spelledAtom, dropped, contract_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil, contract_spelledName]
  rfl

theorem spelledAtom_injective {first second : Nat}
    (same : spelledAtom 0 first = spelledAtom 0 second) : first = second := by
  simp only [spelledAtom, spelledName, dropped, quoted, Pattern.apply.injEq, List.cons.injEq,
    and_true, true_and] at same
  exact numeral_injective same

/-! ## What tells the spellings apart -/

mutual
  /-- The number of droppings in a pattern. -/
  def drops : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments => (if label = "prime-drop" then 1 else 0) + dropsList arguments
    | .lambda _ body => drops body
    | .multiLambda _ _ body => drops body
    | .subst body replacement => drops body + drops replacement
    | .collection _ elements _ => dropsList elements

  /-- The number of droppings in a list of patterns. -/
  def dropsList : List Pattern → Nat
    | [] => 0
    | pattern :: patterns => drops pattern + dropsList patterns
end

theorem drops_numeral (count : Nat) : drops (numeral count) = 0 := by
  induction count with
  | zero => decide
  | succ count ih => simp [numeral, unitAtom, drops, dropsList, ih]

theorem drops_spelledName (depth count : Nat) : drops (spelledName depth count) = depth := by
  induction depth with
  | zero => simp [spelledName, quoted, drops, dropsList, drops_numeral]
  | succ depth ih =>
      simp only [spelledName, quoted, dropped, drops, dropsList, ih]
      simp
      omega

/-- **The number of droppings of a spelling is its depth and one.** -/
theorem drops_spelledAtom (depth count : Nat) : drops (spelledAtom depth count) = depth + 1 := by
  simp only [spelledAtom, dropped, drops, dropsList, drops_spelledName]
  simp
  omega

/-! ## The spellings are terms, and equal ones -/

/-- The quotation of an atom is a name. -/
theorem quoted_wellSorted {bound : List TypeExpr} {atom : Pattern}
    (sorted : OpenPatternWellSorted probeWithRun FreeTypeContext.empty bound (.base "Atom") atom) :
    OpenPatternWellSorted probeWithRun FreeTypeContext.empty bound (.base "CandidateName")
      (quoted atom) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := sorted
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .constructor (rule := quoteConstructor) (by decide)
      (fun bare => by
        have checked := (usesBareCollection?_eq_true_iff _).mpr bare
        revert checked
        decide)
      (.cons trivial rfl typed .nil)
  · simpa [quoted, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  · simpa [quoted, isObjectPattern, isObjectPatternList] using object
  · have here : atom.isWellScopedAt bound.length = true := scopeSafe
    show (quoted atom).isWellScopedAt bound.length = true
    simp [quoted, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here]

/-- The dropping of a name is an atom. -/
theorem dropped_wellSorted {bound : List TypeExpr} {name : Pattern}
    (sorted : OpenPatternWellSorted probeWithRun FreeTypeContext.empty bound (.base "CandidateName")
      name) :
    OpenPatternWellSorted probeWithRun FreeTypeContext.empty bound (.base "Atom")
      (dropped name) := by
  obtain ⟨typed, canonical, object, scopeSafe⟩ := sorted
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact .constructor (rule := dropConstructor) (by decide)
      (fun bare => by
        have checked := (usesBareCollection?_eq_true_iff _).mpr bare
        revert checked
        decide)
      (.cons trivial rfl typed .nil)
  · simpa [dropped, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  · simpa [dropped, isObjectPattern, isObjectPatternList] using object
  · have here : name.isWellScopedAt bound.length = true := scopeSafe
    show (dropped name).isWellScopedAt bound.length = true
    simp [dropped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, here]

theorem spelledName_wellSorted (depth count : Nat) :
    OpenPatternWellSorted probeWithRun FreeTypeContext.empty [.base "Space"]
      (.base "CandidateName") (spelledName depth count) := by
  induction depth with
  | zero =>
      exact quoted_wellSorted
        (numeral_wellSorted_in (lang := probeWithRun) (by decide) (by decide) [.base "Space"] count)
  | succ depth ih => exact quoted_wellSorted (dropped_wellSorted ih)

/-- The run of a spelling, as a term. -/
def spelledTerm (depth count : Nat) : Contexts.Term probeWithRun openProcess :=
  ⟨runPattern (.bvar 0) (spelledAtom depth count),
    runPattern_wellSorted (dropped_wellSorted (spelledName_wellSorted depth count))⟩

/-- **All spellings of one name are equal terms**, for every evaluator. -/
theorem spelledTerm_equiv (base : BasePremiseEvaluator) (depth count : Nat) :
    (termSetoid base probeWithRun openProcess).r (spelledTerm depth count) (spelledTerm 0 count) := by
  induction depth with
  | zero => exact Relation.EqvGen.refl _
  | succ depth ih =>
      exact Relation.EqvGen.trans _ (spelledTerm depth count) _
        (Relation.EqvGen.rel (spelledTerm (depth + 1) count) (spelledTerm depth count)
          (quoteDrop_contextStep base (lang := probeWithRun)
            (probeWithRun_quoteDropOnly.equations ▸ List.mem_singleton.mpr rfl)
            (.apply "prime-run" [.bvar 0] (.apply "prime-drop" [] .hole []) [])
            (spelledName depth count))) ih

theorem contract_spelledRun (count : Nat) :
    contract (runPattern (.bvar 0) (spelledAtom 0 count)) =
      runPattern (.bvar 0) (spelledAtom 0 count) := by
  rw [runPattern, contract_apply_of_ne (by decide)]
  simp only [List.map_cons, List.map_nil, contract_spelledAtom]
  rfl

/-- **The shortest spellings of different numbers are apart**, for every
evaluator. -/
theorem spelledTerm_apart (base : BasePremiseEvaluator) {first second : Nat}
    (related : (termSetoid base probeWithRun openProcess).r (spelledTerm 0 first)
      (spelledTerm 0 second)) : first = second := by
  have same := probeWithRun_quoteDropOnly.contract_eq related
  have unfolded : contract (runPattern (.bvar 0) (spelledAtom 0 first)) =
      contract (runPattern (.bvar 0) (spelledAtom 0 second)) := same
  rw [contract_spelledRun, contract_spelledRun] at unfolded
  simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
  exact spelledAtom_injective unfolded

/-! ## Enumerated theories and the evaluator that runs one -/

/-- **An enumeration of the steps of a theory given by its terms**: a number
for each term, different for different terms, and for each term a sequence
that goes through its reducts.  The terms are compared by identity. -/
structure StepEnumeration (source : GSLT.{0}) where
  /-- The number of a term. -/
  code : source.Term → Nat
  injective : Function.Injective code
  /-- The sequence of the reducts of a term. -/
  reduct : source.Term → Nat → Option source.Term
  branches : ∀ term next : source.Term,
    source.rewrites term next ↔ ∃ index, reduct term index = some next
  discrete : ∀ first second : source.Term, source.equations.r first second → first = second

/-- The answers of the evaluator for one subject: the reduct, in the sequence
of the term that the subject contracts to, at the place that the spelling of
the subject gives. -/
noncomputable def spellingAnswers {Source : Type} (code : Source → Nat)
    (reduct : Source → Nat → Option Source) (bindings : Bindings) (subject : Pattern)
    (answer : String) : List Bindings :=
  open Classical in
  if known : ∃ term, contract (applyBindings bindings subject) = spelledAtom 0 (code term) then
    (reduct (Classical.choose known) (drops (applyBindings bindings subject) - 1)).toList.map
      fun next => (answer, spelledAtom 0 (code next)) :: bindings
  else []

/-- **The evaluator of the premises that runs an enumerated theory**: it
reads the term off the contraction of its subject and the place in the
sequence off its spelling. -/
noncomputable def spellingEvaluator {Source : Type} (code : Source → Nat)
    (reduct : Source → Nat → Option Source) : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery "PrimeStep" [_, subject, .fvar answer] =>
      spellingAnswers code reduct bindings subject answer
  | _ => []

theorem spellingAnswers_eq {Source : Type} {code : Source → Nat}
    (injective : Function.Injective code) (reduct : Source → Nat → Option Source)
    {bindings : Bindings} {subject : Pattern} (answer : String) {term : Source}
    (reads : contract (applyBindings bindings subject) = spelledAtom 0 (code term)) :
    spellingAnswers code reduct bindings subject answer =
      (reduct term (drops (applyBindings bindings subject) - 1)).toList.map
        fun next => (answer, spelledAtom 0 (code next)) :: bindings := by
  have known : ∃ other, contract (applyBindings bindings subject) = spelledAtom 0 (code other) :=
    ⟨term, reads⟩
  have chosen : Classical.choose known = term :=
    injective (spelledAtom_injective ((Classical.choose_spec known).symm.trans reads))
  unfold spellingAnswers
  rw [dif_pos known, chosen]

/-- Under the evaluator of an enumerated theory the run of a term, in the
spelling of a place of its sequence, reduces to the run of the reduct at that
place. -/
theorem spelled_step {Source : Type} {code : Source → Nat} (injective : Function.Injective code)
    (reduct : Source → Nat → Option Source) {term next : Source} {depth : Nat}
    (found : reduct term depth = some next) :
    Step (spellingEvaluator code reduct) probeWithRun
      (runPattern (.bvar 0) (spelledAtom depth (code term)))
      (runPattern (.bvar 0) (spelledAtom 0 (code next))) := by
  refine ⟨1, .rule (rule := runRewrite)
    (initialBindings := [("subject", spelledAtom depth (code term)), ("space", .bvar 0)])
    (finalBindings := [("answer", spelledAtom 0 (code next)),
      ("subject", spelledAtom depth (code term)), ("space", .bvar 0)])
    (by rw [probeWithRun_rewrites]; simp) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, runRewrite, runPattern, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ spellingAnswers code reduct _ (.fvar "subject") "answer"
    rw [spellingAnswers_eq injective reduct "answer" (term := term)
      (by simp [applyBindings, contract_spelledAtom])]
    have place : drops (applyBindings
        [("subject", spelledAtom depth (code term)), ("space", .bvar 0)] (.fvar "subject")) - 1 =
        depth := by
      simp [applyBindings, drops_spelledAtom]
    rw [place, found]
    exact List.mem_map.mpr ⟨next, by simp, rfl⟩
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [runRewrite, runPattern, applyBindings]

/-! ## The hosting map -/

/-- Equal terms have equal runs. -/
theorem spelledTerm_resp {source : GSLT.{0}} (enumeration : StepEnumeration source)
    {first second : source.Term} (related : source.equations.r first second) :
    (termSetoid (spellingEvaluator enumeration.code enumeration.reduct) probeWithRun openProcess).r
      (spelledTerm 0 (enumeration.code first)) (spelledTerm 0 (enumeration.code second)) := by
  rw [enumeration.discrete _ _ related]

/-- **An enumerated theory, in the extended presentation**: a term is read as
the run of the shortest spelling of its number. -/
noncomputable def spelledMap {source : GSLT.{0}} (enumeration : StepEnumeration source) :
    ContextMap source.termsAlone
      (contextTheory (spellingEvaluator enumeration.code enumeration.reduct) runPresentation) :=
  ContextMap.ofTerms (source := source)
    (target := contextTheory (spellingEvaluator enumeration.code enumeration.reduct) runPresentation)
    openProcess (fun term => spelledTerm 0 (enumeration.code term))
    (fun related => spelledTerm_resp enumeration related)

/-- **Under the evaluator that runs it, the extended presentation hosts every
enumerated theory on terms.** -/
theorem spelledMap_hosting {source : GSLT.{0}} (enumeration : StepEnumeration source) :
    (spelledMap enumeration).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := source)
    (target := contextTheory (spellingEvaluator enumeration.code enumeration.reduct) runPresentation)
    openProcess (fun term => spelledTerm 0 (enumeration.code term))
    (fun related => spelledTerm_resp enumeration related)).mpr
    ⟨?_, ?_, ?_⟩
  · intro first second related
    rw [enumeration.injective (spelledTerm_apart _ related)]
  · intro first next step
    obtain ⟨place, found⟩ := (enumeration.branches first next).mp step
    exact ⟨spelledTerm place (enumeration.code first), spelledTerm 0 (enumeration.code next),
      Relation.EqvGen.symm _ _ (spelledTerm_equiv _ place (enumeration.code first)),
      spelled_step enumeration.injective enumeration.reduct found, Relation.EqvGen.refl _⟩
  · rintro first next ⟨redex, contractum, before, fired, after⟩
    have reads : contract redex.1 =
        runPattern (.bvar 0) (spelledAtom 0 (enumeration.code first)) := by
      have same := probeWithRun_quoteDropOnly.contract_eq before
      have unfolded : contract (runPattern (.bvar 0) (spelledAtom 0 (enumeration.code first))) =
          contract redex.1 := same
      rw [contract_spelledRun] at unfolded
      exact unfolded.symm
    obtain ⟨bindings, subject, final, subjectReads, answered, rfl, spaceReads, target⟩ :=
      run_step_inv reads redex.2.1 redex.2.2.2.1 fired
    have answers : final ∈ spellingAnswers enumeration.code enumeration.reduct bindings
        (.fvar "subject") "answer" := answered
    rw [spellingAnswers_eq enumeration.injective enumeration.reduct "answer" subjectReads]
      at answers
    obtain ⟨reduct, member, rfl⟩ := List.mem_map.mp answers
    have found : enumeration.reduct first
        (drops (applyBindings bindings (.fvar "subject")) - 1) = some reduct := by
      simpa using member
    refine ⟨reduct, (enumeration.branches first reduct).mpr ⟨_, found⟩, ?_⟩
    have image : contractum = spelledTerm 0 (enumeration.code reduct) := by
      apply Subtype.ext
      rw [target]
      have space : applyBindings (("answer", spelledAtom 0 (enumeration.code reduct)) :: bindings)
          (.fvar "space") = applyBindings bindings (.fvar "space") := by
        simp [applyBindings]
      have answer : applyBindings (("answer", spelledAtom 0 (enumeration.code reduct)) :: bindings)
          (.fvar "answer") = spelledAtom 0 (enumeration.code reduct) := by
        simp [applyBindings]
      show applyBindings _ (.apply "prime-run" [.fvar "space", .fvar "answer"]) = _
      rw [applyBindings]
      simp only [List.map_cons, List.map_nil, space, answer, spaceReads]
      rfl
    rw [← image]
    exact Relation.EqvGen.symm _ _ after

/-! ## Neither hosting map of the extension is exhausting -/

/-- **Negative**: the run of a numeral is outside the image of every
enumerated theory, so the map is not exhausting. -/
theorem spelledMap_not_exhausting {source : GSLT.{0}} (enumeration : StepEnumeration source) :
    ¬ (spelledMap enumeration).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit) (runTerm 0)
  have same := probeWithRun_quoteDropOnly.contract_eq related
  have unfolded : contract (runPattern (.bvar 0) (numeral 0)) =
      contract (runPattern (.bvar 0) (spelledAtom 0 (enumeration.code preimage))) := same
  rw [contract_runPattern, contract_spelledRun] at unfolded
  simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
  have heads : head? (numeral 0) = head? (spelledAtom 0 (enumeration.code preimage)) :=
    congrArg head? unfolded
  have left : head? (numeral 0) = some "prime-unit" := rfl
  have right : head? (spelledAtom 0 (enumeration.code preimage)) = some "prime-drop" := rfl
  rw [left, right] at heads
  exact absurd heads (by decide)

/-- **Negative**: the run of a dropping is outside the image of every listed
theory, so that map is not exhausting either. -/
theorem runMap_not_exhausting {source : GSLT.{0}} (listing : StepListing source) :
    ¬ (runMap listing).Exhausting := by
  intro exhausting
  obtain ⟨preimage, related⟩ :=
    ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit) (spelledTerm 0 0)
  have same := probeWithRun_quoteDropOnly.contract_eq related
  have unfolded : contract (runPattern (.bvar 0) (spelledAtom 0 0)) =
      contract (runPattern (.bvar 0) (numeral (listing.code preimage))) := same
  rw [contract_runPattern, contract_spelledRun] at unfolded
  simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
  have heads : head? (spelledAtom 0 0) = head? (numeral (listing.code preimage)) :=
    congrArg head? unfolded
  have left : head? (spelledAtom 0 0) = some "prime-drop" := rfl
  cases code : listing.code preimage with
  | zero =>
      rw [left, code] at heads
      exact absurd heads (by decide)
  | succ count =>
      have right : head? (numeral (count + 1)) = some "=" := rfl
      rw [left, code, right] at heads
      exact absurd heads (by decide)

/-! ## Every countable theory is enumerated -/

/-- A set of a countable type is gone through by a sequence. -/
theorem exists_sequence_of_countable {α : Type} [Countable α] (members : Set α) :
    ∃ sequence : Nat → Option α,
      ∀ element, element ∈ members ↔ ∃ index, sequence index = some element := by
  rcases members.eq_empty_or_nonempty with rfl | nonempty
  · exact ⟨fun _ => none, fun element => by simp⟩
  · obtain ⟨sequence, rfl⟩ := (Set.to_countable members).exists_eq_range nonempty
    exact ⟨fun index => some (sequence index), fun element => by simp [Set.mem_range]⟩

/-- **A theory with countably many terms, compared by identity, has an
enumeration of its steps.** -/
noncomputable def StepEnumeration.ofCountable (source : GSLT.{0}) (countable : Countable source.Term)
    (discrete : ∀ first second : source.Term, source.equations.r first second → first = second) :
    StepEnumeration source where
  code := Classical.choose (exists_injective_nat source.Term)
  injective := Classical.choose_spec (exists_injective_nat source.Term)
  reduct := fun term =>
    Classical.choose (exists_sequence_of_countable {next | source.rewrites term next})
  branches := fun term next =>
    Classical.choose_spec (exists_sequence_of_countable {next | source.rewrites term next}) next
  discrete := discrete

/-! ## The rule-table evaluator -/

/-- The characters are countably many. -/
instance charCountable : Countable Char :=
  Function.Injective.countable (f := Char.toNat) fun _ _ same => Char.toNat_inj.mp same

/-- The strings are countably many. -/
instance stringCountable : Countable String :=
  Function.Injective.countable (f := String.toList) fun _ _ same => String.toList_injective same

deriving instance Countable for LF.Srt, LF.Term, Dedukti.RewriteRule, Dedukti.Tabled

/-- An enumeration of the steps of the rule-table evaluator. -/
noncomputable def evaluatorEnumeration : StepEnumeration (tableEvaluator.gslt ()) :=
  StepEnumeration.ofCountable _ (inferInstanceAs (Countable Tabled)) fun _ _ same => same

/-- **The evaluator of the premises that runs the rule-table evaluator.** -/
noncomputable def tableRunEvaluator : BasePremiseEvaluator :=
  spellingEvaluator evaluatorEnumeration.code evaluatorEnumeration.reduct

/-- **The probe with the run constructor is a host of the theories given by a
table, on terms**, under the evaluator of its premises that runs the
rule-table evaluator. -/
theorem runPresentation_hostOf_tabular_terms :
    HostOf (contextTheory tableRunEvaluator runPresentation) TabularTheory .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, rfl⟩, interface, rfl⟩
  exact ⟨(spelledMap evaluatorEnumeration).comp ((loadMap theory table).betweenTerms interface),
    (spelledMap_hosting evaluatorEnumeration).comp
      ((loadMap_hosting tabular).betweenTerms interface)⟩

/-- **Negative**: under the evaluator that answers nothing the same
presentation is no host of them. -/
theorem silentRun_not_hostOf_tabular_terms :
    ¬ HostOf (contextTheory silentEvaluator runPresentation) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_rank silentRunRank

/-- Under that evaluator it hosts none of them. -/
theorem silentRun_hosts_no_tabular_terms {source : ContextTheory.{0}}
    (tabular : TabularTheory source) (interface : source.Interface) :
    ¬ HostedBy (source.gslt interface).termsAlone (contextTheory silentEvaluator runPresentation) :=
  not_hostedBy_tabular_terms_of_rank silentRunRank tabular interface

/-- **Negative**: with all contexts it is no host of them under any
evaluator. -/
theorem runPresentation_not_hostOf_tabular_contexts (base : BasePremiseEvaluator) :
    ¬ HostOf (contextTheory base runPresentation) TabularTheory .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_tabular
    ((runLinearSize base).isEmpty_contextMap_of_discards
      (rewritingTheory_discards Theory.empty) ⟨(.srt .type : LF.Term)⟩).false map

/-! ## The extension that hosts keeps the two pinned defects of the probe -/

/-- In the probe with the run constructor reduction is still in a separate
sort: no constructor of the sort `Process` takes a process. -/
theorem probeWithRun_process_takes_no_process :
    ∀ rule ∈ probeWithRun.terms, rule.category = "Process" →
      ∀ parameter ∈ rule.params, parameter.typeExpr ≠ .base "Process" := by
  decide

/-- And its sort `Alternatives` still has no constructor.  So neither of the
two blocks hosting on terms. -/
theorem probeWithRun_alternatives_no_constructor :
    probeWithRun.terms.all (fun term => !(term.category == "Alternatives")) = true := by
  decide

/-! ## Examples -/

/-- **Positive**: the theory in which zero reduces to every number is
enumerated, although it has no finite listing. -/
def fanEnumeration : StepEnumeration fanTheory where
  code := fun (term : Nat) => term
  injective := fun _ _ same => same
  reduct := fun (term : Nat) index => if term = 0 then some index else none
  branches := fun (term next : Nat) => by
    show term = 0 ↔ ∃ index, (if term = 0 then some index else none) = some next
    by_cases zero : term = 0
    · simp [zero]
    · simp [zero]
  discrete := fun _ _ same => same

/-- **Under the evaluator that reads the spelling one term of the extended
presentation reduces to infinitely many terms that its static equivalence
keeps apart** (`spelledTerm_apart`), although the evaluator answers every
query with at most one binding. -/
theorem spelledFan_step (index : Nat) :
    (contextTheory (spellingEvaluator fanEnumeration.code fanEnumeration.reduct)
      runPresentation).rewrites (spelledTerm 0 0) (spelledTerm 0 index) :=
  ⟨spelledTerm index 0, spelledTerm 0 index,
    Relation.EqvGen.symm _ _ (spelledTerm_equiv _ index 0),
    spelled_step (Source := Nat) fanEnumeration.injective fanEnumeration.reduct
      (term := 0) (next := index) (depth := index)
      (show (if (0 : Nat) = 0 then some index else none) = some index from if_pos rfl),
    Relation.EqvGen.refl _⟩

/-- The theory of the sets of natural numbers, with no step. -/
def continuumTheory : GSLT.{0} :=
  GSLT.stepFree (Set Nat)

/-- **Negative**: a theory with more terms than numbers has no
enumeration. -/
theorem continuumTheory_not_enumeration : IsEmpty (StepEnumeration continuumTheory) :=
  ⟨fun enumeration => Function.cantor_injective (fun term : Set Nat => enumeration.code term)
    enumeration.injective⟩

#print axioms contract_spelledAtom
#print axioms drops_spelledAtom
#print axioms spelledTerm_equiv
#print axioms spelledTerm_apart
#print axioms spelled_step
#print axioms spelledMap_hosting
#print axioms spelledMap_not_exhausting
#print axioms runMap_not_exhausting
#print axioms StepEnumeration.ofCountable
#print axioms runPresentation_hostOf_tabular_terms
#print axioms silentRun_not_hostOf_tabular_terms
#print axioms silentRun_hosts_no_tabular_terms
#print axioms runPresentation_not_hostOf_tabular_contexts
#print axioms probeWithRun_process_takes_no_process
#print axioms probeWithRun_alternatives_no_constructor
#print axioms spelledFan_step
#print axioms continuumTheory_not_enumeration

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

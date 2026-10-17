import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.MatchingProgram

/-!
# Evaluators that answer the run premise by a function

The run rewrite of the probe,

    prime-run space subject  ⟶  prime-run space answer     if PrimeStep(space, subject, answer),

hands its premise to the evaluator with the space and the subject bound.  An
evaluator may answer with any list of bindings; the evaluators met so far
answer in one way: they bind the answer variable, in front of the bindings,
to each of a list of patterns computed from the space and the subject.

* `AnswersRunBy base answers` says so of an evaluator and a function.  The
  matching evaluator does (`matchingEvaluator_answersRunBy`), and so does
  every authored evaluator (`AuthoredEvaluator.answersRunBy`).  An evaluator
  that rebinds the space does not (`clearingEvaluator_not_answersRunBy`).
* `runEvaluator answers` is the evaluator that answers the run premise by a
  function and no other premise.
* Under such an evaluator a run steps exactly to the runs of its answers, in
  the same space (`step_of_answer`, `answered_step_inv`).
* It respects the static equivalence when its answers depend on the
  contractions of the space and of the subject only
  (`runEvaluator_respectsStatics`).
* **A theory is hosted on terms through the run rewrite as soon as the
  answers at the atoms of its terms are the atoms of their reducts**
  (`hostedBy_of_runAnswers`): each term is read as a closed atom with no
  quotation to contract, different terms as different atoms, and a term is
  hosted as the run of its atom in one closed space.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

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
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_applyBindings)
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## Answering by a function -/

/-- **An evaluator answers the run premise by a function of the space and the
subject**: it binds the answer variable, in front of the bindings, to each
pattern of a list computed from the two, and changes nothing else. -/
def AnswersRunBy (base : BasePremiseEvaluator) (answers : Pattern → Pattern → List Pattern) : Prop :=
  ∀ (lang : LanguageDef) (bindings : Bindings),
    base lang bindings runPremise =
      (answers (applyBindings bindings (.fvar "space"))
        (applyBindings bindings (.fvar "subject"))).map fun result => ("answer", result) :: bindings

/-- **The evaluator that answers the run premise by a function, and no other
premise.** -/
def runEvaluator (answers : Pattern → Pattern → List Pattern) : BasePremiseEvaluator :=
  fun _ bindings premise =>
    match premise with
    | .relationQuery "PrimeStep" [.fvar "space", .fvar "subject", .fvar "answer"] =>
        (answers (applyBindings bindings (.fvar "space"))
          (applyBindings bindings (.fvar "subject"))).map fun result => ("answer", result) :: bindings
    | _ => []

theorem runEvaluator_answersRunBy (answers : Pattern → Pattern → List Pattern) :
    AnswersRunBy (runEvaluator answers) answers := fun _ _ => rfl

/-- **Positive**: the matching evaluator. -/
theorem matchingEvaluator_answersRunBy :
    AnswersRunBy matchingEvaluator fun space subject =>
      matchResults (contract space) (contract subject) := fun _ _ => rfl

/-- **Positive**: every authored evaluator, by the answers of its program to
`PrimeStep`. -/
theorem AuthoredEvaluator.answersRunBy (A : AuthoredEvaluator) :
    AnswersRunBy A.evaluator fun space subject => A.answers "PrimeStep" [space, subject] :=
  fun lang bindings => A.evaluator_runPremise lang bindings

/-- An evaluator that answers every premise by clearing the space. -/
def clearingEvaluator : BasePremiseEvaluator := fun _ bindings _ =>
  [("space", emptySpace) :: bindings]

/-- **Negative**: an evaluator that rebinds the space answers by no
function. -/
theorem clearingEvaluator_not_answersRunBy (answers : Pattern → Pattern → List Pattern) :
    ¬ AnswersRunBy clearingEvaluator answers := by
  intro byRun
  have same := byRun probeWithSpace []
  have listed : (("space", emptySpace) :: ([] : Bindings)) ∈
      (answers (applyBindings [] (.fvar "space")) (applyBindings [] (.fvar "subject"))).map
        fun result => ("answer", result) :: ([] : Bindings) := by
    rw [← same]
    exact List.mem_singleton.mpr rfl
  obtain ⟨result, -, wrong⟩ := List.mem_map.mp listed
  simp at wrong

/-! ## The steps of a run -/

/-- **A run steps to the run of each answer**, in the same space. -/
theorem step_of_answer {lang : LanguageDef} (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} {answers : Pattern → Pattern → List Pattern}
    (byRun : AnswersRunBy base answers) {space subject result : Pattern}
    (found : result ∈ answers space subject) :
    Step base lang (runPattern space subject) (runPattern space result) := by
  refine ⟨1, .rule (rule := runRewrite)
    (initialBindings := [("subject", subject), ("space", space)])
    (finalBindings := [("answer", result), ("subject", subject), ("space", space)])
    (by rw [rules, probeWithRun_rewrites]; simp) ?_ ?_ ?_⟩
  · simp [matchPatternForRule_eq_syntactic, runRewrite, runPattern, matchPattern, matchArgs,
      mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ base lang [("subject", subject), ("space", space)] runPremise
    rw [byRun]
    have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
        space := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
        subject := by simp [applyBindings]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨result, found, rfl⟩
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide)]
    simp [runRewrite, runPattern, applyBindings]

/-- **A step out of a pattern that contracts to a run is the step to the run
of an answer**, in the same space. -/
theorem answered_step_inv {lang : LanguageDef} (rules : lang.rewrites = probeWithRun.rewrites)
    {base : BasePremiseEvaluator} {answers : Pattern → Pattern → List Pattern}
    (byRun : AnswersRunBy base answers) {redex contractum : Pattern}
    (runHead : head? (contract redex) = some "prime-run")
    (step : Step base lang redex contractum) :
    ∃ space subject result, redex = runPattern space subject ∧
      result ∈ answers space subject ∧ contractum = runPattern space result := by
  obtain ⟨space, subject, final, rfl, answered, rfl⟩ := run_step_shape rules runHead step
  rw [byRun] at answered
  have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
      space := by simp [applyBindings]
  have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
      subject := by simp [applyBindings]
  rw [spaceValue, subjectValue] at answered
  obtain ⟨result, found, rfl⟩ := List.mem_map.mp answered
  exact ⟨space, subject, result, rfl, found, by simp [runRewrite, runPattern, applyBindings]⟩

/-! ## Respecting the static equivalence -/

/-- **The evaluator of a function respects the static equivalence when the
function reads the space and the subject up to it**: spaces and subjects with
the same contractions get answers with the same contractions. -/
theorem runEvaluator_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) {answers : Pattern → Pattern → List Pattern}
    (reads : ∀ space subject otherSpace otherSubject, contract space = contract otherSpace →
      contract subject = contract otherSubject →
        (answers space subject).map contract = (answers otherSpace otherSubject).map contract) :
    RespectsStatics (runEvaluator answers) lang := by
  intro premise member first second related result answered
  have contractions : BindingsRelated (fun left right => contract left = contract right) first
      second := related.mono fun _ _ equivalent => only.equationEquiv_iff.mp equivalent
  rw [presentedPremises_of_rules only rules, presentedPremises_probeWithRun] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp [runEvaluator] at answered
  · simp [runEvaluator] at answered
  · simp [runEvaluator] at answered
  · have listed : result ∈ (answers (applyBindings first (.fvar "space"))
        (applyBindings first (.fvar "subject"))).map fun value => ("answer", value) :: first :=
      answered
    obtain ⟨value, found, rfl⟩ := List.mem_map.mp listed
    have same := reads _ _ _ _
      (contract_applyBindings_congr contractions (.fvar "space") rfl)
      (contract_applyBindings_congr contractions (.fvar "subject") rfl)
    have image : contract value ∈ (answers (applyBindings second (.fvar "space"))
        (applyBindings second (.fvar "subject"))).map contract := by
      rw [← same]
      exact List.mem_map.mpr ⟨value, found, rfl⟩
    obtain ⟨other, otherFound, equal⟩ := List.mem_map.mp image
    refine ⟨("answer", other) :: second, ?_,
      .cons ⟨rfl, only.equationEquiv_iff.mpr equal.symm⟩ related⟩
    show _ ∈ (answers (applyBindings second (.fvar "space"))
      (applyBindings second (.fvar "subject"))).map fun value => ("answer", value) :: second
    exact List.mem_map.mpr ⟨other, otherFound, rfl⟩

/-- **Positive**: a function that contracts what it reads. -/
theorem runEvaluator_contracting_respectsStatics {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) (inner : Pattern → Pattern → List Pattern) :
    RespectsStatics (runEvaluator fun space subject => inner (contract space) (contract subject))
      lang :=
  runEvaluator_respectsStatics only rules fun _ _ _ _ spaces subjects => by rw [spaces, subjects]

/-- **Negative**: the function that answers with the label at the root of its
subject, as it is written. -/
theorem runEvaluator_rootLabel_not_respectsStatics :
    ¬ RespectsStatics
      (runEvaluator fun _ subject =>
        match subject with
        | .apply label _ => [.apply label []]
        | _ => [])
      probeWithSpace := by
  intro respects
  have related : BindingsRelated
      (EquationEquiv (runEvaluator fun _ subject =>
        match subject with
        | .apply label _ => [.apply label []]
        | _ => []) probeWithSpace)
      [("subject", quoted (dropped unitAtom)), ("space", emptySpace)]
      [("subject", unitAtom), ("space", emptySpace)] :=
    .cons ⟨rfl, probeWithSpace_quoteDropOnly.equationEquiv_iff.mpr (by decide)⟩
      (.cons ⟨rfl, .refl _⟩ .nil)
  obtain ⟨other, otherAnswered, otherRelated⟩ := respects runPremise
    (by rw [presentedPremises_of_rules probeWithSpace_quoteDropOnly probeWithSpace_rewrites,
      presentedPremises_probeWithRun]; simp) related
    [("answer", .apply "prime-quote" []), ("subject", quoted (dropped unitAtom)),
      ("space", emptySpace)]
    (by simp [runEvaluator, runPremise, applyBindings, quoted])
  have shape : other = [("answer", .apply "prime-unit" []), ("subject", unitAtom),
      ("space", emptySpace)] := by
    simpa [runEvaluator, runPremise, applyBindings, unitAtom] using otherAnswered
  subst shape
  cases otherRelated with
  | cons pair _ =>
      have same := probeWithSpace_quoteDropOnly.equationEquiv_iff.mp pair.2
      revert same
      decide

/-! ## Hosting through the run rewrite -/

/-- The run of an atom in a closed space is a closed process of the probe
with a space. -/
theorem runPattern_closed {space subject : Pattern}
    (spaceSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Space")
      space)
    (subjectSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom")
      subject) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Process")
      (runPattern space subject) :=
  wellSorted_apply_two (lang := probeWithSpace) (label := "prime-run") (firstName := "space")
    (secondName := "subject") (by decide) spaceSorted subjectSorted

/-- **Hosting on terms through the run rewrite.**  A theory whose terms are
compared by identity and read, different terms differently, as closed atoms
with no quotation to contract, is hosted by the probe with a space, under an
evaluator that answers the run premise by a function, as soon as in one closed
space the answers at the atom of a term are the atoms of its reducts, for
every way of writing the space and the atom. -/
theorem hostedBy_of_runAnswers {source : GSLT.{0}} {base : BasePremiseEvaluator}
    {answers : Pattern → Pattern → List Pattern} (byRun : AnswersRunBy base answers)
    {space : Pattern}
    (spaceSorted : OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Space")
      space)
    (spaceContracted : contract space = space) (read : source.Term → Pattern)
    (sorted : ∀ term, OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom")
      (read term))
    (contracted : ∀ term, contract (read term) = read term)
    (injective : Function.Injective read)
    (discrete : ∀ first second : source.Term, source.equations.r first second → first = second)
    (forth : ∀ term next : source.Term, source.rewrites term next →
      read next ∈ answers space (read term))
    (back : ∀ (written subject : Pattern) (term : source.Term) (result : Pattern),
      contract written = space → contract subject = read term →
        result ∈ answers written subject →
          ∃ next, source.rewrites term next ∧ contract result = read next) :
    HostedBy source.termsAlone (contextTheory base spacePresentation) := by
  let image : source.Term → Contexts.Term probeWithSpace closedProcess := fun term =>
    ⟨runPattern space (read term), runPattern_closed spaceSorted (sorted term)⟩
  have imageContract : ∀ term, contract (image term).1 = runPattern space (read term) := by
    intro term
    show contract (runPattern space (read term)) = _
    rw [contract_runPattern', spaceContracted, contracted]
  have resp : ∀ {first second : source.Term}, source.equations.r first second →
      (termSetoid base probeWithSpace closedProcess).r (image first) (image second) := by
    intro first second related
    rw [discrete _ _ related]
  refine ⟨ContextMap.ofTerms (source := source) (target := contextTheory base spacePresentation)
    closedProcess image resp,
    (ContextMap.ofTerms_hosting_iff (source := source)
      (target := contextTheory base spacePresentation) closedProcess image resp).mpr
      ⟨?_, ?_, ?_⟩⟩
  · intro first second related
    have same := probeWithSpace_quoteDropOnly.contract_eq related
    have unfolded : contract (image first).1 = contract (image second).1 := same
    rw [imageContract, imageContract] at unfolded
    simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at unfolded
    rw [injective unfolded]
  · intro first next step
    exact ⟨image first, image next, Relation.EqvGen.refl _,
      step_of_answer probeWithSpace_rewrites byRun (forth first next step), Relation.EqvGen.refl _⟩
  · intro first next step
    obtain ⟨redex, contractum, before, fired, after⟩ := step
    have same := probeWithSpace_quoteDropOnly.contract_eq before
    have redexClass : contract redex.1 = runPattern space (read first) := by
      have unfolded : contract (image first).1 = contract redex.1 := same
      rw [imageContract] at unfolded
      exact unfolded.symm
    obtain ⟨written, subject, result, redexShape, found, contractumShape⟩ :=
      answered_step_inv probeWithSpace_rewrites byRun (by rw [redexClass]; rfl) fired
    rw [redexShape, contract_runPattern'] at redexClass
    simp only [runPattern, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at redexClass
    obtain ⟨reduct, sourceStep, resultClass⟩ :=
      back written subject first result redexClass.1 redexClass.2 found
    refine ⟨reduct, sourceStep, ?_⟩
    refine (probeWithSpace_quoteDropOnly.termSetoid_iff probeWithSpace_quoteDropSorted).mpr ?_
    rw [← probeWithSpace_quoteDropOnly.contract_eq after]
    show contract contractum.1 = contract (image reduct).1
    rw [contractumShape, contract_runPattern', redexClass.1, resultClass, imageContract]

/-- The numeral of a number is a closed atom of the probe with a space. -/
theorem numeral_closedAtom (count : Nat) :
    OpenPatternWellSorted probeWithSpace FreeTypeContext.empty [] (.base "Atom") (numeral count) :=
  numeral_wellSorted_in (lang := probeWithSpace) (by decide) (by decide) [] count

#print axioms matchingEvaluator_answersRunBy
#print axioms clearingEvaluator_not_answersRunBy
#print axioms step_of_answer
#print axioms answered_step_inv
#print axioms runEvaluator_respectsStatics
#print axioms runEvaluator_rootLabel_not_respectsStatics
#print axioms hostedBy_of_runAnswers

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

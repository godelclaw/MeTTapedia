import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.WeakEvaluators

/-!
# Authored does not mean weak

Being the evaluator of an equation program does not bound what an evaluator
computes.  Two programs say so.

## A program that hosts what no stored rules host

`climbProgram` has twenty-three equations: those of contraction and eight of
its own.  It answers the run premise without reading the space: at a subject
it answers with the subject under one more equation, and with each of its
nested right arguments.

* Its evaluator is authored (`climbAuthored`) and respects the static
  equivalence (`climbAuthored_respectsStatics`).
* **Through one run rewrite it hosts a theory that branches without bound
  along one reduction** (`climbTheory`, `climbTheory_unboundedBranching`,
  `climbAuthored_hosts`): a number steps to its successor and to every smaller
  number.
* The matching evaluator does not host that theory
  (`authored_hosts_beyond_matching`), and no answers by stored rules do, so the
  answers of the program are not answers by stored rules
  (`climb_not_answersByStoredRules`).  It answers at the empty space
  (`climbAuthored_not_rulesFromSpace`).

## A program that does not respect the static equivalence

`labelProgram` has one equation: it answers with the label at the root of its
subject, as the subject is written.  Its evaluator is authored
(`labelAuthored`) and does not respect the static equivalence
(`labelAuthored_not_respectsStatics`): a program is handed its inputs as they
are written, and the contraction is its own to do.

## The rule-table evaluator

One step of the rule-table evaluator, with beta and with steps at every
position, has finitely many results up to the static equivalence only for
tables whose rules determine their right sides.  So no authored evaluator that
respects the static equivalence hosts the theories given by a table through
the run rewrite (`authored_not_hostOf_tabular`): this holds of every
evaluator that respects it, and being authored adds nothing.  For the empty
table the step is beta at every position, and the module `BetaProgram` writes
the program for it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## What the program computes -/

mutual
  /-- The nested right arguments of the equations of a pattern, the outermost
  first. -/
  def tails : Pattern → List Pattern
    | .apply label arguments => if label = "=" then tailsList arguments else []
    | .bvar _ => []
    | .fvar _ => []
    | .lambda _ _ => []
    | .multiLambda _ _ _ => []
    | .subst _ _ => []
    | .collection _ _ _ => []

  /-- Those of the two arguments of an equation. -/
  def tailsList : List Pattern → List Pattern
    | [_, rest] => rest :: tails rest
    | _ => []
end

/-- **The answers at a subject**: the subject under one more equation, and its
nested right arguments. -/
def climbAnswers (subject : Pattern) : List Pattern :=
  .apply "=" [unitAtom, subject] :: tails subject

/-- **Positive**: the nested right arguments of a numeral are the smaller
numerals. -/
theorem tails_numeral : ∀ count : Nat, tails (numeral count) = (List.range count).reverse.map numeral
  | 0 => by decide
  | count + 1 => by
      rw [numeral, tails, if_pos rfl, tailsList, tails_numeral count, List.range_succ,
        List.reverse_append]
      rfl

/-- **Negative**: an atom that is no equation has none. -/
theorem tails_unit : tails unitAtom = [] := by decide

theorem mem_climbAnswers_numeral {count : Nat} {result : Pattern} :
    result ∈ climbAnswers (numeral count) ↔
      ∃ other, result = numeral other ∧ (other = count + 1 ∨ other < count) := by
  rw [climbAnswers, tails_numeral]
  constructor
  · intro member
    rcases List.mem_cons.mp member with rfl | smaller
    · exact ⟨count + 1, rfl, .inl rfl⟩
    · obtain ⟨other, inRange, rfl⟩ := List.mem_map.mp smaller
      exact ⟨other, rfl, .inr (List.mem_range.mp (List.mem_reverse.mp inRange))⟩
  · rintro ⟨other, rfl, rfl | smaller⟩
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨other, List.mem_reverse.mpr (List.mem_range.mpr smaller), rfl⟩)

/-- The answers of the program to a relation and a list of inputs. -/
def climbingAnswers (relation : String) (inputs : List Pattern) : List Pattern :=
  if relation = "PrimeStep" then
    match inputs with
    | [_, subject] => climbAnswers (contract subject)
    | _ => []
  else []

/-! ## The program -/

/-- The equations of the program, after those of contraction. -/
def climbEquations : Program := [
  ⟨"premise", "premise", [slot "relation", slot "inputs"],
    call "run-premise" [same (slot "relation") (encodeName "PrimeStep"), slot "inputs"]⟩,
  ⟨"run-two", "run-premise", [yes, cell (slot "space") (cell (slot "subject") empty)],
    call "climb" [call "contract" [slot "subject"]]⟩,
  ⟨"run-other", "run-premise", [slot "t", slot "inputs"], empty⟩,
  ⟨"climb", "climb", [slot "s"],
    cell
      (call "apply" [encodeName "=",
        cell (call "apply" [encodeName "prime-unit", empty]) (cell (slot "s") empty)])
      (call "tails" [slot "s"])⟩,
  ⟨"tails-apply", "tails", [call "apply" [slot "c", slot "args"]],
    call "tails-step" [same (slot "c") (encodeName "="), slot "args"]⟩,
  ⟨"tails-other", "tails", [slot "other"], empty⟩,
  ⟨"tails-step", "tails-step", [yes, cell (slot "first") (cell (slot "rest") empty)],
    cell (slot "rest") (call "tails" [slot "rest"])⟩,
  ⟨"tails-stop", "tails-step", [slot "t", slot "args"], empty⟩]

/-- **The climbing program.** -/
def climbProgram : Program := contractEquations ++ climbEquations

theorem climbProgram_length : climbProgram.length = 23 := rfl

local notation "P" => climbProgram
local notation "H" => sharedHost

theorem climbProgram_keepsCells : KeepsCells P H := keepsCells_dataEqualityHost (by rfl)

local notation "keeps" => climbProgram_keepsCells

theorem climbEquations_apart :
    ∀ equation ∈ climbEquations, equation.head ∉ contractEquations.calledHeads := by
  decide +kernel

theorem climb_contract (pattern : Pattern) :
    Applies P H "contract" [encodePattern pattern] (encodePattern (contract pattern)) :=
  (Applies.append_iff contractEquations climbEquations sharedHost climbEquations_apart "contract"
    (by decide +kernel) _ _).mpr (contractEquations_computes pattern)

theorem tailsStep_computes (label : String) (arguments : List Pattern)
    (later : ∀ rest ∈ arguments,
      Applies P H "tails" [encodePattern rest] (encodePatterns (tails rest))) :
    Applies P H "tails-step" [boolean (decide (label = "=")), encodePatterns arguments]
      (encodePatterns (if label = "=" then tailsList arguments else [])) := by
  by_cases equation : label = "="
  · simp only [equation, decide_true, if_true, boolean]
    rcases arguments with _ | ⟨first, _ | ⟨rest, _ | ⟨third, more⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using exact later rest (by simp)
    · by_equation
      engine keeps
  · simp only [equation, decide_false, if_false, boolean]
    by_equation
    engine keeps

theorem tails_computes (pattern : Pattern) :
    Applies P H "tails" [encodePattern pattern] (encodePatterns (tails pattern)) := by
  induction pattern using Pattern.inductionOn with
  | happly label arguments ih =>
      by_equation
      engine keeps using exact tailsStep_computes label arguments ih
  | _ =>
      by_equation
      engine keeps

theorem climb_computes (subject : Pattern) :
    Applies P H "climb" [encodePattern subject] (encodePatterns (climbAnswers subject)) := by
  by_equation
  engine keeps using exact tails_computes subject

theorem climbRun_computes (relation : String) (inputs : List Pattern) :
    Applies P H "run-premise" [boolean (decide (relation = "PrimeStep")), encodePatterns inputs]
      (encodePatterns (climbingAnswers relation inputs)) := by
  by_cases step : relation = "PrimeStep"
  · subst step
    rcases inputs with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
    · by_equation
      engine keeps
    · by_equation
      engine keeps
    · by_equation
      engine keeps using first
        | exact climb_contract subject
        | exact climb_computes (contract subject)
    · by_equation
      engine keeps
  · have empty : climbingAnswers relation inputs = [] := by simp [climbingAnswers, step]
    rw [empty]
    simp only [step, decide_false, boolean]
    by_equation
    engine keeps

/-- **On every relation and every list of inputs the program returns its
answers.** -/
theorem climbPremise_computes (relation : String) (inputs : List Pattern) :
    Applies P H premiseHead (premiseArguments relation inputs)
      (encodePatterns (climbingAnswers relation inputs)) := by
  show Applies P H "premise" [encodeName relation, encodePatterns inputs] _
  by_equation
  engine keeps using exact climbRun_computes relation inputs

theorem climbProgram_total : Total climbProgram := fun relation inputs =>
  ended_of_applies (climbPremise_computes relation inputs)

/-- **The authored evaluator of the climbing program.** -/
def climbAuthored : AuthoredEvaluator := ⟨climbProgram, climbProgram_total⟩

theorem climbAuthored_answers (relation : String) (inputs : List Pattern) :
    climbAuthored.answers relation inputs = climbingAnswers relation inputs :=
  climbAuthored.answers_of_applies (climbPremise_computes relation inputs)

theorem climbAuthored_run (space subject : Pattern) :
    climbAuthored.answers "PrimeStep" [space, subject] = climbAnswers (contract subject) := by
  rw [climbAuthored_answers]
  rfl

/-! ## Its evaluator respects the static equivalence -/

/-- Answers that read their inputs up to the static equivalence are stable. -/
theorem AuthoredEvaluator.stableAt_of_reads {A : AuthoredEvaluator} {relation : String}
    (reads : ∀ first second : List Pattern, first.map contract = second.map contract →
      A.answers relation first = A.answers relation second) (arity : Nat) :
    A.StableAt relation arity := fun first second _ same result found =>
  ⟨result, reads first second same ▸ found, rfl⟩

theorem climbingAnswers_reads (relation : String) (first second : List Pattern)
    (same : first.map contract = second.map contract) :
    climbingAnswers relation first = climbingAnswers relation second := by
  unfold climbingAnswers
  by_cases step : relation = "PrimeStep"
  · rw [if_pos step, if_pos step]
    rcases first with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩ <;>
      rcases second with _ | ⟨otherSpace, _ | ⟨otherSubject, _ | ⟨fourth, more⟩⟩⟩ <;>
      simp_all
  · rw [if_neg step, if_neg step]

theorem climbAuthored_stableAt (relation : String) (arity : Nat) :
    climbAuthored.StableAt relation arity :=
  AuthoredEvaluator.stableAt_of_reads (fun first second same => by
    rw [climbAuthored_answers, climbAuthored_answers, climbingAnswers_reads relation first second same])
    arity

/-- **The evaluator of the climbing program respects the static
equivalence.** -/
theorem climbAuthored_respectsStatics : RespectsStatics climbAuthored.evaluator probeWithSpace :=
  (respectsStatics_iff_stable_probe probeWithSpace_quoteDropOnly probeWithSpace_rewrites
    climbAuthored).mpr
    ⟨climbAuthored_stableAt _ _, climbAuthored_stableAt _ _, climbAuthored_stableAt _ _,
      climbAuthored_stableAt _ _⟩

/-! ## What it hosts -/

/-- **A theory that climbs and falls**: a number steps to its successor and to
every smaller number. -/
def climbTheory : GSLT.{0} where
  Term := Nat
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := fun term next => next = term + 1 ∨ next < term
  rewrites_resp_left := fun same step => ⟨_, same ▸ step, rfl⟩
  rewrites_resp_right := fun step same => same ▸ step

/-- **It branches without bound along one reduction**: the number at each
place has as many smaller numbers. -/
theorem climbTheory_unboundedBranching : UnboundedBranching climbTheory := by
  refine ⟨fun index => (index : Nat), fun index => .inl rfl, fun index => ?_⟩
  refine ⟨List.range index, List.length_range, fun reduct member => ?_, ?_⟩
  · exact .inr (List.mem_range.mp member)
  · exact List.nodup_range

/-- **Negative**: zero has one reduct. -/
theorem climbTheory_zero {next : Nat} (step : climbTheory.rewrites (0 : Nat) next) : next = 1 := by
  rcases step with rfl | smaller
  · rfl
  · exact absurd smaller (Nat.not_lt_zero _)

/-- **Through one run rewrite the climbing program hosts the theory that
climbs and falls**, on terms: a number is read as the run of its numeral at
the empty space. -/
theorem climbAuthored_hosts :
    HostedBy climbTheory.termsAlone (contextTheory climbAuthored.evaluator spacePresentation) := by
  refine hostedBy_of_runAnswers climbAuthored.answersRunBy (emptySpace_wellSorted [])
    (by decide) (fun term : climbTheory.Term => numeral (term : Nat))
    (fun term => numeral_closedAtom _) (fun term => contract_numeral _)
    (fun _ _ same => numeral_injective same) (fun _ _ same => same) ?_ ?_
  · intro (term : Nat) (next : Nat) step
    show numeral next ∈ climbAuthored.answers "PrimeStep" [emptySpace, numeral term]
    rw [climbAuthored_run, contract_numeral]
    exact mem_climbAnswers_numeral.mpr ⟨next, rfl, step⟩
  · intro written subject (term : Nat) result _ subjects found
    have listed : result ∈ climbAuthored.answers "PrimeStep" [written, subject] := found
    rw [climbAuthored_run, subjects] at listed
    obtain ⟨other, rfl, step⟩ := mem_climbAnswers_numeral.mp listed
    exact ⟨other, step, contract_numeral other⟩

/-- **Authored does not mean weak.**  An authored evaluator that respects the
static equivalence hosts, through one run rewrite, a theory that the matching
evaluator does not host. -/
theorem authored_hosts_beyond_matching :
    ∃ A : AuthoredEvaluator, RespectsStatics A.evaluator probeWithSpace ∧
      ∃ source : GSLT.{0}, UnboundedBranching source ∧
        HostedBy source.termsAlone (contextTheory A.evaluator spacePresentation) ∧
          ¬ HostedBy source.termsAlone matchingCandidate :=
  ⟨climbAuthored, climbAuthored_respectsStatics, climbTheory, climbTheory_unboundedBranching,
    climbAuthored_hosts,
    not_hostedBy_matching_of_unboundedBranching climbTheory_unboundedBranching⟩

/-- **Negative**: the answers of the climbing program are not answers by
stored rules. -/
theorem climb_not_answersByStoredRules :
    ¬ AnswersByStoredRules fun space subject =>
      climbAuthored.answers "PrimeStep" [space, subject] := fun weak =>
  storedRules_not_hostedBy_of_unboundedBranching climbAuthored.answersRunBy weak
    climbTheory_unboundedBranching climbAuthored_hosts

/-- **Negative**: it does not take its rules from the space; it answers at the
empty space. -/
theorem climbAuthored_not_rulesFromSpace : ¬ RulesFromSpace climbAuthored.evaluator := by
  intro fromSpace
  have silent := fromSpace probeWithSpace [("subject", unitAtom), ("space", emptySpace)]
    (by
      rw [show applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "space") =
        emptySpace by simp [applyBindings]]
      decide)
  rw [climbAuthored.evaluator_runPremise] at silent
  have answers : climbAuthored.answers "PrimeStep"
      [applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "space"),
        applyBindings [("subject", unitAtom), ("space", emptySpace)] (.fvar "subject")] ≠ [] := by
    rw [climbAuthored_run]
    exact List.cons_ne_nil _ _
  exact answers (List.map_eq_nil_iff.mp silent)

/-! ## A program that does not respect the static equivalence -/

/-- The one equation of the program: the label at the root of the subject. -/
def labelProgram : Program := [
  ⟨"premise", "premise",
    [slot "relation", cell (slot "space") (cell (call "apply" [slot "c", slot "args"]) empty)],
    cell (call "apply" [slot "c", empty]) empty⟩]

theorem labelProgram_keepsCells : KeepsCells labelProgram sharedHost :=
  keepsCells_dataEqualityHost (by rfl)

theorem labelPremise_computes (relation : String) (space : Pattern) (label : String)
    (arguments : List Pattern) :
    Applies labelProgram sharedHost premiseHead
      (premiseArguments relation [space, .apply label arguments])
      (encodePatterns [.apply label []]) := by
  show Applies labelProgram sharedHost "premise"
    [encodeName relation, encodePatterns [space, .apply label arguments]] _
  by_equation
  engine labelProgram_keepsCells

theorem labelProgram_total : Total labelProgram := by
  intro relation inputs
  have failed : ∀ arguments : List Term,
      labelProgram.select "premise" arguments = none → arguments.length = 2 →
        apply labelProgram sharedHost 0 "premise" arguments ≠ .exhausted := by
    intro arguments unmatched arity
    have defined : labelProgram.definesAt "premise" arguments.length = true := by
      rw [arity]
      rfl
    simp [apply, applyWith, defined, unmatched]
  rcases inputs with _ | ⟨space, _ | ⟨subject, _ | ⟨third, rest⟩⟩⟩
  · exact ⟨0, failed _ rfl rfl⟩
  · exact ⟨0, failed _ rfl rfl⟩
  · cases subject with
    | apply label arguments => exact ended_of_applies (labelPremise_computes relation space label arguments)
    | _ => exact ⟨0, failed _ rfl rfl⟩
  · cases subject <;> exact ⟨0, failed _ rfl rfl⟩

/-- **The authored evaluator of the label program.** -/
def labelAuthored : AuthoredEvaluator := ⟨labelProgram, labelProgram_total⟩

theorem labelAuthored_answers (relation : String) (space : Pattern) (label : String)
    (arguments : List Pattern) :
    labelAuthored.answers relation [space, .apply label arguments] = [.apply label []] :=
  labelAuthored.answers_of_applies (labelPremise_computes relation space label arguments)

/-- **Authored does not mean that the static equivalence is respected.**  The
label program answers a quoted dropping and what was dropped differently. -/
theorem labelAuthored_not_respectsStatics :
    ¬ RespectsStatics labelAuthored.evaluator probeWithSpace := by
  intro respects
  have stable := ((respectsStatics_iff_stable_probe probeWithSpace_quoteDropOnly
    probeWithSpace_rewrites labelAuthored).mp respects).2.2.2
  obtain ⟨other, found, same⟩ := stable [emptySpace, quoted (dropped unitAtom)]
    [emptySpace, unitAtom] rfl (by decide) (.apply "prime-quote" [])
    (by
      show _ ∈ labelAuthored.answers "PrimeStep" [emptySpace, .apply "prime-quote" [dropped unitAtom]]
      rw [labelAuthored_answers]
      exact List.mem_singleton.mpr rfl)
  have listed : other ∈ labelAuthored.answers "PrimeStep" [emptySpace, .apply "prime-unit" []] :=
    found
  rw [labelAuthored_answers] at listed
  rw [List.mem_singleton.mp listed] at same
  revert same
  decide

/-! ## The rule-table evaluator -/

/-- **No authored evaluator that respects the static equivalence makes the
probe with the run constructor a host of the theories given by a table.**
The statement holds of every evaluator that respects the static equivalence;
being authored adds nothing to it. -/
theorem authored_not_hostOf_tabular (A : AuthoredEvaluator)
    (respects : RespectsStatics A.evaluator probeWithRun) :
    ¬ HostOf (contextTheory A.evaluator runPresentation) TabularTheory .terms .hosting :=
  not_hostOf_tabular_terms_of_respectsStatics respects

/-! ## The evaluators of the two programs run -/

#guard (climbAuthored.evaluator probeWithSpace
    [("subject", quoted (dropped (numeral 2))), ("space", emptySpace)] runPremise).map
      (fun bindings => applyBindings bindings (.fvar "answer")) ==
  [numeral 3, numeral 1, numeral 0]

#guard (labelAuthored.evaluator probeWithSpace
    [("subject", quoted (dropped unitAtom)), ("space", emptySpace)] runPremise).map
      (fun bindings => applyBindings bindings (.fvar "answer")) ==
  [.apply "prime-quote" []]

#guard (labelAuthored.evaluator probeWithSpace
    [("subject", .bvar 0), ("space", emptySpace)] runPremise).isEmpty

#print axioms tails_numeral
#print axioms tails_computes
#print axioms climbPremise_computes
#print axioms climbAuthored
#print axioms climbAuthored_respectsStatics
#print axioms climbTheory_unboundedBranching
#print axioms climbAuthored_hosts
#print axioms authored_hosts_beyond_matching
#print axioms climb_not_answersByStoredRules
#print axioms climbAuthored_not_rulesFromSpace
#print axioms labelAuthored
#print axioms labelAuthored_not_respectsStatics
#print axioms authored_not_hostOf_tabular

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

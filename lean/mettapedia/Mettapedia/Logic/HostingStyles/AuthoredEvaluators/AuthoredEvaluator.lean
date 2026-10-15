import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.PatternData
import Mettapedia.Logic.HostingStyles.PrimeCandidate.CandidateSentence

/-!
# Authored evaluators

The premises of the rewrites of a presented language are answered by an
evaluator, a function that the presentation does not show.  An *authored*
evaluator is given by an equation program, run by the shared engine on the
shared host: everything about it is the program.

## The call that a premise makes

The reading of a premise is fixed, for every program.

* A premise `relation(inputs…, answer)`, whose last argument is a variable, is
  a query: its inputs are instantiated by the bindings, and the engine calls
  the head `premise` on the name of the relation and the list of the inputs,
  both as data (`premiseArguments`).
* The value of the call is read as a list of patterns
  (`AuthoredEvaluator.answers`); each of them is bound to the answer variable,
  in front of the bindings (`AuthoredEvaluator.evaluator`).  A value that is
  no list of patterns, and a failure, are no answer.
* Every other premise gets no answer.

## The definition

`AuthoredEvaluator` is a program that halts on every query (`Total`).  Its
evaluator runs the engine with the least fuel that ends the call
(`AuthoredEvaluator.fuel`), so it is a function that the compiler accepts
without `noncomputable`: **an authored evaluator is a computable function of
its program**.  A value that the call returns with any fuel is the value that
the evaluator reads (`AuthoredEvaluator.answers_of_applies`).

`IsAuthored base` says that an evaluator is the evaluator of some program.

* **Positive**: the evaluator that answers nothing is the evaluator of the
  empty program (`silentAuthored_evaluator`).
* **Negative**: the program that calls itself is no authored evaluator
  (`loopingProgram_not_total`).

## Respecting the static equivalence

For a language whose static equivalence is that of quotation and dropping
and whose premises are queries on distinct variables, an authored evaluator
respects the static equivalence **exactly when the answers of its program are
stable**: inputs with one contraction get answers with one contraction
(`AuthoredEvaluator.StableAt`, `respectsStatics_iff_stable`).  Being authored
does not give it: a program is handed its inputs as they are written.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Logic.HostingStyles.PrimeCandidate

/-! ## The call that a premise makes -/

/-- **The host of the shared engine.** -/
abbrev sharedHost : Host := dataEqualityHost

/-- The head that the engine calls for a premise. -/
def premiseHead : String := "premise"

/-- The arguments of the call for a relation and its instantiated inputs. -/
def premiseArguments (relation : String) (inputs : List Pattern) : List Term :=
  [encodeName relation, encodePatterns inputs]

/-- **The inputs of a query and the variable that receives its answers**: the
arguments but the last, and the last when it is a variable. -/
def queryShape : List Pattern → Option (List Pattern × String)
  | [] => none
  | last :: [] =>
    match last with
    | .fvar answer => some ([], answer)
    | _ => none
  | input :: next :: rest =>
    (queryShape (next :: rest)).map fun shape => (input :: shape.1, shape.2)

theorem queryShape_append (answer : String) :
    ∀ inputs : List Pattern, queryShape (inputs ++ [.fvar answer]) = some (inputs, answer)
  | [] => rfl
  | [input] => rfl
  | input :: next :: rest => by
      have later := queryShape_append answer (next :: rest)
      simp only [List.cons_append] at later ⊢
      rw [queryShape, later]
      rfl

theorem eq_append_of_queryShape :
    ∀ {arguments inputs : List Pattern} {answer : String},
      queryShape arguments = some (inputs, answer) → arguments = inputs ++ [.fvar answer]
  | [], _, _, found => by cases found
  | [last], inputs, answer, found => by
      cases last <;> simp [queryShape] at found
      obtain ⟨rfl, rfl⟩ := found
      rfl
  | input :: next :: rest, inputs, answer, found => by
      rw [queryShape] at found
      cases later : queryShape (next :: rest) with
      | none => simp [later] at found
      | some shape =>
          obtain ⟨tail, name⟩ := shape
          simp only [later, Option.map_some, Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          rw [eq_append_of_queryShape later]
          rfl

/-- **Positive**: the run premise is a query with two inputs. -/
theorem queryShape_runPremise :
    queryShape [.fvar "space", .fvar "subject", .fvar "answer"] =
      some ([.fvar "space", .fvar "subject"], "answer") := rfl

/-- **Negative**: arguments that end with an application are no query. -/
theorem queryShape_apply (label : String) (arguments : List Pattern) (input : Pattern) :
    queryShape [input, .apply label arguments] = none := rfl

/-! ## Programs that halt on every query -/

instance decidableEnded (result : Outcome) : Decidable (result ≠ .exhausted) :=
  match result with
  | .exhausted => isFalse fun ended => ended rfl
  | .value _ => isTrue fun wrong => by cases wrong
  | .failure => isTrue fun wrong => by cases wrong

/-- **A program halts on every query**: for each relation and each list of
inputs some fuel ends the call. -/
def Total (program : Program) : Prop :=
  ∀ (relation : String) (inputs : List Pattern),
    ∃ fuel, apply program sharedHost fuel premiseHead (premiseArguments relation inputs) ≠ .exhausted

/-- A call that returns a value ends. -/
theorem ended_of_applies {program : Program} {head : String} {arguments : List Term}
    {result : Term} (computed : Applies program sharedHost head arguments result) :
    ∃ fuel, apply program sharedHost fuel head arguments ≠ .exhausted := by
  obtain ⟨fuel, returned⟩ := computed
  exact ⟨fuel, by rw [returned]; intro wrong; cases wrong⟩

/-- **An authored evaluator**: an equation program that halts on every
query. -/
structure AuthoredEvaluator where
  /-- The program. -/
  program : Program
  total : Total program

namespace AuthoredEvaluator

variable (A : AuthoredEvaluator)

/-- The least fuel that ends the call of a query. -/
def fuel (relation : String) (inputs : List Pattern) : Nat :=
  Nat.find (A.total relation inputs)

/-- The outcome of the call of a query. -/
def run (relation : String) (inputs : List Pattern) : Outcome :=
  apply A.program sharedHost (A.fuel relation inputs) premiseHead (premiseArguments relation inputs)

theorem run_ended (relation : String) (inputs : List Pattern) :
    A.run relation inputs ≠ .exhausted :=
  Nat.find_spec (A.total relation inputs)

/-- **An outcome that the call has with any fuel is its outcome.** -/
theorem run_eq_of_apply {relation : String} {inputs : List Pattern} {fuel : Nat}
    {result : Outcome}
    (computed :
      apply A.program sharedHost fuel premiseHead (premiseArguments relation inputs) = result)
    (ended : result ≠ .exhausted) : A.run relation inputs = result := by
  have first := apply_le (P := A.program) (H := sharedHost) (f := premiseHead)
    (vs := premiseArguments relation inputs) (Nat.le_max_left fuel (A.fuel relation inputs))
    (by rw [computed]; exact ended)
  have second := apply_le (P := A.program) (H := sharedHost) (f := premiseHead)
    (vs := premiseArguments relation inputs) (Nat.le_max_right fuel (A.fuel relation inputs))
    (A.run_ended relation inputs)
  exact (second.symm.trans first).trans computed

/-- **The answers of the program to a query**: the patterns of the list that
the call returns. -/
def answers (relation : String) (inputs : List Pattern) : List Pattern :=
  match A.run relation inputs with
  | .value result => (decodePatterns result).getD []
  | _ => []

/-- **A list of patterns that the call returns with some fuel is the list of
the answers.** -/
theorem answers_of_applies {relation : String} {inputs results : List Pattern}
    (computed : Applies A.program sharedHost premiseHead (premiseArguments relation inputs)
      (encodePatterns results)) : A.answers relation inputs = results := by
  obtain ⟨fuel, returned⟩ := computed
  have ran := A.run_eq_of_apply returned (fun wrong => by cases wrong)
  simp [answers, ran, decodePatterns_encodePatterns]

/-- A call that fails gives no answer. -/
theorem answers_of_failure {relation : String} {inputs : List Pattern} {fuel : Nat}
    (failed :
      apply A.program sharedHost fuel premiseHead (premiseArguments relation inputs) = .failure) :
    A.answers relation inputs = [] := by
  have ran := A.run_eq_of_apply failed (fun wrong => by cases wrong)
  simp [answers, ran]

/-- A value that is no list of patterns gives no answer. -/
theorem answers_of_value {relation : String} {inputs : List Pattern} {result : Term}
    (computed : Applies A.program sharedHost premiseHead (premiseArguments relation inputs) result)
    (other : decodePatterns result = none) : A.answers relation inputs = [] := by
  obtain ⟨fuel, returned⟩ := computed
  have ran := A.run_eq_of_apply returned (fun wrong => by cases wrong)
  simp [answers, ran, other]

/-- **The evaluator of an authored evaluator.**  It is a function of the
program: no `noncomputable`, and no choice. -/
def evaluator : BasePremiseEvaluator := fun _ bindings premise =>
  match premise with
  | .relationQuery relation arguments =>
    match queryShape arguments with
    | some (inputs, answer) =>
        (A.answers relation (inputs.map (applyBindings bindings))).map fun result =>
          (answer, result) :: bindings
    | none => []
  | _ => []

theorem evaluator_query (lang : LanguageDef) (bindings : Bindings) (relation : String)
    (inputs : List Pattern) (answer : String) :
    A.evaluator lang bindings (.relationQuery relation (inputs ++ [.fvar answer])) =
      (A.answers relation (inputs.map (applyBindings bindings))).map fun result =>
        (answer, result) :: bindings := by
  simp only [evaluator, queryShape_append]

theorem evaluator_runPremise (lang : LanguageDef) (bindings : Bindings) :
    A.evaluator lang bindings runPremise =
      (A.answers "PrimeStep"
        [applyBindings bindings (.fvar "space"), applyBindings bindings (.fvar "subject")]).map
          fun result => ("answer", result) :: bindings := rfl

/-- What an authored evaluator answers to a premise, in one formula. -/
theorem evaluator_apply (lang : LanguageDef) (bindings : Bindings) (premise : Premise) :
    A.evaluator lang bindings premise =
      match premise with
      | .relationQuery relation arguments =>
        match queryShape arguments with
        | some (inputs, answer) =>
            (A.answers relation (inputs.map (applyBindings bindings))).map fun result =>
              (answer, result) :: bindings
        | none => []
      | _ => [] := rfl

end AuthoredEvaluator

/-- **An evaluator is authored**: it is the evaluator of an equation
program. -/
def IsAuthored (base : BasePremiseEvaluator) : Prop :=
  ∃ A : AuthoredEvaluator, A.evaluator = base

/-! ## The empty program, and a program that does not halt -/

/-- The empty program halts on every query: `premise` is then a constructor. -/
theorem empty_total : Total [] := fun _ _ => ⟨0, fun wrong => by cases wrong⟩

/-- **The authored evaluator of the empty program.** -/
def silentAuthored : AuthoredEvaluator := ⟨[], empty_total⟩

theorem silentAuthored_answers (relation : String) (inputs : List Pattern) :
    silentAuthored.answers relation inputs = [] :=
  silentAuthored.answers_of_value (result := .expr (.sym premiseHead :: premiseArguments relation inputs))
    ⟨0, rfl⟩ (decodePatterns_call _ _ _ (by decide))

/-- **Positive**: the evaluator that answers nothing is the evaluator of the
empty program. -/
theorem silentAuthored_evaluator : silentAuthored.evaluator = silentEvaluator := by
  funext lang bindings premise
  rw [AuthoredEvaluator.evaluator_apply]
  cases premise with
  | relationQuery relation arguments =>
      show (match queryShape arguments with
        | some (inputs, answer) =>
            (silentAuthored.answers relation (inputs.map (applyBindings bindings))).map
              fun result => (answer, result) :: bindings
        | none => []) = []
      cases queryShape arguments with
      | none => rfl
      | some shape => simp [silentAuthored_answers]
  | _ => rfl

theorem silentEvaluator_isAuthored : IsAuthored silentEvaluator :=
  ⟨silentAuthored, silentAuthored_evaluator⟩

/-- The program whose one equation calls itself. -/
def loopingProgram : Program :=
  [⟨"premise", "premise", [.var "relation", .var "inputs"],
    .expr [.sym "premise", .var "relation", .var "inputs"]⟩]

theorem loopingProgram_exhausts (first second : Term) :
    ∀ fuel, apply loopingProgram sharedHost fuel "premise" [first, second] = .exhausted
  | 0 => rfl
  | fuel + 1 => by
      have previous := loopingProgram_exhausts first second fuel
      have unfolded : apply loopingProgram sharedHost (fuel + 1) "premise" [first, second] =
          eval loopingProgram sharedHost (fuel + 1) [("relation", first), ("inputs", second)]
            (.expr [.sym "premise", .var "relation", .var "inputs"]) := rfl
      rw [unfolded, eval, evalStep_head (by simp [Special])]
      cases fuel with
      | zero => rfl
      | succ fuel =>
          have items : evalItemsWith (eval loopingProgram sharedHost (fuel + 1))
              [("relation", first), ("inputs", second)] [.var "relation", .var "inputs"] =
              .values [first, second] := rfl
          rw [items]
          exact previous

/-- **Negative**: the program that calls itself halts on no query, so it is
the program of no authored evaluator. -/
theorem loopingProgram_not_total : ¬ Total loopingProgram := fun total => by
  obtain ⟨fuel, ended⟩ := total "PrimeStep" []
  exact ended (loopingProgram_exhausts _ _ fuel)

/-! ## Respecting the static equivalence -/

namespace AuthoredEvaluator

/-- **The answers of a program to a relation are stable**: lists of inputs of
a given length with the same contractions get answers with the same
contractions. -/
def StableAt (A : AuthoredEvaluator) (relation : String) (arity : Nat) : Prop :=
  ∀ first second : List Pattern, first.length = arity →
    first.map contract = second.map contract →
      ∀ result ∈ A.answers relation first,
        ∃ other ∈ A.answers relation second, contract result = contract other

end AuthoredEvaluator

/-- Bindings of distinct variables give each variable its value. -/
theorem applyBindings_zip :
    ∀ (names : List String) (values : List Pattern), names.Nodup → names.length = values.length →
      (names.map Pattern.fvar).map (applyBindings (names.zip values)) = values
  | [], [], _, _ => rfl
  | [], _ :: _, _, lengths => by cases lengths
  | _ :: _, [], _, lengths => by cases lengths
  | name :: names, value :: values, distinct, lengths => by
      obtain ⟨fresh, rest⟩ := List.nodup_cons.mp distinct
      have later := applyBindings_zip names values rest (Nat.succ.inj lengths)
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
      refine ⟨by rw [applyBindings_fvar_cons]; simp, ?_⟩
      have same : (names.map Pattern.fvar).map (applyBindings ((name, value) :: names.zip values)) =
          (names.map Pattern.fvar).map (applyBindings (names.zip values)) := by
        apply List.map_congr_left
        intro pattern member
        obtain ⟨other, inNames, rfl⟩ := List.mem_map.mp member
        rw [applyBindings_fvar_cons, if_neg (fun equal : name = other => fresh (equal ▸ inNames))]
      rw [same, later]

theorem bindingsRelated_zip {relation : Pattern → Pattern → Prop} :
    ∀ (names : List String) {first second : List Pattern},
      List.Forall₂ relation first second → BindingsRelated relation (names.zip first)
        (names.zip second)
  | [], _, _, _ => by
      simp only [List.zip_nil_left]
      exact .nil
  | _ :: _, _, _, .nil => .nil
  | name :: names, _, _, .cons head tail => .cons ⟨rfl, head⟩ (bindingsRelated_zip names tail)

theorem forall₂_of_map_eq {α β : Type} (image : α → β) :
    ∀ {first second : List α}, first.map image = second.map image →
      List.Forall₂ (fun left right => image left = image right) first second
  | [], [], _ => .nil
  | [], _ :: _, same => by cases same
  | _ :: _, [], same => by cases same
  | _ :: _, _ :: _, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      exact .cons same.1 (forall₂_of_map_eq image same.2)

/-- Bindings that are related give related instances to a list of variables. -/
theorem map_contract_applyBindings {first second : Bindings}
    (related : BindingsRelated (fun left right => contract left = contract right) first second)
    (names : List String) :
    ((names.map Pattern.fvar).map (applyBindings first)).map contract =
      ((names.map Pattern.fvar).map (applyBindings second)).map contract := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro name _
  exact BindingsRelated.lookup (relation := fun left right => contract left = contract right)
    (fun _ => rfl) related name

/-- **What it takes for an authored evaluator to respect the static
equivalence.**  In a language whose static equivalence is that of quotation
and dropping and whose premises are queries on distinct variables, an authored
evaluator respects the static equivalence exactly when the answers of its
program to each of these queries are stable. -/
theorem respectsStatics_iff_stable {lang : LanguageDef} (only : QuoteDropOnly lang)
    (A : AuthoredEvaluator)
    (queries : ∀ premise ∈ presentedPremises lang, ∃ (relation : String) (names : List String)
      (answer : String),
      premise = .relationQuery relation (names.map Pattern.fvar ++ [.fvar answer]) ∧ names.Nodup) :
    RespectsStatics A.evaluator lang ↔
      ∀ premise ∈ presentedPremises lang, ∀ (relation : String) (names : List String)
        (answer : String),
        premise = .relationQuery relation (names.map Pattern.fvar ++ [.fvar answer]) →
          names.Nodup → A.StableAt relation names.length := by
  constructor
  · intro respects premise member relation names answer shape distinct first second arity same
      result found
    have lengths : names.length = first.length := arity.symm
    have others : names.length = second.length := by
      rw [lengths, ← List.length_map (f := contract), same, List.length_map]
    have related : BindingsRelated (EquationEquiv A.evaluator lang) (names.zip first)
        (names.zip second) :=
      bindingsRelated_zip names
        ((forall₂_of_map_eq contract same).imp fun _ _ equal => only.equationEquiv_iff.mpr equal)
    have answered : ((answer, result) :: names.zip first) ∈
        A.evaluator lang (names.zip first) premise := by
      rw [shape, A.evaluator_query, applyBindings_zip names first distinct lengths]
      exact List.mem_map.mpr ⟨result, found, rfl⟩
    obtain ⟨other, otherAnswered, otherRelated⟩ := respects premise member related _ answered
    rw [shape, A.evaluator_query, applyBindings_zip names second distinct others] at otherAnswered
    obtain ⟨answerValue, otherFound, rfl⟩ := List.mem_map.mp otherAnswered
    cases otherRelated with
    | cons pair _ => exact ⟨answerValue, otherFound, only.equationEquiv_iff.mp pair.2⟩
  · intro stable premise member first second related result answered
    obtain ⟨relation, names, answer, shape, distinct⟩ := queries premise member
    have contractions : BindingsRelated (fun left right => contract left = contract right) first
        second := related.mono fun _ _ equivalent => only.equationEquiv_iff.mp equivalent
    rw [shape, A.evaluator_query] at answered
    obtain ⟨value, found, rfl⟩ := List.mem_map.mp answered
    obtain ⟨other, otherFound, same⟩ := stable premise member relation names answer shape distinct
      ((names.map Pattern.fvar).map (applyBindings first))
      ((names.map Pattern.fvar).map (applyBindings second)) (by simp)
      (map_contract_applyBindings contractions names) value found
    refine ⟨(answer, other) :: second, ?_, .cons ⟨rfl, only.equationEquiv_iff.mpr same⟩ related⟩
    rw [shape, A.evaluator_query]
    exact List.mem_map.mpr ⟨other, otherFound, rfl⟩

/-- The premises of a language with the rewrites of the probe with the run
constructor are queries on distinct variables. -/
theorem probeWithRun_premises_queries {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) :
    ∀ premise ∈ presentedPremises lang, ∃ (relation : String) (names : List String)
      (answer : String),
      premise = .relationQuery relation (names.map Pattern.fvar ++ [.fvar answer]) ∧ names.Nodup := by
  intro premise member
  rw [presentedPremises_of_rules only rules, presentedPremises_probeWithRun] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨"ZeroQuery", ["space", "pattern", "template"], "answer", rfl, by decide⟩
  · exact ⟨"ZeroEvaluate", ["space", "subject"], "answer", rfl, by decide⟩
  · exact ⟨"CandidateNeed", ["space", "subject", "answer"], "receipt", rfl, by decide⟩
  · exact ⟨"PrimeStep", ["space", "subject"], "answer", rfl, by decide⟩

/-- **For the probe with a run constructor and its extensions**: an authored
evaluator respects the static equivalence exactly when its answers to the
four relations of the premises are stable. -/
theorem respectsStatics_iff_stable_probe {lang : LanguageDef} (only : QuoteDropOnly lang)
    (rules : lang.rewrites = probeWithRun.rewrites) (A : AuthoredEvaluator) :
    RespectsStatics A.evaluator lang ↔
      A.StableAt "ZeroQuery" 3 ∧ A.StableAt "ZeroEvaluate" 2 ∧ A.StableAt "CandidateNeed" 3 ∧
        A.StableAt "PrimeStep" 2 := by
  rw [respectsStatics_iff_stable only A (probeWithRun_premises_queries only rules),
    presentedPremises_of_rules only rules, presentedPremises_probeWithRun]
  constructor
  · intro stable
    exact ⟨stable _ (by simp) "ZeroQuery" ["space", "pattern", "template"] "answer" rfl (by decide),
      stable _ (by simp) "ZeroEvaluate" ["space", "subject"] "answer" rfl (by decide),
      stable _ (by simp) "CandidateNeed" ["space", "subject", "answer"] "receipt" rfl (by decide),
      stable _ (by simp [runPremise]) "PrimeStep" ["space", "subject"] "answer" rfl (by decide)⟩
  · rintro ⟨query, evaluation, need, run⟩ premise member relation names answer shape distinct
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    have arguments : ∀ {other : String} {inputs : List String} {output : String},
        Premise.relationQuery other (inputs.map Pattern.fvar ++ [.fvar output]) =
          .relationQuery relation (names.map Pattern.fvar ++ [.fvar answer]) →
            other = relation ∧ inputs.length = names.length := by
      intro other inputs output same
      simp only [Premise.relationQuery.injEq] at same
      refine ⟨same.1, ?_⟩
      have lengths := congrArg List.length same.2
      simpa using lengths
    rcases member with rfl | rfl | rfl | rfl
    · obtain ⟨rfl, lengths⟩ := arguments (other := "ZeroQuery")
        (inputs := ["space", "pattern", "template"]) (output := "answer") shape
      exact lengths ▸ query
    · obtain ⟨rfl, lengths⟩ := arguments (other := "ZeroEvaluate")
        (inputs := ["space", "subject"]) (output := "answer") shape
      exact lengths ▸ evaluation
    · obtain ⟨rfl, lengths⟩ := arguments (other := "CandidateNeed")
        (inputs := ["space", "subject", "answer"]) (output := "receipt") shape
      exact lengths ▸ need
    · obtain ⟨rfl, lengths⟩ := arguments (other := "PrimeStep")
        (inputs := ["space", "subject"]) (output := "answer") shape
      exact lengths ▸ run

/-- **Positive**: the answers of the empty program are stable, and its
evaluator respects every static equivalence. -/
theorem silentAuthored_stableAt (relation : String) (arity : Nat) :
    silentAuthored.StableAt relation arity := by
  intro first second _ _ result found
  rw [silentAuthored_answers] at found
  cases found

theorem silentAuthored_respectsStatics (lang : LanguageDef) :
    RespectsStatics silentAuthored.evaluator lang := by
  rw [silentAuthored_evaluator]
  exact silentEvaluator_respectsStatics lang

#print axioms queryShape_append
#print axioms AuthoredEvaluator.run_eq_of_apply
#print axioms AuthoredEvaluator.answers_of_applies
#print axioms AuthoredEvaluator.evaluator
#print axioms silentAuthored
#print axioms silentAuthored_evaluator
#print axioms loopingProgram_not_total
#print axioms applyBindings_zip
#print axioms respectsStatics_iff_stable
#print axioms respectsStatics_iff_stable_probe
#print axioms silentAuthored_respectsStatics

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators

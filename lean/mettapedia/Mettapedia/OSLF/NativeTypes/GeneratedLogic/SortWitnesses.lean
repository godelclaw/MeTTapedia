import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Witnesses of a sort, searched

The sort quantifiers range over every object of a sort: `someOf s φ` holds when some object of sort `s` has `φ`, and
`everyOf s φ` when every one does. The front door's strategies explore a term's region, which says nothing about other
objects. A sort's closed terms can be enumerated from the grammar, though, and each asked with the front door itself:

- **a witness proves `someOf`** and **a counterexample refutes `everyOf`** (`sortDecider`): a closed object pattern
  the well-sortedness checker types at the sort, at which `ask` proves, respectively refutes, the body;
- the enumeration (`termsOfSort`, constructors whose parameters are sorts, to a depth) is only a supply of candidates:
  every candidate is checked, so it needs no completeness, and the decider answers nothing it has not witnessed;
- deciders combine, the first answer winning (`Decider.orElse`).
- **Predecessors by witnesses** (`predecessorDecider`): a candidate at which the front door proves a step to a term
  equivalent to `t` is a predecessor of `t` (`step_of_equivalent_target`), so a candidate predecessor with `φ` proves
  `⧫φ` at `t`, and one without refutes `⊟φ`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern FreeTypeContext)
open Mettapedia.OSLF.Framework.FiniteModels (Signature)

variable {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}

/-- **Deciders combined**: the first one's answer, or else the second's. -/
def Decider.orElse (first second : Decider relEnv language reading) : Decider relEnv language reading where
  decide formula term := (first.decide formula term).orElse fun _ => second.decide formula term
  exact {formula term answer} decided := by
    cases found : first.decide formula term with
    | some value =>
      simp only [found, Option.orElse_some] at decided
      cases decided
      exact first.exact found
    | none =>
      simp only [found, Option.orElse_none] at decided
      exact second.exact decided

/-- All choices of one element from each list. -/
def choices : List (List Pattern) → List (List Pattern)
  | [] => [[]]
  | options :: rest => options.flatMap fun option => (choices rest).map (option :: ·)

/-- The sorts of a constructor's parameters, when all are plain sorts. -/
def paramSorts (rule : GrammarRule) : Option (List String) :=
  rule.params.mapM fun param =>
    match param with
    | .simple _ (.base sort) => some sort
    | _ => none

variable (language) in
/-- **Closed terms of a sort**, to a depth: each constructor of the sort whose parameters are sorts, applied to terms of
those sorts one level less deep. -/
def termsOfSort : ℕ → String → List Pattern
  | 0, _ => []
  | depth + 1, sort =>
    (language.terms.filter (·.category == sort)).flatMap fun rule =>
      match paramSorts rule with
      | some sorts => (choices (sorts.map (termsOfSort depth))).map (.apply rule.label)
      | none => []

/-- A candidate is a closed object the checker types at the sort. -/
def typedCandidate (language : LanguageDef) (sort : String) (candidate : Pattern) : Bool :=
  isObjectPattern candidate && checkCarrierTyped language (.base sort) candidate

theorem typed_of_candidate {sort : String} {candidate : Pattern} (checked : typedCandidate language sort candidate = true) :
    (referenceStructure relEnv language reading).typed candidate (.base sort) := by
  simp only [typedCandidate, Bool.and_eq_true] at checked
  exact ⟨checked.1, candidate, Relation.EqvGen.refl _,
    checkCarrierTyped_eq_true_iff.mp checked.2⟩

variable (relEnv language) in
/-- **The sort decider**: a witness proves `someOf`, a counterexample refutes `everyOf`. Candidates are the sort's
closed terms to a depth, at most `limit` of them, each checked and asked with the front door, with forms compatible
with the reading. -/
def sortDecider (signature : Signature) (fuel : ℕ) (forms : Option (CanonicalForms relEnv language fuel))
    (compatible : FormsFor forms reading) (depth limit rounds : ℕ) : Decider relEnv language reading where
  decide formula _ :=
    match formula with
    | .someOf (.base sort) inner =>
      if ((termsOfSort language depth sort).take limit).any fun candidate => typedCandidate language sort candidate &&
          (match ask relEnv signature language fuel inner candidate none rounds forms with
            | .proved _ => true
            | _ => false) then some true else none
    | .everyOf (.base sort) inner =>
      if ((termsOfSort language depth sort).take limit).any fun candidate => typedCandidate language sort candidate &&
          (match ask relEnv signature language fuel inner candidate none rounds forms with
            | .refuted _ => true
            | _ => false) then some false else none
    | _ => none
  exact {formula term answer} decided := by
    split at decided
    · rename_i sort inner
      split at decided
      · rename_i witnessed
        cases decided
        obtain ⟨candidate, -, found⟩ := List.any_eq_true.mp witnessed
        simp only [Bool.and_eq_true] at found
        obtain ⟨typed, asked⟩ := found
        split at asked
        · rename_i evidence proved
          exact iff_of_true ⟨candidate, typed_of_candidate typed, ask_proved_in compatible proved⟩ rfl
        · cases asked
      · cases decided
    · rename_i sort inner
      split at decided
      · rename_i countered
        cases decided
        obtain ⟨candidate, -, found⟩ := List.any_eq_true.mp countered
        simp only [Bool.and_eq_true] at found
        obtain ⟨typed, asked⟩ := found
        split at asked
        · rename_i evidence refuted
          exact iff_of_false (fun every => ask_refuted_in compatible refuted (every candidate (typed_of_candidate typed)))
            Bool.false_ne_true
        · cases asked
      · cases decided
    · cases decided

/-! ## Predecessors by witnesses -/

/-- **A step to a term equivalent to a state is a step to the state.** -/
theorem step_of_equivalent_target {source next target : Pattern} {label : StepLabel}
    (step : (referenceStructure relEnv language reading).step source label next)
    (equivalent : ObjectEquivalent relEnv language reading next target) (targetState : IsState target) :
    (referenceStructure relEnv language reading).step source label target := by
  obtain ⟨sourceState, -, redex, contractum, witness, toRedex, redexState, valid, contractumState, toNext, admits⟩ := step
  exact ⟨sourceState, targetState, redex, contractum, witness, toRedex, redexState, valid, contractumState,
    Relation.EqvGen.trans _ _ _ toNext equivalent, admits⟩

/-- Whether a pattern is a state: closed and an object. -/
def isState (term : Pattern) : Bool := term.isWellScopedAt 0 && isObjectPattern term

theorem isState_iff {term : Pattern} : isState term = true → IsState term := by
  intro checked
  simp only [isState, Bool.and_eq_true] at checked
  exact ⟨checked.1, checked.2⟩

variable (language) in
/-- Candidates of every sort, to a depth, at most `limit` of them. -/
def candidatesOf (depth limit : ℕ) : List Pattern :=
  (language.types.flatMap fun type => termsOfSort language depth type.name).take limit

variable (relEnv language) in
/-- **The predecessor decider**: a candidate the front door shows steps to the term, and has the body, proves `⧫φ`; one
that steps to the term and lacks the body refutes `⊟φ`. -/
def predecessorDecider (signature : Signature) (fuel : ℕ) (forms : Option (CanonicalForms relEnv language fuel))
    (compatible : FormsFor forms reading) (depth limit rounds : ℕ) : Decider relEnv language reading where
  decide formula term :=
    match formula with
    | .sometimeBefore label inner =>
      if isState term && (candidatesOf language depth limit).any fun candidate =>
          (match ask relEnv signature language fuel (.possibly label (.is term)) candidate none rounds forms with
            | .proved _ => true
            | _ => false) &&
          (match ask relEnv signature language fuel inner candidate none rounds forms with
            | .proved _ => true
            | _ => false) then some true else none
    | .alwaysBefore label inner =>
      if isState term && (candidatesOf language depth limit).any fun candidate =>
          (match ask relEnv signature language fuel (.possibly label (.is term)) candidate none rounds forms with
            | .proved _ => true
            | _ => false) &&
          (match ask relEnv signature language fuel inner candidate none rounds forms with
            | .refuted _ => true
            | _ => false) then some false else none
    | _ => none
  exact {formula term answer} decided := by
    split at decided
    · rename_i label inner
      split at decided
      · rename_i witnessed
        cases decided
        simp only [Bool.and_eq_true, List.any_eq_true] at witnessed
        obtain ⟨stateChecked, candidate, -, steps, holds⟩ := witnessed
        split at steps
        · rename_i stepEvidence stepProved
          split at holds
          · rename_i evidence proved
            obtain ⟨next, step, -, equivalent⟩ := ask_proved_in compatible stepProved
            exact iff_of_true ⟨candidate, step_of_equivalent_target step equivalent (isState_iff stateChecked),
              ask_proved_in compatible proved⟩ rfl
          · cases holds
        · cases steps
      · cases decided
    · rename_i label inner
      split at decided
      · rename_i countered
        cases decided
        simp only [Bool.and_eq_true, List.any_eq_true] at countered
        obtain ⟨stateChecked, candidate, -, steps, fails⟩ := countered
        split at steps
        · rename_i stepEvidence stepProved
          split at fails
          · rename_i evidence refuted
            obtain ⟨next, step, -, equivalent⟩ := ask_proved_in compatible stepProved
            exact iff_of_false (fun every => ask_refuted_in compatible refuted
              (every candidate (step_of_equivalent_target step equivalent (isState_iff stateChecked))))
              Bool.false_ne_true
          · cases fails
        · cases steps
      · cases decided
    · cases decided

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Selection by structure: one search, two policies

A call answers from every equation whose head unifies with its arguments, in
order; a `case` answers from the first arm whose pattern unifies with its key.
Both select from an ordered list of candidate patterns, and they differ only
in their policy (`selectAll`, `selectFirst`).

A structural refutation decides, without binding anything, that no
substitution makes a pattern and a value equal: a literal against a different
closed leaf, an expression against a value of another kind or length
(`refutes`).  It is sound for unification (`refutes_sound`), and so is its
first test alone, at the pattern's root (`refutesRoot_sound`).  It is not
complete: a repeated variable survives it and may still fail to unify
(`repeated_variable_survives`).

Any sound refutation may skip candidates under either policy without changing
the answers, their order or their multiplicity (`selectAll_filter`,
`selectFirst_filter`).  A candidate whose later candidates are all refuted is
the last one: nothing after it contributes (`selectAll_last`,
`selectFirst_last`), so an implementation keeps no choice for them, and under
the first-match policy a failed attempt of that candidate fails the selection.
Sound refutations are closed under disjunction (`Sound.or`): a root test, an
index over literal positions and a full structural probe compose into one.
A structural refutation is sound for every attempt that succeeds only on
unifiable candidates (`refutes_sound_selection`).

The two policies differ exactly in commitment: the first-match policy commits
at the first successful attempt even when that candidate answers nothing
(`first_commits`, against `all_continues`).

CeTTa's open-equation machine applies these laws to equation heads, typed-call
signatures and `superpose` alternatives (every match) and to case arms (the
first match).  Relating its unifier, its cells and its list representations to
`subst` remains a realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PatternSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

/-! ## Structural refutation -/

/-- Some substitution makes the two atoms equal. -/
def Unifiable (pattern value : Atom) : Prop :=
  ∃ σ : Subst, subst σ pattern = subst σ value

mutual

/-- No substitution makes `pattern` and `value` equal, decided by their
structure alone.  A variable on either side refutes nothing. -/
def refutes : Atom → Atom → Bool
  | .var _, _ => false
  | _, .var _ => false
  | .symbol a, .symbol b => decide (a ≠ b)
  | .grounded g, .grounded h => decide (g ≠ h)
  | .expression patterns, .expression values => refutesList patterns values
  | _, _ => true

/-- Element-wise refutation; lists of different lengths refute each other. -/
def refutesList : List Atom → List Atom → Bool
  | [], [] => false
  | pattern :: patterns, value :: values =>
      refutes pattern value || refutesList patterns values
  | _, _ => true

end

mutual

theorem refutes_sound (σ : Subst) :
    ∀ (pattern value : Atom), refutes pattern value = true →
      subst σ pattern ≠ subst σ value
  | .var _, _, refuted => by simp [refutes] at refuted
  | .symbol _, .var _, refuted => by simp [refutes] at refuted
  | .grounded _, .var _, refuted => by simp [refutes] at refuted
  | .expression _, .var _, refuted => by simp [refutes] at refuted
  | .symbol a, .symbol b, refuted => by
      simp only [refutes, decide_eq_true_eq] at refuted
      simp [subst, refuted]
  | .grounded g, .grounded k, refuted => by
      simp only [refutes, decide_eq_true_eq] at refuted
      simp [subst, refuted]
  | .symbol _, .grounded _, _ => by simp [subst]
  | .symbol _, .expression _, _ => by simp [subst]
  | .grounded _, .symbol _, _ => by simp [subst]
  | .grounded _, .expression _, _ => by simp [subst]
  | .expression _, .symbol _, _ => by simp [subst]
  | .expression _, .grounded _, _ => by simp [subst]
  | .expression patterns, .expression values, refuted => by
      simp only [refutes] at refuted
      intro equal
      simp only [subst, Atom.expression.injEq] at equal
      exact refutesList_sound σ patterns values refuted equal

theorem refutesList_sound (σ : Subst) :
    ∀ (patterns values : List Atom), refutesList patterns values = true →
      subst.substList σ patterns ≠ subst.substList σ values
  | [], [], refuted => by simp [refutesList] at refuted
  | [], _ :: _, _ => by simp [subst.substList]
  | _ :: _, [], _ => by simp [subst.substList]
  | pattern :: patterns, value :: values, refuted => by
      simp only [refutesList, Bool.or_eq_true] at refuted
      intro equal
      simp only [subst.substList, List.cons.injEq] at equal
      rcases refuted with first | rest
      · exact refutes_sound σ pattern value first equal.1
      · exact refutesList_sound σ patterns values rest equal.2

end

/-- A refuted pattern does not unify with the value. -/
theorem not_unifiable_of_refutes {pattern value : Atom}
    (refuted : refutes pattern value = true) : ¬ Unifiable pattern value := by
  rintro ⟨σ, equal⟩
  exact refutes_sound σ pattern value refuted equal

theorem refutesList_of_length_ne :
    ∀ (patterns values : List Atom), patterns.length ≠ values.length →
      refutesList patterns values = true
  | [], [], different => absurd rfl different
  | [], _ :: _, _ => by simp [refutesList]
  | _ :: _, [], _ => by simp [refutesList]
  | _ :: patterns, _ :: values, different => by
      have rest : patterns.length ≠ values.length := by
        simpa using different
      simp [refutesList, refutesList_of_length_ne patterns values rest]

/-- The first test of a pattern, at its root, as an implementation tests a
call's heads and a case's arms before trying them: a literal against the
value, an expression against the value's kind and length. -/
def refutesRoot (pattern value : Atom) : Bool :=
  match pattern, value with
  | .expression patterns, .expression values =>
      decide (patterns.length ≠ values.length)
  | _, _ => refutes pattern value

theorem refutes_of_refutesRoot {pattern value : Atom}
    (refuted : refutesRoot pattern value = true) : refutes pattern value = true := by
  cases pattern <;> cases value <;>
    first
    | exact refuted
    | (simp only [refutesRoot, decide_eq_true_eq] at refuted
       simp only [refutes]
       exact refutesList_of_length_ne _ _ refuted)

/-- The root test alone is sound for unification. -/
theorem refutesRoot_sound (σ : Subst) {pattern value : Atom}
    (refuted : refutesRoot pattern value = true) : subst σ pattern ≠ subst σ value :=
  refutes_sound σ pattern value (refutes_of_refutesRoot refuted)

/-! ### Controls -/

/-- A cons pattern refutes the empty list at its root. -/
example : refutesRoot (.expression [.symbol "LCons", .var "h", .var "t"]) (.symbol "LNil") =
    true := rfl

/-- Two expressions of different lengths refute each other at the root. -/
example : refutesRoot (.expression [.symbol "Some", .var "x"])
    (.expression [.symbol "Pair", .symbol "a", .symbol "b"]) = true := by
  simp [refutesRoot]

/-- A variable refutes nothing, on either side. -/
example : refutes (.var "x") (.symbol "LNil") = false := rfl
example : refutes (.symbol "LNil") (.var "x") = false := rfl

/-- Different literals refute each other; equal ones do not. -/
example : refutes (.symbol "LNil") (.symbol "None") = true := by simp [refutes]
example : refutes (.symbol "LNil") (.symbol "LNil") = false := by simp [refutes]

/-- A difference below the root is refuted by the full test, not by the root
test: the root test leaves the candidate to its attempt. -/
example : refutes (.expression [.symbol "Machine", .symbol "Running"])
    (.expression [.symbol "Machine", .symbol "Done"]) = true := by
  simp [refutes, refutesList]
example : refutesRoot (.expression [.symbol "Machine", .symbol "Running"])
    (.expression [.symbol "Machine", .symbol "Done"]) = false := by
  simp [refutesRoot]

/-- The refutation is not complete: a repeated variable survives it, yet no
substitution unifies the two. -/
theorem repeated_variable_survives :
    refutes (.expression [.symbol "f", .var "x", .var "x"])
        (.expression [.symbol "f", .symbol "a", .symbol "b"]) = false ∧
      ¬ Unifiable (.expression [.symbol "f", .var "x", .var "x"])
        (.expression [.symbol "f", .symbol "a", .symbol "b"]) := by
  constructor
  · simp [refutes, refutesList]
  · rintro ⟨σ, equal⟩
    simp only [subst, subst.substList, Atom.expression.injEq, List.cons.injEq] at equal
    obtain ⟨-, first, second, -⟩ := equal
    rw [first] at second
    simp at second

/-! ## Two policies over one selection -/

section Policies

variable {Candidate Match Answer : Type*}

/-- The answers a candidate contributes when its attempt is made. -/
def answersOf (attempt : Candidate → Option Match)
    (body : Candidate → Match → List Answer) (candidate : Candidate) : List Answer :=
  match attempt candidate with
  | some found => body candidate found
  | none => []

/-- Every candidate's answers, in candidate order: a call over its equations. -/
def selectAll (attempt : Candidate → Option Match)
    (body : Candidate → Match → List Answer) (candidates : List Candidate) :
    List Answer :=
  candidates.flatMap (answersOf attempt body)

/-- The answers of the first candidate whose attempt succeeds: a `case` over
its arms.  The selection commits there, whatever that candidate answers. -/
def selectFirst (attempt : Candidate → Option Match)
    (body : Candidate → Match → List Answer) : List Candidate → List Answer
  | [] => []
  | candidate :: rest =>
      match attempt candidate with
      | some found => body candidate found
      | none => selectFirst attempt body rest

/-- A refutation is sound when it refutes only candidates whose attempt fails. -/
def Sound (attempt : Candidate → Option Match) (refuted : Candidate → Bool) : Prop :=
  ∀ candidate, refuted candidate = true → attempt candidate = none

theorem Sound.or {attempt : Candidate → Option Match} {first second : Candidate → Bool}
    (soundFirst : Sound attempt first) (soundSecond : Sound attempt second) :
    Sound attempt (fun candidate => first candidate || second candidate) := by
  intro candidate refuted
  rcases Bool.or_eq_true _ _ ▸ refuted with inFirst | inSecond
  · exact soundFirst candidate inFirst
  · exact soundSecond candidate inSecond

theorem answersOf_of_none {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {candidate : Candidate}
    (failed : attempt candidate = none) : answersOf attempt body candidate = [] := by
  simp [answersOf, failed]

/-- Skipping soundly refuted candidates leaves every-match selection unchanged,
in order and multiplicity. -/
theorem selectAll_filter {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) (candidates : List Candidate) :
    selectAll attempt body (candidates.filter (fun candidate => !refuted candidate)) =
      selectAll attempt body candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      by_cases skipped : refuted candidate = true
      · rw [List.filter_cons_of_neg (by simp [skipped]), ih]
        simp [selectAll, answersOf_of_none (body := body) (sound candidate skipped)]
      · rw [List.filter_cons_of_pos (by simpa using skipped)]
        simp only [selectAll, List.flatMap_cons] at ih ⊢
        rw [ih]

/-- Skipping soundly refuted candidates leaves first-match selection
unchanged. -/
theorem selectFirst_filter {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) (candidates : List Candidate) :
    selectFirst attempt body (candidates.filter (fun candidate => !refuted candidate)) =
      selectFirst attempt body candidates := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      by_cases skipped : refuted candidate = true
      · rw [List.filter_cons_of_neg (by simp [skipped]), ih]
        simp [selectFirst, sound candidate skipped]
      · rw [List.filter_cons_of_pos (by simpa using skipped)]
        simp only [selectFirst]
        cases attempt candidate with
        | some found => rfl
        | none => exact ih

theorem selectAll_refuted {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) :
    ∀ candidates : List Candidate, (∀ other ∈ candidates, refuted other = true) →
      selectAll attempt body candidates = []
  | [], _ => rfl
  | candidate :: rest, all => by
      simp only [selectAll, List.flatMap_cons]
      rw [answersOf_of_none (sound candidate (all candidate (by simp)))]
      exact selectAll_refuted sound rest (fun other member => all other (by simp [member]))

theorem selectFirst_refuted {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) :
    ∀ candidates : List Candidate, (∀ other ∈ candidates, refuted other = true) →
      selectFirst attempt body candidates = []
  | [], _ => rfl
  | candidate :: rest, all => by
      simp only [selectFirst, sound candidate (all candidate (by simp))]
      exact selectFirst_refuted sound rest (fun other member => all other (by simp [member]))

/-- A candidate whose later candidates are all refuted is the last one under
every-match selection: its own answers are the selection's. -/
theorem selectAll_last {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) {candidate : Candidate} {rest : List Candidate}
    (later : ∀ other ∈ rest, refuted other = true) :
    selectAll attempt body (candidate :: rest) = answersOf attempt body candidate := by
  have none : selectAll attempt body rest = [] := selectAll_refuted sound rest later
  simp only [selectAll, List.flatMap_cons] at none ⊢
  rw [none, List.append_nil]

/-- A candidate whose later candidates are all refuted is the last one under
first-match selection: when its attempt fails, the selection fails. -/
theorem selectFirst_last {attempt : Candidate → Option Match}
    {body : Candidate → Match → List Answer} {refuted : Candidate → Bool}
    (sound : Sound attempt refuted) {candidate : Candidate} {rest : List Candidate}
    (later : ∀ other ∈ rest, refuted other = true) :
    selectFirst attempt body (candidate :: rest) = answersOf attempt body candidate := by
  simp only [selectFirst, answersOf]
  cases attempt candidate with
  | some found => rfl
  | none => exact selectFirst_refuted sound rest later

end Policies

/-- A structural refutation is sound for any attempt that succeeds only on
candidates whose pattern unifies with the value. -/
theorem refutes_sound_selection {Candidate Match : Type*}
    (attempt : Candidate → Option Match) (pattern : Candidate → Atom) (value : Atom)
    (unifies : ∀ candidate found, attempt candidate = some found →
      Unifiable (pattern candidate) value) :
    Sound attempt (fun candidate => refutes (pattern candidate) value) := by
  intro candidate refuted
  cases attempted : attempt candidate with
  | none => rfl
  | some found =>
      exact absurd (unifies candidate found attempted) (not_unifiable_of_refutes refuted)

/-- So is the root test alone. -/
theorem refutesRoot_sound_selection {Candidate Match : Type*}
    (attempt : Candidate → Option Match) (pattern : Candidate → Atom) (value : Atom)
    (unifies : ∀ candidate found, attempt candidate = some found →
      Unifiable (pattern candidate) value) :
    Sound attempt (fun candidate => refutesRoot (pattern candidate) value) := by
  intro candidate refuted
  exact refutes_sound_selection attempt pattern value unifies candidate
    (refutes_of_refutesRoot refuted)

/-! ### The policies differ in commitment -/

/-- A first arm that matches but answers nothing leaves the case without
answers. -/
theorem first_commits :
    selectFirst (fun n : Nat => some n) (fun n _ => if n = 0 then [] else [n]) [0, 1] =
      [] := by
  simp [selectFirst]

/-- Every-match selection goes on to the second candidate's answer. -/
theorem all_continues :
    selectAll (fun n : Nat => some n) (fun n _ => if n = 0 then [] else [n]) [0, 1] =
      [1] := by
  simp [selectAll, answersOf]

end Mettapedia.Languages.MeTTa.PatternSelection

import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Demand
import Mathlib.Data.Nat.Find

/-!
# The HE call calculus with a choice of return rule

A core of Hyperon Experimental's `metta` evaluation, written once and
parameterized by how a call returns its value.

## Programs

A program is a list of equations `(= lhs rhs)` in stored order, together with
declarations giving a head symbol a mode for each parameter and for its
result. A `value` parameter (type `%Undefined%` or any type other than `Atom`)
is evaluated before the call; an `atom` parameter (type `Atom`) is passed as
written. An `evaluate` result (type other than `Atom`) is evaluated again on
return; an `atom` result is returned as it is. Undeclared heads take value
parameters and evaluated results, as untyped HE code does.

## Evaluation (applicative order)

* A symbol, variable or grounded atom is its own single result.
* An expression whose root is marked returns itself once, under the rules
  that read the mark (`rustEqualToInput`, `evaluatedValues`).
* Any other expression evaluates the elements in value positions (the head is
  always in a value position), takes every combination of their results, and
  calls the resulting expression:
  * `collapse`, `superpose`, `unique`, `let` and `car-atom` are primitive (see
    below);
  * otherwise the equations are queried in order. No match returns the call
    itself. A reply `NotReducible` returns the call itself. Any other reply is
    the right-hand side instantiated (inserted values keep their bits, written
    code is unmarked) and, in `evaluate` result mode, it is evaluated again.
* Marking. Every rule marks an answer that is, up to marks, the term that
  was evaluated. `evaluatedValues` also marks a call that is stuck after its
  arguments were evaluated (no equation applies, or one replies
  `NotReducible`). Every other answer keeps the marks it already has, so
  syntax returned through an `Atom` result, a `collapse` tuple and a
  `car-atom` child are code where they are used next.

The three rules differ only in which answers are marked (`marksStuck`) and
whether the mark is read (`honorsMark`): `reevaluate` does not read it;
`rustEqualToInput` reads it and marks only answers equal to the evaluated
term, so a stuck call whose arguments were reduced stays code;
`evaluatedValues` reads it and also marks stuck calls.

## Primitives (HE standard library, on this fragment)

* `(collapse e)`: the parameter is `Atom`; the result is one tuple of all results
  of `e`, returned without further evaluation.
* `(superpose (e₁ … eₙ))`: the parameter is `Expression`, so the tuple is not
  evaluated; each element is returned through an evaluating return.
* `(unique e)`: collapse, drop later duplicates up to erasure, superpose.
* `(let p v body)`: `v` is evaluated; each result is matched against `p`, and
  `body` with the match substituted is evaluated. A failed match gives no
  result.
* `(car-atom (e₁ e₂ …))`: the parameter is `Expression` and the result is
  `Atom`; the first element is returned as it is.

## Fragment boundaries

Faithful on: ground calls, equations whose left-hand sides are symbol-headed
patterns, declared heads used at their declared arity, no `Empty`/`Error`
values, `NotReducible` only as an equation reply. Matching is one-way; a
runtime variable is matched only by a pattern variable, where HE would
unify. Equation variables are not renamed apart, which matters only for terms
with free variables. Type checks other than the parameter and result modes are
not modelled.

## Fuel

`evalFuel rule P n` is the evaluator with recursion depth `n`; `none` means the
depth was insufficient, never "no results". `eval rule P` is its limit, a
fixed point of one step (`eval_fix`); `eval_eq_some_iff` says exactly when it
answers.
-/

namespace Mettapedia.Languages.MeTTa.HE.EvaluatedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- How a call returns its value. The rules differ only in which answers are
marked and whether the mark is read. -/
inductive ReturnRule where
  /-- Every returned expression is evaluated again: the mark is not read (the
  rule HE's Lean specification had). -/
  | reevaluate
  /-- The mark is read; an evaluation marks the answers that are, up to marks,
  the term it evaluated (Rust Hyperon Experimental). -/
  | rustEqualToInput
  /-- The mark is read; an evaluation also marks a call that is stuck after its
  arguments were evaluated (no equation applies, or one replies
  `NotReducible`): the value is the call over its arguments' values. -/
  | evaluatedValues
  deriving DecidableEq, Repr

/-- Whether the rule reads the evaluated mark. -/
def ReturnRule.honorsMark : ReturnRule → Bool
  | .reevaluate => false
  | .rustEqualToInput => true
  | .evaluatedValues => true

/-- Whether the rule marks a call that is stuck after argument evaluation. -/
def ReturnRule.marksStuck : ReturnRule → Bool
  | .evaluatedValues => true
  | _ => false

/-- Parameter modes. -/
inductive ParamMode where
  /-- The argument is evaluated before the call. -/
  | value
  /-- The argument is passed as written (parameter type `Atom`). -/
  | atom
  deriving DecidableEq, Repr

/-- Result modes. -/
inductive ResultMode where
  /-- The returned atom is evaluated again. -/
  | evaluate
  /-- The returned atom is returned as it is (result type `Atom`). -/
  | atom
  deriving DecidableEq, Repr

/-- A type declaration `(: head (-> T₁ … Tₙ R))`, read as modes. -/
structure Decl where
  head : String
  params : List ParamMode
  result : ResultMode
  deriving Repr

/-- Equations `(= lhs rhs)` in stored order, and type declarations. -/
structure Program where
  equations : List (Atom × Atom)
  decls : List Decl := []

/-- Primitive operations of the fragment. -/
inductive Prim where
  | collapse
  | superpose
  | unique
  | let_
  | carAtom
  deriving DecidableEq, Repr

/-- The primitive named by a head symbol. -/
def Prim.ofName : String → Option Prim
  | "collapse" => some .collapse
  | "superpose" => some .superpose
  | "unique" => some .unique
  | "let" => some .let_
  | "car-atom" => some .carAtom
  | _ => none

/-- Parameter modes of the primitives. -/
def Prim.params : Prim → List ParamMode
  | .collapse => [.atom]
  | .superpose => [.atom]
  | .unique => [.atom]
  | .let_ => [.atom, .value, .atom]
  | .carAtom => [.atom]

/-- Pair children with modes; missing modes are `value`. -/
def withModes : List ParamMode → List MAtom → List (ParamMode × MAtom)
  | _, [] => []
  | [], c :: cs => (.value, c) :: withModes [] cs
  | m :: ms, c :: cs => (m, c) :: withModes ms cs

/-- One element in its mode: evaluate it, or keep it as written. -/
def argDemand : ParamMode × MAtom → Demand (List MAtom)
  | (.value, c) => .need c .done
  | (.atom, c) => .done [c]

/-- The reply to an equation instance, returned through the call boundary. -/
def returnDemand (mode : ResultMode) (call r : MAtom) : Demand (List MAtom) :=
  if r.erase = Atom.notReducible then .done [call]
  else
    match mode with
    | .evaluate => .need r .done
    | .atom => .done [r]

/-- The primitives, on their evaluated elements; `fallback` otherwise. -/
def primDemand (p : Prim) (args : List MAtom) (fallback : Demand (List MAtom)) :
    Demand (List MAtom) :=
  match p, args with
  | .collapse, [a] => .need a fun r => .done [.expr false r]
  | .superpose, [.expr _ es] => Demand.forEach es fun e => .need e .done
  | .unique, [a] => .need a fun r => Demand.forEach (dedupErase r) fun e => .need e .done
  | .let_, [pat, val, body] =>
    match matchAtom pat.erase val [] with
    | some σ => .need (body.subst σ) .done
    | none => .done []
  | .carAtom, [a] =>
    match a with
    | .expr _ (h :: _) => .done [h]
    | _ => fallback
  | _, _ => fallback

namespace Program

/-- The declaration of a head symbol. -/
def decl? (P : Program) (f : String) : Option Decl := P.decls.find? fun d => d.head == f

/-- Parameter modes of a head. -/
def paramModes (P : Program) : MAtom → List ParamMode
  | .symbol f =>
    match Prim.ofName f with
    | some p => p.params
    | none =>
      match P.decl? f with
      | some d => d.params
      | none => []
  | _ => []

/-- Result mode of a head. -/
def resultMode (P : Program) : MAtom → ResultMode
  | .symbol f =>
    match P.decl? f with
    | some d => d.result
    | none => .evaluate
  | _ => .evaluate

/-- Modes of all elements of an expression; the head is a value position. -/
def elementModes (P : Program) : List MAtom → List ParamMode
  | [] => []
  | h :: _ => .value :: P.paramModes h

/-- Result mode of a call. -/
def callResultMode (P : Program) : List MAtom → ResultMode
  | [] => .evaluate
  | h :: _ => P.resultMode h

/-- Evaluate the elements of an expression in their modes. -/
def argsDemand (P : Program) (cs : List MAtom) : Demand (List (List MAtom)) :=
  Demand.traverse (withModes (P.elementModes cs) cs) argDemand

/-- Instantiated right-hand sides of the equations matching a call, in stored
order. -/
def replies (P : Program) (call : MAtom) : List MAtom :=
  P.equations.filterMap fun eq => (matchAtom eq.1 call []).map fun σ => (code eq.2).subst σ

/-- Query the equations for a call on evaluated elements. A stuck call (no
equation applies, or one replies `NotReducible`) is returned as itself, with
its root mark set to `ms`. -/
def queryDemand (P : Program) (ms : Bool) (vs : List MAtom) : Demand (List MAtom) :=
  match P.replies (.expr false vs) with
  | [] => .done [.expr ms vs]
  | r :: rs => Demand.forEach (r :: rs) (returnDemand (P.callResultMode vs) (.expr ms vs))

/-- A call on evaluated elements. -/
def callDemand (P : Program) (ms : Bool) (vs : List MAtom) : Demand (List MAtom) :=
  match vs with
  | .symbol f :: args =>
    match Prim.ofName f with
    | some p => primDemand p args (P.queryDemand ms vs)
    | none => P.queryDemand ms vs
  | _ => P.queryDemand ms vs

end Program

/-- Whether `rule` returns `t` as itself without evaluating it: `t` is an
expression with a marked root and the rule reads the mark. -/
def ReturnRule.keeps (rule : ReturnRule) : MAtom → Bool
  | .expr m _ => rule.honorsMark && m
  | _ => false

/-- Evaluation of a term when its mark is not read: an expression evaluates
its value positions, calls every combination, and marks the results that are
the term itself up to marks. -/
def openStep (rule : ReturnRule) (P : Program) : MAtom → Demand (List MAtom)
  | .expr m cs => ((P.argsDemand cs).bind fun rss =>
      Demand.forEach (combos rss) (P.callDemand rule.marksStuck)).map
        (List.map (MAtom.markIf (MAtom.expr m cs).erase))
  | t => .done [t]

/-- One evaluation step: what evaluating `t` demands and returns. -/
def stepDemand (rule : ReturnRule) (P : Program) (t : MAtom) : Demand (List MAtom) :=
  if rule.keeps t then .done [t] else openStep rule P t

@[simp] theorem stepDemand_reevaluate (P : Program) (t : MAtom) :
    stepDemand .reevaluate P t = openStep .reevaluate P t := by
  cases t <;> rfl

theorem stepDemand_of_not_keeps {rule : ReturnRule} (P : Program) {t : MAtom}
    (h : rule.keeps t = false) : stepDemand rule P t = openStep rule P t := by
  simp [stepDemand, h]

/-- The evaluator with recursion depth `n`. -/
def evalFuel (rule : ReturnRule) (P : Program) : ℕ → Evaluator
  | 0 => fun _ => none
  | n + 1 => fun t => (stepDemand rule P t).run (evalFuel rule P n)

@[simp] theorem evalFuel_zero (rule : ReturnRule) (P : Program) (t : MAtom) :
    evalFuel rule P 0 t = none := rfl

theorem evalFuel_succ (rule : ReturnRule) (P : Program) (n : ℕ) (t : MAtom) :
    evalFuel rule P (n + 1) t = (stepDemand rule P t).run (evalFuel rule P n) := rfl

theorem evalFuel_extends_succ (rule : ReturnRule) (P : Program) :
    ∀ n, (evalFuel rule P n).Extends (evalFuel rule P (n + 1)) := by
  intro n
  induction n with
  | zero => intro t r h; simp at h
  | succ n ih => intro t r h; exact Demand.run_mono ih h

theorem evalFuel_extends (rule : ReturnRule) (P : Program) {n m : ℕ} (h : n ≤ m) :
    (evalFuel rule P n).Extends (evalFuel rule P m) := by
  induction h with
  | refl => exact Evaluator.Extends.refl _
  | step _ ih => exact ih.trans (evalFuel_extends_succ rule P _)

/-- Results do not depend on the depth at which they are reached. -/
theorem evalFuel_det (rule : ReturnRule) (P : Program) {n m : ℕ} {t : MAtom}
    {R R' : List MAtom} (h : evalFuel rule P n t = some R) (h' : evalFuel rule P m t = some R') :
    R = R' := by
  have h1 := evalFuel_extends rule P (le_max_left n m) t R h
  have h2 := evalFuel_extends rule P (le_max_right n m) t R' h'
  rw [h1] at h2
  exact Option.some.inj h2

open Classical in
/-- The evaluator: the limit of `evalFuel` over all depths. -/
noncomputable def eval (rule : ReturnRule) (P : Program) : Evaluator := fun t =>
  if h : ∃ n, (evalFuel rule P n t).isSome then evalFuel rule P (Nat.find h) t else none

theorem eval_eq_some_iff {rule : ReturnRule} {P : Program} {t : MAtom} {R : List MAtom} :
    eval rule P t = some R ↔ ∃ n, evalFuel rule P n t = some R := by
  classical
  constructor
  · intro h
    simp only [eval] at h
    split at h
    · exact ⟨_, h⟩
    · simp at h
  · rintro ⟨n, hn⟩
    have hex : ∃ n, (evalFuel rule P n t).isSome := ⟨n, by simp [hn]⟩
    simp only [eval, dif_pos hex]
    obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.mp (Nat.find_spec hex)
    rw [hR', evalFuel_det rule P hR' hn]

theorem evalFuel_extends_eval (rule : ReturnRule) (P : Program) (n : ℕ) :
    (evalFuel rule P n).Extends (eval rule P) :=
  fun _ _ h => eval_eq_some_iff.mpr ⟨n, h⟩

/-- The evaluator is a fixed point of one evaluation step. -/
theorem eval_fix (rule : ReturnRule) (P : Program) (t : MAtom) :
    eval rule P t = (stepDemand rule P t).run (eval rule P) := by
  cases h : eval rule P t with
  | some R =>
    obtain ⟨n, hn⟩ := eval_eq_some_iff.mp h
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [evalFuel_succ] at hn
      exact (Demand.run_mono (evalFuel_extends_eval rule P n) hn).symm
  | none =>
    cases hrun : (stepDemand rule P t).run (eval rule P) with
    | none => rfl
    | some R =>
      obtain ⟨n, hn⟩ := Demand.run_continuous (evalFuel_extends_succ rule P)
        (fun _ _ h => eval_eq_some_iff.mp h) hrun
      have : eval rule P t = some R := eval_eq_some_iff.mpr ⟨n + 1, hn⟩
      rw [h] at this
      cases this

/-- Read a converged depth-bounded run as the evaluator's answer. -/
theorem eval_of_evalFuel {rule : ReturnRule} {P : Program} {n : ℕ} {t : MAtom}
    {R : List MAtom} (h : evalFuel rule P n t = some R) : eval rule P t = some R :=
  eval_eq_some_iff.mpr ⟨n, h⟩

/-- Observation: plain atoms in, erasures of the results out, in order. -/
noncomputable def observe (rule : ReturnRule) (P : Program) (a : Atom) : Option (List Atom) :=
  (eval rule P (code a)).map (List.map MAtom.erase)

/-- Read a converged depth-bounded run as an observation. -/
theorem observe_of_evalFuel {rule : ReturnRule} {P : Program} {n : ℕ} {a : Atom}
    {R : List Atom} (h : (evalFuel rule P n (code a)).map (List.map MAtom.erase) = some R) :
    observe rule P a = some R := by
  obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.mp h
  simp [observe, eval_of_evalFuel hR']

/-! ## Unfolding one step -/

@[simp] theorem stepDemand_symbol (rule : ReturnRule) (P : Program) (s : String) :
    stepDemand rule P (.symbol s) = .done [.symbol s] := by cases rule <;> rfl
@[simp] theorem stepDemand_var (rule : ReturnRule) (P : Program) (x : String) :
    stepDemand rule P (.var x) = .done [.var x] := by cases rule <;> rfl
@[simp] theorem stepDemand_grounded (rule : ReturnRule) (P : Program) (g : GroundedValue) :
    stepDemand rule P (.grounded g) = .done [.grounded g] := by cases rule <;> rfl

theorem stepDemand_expr_open {rule : ReturnRule} (P : Program) {m : Bool} (cs : List MAtom)
    (h : (rule.honorsMark && m) = false) :
    stepDemand rule P (.expr m cs) = ((P.argsDemand cs).bind fun rss =>
      Demand.forEach (combos rss) (P.callDemand rule.marksStuck)).map
        (List.map (MAtom.markIf (MAtom.expr m cs).erase)) := by
  simp [stepDemand, ReturnRule.keeps, h, openStep]

/-- Under a rule that reads the mark, a value is its own single result. -/
theorem stepDemand_value {rule : ReturnRule} (hr : rule.honorsMark = true) (P : Program)
    {v : MAtom} (hv : v.isValue = true) : stepDemand rule P v = .done [v] := by
  cases v with
  | expr m cs =>
    simp only [MAtom.isValue] at hv
    simp [stepDemand, ReturnRule.keeps, hr, hv]
  | _ => cases rule <;> rfl

theorem eval_value {rule : ReturnRule} (hr : rule.honorsMark = true) (P : Program) {v : MAtom}
    (hv : v.isValue = true) : eval rule P v = some [v] := by
  rw [eval_fix, stepDemand_value hr P hv]; rfl

/-- Atoms without an expression root are their own single result under either
rule. -/
theorem eval_nonexpr (rule : ReturnRule) (P : Program) {v : MAtom}
    (hv : ∀ m cs, v ≠ .expr m cs) : eval rule P v = some [v] := by
  rw [eval_fix]
  cases v with
  | expr m cs => exact absurd rfl (hv m cs)
  | _ => cases rule <;> rfl

theorem evalFuel_value {rule : ReturnRule} (hr : rule.honorsMark = true) (P : Program) (n : ℕ)
    {v : MAtom} (hv : v.isValue = true) : evalFuel rule P (n + 1) v = some [v] := by
  rw [evalFuel_succ, stepDemand_value hr P hv]; rfl

end Mettapedia.Languages.MeTTa.HE.EvaluatedValues

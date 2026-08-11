import Mettapedia.Logic.LP.StandardizeApart

/-!
# Prolog control syntax over the canonical LP representation

This module extends `Logic.LP` terms, atoms, and clauses with Prolog control.
It does not introduce another term language or resolver.  Ordinary predicate
calls carry `LP.Atom` directly, and a definite LP clause embeds by interpreting
its ordered body as a conjunction of calls.

The older `PrologGoal` type in `Core.lean` is a `MeTTaIL.Pattern`-level
characterization used by the ISO fixture corpus.  `Goal` below is the syntax
consumed by the canonical executable Prolog lane.
-/

namespace Mettapedia.Logic.Prolog

/-! ## Goals -/

/-- Prolog control over one canonical `Logic.LP` signature.

`call` is the only clause-selection constructor.  All data arguments are
ordinary `LP.Term`s, so unification, freshening, readback, and least-model
soundness continue to use the established LP kernel. -/
inductive Goal (sigma : LP.LPSignature) where
  | call (atom : LP.Atom sigma)
  | succeed
  | fail
  | cut
  | conj (left right : Goal sigma)
  | disj (left right : Goal sigma)
  | ifThenElse (condition thenBranch elseBranch : Goal sigma)
  | softIfThenElse (condition thenBranch elseBranch : Goal sigma)
  | once (goal : Goal sigma)
  | neg (goal : Goal sigma)
  | unify (left right : LP.Term sigma)
  | notUnify (left right : LP.Term sigma)
  | isVar (term : LP.Term sigma)
  | findall (template : LP.Term sigma) (generator : Goal sigma)
      (bag : LP.Term sigma)
  | catch (guarded : Goal sigma) (catcher : LP.Term sigma)
      (recovery : Goal sigma)
  | throw (ball : LP.Term sigma)

namespace Goal

/-- The ordered conjunction represented by a definite-clause body.

The empty body is `succeed`; a singleton remains a single `call`; longer
bodies are right-associated. -/
def calls {sigma : LP.LPSignature} : List (LP.Atom sigma) -> Goal sigma
  | [] => .succeed
  | [atom] => .call atom
  | atom :: next :: rest => .conj (.call atom) (calls (next :: rest))

/-- Recognize the pure definite-clause fragment and recover its ordered atoms.
No control constructor is silently erased. -/
def toAtoms? {sigma : LP.LPSignature} : Goal sigma -> Option (List (LP.Atom sigma))
  | .call atom => some [atom]
  | .succeed => some []
  | .conj left right => do
      let leftAtoms <- left.toAtoms?
      let rightAtoms <- right.toAtoms?
      pure (leftAtoms ++ rightAtoms)
  | _ => none

@[simp]
theorem toAtoms?_calls {sigma : LP.LPSignature}
    (atoms : List (LP.Atom sigma)) :
    toAtoms? (calls atoms) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          simp only [calls, toAtoms?]
          rw [inductionHypothesis]
          rfl

@[simp]
theorem toAtoms?_cut {sigma : LP.LPSignature} :
    toAtoms? (.cut : Goal sigma) = none := rfl

@[simp]
theorem toAtoms?_disj {sigma : LP.LPSignature} (left right : Goal sigma) :
    toAtoms? (.disj left right) = none := rfl

/-- Standardize every term in a goal into one activation scope. -/
def atScope {sigma : LP.LPSignature} (scope : Nat) :
    Goal sigma -> Goal sigma.scoped
  | .call atom => .call (atom.atScope scope)
  | .succeed => .succeed
  | .fail => .fail
  | .cut => .cut
  | .conj left right => .conj (left.atScope scope) (right.atScope scope)
  | .disj left right => .disj (left.atScope scope) (right.atScope scope)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (condition.atScope scope) (thenBranch.atScope scope)
        (elseBranch.atScope scope)
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse (condition.atScope scope) (thenBranch.atScope scope)
        (elseBranch.atScope scope)
  | .once goal => .once (goal.atScope scope)
  | .neg goal => .neg (goal.atScope scope)
  | .unify left right => .unify (left.atScope scope) (right.atScope scope)
  | .notUnify left right =>
      .notUnify (left.atScope scope) (right.atScope scope)
  | .isVar term => .isVar (term.atScope scope)
  | .findall template generator bag =>
      .findall (template.atScope scope) (generator.atScope scope)
        (bag.atScope scope)
  | .catch guarded catcher recovery =>
      .catch (guarded.atScope scope) (catcher.atScope scope)
        (recovery.atScope scope)
  | .throw ball => .throw (ball.atScope scope)

@[simp]
theorem atScope_calls {sigma : LP.LPSignature} (scope : Nat)
    (atoms : List (LP.Atom sigma)) :
    atScope scope (calls atoms) =
      calls (atoms.map (LP.Atom.atScope scope)) := by
  induction atoms with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          simp only [calls, atScope, List.map_cons]
          rw [inductionHypothesis]
          rfl

end Goal

/-! ## Prolog clauses and the exact pure-Horn embedding -/

/-- A Prolog clause has an LP head and a control-aware body. -/
@[ext]
structure Clause (sigma : LP.LPSignature) where
  head : LP.Atom sigma
  body : Goal sigma

/-- A source-ordered Prolog program. -/
abbrev Program (sigma : LP.LPSignature) := List (Clause sigma)

namespace Clause

/-- Embed one definite LP clause without changing its head, terms, or body
order. -/
def ofLP {sigma : LP.LPSignature} (clause : LP.Clause sigma) : Clause sigma where
  head := clause.head
  body := Goal.calls clause.body

/-- Project a clause back to LP exactly when its body is a pure conjunction of
ordinary calls. -/
def toLP? {sigma : LP.LPSignature} (clause : Clause sigma) :
    Option (LP.Clause sigma) := do
  let body <- clause.body.toAtoms?
  pure { head := clause.head, body }

@[simp]
theorem toLP?_ofLP {sigma : LP.LPSignature} (clause : LP.Clause sigma) :
    (ofLP clause).toLP? = some clause := by
  cases clause
  simp [ofLP, toLP?]

/-- The pure-clause embedding loses no source information. -/
theorem ofLP_injective {sigma : LP.LPSignature} :
    Function.Injective (@ofLP sigma) := by
  intro first second equal
  have projected := congrArg toLP? equal
  simpa using projected

/-- Control cannot be laundered into an LP clause: projection rejects it. -/
@[simp]
theorem cut_toLP?_eq_none {sigma : LP.LPSignature} (head : LP.Atom sigma) :
    toLP? ({ head, body := .cut } : Clause sigma) = none := rfl

/-- Standardize a control-aware clause apart using the same scoped variables
as the LP kernel. -/
def atScope {sigma : LP.LPSignature} (scope : Nat)
    (clause : Clause sigma) : Clause sigma.scoped where
  head := clause.head.atScope scope
  body := clause.body.atScope scope

@[simp]
theorem atScope_ofLP {sigma : LP.LPSignature} (scope : Nat)
    (clause : LP.Clause sigma) :
    atScope scope (ofLP clause) = ofLP (clause.atScope scope) := by
  cases clause with
  | mk head body =>
      apply Clause.ext
      · rfl
      · exact Goal.atScope_calls scope body

end Clause

namespace Program

/-- Source-ordered clauses for one predicate.  Arity remains checked by the
canonical clause-entry boundary, so this index performs no semantic work. -/
def clausesFor {sigma : LP.LPSignature} [DecidableEq sigma.relationSymbols]
    (program : Program sigma) (symbol : sigma.relationSymbols) :
    List (Clause sigma) :=
  program.filter fun clause => decide (clause.head.symbol = symbol)

@[simp]
theorem clausesFor_append {sigma : LP.LPSignature}
    [DecidableEq sigma.relationSymbols]
    (left right : Program sigma) (symbol : sigma.relationSymbols) :
    clausesFor (left ++ right) symbol =
      clausesFor left symbol ++ clausesFor right symbol := by
  simp [clausesFor]

/-- Embed an LP program clause-for-clause, preserving source order. -/
def ofLP {sigma : LP.LPSignature} (program : LP.Program sigma) : Program sigma :=
  program.map Clause.ofLP

/-- Recover an LP program only when every clause belongs to the pure fragment. -/
def toLP? {sigma : LP.LPSignature} (program : Program sigma) :
    Option (LP.Program sigma) :=
  match program with
  | [] => some []
  | clause :: rest => do
      let first <- clause.toLP?
      let later <- toLP? rest
      pure (first :: later)

@[simp]
theorem toLP?_ofLP {sigma : LP.LPSignature} (program : LP.Program sigma) :
    toLP? (ofLP program) = some program := by
  induction program with
  | nil => rfl
  | cons clause rest inductionHypothesis =>
      simp only [ofLP, List.map_cons, toLP?, Clause.toLP?_ofLP]
      change (do
        let later <- toLP? (ofLP rest)
        pure (clause :: later)) = some (clause :: rest)
      rw [inductionHypothesis]
      rfl

/-- The clausewise pure-program embedding preserves order, multiplicity, and
all source syntax. -/
theorem ofLP_injective {sigma : LP.LPSignature} :
    Function.Injective (@ofLP sigma) := by
  intro first second equal
  have projected := congrArg toLP? equal
  simpa using projected

end Program

end Mettapedia.Logic.Prolog

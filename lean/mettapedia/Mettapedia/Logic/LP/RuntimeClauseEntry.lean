import Mettapedia.Logic.LP.RuntimeMaterialize
import Mettapedia.Logic.LP.RuntimeUnification

/-!
# Canonical runtime clause entry

Clause selection and control decide *which* materialized clause to enter.  This
module defines the one mechanism that enters its head: validate predicate and
arity, construct the ordered head-unification agenda, and start the canonical
graph unifier.

The body type is parametric.  Pure LP atom lists and typed Prolog control
therefore share this exact entry mechanism without sharing or duplicating a
search machine.
-/

namespace Mettapedia.Logic.LP.RuntimeClauseEntry

open RuntimeTerm RuntimeMaterialize

/-- A selected source clause cannot enter a call with a different predicate
or arity. -/
inductive EntryError where
  | predicateMismatch
  | arityMismatch
deriving DecidableEq, Repr

/-- The result of entering a materialized clause.  The memory and body are
carried unchanged; only the head-unification machine is initialized. -/
structure Entered (sigma : LPSignature) (Body : Type*) where
  memory : Memory sigma
  body : Body
  unifier : RuntimeUnification.Machine sigma

/-- Enter one already-materialized clause head.  Argument pairing is
left-to-right and uses the signature-sized runtime arrays. -/
def enter {sigma : LPSignature} [DecidableEq sigma.relationSymbols]
    (goal head : RuntimeAtom sigma) (memory : Memory sigma) (body : Body) :
    Except EntryError (Entered sigma Body) :=
  if goal.symbol = head.symbol then
    if goal.args.size = head.args.size then
      let agenda := goal.args.toList.zip head.args.toList
      .ok {
        memory
        body
        unifier := RuntimeUnification.startMany memory agenda
      }
    else
      .error .arityMismatch
  else
    .error .predicateMismatch

/-- Matching heads enter with the exact supplied memory/body and the canonical
ordered unification agenda. -/
theorem enter_of_matches {sigma : LPSignature}
    [DecidableEq sigma.relationSymbols]
    (goal head : RuntimeAtom sigma) (memory : Memory sigma) (body : Body)
    (hPredicate : goal.symbol = head.symbol)
    (hArity : goal.args.size = head.args.size) :
    enter goal head memory body = .ok {
      memory
      body
      unifier := RuntimeUnification.startMany memory
        (goal.args.toList.zip head.args.toList)
    } := by
  simp [enter, hPredicate, hArity]

/-- Predicate mismatch is rejected before a unifier can be created. -/
theorem enter_predicate_mismatch {sigma : LPSignature}
    [DecidableEq sigma.relationSymbols]
    (goal head : RuntimeAtom sigma) (memory : Memory sigma) (body : Body)
    (hMismatch : goal.symbol ≠ head.symbol) :
    enter goal head memory body = .error .predicateMismatch := by
  simp [enter, hMismatch]

/-- Arity mismatch is independently observable after predicates agree. -/
theorem enter_arity_mismatch {sigma : LPSignature}
    [DecidableEq sigma.relationSymbols]
    (goal head : RuntimeAtom sigma) (memory : Memory sigma) (body : Body)
    (hPredicate : goal.symbol = head.symbol)
    (hMismatch : goal.args.size ≠ head.args.size) :
    enter goal head memory body = .error .arityMismatch := by
  simp [enter, hPredicate, hMismatch]

end Mettapedia.Logic.LP.RuntimeClauseEntry

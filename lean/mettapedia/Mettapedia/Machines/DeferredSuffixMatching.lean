import Mettapedia.Machines.FreshFrameNoninterference
import Mettapedia.Logic.LP.ListTerms

/-!
# Postponing suffix materialization past a failed head match

The backing sequence is fixed during one atomic match. Materialization builds
an ordinary first-order sequence term; both head and tail constraints use the
existing total unifier, retaining the complete substitution and aliasing.

The cost counts materialization requests, not instructions or physical bytes.
The result is a cost refinement: postponement never adds a request and avoids
one on every rejected head. No optimality theorem about arbitrary matching
algorithms, arena allocation, native carriers or the C implementation is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DeferredSuffixMatching

open Mettapedia.Logic.LP
open FreshFrameNoninterference

variable {Constant Variable : Type} [DecidableEq Constant] [DecidableEq Variable]

abbrev Sig (Constant Variable : Type) := ListTerms.signature Constant Variable
abbrev Value (Constant Variable : Type) := Term (Sig Constant Variable)

/-- An eager suffix is constructed before any head constraint is attempted. -/
def eager (store : Subst (Sig Constant Variable))
    (headPattern tailPattern : Value Constant Variable) :
    List (Value Constant Variable) → Option (Subst (Sig Constant Variable)) × Nat
  | [] => (none, 0)
  | head :: tail =>
      let suffix := ListTerms.ofList tail
      ((solveStep store [(headPattern, head)]).bind
        (fun next => solveStep next [(tailPattern, suffix)]), 1)

/-- The pending suffix is just a borrowed sequence until the head succeeds. -/
def deferred (store : Subst (Sig Constant Variable))
    (headPattern tailPattern : Value Constant Variable) :
    List (Value Constant Variable) → Option (Subst (Sig Constant Variable)) × Nat
  | [] => (none, 0)
  | head :: tail =>
      match solveStep store [(headPattern, head)] with
      | none => (none, 0)
      | some next => (solveStep next [(tailPattern, ListTerms.ofList tail)], 1)

/-- Successful matching is specified as two ordered constraints, not by
either materialization schedule. -/
def Matches (store result : Subst (Sig Constant Variable))
    (headPattern tailPattern head : Value Constant Variable)
    (tail : List (Value Constant Variable)) : Prop :=
  ∃ next, solveStep store [(headPattern, head)] = some next ∧
    solveStep next [(tailPattern, ListTerms.ofList tail)] = some result

theorem deferred_matches_iff (store result : Subst (Sig Constant Variable))
    (headPattern tailPattern head : Value Constant Variable)
    (tail : List (Value Constant Variable)) :
    (deferred store headPattern tailPattern (head :: tail)).1 = some result ↔
      Matches store result headPattern tailPattern head tail := by
  unfold deferred Matches
  cases first : solveStep store [(headPattern, head)] <;> simp [first]

theorem outcomes_equal (store : Subst (Sig Constant Variable))
    (headPattern tailPattern : Value Constant Variable)
    (values : List (Value Constant Variable)) :
    (deferred store headPattern tailPattern values).1 =
      (eager store headPattern tailPattern values).1 := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [deferred, eager]
      cases solveStep store [(headPattern, head)] <;> rfl

theorem requests_nonincreasing (store : Subst (Sig Constant Variable))
    (headPattern tailPattern : Value Constant Variable)
    (values : List (Value Constant Variable)) :
    (deferred store headPattern tailPattern values).2 ≤
      (eager store headPattern tailPattern values).2 := by
  cases values with
  | nil => exact Nat.le_refl _
  | cons head tail =>
      simp only [deferred, eager]
      cases solveStep store [(headPattern, head)] <;> simp

theorem rejected_head_no_materialization (store : Subst (Sig Constant Variable))
    (headPattern tailPattern head : Value Constant Variable)
    (tail : List (Value Constant Variable))
    (rejected : solveStep store [(headPattern, head)] = none) :
    (deferred store headPattern tailPattern (head :: tail)).2 = 0 ∧
      (eager store headPattern tailPattern (head :: tail)).2 = 1 := by
  simp [deferred, eager, rejected]

namespace Controls

abbrev Signature := Sig Nat Nat

def start : Subst Signature := Subst.id Signature

/-- The head binds a variable; the tail must observe that same binding. -/
theorem alias_preserved :
    ((deferred start (.var 0) (ListTerms.ofList [.var 0])
      [.const 7, .const 7]).1.map (fun store => store 0)) = some (.const 7) ∧
    (deferred start (.var 0) (ListTerms.ofList [.var 0])
      [.const 7, .const 7]).2 = 1 := by
  simp [deferred, solveStep, start, ListTerms.ofList, Subst.applyEqs,
    Subst.applyTerm, Subst.id, unifyTotal, Subst.comp, Subst.single,
    Term.occursIn, finPairsToList, List.finRange]
  exact ⟨_, rfl⟩

theorem rejecting_head_saves_request :
    (deferred start (.const 3) (.var 0) [.const 7, .const 9]).2 = 0 ∧
    (eager start (.const 3) (.var 0) [.const 7, .const 9]).2 = 1 := by
  simp [deferred, eager, solveStep, start, Subst.applyEqs,
    Subst.applyTerm, Subst.id, unifyTotal]

/-- Tail mismatch is still a rejection, after exactly one request. -/
theorem rejecting_tail_preserved :
    (deferred start (.var 0) (ListTerms.ofList [.var 0])
      [.const 7, .const 9]).1 = none ∧
    (deferred start (.var 0) (ListTerms.ofList [.var 0])
      [.const 7, .const 9]).2 = 1 := by
  simp [deferred, solveStep, start, ListTerms.ofList, Subst.applyEqs,
    Subst.applyTerm, Subst.id, unifyTotal, Subst.comp, Subst.single,
    Term.occursIn, finPairsToList, List.finRange]

end Controls
end Mettapedia.Machines.DeferredSuffixMatching

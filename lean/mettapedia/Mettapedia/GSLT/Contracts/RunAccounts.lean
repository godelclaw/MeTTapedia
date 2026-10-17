import Mettapedia.CategoryTheory.RunAccount
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Visible traces and costs are both run accounts

A run account (`Mettapedia.Effects.RunAccount`) assigns an element of a monoid
to every run of a category, multiplicatively along composition.  Two contract
dimensions are run accounts of the same runs:

* the **visible trace** of a run, in the free monoid of events;
* the **cost** of a run, in a monoid of costs.

Labelling every edge of a transition graph with a monoid element gives an
account of the paths of its free category (`pathAccount`), first edge first
(`pathAccount_cons`).  The trace and the cost of a contract are one account
into the product monoid (`RunAccount.prod`).

An **observer** that forgets some events is a monoid homomorphism out of the
free monoid (`keepOnly`), and the observed account is the trace account mapped
along it (`RunAccount.map`).  An observer that forgets faults identifies a run
that faults before answering with a run that does administrative work before
answering, although their raw traces differ and their costs agree
(`fault_erasure_identifies`).  Whether an observer may forget an event is a
declared contract, not a consequence of the account.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Accounts

open _root_.CategoryTheory
open Mettapedia.Effects

universe u v w

section Paths

variable {V : Type u} [Quiver.{v} V] {M : Type w} [Monoid M]

/-- The prefunctor sending every edge to its label, in the one-object category
of the opposite monoid. -/
def labelPrefunctor (label : ∀ {a b : V}, (a ⟶ b) → M) : V ⥤q SingleObj Mᵐᵒᵖ where
  obj _ := SingleObj.star _
  map e := MulOpposite.op (label e)

/-- **The account of a path is the product of its edge labels.** -/
def pathAccount (label : ∀ {a b : V}, (a ⟶ b) → M) : RunAccount (Paths V) M :=
  RunAccount.ofFunctor (Paths.lift (labelPrefunctor label))

@[simp] theorem pathAccount_nil (label : ∀ {a b : V}, (a ⟶ b) → M) (a : V) :
    (pathAccount label).of (Quiver.Path.nil : Quiver.Path a a) = 1 := rfl

/-- Extending a path by an edge multiplies its account by the edge's label,
on the right. -/
theorem pathAccount_cons (label : ∀ {a b : V}, (a ⟶ b) → M) {a b c : V}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    (pathAccount label).of (p.cons e) = (pathAccount label).of p * label e := rfl

end Paths

/-! ## Traces, costs, and an observer -/

/-- Visible events. -/
inductive Event where
  | fault
  | served
  deriving DecidableEq, Repr

/-- Traces of events are compared as lists. -/
instance : DecidableEq (FreeMonoid Event) := inferInstanceAs (DecidableEq (List Event))

/-- The observer keeping only the events a predicate selects. -/
def keepOnly (keep : Event → Bool) : FreeMonoid Event →* FreeMonoid Event :=
  FreeMonoid.lift fun e => if keep e then FreeMonoid.of e else 1

/-- Keep everything but faults. -/
def notFault : Event → Bool
  | .fault => false
  | .served => true

/-- Nodes of a small transition graph. -/
inductive Node where
  | root
  | faulted
  | working
  | done
  deriving DecidableEq, Repr

/-- Edges: a fault then the answer, or administrative work then the answer. -/
inductive Edge : Node → Node → Type where
  | fault : Edge .root .faulted
  | answerAfterFault : Edge .faulted .done
  | admin : Edge .root .working
  | answerAfterWork : Edge .working .done

instance : Quiver Node := ⟨Edge⟩

/-- The visible event of an edge, if any. -/
def traceLabel : ∀ {a b : Node}, Edge a b → FreeMonoid Event
  | _, _, .fault => FreeMonoid.of .fault
  | _, _, .answerAfterFault => FreeMonoid.of .served
  | _, _, .admin => 1
  | _, _, .answerAfterWork => FreeMonoid.of .served

/-- Every edge costs one unit of work. -/
def costLabel : ∀ {a b : Node}, Edge a b → Multiplicative ℕ
  | _, _, _ => Multiplicative.ofAdd 1

def traceAccount : RunAccount (Paths Node) (FreeMonoid Event) :=
  pathAccount fun e => traceLabel e

def costAccount : RunAccount (Paths Node) (Multiplicative ℕ) :=
  pathAccount fun e => costLabel e

/-- The contract account: trace and cost of the same runs. -/
def contractAccount : RunAccount (Paths Node) (FreeMonoid Event × Multiplicative ℕ) :=
  traceAccount.prod costAccount

/-- A fault, then the answer. -/
def faultRun : Quiver.Path Node.root Node.done :=
  (Quiver.Path.nil.cons (Edge.fault : Node.root ⟶ .faulted)).cons
    (Edge.answerAfterFault : Node.faulted ⟶ .done)

/-- Administrative work, then the answer. -/
def adminRun : Quiver.Path Node.root Node.done :=
  (Quiver.Path.nil.cons (Edge.admin : Node.root ⟶ .working)).cons
    (Edge.answerAfterWork : Node.working ⟶ .done)

/-- **Forgetting faults identifies two runs that the raw trace separates**, at
equal cost. -/
theorem fault_erasure_identifies :
    (traceAccount.map (keepOnly notFault)).of faultRun =
        (traceAccount.map (keepOnly notFault)).of adminRun ∧
      traceAccount.of faultRun ≠ traceAccount.of adminRun ∧
      costAccount.of faultRun = costAccount.of adminRun := by
  refine ⟨?_, ?_, rfl⟩
  · change keepOnly notFault (traceAccount.of faultRun) = keepOnly notFault (traceAccount.of adminRun)
    decide
  · decide

/-- The contract account reads both dimensions of a run at once. -/
theorem contractAccount_of {a b : Node} (run : Quiver.Path a b) :
    contractAccount.of run = (traceAccount.of run, costAccount.of run) := rfl

/-! ## Axiom audit -/

#print axioms pathAccount_cons
#print axioms fault_erasure_identifies

end Mettapedia.GSLT.Contracts.Accounts

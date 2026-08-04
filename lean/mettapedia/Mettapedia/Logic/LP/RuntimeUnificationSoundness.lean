import Mettapedia.Logic.LP.RuntimeReadback
import Mettapedia.Logic.LP.RuntimeUnification

/-!
# Toward success soundness of the runtime graph unifier

The unification machine has executable behavior but no semantic theorem:
nothing yet says that reaching `.success` makes a unified pair denote the same
term.  This module builds the semantic layer for that theorem on the
function-free fragment (no `app` cells).  Scope, stated honestly: this covers
the current regression *fixtures*, not the runtime — `RuntimeQuery`
materializes and unifies compound cells, whose treatment needs structural
graph correspondence (a later milestone), and rational (cyclic) structures are
excluded by the `.ok`-conditional statements rather than handled.  These are
implementation-refinement lemmas about the canonical representation; they are
not, by themselves, semantic grounding against an SLD judgment.

Design, chosen to avoid fighting the fixed readback budget:

* equalities are carried as **root convergence at some explicit fuel**
  (`ConvergedAt`), which is budget-free and survives later bindings;
* machine writes only overwrite an *unbound* variable cell — a dereference
  terminal — and never change heap size, so every other cell (including every
  `const` root) is immutable along a unification run;
* readback is connected to convergence by `readTermFuel_of_root`, and final
  `Heap.readTerm` statements follow by fuel monotonicity alone.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeUnificationSoundness

open RuntimeTerm RuntimeUnification RuntimeReadback

/-! ## Function-free heaps -/

/-- No compound cells anywhere in the heap. -/
def FunctionFree {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (address : Addr) (symbol : σ.functionSymbols) (args : Array Addr),
    heap[address]? ≠ some (Cell.app symbol args)

/-! ## Targeted readback equations -/

theorem readTermFuel_invalid {σ : LPSignature} (heap : Heap σ)
    (fuel address : Nat) (h : heap[address]? = none) :
    readTermFuel heap (fuel + 1) address =
      .error (.invalidAddress address) := by
  simp [readTermFuel, h]

theorem readTermFuel_app {σ : LPSignature} (heap : Heap σ)
    (fuel address : Nat) (symbol : σ.functionSymbols) (args : Array Addr)
    (h : heap[address]? = some (Cell.app symbol args)) :
    readTermFuel heap (fuel + 1) address =
      (do
        let children ← readListFuel heap fuel args.toList
        if hLength : children.length = σ.functionArity symbol then
          Except.ok (.app symbol
            fun index => children.get (Fin.cast hLength.symm index))
        else
          Except.error .arityMismatch) := by
  simp [readTermFuel, h]

/-! ## Fuel monotonicity of readback -/

theorem readListFuel_mono {σ : LPSignature} {heap : Heap σ} {fuel : Nat}
    (termMono : ∀ address term, readTermFuel heap fuel address = .ok term →
      readTermFuel heap (fuel + 1) address = .ok term) :
    ∀ (addresses : List Addr) (terms : List (Term σ)),
      readListFuel heap fuel addresses = .ok terms →
      readListFuel heap (fuel + 1) addresses = .ok terms := by
  intro addresses
  induction addresses with
  | nil => intro terms h; simpa [readListFuel] using h
  | cons head tail tailIh =>
      intro terms h
      simp only [readListFuel, Bind.bind, Except.bind] at h ⊢
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; simp at h
      | ok headTerm =>
          rw [hHead] at h
          rw [termMono head headTerm hHead]
          cases hTail : readListFuel heap fuel tail with
          | error e => rw [hTail] at h; simp at h
          | ok tailTerms =>
              rw [hTail] at h
              rw [tailIh tailTerms hTail]
              exact h

theorem readTermFuel_mono {σ : LPSignature} (heap : Heap σ) :
    ∀ (fuel : Nat) (address : Addr) (term : Term σ),
      readTermFuel heap fuel address = .ok term →
      readTermFuel heap (fuel + 1) address = .ok term := by
  intro fuel
  induction fuel with
  | zero => intro address term h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address term h
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell] at h
                  rw [readTermFuel_unbound heap (fuel + 1) address identity hcell]
                  exact h
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity hcell] at h
                  rw [readTermFuel_link heap (fuel + 1) address target identity hcell]
                  exact ih target term h
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              rw [readTermFuel_const heap (fuel + 1) address symbol hcell]
              exact h
          | app symbol args =>
              rw [readTermFuel_app heap fuel address symbol args hcell] at h
              rw [readTermFuel_app heap (fuel + 1) address symbol args hcell]
              simp only [Bind.bind, Except.bind] at h ⊢
              cases hArgs : readListFuel heap fuel args.toList with
              | error e => rw [hArgs] at h; simp at h
              | ok children =>
                  rw [hArgs] at h
                  rw [readListFuel_mono (fun a t => ih a t) args.toList
                    children hArgs]
                  exact h

theorem readTermFuel_mono_le {σ : LPSignature} (heap : Heap σ)
    {small large : Nat} (hle : small ≤ large) (address : Addr) (term : Term σ)
    (hRead : readTermFuel heap small address = .ok term) :
    readTermFuel heap large address = .ok term := by
  induction hle with
  | refl => exact hRead
  | step _ ih => exact readTermFuel_mono heap _ address term ih

/-! ## Root convergence -/

/-- Two addresses dereference to one shared root at some explicit fuel.  The
existential fuel makes the predicate budget-free: it is preserved verbatim when
later bindings lengthen chains elsewhere. -/
def ConvergedAt {σ : LPSignature} (heap : Heap σ) (left right : Addr) : Prop :=
  ∃ fuel root,
    Heap.derefLoop heap fuel left = .ok (.root root) ∧
    Heap.derefLoop heap fuel right = .ok (.root root)

/-- On a function-free heap, reading an address is reading its dereference
root: the chain fuel shifts out and the leaf costs one. -/
theorem readTermFuel_of_root {σ : LPSignature} {heap : Heap σ}
    (ff : FunctionFree heap) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap fuel address = .ok (.root root) →
      ∀ extra, readTermFuel heap (fuel + extra) address =
        readTermFuel heap (1 + extra) root := by
  intro fuel
  induction fuel with
  | zero => intro address root h extra; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h extra
      cases hcell : heap[address]? with
      | none => simp [Heap.derefLoop, hcell] at h
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | some target =>
                  simp only [Heap.derefLoop, hcell] at h
                  have shift : fuel + 1 + extra = (fuel + extra) + 1 := by omega
                  rw [shift,
                    readTermFuel_link heap (fuel + extra) address target identity hcell]
                  exact ih target root h extra
              | none =>
                  simp only [Heap.derefLoop, hcell] at h
                  obtain rfl : address = root := by simpa using h
                  have shift : fuel + 1 + extra = (fuel + extra) + 1 := by omega
                  have shift' : 1 + extra = extra + 1 := by omega
                  rw [shift, shift',
                    readTermFuel_unbound heap (fuel + extra) address identity hcell,
                    readTermFuel_unbound heap extra address identity hcell]
          | const symbol =>
              simp only [Heap.derefLoop, hcell] at h
              obtain rfl : address = root := by simpa using h
              have shift : fuel + 1 + extra = (fuel + extra) + 1 := by omega
              have shift' : 1 + extra = extra + 1 := by omega
              rw [shift, shift',
                readTermFuel_const heap (fuel + extra) address symbol hcell,
                readTermFuel_const heap extra address symbol hcell]
          | app symbol args => exact absurd hcell (ff address symbol args)

/-- Converged addresses have equal finite readbacks: the load-bearing bridge
from machine facts to term equality.  Stated `.ok`-conditionally so cyclic
(rational) readbacks are excluded honestly rather than silently. -/
theorem ConvergedAt.readTerm_eq {σ : LPSignature} {heap : Heap σ}
    (ff : FunctionFree heap) {left right : Addr}
    (converged : ConvergedAt heap left right)
    {leftTerm rightTerm : Term σ}
    (hLeft : Heap.readTerm heap left = .ok leftTerm)
    (hRight : Heap.readTerm heap right = .ok rightTerm) :
    leftTerm = rightTerm := by
  obtain ⟨fuel, root, hL, hR⟩ := converged
  have hLBig : readTermFuel heap (fuel + (heap.size + 1)) left = .ok leftTerm :=
    readTermFuel_mono_le heap (by omega) left leftTerm hLeft
  have hRBig : readTermFuel heap (fuel + (heap.size + 1)) right = .ok rightTerm :=
    readTermFuel_mono_le heap (by omega) right rightTerm hRight
  have hLRoot := readTermFuel_of_root ff fuel left root hL (heap.size + 1)
  have hRRoot := readTermFuel_of_root ff fuel right root hR (heap.size + 1)
  have chain : (Except.ok leftTerm : Except ReadbackError (Term σ)) =
      .ok rightTerm := by
    calc (Except.ok leftTerm : Except ReadbackError (Term σ))
        = readTermFuel heap (fuel + (heap.size + 1)) left := hLBig.symm
      _ = readTermFuel heap (1 + (heap.size + 1)) root := hLRoot
      _ = readTermFuel heap (fuel + (heap.size + 1)) right := hRRoot.symm
      _ = Except.ok rightTerm := hRBig
  simpa using chain

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP

import Mettapedia.Logic.LP.RuntimeReadback
import Mettapedia.Logic.LP.Substitution
import Mettapedia.Logic.LP.SLD
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

/-! ## Write-frame facts for machine bindings -/

/-- Invert a successful `Memory.write`: the new heap is `set`, in bounds. -/
theorem write_ok_heap {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    ∃ hlt : address < memory.heap.size,
      memory'.heap = memory.heap.set address cell hlt := by
  unfold Memory.write at h
  split at h
  · split at h
    · split at h
      · exact ⟨‹_›, by cases h; rfl⟩
      · rcases hfind :
            (Cell.references cell).find?
              (fun target => decide (memory.heap.size ≤ target)) with _ | t <;>
          rw [hfind] at h <;> cases h
    · cases h
  · cases h

theorem heap_set_size {σ : LPSignature} (heap : Heap σ) (address : Addr)
    (cell : Cell σ) (hlt : address < heap.size) :
    (heap.set address cell hlt).size = heap.size := by
  simp

theorem heap_set_get_ne {σ : LPSignature} (heap : Heap σ) {address other : Addr}
    (cell : Cell σ) (hlt : address < heap.size) (hne : other ≠ address) :
    (heap.set address cell hlt)[other]? = heap[other]? := by
  simp [hne.symm]

theorem heap_set_get_self {σ : LPSignature} (heap : Heap σ) {address : Addr}
    (cell : Cell σ) (hlt : address < heap.size) :
    (heap.set address cell hlt)[address]? = some cell := by
  simp [hlt]

/-! ## Dereference persistence under one binding -/

/-- Dereference results are monotone in fuel (root results). -/
theorem derefLoop_mono {σ : LPSignature} (heap : Heap σ) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap fuel address = .ok (.root root) →
      Heap.derefLoop heap (fuel + 1) address = .ok (.root root) := by
  intro fuel
  induction fuel with
  | zero => intro address root h; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h
      cases hcell : heap[address]? with
      | none => simp [Heap.derefLoop, hcell] at h
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | some target =>
                  simp only [Heap.derefLoop, hcell] at h ⊢
                  exact ih target root h
              | none => simpa only [Heap.derefLoop, hcell] using h
          | const symbol => simpa only [Heap.derefLoop, hcell] using h
          | app symbol args => simpa only [Heap.derefLoop, hcell] using h

theorem derefLoop_mono_le {σ : LPSignature} (heap : Heap σ)
    {small large : Nat} (hle : small ≤ large) {address root : Addr}
    (h : Heap.derefLoop heap small address = .ok (.root root)) :
    Heap.derefLoop heap large address = .ok (.root root) := by
  induction hle with
  | refl => exact h
  | step _ ih => exact derefLoop_mono heap _ address root ih

/-- Chains that end at a root other than the freshly bound cell are untouched
by the binding: the bound cell was an unbound-variable *terminal*, so it can
only ever appear as a chain's endpoint. -/
theorem derefLoop_frame {σ : LPSignature} {heap heap' : Heap σ}
    {bound : Addr} {identity : σ.vars}
    (hBound : heap[bound]? = some (Cell.var identity none))
    (hFrame : ∀ other, other ≠ bound → heap'[other]? = heap[other]?) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap fuel address = .ok (.root root) → root ≠ bound →
      Heap.derefLoop heap' fuel address = .ok (.root root) := by
  intro fuel
  induction fuel with
  | zero => intro address root h _; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h hroot
      by_cases hz : address = bound
      · subst hz
        simp only [Heap.derefLoop, hBound] at h
        obtain rfl : address = root := by simpa using h
        exact absurd rfl hroot
      · cases hcell : heap[address]? with
        | none => simp [Heap.derefLoop, hcell] at h
        | some cell =>
            have hcell' : heap'[address]? = some cell := by
              rw [hFrame address hz]; exact hcell
            cases cell with
            | var identity₂ link =>
                cases link with
                | some target₂ =>
                    simp only [Heap.derefLoop, hcell] at h
                    simp only [Heap.derefLoop, hcell']
                    exact ih target₂ root h hroot
                | none =>
                    simp only [Heap.derefLoop, hcell] at h
                    simp only [Heap.derefLoop, hcell']
                    exact h
            | const symbol =>
                simp only [Heap.derefLoop, hcell] at h
                simp only [Heap.derefLoop, hcell']
                exact h
            | app symbol args =>
                simp only [Heap.derefLoop, hcell] at h
                simp only [Heap.derefLoop, hcell']
                exact h

/-- Chains that ended at the freshly bound cell continue to the binding's
target root, one hop longer. -/
theorem derefLoop_redirect {σ : LPSignature} {heap heap' : Heap σ}
    {bound : Addr} {identity : σ.vars} {target : Addr}
    (hBound : heap[bound]? = some (Cell.var identity none))
    (hFrame : ∀ other, other ≠ bound → heap'[other]? = heap[other]?)
    (hBound' : heap'[bound]? = some (Cell.var identity (some target)))
    (hTargetLeaf : ∀ fuel, Heap.derefLoop heap' (fuel + 1) target =
      .ok (.root target)) :
    ∀ (fuel : Nat) (address : Addr),
      Heap.derefLoop heap fuel address = .ok (.root bound) →
      Heap.derefLoop heap' (fuel + 1) address = .ok (.root target) := by
  intro fuel
  induction fuel with
  | zero => intro address h; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address h
      by_cases hz : address = bound
      · subst hz
        simp only [Heap.derefLoop, hBound']
        exact hTargetLeaf fuel
      · cases hcell : heap[address]? with
        | none => simp [Heap.derefLoop, hcell] at h
        | some cell =>
            have hcell' : heap'[address]? = some cell := by
              rw [hFrame address hz]; exact hcell
            cases cell with
            | var identity₂ link =>
                cases link with
                | some target₂ =>
                    simp only [Heap.derefLoop, hcell] at h
                    simp only [Heap.derefLoop, hcell']
                    exact ih target₂ h
                | none =>
                    simp only [Heap.derefLoop, hcell] at h
                    obtain rfl : address = bound := by simpa using h
                    exact absurd rfl hz
            | const symbol =>
                simp only [Heap.derefLoop, hcell] at h
                obtain rfl : address = bound := by simpa using h
                exact absurd rfl hz
            | app symbol args =>
                simp only [Heap.derefLoop, hcell] at h
                obtain rfl : address = bound := by simpa using h
                exact absurd rfl hz

/-! ## Discharged pairs: the run invariant's currency -/

/-- Leaf cells are dereference fixed points. -/
theorem derefLoop_leaf {σ : LPSignature} {heap : Heap σ} {address : Addr}
    {cell : Cell σ} (hcell : heap[address]? = some cell)
    (hleaf : ∀ identity target, cell ≠ Cell.var identity (some target)) :
    ∀ fuel, Heap.derefLoop heap (fuel + 1) address = .ok (.root address) := by
  intro fuel
  cases cell with
  | var identity link =>
      cases link with
      | none => simp [Heap.derefLoop, hcell]
      | some target => exact absurd rfl (hleaf identity target)
  | const symbol => simp [Heap.derefLoop, hcell]
  | app symbol args => simp [Heap.derefLoop, hcell]

/-- A discharged unification pair: either both sides converge to one root, or
both roots hold the same constant.  Exactly the two ways the machine ever
discharges a pair on a function-free heap. -/
def GoodPair {σ : LPSignature} (heap : Heap σ) (left right : Addr) : Prop :=
  ConvergedAt heap left right ∨
  ∃ fuel leftRoot rightRoot symbol,
    Heap.derefLoop heap fuel left = .ok (.root leftRoot) ∧
    Heap.derefLoop heap fuel right = .ok (.root rightRoot) ∧
    heap[leftRoot]? = some (Cell.const symbol) ∧
    heap[rightRoot]? = some (Cell.const symbol)

theorem GoodPair.symm {σ : LPSignature} {heap : Heap σ} {left right : Addr}
    (h : GoodPair heap left right) : GoodPair heap right left := by
  rcases h with ⟨fuel, root, hL, hR⟩ | ⟨fuel, ρl, ρr, symbol, hL, hR, hCl, hCr⟩
  · exact .inl ⟨fuel, root, hR, hL⟩
  · exact .inr ⟨fuel, ρr, ρl, symbol, hR, hL, hCr, hCl⟩

/-- Discharge by shared root (identical-root and fresh-binding cases). -/
theorem GoodPair.of_same_root {σ : LPSignature} {heap : Heap σ}
    {left right root : Addr} {fuel : Nat}
    (hL : Heap.derefLoop heap fuel left = .ok (.root root))
    (hR : Heap.derefLoop heap fuel right = .ok (.root root)) :
    GoodPair heap left right :=
  .inl ⟨fuel, root, hL, hR⟩

/-- Discharge by equal constants. -/
theorem GoodPair.of_const {σ : LPSignature} {heap : Heap σ}
    {left right leftRoot rightRoot : Addr} {fuel : Nat} {symbol : σ.constants}
    (hL : Heap.derefLoop heap fuel left = .ok (.root leftRoot))
    (hR : Heap.derefLoop heap fuel right = .ok (.root rightRoot))
    (hCl : heap[leftRoot]? = some (Cell.const symbol))
    (hCr : heap[rightRoot]? = some (Cell.const symbol)) :
    GoodPair heap left right :=
  .inr ⟨fuel, leftRoot, rightRoot, symbol, hL, hR, hCl, hCr⟩

/-- Discharged pairs survive one fresh binding: chains ending away from the
bound cell are framed, chains ending at it are redirected to the binding's
target, and constant roots can never be the bound (variable) cell. -/
theorem GoodPair.persist {σ : LPSignature} {heap heap' : Heap σ}
    {bound target : Addr} {identity : σ.vars}
    (hBound : heap[bound]? = some (Cell.var identity none))
    (hFrame : ∀ other, other ≠ bound → heap'[other]? = heap[other]?)
    (hBound' : heap'[bound]? = some (Cell.var identity (some target)))
    (hTargetLeaf : ∀ fuel,
      Heap.derefLoop heap' (fuel + 1) target = .ok (.root target))
    {left right : Addr} (h : GoodPair heap left right) :
    GoodPair heap' left right := by
  rcases h with ⟨fuel, root, hL, hR⟩ | ⟨fuel, ρl, ρr, symbol, hL, hR, hCl, hCr⟩
  · by_cases hroot : root = bound
    · subst hroot
      exact .inl ⟨fuel + 1, target,
        derefLoop_redirect hBound hFrame hBound' hTargetLeaf fuel left hL,
        derefLoop_redirect hBound hFrame hBound' hTargetLeaf fuel right hR⟩
    · exact .inl ⟨fuel, root,
        derefLoop_frame hBound hFrame fuel left root hL hroot,
        derefLoop_frame hBound hFrame fuel right root hR hroot⟩
  · have hρl : ρl ≠ bound := by
      intro e; subst e; simp [hBound] at hCl
    have hρr : ρr ≠ bound := by
      intro e; subst e; simp [hBound] at hCr
    refine .inr ⟨fuel, ρl, ρr, symbol,
      derefLoop_frame hBound hFrame fuel left ρl hL hρl,
      derefLoop_frame hBound hFrame fuel right ρr hR hρr, ?_, ?_⟩
    · rw [hFrame ρl hρl]; exact hCl
    · rw [hFrame ρr hρr]; exact hCr

/-- Establishment at a fresh binding: the side whose chain ended at the bound
cell redirects to the target; the other side's chain already ended at the
target. -/
theorem GoodPair.of_bind {σ : LPSignature} {heap heap' : Heap σ}
    {bound target : Addr} {identity : σ.vars}
    (hBound : heap[bound]? = some (Cell.var identity none))
    (hFrame : ∀ other, other ≠ bound → heap'[other]? = heap[other]?)
    (hBound' : heap'[bound]? = some (Cell.var identity (some target)))
    (hTargetLeaf : ∀ fuel,
      Heap.derefLoop heap' (fuel + 1) target = .ok (.root target))
    (hTargetNe : target ≠ bound)
    {left right : Addr} {fuel : Nat}
    (hL : Heap.derefLoop heap fuel left = .ok (.root bound))
    (hR : Heap.derefLoop heap fuel right = .ok (.root target)) :
    GoodPair heap' left right :=
  .inl ⟨fuel + 1, target,
    derefLoop_redirect hBound hFrame hBound' hTargetLeaf fuel left hL,
    derefLoop_mono heap' fuel right target
      (derefLoop_frame hBound hFrame fuel right target hR hTargetNe)⟩

/-! ## Run-level helpers -/

theorem runSteps_terminal {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) (result : Terminal σ) :
    runSteps fuel (.terminal result) = .terminal result := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [runSteps, step]

theorem runSteps_succ_none {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {machine : Machine σ} {fuel : Nat}
    (h : step machine = none) :
    runSteps (fuel + 1) machine = machine := by
  simp [runSteps, h]

theorem runSteps_succ_some {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {machine next : Machine σ} {fuel : Nat}
    (h : step machine = some next) :
    runSteps (fuel + 1) machine = runSteps fuel next := by
  simp [runSteps, h]

/-- Finishing a rollback never yields `.success`, at any remaining fuel. -/
theorem rollbackTerminal_no_success {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) (reason : RollbackReason)
    (memory m : Memory σ) :
    runSteps fuel (rollbackTerminal reason memory) ≠
      .terminal (.success m) := by
  cases reason <;> simp [rollbackTerminal, runSteps_terminal]

/-- A machine in rollback phase can never reach `.success`: every rollback
step either stays in rollback or terminates with failure or a runtime
error. -/
theorem rollback_no_success {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (reason : RollbackReason)
      (m : Memory σ),
      c.phase = .rollback reason →
      runSteps fuel (.running c) ≠ .terminal (.success m) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c reason m _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c reason m hphase hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          simp only [step, hphase] at hstep
          split at hstep
          · cases hstep
            exact rollbackTerminal_no_success fuel reason c.memory m hrun
          · split at hstep
            · cases hundo : c.memory.undoLast with
              | ok memory' =>
                  simp only [hundo] at hstep
                  cases hstep
                  exact ih { c with memory := memory', phase := .rollback reason } reason m rfl hrun
              | error e =>
                  simp only [hundo] at hstep
                  cases hstep
                  rw [runSteps_terminal] at hrun
                  simp at hrun
            · cases hstep
              rw [runSteps_terminal] at hrun
              simp at hrun

/-- The cell at a dereference root is never a link. -/
theorem deref_root_cell {σ : LPSignature} (heap : Heap σ) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap fuel address = .ok (.root root) →
      ∀ (identity : σ.vars) (target : Addr),
        heap[root]? ≠ some (Cell.var identity (some target)) := by
  intro fuel
  induction fuel with
  | zero => intro address root h; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h identity target hcell
      cases hc : heap[address]? with
      | none => simp [Heap.derefLoop, hc] at h
      | some cell =>
          cases cell with
          | var identity₂ link =>
              cases link with
              | some target₂ =>
                  simp only [Heap.derefLoop, hc] at h
                  exact ih target₂ root h identity target hcell
              | none =>
                  simp only [Heap.derefLoop, hc] at h
                  obtain rfl : address = root := by simpa using h
                  rw [hc] at hcell
                  simp at hcell
          | const symbol =>
              simp only [Heap.derefLoop, hc] at h
              obtain rfl : address = root := by simpa using h
              rw [hc] at hcell
              simp at hcell
          | app symbol args =>
              simp only [Heap.derefLoop, hc] at h
              obtain rfl : address = root := by simpa using h
              rw [hc] at hcell
              simp at hcell

/-- Function-freeness survives overwriting a cell with a variable cell. -/
theorem FunctionFree.set_var {σ : LPSignature} {heap : Heap σ}
    (ff : FunctionFree heap) {address : Addr} {identity : σ.vars}
    {link : Option Addr} (hlt : address < heap.size) :
    FunctionFree (heap.set address (Cell.var identity link) hlt) := by
  intro other symbol args h
  by_cases he : other = address
  · subst he
    rw [heap_set_get_self heap _ hlt] at h
    simp at h
  · rw [heap_set_get_ne heap _ hlt he] at h
    exact ff other symbol args h

/-! ## The success run invariant -/

/-- `Heap.deref` is `derefLoop` at the standard budget (definitional). -/
theorem deref_root {σ : LPSignature} {heap : Heap σ} {address root : Addr}
    (h : Heap.deref heap address = .ok (.root root)) :
    Heap.derefLoop heap (heap.size + 1) address = .ok (.root root) := h

/-- `beginRollback` never reaches `.success`. -/
theorem beginRollback_no_success {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) (c : Configuration σ)
    (reason : RollbackReason) (m : Memory σ) :
    runSteps fuel (beginRollback c reason) ≠ .terminal (.success m) :=
  rollback_no_success fuel { c with agenda := [], phase := .rollback reason }
    reason m rfl

/-- The three-part conclusion of the run invariant, abbreviated. -/
def InvariantConclusion {σ : LPSignature} (c : Configuration σ)
    (m : Memory σ) : Prop :=
  FunctionFree m.heap ∧
  (∀ x y, GoodPair c.memory.heap x y → GoodPair m.heap x y) ∧
  (∀ pair ∈ c.agenda, GoodPair m.heap pair.1 pair.2)

/-- One successful binding step, discharged uniformly for all four machine
orientations: the run invariant holds across `afterBinding`, and the bound
agenda pair is itself discharged. -/
theorem afterBinding_invariant {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat)
    (ih : ∀ (c' : Configuration σ) (m : Memory σ), c'.phase = .compare →
      FunctionFree c'.memory.heap →
      runSteps fuel (.running c') = .terminal (.success m) →
      InvariantConclusion c' m)
    (c : Configuration σ) (m : Memory σ) (rest : List (Addr × Addr))
    (hphase : c.phase = .compare)
    (hFF : FunctionFree c.memory.heap)
    {varAddr target : Addr} {identity : σ.vars}
    (hBound : c.memory.heap[varAddr]? = some (Cell.var identity none))
    (hTargetCell :
      (∃ tid, c.memory.heap[target]? = some (Cell.var tid none)) ∨
      (∃ ts, c.memory.heap[target]? = some (Cell.const ts)))
    (hTargetNe : target ≠ varAddr)
    {lAddr rAddr : Addr}
    (hL : Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) lAddr =
      .ok (.root varAddr))
    (hR : Heap.derefLoop c.memory.heap (c.memory.heap.size + 1) rAddr =
      .ok (.root target))
    (hrun : runSteps fuel (afterBinding c rest varAddr identity target) =
      .terminal (.success m)) :
    FunctionFree m.heap ∧
    (∀ x y, GoodPair c.memory.heap x y → GoodPair m.heap x y) ∧
    (∀ pair ∈ rest, GoodPair m.heap pair.1 pair.2) ∧
    GoodPair m.heap lAddr rAddr := by
  cases hw : c.memory.write varAddr (Cell.var identity (some target)) with
  | error e =>
      simp only [afterBinding, hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      simp only [afterBinding, hw] at hrun
      obtain ⟨hlt, hheq⟩ := write_ok_heap hw
      have hFrame : ∀ other, other ≠ varAddr →
          memory'.heap[other]? = c.memory.heap[other]? := by
        intro other ho
        rw [hheq]
        exact heap_set_get_ne _ _ hlt ho
      have hBound' :
          memory'.heap[varAddr]? =
            some (Cell.var identity (some target)) := by
        rw [hheq]
        exact heap_set_get_self _ _ hlt
      have hTargetCell' :
          memory'.heap[target]? = c.memory.heap[target]? :=
        hFrame target hTargetNe
      have hTargetLeaf : ∀ f,
          Heap.derefLoop memory'.heap (f + 1) target = .ok (.root target) := by
        rcases hTargetCell with ⟨tid, hc⟩ | ⟨ts, hc⟩
        · exact derefLoop_leaf (hTargetCell'.trans hc) (by intro _ _ h; cases h)
        · exact derefLoop_leaf (hTargetCell'.trans hc) (by intro _ _ h; cases h)
      have hFF' : FunctionFree memory'.heap := by
        rw [hheq]
        exact FunctionFree.set_var hFF hlt
      obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
        ih { c with memory := memory', agenda := rest } m hphase hFF' hrun
      have persistBind : ∀ x y, GoodPair c.memory.heap x y →
          GoodPair memory'.heap x y :=
        fun _ _ g => GoodPair.persist hBound hFrame hBound' hTargetLeaf g
      have established : GoodPair memory'.heap lAddr rAddr :=
        GoodPair.of_bind hBound hFrame hBound' hTargetLeaf hTargetNe hL hR
      exact ⟨ihFF, fun x y g => ihPersist x y (persistBind x y g),
        fun pair hp => ihPairs pair hp, ihPersist _ _ established⟩

/-- **The run invariant**: a successful run from a compare-phase
configuration on a function-free heap (i) keeps the final heap
function-free, (ii) carries every already-discharged `GoodPair` to the final
heap, and (iii) discharges every agenda pair as a `GoodPair` of the final
heap. -/
theorem runSteps_success_invariant {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      FunctionFree c.memory.heap →
      runSteps fuel (.running c) = .terminal (.success m) →
      InvariantConclusion c m := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hFF hrun
      cases hstep : step (Machine.running c) with
      | none =>
          rw [runSteps_succ_none hstep] at hrun
          simp at hrun
      | some next =>
          rw [runSteps_succ_some hstep] at hrun
          cases hagenda : c.agenda with
          | nil =>
              simp only [step, hphase, hagenda] at hstep
              cases hstep
              rw [runSteps_terminal] at hrun
              have hm : c.memory = m := by
                injection hrun with h1
                injection h1
              subst hm
              refine ⟨hFF, fun _ _ g => g, ?_⟩
              intro pair hp
              rw [hagenda] at hp
              simp at hp
          | cons pair rest =>
              obtain ⟨l, r⟩ := pair
              simp only [step, hphase, hagenda] at hstep
              cases hdl : c.memory.heap.deref l with
              | error e =>
                  simp only [hdl] at hstep
                  cases hstep
                  exact absurd hrun (beginRollback_no_success fuel c _ m)
              | ok dresL =>
                  cases dresL with
                  | variableCycle a =>
                      simp only [hdl] at hstep
                      cases hstep
                      exact absurd hrun (beginRollback_no_success fuel c _ m)
                  | root leftRoot =>
                      simp only [hdl] at hstep
                      cases hdr : c.memory.heap.deref r with
                      | error e =>
                          simp only [hdr] at hstep
                          cases hstep
                          exact absurd hrun (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              split at hstep
                              · rename_i heq
                                cases hstep
                                obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
                                  ih { c with agenda := rest, phase := .compare }
                                    m rfl hFF hrun
                                refine ⟨ihFF, ihPersist, ?_⟩
                                intro pair hp
                                rw [hagenda] at hp
                                rcases List.mem_cons.mp hp with hhd | htl
                                · cases hhd
                                  exact ihPersist l r
                                    (GoodPair.of_same_root (deref_root hdl)
                                      (heq ▸ deref_root hdr))
                                · exact ihPairs pair htl
                              · rename_i hne
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases cellL with
                                    | app symbol args =>
                                        exact absurd hcl (hFF leftRoot symbol args)
                                    | var lid linkL =>
                                        cases linkL with
                                        | some t =>
                                            exact absurd hcl
                                              (deref_root_cell c.memory.heap _ l
                                                leftRoot (deref_root hdl) lid t)
                                        | none =>
                                            cases hcr : c.memory.heap[rightRoot]? with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success fuel c _ m)
                                            | some cellR =>
                                                cases cellR with
                                                | app symbol args =>
                                                    exact absurd hcr
                                                      (hFF rightRoot symbol args)
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | some t =>
                                                        exact absurd hcr
                                                          (deref_root_cell
                                                            c.memory.heap _ r
                                                            rightRoot
                                                            (deref_root hdr) rid t)
                                                    | none =>
                                                        simp only [hcl, hcr] at hstep
                                                        split at hstep
                                                        · cases hstep
                                                          obtain ⟨jFF, jPersist,
                                                              jRest, jPair⟩ :=
                                                            afterBinding_invariant
                                                              fuel ih c m rest
                                                              hphase hFF hcr
                                                              (Or.inl ⟨lid, hcl⟩)
                                                              hne
                                                              (deref_root hdr)
                                                              (deref_root hdl) hrun
                                                          refine ⟨jFF, jPersist, ?_⟩
                                                          intro pair hp
                                                          rw [hagenda] at hp
                                                          rcases List.mem_cons.mp hp
                                                            with hhd | htl
                                                          · cases hhd
                                                            exact jPair.symm
                                                          · exact jRest pair htl
                                                        · cases hstep
                                                          obtain ⟨jFF, jPersist,
                                                              jRest, jPair⟩ :=
                                                            afterBinding_invariant
                                                              fuel ih c m rest
                                                              hphase hFF hcl
                                                              (Or.inl ⟨rid, hcr⟩)
                                                              (fun e => hne e.symm)
                                                              (deref_root hdl)
                                                              (deref_root hdr) hrun
                                                          refine ⟨jFF, jPersist, ?_⟩
                                                          intro pair hp
                                                          rw [hagenda] at hp
                                                          rcases List.mem_cons.mp hp
                                                            with hhd | htl
                                                          · cases hhd
                                                            exact jPair
                                                          · exact jRest pair htl
                                                | const symbolR =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    obtain ⟨jFF, jPersist,
                                                        jRest, jPair⟩ :=
                                                      afterBinding_invariant
                                                        fuel ih c m rest
                                                        hphase hFF hcl
                                                        (Or.inr ⟨symbolR, hcr⟩)
                                                        (fun e => hne e.symm)
                                                        (deref_root hdl)
                                                        (deref_root hdr) hrun
                                                    refine ⟨jFF, jPersist, ?_⟩
                                                    intro pair hp
                                                    rw [hagenda] at hp
                                                    rcases List.mem_cons.mp hp
                                                      with hhd | htl
                                                    · cases hhd
                                                      exact jPair
                                                    · exact jRest pair htl
                                    | const symbolL =>
                                        cases hcr : c.memory.heap[rightRoot]? with
                                        | none =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success fuel c _ m)
                                        | some cellR =>
                                            cases cellR with
                                            | app symbol args =>
                                                exact absurd hcr
                                                  (hFF rightRoot symbol args)
                                            | var rid linkR =>
                                                cases linkR with
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell c.memory.heap
                                                        _ r rightRoot
                                                        (deref_root hdr) rid t)
                                                | none =>
                                                    simp only [hcl, hcr] at hstep
                                                    cases hstep
                                                    obtain ⟨jFF, jPersist,
                                                        jRest, jPair⟩ :=
                                                      afterBinding_invariant
                                                        fuel ih c m rest
                                                        hphase hFF hcr
                                                        (Or.inr ⟨symbolL, hcl⟩)
                                                        hne
                                                        (deref_root hdr)
                                                        (deref_root hdl) hrun
                                                    refine ⟨jFF, jPersist, ?_⟩
                                                    intro pair hp
                                                    rw [hagenda] at hp
                                                    rcases List.mem_cons.mp hp
                                                      with hhd | htl
                                                    · cases hhd
                                                      exact jPair.symm
                                                    · exact jRest pair htl
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · rename_i hsym
                                                  cases hstep
                                                  obtain ⟨ihFF, ihPersist, ihPairs⟩ :=
                                                    ih { c with agenda := rest, phase := .compare } m rfl hFF hrun
                                                  refine ⟨ihFF, ihPersist, ?_⟩
                                                  intro pair hp
                                                  rw [hagenda] at hp
                                                  rcases List.mem_cons.mp hp
                                                    with hhd | htl
                                                  · cases hhd
                                                    exact ihPersist l r
                                                      (GoodPair.of_const
                                                        (deref_root hdl)
                                                        (deref_root hdr) hcl
                                                        (hsym ▸ hcr))
                                                  · exact ihPairs pair htl
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)

/-! ## Success soundness -/

/-- **Success soundness of the runtime graph unifier (function-free
fragment)**: if `startMany` reaches `.success`, every entry agenda pair
reads back equally in the final memory — whenever both sides read back
finitely at all, they read back to the *same* canonical `Term`.  Rational
(cyclic) results are excluded honestly by the `.ok` hypotheses rather than
silently. -/
theorem startMany_success_readTerm_eq {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hFF : FunctionFree memory₀.heap)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m)) :
    ∀ pair ∈ agenda, ∀ leftTerm rightTerm : Term σ,
      Heap.readTerm m.heap pair.1 = .ok leftTerm →
      Heap.readTerm m.heap pair.2 = .ok rightTerm →
      leftTerm = rightTerm := by
  obtain ⟨mFF, _, pairs⟩ :=
    runSteps_success_invariant fuel
      { memory := memory₀, agenda := agenda, visited := []
        entryMark := memory₀.trailMark, phase := .compare }
      m rfl hFF hrun
  intro pair hp leftTerm rightTerm hLeft hRight
  rcases pairs pair hp with conv | ⟨f, ρl, ρr, symbol, hL, hR, hCl, hCr⟩
  · exact ConvergedAt.readTerm_eq mFF conv hLeft hRight
  · have hTl : leftTerm = .const symbol := by
      have hBig : readTermFuel m.heap (f + (m.heap.size + 1)) pair.1 =
          .ok leftTerm :=
        readTermFuel_mono_le m.heap (by omega) pair.1 leftTerm hLeft
      have hRoot := readTermFuel_of_root mFF f pair.1 ρl hL (m.heap.size + 1)
      have hConst : readTermFuel m.heap (1 + (m.heap.size + 1)) ρl =
          .ok (.const symbol) := by
        have shift : 1 + (m.heap.size + 1) = (m.heap.size + 1) + 1 := by omega
        rw [shift]
        exact readTermFuel_const m.heap _ ρl symbol hCl
      have : (Except.ok leftTerm : Except ReadbackError (Term σ)) =
          .ok (.const symbol) := by
        rw [← hBig, hRoot, hConst]
      simpa using this
    have hTr : rightTerm = .const symbol := by
      have hBig : readTermFuel m.heap (f + (m.heap.size + 1)) pair.2 =
          .ok rightTerm :=
        readTermFuel_mono_le m.heap (by omega) pair.2 rightTerm hRight
      have hRoot := readTermFuel_of_root mFF f pair.2 ρr hR (m.heap.size + 1)
      have hConst : readTermFuel m.heap (1 + (m.heap.size + 1)) ρr =
          .ok (.const symbol) := by
        have shift : 1 + (m.heap.size + 1) = (m.heap.size + 1) + 1 := by omega
        rw [shift]
        exact readTermFuel_const m.heap _ ρr symbol hCr
      have : (Except.ok rightTerm : Except ReadbackError (Term σ)) =
          .ok (.const symbol) := by
        rw [← hBig, hRoot, hConst]
      simpa using this
    rw [hTl, hTr]

/-! ## Stage 1: exact choice-point restoration

`WritesN.undoN_exact` already reverses pure write sequences.  The query
machine additionally *allocates* between checkpoints; `Extends` certifies an
arbitrary interleaving of successful writes and allocations, and
`Extends.restore_exact` proves `Memory.restore` recovers the checkpointed
memory exactly — the backtracking law every refinement case stands on. -/

/-- History certificate: `after` arises from `before` by successful trailed
writes and allocations, in any interleaving. -/
inductive Extends {σ : LPSignature} : Memory σ → Memory σ → Prop
  | refl (memory : Memory σ) : Extends memory memory
  | write {before middle after : Memory σ} {address : Addr} {cell : Cell σ}
      (history : Extends before middle)
      (step : middle.write address cell = .ok after) :
      Extends before after
  | alloc {before middle after : Memory σ} {address : Addr} {cell : Cell σ}
      (history : Extends before middle)
      (step : middle.allocate cell = .ok (address, after)) :
      Extends before after

/-- Invert a successful `Memory.write` completely. -/
theorem write_ok_inv {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    ∃ hlt : address < memory.heap.size,
      memory' = {
        heap := memory.heap.set address cell hlt
        trail := memory.trail.push { address, previous := memory.heap[address] }
      } := by
  unfold Memory.write at h
  split at h
  · split at h
    · split at h
      · exact ⟨‹_›, by cases h; rfl⟩
      · rcases hfind :
            (Cell.references cell).find?
              (fun target => decide (memory.heap.size ≤ target)) with _ | t <;>
          rw [hfind] at h <;> cases h
    · cases h
  · cases h

/-- Invert a successful `Memory.allocate` completely. -/
theorem allocate_ok_inv {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.allocate cell = .ok (address, memory')) :
    address = memory.heap.size ∧
      memory' = { memory with heap := memory.heap.push cell } := by
  unfold Memory.allocate at h
  split at h
  · split at h
    · refine ⟨?_, ?_⟩ <;> cases h <;> rfl
    · rcases hfind :
          (Cell.references cell).find?
            (fun target => decide (memory.heap.size ≤ target)) with _ | t <;>
        rw [hfind] at h <;> cases h
  · cases h

theorem Extends.heap_le {σ : LPSignature} {before after : Memory σ}
    (h : Extends before after) : before.heap.size ≤ after.heap.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | write _ step ih =>
      obtain ⟨hlt, rfl⟩ := write_ok_inv step
      simpa using ih
  | alloc _ step ih =>
      obtain ⟨_, rfl⟩ := allocate_ok_inv step
      simp only [Array.size_push]
      omega

theorem Extends.trail_le {σ : LPSignature} {before after : Memory σ}
    (h : Extends before after) : before.trail.size ≤ after.trail.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | write _ step ih =>
      obtain ⟨hlt, rfl⟩ := write_ok_inv step
      simp only [Array.size_push]
      omega
  | alloc _ step ih =>
      obtain ⟨_, rfl⟩ := allocate_ok_inv step
      simpa using ih

/-- `Memory.unwindLoop` commutes with pushing one fresh (untrailed) heap cell. -/
theorem unwindLoop_push {σ : LPSignature} :
    ∀ (steps : Nat) (memory unwound : Memory σ) (cell : Cell σ),
      Memory.unwindLoop steps memory = .ok unwound →
      Memory.unwindLoop steps
          { heap := memory.heap.push cell, trail := memory.trail } =
        .ok { heap := unwound.heap.push cell, trail := unwound.trail } := by
  intro steps
  induction steps with
  | zero =>
      intro memory unwound cell h
      cases h
      rfl
  | succ steps ih =>
      intro memory unwound cell h
      cases hback : memory.trail.back? with
      | none => simp [Memory.unwindLoop, hback] at h
      | some entry =>
          by_cases hlt : entry.address < memory.heap.size
          · simp only [Memory.unwindLoop, hback, dif_pos hlt] at h
            simp only [Memory.unwindLoop, hback]
            have hlt' : entry.address < (memory.heap.push cell).size := by
              simp only [Array.size_push]
              exact Nat.lt_succ_of_lt hlt
            rw [dif_pos hlt']
            have hcomm :
                (memory.heap.push cell).set entry.address entry.previous hlt' =
                  (memory.heap.set entry.address entry.previous hlt).push
                    cell := by
              apply Array.ext
              · simp
              · intro i hi₁ hi₂
                by_cases hie : i = entry.address
                · subst hie
                  simp [Array.getElem_push, hlt]
                · simp [Array.getElem_push, Array.getElem_set, Ne.symm hie]
            rw [hcomm]
            exact ih _ _ cell h
          · simp [Memory.unwindLoop, hback, dif_neg hlt] at h

/-- Unwinding back to a checkpointed trail size succeeds along any `Extends`
history, restores the checkpointed trail, preserves heap size, and restores
every checkpointed cell. -/
theorem Extends.unwind_exact {σ : LPSignature} {before after : Memory σ}
    (h : Extends before after) :
    ∃ unwound : Memory σ,
      after.unwindTrail before.trail.size = .ok unwound ∧
      unwound.trail = before.trail ∧
      unwound.heap.size = after.heap.size ∧
      ∀ address, address < before.heap.size →
        unwound.heap[address]? = before.heap[address]? := by
  induction h with
  | refl =>
      refine ⟨before, ?_, rfl, rfl, fun _ _ => rfl⟩
      unfold Memory.unwindTrail
      rw [dif_pos (Nat.le_refl _)]
      simp [Memory.unwindLoop]
  | write history step ih =>
      rename_i middle after address cell
      obtain ⟨unwound, hunwind, htrail, hsize, hcells⟩ := ih
      obtain ⟨hlt, rfl⟩ := write_ok_inv step
      refine ⟨unwound, ?_, htrail, by simpa using hsize, hcells⟩
      have hle := history.trail_le
      unfold Memory.unwindTrail at hunwind ⊢
      rw [dif_pos hle] at hunwind
      rw [dif_pos (by simp only [Array.size_push]; omega)]
      have hcount :
          (middle.trail.push
              { address := address,
                previous := middle.heap[address] }).size -
            before.trail.size =
          (middle.trail.size - before.trail.size) + 1 := by
        simp only [Array.size_push]
        omega
      rw [hcount]
      simp only [Memory.unwindLoop, Array.back?_push]
      rw [dif_pos (show address < (middle.heap.set address cell hlt).size by
        simpa using hlt)]
      have hundo :
          (middle.heap.set address cell hlt).set address middle.heap[address]
              (by simpa using hlt) = middle.heap := by
        apply Array.ext
        · simp
        · intro i hi₁ hi₂
          by_cases hie : i = address
          · subst hie
            simp
          · simp
      simp only [hundo, Array.pop_push]
      exact hunwind
  | alloc history step ih =>
      rename_i middle after address cell
      obtain ⟨unwound, hunwind, htrail, hsize, hcells⟩ := ih
      obtain ⟨rfl, rfl⟩ := allocate_ok_inv step
      have hle := history.trail_le
      unfold Memory.unwindTrail at hunwind ⊢
      rw [dif_pos hle] at hunwind
      refine ⟨{ heap := unwound.heap.push cell, trail := unwound.trail },
        ?_, htrail, ?_, ?_⟩
      · rw [dif_pos (show before.trail.size ≤
            ({ middle with heap := middle.heap.push cell } :
              Memory σ).trail.size from hle)]
        exact unwindLoop_push _ middle unwound cell hunwind
      · simp only [Array.size_push]
        omega
      · intro a ha
        have hau : a < unwound.heap.size := by
          have := history.heap_le
          omega
        have hne : a ≠ unwound.heap.size := by omega
        simp only [Array.getElem?_push, hne, if_false]
        exact hcells a ha

/-- **Exact restoration**: along any write/allocate history, `restore`
recovers the checkpointed memory exactly, provided the checkpointed heap
passes the runtime's well-formedness gates. -/
theorem Extends.restore_exact {σ : LPSignature} {before after : Memory σ}
    (h : Extends before after)
    (hWF : before.heap.checkWellFormed = true)
    (hWS : before.heap.checkWellShaped = true) :
    after.restore before.checkpoint = .ok before := by
  obtain ⟨unwound, hunwind, htrail, hsize, hcells⟩ := h.unwind_exact
  have hheap : unwound.heap.extract 0 before.heap.size = before.heap := by
    apply Array.ext
    · simp only [Array.size_extract]
      have := h.heap_le
      omega
    · intro i hi₁ hi₂
      have hib : i < before.heap.size := hi₂
      have hiu : i < unwound.heap.size := by
        have := h.heap_le
        omega
      rw [Array.getElem_extract]
      have hcell := hcells i hib
      rw [Array.getElem?_eq_getElem (by simpa using hiu),
        Array.getElem?_eq_getElem hib] at hcell
      simpa using hcell
  unfold Memory.restore
  simp only [Memory.checkpoint]
  rw [if_pos h.heap_le, hunwind]
  simp only [hheap, htrail, hWF, hWS, if_true]

/-! ## Stage 2: the canonical answer substitution

The refinement theorem's substitution is not chosen — it is *read off the
answer heap*.  Under identity-injectivity (at most one cell per variable
identity, a consequence of the scope discipline) the denoted substitution is
well-defined and idempotent, which is what lets the SLD judgment's answer
compositions telescope to it. -/

/-- At most one heap cell carries each variable identity. -/
def IdentityInjective {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (a b : Addr) (identity : σ.vars) (la lb : Option Addr),
    heap[a]? = some (Cell.var identity la) →
    heap[b]? = some (Cell.var identity lb) → a = b

attribute [local instance] Classical.propDecidable

/-- The cell carrying one variable identity, when it exists. -/
noncomputable def cellOf {σ : LPSignature} (heap : Heap σ) (v : σ.vars) :
    Option Addr :=
  if h : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var v link) then
    some h.choose
  else none

/-- Every listed variable has a cell with *finite* readback.  This is the
interface guard for `heapSubst`: outside a readable support, its fallback
below silently treats a variable as unbound, which would misrepresent a
rational (cyclic) binding as freedom.  Theorems must either hypothesize
readability of every relevant variable or discharge it (the function-free
fragment proves it outright). -/
def ReadableOn {σ : LPSignature} (heap : Heap σ) (support : List σ.vars) :
    Prop :=
  ∀ v ∈ support, ∃ address term,
    cellOf heap v = some address ∧
    Heap.readTerm heap address = .ok term

/-- The **finite heap projection**: each identity reads back its cell;
identities without a cell, or whose cell has no finite readback (a rational
cycle), fall back to themselves.  On a `ReadableOn` support — automatic in
the function-free fragment — this is the canonical answer substitution; the
fallback is never semantically meaningful and consumers must not rely on
it. -/
noncomputable def heapSubst {σ : LPSignature} (heap : Heap σ) : Subst σ :=
  fun v =>
    match cellOf heap v with
    | none => .var v
    | some address =>
        match Heap.readTerm heap address with
        | .ok term => term
        | .error _ => .var v

/-- List companion for `readTermFuel_freeVar_unbound`. -/
theorem readListFuel_freeVar_unbound {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} {fuel : Nat}
    (termCase : ∀ address term, readTermFuel heap fuel address = .ok term →
      ∀ w ∈ term.freeVars, ∃ b : Addr, heap[b]? = some (Cell.var w none)) :
    ∀ (addresses : List Addr) (terms : List (Term σ)),
      readListFuel heap fuel addresses = .ok terms →
      ∀ c ∈ terms, ∀ w ∈ c.freeVars,
        ∃ b : Addr, heap[b]? = some (Cell.var w none) := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms h c hc _ _
      have : ([] : List (Term σ)) = terms := by simpa [readListFuel] using h
      subst this
      simp at hc
  | cons head tailA tailIh =>
      intro terms h c hc w hw
      simp only [readListFuel, Bind.bind, Except.bind] at h
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; simp at h
      | ok headTerm =>
          rw [hHead] at h
          cases hTail : readListFuel heap fuel tailA with
          | error e => rw [hTail] at h; simp at h
          | ok tailTerms =>
              rw [hTail] at h
              have : headTerm :: tailTerms = terms := by simpa using h
              subst this
              rcases List.mem_cons.mp hc with rfl | hc'
              · exact termCase head c hHead w hw
              · exact tailIh tailTerms hTail c hc' w hw

/-- Every free variable of a finite readback names an *unbound* cell. -/
theorem readTermFuel_freeVar_unbound {σ : LPSignature}
    [DecidableEq σ.vars] (heap : Heap σ) :
    ∀ (fuel : Nat) (address : Addr) (term : Term σ),
      readTermFuel heap fuel address = .ok term →
      ∀ w ∈ term.freeVars, ∃ b : Addr, heap[b]? = some (Cell.var w none) := by
  intro fuel
  induction fuel with
  | zero => intro address term h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address term h w hw
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
                  have : Term.var identity = term := by simpa using h
                  subst this
                  have : w = identity := by
                    simpa [Term.freeVars] using hw
                  subst this
                  exact ⟨address, hcell⟩
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  exact ih target term h w hw
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              have : Term.const symbol = term := by simpa using h
              subst this
              simp [Term.freeVars] at hw
          | app symbol args =>
              rw [readTermFuel_app heap fuel address symbol args hcell] at h
              simp only [Bind.bind, Except.bind] at h
              cases hArgs : readListFuel heap fuel args.toList with
              | error e => rw [hArgs] at h; simp at h
              | ok children =>
                  simp only [hArgs] at h
                  by_cases hLength :
                      children.length = σ.functionArity symbol
                  case neg =>
                    rw [dif_neg hLength] at h
                    exact absurd h (by simp)
                  case pos =>
                    rw [dif_pos hLength] at h
                    have hterm :
                        Term.app symbol (fun index =>
                          children.get (Fin.cast hLength.symm index)) =
                          term := by
                      simpa using h
                    subst hterm
                    simp only [Term.freeVars, Finset.mem_biUnion,
                      Finset.mem_univ, true_and] at hw
                    obtain ⟨i, hi⟩ := hw
                    exact readListFuel_freeVar_unbound
                      (fun a t ht => ih a t ht) args.toList children hArgs
                      _ (children.get_mem _) w hi

/-- Under injectivity, `cellOf` finds exactly the unbound cell. -/
theorem cellOf_unbound {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    (hb : heap[b]? = some (Cell.var w none)) :
    cellOf heap w = some b := by
  unfold cellOf
  have hex : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var w link) :=
    ⟨b, none, hb⟩
  rw [dif_pos hex]
  obtain ⟨link, hl⟩ := hex.choose_spec
  exact congrArg some (inj _ b w link none hl hb)

/-- An unbound identity denotes itself. -/
theorem heapSubst_unbound {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    (hb : heap[b]? = some (Cell.var w none)) :
    heapSubst heap w = .var w := by
  have hread : Heap.readTerm heap b = .ok (Term.var w) :=
    readTermFuel_unbound heap heap.size b w hb
  simp [heapSubst, cellOf_unbound inj hb, hread]

/-- A substitution fixing every free variable fixes the term. -/
theorem applyTerm_eq_self_of_freeVars {σ : LPSignature} [DecidableEq σ.vars]
    {θ : Subst σ} :
    ∀ {t : Term σ}, (∀ w ∈ t.freeVars, θ w = .var w) →
      θ.applyTerm t = t := by
  intro t
  induction t with
  | var v =>
      intro h
      simpa [Subst.applyTerm] using h v (by simp [Term.freeVars])
  | const c => intro _; rfl
  | app f ts ih =>
      intro h
      simp only [Subst.applyTerm]
      congr 1
      funext i
      exact ih i (fun w hw => h w (by
        simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ,
          true_and]
        exact ⟨i, hw⟩))

/-- Pointwise idempotence of the denoted substitution. -/
theorem heapSubst_applyTerm_self {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) (v : σ.vars) :
    (heapSubst heap).applyTerm (heapSubst heap v) = heapSubst heap v := by
  have hval : heapSubst heap v = .var v ∨
      ∃ a t, Heap.readTerm heap a = .ok t ∧ heapSubst heap v = t := by
    cases hc : cellOf heap v with
    | none => exact .inl (by simp [heapSubst, hc])
    | some a =>
        cases hr : Heap.readTerm heap a with
        | ok term => exact .inr ⟨a, term, hr, by simp [heapSubst, hc, hr]⟩
        | error e => exact .inl (by simp [heapSubst, hc, hr])
  rcases hval with h | ⟨a, t, hrt, h⟩
  · rw [h]
    simp only [Subst.applyTerm]
    exact h
  · rw [h]
    apply applyTerm_eq_self_of_freeVars
    intro w hw
    obtain ⟨b, hb⟩ :=
      readTermFuel_freeVar_unbound heap (heap.size + 1) a t hrt w hw
    exact heapSubst_unbound inj hb

/-- **Idempotence**: the denoted substitution absorbs itself under
composition — the law that lets SLD answer compositions telescope. -/
theorem heapSubst_idem {σ : LPSignature} [DecidableEq σ.vars]
    {heap : Heap σ} (inj : IdentityInjective heap) :
    heapSubst heap ∘ₛ heapSubst heap = heapSubst heap := by
  funext v
  simpa [Subst.comp] using heapSubst_applyTerm_self inj v

/-! ## Stage 3a: readback under append-only extension, and atom readback -/

/-- List companion for `readTermFuel_extend`. -/
theorem readListFuel_extend {σ : LPSignature} {heap heap' : Heap σ}
    {fuel : Nat}
    (termCase : ∀ address, address < heap.size → ∀ t,
      readTermFuel heap fuel address = .ok t →
      readTermFuel heap' fuel address = .ok t) :
    ∀ (addresses : List Addr), (∀ a ∈ addresses, a < heap.size) →
      ∀ (terms : List (Term σ)),
        readListFuel heap fuel addresses = .ok terms →
        readListFuel heap' fuel addresses = .ok terms := by
  intro addresses
  induction addresses with
  | nil => intro _ terms h; simpa [readListFuel] using h
  | cons head tailA tailIh =>
      intro hbound terms h
      simp only [readListFuel, Bind.bind, Except.bind] at h ⊢
      cases hHead : readTermFuel heap fuel head with
      | error e => rw [hHead] at h; simp at h
      | ok headTerm =>
          rw [hHead] at h
          rw [termCase head (hbound head (by simp)) headTerm hHead]
          cases hTail : readListFuel heap fuel tailA with
          | error e => rw [hTail] at h; simp at h
          | ok tailTerms =>
              rw [hTail] at h
              rw [tailIh (fun a ha => hbound a (by simp [ha])) tailTerms hTail]
              exact h

/-- Readback is stable under append-only extension of a *well-formed* heap:
the prefix is reference-closed, so chains never leave it. -/
theorem readTermFuel_extend {σ : LPSignature} {heap heap' : Heap σ}
    (hwf : Heap.WellFormed heap)
    (hpre : ∀ i, i < heap.size → heap'[i]? = heap[i]?) :
    ∀ (fuel : Nat) (address : Addr), address < heap.size →
      ∀ t, readTermFuel heap fuel address = .ok t →
        readTermFuel heap' fuel address = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro address _ t h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address haddr t h
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          have hcell' : heap'[address]? = some cell := by
            rw [hpre address haddr]; exact hcell
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell] at h
                  rw [readTermFuel_unbound heap' fuel address identity hcell']
                  exact h
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  rw [readTermFuel_link heap' fuel address target identity
                    hcell']
                  have htarget : target < heap.size :=
                    hwf address _ hcell target (by simp [Cell.references])
                  exact ih target htarget t h
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              rw [readTermFuel_const heap' fuel address symbol hcell']
              exact h
          | app symbol args =>
              rw [readTermFuel_app heap fuel address symbol args hcell] at h
              rw [readTermFuel_app heap' fuel address symbol args hcell']
              simp only [Bind.bind, Except.bind] at h ⊢
              cases hArgs : readListFuel heap fuel args.toList with
              | error e => rw [hArgs] at h; simp at h
              | ok children =>
                  rw [hArgs] at h
                  have hbound : ∀ a ∈ args.toList, a < heap.size := by
                    intro a ha
                    exact hwf address _ hcell a (by
                      simpa [Cell.references] using ha)
                  rw [readListFuel_extend (fun a ha => ih a ha) args.toList
                    hbound children hArgs]
                  exact h

/-- Read one runtime atom back into a canonical LP atom. -/
def readAtom {σ : LPSignature} (heap : Heap σ)
    (atom : RuntimeMaterialize.RuntimeAtom σ) :
    Except ReadbackError (Atom σ) := do
  let children ← readListFuel heap (heap.size + 1) atom.args.toList
  if h : children.length = σ.relationArity atom.symbol then
    .ok ⟨atom.symbol, fun index => children.get (Fin.cast h.symm index)⟩
  else
    .error .arityMismatch

/-! ## Stage 3b: builder mechanics -/

open RuntimeMaterialize in
/-- All variable-map entries point at unbound cells carrying their identity. -/
def VarMapCells {σ : LPSignature} (state : BuilderState σ) : Prop :=
  ∀ pair ∈ state.varMap,
    state.heap[pair.2]? = some (Cell.var pair.1 none)

@[simp] theorem BuilderM.run_bind {σ : LPSignature} {α β : Type _}
    (action : RuntimeMaterialize.BuilderM σ α)
    (next : α → RuntimeMaterialize.BuilderM σ β)
    (state : RuntimeMaterialize.BuilderState σ) :
    (action >>= next).run state =
      match action.run state with
      | .error error => .error error
      | .ok (value, nextState) => (next value).run nextState := rfl

@[simp] theorem BuilderM.run_pure {σ : LPSignature} {α : Type _}
    (value : α) (state : RuntimeMaterialize.BuilderState σ) :
    (pure value : RuntimeMaterialize.BuilderM σ α).run state =
      .ok (value, state) := rfl

open RuntimeMaterialize in
/-- Builder-level allocation, inverted. -/
theorem allocate_run_spec {σ : LPSignature} {cell : Cell σ}
    {s₀ s₁ : BuilderState σ} {address : Addr}
    (h : (RuntimeMaterialize.allocate cell).run s₀ = .ok (address, s₁)) :
    address = s₀.heap.size ∧ s₁.heap = s₀.heap.push cell ∧
      s₁.varMap = s₀.varMap := by
  simp only [RuntimeMaterialize.allocate, BuilderM.run_bind,
    BuilderM.get, BuilderM.set, BuilderM.throw] at h
  cases halloc : Memory.allocate { heap := s₀.heap, trail := #[] } cell with
  | error e => rw [halloc] at h; cases h
  | ok pair =>
      obtain ⟨addr₀, memory₀⟩ := pair
      rw [halloc] at h
      obtain ⟨haddr, hmem⟩ := allocate_ok_inv halloc
      cases h
      refine ⟨haddr, ?_, rfl⟩
      rw [hmem]

/-- Pointwise readbacks assemble into a list readback. -/
theorem readListFuel_of_pointwise {σ : LPSignature} {heap : Heap σ}
    {fuel : Nat} :
    ∀ (addresses : List Addr) (terms : List (Term σ)),
      addresses.length = terms.length →
      (∀ k (hk : k < addresses.length) (hk' : k < terms.length),
        readTermFuel heap fuel addresses[k] = .ok terms[k]) →
      readListFuel heap fuel addresses = .ok terms := by
  intro addresses
  induction addresses with
  | nil =>
      intro terms hlen _
      cases terms with
      | nil => simp [readListFuel]
      | cons _ _ => simp at hlen
  | cons head tailA tailIh =>
      intro terms hlen hpoint
      cases terms with
      | nil => simp at hlen
      | cons headTerm tailTerms =>
          simp only [readListFuel, Bind.bind, Except.bind]
          have hhead := hpoint 0 (by simp) (by simp)
          simp only [List.getElem_cons_zero] at hhead
          rw [hhead]
          have htail := tailIh tailTerms (by simpa using hlen)
            (fun k hk hk' => by
              have := hpoint (k + 1) (by simpa using hk)
                (by simpa using hk')
              simpa using this)
          rw [htail]

open RuntimeMaterialize

/-- A cell lookup pins the address in bounds. -/
theorem lt_of_getElem?_some {σ : LPSignature} {heap : Heap σ} {a : Addr}
    {cell : Cell σ} (h : heap[a]? = some cell) : a < heap.size := by
  cases Nat.lt_or_ge a heap.size with
  | inl hlt => exact hlt
  | inr hge => rw [Array.getElem?_eq_none hge] at h; cases h

theorem getElem?_push_lt {σ : LPSignature} (heap : Heap σ) (cell : Cell σ)
    {a : Addr} (ha : a < heap.size) :
    (heap.push cell)[a]? = heap[a]? := by
  have hne : a ≠ heap.size := Nat.ne_of_lt ha
  simp [Array.getElem?_push, hne]

/-- What one builder step must preserve. -/
structure BuildOk {σ : LPSignature} (s₀ s₁ : BuilderState σ) : Prop where
  prefixEq : ∀ i, i < s₀.heap.size → s₁.heap[i]? = s₀.heap[i]?
  sizeLe : s₀.heap.size ≤ s₁.heap.size
  wf : Heap.WellFormed s₁.heap
  cells : VarMapCells s₁
  varMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap

theorem BuildOk.rfl {σ : LPSignature} {s : BuilderState σ}
    (hwf : Heap.WellFormed s.heap) (hcells : VarMapCells s) : BuildOk s s :=
  ⟨fun _ _ => _root_.rfl, Nat.le_refl _, hwf, hcells, fun _ hp => hp⟩

theorem BuildOk.trans {σ : LPSignature} {s₀ s₁ s₂ : BuilderState σ}
    (a : BuildOk s₀ s₁) (b : BuildOk s₁ s₂) : BuildOk s₀ s₂ where
  prefixEq i hi := by
    rw [b.prefixEq i (Nat.lt_of_lt_of_le hi a.sizeLe)]
    exact a.prefixEq i hi
  sizeLe := a.sizeLe.trans b.sizeLe
  wf := b.wf
  cells := b.cells
  varMono pair hp := b.varMono pair (a.varMono pair hp)

/-- Pushing a reference-closed cell is a valid builder step. -/
theorem BuildOk.push {σ : LPSignature} {s : BuilderState σ} {cell : Cell σ}
    (hwf : Heap.WellFormed s.heap) (hcells : VarMapCells s)
    (hrefs : ∀ target ∈ Cell.references cell, target < s.heap.size) :
    BuildOk s { heap := s.heap.push cell, varMap := s.varMap } where
  prefixEq i hi := getElem?_push_lt s.heap cell hi
  sizeLe := by
    simp only [Array.size_push]
    exact Nat.le_succ _
  wf := by
    intro address cell' hcell' target ht
    simp only [Array.size_push]
    by_cases haddr : address = s.heap.size
    · subst haddr
      have hpe : (s.heap.push cell)[s.heap.size]? = some cell := by
        simp
      rw [hpe] at hcell'
      cases hcell'
      exact Nat.lt_succ_of_lt (hrefs target ht)
    · have hlt : address < s.heap.size := by
        have hlt' := lt_of_getElem?_some hcell'
        simp only [Array.size_push] at hlt'
        exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt') haddr
      rw [getElem?_push_lt s.heap cell hlt] at hcell'
      exact Nat.lt_succ_of_lt (hwf address cell' hcell' target ht)
  cells pair hp := by
    have hcell := hcells pair hp
    have hlt := lt_of_getElem?_some hcell
    rw [getElem?_push_lt s.heap cell hlt]
    exact hcell
  varMono _ hp := hp

/-- A successful association-list lookup names an entry. -/
theorem mem_of_list_lookup {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ {varMap : List (σ.vars × Addr)} {identity : σ.vars} {address : Addr},
      List.lookup identity varMap = some address →
      (identity, address) ∈ varMap := by
  intro varMap
  induction varMap with
  | nil => intro _ _ h; simp [List.lookup] at h
  | cons head tailM ih =>
      intro identity address h
      obtain ⟨key, value⟩ := head
      by_cases he : identity = key
      · subst he
        simp [List.lookup] at h
        subst h
        exact List.mem_cons_self ..
      · have hne : (identity == key) = false := by
          simpa using he
        simp [List.lookup, hne] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- The specification one materialized term satisfies. -/
def TermSpec {σ : LPSignature} [DecidableEq σ.vars] (t : Term σ) : Prop :=
  ∀ {s₀ s₁ : BuilderState σ} {address : Addr},
    (materializeTermAux t).run s₀ = .ok (address, s₁) →
    Heap.WellFormed s₀.heap → VarMapCells s₀ →
    BuildOk s₀ s₁ ∧ address < s₁.heap.size ∧
      readTermFuel s₁.heap (s₁.heap.size + 1) address = .ok t

/-- Run-level unfolding of `List.mapM.loop` for the builder monad, proved
directly so no `LawfulMonad` instance is needed. -/
theorem run_mapM_loop {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) :
    ∀ (as : List α) (acc : List β) (s : BuilderState σ),
      (List.mapM.loop f as acc).run s =
        match (as.mapM f).run s with
        | .error e => .error e
        | .ok (bs, s') => .ok (acc.reverse ++ bs, s') := by
  intro as
  induction as with
  | nil =>
      intro acc s
      simp [List.mapM, List.mapM.loop, BuilderM.run_pure]
  | cons head tailA ih =>
      intro acc s
      show (List.mapM.loop f (head :: tailA) acc).run s = _
      simp only [List.mapM.loop, BuilderM.run_bind]
      cases hHead : (f head).run s with
      | error e =>
          simp only [List.mapM, List.mapM.loop, BuilderM.run_bind, hHead]
      | ok pair =>
          obtain ⟨b, s'⟩ := pair
          simp only [List.mapM, List.mapM.loop, BuilderM.run_bind, hHead]
          rw [ih (b :: acc) s', ih [b] s']
          cases hTail : (tailA.mapM f).run s' with
          | error e => rfl
          | ok pair' =>
              obtain ⟨bs, s''⟩ := pair'
              simp

theorem run_mapM_nil {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) (s : BuilderState σ) :
    (([] : List α).mapM f).run s = .ok (([] : List β), s) := by
  simp [List.mapM, List.mapM.loop, BuilderM.run_pure]

theorem run_mapM_cons {σ : LPSignature} {α β : Type _}
    (f : α → RuntimeMaterialize.BuilderM σ β) (a : α) (as : List α)
    (s : BuilderState σ) :
    ((a :: as).mapM f).run s =
      match (f a).run s with
      | .error e => .error e
      | .ok (b, s') =>
          match (as.mapM f).run s' with
          | .error e => .error e
          | .ok (bs, s'') => .ok (b :: bs, s'') := by
  show (List.mapM.loop f (a :: as) []).run s = _
  simp only [List.mapM.loop, BuilderM.run_bind]
  cases hHead : (f a).run s with
  | error e => rfl
  | ok pair =>
      obtain ⟨b, s'⟩ := pair
      dsimp only
      rw [run_mapM_loop f as [b] s']
      cases hTail : (as.mapM f).run s' with
      | error e => rfl
      | ok pair' =>
          obtain ⟨bs, s''⟩ := pair'
          simp

/-- mapM companion: element specs assemble into a run over an index list. -/
theorem materializeMapM_spec {σ : LPSignature} [DecidableEq σ.vars]
    {ι : Type _} (f : ι → Term σ) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, TermSpec (f i)) →
      ∀ {s₀ s₁ : BuilderState σ} {addresses : List Addr},
        (indices.mapM fun i => materializeTermAux (f i)).run s₀ =
          .ok (addresses, s₁) →
        Heap.WellFormed s₀.heap → VarMapCells s₀ →
        BuildOk s₀ s₁ ∧ addresses.length = indices.length ∧
          ∀ k (hk : k < addresses.length) (hk' : k < indices.length),
            addresses[k] < s₁.heap.size ∧
            readTermFuel s₁.heap (s₁.heap.size + 1) addresses[k] =
              .ok (f indices[k]) := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ addresses h hwf hcells
      rw [run_mapM_nil] at h
      cases h
      exact ⟨BuildOk.rfl hwf hcells, _root_.rfl,
        fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tailI tailIh =>
      intro elemSpec s₀ s₁ addresses h hwf hcells
      rw [run_mapM_cons] at h
      cases hHead : (materializeTermAux (f head)).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headAddr, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM fun i => materializeTermAux (f i)).run
              sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailAddrs, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              obtain ⟨bHead, hHeadLt, hHeadRead⟩ :=
                elemSpec head (by simp) hHead hwf hcells
              obtain ⟨bTail, hLen, hPoint⟩ :=
                tailIh (fun i hi => elemSpec i (by simp [hi]))
                  hTail bHead.wf bHead.cells
              refine ⟨bHead.trans bTail,
                congrArg (fun n => n + 1) hLen, ?_⟩
              intro k hk hk'
              cases k with
              | zero =>
                  refine ⟨Nat.lt_of_lt_of_le hHeadLt bTail.sizeLe, ?_⟩
                  simp only [List.getElem_cons_zero]
                  have hExt := readTermFuel_extend bHead.wf bTail.prefixEq
                    (sMid.heap.size + 1) headAddr hHeadLt _ hHeadRead
                  exact readTermFuel_mono_le _
                    (Nat.succ_le_succ bTail.sizeLe) headAddr _ hExt
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- **Materialization round-trip** (term level): a materialized term reads
back verbatim, the heap grows append-only and stays well-formed, and the
variable map stays coherent. -/
theorem materializeTermAux_spec {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ t : Term σ, TermSpec t := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact ⟨BuildOk.rfl hwf hcells,
            lt_of_getElem?_some (hcells _ (mem_of_list_lookup hlook)),
            readTermFuel_unbound _ _ _ _
              (hcells _ (mem_of_list_lookup hlook))⟩
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              subst haddr
              have hself : sMid.heap[s₀.heap.size]? =
                  some (Cell.var identity none) := by
                rw [hheap]
                simp
              have bPush : BuildOk s₀
                  { heap := sMid.heap, varMap := s₀.varMap } := by
                have := BuildOk.push (cell := Cell.var identity none)
                  hwf hcells (by simp [Cell.references])
                rwa [← hheap] at this
              have hCells : VarMapCells
                  ({ heap := sMid.heap,
                     varMap := (identity, s₀.heap.size) :: sMid.varMap } :
                    BuilderState σ) := by
                intro pair hp
                rcases List.mem_cons.mp hp with hhd | hp'
                · rw [hhd]
                  exact hself
                · rw [hvar] at hp'
                  exact bPush.cells pair hp'
              have hVarMono : ∀ pair ∈ s₀.varMap,
                  pair ∈ (identity, s₀.heap.size) :: sMid.varMap := by
                intro pair hp
                rw [hvar]
                exact List.mem_cons_of_mem _ hp
              refine ⟨⟨bPush.prefixEq, bPush.sizeLe, bPush.wf, hCells,
                hVarMono⟩, ?_, ?_⟩
              · rw [hheap]
                simp only [Array.size_push]
                exact Nat.lt_succ_self _
              · exact readTermFuel_unbound sMid.heap sMid.heap.size
                  s₀.heap.size identity hself
  | const symbol =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux] at h
      obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec h
      subst haddr
      have hself : s₁.heap[s₀.heap.size]? = some (Cell.const symbol) := by
        rw [hheap]
        simp
      have bPush : BuildOk s₀ { heap := s₁.heap, varMap := s₀.varMap } := by
        have := BuildOk.push (cell := Cell.const symbol) hwf hcells
          (by simp [Cell.references])
        rwa [← hheap] at this
      have hCells : VarMapCells s₁ := by
        intro pair hp
        rw [hvar] at hp
        exact bPush.cells pair hp
      have hVarMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap := by
        intro pair hp
        rw [hvar]
        exact bPush.varMono pair hp
      refine ⟨⟨bPush.prefixEq, bPush.sizeLe, bPush.wf, hCells, hVarMono⟩,
        ?_, ?_⟩
      · rw [hheap]
        simp only [Array.size_push]
        exact Nat.lt_succ_self _
      · exact readTermFuel_const s₁.heap s₁.heap.size s₀.heap.size symbol hself
  | app symbol args ih =>
      intro s₀ s₁ address h hwf hcells
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          obtain ⟨bMap, hLen, hPoint⟩ :=
            materializeMapM_spec (fun index => args index)
              (List.finRange (σ.functionArity symbol))
              (fun i _ => ih i) hMap hwf hcells
          obtain ⟨haddr, hheap, hvar⟩ := allocate_run_spec h
          subst haddr
          have hLenArity : childAddrs.length = σ.functionArity symbol := by
            simpa [List.length_finRange] using hLen
          have hself : s₁.heap[sMid.heap.size]? =
              some (Cell.app symbol childAddrs.toArray) := by
            rw [hheap]
            simp
          have hrefs : ∀ target ∈ Cell.references
              (Cell.app symbol childAddrs.toArray),
              target < sMid.heap.size := by
            intro target ht
            simp only [Cell.references] at ht
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
            exact (hPoint k hk (by omega)).1
          have bPush : BuildOk sMid
              { heap := s₁.heap, varMap := sMid.varMap } := by
            have := BuildOk.push (cell := Cell.app symbol childAddrs.toArray)
              bMap.wf bMap.cells hrefs
            rwa [← hheap] at this
          have bAll : BuildOk s₀ { heap := s₁.heap, varMap := sMid.varMap } :=
            bMap.trans bPush
          have hCells : VarMapCells s₁ := by
            intro pair hp
            rw [hvar] at hp
            exact bAll.cells pair hp
          have hVarMono : ∀ pair ∈ s₀.varMap, pair ∈ s₁.varMap := by
            intro pair hp
            rw [hvar]
            exact bAll.varMono pair hp
          have hsize : s₁.heap.size = sMid.heap.size + 1 := by
            rw [hheap]
            simp
          refine ⟨⟨bAll.prefixEq, bAll.sizeLe, bAll.wf, hCells, hVarMono⟩,
            ?_, ?_⟩
          · rw [hheap]
            simp only [Array.size_push]
            exact Nat.lt_succ_self _
          · rw [readTermFuel_app s₁.heap s₁.heap.size sMid.heap.size symbol
              childAddrs.toArray hself]
            have hChildren :
                readListFuel s₁.heap s₁.heap.size childAddrs.toArray.toList =
                  .ok ((List.finRange (σ.functionArity symbol)).map
                    fun index => args index) := by
              rw [show childAddrs.toArray.toList = childAddrs from by simp]
              apply readListFuel_of_pointwise
              · simp [hLenArity, List.length_finRange]
              · intro k hk hk'
                have hp := hPoint k hk (by
                  simpa [List.length_finRange, hLenArity] using hk)
                have hExt := readTermFuel_extend bMap.wf bPush.prefixEq
                  (sMid.heap.size + 1) childAddrs[k] hp.1 _ hp.2
                rw [hsize]
                have hidx :
                    ((List.finRange (σ.functionArity symbol)).map
                      fun index => args index)[k]'hk' =
                      args ((List.finRange (σ.functionArity symbol))[k]'(by
                        simpa [List.length_finRange, hLenArity] using hk)) := by
                  simp
                rw [hidx]
                exact hExt
            simp only [Bind.bind, Except.bind, hChildren]
            rw [dif_pos (by simp [List.length_finRange])]
            refine congrArg Except.ok ?_
            refine congrArg (Term.app symbol) ?_
            funext index
            simp [List.get_eq_getElem, List.getElem_map,
              List.getElem_finRange]

/-! ## The keystone endpoint, pinned

The exact statement stages S4–S6 must produce — written down now so the arc
has one fixed consumer and cannot drift.  `Prop`-level only; proving it *is*
the remaining work, and immediately afterwards it must be composed with
`SLDScopedTree_sound` into one named least-model theorem. -/

/-- Static, cut-free execution of a materialized query yields only answers
that the standardized-apart SLD judgment derives, with the yielded bindings
agreeing with the derivation's substitution. -/
def RefinementEndpoint (σ : LPSignature) [DecidableEq σ.vars]
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    [DecidableEq σ.relationSymbols] : Prop :=
  ∀ (builtins : RuntimeQuery.Builtins σ)
    (program : Program σ) (goals : List (Atom σ))
    (state : RuntimeQuery.State σ) (fuel : Nat)
    (answer : RuntimeQuery.Answer σ) (resumed : RuntimeQuery.State σ),
    (∀ symbol, builtins.isCut symbol = false) →
    RuntimeQuery.openQuery (Memory.empty σ.scoped) 0 1 goals = .ok state →
    RuntimeQuery.pull builtins program fuel state = .answer answer resumed →
    ∃ θ : Subst σ.scoped,
      SLDScopedTree program 1 (queryAtScope 0 goals) θ ∧
      ∀ pair ∈ answer.queryVarMap, ∀ term,
        Heap.readTerm answer.memory.heap pair.2 = .ok term →
        θ pair.1 = term

/-! ## Stage 4: readback naturality

Between two snapshots of one run segment, cells change in exactly one way:
an unbound variable acquires a binding.  `BindingExtension` captures that,
and `readback_naturality` proves the payoff: the later readback of any
address is the finite heap projection applied to its earlier readback.
This is the bridge that lets one substitution — read off the final memory —
justify every resolution step of a derivation. -/

/-- `heap₁` extends `heap₀` by bindings and fresh cells only: every old cell
is preserved verbatim, or was an unbound variable and acquired a link with
the *same identity*. -/
def BindingExtension {σ : LPSignature} (heap₀ heap₁ : Heap σ) : Prop :=
  heap₀.size ≤ heap₁.size ∧
  ∀ (a : Addr) (cell : Cell σ), heap₀[a]? = some cell →
    heap₁[a]? = some cell ∨
    ∃ identity target, cell = Cell.var identity none ∧
      heap₁[a]? = some (Cell.var identity (some target))

/-- Interior chain links (bound variables) are always preserved. -/
theorem BindingExtension.link_preserved {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a target : Addr} {identity : σ.vars}
    (h : heap₀[a]? = some (Cell.var identity (some target))) :
    heap₁[a]? = some (Cell.var identity (some target)) := by
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact hsame
  · cases habs

/-- Constant cells are always preserved. -/
theorem BindingExtension.const_preserved {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a : Addr} {symbol : σ.constants}
    (h : heap₀[a]? = some (Cell.const symbol)) :
    heap₁[a]? = some (Cell.const symbol) := by
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact hsame
  · cases habs

/-- Function-freeness transfers backwards along a binding extension. -/
theorem BindingExtension.ff_back {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    (ff : FunctionFree heap₁) : FunctionFree heap₀ := by
  intro a symbol args h
  rcases ext.2 a _ h with hsame | ⟨_, _, habs, _⟩
  · exact ff a symbol args hsame
  · cases habs

/-- Generalized `cellOf` characterization: any cell carrying the identity is
the cell `cellOf` finds, bound or not. -/
theorem cellOf_of_cell {σ : LPSignature} {heap : Heap σ}
    (inj : IdentityInjective heap) {b : Addr} {w : σ.vars}
    {link : Option Addr}
    (hb : heap[b]? = some (Cell.var w link)) :
    cellOf heap w = some b := by
  unfold cellOf
  have hex : ∃ a : Addr, ∃ l, heap[a]? = some (Cell.var w l) :=
    ⟨b, link, hb⟩
  rw [dif_pos hex]
  obtain ⟨l', hl'⟩ := hex.choose_spec
  exact congrArg some (inj _ b w l' link hl' hb)

/-- On a function-free heap, an `.ok` readback pins the dereference root and
the read value simultaneously. -/
theorem deref_of_readTerm_ff {σ : LPSignature} {heap : Heap σ}
    (ff : FunctionFree heap) :
    ∀ (fuel : Nat) (address : Addr) (t : Term σ),
      readTermFuel heap fuel address = .ok t →
      ∃ root, Heap.derefLoop heap fuel address = .ok (.root root) ∧
        ((∃ identity, heap[root]? = some (Cell.var identity none) ∧
            t = .var identity) ∨
         (∃ symbol, heap[root]? = some (Cell.const symbol) ∧
            t = .const symbol)) := by
  intro fuel
  induction fuel with
  | zero => intro address t h; simp [readTermFuel] at h
  | succ fuel ih =>
      intro address t h
      cases hcell : heap[address]? with
      | none =>
          rw [readTermFuel_invalid heap fuel address hcell] at h
          exact absurd h (by simp)
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | none =>
                  rw [readTermFuel_unbound heap fuel address identity hcell]
                    at h
                  have ht : Term.var identity = t := by simpa using h
                  refine ⟨address, ?_, .inl ⟨identity, hcell, ht.symm⟩⟩
                  simp [Heap.derefLoop, hcell]
              | some target =>
                  rw [readTermFuel_link heap fuel address target identity
                    hcell] at h
                  obtain ⟨root, hroot, hval⟩ := ih target t h
                  refine ⟨root, ?_, hval⟩
                  simp only [Heap.derefLoop, hcell]
                  exact hroot
          | const symbol =>
              rw [readTermFuel_const heap fuel address symbol hcell] at h
              have ht : Term.const symbol = t := by simpa using h
              refine ⟨address, ?_, .inr ⟨symbol, hcell, ht.symm⟩⟩
              simp [Heap.derefLoop, hcell]
          | app symbol args => exact absurd hcell (ff address symbol args)

/-- Walking a preserved chain down: a later-heap `.ok` readback of the chain
head is also the later-heap readback of the old root, at no more fuel. -/
theorem readTermFuel_descend_ext {σ : LPSignature} {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁) :
    ∀ (fuel : Nat) (address root : Addr),
      Heap.derefLoop heap₀ fuel address = .ok (.root root) →
      ∀ (bigFuel : Nat) (t : Term σ),
        readTermFuel heap₁ bigFuel address = .ok t →
        ∃ smallFuel ≤ bigFuel, readTermFuel heap₁ smallFuel root = .ok t := by
  intro fuel
  induction fuel with
  | zero => intro address root h; simp [Heap.derefLoop] at h
  | succ fuel ih =>
      intro address root h bigFuel t hread
      cases hcell : heap₀[address]? with
      | none => simp [Heap.derefLoop, hcell] at h
      | some cell =>
          cases cell with
          | var identity link =>
              cases link with
              | some target =>
                  simp only [Heap.derefLoop, hcell] at h
                  have hcell₁ := ext.link_preserved hcell
                  cases bigFuel with
                  | zero => simp [readTermFuel] at hread
                  | succ bigFuel =>
                      rw [readTermFuel_link heap₁ bigFuel address target
                        identity hcell₁] at hread
                      obtain ⟨smallFuel, hle, hres⟩ :=
                        ih target root h bigFuel t hread
                      exact ⟨smallFuel, Nat.le_succ_of_le hle, hres⟩
              | none =>
                  simp only [Heap.derefLoop, hcell] at h
                  obtain rfl : address = root := by simpa using h
                  exact ⟨bigFuel, Nat.le_refl _, hread⟩
          | const symbol =>
              simp only [Heap.derefLoop, hcell] at h
              obtain rfl : address = root := by simpa using h
              exact ⟨bigFuel, Nat.le_refl _, hread⟩
          | app symbol args =>
              simp only [Heap.derefLoop, hcell] at h
              obtain rfl : address = root := by simpa using h
              exact ⟨bigFuel, Nat.le_refl _, hread⟩

/-- **Readback naturality**: along a binding extension, the later readback
of any address is the finite heap projection of the later heap applied to
its earlier readback. -/
theorem readback_naturality {σ : LPSignature} [DecidableEq σ.vars]
    {heap₀ heap₁ : Heap σ}
    (ext : BindingExtension heap₀ heap₁)
    (inj : IdentityInjective heap₁)
    (ff : FunctionFree heap₁)
    {address : Addr} {t₀ t₁ : Term σ}
    (h₀ : Heap.readTerm heap₀ address = .ok t₀)
    (h₁ : Heap.readTerm heap₁ address = .ok t₁) :
    (heapSubst heap₁).applyTerm t₀ = t₁ := by
  obtain ⟨root, hroot, hval⟩ :=
    deref_of_readTerm_ff (ext.ff_back ff) (heap₀.size + 1) address t₀ h₀
  obtain ⟨smallFuel, hle, hrootRead⟩ :=
    readTermFuel_descend_ext ext (heap₀.size + 1) address root hroot
      (heap₁.size + 1) t₁ h₁
  have hrootFull : Heap.readTerm heap₁ root = .ok t₁ :=
    readTermFuel_mono_le heap₁ (Nat.le_trans hle (Nat.le_refl _)) root t₁
      hrootRead
  rcases hval with ⟨identity, hcell₀, rfl⟩ | ⟨symbol, hcell₀, rfl⟩
  · -- variable leaf: both extension outcomes give the identity a cell at
    -- `root` in the later heap, so the projection sends it to `t₁`.
    have hcell₁ : ∃ link, heap₁[root]? = some (Cell.var identity link) := by
      rcases ext.2 root _ hcell₀ with hsame | ⟨id₂, target, heq, hbound⟩
      · exact ⟨none, hsame⟩
      · cases heq
        exact ⟨some target, hbound⟩
    obtain ⟨link, hcell₁⟩ := hcell₁
    show heapSubst heap₁ identity = t₁
    simp [heapSubst, cellOf_of_cell inj hcell₁, hrootFull]
  · -- constant leaf: preserved verbatim, so both readbacks are the symbol.
    have hcell₁ := ext.const_preserved hcell₀
    have hconst : (Except.ok t₁ : Except ReadbackError (Term σ)) =
        .ok (Term.const symbol) :=
      hrootFull.symm.trans
        (readTermFuel_const heap₁ heap₁.size root symbol hcell₁)
    have : t₁ = Term.const symbol := by simpa using hconst
    rw [this]
    rfl

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP

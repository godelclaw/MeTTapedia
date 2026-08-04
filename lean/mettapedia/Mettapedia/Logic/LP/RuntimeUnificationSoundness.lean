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
  simp [Array.getElem?_set, hne.symm]

theorem heap_set_get_self {σ : LPSignature} (heap : Heap σ) {address : Addr}
    (cell : Cell σ) (hlt : address < heap.size) :
    (heap.set address cell hlt)[address]? = some cell := by
  simp [Array.getElem?_set, hlt]

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

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP

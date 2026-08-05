import Mettapedia.Logic.LP.RuntimeReadback
import Mettapedia.Logic.LP.RuntimeUnification

/-!
# Restoration: memory-operation laws and exact choice-point recovery

Function-free heaps, the targeted readback equations and their fuel
monotonicity, complete inversions of the runtime's write/allocate/set
operations, machine stepping helpers, dereference-root laws — and the
`Extends` write/allocation history with its exact unwind/restore theorems:
restoring a checkpoint recovers the checkpointed memory verbatim.
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

/-- Two live cells never carry one variable identity.  Materialization
gives this for freshly copied structure; the machine's bindings preserve
it.  It makes `heapSubst` well-defined on identities. -/
def IdentityInjective {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (a b : Addr) (identity : σ.vars) (la lb : Option Addr),
    heap[a]? = some (Cell.var identity la) →
    heap[b]? = some (Cell.var identity lb) → a = b

/-- A cell of a pushed heap is an old cell or the pushed cell at the top. -/
theorem getElem?_push_cases {σ : LPSignature} {heap : Heap σ}
    {cell target : Cell σ} {a : Addr}
    (h : (heap.push cell)[a]? = some target) :
    (a < heap.size ∧ heap[a]? = some target) ∨
      (a = heap.size ∧ target = cell) := by
  have hsz : a < heap.size + 1 := by
    have := lt_of_getElem?_some h
    simpa using this
  rcases Nat.lt_or_ge a heap.size with hlt | hge
  · rw [getElem?_push_lt heap cell hlt] at h
    exact .inl ⟨hlt, h⟩
  · have heq : a = heap.size := Nat.le_antisymm (Nat.le_of_lt_succ hsz) hge
    subst heq
    have htop : (heap.push cell)[heap.size]? = some cell := by simp
    rw [htop] at h
    cases h
    exact .inr ⟨rfl, rfl⟩

/-- Every bound variable links strictly downward or to a constant cell. -/
def DescendingOrConst {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (address : Addr) (identity : σ.vars) (target : Addr),
    heap[address]? = some (Cell.var identity (some target)) →
    target < address ∨ ∃ symbol, heap[target]? = some (Cell.const symbol)

/-- The readback-wellfoundedness bundle threaded through machine runs. -/
def OrderedFF {σ : LPSignature} (heap : Heap σ) : Prop :=
  DescendingOrConst heap ∧ FunctionFree heap

/-- `heap₁` extends `heap₀` by bindings and fresh cells only: every old cell
is preserved verbatim, or was an unbound variable and acquired a link with
the *same identity*. -/
def BindingExtension {σ : LPSignature} (heap₀ heap₁ : Heap σ) : Prop :=
  heap₀.size ≤ heap₁.size ∧
  ∀ (a : Addr) (cell : Cell σ), heap₀[a]? = some cell →
    heap₁[a]? = some cell ∨
    ∃ identity target, cell = Cell.var identity none ∧
      heap₁[a]? = some (Cell.var identity (some target))

theorem Extends.trans {σ : LPSignature} {m₀ m₁ m₂ : Memory σ}
    (a : Extends m₀ m₁) (b : Extends m₁ m₂) : Extends m₀ m₂ := by
  induction b with
  | refl => exact a
  | write history step ih => exact .write ih step
  | alloc history step ih => exact .alloc ih step

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP

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

/-! ## Stage 5a: materializer discharge

Every S1–S4 hypothesis, proved for what materialization actually does:
the memory-level history is a genuine `Extends` chain of real allocations
(trail untouched), and function-free source keeps the heap function-free. -/

theorem Extends.trans {σ : LPSignature} {m₀ m₁ m₂ : Memory σ}
    (a : Extends m₀ m₁) (b : Extends m₁ m₂) : Extends m₀ m₂ := by
  induction b with
  | refl => exact a
  | write history step ih => exact .write ih step
  | alloc history step ih => exact .alloc ih step

/-- `Memory.allocate` ignores the trail: success transports to any trail. -/
theorem allocate_trail_irrelevant {σ : LPSignature} {heap : Heap σ}
    {trail₁ trail₂ : Array (TrailEntry σ)} {cell : Cell σ}
    {address : Addr} {memory' : Memory σ}
    (h : Memory.allocate { heap := heap, trail := trail₁ } cell =
      .ok (address, memory')) :
    Memory.allocate { heap := heap, trail := trail₂ } cell =
      .ok (address, { heap := memory'.heap, trail := trail₂ }) := by
  obtain ⟨haddr, hmem⟩ := allocate_ok_inv h
  subst haddr
  unfold Memory.allocate at h ⊢
  split at h
  · split at h
    · rw [if_pos ‹_›, if_pos ‹_›]
      rw [hmem]
      rfl
    · rcases hfind :
          (Cell.references cell).find?
            (fun target => decide (heap.size ≤ target)) with _ | t <;>
        rw [hfind] at h <;> cases h
  · cases h

/-- A successful builder allocation is a real memory-level allocation step,
for any caller trail. -/
theorem allocate_extends {σ : LPSignature} {cell : Cell σ}
    {s₀ s₁ : BuilderState σ} {address : Addr}
    (h : (RuntimeMaterialize.allocate cell).run s₀ = .ok (address, s₁))
    (trail : Array (TrailEntry σ)) :
    Extends { heap := s₀.heap, trail := trail }
      { heap := s₁.heap, trail := trail } := by
  simp only [RuntimeMaterialize.allocate, BuilderM.run_bind,
    BuilderM.get, BuilderM.set, BuilderM.throw] at h
  cases hSc : Memory.allocate { heap := s₀.heap, trail := #[] } cell with
  | error e => rw [hSc] at h; cases h
  | ok pair =>
      obtain ⟨addr₀, memory₀⟩ := pair
      rw [hSc] at h
      cases h
      exact .alloc (.refl _) (allocate_trail_irrelevant hSc)

/-- mapM companion for `Extends`, over any builder element action. -/
theorem mapM_extends {σ : LPSignature}
    {ι : Type _} {β : Type _} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β}
        (trail : Array (TrailEntry σ)),
        (g i).run s₀ = .ok (value, s₁) →
        Extends { heap := s₀.heap, trail := trail }
          { heap := s₁.heap, trail := trail }) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β}
        (trail : Array (TrailEntry σ)),
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        Extends { heap := s₀.heap, trail := trail }
          { heap := s₁.heap, trail := trail } := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values trail h
      rw [run_mapM_nil] at h
      cases h
      exact .refl _
  | cons head tailI tailIh =>
      intro elemExt s₀ s₁ values trail h
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact (elemExt head (by simp) trail hHead).trans
                (tailIh (fun i hi => elemExt i (by simp [hi]))
                  trail hTail)

/-- A materializer run realizes a genuine memory-level `Extends` history. -/
theorem materializeTermAux_extends {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr}
      (trail : Array (TrailEntry σ)),
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      Extends { heap := s₀.heap, trail := trail }
        { heap := s₁.heap, trail := trail } := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact .refl _
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              exact allocate_extends hAlloc trail
  | const symbol =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux] at h
      exact allocate_extends h trail
  | app symbol args ih =>
      intro s₀ s₁ address trail h
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          exact (mapM_extends
            (fun index => materializeTermAux (args index))
            (List.finRange (σ.functionArity symbol))
            (fun i _ => ih i) trail hMap).trans
            (allocate_extends h trail)

/-- Function-free source syntax: no function applications. -/
def TermFF {σ : LPSignature} : Term σ → Prop
  | .var _ => True
  | .const _ => True
  | .app _ _ => False

/-- Materializing function-free source keeps the heap function-free. -/
theorem materializeTermAux_ff {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr},
      TermFF t →
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      FunctionFree s₀.heap → FunctionFree s₁.heap := by
  intro t
  cases t with
  | var identity =>
      intro s₀ s₁ address _ h ff
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact ff
      | none =>
          simp only [hlook, BuilderM.run_bind] at h
          cases hAlloc : (RuntimeMaterialize.allocate
              (Cell.var identity none)).run s₀ with
          | error e => rw [hAlloc] at h; cases h
          | ok pair =>
              obtain ⟨addr₀, sMid⟩ := pair
              rw [hAlloc] at h
              obtain ⟨_, hheap, _⟩ := allocate_run_spec hAlloc
              simp only [BuilderM.set, BuilderM.run_pure] at h
              cases h
              intro a symbol args ha
              rcases Nat.lt_trichotomy a s₀.heap.size with hlt | heq | hgt
              · rw [hheap, getElem?_push_lt _ _ hlt] at ha
                exact ff a symbol args ha
              · subst heq
                rw [hheap] at ha
                simp at ha
              · rw [hheap, Array.getElem?_eq_none (by
                  simp only [Array.size_push]; omega)] at ha
                cases ha
  | const symbol =>
      intro s₀ s₁ address _ h ff
      simp only [materializeTermAux] at h
      obtain ⟨_, hheap, _⟩ := allocate_run_spec h
      intro a symbol' args ha
      rcases Nat.lt_trichotomy a s₀.heap.size with hlt | heq | hgt
      · rw [hheap, getElem?_push_lt _ _ hlt] at ha
        exact ff a symbol' args ha
      · subst heq
        rw [hheap] at ha
        simp at ha
      · rw [hheap, Array.getElem?_eq_none (by
          simp only [Array.size_push]; omega)] at ha
        cases ha
  | app symbol args =>
      intro _ _ _ hFF
      cases hFF

/-! ## Stage 5a continued: atom, goals, and clause round-trips -/

theorem readListFuel_mono_le {σ : LPSignature} (heap : Heap σ)
    {small large : Nat} (hle : small ≤ large)
    (addresses : List Addr) (terms : List (Term σ))
    (h : readListFuel heap small addresses = .ok terms) :
    readListFuel heap large addresses = .ok terms := by
  induction hle with
  | refl => exact h
  | step _ ih =>
      exact readListFuel_mono
        (fun a t' ht => readTermFuel_mono heap _ a t' ht) addresses terms ih

/-- `readAtom` results survive append-only extension of a well-formed heap. -/
theorem readAtom_extend {σ : LPSignature} {heap heap' : Heap σ}
    (hwf : Heap.WellFormed heap)
    (hpre : ∀ i, i < heap.size → heap'[i]? = heap[i]?)
    (hsize : heap.size ≤ heap'.size)
    {atom : RuntimeAtom σ} {result : Atom σ}
    (hbound : ∀ a ∈ atom.args.toList, a < heap.size)
    (h : readAtom heap atom = .ok result) :
    readAtom heap' atom = .ok result := by
  unfold readAtom at h ⊢
  simp only [Bind.bind, Except.bind] at h ⊢
  cases hList : readListFuel heap (heap.size + 1) atom.args.toList with
  | error e => rw [hList] at h; simp at h
  | ok children =>
      rw [hList] at h
      have hExt := readListFuel_extend
        (fun a ha t' ht => readTermFuel_extend hwf hpre (heap.size + 1)
          a ha t' ht) atom.args.toList hbound children hList
      have hLift := readListFuel_mono_le heap'
        (Nat.succ_le_succ hsize) atom.args.toList children hExt
      rw [hLift]
      exact h

/-- What one materialized atom satisfies. -/
theorem materializeAtomAux_spec {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ}
    {ratom : RuntimeAtom σ}
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁))
    (hwf : Heap.WellFormed s₀.heap) (hcells : VarMapCells s₀) :
    BuildOk s₀ s₁ ∧
    (∀ a ∈ ratom.args.toList, a < s₁.heap.size) ∧
    readAtom s₁.heap ratom = .ok atom := by
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      obtain ⟨bMap, hLen, hPoint⟩ :=
        materializeMapM_spec (fun index => atom.args index)
          (List.finRange (σ.relationArity atom.symbol))
          (fun i _ => materializeTermAux_spec (atom.args i)) hMap hwf hcells
      have hLenArity : childAddrs.length = σ.relationArity atom.symbol := by
        simpa [List.length_finRange] using hLen
      have hbound : ∀ a ∈ childAddrs.toArray.toList, a < s₁.heap.size := by
        intro a ha
        rw [show childAddrs.toArray.toList = childAddrs from by simp] at ha
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        exact (hPoint k hk (by omega)).1
      refine ⟨bMap, hbound, ?_⟩
      unfold readAtom
      simp only [Bind.bind, Except.bind]
      have hChildren :
          readListFuel s₁.heap (s₁.heap.size + 1)
              childAddrs.toArray.toList =
            .ok ((List.finRange (σ.relationArity atom.symbol)).map
              fun index => atom.args index) := by
        rw [show childAddrs.toArray.toList = childAddrs from by simp]
        apply readListFuel_of_pointwise
        · simp [hLenArity, List.length_finRange]
        · intro k hk hk'
          have hp := hPoint k hk (by
            simpa [List.length_finRange, hLenArity] using hk)
          have hidx :
              ((List.finRange (σ.relationArity atom.symbol)).map
                fun index => atom.args index)[k]'hk' =
                atom.args ((List.finRange (σ.relationArity atom.symbol))[k]'(by
                  simpa [List.length_finRange, hLenArity] using hk)) := by
            simp
          rw [hidx]
          exact hp.2
      rw [hChildren]
      dsimp only
      rw [dif_pos (by simp [List.length_finRange])]
      refine congrArg Except.ok ?_
      cases atom with
      | mk symbol args =>
          refine congrArg (Atom.mk symbol) ?_
          funext index
          simp [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]

/-- Generic mapM preservation of a heap invariant. -/
theorem mapM_heap_preserves {σ : LPSignature} {ι β : Type _}
    {P : Heap σ → Prop} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β},
        (g i).run s₀ = .ok (value, s₁) → P s₀.heap → P s₁.heap) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β},
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        P s₀.heap → P s₁.heap := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values h hP
      rw [run_mapM_nil] at h
      cases h
      exact hP
  | cons head tailI tailIh =>
      intro elem s₀ s₁ values h hP
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact tailIh (fun i hi => elem i (by simp [hi])) hTail
                (elem head (by simp) hHead hP)

/-- Atom materialization is a memory-level `Extends` history. -/
theorem materializeAtomAux_extends {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (trail : Array (TrailEntry σ))
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    Extends { heap := s₀.heap, trail := trail }
      { heap := s₁.heap, trail := trail } := by
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_extends _ _
        (fun i _ => fun {s₀ s₁ value} trail' h' =>
          materializeTermAux_extends (atom.args i) trail' h') trail hMap

/-- Function-free atoms keep the heap function-free. -/
def AtomFF {σ : LPSignature} (atom : Atom σ) : Prop :=
  ∀ index, TermFF (atom.args index)

theorem materializeAtomAux_ff {σ : LPSignature} [DecidableEq σ.vars]
    (atom : Atom σ) {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (hFF : AtomFF atom)
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    FunctionFree s₀.heap → FunctionFree s₁.heap := by
  intro ff
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_heap_preserves _ _
        (fun i _ => fun {s₀ s₁ value} h' hp =>
          materializeTermAux_ff (atom.args i) (hFF i) h' hp)
        hMap ff

/-- mapM companion for atom round-trips: every materialized atom reads back
in the final builder heap. -/
theorem materializeAtomsMapM_spec {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ (atoms : List (Atom σ)) {s₀ s₁ : BuilderState σ}
      {ratoms : List (RuntimeAtom σ)},
      (atoms.mapM materializeAtomAux).run s₀ = .ok (ratoms, s₁) →
      Heap.WellFormed s₀.heap → VarMapCells s₀ →
      BuildOk s₀ s₁ ∧ ratoms.length = atoms.length ∧
        ∀ k (hk : k < ratoms.length) (hk' : k < atoms.length),
          readAtom s₁.heap ratoms[k] = .ok atoms[k] := by
  intro atoms
  induction atoms with
  | nil =>
      intro s₀ s₁ ratoms h hwf hcells
      rw [run_mapM_nil] at h
      cases h
      exact ⟨BuildOk.rfl hwf hcells, _root_.rfl,
        fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | cons head tailA tailIh =>
      intro s₀ s₁ ratoms h hwf hcells
      rw [run_mapM_cons] at h
      cases hHead : (materializeAtomAux head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headAtom, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailA.mapM materializeAtomAux).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailAtoms, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              obtain ⟨bHead, hBound, hHeadRead⟩ :=
                materializeAtomAux_spec head hHead hwf hcells
              obtain ⟨bTail, hLen, hPoint⟩ :=
                tailIh hTail bHead.wf bHead.cells
              refine ⟨bHead.trans bTail,
                congrArg (fun n => n + 1) hLen, ?_⟩
              intro k hk hk'
              cases k with
              | zero =>
                  simp only [List.getElem_cons_zero]
                  exact readAtom_extend bHead.wf bTail.prefixEq bTail.sizeLe
                    hBound hHeadRead
              | succ k =>
                  have := hPoint k (by simpa using hk) (by simpa using hk')
                  simpa using this

/-- Invert `runChecked` success into its checks and the raw run. -/
theorem runChecked_ok {σ : LPSignature} {α : Type _}
    {action : RuntimeMaterialize.BuilderM σ α} {heap : Heap σ}
    {value : α} {state : BuilderState σ}
    (h : RuntimeMaterialize.runChecked action heap = .ok (value, state)) :
    heap.checkWellFormed = true ∧ heap.checkWellShaped = true ∧
      action.run (BuilderState.start heap) = .ok (value, state) ∧
      state.heap.checkWellFormed = true ∧
      state.heap.checkWellShaped = true := by
  unfold RuntimeMaterialize.runChecked at h
  by_cases hWF : heap.checkWellFormed
  case neg => rw [if_neg hWF] at h; cases h
  case pos =>
  rw [if_pos hWF] at h
  by_cases hWS : heap.checkWellShaped
  case neg => rw [if_neg hWS] at h; cases h
  case pos =>
  rw [if_pos hWS] at h
  cases hrun : action.run (BuilderState.start heap) with
  | error e => rw [hrun] at h; cases h
  | ok pair =>
      rw [hrun] at h
      dsimp only at h
      by_cases hWF' : pair.2.heap.checkWellFormed
      case neg => rw [if_neg hWF'] at h; cases h
      case pos =>
      rw [if_pos hWF'] at h
      by_cases hWS' : pair.2.heap.checkWellShaped
      case neg => rw [if_neg hWS'] at h; cases h
      case pos =>
      rw [if_pos hWS'] at h
      cases h
      exact ⟨hWF, hWS, by first | exact hrun | rfl, hWF', hWS'⟩

/-- **Public goals round-trip**: a materialized query's runtime atoms read
back verbatim in the result memory; the memory extends the caller's by real
allocations only; and the variable map is cell-coherent. -/
theorem materializeGoals_roundtrip {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result) :
    Extends memory result.memory ∧
    result.goals.length = goals.length ∧
    (∀ k (hk : k < result.goals.length) (hk' : k < goals.length),
      readAtom result.memory.heap result.goals[k] = .ok goals[k]) ∧
    Heap.WellFormed result.memory.heap ∧
    VarMapCells { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨hWF, hWS, hrun, hWF', hWS'⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        obtain ⟨bOk, hLen, hPoint⟩ :=
          materializeAtomsMapM_spec goals hrun
            (Heap.wellFormed_of_check hWF)
            (fun pair hp => by simp [BuilderState.start] at hp)
        have hExtends : Extends memory
            { heap := state.heap, trail := memory.trail } := by
          have := mapM_extends materializeAtomAux goals
            (fun i _ => fun {s₀ s₁ value} trail' h' =>
              materializeAtomAux_extends i trail' h')
            memory.trail hrun
          simpa [BuilderState.start] using this
        exact ⟨hExtends, hLen, hPoint, bOk.wf, bOk.cells⟩

/-- **Public clause round-trip**: a materialized (already standardized-apart)
clause reads back verbatim — head and every body atom — in the result
memory, which extends the caller's by real allocations only. -/
theorem materializeClause_roundtrip {σ : LPSignature} [DecidableEq σ.vars]
    {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result) :
    Extends memory result.memory ∧
    readAtom result.memory.heap result.clause.head = .ok clause.head ∧
    result.clause.body.length = clause.body.length ∧
    (∀ k (hk : k < result.clause.body.length)
      (hk' : k < clause.body.length),
      readAtom result.memory.heap result.clause.body[k] =
        .ok clause.body[k]) ∧
    Heap.WellFormed result.memory.heap ∧
    VarMapCells { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨hWF, hWS, hrun, hWF', hWS'⟩ := runChecked_ok hrc
      by_cases hCheck :
          runtimeClause.checkWellFormed state.heap = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        simp only [materializeClauseAux, BuilderM.run_bind] at hrun
        cases hHead : (materializeAtomAux clause.head).run
            (BuilderState.start memory.heap) with
        | error e => rw [hHead] at hrun; cases hrun
        | ok headPair =>
            obtain ⟨headAtom, sMid⟩ := headPair
            rw [hHead] at hrun
            dsimp only at hrun
            cases hBody : (clause.body.mapM materializeAtomAux).run sMid with
            | error e => rw [hBody] at hrun; cases hrun
            | ok bodyPair =>
                obtain ⟨bodyAtoms, sEnd⟩ := bodyPair
                rw [hBody] at hrun
                dsimp only at hrun
                cases hrun
                have hwf₀ : Heap.WellFormed
                    (BuilderState.start memory.heap).heap :=
                  Heap.wellFormed_of_check hWF
                have hcells₀ : VarMapCells (BuilderState.start memory.heap) :=
                  fun pair hp => by simp [BuilderState.start] at hp
                obtain ⟨bHead, hBound, hHeadRead⟩ :=
                  materializeAtomAux_spec clause.head hHead hwf₀ hcells₀
                obtain ⟨bBody, hLen, hPoint⟩ :=
                  materializeAtomsMapM_spec clause.body hBody
                    bHead.wf bHead.cells
                have hExtends : Extends memory
                    { heap := state.heap, trail := memory.trail } := by
                  have hHeadExt := materializeAtomAux_extends clause.head
                    memory.trail hHead
                  have hBodyExt := mapM_extends materializeAtomAux clause.body
                    (fun i _ => fun {s₀ s₁ value} trail' h' =>
                      materializeAtomAux_extends i trail' h')
                    memory.trail hBody
                  have := hHeadExt.trans hBodyExt
                  simpa [BuilderState.start] using this
                refine ⟨hExtends, ?_, hLen, hPoint, bBody.wf,
                  bBody.cells⟩
                exact readAtom_extend bHead.wf bBody.prefixEq bBody.sizeLe
                  hBound hHeadRead

/-! ## Stage 5b: machine-side discharge

The unifier's success segments realize both relations S4 and S1 consume:
every write is a fresh binding over an unbound cell (`BindingExtension`)
and a genuine trailed `Memory.write` (`Extends`). -/

theorem BindingExtension.rfl {σ : LPSignature} (heap : Heap σ) :
    BindingExtension heap heap :=
  ⟨Nat.le_refl _, fun _ _ h => .inl h⟩

theorem BindingExtension.trans {σ : LPSignature}
    {heap₀ heap₁ heap₂ : Heap σ} (a : BindingExtension heap₀ heap₁)
    (b : BindingExtension heap₁ heap₂) : BindingExtension heap₀ heap₂ := by
  refine ⟨a.1.trans b.1, ?_⟩
  intro addr cell h
  rcases a.2 addr cell h with h₁ | ⟨id, target, rfl, h₁⟩
  · exact b.2 addr cell h₁
  · rcases b.2 addr _ h₁ with h₂ | ⟨id₂, target₂, habs, _⟩
    · exact .inr ⟨id, target, _root_.rfl, h₂⟩
    · cases habs

/-- One machine binding is a binding extension. -/
theorem bindingExtension_of_write {σ : LPSignature}
    {memory memory' : Memory σ} {address target : Addr} {identity : σ.vars}
    (hcell : memory.heap[address]? = some (Cell.var identity none))
    (hw : memory.write address (Cell.var identity (some target)) =
      .ok memory') :
    BindingExtension memory.heap memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  refine ⟨by rw [hheq]; simp, ?_⟩
  intro addr cell h
  by_cases haddr : addr = address
  · subst haddr
    rw [h] at hcell
    cases hcell
    exact .inr ⟨identity, target, _root_.rfl, by
      rw [hheq]
      exact heap_set_get_self _ _ hlt⟩
  · exact .inl (by rw [hheq, heap_set_get_ne _ _ hlt haddr]; exact h)

/-- Abbreviation for the extension induction hypothesis. -/
def ExtensionIH (σ : LPSignature) [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) : Prop :=
  ∀ (c : Configuration σ) (m : Memory σ), c.phase = .compare →
    runSteps fuel (.running c) = .terminal (.success m) →
    BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
      c.memory.heap.size = m.heap.size

/-- One binding step followed by a successful run composes both relations. -/
theorem bindStep_extension {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {fuel : Nat}
    (ih : ExtensionIH σ fuel) (c : Configuration σ) (m : Memory σ)
    (rest : List (Addr × Addr)) {bound target : Addr} {identity : σ.vars}
    (hphase : c.phase = .compare)
    (hcellBound : c.memory.heap[bound]? = some (Cell.var identity none))
    (hrun : runSteps fuel (afterBinding c rest bound identity target) =
      .terminal (.success m)) :
    BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
      c.memory.heap.size = m.heap.size := by
  simp only [afterBinding] at hrun
  cases hw : c.memory.write bound (Cell.var identity (some target)) with
  | error e =>
      rw [hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      rw [hw] at hrun
      obtain ⟨ihBE, ihEx, ihSize⟩ :=
        ih { c with memory := memory', agenda := rest } m hphase hrun
      obtain ⟨hlt, hheq⟩ := write_ok_heap hw
      refine ⟨(bindingExtension_of_write hcellBound hw).trans ihBE,
        (Extends.write (.refl c.memory) hw).trans ihEx, ?_⟩
      have hsz : memory'.heap.size = c.memory.heap.size := by
        rw [hheq]; simp
      exact hsz.symm.trans ihSize

/-- A successful unifier run is a binding extension and a real write
history of the entry memory. -/
theorem runSteps_success_extension {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      runSteps fuel (.running c) = .terminal (.success m) →
      BindingExtension c.memory.heap m.heap ∧ Extends c.memory m ∧
        c.memory.heap.size = m.heap.size := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ hrun
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hrun
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
              exact ⟨BindingExtension.rfl _, .refl _, _root_.rfl⟩
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
                              exact absurd hrun
                                (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              split at hstep
                              · cases hstep
                                exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                              · -- distinct roots: analyze both cells
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases hcr : c.memory.heap[rightRoot]? with
                                    | none =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | some t =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | const s =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                        | app s a =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                    | some cellR =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | some t =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          bindStep_extension
                                                            ih c m rest hphase
                                                            hcr hrun
                                                    | some t₂ =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact absurd hrun
                                                          (beginRollback_no_success
                                                            fuel c _ m)
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | none =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        split at hstep <;>
                                                          cases hstep
                                                        · exact
                                                            bindStep_extension
                                                              ih c m rest hphase
                                                              hcr hrun
                                                        · exact
                                                            bindStep_extension
                                                              ih c m rest hphase
                                                              hcl hrun
                                                    | some t =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        cases hstep
                                                        exact
                                                          bindStep_extension
                                                            ih c m rest hphase
                                                            hcl hrun
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcl hrun
                                                | app symbolR argsR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcl hrun
                                        | const symbolL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcr hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep <;> cases hstep
                                                · exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                                                · exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | app symbolL argsL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_extension
                                                      ih c m rest hphase hcr hrun
                                                | some t =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact absurd hrun
                                                      (beginRollback_no_success
                                                        fuel c _ m)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | app symbolR argsR =>
                                                simp only [hcl, hcr] at hstep
                                                split at hstep
                                                · split at hstep <;> cases hstep
                                                  · exact ih { c with agenda := rest, phase := .compare } m rfl hrun
                                                  · exact ih { c with agenda := argsL.toList.zip argsR.toList ++ rest, visited := orderedPair leftRoot rightRoot :: c.visited, phase := .compare } m rfl hrun
                                                · cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)

/-- Entry-point form: a successful `startMany` unification run extends its
entry memory by fresh bindings only, as a real write history. -/
theorem startMany_success_extension {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m)) :
    BindingExtension memory₀.heap m.heap ∧ Extends memory₀ m ∧
      memory₀.heap.size = m.heap.size :=
  runSteps_success_extension fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare } m rfl hrun

/-- In-bounds addresses always hold a cell. -/
theorem getElem?_some_of_lt {σ : LPSignature} {heap : Heap σ} {a : Addr}
    (h : a < heap.size) : ∃ cell, heap[a]? = some cell := by
  rcases hcell : heap[a]? with _ | cell
  · rw [Array.getElem?_eq_none_iff] at hcell
    exact absurd hcell (Nat.not_le.mpr h)
  · exact ⟨cell, _root_.rfl⟩

/-- A later-heap variable cell came from an earlier variable cell with the
same identity, along a binding extension within bounds. -/
theorem BindingExtension.var_back {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    {a : Addr} {identity : σ.vars} {link : Option Addr}
    (hlt : a < heap₀.size)
    (h : heap₁[a]? = some (Cell.var identity link)) :
    ∃ link₀, heap₀[a]? = some (Cell.var identity link₀) := by
  obtain ⟨cell, hc⟩ := getElem?_some_of_lt hlt
  rcases ext.2 a cell hc with hsame | ⟨id₂, target, rfl, hbound⟩
  · rw [hsame] at h
    cases h
    exact ⟨_, hc⟩
  · rw [hbound] at h
    cases h
    exact ⟨none, hc⟩

/-- Identity injectivity transfers across a size-preserving binding
extension: identities of existing cells never change, and no cells are
added. -/
theorem IdentityInjective.of_bindingExtension {σ : LPSignature}
    {heap₀ heap₁ : Heap σ} (ext : BindingExtension heap₀ heap₁)
    (hsize : heap₀.size = heap₁.size)
    (inj : IdentityInjective heap₀) : IdentityInjective heap₁ := by
  intro a b identity la lb ha hb
  have haLt : a < heap₀.size := hsize.symm ▸ lt_of_getElem?_some ha
  have hbLt : b < heap₀.size := hsize.symm ▸ lt_of_getElem?_some hb
  obtain ⟨la₀, ha₀⟩ := ext.var_back haLt ha
  obtain ⟨lb₀, hb₀⟩ := ext.var_back hbLt hb
  exact inj a b identity la₀ lb₀ ha₀ hb₀

/-! ## Stage 5b: identity injectivity is established at materialization

Materialization is where variable identities enter the heap.  Under a
freshness predicate separating the activation's identities from everything
already allocated — discharged at the call sites by the scope discipline —
the builder's variable-map bookkeeping yields identity injectivity outright:
a fresh identity is allocated at most once because the variable map is
consulted first, and a fresh identity can never collide with an old cell
because old cells are never fresh. -/

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

/-- A failed association-list lookup excludes every entry with that key. -/
theorem lookup_none_not_mem {σ : LPSignature} [DecidableEq σ.vars] :
    ∀ {varMap : List (σ.vars × Addr)} {identity : σ.vars},
      List.lookup identity varMap = none →
      ∀ address, (identity, address) ∉ varMap := by
  intro varMap
  induction varMap with
  | nil =>
      intro _ _ address hmem
      cases hmem
  | cons head tailM ih =>
      intro identity h address hmem
      obtain ⟨key, value⟩ := head
      by_cases he : identity = key
      · subst he
        simp [List.lookup] at h
      · have hne : (identity == key) = false := by simpa using he
        simp only [List.lookup, hne] at h
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exact he (by cases heq; rfl)
        · exact ih h address hmem'

/-- The freshness bundle carried through one materialization: the variable
map is functional, every heap cell carrying a fresh identity is registered
in the variable map, and the whole heap is identity-injective. -/
structure FreshInv {σ : LPSignature} (Fresh : σ.vars → Prop)
    (s : BuilderState σ) : Prop where
  functional : ∀ (identity : σ.vars) (a b : Addr),
    (identity, a) ∈ s.varMap → (identity, b) ∈ s.varMap → a = b
  registered : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
    s.heap[a]? = some (Cell.var identity link) → Fresh identity →
      (identity, a) ∈ s.varMap
  injective : IdentityInjective s.heap

/-- Pushing a non-variable cell preserves the freshness bundle. -/
theorem FreshInv.push_nonvar {σ : LPSignature} {Fresh : σ.vars → Prop}
    {s : BuilderState σ} (hInv : FreshInv Fresh s) {cell : Cell σ}
    (hNonvar : ∀ identity link, cell ≠ Cell.var identity link) :
    FreshInv Fresh { heap := s.heap.push cell, varMap := s.varMap } where
  functional := hInv.functional
  registered := by
    intro a identity link hcell hFid
    rcases getElem?_push_cases hcell with ⟨_, hold⟩ | ⟨_, hcelleq⟩
    · exact hInv.registered a identity link hold hFid
    · exact absurd hcelleq.symm (hNonvar identity link)
  injective := by
    intro a b identity la lb ha hb
    rcases getElem?_push_cases ha with ⟨_, haOld⟩ | ⟨_, haNew⟩
    · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨_, hbNew⟩
      · exact hInv.injective a b identity la lb haOld hbOld
      · exact absurd hbNew.symm (hNonvar identity lb)
    · exact absurd haNew.symm (hNonvar identity la)

/-- Generic mapM preservation of a builder-state invariant. -/
theorem mapM_state_preserves {σ : LPSignature} {ι β : Type _}
    {P : BuilderState σ → Prop} (g : ι → RuntimeMaterialize.BuilderM σ β) :
    ∀ (indices : List ι),
      (∀ i ∈ indices, ∀ {s₀ s₁ : BuilderState σ} {value : β},
        (g i).run s₀ = .ok (value, s₁) → P s₀ → P s₁) →
      ∀ {s₀ s₁ : BuilderState σ} {values : List β},
        (indices.mapM g).run s₀ = .ok (values, s₁) →
        P s₀ → P s₁ := by
  intro indices
  induction indices with
  | nil =>
      intro _ s₀ s₁ values h hP
      rw [run_mapM_nil] at h
      cases h
      exact hP
  | cons head tailI tailIh =>
      intro elem s₀ s₁ values h hP
      rw [run_mapM_cons] at h
      cases hHead : (g head).run s₀ with
      | error e => rw [hHead] at h; cases h
      | ok headPair =>
          obtain ⟨headVal, sMid⟩ := headPair
          rw [hHead] at h
          dsimp only at h
          cases hTail : (tailI.mapM g).run sMid with
          | error e => rw [hTail] at h; cases h
          | ok tailPair =>
              obtain ⟨tailVals, sEnd⟩ := tailPair
              rw [hTail] at h
              dsimp only at h
              cases h
              exact tailIh (fun i hi => elem i (by simp [hi])) hTail
                (elem head (by simp) hHead hP)

/-- Term materialization preserves the freshness bundle when every variable
of the term is fresh. -/
theorem materializeTermAux_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} :
    ∀ (t : Term σ) {s₀ s₁ : BuilderState σ} {address : Addr},
      (∀ v ∈ t.freeVars, Fresh v) →
      (materializeTermAux t).run s₀ = .ok (address, s₁) →
      FreshInv Fresh s₀ → FreshInv Fresh s₁ := by
  intro t
  induction t with
  | var identity =>
      intro s₀ s₁ address hFreshT h hInv
      have hFreshId : Fresh identity :=
        hFreshT identity (by simp [Term.freeVars])
      simp only [materializeTermAux, BuilderM.run_bind, BuilderM.get] at h
      cases hlook : List.lookup identity s₀.varMap with
      | some existing =>
          simp only [hlook, BuilderM.run_pure] at h
          cases h
          exact hInv
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
              refine ⟨?_, ?_, ?_⟩
              · -- functionality of the extended variable map
                intro id a b ha hb
                rcases List.mem_cons.mp ha with haH | haT
                · rcases List.mem_cons.mp hb with hbH | hbT
                  · rw [Prod.mk.injEq] at haH hbH
                    exact haH.2.trans hbH.2.symm
                  · rw [Prod.mk.injEq] at haH
                    rw [hvar] at hbT
                    exact absurd (haH.1 ▸ hbT)
                      (lookup_none_not_mem hlook b)
                · rcases List.mem_cons.mp hb with hbH | hbT
                  · rw [Prod.mk.injEq] at hbH
                    rw [hvar] at haT
                    exact absurd (hbH.1 ▸ haT)
                      (lookup_none_not_mem hlook a)
                  · rw [hvar] at haT hbT
                    exact hInv.functional id a b haT hbT
              · -- fresh cells stay registered
                intro a id link hcell hFid
                rw [hheap] at hcell
                rcases getElem?_push_cases hcell with ⟨_, hold⟩ | ⟨heq, hcelleq⟩
                · have := hInv.registered a id link hold hFid
                  rw [← hvar] at this
                  exact List.mem_cons_of_mem _ this
                · injection hcelleq with hid _
                  subst heq
                  subst hid
                  exact List.mem_cons_self ..
              · -- injectivity with one genuinely new identity
                intro a b id la lb ha hb
                rw [hheap] at ha hb
                rcases getElem?_push_cases ha with ⟨_, haOld⟩ | ⟨haEq, haNew⟩
                · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨hbEq, hbNew⟩
                  · exact hInv.injective a b id la lb haOld hbOld
                  · injection hbNew with hid _
                    subst hid
                    exact absurd (hInv.registered a id la haOld hFreshId)
                      (lookup_none_not_mem hlook a)
                · rcases getElem?_push_cases hb with ⟨_, hbOld⟩ | ⟨hbEq, hbNew⟩
                  · injection haNew with hid _
                    subst hid
                    exact absurd (hInv.registered b id lb hbOld hFreshId)
                      (lookup_none_not_mem hlook b)
                  · exact haEq.trans hbEq.symm
  | const symbol =>
      intro s₀ s₁ address _ h hInv
      simp only [materializeTermAux] at h
      obtain ⟨_, hheap, hvar⟩ := allocate_run_spec h
      have := hInv.push_nonvar (cell := Cell.const symbol)
        (fun _ _ hEq => by cases hEq)
      rw [← hheap, ← hvar] at this
      exact this
  | app symbol args ih =>
      intro s₀ s₁ address hFreshT h hInv
      simp only [materializeTermAux, BuilderM.run_bind] at h
      cases hMap : ((List.finRange (σ.functionArity symbol)).mapM fun index =>
          materializeTermAux (args index)).run s₀ with
      | error e => rw [hMap] at h; cases h
      | ok mapPair =>
          obtain ⟨childAddrs, sMid⟩ := mapPair
          rw [hMap] at h
          obtain ⟨_, hheap, hvar⟩ := allocate_run_spec h
          have hMid : FreshInv Fresh sMid :=
            mapM_state_preserves _ _
              (fun i _ => fun {s₀ s₁ value} h' hp =>
                ih i (fun v hv => hFreshT v (by
                  simp only [Term.freeVars]
                  exact Finset.mem_biUnion.mpr
                    ⟨i, Finset.mem_univ i, hv⟩)) h' hp)
              hMap hInv
          have := hMid.push_nonvar
            (cell := Cell.app symbol childAddrs.toArray)
            (fun _ _ hEq => by cases hEq)
          rw [← hheap, ← hvar] at this
          exact this

/-- Atom materialization preserves the freshness bundle when every variable
of the atom is fresh. -/
theorem materializeAtomAux_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} (atom : Atom σ)
    {s₀ s₁ : BuilderState σ} {ratom : RuntimeAtom σ}
    (hFresh : ∀ v ∈ atom.freeVars, Fresh v)
    (h : (materializeAtomAux atom).run s₀ = .ok (ratom, s₁)) :
    FreshInv Fresh s₀ → FreshInv Fresh s₁ := by
  intro hInv
  simp only [materializeAtomAux, BuilderM.run_bind] at h
  cases hMap : ((List.finRange (σ.relationArity atom.symbol)).mapM
      fun index => materializeTermAux (atom.args index)).run s₀ with
  | error e => rw [hMap] at h; cases h
  | ok mapPair =>
      obtain ⟨childAddrs, sMid⟩ := mapPair
      rw [hMap] at h
      dsimp only at h
      cases h
      exact mapM_state_preserves _ _
        (fun i _ => fun {s₀ s₁ value} h' hp =>
          materializeTermAux_freshInv (atom.args i)
            (fun v hv => hFresh v (by
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩))
            h' hp)
        hMap hInv

/-- **Goal materialization establishes injectivity.**  If the caller's heap
is identity-injective and carries no fresh identities, and every goal
variable is fresh, then the materialized result is identity-injective and
every fresh-identity cell is registered in the returned variable map. -/
theorem materializeGoals_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} {memory : Memory σ} {goals : List (Atom σ)}
    {result : MaterializedGoals σ}
    (h : materializeGoals memory goals = .ok result)
    (hFresh : ∀ atom ∈ goals, ∀ v ∈ atom.freeVars, Fresh v)
    (hFree : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
      memory.heap[a]? = some (Cell.var identity link) → ¬ Fresh identity)
    (hInj : IdentityInjective memory.heap) :
    FreshInv Fresh
      { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeGoals at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeGoalsAux goals) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeGoals, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck : (runtimeGoals.all
          fun atom => atom.checkWellFormed state.heap) = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        have hStart : FreshInv Fresh (BuilderState.start memory.heap) := by
          refine ⟨?_, ?_, ?_⟩
          · intro id a b ha _
            cases ha
          · intro a id link hcell hFid
            exact absurd hFid (hFree a id link hcell)
          · exact hInj
        exact mapM_state_preserves materializeAtomAux goals
          (fun i hi => fun {s₀ s₁ value} h' hp =>
            materializeAtomAux_freshInv i (hFresh i hi) h' hp)
          hrun hStart

/-- **Clause materialization establishes injectivity**, under the same
freshness split: old cells are never fresh, clause variables always are. -/
theorem materializeClause_freshInv {σ : LPSignature} [DecidableEq σ.vars]
    {Fresh : σ.vars → Prop} {memory : Memory σ} {clause : Clause σ}
    {result : MaterializedClause σ}
    (h : materializeClause memory clause = .ok result)
    (hFreshHead : ∀ v ∈ clause.head.freeVars, Fresh v)
    (hFreshBody : ∀ atom ∈ clause.body, ∀ v ∈ atom.freeVars, Fresh v)
    (hFree : ∀ (a : Addr) (identity : σ.vars) (link : Option Addr),
      memory.heap[a]? = some (Cell.var identity link) → ¬ Fresh identity)
    (hInj : IdentityInjective memory.heap) :
    FreshInv Fresh
      { heap := result.memory.heap, varMap := result.varMap } := by
  unfold materializeClause at h
  cases hrc : RuntimeMaterialize.runChecked
      (materializeClauseAux clause) memory.heap with
  | error e => rw [hrc] at h; cases h
  | ok pair =>
      obtain ⟨runtimeClause, state⟩ := pair
      rw [hrc] at h
      dsimp only at h
      obtain ⟨_, _, hrun, _, _⟩ := runChecked_ok hrc
      by_cases hCheck :
          runtimeClause.checkWellFormed state.heap = true
      case neg => rw [if_neg hCheck] at h; cases h
      case pos =>
        rw [if_pos hCheck] at h
        cases h
        simp only [materializeClauseAux, BuilderM.run_bind] at hrun
        cases hHead : (materializeAtomAux clause.head).run
            (BuilderState.start memory.heap) with
        | error e => rw [hHead] at hrun; cases hrun
        | ok headPair =>
            obtain ⟨headAtom, sMid⟩ := headPair
            rw [hHead] at hrun
            dsimp only at hrun
            cases hBody : (clause.body.mapM materializeAtomAux).run sMid with
            | error e => rw [hBody] at hrun; cases hrun
            | ok bodyPair =>
                obtain ⟨bodyAtoms, sEnd⟩ := bodyPair
                rw [hBody] at hrun
                dsimp only at hrun
                cases hrun
                have hStart : FreshInv Fresh
                    (BuilderState.start memory.heap) := by
                  refine ⟨?_, ?_, ?_⟩
                  · intro id a b ha _
                    cases ha
                  · intro a id link hcell hFid
                    exact absurd hFid (hFree a id link hcell)
                  · exact hInj
                have hMid : FreshInv Fresh sMid :=
                  materializeAtomAux_freshInv clause.head hFreshHead
                    hHead hStart
                exact mapM_state_preserves materializeAtomAux clause.body
                  (fun i hi => fun {s₀ s₁ value} h' hp =>
                    materializeAtomAux_freshInv i (hFreshBody i hi) h' hp)
                  hBody hMid

/-! ### Scope discipline discharges freshness

Every variable of a term copied `atScope scope` carries exactly that scope,
so `Fresh := (·.scope = scope)` splits new activations from every heap
whose identities all live at strictly lower scopes. -/

theorem Term.freeVars_atScope {σ : LPSignature} [DecidableEq σ.vars]
    (scope : Nat) :
    ∀ (t : Term σ) (v : ScopedVar σ.vars),
      v ∈ (Term.atScope scope t).freeVars → v.scope = scope := by
  intro t
  induction t with
  | var w =>
      intro v hv
      simp only [Term.atScope, Term.renameVars_var, Term.freeVars,
        Finset.mem_singleton] at hv
      subst hv
      rfl
  | const c =>
      intro v hv
      simp [Term.atScope, Term.renameVars_const, Term.freeVars] at hv
  | app f ts ih =>
      intro v hv
      simp only [Term.atScope, Term.renameVars_app, Term.freeVars] at hv
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
      exact ih i v hi

theorem Atom.freeVars_atScope {σ : LPSignature} [DecidableEq σ.vars]
    (scope : Nat) (atom : Atom σ) (v : ScopedVar σ.vars)
    (hv : v ∈ (Atom.atScope scope atom).freeVars) : v.scope = scope := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact Term.freeVars_atScope scope (atom.args i) v hi

/-- Every variable identity in the heap lives strictly below the bound.
This is the run invariant that makes each new activation scope fresh. -/
def HeapScopesBelow {σ : LPSignature} (bound : Nat)
    (heap : Heap σ.scoped) : Prop :=
  ∀ (a : Addr) (identity : ScopedVar σ.vars) (link : Option Addr),
    heap[a]? = some (Cell.var identity link) → identity.scope < bound

/-- Scoped instantiation for query materialization: a query copied at
`scope` over a heap whose scopes are below `scope` builds an
identity-injective heap with all `scope`-cells registered. -/
theorem materializeGoals_scoped_freshInv {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {goals : List (Atom σ)} {scope : Nat}
    {result : MaterializedGoals σ.scoped}
    (h : materializeGoals memory (queryAtScope scope goals) = .ok result)
    (hBelow : HeapScopesBelow scope memory.heap)
    (hInj : IdentityInjective memory.heap) :
    FreshInv (fun v : ScopedVar σ.vars => v.scope = scope)
      { heap := result.memory.heap, varMap := result.varMap } :=
  materializeGoals_freshInv h
    (fun atom hatom v hv => by
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp hatom
      exact Atom.freeVars_atScope scope source v hv)
    (fun a id link hcell => Nat.ne_of_lt (hBelow a id link hcell))
    hInj

/-- Scoped instantiation for clause activation: a clause standardized apart
at `scope` over a heap whose scopes are below `scope` builds an
identity-injective heap with all `scope`-cells registered. -/
theorem materializeClause_scoped_freshInv {σ : LPSignature}
    [DecidableEq σ.vars] {memory : Memory σ.scoped}
    {clause : Clause σ} {scope : Nat}
    {result : MaterializedClause σ.scoped}
    (h : materializeClause memory (clause.atScope scope) = .ok result)
    (hBelow : HeapScopesBelow scope memory.heap)
    (hInj : IdentityInjective memory.heap) :
    FreshInv (fun v : ScopedVar σ.vars => v.scope = scope)
      { heap := result.memory.heap, varMap := result.varMap } :=
  materializeClause_freshInv h
    (fun v hv => Atom.freeVars_atScope scope clause.head v hv)
    (fun atom hatom v hv => by
      obtain ⟨source, _, rfl⟩ := List.mem_map.mp hatom
      exact Atom.freeVars_atScope scope source v hv)
    (fun a id link hcell => Nat.ne_of_lt (hBelow a id link hcell))
    hInj

/-! ## Stage 5b: the machine preserves descending links

The graph unifier binds the higher-addressed unbound variable toward the
lower one, and otherwise binds variables to constant cells.  On
function-free heaps this keeps every variable chain strictly descending or
terminating at a constant — the well-foundedness that makes finite readback
total.  This section proves that shape is a run invariant of successful
unifier runs. -/

/-- Every bound variable links strictly downward or to a constant cell. -/
def DescendingOrConst {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (address : Addr) (identity : σ.vars) (target : Addr),
    heap[address]? = some (Cell.var identity (some target)) →
    target < address ∨ ∃ symbol, heap[target]? = some (Cell.const symbol)

/-- The readback-wellfoundedness bundle threaded through machine runs. -/
def OrderedFF {σ : LPSignature} (heap : Heap σ) : Prop :=
  DescendingOrConst heap ∧ FunctionFree heap

/-- A machine binding whose target is lower or a constant preserves
descending links. -/
theorem descendingOrConst_write {σ : LPSignature}
    {memory memory' : Memory σ} {bound target : Addr} {identity : σ.vars}
    (hcell : memory.heap[bound]? = some (Cell.var identity none))
    (hw : memory.write bound (Cell.var identity (some target)) =
      .ok memory')
    (hTarget : target < bound ∨
      ∃ symbol, memory.heap[target]? = some (Cell.const symbol))
    (hDesc : DescendingOrConst memory.heap) :
    DescendingOrConst memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  intro a id t hcellA
  rw [hheq] at hcellA
  by_cases haddr : a = bound
  · rw [haddr, heap_set_get_self _ _ hlt] at hcellA
    injection hcellA with hcellA'
    injection hcellA' with hid hlink
    injection hlink with htg
    rcases hTarget with hord | ⟨symbol, hconst⟩
    · rw [haddr, ← htg]
      exact .inl hord
    · refine .inr ⟨symbol, ?_⟩
      rw [hheq, ← htg]
      have hne : target ≠ bound := by
        intro hEq
        rw [hEq, hcell] at hconst
        cases hconst
      rw [heap_set_get_ne _ _ hlt hne]
      exact hconst
  · rw [heap_set_get_ne _ _ hlt haddr] at hcellA
    rcases hDesc a id t hcellA with hord | ⟨symbol, hconst⟩
    · exact .inl hord
    · refine .inr ⟨symbol, ?_⟩
      rw [hheq]
      have hne : t ≠ bound := by
        intro hEq
        rw [hEq, hcell] at hconst
        cases hconst
      rw [heap_set_get_ne _ _ hlt hne]
      exact hconst

/-- Machine bindings never create compound cells. -/
theorem functionFree_write {σ : LPSignature}
    {memory memory' : Memory σ} {bound target : Addr} {identity : σ.vars}
    (hw : memory.write bound (Cell.var identity (some target)) =
      .ok memory')
    (hFF : FunctionFree memory.heap) : FunctionFree memory'.heap := by
  obtain ⟨hlt, hheq⟩ := write_ok_heap hw
  intro a symbol args hcellA
  rw [hheq] at hcellA
  by_cases haddr : a = bound
  · subst haddr
    rw [heap_set_get_self _ _ hlt] at hcellA
    cases hcellA
  · rw [heap_set_get_ne _ _ hlt haddr] at hcellA
    exact hFF a symbol args hcellA

/-- Abbreviation for the wellfoundedness induction hypothesis. -/
def OrderedFFIH (σ : LPSignature) [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (fuel : Nat) : Prop :=
  ∀ (c : Configuration σ) (m : Memory σ), c.phase = .compare →
    runSteps fuel (.running c) = .terminal (.success m) →
    OrderedFF c.memory.heap → OrderedFF m.heap

/-- One ordered binding step followed by a successful run. -/
theorem bindStep_orderedFF {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] {fuel : Nat}
    (ih : OrderedFFIH σ fuel) (c : Configuration σ) (m : Memory σ)
    (rest : List (Addr × Addr)) {bound target : Addr} {identity : σ.vars}
    (hphase : c.phase = .compare)
    (hcellBound : c.memory.heap[bound]? = some (Cell.var identity none))
    (hTarget : target < bound ∨
      ∃ symbol, c.memory.heap[target]? = some (Cell.const symbol))
    (hrun : runSteps fuel (afterBinding c rest bound identity target) =
      .terminal (.success m))
    (hwf : OrderedFF c.memory.heap) : OrderedFF m.heap := by
  simp only [afterBinding] at hrun
  cases hw : c.memory.write bound (Cell.var identity (some target)) with
  | error e =>
      rw [hw] at hrun
      exact absurd hrun (beginRollback_no_success fuel c _ m)
  | ok memory' =>
      rw [hw] at hrun
      exact ih { c with memory := memory', agenda := rest } m hphase hrun
        ⟨descendingOrConst_write hcellBound hw hTarget hwf.1,
          functionFree_write hw hwf.2⟩

/-- **Successful unifier runs preserve descending links and
function-freeness.**  Together with size preservation this is exactly what
finite-readback totality needs at the answer memory. -/
theorem runSteps_success_orderedFF {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] :
    ∀ (fuel : Nat) (c : Configuration σ) (m : Memory σ),
      c.phase = .compare →
      runSteps fuel (.running c) = .terminal (.success m) →
      OrderedFF c.memory.heap → OrderedFF m.heap := by
  intro fuel
  induction fuel with
  | zero =>
      intro c m _ hrun _
      rw [runSteps_zero] at hrun
      simp at hrun
  | succ fuel ih =>
      intro c m hphase hrun hwf
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
              exact hwf
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
                          exact absurd hrun
                            (beginRollback_no_success fuel c _ m)
                      | ok dresR =>
                          cases dresR with
                          | variableCycle a =>
                              simp only [hdr] at hstep
                              cases hstep
                              exact absurd hrun
                                (beginRollback_no_success fuel c _ m)
                          | root rightRoot =>
                              simp only [hdr] at hstep
                              by_cases hroots : leftRoot = rightRoot
                              · rw [if_pos hroots] at hstep
                                cases hstep
                                exact ih { c with agenda := rest, phase := .compare } m rfl hrun hwf
                              · rw [if_neg hroots] at hstep
                                cases hcl : c.memory.heap[leftRoot]? with
                                | none =>
                                    simp only [hcl] at hstep
                                    cases hstep
                                    exact absurd hrun
                                      (beginRollback_no_success fuel c _ m)
                                | some cellL =>
                                    cases hcr :
                                        c.memory.heap[rightRoot]? with
                                    | none =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | none =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                            | some t =>
                                                simp only [hcl, hcr] at hstep
                                                cases hstep
                                                exact absurd hrun
                                                  (beginRollback_no_success
                                                    fuel c _ m)
                                        | const s =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                        | app s a =>
                                            simp only [hcl, hcr] at hstep
                                            cases hstep
                                            exact absurd hrun
                                              (beginRollback_no_success
                                                fuel c _ m)
                                    | some cellR =>
                                        cases cellL with
                                        | var lid linkL =>
                                            cases linkL with
                                            | some t =>
                                                exact absurd hcl
                                                  (deref_root_cell
                                                    c.memory.heap _ l leftRoot
                                                    (deref_root hdl) lid t)
                                            | none =>
                                                cases cellR with
                                                | var rid linkR =>
                                                    cases linkR with
                                                    | none =>
                                                        simp only [hcl, hcr]
                                                          at hstep
                                                        by_cases hord :
                                                            leftRoot < rightRoot
                                                        · rw [if_pos hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_orderedFF
                                                              ih c m rest hphase
                                                              hcr (.inl hord)
                                                              hrun hwf
                                                        · rw [if_neg hord]
                                                            at hstep
                                                          cases hstep
                                                          exact
                                                            bindStep_orderedFF
                                                              ih c m rest hphase
                                                              hcl
                                                              (.inl
                                                                (Nat.lt_of_le_of_ne
                                                                  (Nat.not_lt.mp
                                                                    hord)
                                                                  (fun hEq =>
                                                                    hroots
                                                                      hEq.symm)))
                                                              hrun hwf
                                                    | some t =>
                                                        exact absurd hcr
                                                          (deref_root_cell
                                                            c.memory.heap _ r
                                                            rightRoot
                                                            (deref_root hdr)
                                                            rid t)
                                                | const symbolR =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_orderedFF
                                                      ih c m rest hphase hcl
                                                      (.inr ⟨symbolR, hcr⟩)
                                                      hrun hwf
                                                | app symbolR argsR =>
                                                    exact absurd hcr
                                                      (hwf.2 rightRoot
                                                        symbolR argsR)
                                        | const symbolL =>
                                            cases cellR with
                                            | var rid linkR =>
                                                cases linkR with
                                                | none =>
                                                    simp only [hcl, hcr]
                                                      at hstep
                                                    cases hstep
                                                    exact bindStep_orderedFF
                                                      ih c m rest hphase hcr
                                                      (.inr ⟨symbolL, hcl⟩)
                                                      hrun hwf
                                                | some t =>
                                                    exact absurd hcr
                                                      (deref_root_cell
                                                        c.memory.heap _ r
                                                        rightRoot
                                                        (deref_root hdr)
                                                        rid t)
                                            | const symbolR =>
                                                simp only [hcl, hcr] at hstep
                                                by_cases hsym :
                                                    symbolL = symbolR
                                                · rw [if_pos hsym] at hstep
                                                  cases hstep
                                                  exact ih { c with agenda := rest, phase := .compare } m rfl hrun hwf
                                                · rw [if_neg hsym] at hstep
                                                  cases hstep
                                                  exact absurd hrun
                                                    (beginRollback_no_success
                                                      fuel c _ m)
                                            | app symbolR argsR =>
                                                exact absurd hcr
                                                  (hwf.2 rightRoot
                                                    symbolR argsR)
                                        | app symbolL argsL =>
                                            exact absurd hcl
                                              (hwf.2 leftRoot symbolL argsL)

/-- Entry-point form: successful `startMany` runs preserve the
readback-wellfoundedness bundle. -/
theorem startMany_success_orderedFF {σ : LPSignature}
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (fuel : Nat) (memory₀ : Memory σ) (agenda : List (Addr × Addr))
    (m : Memory σ)
    (hrun : runSteps fuel (startMany memory₀ agenda) =
      .terminal (.success m))
    (hwf : OrderedFF memory₀.heap) : OrderedFF m.heap :=
  runSteps_success_orderedFF fuel
    { memory := memory₀, agenda := agenda, visited := []
      entryMark := memory₀.trailMark, phase := .compare } m rfl hrun hwf

/-! ## Stage 5b: readback totality on ordered function-free heaps

Descending links terminate: every chain strictly decreases its address or
reaches a constant cell.  So finite readback needs no more fuel than the
address itself allows, and `notFinite` is impossible — the discharge, not
an assumption, of every finite-readback side condition in the endpoint. -/

/-- On a descending, function-free heap every in-bounds address reads back
with fuel `address + 2`. -/
theorem readTermFuel_total_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) :
    ∀ (address : Addr), address < heap.size →
      ∃ term, readTermFuel heap (address + 2) address = .ok term := by
  intro address
  induction address using Nat.strong_induction_on with
  | _ address ih =>
      intro ha
      obtain ⟨cell, hcell⟩ := getElem?_some_of_lt ha
      cases cell with
      | var identity link =>
          cases link with
          | none =>
              exact ⟨.var identity,
                readTermFuel_unbound heap _ address identity hcell⟩
          | some target =>
              rw [readTermFuel_link heap (address + 1) address target
                identity hcell]
              rcases hwf.1 address identity target hcell with
                hord | ⟨symbol, hconst⟩
              · obtain ⟨term, hterm⟩ :=
                  ih target hord (Nat.lt_trans hord ha)
                exact ⟨term, readTermFuel_mono_le heap
                  (Nat.succ_le_succ (Nat.succ_le_of_lt hord))
                  target term hterm⟩
              · exact ⟨.const symbol,
                  readTermFuel_const heap address target symbol hconst⟩
      | const symbol =>
          exact ⟨.const symbol,
            readTermFuel_const heap _ address symbol hcell⟩
      | app symbol args =>
          exact absurd hcell (hwf.2 address symbol args)

/-- Every in-bounds address of an ordered function-free heap has a finite
readback at the standard budget. -/
theorem readTerm_total_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) {address : Addr} (ha : address < heap.size) :
    ∃ term, Heap.readTerm heap address = .ok term := by
  obtain ⟨term, hterm⟩ := readTermFuel_total_of_orderedFF hwf address ha
  exact ⟨term, readTermFuel_mono_le heap
    (Nat.succ_le_succ (Nat.succ_le_of_lt ha)) address term hterm⟩

/-- Any variable support whose identities have cells is readable on an
ordered function-free heap. -/
theorem readableOn_of_orderedFF {σ : LPSignature} {heap : Heap σ}
    (hwf : OrderedFF heap) (support : List σ.vars)
    (hcells : ∀ v ∈ support, ∃ (address : Addr) (link : Option Addr),
      heap[address]? = some (Cell.var v link)) :
    ReadableOn heap support := by
  intro v hv
  obtain ⟨address, link, hcell⟩ := hcells v hv
  have hex : ∃ a : Addr, ∃ link, heap[a]? = some (Cell.var v link) :=
    ⟨address, link, hcell⟩
  have hcellOf : cellOf heap v = some hex.choose := by
    unfold cellOf
    rw [dif_pos hex]
  obtain ⟨link', hchoose⟩ := hex.choose_spec
  obtain ⟨term, hterm⟩ :=
    readTerm_total_of_orderedFF hwf (lt_of_getElem?_some hchoose)
  exact ⟨hex.choose, term, hcellOf, hterm⟩

end RuntimeUnificationSoundness
end Mettapedia.Logic.LP

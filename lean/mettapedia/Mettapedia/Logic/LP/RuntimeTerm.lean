import Mettapedia.Logic.LP.Core
import Mathlib.Init
import Mathlib.Data.List.FinRange

/-!
# Runtime term graphs for Prolog execution

`Logic.LP.Term` remains the finite, inductive term language used by the LP
theory.  An executable SWI-compatible Prolog engine additionally needs a
finite *graph* representation: an unbound variable is a heap cell, binding a
variable redirects that cell, and a compound may point back to a variable that
points to the compound.  The last case represents rational trees when
`occurs_check=false`.

The layout follows the semantic spine of SWI-Prolog V10.1.9 rather than its C
word tagging.  In particular, bindings are destructive heap updates recorded
on a trail and choice points retain both heap and trail tops.  The source anchors are
`src/pl-prims.c` (`unify_simple_ptrs`, `do_unify`, `unify_ptrs`) and
`src/pl-wam.c` (trail unwinding at choice points), pinned by
`Logic/Prolog/SWI/SWI_PROVENANCE.json`.

This file only defines the shared LP runtime substrate.  The unification
algorithm and Prolog control machine are layered on it.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeTerm

/-- Heap address.  Addresses remain stable while a query is live. -/
abbrev Addr := Nat

/-- A cell in the runtime term graph.

An unbound variable has `link = none`.  Binding updates the cell to point at a
term root.  Keeping the source-level identity alongside the link makes the
finite LP embedding and alpha-normalized answer projection explicit; it does
not affect dereferencing. -/
inductive Cell (σ : LPSignature) where
  | var (identity : σ.vars) (link : Option Addr)
  | const (symbol : σ.constants)
  | app (symbol : σ.functionSymbols) (args : Array Addr)

/-- All outgoing heap references carried by a cell. -/
def Cell.references {σ : LPSignature} : Cell σ → List Addr
  | .var _ none => []
  | .var _ (some target) => [target]
  | .const _ => []
  | .app _ args => args.toList

/-- A runtime compound must carry exactly the arity declared by its signature. -/
def Cell.ShapeCorrect {σ : LPSignature} : Cell σ → Prop
  | .var _ _ => True
  | .const _ => True
  | .app symbol args => args.size = σ.functionArity symbol

/-- Executable form of `ShapeCorrect`. -/
def Cell.checkShape {σ : LPSignature} : Cell σ → Bool
  | .var _ _ => true
  | .const _ => true
  | .app symbol args => args.size == σ.functionArity symbol

theorem Cell.shapeCorrect_of_check {σ : LPSignature} {cell : Cell σ}
    (h : cell.checkShape = true) : cell.ShapeCorrect := by
  cases cell with
  | var => trivial
  | const => trivial
  | app symbol args =>
      exact beq_iff_eq.mp h

/-- The mutable graph portion of the runtime state. -/
abbrev Heap (σ : LPSignature) := Array (Cell σ)

namespace Heap

/-- Every edge in a well-formed heap points to an allocated cell. -/
def WellFormed {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (address : Addr) (cell : Cell σ), heap[address]? = some cell →
    ∀ target ∈ Cell.references cell, target < heap.size

/-- Every compound stored in the heap agrees with the signature arity. -/
def WellShaped {σ : LPSignature} (heap : Heap σ) : Prop :=
  ∀ (address : Addr) (cell : Cell σ), heap[address]? = some cell →
    cell.ShapeCorrect

/-- A cell may be appended when all of its references are already allocated.
This is the usual WAM construction order for a freshly materialized term. -/
def MayAppend {σ : LPSignature} (heap : Heap σ) (cell : Cell σ) : Prop :=
  ∀ target ∈ Cell.references cell, target < heap.size

/-- Executable validation of `WellFormed`.  Keeping the checker next to the
proposition makes the runtime boundary explicit: callers receive a graph only
after this finite check succeeds. -/
def checkWellFormed {σ : LPSignature} (heap : Heap σ) : Bool :=
  heap.all fun cell =>
    (Cell.references cell).all fun target => target < heap.size

def checkWellShaped {σ : LPSignature} (heap : Heap σ) : Bool :=
  heap.all Cell.checkShape

theorem wellFormed_of_check {σ : LPSignature} {heap : Heap σ}
    (hCheck : heap.checkWellFormed = true) : heap.WellFormed := by
  intro address cell hCell target hTarget
  obtain ⟨hAddress, hFound⟩ := Array.getElem?_eq_some_iff.mp hCell
  have hAll := Array.all_eq_true.mp hCheck address hAddress
  rw [hFound] at hAll
  exact of_decide_eq_true (List.all_eq_true.mp hAll target hTarget)

theorem wellShaped_of_check {σ : LPSignature} {heap : Heap σ}
    (hCheck : heap.checkWellShaped = true) : heap.WellShaped := by
  intro address cell hCell
  obtain ⟨hAddress, hFound⟩ := Array.getElem?_eq_some_iff.mp hCell
  have hShape := Array.all_eq_true.mp hCheck address hAddress
  rw [hFound] at hShape
  exact Cell.shapeCorrect_of_check hShape

@[simp]
theorem empty_wellFormed {σ : LPSignature} : WellFormed (#[] : Heap σ) := by
  unfold WellFormed
  intro address cell h
  simp at h

/-- Append a cell and return its stable address.  Callers that construct
well-formed terms establish `MayAppend`; runtime-facing allocation uses
`Memory.allocate` below, which checks this condition. -/
def append {σ : LPSignature} (heap : Heap σ) (cell : Cell σ) : Addr × Heap σ :=
  (heap.size, heap.push cell)

@[simp]
theorem append_address {σ : LPSignature} (heap : Heap σ) (cell : Cell σ) :
    (append heap cell).1 = heap.size := rfl

@[simp]
theorem append_size {σ : LPSignature} (heap : Heap σ) (cell : Cell σ) :
    (append heap cell).2.size = heap.size + 1 := by
  simp [append]

theorem append_root_valid {σ : LPSignature} (heap : Heap σ) (cell : Cell σ) :
    (append heap cell).1 < (append heap cell).2.size := by
  simp [append]

theorem append_wellFormed {σ : LPSignature} {heap : Heap σ} {cell : Cell σ}
    (hHeap : heap.WellFormed) (hCell : heap.MayAppend cell) :
    (heap.append cell).2.WellFormed := by
  unfold WellFormed
  intro address found hFound target hTarget
  simp only [Heap.append, Array.getElem?_push] at hFound
  simp only [Heap.append, Array.size_push]
  by_cases hAddress : address = heap.size
  · subst address
    simp at hFound
    have hCellEq : cell = found := hFound
    subst found
    have := hCell target hTarget
    exact Nat.lt_trans this (Nat.lt_succ_self heap.size)
  · simp only [if_neg hAddress] at hFound
    have := hHeap address found hFound target hTarget
    exact Nat.lt_trans this (Nat.lt_succ_self heap.size)

theorem append_wellShaped {σ : LPSignature} {heap : Heap σ} {cell : Cell σ}
    (hHeap : heap.WellShaped) (hCell : cell.ShapeCorrect) :
    (heap.append cell).2.WellShaped := by
  intro address found hFound
  simp only [Heap.append, Array.getElem?_push] at hFound
  by_cases hAddress : address = heap.size
  · subst address
    simp at hFound
    cases hFound
    exact hCell
  · simp only [if_neg hAddress] at hFound
    exact hHeap address found hFound

end Heap

/-- A trailed destructive update.  `previous` is sufficient to restore the
heap exactly when backtracking reaches the associated mark. -/
structure TrailEntry (σ : LPSignature) where
  address : Addr
  previous : Cell σ

/-- Heap plus the chronological trail of destructive updates. -/
structure Memory (σ : LPSignature) where
  heap : Heap σ
  trail : Array (TrailEntry σ)

private def Cell.decisionCode {σ : LPSignature} : Cell σ →
    (σ.vars × Option Addr) ⊕ (σ.constants ⊕ (σ.functionSymbols × Array Addr))
  | .var identity link => .inl (identity, link)
  | .const symbol => .inr (.inl symbol)
  | .app symbol args => .inr (.inr (symbol, args))

private theorem Cell.decisionCode_injective {σ : LPSignature} :
    Function.Injective (Cell.decisionCode (σ := σ)) := by
  intro left right h
  cases left <;> cases right <;> simp_all [Cell.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (Cell σ) :=
  Cell.decisionCode_injective.decidableEq

private def TrailEntry.decisionCode {σ : LPSignature}
    (entry : TrailEntry σ) : Addr × Cell σ :=
  (entry.address, entry.previous)

private theorem TrailEntry.decisionCode_injective {σ : LPSignature} :
    Function.Injective (TrailEntry.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [TrailEntry.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (TrailEntry σ) :=
  TrailEntry.decisionCode_injective.decidableEq

private def Memory.decisionCode {σ : LPSignature}
    (memory : Memory σ) : Heap σ × Array (TrailEntry σ) :=
  (memory.heap, memory.trail)

private theorem Memory.decisionCode_injective {σ : LPSignature} :
    Function.Injective (Memory.decisionCode (σ := σ)) := by
  intro left right h
  cases left
  cases right
  simp_all [Memory.decisionCode]

instance {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : DecidableEq (Memory σ) :=
  Memory.decisionCode_injective.decidableEq

/-- Structured failures of the total runtime-memory API. -/
inductive MemoryError where
  | invalidAddress (address : Addr)
  | danglingReference (address : Addr)
  | variableReferenceCycle (address : Addr)
  | invalidTrailMark (mark current : Nat)
  | invalidHeapMark (mark current : Nat)
  | corruptTrailAddress (address : Addr)
  | illShapedCell
  | illFormedHeap
deriving DecidableEq, Repr

namespace Memory

/-- Empty runtime memory. -/
def empty (σ : LPSignature) : Memory σ :=
  { heap := #[], trail := #[] }

/-- A transactional unification records this trail position. -/
def trailMark {σ : LPSignature} (memory : Memory σ) : Nat :=
  memory.trail.size

/-- A Prolog choice point records both arena and trail tops.  Restoring only
the trail would leak all term copies allocated after the choice. -/
structure Checkpoint where
  heapSize : Nat
  trailSize : Nat
deriving DecidableEq, Repr

def checkpoint {σ : LPSignature} (memory : Memory σ) : Checkpoint := {
  heapSize := memory.heap.size
  trailSize := memory.trail.size
}

/-- Allocate a cell after dynamically checking its declared arity and that
every outgoing reference already exists.  Unsupported/corrupt input is visible
as an error rather than creating an ill-formed heap. -/
def allocate {σ : LPSignature} (memory : Memory σ) (cell : Cell σ) :
    Except MemoryError (Addr × Memory σ) :=
  if cell.checkShape then
    if (Cell.references cell).all (fun address => address < memory.heap.size) then
      let result := memory.heap.append cell
      .ok (result.1, { memory with heap := result.2 })
    else
      match (Cell.references cell).find? (fun address => decide (memory.heap.size ≤ address)) with
      | some address => .error (.danglingReference address)
      | none => .error (.danglingReference memory.heap.size)
  else
    .error .illShapedCell

/-- Destructively update one allocated cell and trail its previous contents. -/
def write {σ : LPSignature} (memory : Memory σ) (address : Addr) (cell : Cell σ) :
    Except MemoryError (Memory σ) :=
  if h : address < memory.heap.size then
    if cell.checkShape then
      if (Cell.references cell).all (fun target => target < memory.heap.size) then
        let previous := memory.heap[address]
        .ok {
          heap := memory.heap.set address cell
          trail := memory.trail.push { address, previous }
        }
      else
        match (Cell.references cell).find? (fun target => decide (memory.heap.size ≤ target)) with
        | some target => .error (.danglingReference target)
        | none => .error (.danglingReference memory.heap.size)
    else
      .error .illShapedCell
  else
    .error (.invalidAddress address)

/-- Every write appended since `trailMark` targets an address outside the
protected heap prefix.  This is the graph-runtime form of single-sided head
matching: freshly materialized clause cells may be bound, but no cell owned by
the caller may be changed.  A stale mark fails closed. -/
def protectsHeapPrefixSince {σ : LPSignature} (memory : Memory σ)
    (trailMark protectedHeapSize : Nat) : Bool :=
  decide (trailMark ≤ memory.trail.size) &&
    (memory.trail.toList.drop trailMark).all fun entry =>
      decide (protectedHeapSize ≤ entry.address)

/-- The executable prefix check is exactly a valid trail suffix plus the
pointwise address floor; it does not infer acceptance from trail length alone. -/
theorem protectsHeapPrefixSince_eq_true_iff {σ : LPSignature}
    (memory : Memory σ) (trailMark protectedHeapSize : Nat) :
    memory.protectsHeapPrefixSince trailMark protectedHeapSize = true ↔
      trailMark ≤ memory.trail.size ∧
        ∀ entry ∈ memory.trail.toList.drop trailMark,
          protectedHeapSize ≤ entry.address := by
  simp [protectsHeapPrefixSince]

/-- With no writes after a valid mark, single-sided matching accepts
regardless of the protected prefix size. -/
@[simp]
theorem protectsHeapPrefixSince_at_end {σ : LPSignature}
    (memory : Memory σ) (protectedHeapSize : Nat) :
    memory.protectsHeapPrefixSince memory.trail.size protectedHeapSize = true := by
  simp only [protectsHeapPrefixSince, le_refl, decide_true, Bool.true_and]
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

/-- Undo exactly the most recent trailed write.  Query-level rollback repeats
this operation until it reaches the choice-point mark, making rollback itself
available as a visible microstep. -/
def undoLast {σ : LPSignature} (memory : Memory σ) :
    Except MemoryError (Memory σ) :=
  match memory.trail.back? with
  | none => .error (.invalidTrailMark 0 0)
  | some entry =>
      if h : entry.address < memory.heap.size then
        .ok {
          heap := memory.heap.set entry.address entry.previous
          trail := memory.trail.pop
        }
      else
        .error (.corruptTrailAddress entry.address)

/-- Repeat the same one-entry rollback step `count` times. -/
def undoN {σ : LPSignature} : Nat → Memory σ → Except MemoryError (Memory σ)
  | 0, memory => .ok memory
  | count + 1, memory => do
      let previous ← memory.undoLast
      undoN count previous

/-- Evidence that `after` was obtained from `before` by exactly `count`
successful trailed writes.  This is a local history certificate for rollback,
not a second operational semantics. -/
inductive WritesN {σ : LPSignature} : Nat → Memory σ → Memory σ → Prop
  | refl (memory : Memory σ) : WritesN 0 memory memory
  | tail {count : Nat} {before middle after : Memory σ}
      {address : Addr} {cell : Cell σ}
      (history : WritesN count before middle)
      (write : middle.write address cell = .ok after) :
      WritesN (count + 1) before after

def unwindLoop {σ : LPSignature} : Nat → Memory σ → Except MemoryError (Memory σ)
  | 0, memory => .ok memory
  | steps + 1, memory =>
      match memory.trail.back? with
      | none => .error (.invalidTrailMark steps 0)
      | some entry =>
          if h : entry.address < memory.heap.size then
            unwindLoop steps {
              heap := memory.heap.set entry.address entry.previous
              trail := memory.trail.pop
            }
          else
            .error (.corruptTrailAddress entry.address)

/-- Restore all bindings made after `mark`.  This is the transaction primitive
used by unification; query choice points use `restore` below. -/
def unwindTrail {σ : LPSignature} (memory : Memory σ) (mark : Nat) :
    Except MemoryError (Memory σ) :=
  if _h : mark ≤ memory.trail.size then
    unwindLoop (memory.trail.size - mark) memory
  else
    .error (.invalidTrailMark mark memory.trail.size)

private theorem unwindLoop_heap_size {σ : LPSignature} {steps : Nat}
    {memory restored : Memory σ}
    (hUnwind : unwindLoop steps memory = .ok restored) :
    restored.heap.size = memory.heap.size := by
  induction steps generalizing memory with
  | zero =>
      simp only [unwindLoop] at hUnwind
      cases hUnwind
      rfl
  | succ steps ih =>
      simp only [unwindLoop] at hUnwind
      cases hBack : memory.trail.back? with
      | none => simp [hBack] at hUnwind
      | some entry =>
          simp only [hBack] at hUnwind
          split at hUnwind
          · have hSize := ih hUnwind
            simpa using hSize
          · contradiction

theorem unwindTrail_heap_size {σ : LPSignature} {memory restored : Memory σ}
    {mark : Nat} (hUnwind : memory.unwindTrail mark = .ok restored) :
    restored.heap.size = memory.heap.size := by
  simp only [unwindTrail] at hUnwind
  split at hUnwind
  · exact unwindLoop_heap_size hUnwind
  · contradiction

/-- Restore a full query checkpoint: unwind bindings first, then reclaim every
heap cell allocated after the saved heap top. -/
def restore {σ : LPSignature} (memory : Memory σ) (saved : Checkpoint) :
    Except MemoryError (Memory σ) :=
  if saved.heapSize ≤ memory.heap.size then
    match memory.unwindTrail saved.trailSize with
    | .error error => .error error
    | .ok unwound =>
        let restored : Memory σ := {
          heap := unwound.heap.extract 0 saved.heapSize
          trail := unwound.trail
        }
        if restored.heap.checkWellFormed then
          if restored.heap.checkWellShaped then
            .ok restored
          else
            .error .illFormedHeap
        else
          .error .illFormedHeap
  else
    .error (.invalidHeapMark saved.heapSize memory.heap.size)

/-- Restore a query checkpoint while retaining a monotone prefix of the heap.
This is the canonical runtime analogue of SWI-Prolog's non-backtrackable
global-stack frontier: ordinary bindings are still unwound to the saved trail
mark, but cells below `heapFloor` cannot be reclaimed by a choice point that
predates their persistent allocation. -/
def restorePreserving {σ : LPSignature} (memory : Memory σ)
    (heapFloor : Nat) (saved : Checkpoint) : Except MemoryError (Memory σ) :=
  memory.restore { saved with heapSize := max saved.heapSize heapFloor }

@[simp]
theorem restorePreserving_zero {σ : LPSignature} (memory : Memory σ)
    (saved : Checkpoint) :
    memory.restorePreserving 0 saved = memory.restore saved := by
  simp [restorePreserving]

/-- A successful protected restore lands at exactly the larger of the saved
arena top and the persistent floor. -/
theorem restorePreserving_heap_size {σ : LPSignature}
    {memory restored : Memory σ} {heapFloor : Nat} {saved : Checkpoint}
    (hRestore : memory.restorePreserving heapFloor saved = .ok restored) :
    restored.heap.size = max saved.heapSize heapFloor := by
  simp only [restorePreserving, restore] at hRestore
  split at hRestore
  · next hHeap =>
    split at hRestore
    · next error => contradiction
    · next unwound hUnwind =>
      have hUnwindSize := unwindTrail_heap_size hUnwind
      split at hRestore
      · next hWellFormed =>
        split at hRestore
        · cases hRestore
          simp
          omega
        · contradiction
      · contradiction
  · contradiction

theorem le_restorePreserving_heap_size {σ : LPSignature}
    {memory restored : Memory σ} {heapFloor : Nat} {saved : Checkpoint}
    (hRestore : memory.restorePreserving heapFloor saved = .ok restored) :
    heapFloor ≤ restored.heap.size := by
  rw [restorePreserving_heap_size hRestore]
  exact Nat.le_max_right _ _

@[simp]
theorem empty_trailMark {σ : LPSignature} : (empty σ).trailMark = 0 := rfl

@[simp]
theorem unwindTrail_current {σ : LPSignature} (memory : Memory σ) :
    memory.unwindTrail memory.trailMark = .ok memory := by
  simp [unwindTrail, trailMark, unwindLoop]

theorem allocate_trailMark {σ : LPSignature} {memory memory' : Memory σ}
    {cell : Cell σ} {address : Addr}
    (h : memory.allocate cell = .ok (address, memory')) :
    memory'.trailMark = memory.trailMark := by
  simp only [allocate] at h
  split at h
  · split at h
    · cases h
      simp [trailMark]
    · split at h <;> contradiction
  · contradiction

theorem allocate_heap_size_succ {σ : LPSignature} {memory memory' : Memory σ}
    {cell : Cell σ} {address : Addr}
    (h : memory.allocate cell = .ok (address, memory')) :
    memory'.heap.size = memory.heap.size + 1 := by
  simp only [allocate] at h
  split at h
  · split at h
    · cases h
      simp
    · split at h <;> contradiction
  · contradiction

theorem allocate_wellFormed {σ : LPSignature} {memory memory' : Memory σ}
    {cell : Cell σ} {address : Addr}
    (hMemory : memory.heap.WellFormed)
    (h : memory.allocate cell = .ok (address, memory')) :
    memory'.heap.WellFormed := by
  simp only [allocate] at h
  split at h
  next _hShape =>
    split at h
    next hReferences =>
      cases h
      apply Heap.append_wellFormed hMemory
      intro target hTarget
      have hAll := List.all_eq_true.mp hReferences target hTarget
      simpa using hAll
    next _ =>
      split at h <;> contradiction
  next _ =>
    contradiction

theorem allocate_wellShaped {σ : LPSignature} {memory memory' : Memory σ}
    {cell : Cell σ} {address : Addr}
    (hMemory : memory.heap.WellShaped)
    (h : memory.allocate cell = .ok (address, memory')) :
    memory'.heap.WellShaped := by
  simp only [allocate] at h
  split at h
  next hShape =>
    split at h
    · cases h
      exact Heap.append_wellShaped hMemory (Cell.shapeCorrect_of_check hShape)
    · split at h <;> contradiction
  next _ =>
    contradiction

theorem write_trailMark_succ {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    memory'.trailMark = memory.trailMark + 1 := by
  simp only [write] at h
  split at h
  · split at h
    · split at h
      · cases h
        simp [trailMark]
      · split at h <;> contradiction
    · contradiction
  · contradiction

theorem write_heap_size {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    memory'.heap.size = memory.heap.size := by
  simp only [write] at h
  split at h
  · split at h
    · split at h
      · cases h
        simp
      · split at h <;> contradiction
    · contradiction
  · contradiction

theorem write_wellFormed {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (hMemory : memory.heap.WellFormed)
    (h : memory.write address cell = .ok memory') :
    memory'.heap.WellFormed := by
  simp only [write] at h
  split at h
  next hAddress =>
    split at h
    next _hShape =>
      split at h
      next hReferences =>
        cases h
        intro foundAddress foundCell hFound target hTarget
        rw [Array.getElem?_set hAddress] at hFound
        split at hFound
        next hSame =>
          cases hFound
          have hAll := List.all_eq_true.mp hReferences target hTarget
          simpa [Array.size_set] using (of_decide_eq_true hAll)
        next hDifferent =>
          have hOld := hMemory foundAddress foundCell hFound target hTarget
          simpa [Array.size_set] using hOld
      next _ =>
        split at h <;> contradiction
    next _ =>
      contradiction
  · contradiction

theorem write_wellShaped {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (hMemory : memory.heap.WellShaped)
    (h : memory.write address cell = .ok memory') :
    memory'.heap.WellShaped := by
  simp only [write] at h
  split at h
  next hAddress =>
    split at h
    next hShape =>
      split at h
      · cases h
        intro foundAddress foundCell hFound
        rw [Array.getElem?_set hAddress] at hFound
        split at hFound
        next _ =>
          cases hFound
          exact Cell.shapeCorrect_of_check hShape
        next _ =>
          exact hMemory foundAddress foundCell hFound
      · split at h <;> contradiction
    next _ =>
      contradiction
  · contradiction

theorem undoLast_write {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    memory'.undoLast = .ok memory := by
  simp only [write] at h
  split at h
  next hAddress =>
    split at h
    next _hShape =>
      split at h
      next _hReferences =>
        cases h
        simp [undoLast, hAddress]
      next _ =>
        split at h <;> contradiction
    next _ => contradiction
  · contradiction

theorem WritesN.trailMark_exact {σ : LPSignature} {count : Nat}
    {before after : Memory σ} (writes : WritesN count before after) :
    after.trailMark = before.trailMark + count := by
  induction writes with
  | refl => simp
  | tail history write ih =>
      rw [write_trailMark_succ write, ih]
      omega

/-- Any finite sequence of successful writes is exactly reversible. -/
theorem WritesN.undoN_exact {σ : LPSignature} {count : Nat}
    {before after : Memory σ} (writes : WritesN count before after) :
    after.undoN count = .ok before := by
  induction writes with
  | refl => rfl
  | tail history write ih =>
      simp only [undoN, undoLast_write write]
      exact ih

/-- A single trailed write is exactly undone at the preceding choice-point
mark.  This is the smallest non-vacuous rollback law used by the later
choice-point machine. -/
theorem unwindTrail_write {σ : LPSignature} {memory memory' : Memory σ}
    {address : Addr} {cell : Cell σ}
    (h : memory.write address cell = .ok memory') :
    memory'.unwindTrail memory.trailMark = .ok memory := by
  simp only [write] at h
  split at h
  next hAddress =>
    split at h
    next _hShape =>
      split at h
      next _hReferences =>
        cases h
        simp [unwindTrail, trailMark, unwindLoop, hAddress]
      next _ =>
        split at h <;> contradiction
    next _ => contradiction
  · contradiction

end Memory

/-- Result of bounded variable-chain dereferencing.  A rational tree cycle
through a compound is not a variable-chain cycle: dereferencing stops at the
compound root. -/
inductive DerefResult where
  | root (address : Addr)
  | variableCycle (address : Addr)
deriving DecidableEq, Repr

namespace Heap

def derefLoop {σ : LPSignature} (heap : Heap σ) : Nat → Addr →
    Except MemoryError DerefResult
  | 0, address => .ok (.variableCycle address)
  | fuel + 1, address =>
      match heap[address]? with
      | none => .error (.invalidAddress address)
      | some (.var _ (some target)) => derefLoop heap fuel target
      | some _ => .ok (.root address)

/-- Follow variable links.  More than `heap.size` links necessarily revisits a
cell, so `heap.size + 1` is a complete bound for detecting corrupt variable-only
cycles. -/
def deref {σ : LPSignature} (heap : Heap σ) (address : Addr) :
    Except MemoryError DerefResult :=
  derefLoop heap (heap.size + 1) address

end Heap

/-! ## Embedding finite LP terms -/

/-- Builder state for embedding an inductive LP term into a shared graph.
Repeated source variables reuse the same heap address. -/
structure BuildState (σ : LPSignature) where
  heap : Heap σ
  varMap : List (σ.vars × Addr)

namespace BuildState

def empty (σ : LPSignature) : BuildState σ :=
  { heap := #[], varMap := [] }

def allocate {σ : LPSignature} (cell : Cell σ) : StateM (BuildState σ) Addr := do
  let state ← get
  let address := state.heap.size
  set { state with heap := state.heap.push cell }
  pure address

def lookupVariable {σ : LPSignature} [DecidableEq σ.vars]
    (varMap : List (σ.vars × Addr)) (varId : σ.vars) : Option Addr :=
  (varMap.find? fun entry => decide (entry.1 = varId)).map Prod.snd

/-- Embed a finite term.  Compound cells are allocated after their children;
therefore every new compound reference points backward to an allocated cell. -/
def embedAux {σ : LPSignature} [DecidableEq σ.vars] :
    Term σ → StateM (BuildState σ) Addr
  | .var varId => do
      let state ← get
      match lookupVariable state.varMap varId with
      | some address => pure address
      | none =>
          let address ← allocate (.var varId none)
          modify fun next => { next with varMap := (varId, address) :: next.varMap }
          pure address
  | .const symbol => allocate (.const symbol)
  | .app symbol args => do
      let addresses ← (List.finRange (σ.functionArity symbol)).mapM fun index =>
        embedAux (args index)
      allocate (.app symbol addresses.toArray)
termination_by term => term.size
decreasing_by
  exact Term.size_subterm _

end BuildState

/-- A finite LP term embedded into a runtime graph. -/
structure Embedded (σ : LPSignature) where
  heap : Heap σ
  root : Addr
  varMap : List (σ.vars × Addr)

/-- Construct the candidate graph before validating its public invariants. -/
def embedCandidate {σ : LPSignature} [DecidableEq σ.vars]
    (term : Term σ) : Embedded σ :=
  let result := BuildState.embedAux term |>.run (BuildState.empty σ)
  { heap := result.2.heap, root := result.1, varMap := result.2.varMap }

/-- Embed a finite LP term into an initially empty runtime graph.

The graph is exposed only when its root exists and all references are in
bounds.  This checked boundary is intentionally total even if a future change
to the builder introduces a malformed candidate. -/
def embed {σ : LPSignature} [DecidableEq σ.vars] (term : Term σ) :
    Except MemoryError (Embedded σ) :=
  let candidate := embedCandidate term
  if candidate.root < candidate.heap.size then
    if candidate.heap.checkWellFormed then
      if candidate.heap.checkWellShaped then
        .ok candidate
      else
        .error .illFormedHeap
    else
      .error .illFormedHeap
  else
    .error (.invalidAddress candidate.root)

theorem embed_root_valid {σ : LPSignature} [DecidableEq σ.vars]
    {term : Term σ} {result : Embedded σ}
    (h : embed term = .ok result) : result.root < result.heap.size := by
  simp only [embed] at h
  split at h
  next hRoot =>
    split at h
    · split at h
      · cases h
        exact hRoot
      · contradiction
    · contradiction
  · contradiction

theorem embed_wellFormed {σ : LPSignature} [DecidableEq σ.vars]
    {term : Term σ} {result : Embedded σ}
    (h : embed term = .ok result) : result.heap.WellFormed := by
  simp only [embed] at h
  split at h
  · split at h
    next hCheck =>
      split at h
      · cases h
        exact Heap.wellFormed_of_check hCheck
      · contradiction
    · contradiction
  · contradiction

theorem embed_wellShaped {σ : LPSignature} [DecidableEq σ.vars]
    {term : Term σ} {result : Embedded σ}
    (h : embed term = .ok result) : result.heap.WellShaped := by
  simp only [embed] at h
  split at h
  · split at h
    · split at h
      next hShape =>
        cases h
        exact Heap.wellShaped_of_check hShape
      · contradiction
    · contradiction
  · contradiction

end RuntimeTerm
end Mettapedia.Logic.LP

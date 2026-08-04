import Mettapedia.Logic.LP.RuntimeTerm

/-!
# Runtime term graph regressions

These fixtures distinguish the graph runtime from both a tree-only encoding
and an untrailed destructive store:

* two occurrences of one LP variable share one heap address;
* `X = loop(X)` is representable without an occurs check;
* dereferencing the rational tree stops at its compound root; and
* unwinding the trail restores the exact unbound-variable heap; and
* pointer-safe but arity-invalid cells are rejected at allocation.
-/

namespace Mettapedia.Logic.LP.RuntimeTermRegression

open RuntimeTerm

inductive RConst where
  | atom
deriving DecidableEq, Repr

inductive RVar where
  | x
deriving DecidableEq, Repr

inductive RRel where
  | p
deriving DecidableEq, Repr

inductive RFun where
  | pair
  | loop
deriving DecidableEq, Repr

def rSig : LPSignature where
  constants := RConst
  vars := RVar
  relationSymbols := RRel
  relationArity := fun _ => 0
  functionSymbols := RFun
  functionArity
    | .pair => 2
    | .loop => 1

instance : DecidableEq rSig.vars := inferInstanceAs (DecidableEq RVar)
instance : DecidableEq rSig.constants := inferInstanceAs (DecidableEq RConst)
instance : DecidableEq rSig.functionSymbols := inferInstanceAs (DecidableEq RFun)

def sharedVariableTerm : Term rSig :=
  .app .pair (fun _ => .var .x)

/-- The two syntactic occurrences allocate one variable cell, not two.  The
exact result also proves that the checked public boundary accepts this
non-ground shared term. -/
theorem finite_embedding_preserves_variable_sharing :
    RuntimeTerm.embed sharedVariableTerm = .ok {
      heap := #[.var .x none, .app .pair #[0, 0]]
      root := 1
      varMap := [(.x, 0)]
    } := by
  simp [RuntimeTerm.embed, RuntimeTerm.embedCandidate, sharedVariableTerm,
    BuildState.embedAux, BuildState.empty, BuildState.allocate,
    BuildState.lookupVariable, Heap.checkWellFormed, Heap.checkWellShaped,
    Cell.checkShape, rSig, List.finRange]
  rfl

/-- Heap before the rational binding. -/
def rationalBase : Memory rSig := {
  heap := #[.var .x none, .app .loop #[0]]
  trail := #[]
}

/-- Heap after binding `X` to `loop(X)`. -/
def rationalBound : Memory rSig := {
  heap := #[.var .x (some 1), .app .loop #[0]]
  trail := #[{ address := 0, previous := .var .x none }]
}

theorem rational_binding_is_a_real_trailed_write :
    rationalBase.write 0 (.var .x (some 1)) = .ok rationalBound := by
  rfl

/-- A compound cycle is a valid rational tree, not a variable-link cycle. -/
theorem rational_cycle_derefs_to_compound :
    rationalBound.heap.deref 0 = .ok (.root 1) := by
  rfl

/-- Backtracking restores the exact state before the rational binding. -/
theorem rational_binding_unwinds_exactly :
    rationalBound.unwindTrail rationalBase.trailMark = .ok rationalBase := by
  exact Memory.unwindTrail_write rational_binding_is_a_real_trailed_write

def checkpointBase : Memory rSig := {
  heap := #[.var .x none]
  trail := #[]
}

def afterCheckpointAllocation : Memory rSig := {
  heap := #[.var .x none, .const .atom]
  trail := #[]
}

def afterCheckpointWrite : Memory rSig := {
  heap := #[.var .x (some 1), .const .atom]
  trail := #[{ address := 0, previous := .var .x none }]
}

theorem checkpoint_fixture_allocates :
    checkpointBase.allocate (.const .atom) = .ok (1, afterCheckpointAllocation) := by
  rfl

/-- Reference validity alone is insufficient: `pair/2` cannot be allocated
with one argument even though that argument points to an existing cell. -/
theorem wrong_arity_allocation_is_rejected :
    checkpointBase.allocate (.app .pair #[0]) = .error .illShapedCell := by
  rfl

theorem checkpoint_fixture_writes :
    afterCheckpointAllocation.write 0 (.var .x (some 1)) =
      .ok afterCheckpointWrite := by
  rfl

/-- A full choice checkpoint restores both the overwritten variable and the
arena top, reclaiming the constant allocated after entry. -/
theorem checkpoint_restores_heap_and_trail :
    afterCheckpointWrite.restore checkpointBase.checkpoint = .ok checkpointBase := by
  simp [Memory.restore, Memory.checkpoint, Memory.unwindTrail, Memory.unwindLoop,
    checkpointBase, afterCheckpointWrite, Heap.checkWellFormed,
    Heap.checkWellShaped, Cell.checkShape, Cell.references]

/-- The same fixture is non-degenerate: its compound points back to the bound
variable, so flattening it as an inductive finite term is impossible. -/
theorem rational_cycle_has_back_edge :
    rationalBound.heap[1]? = some (.app .loop #[0]) ∧
    rationalBound.heap[0]? = some (.var .x (some 1)) := by
  constructor <;> rfl

end Mettapedia.Logic.LP.RuntimeTermRegression

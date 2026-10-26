import Mathlib.Tactic

/-!
# Keeping the active unification pair in a register

The reference machine pushes every pair onto its worklist. The lowering
keeps its active pair separately and pushes only deferred siblings. One
opaque inspection may bind the store, decompose a pair, fail after partial
writes, or report a fault. The two machines retain identical inspection
prefixes, stores and pending work at every inspection allowance.

Worklist traffic is counted independently of those inspections. Native
pointer lifetimes, the correctness of the inspection, bounded capacities
and C correspondence are separate obligations. A pair includes any views
or coordinates needed to identify its operands; no field is discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.UnificationWorklist

variable {Pair Store Fault : Type}

inductive Inspection (Pair Store Fault : Type) where
  | next (store : Store) (children : List Pair)
  | failed (store : Store)
  | fault (error : Fault) (store : Store)

inductive Outcome (Pair Store Fault : Type) where
  | complete (store : Store)
  | failed (store : Store)
  | fault (error : Fault) (store : Store)
  | paused (pending : List Pair) (store : Store)
  deriving DecidableEq, Repr

structure Receipt (Pair Store Fault : Type) where
  outcome : Outcome Pair Store Fault
  inspected : List Pair
  pushes : Nat
  pops : Nat
  deriving DecidableEq, Repr

def terminal (outcome : Outcome Pair Store Fault) : Receipt Pair Store Fault :=
  ⟨outcome, [], 0, 0⟩

def record (pair : Pair) (pushes pops : Nat) (later : Receipt Pair Store Fault) :
    Receipt Pair Store Fault :=
  ⟨later.outcome, pair :: later.inspected,
    pushes + later.pushes, pops + later.pops⟩

/-- The initial pair is already on the stack. Each inspection pops once;
all children are pushed, in execution order, ahead of the pending suffix. -/
def stackRun (inspect : Store → Pair → Inspection Pair Store Fault) :
    Nat → List Pair → Store → Receipt Pair Store Fault
  | _, [], store => terminal (.complete store)
  | 0, pending, store => terminal (.paused pending store)
  | allowance + 1, pair :: pending, store =>
      match inspect store pair with
      | .failed later => record pair 0 1 (terminal (.failed later))
      | .fault error later => record pair 0 1 (terminal (.fault error later))
      | .next later children => record pair children.length 1
          (stackRun inspect allowance (children ++ pending) later)

/-- Children take over the active register directly. Only their siblings
are written to the stack; an exhausted child list pops the pending suffix. -/
def registerRun (inspect : Store → Pair → Inspection Pair Store Fault) :
    Nat → Pair → List Pair → Store → Receipt Pair Store Fault
  | 0, pair, pending, store => terminal (.paused (pair :: pending) store)
  | allowance + 1, pair, pending, store =>
      match inspect store pair with
      | .failed later => record pair 0 0 (terminal (.failed later))
      | .fault error later => record pair 0 0 (terminal (.fault error later))
      | .next later (child :: siblings) => record pair siblings.length 0
          (registerRun inspect allowance child (siblings ++ pending) later)
      | .next later [] =>
          match pending with
          | [] => record pair 0 0 (terminal (.complete later))
          | next :: rest => record pair 0 1
              (registerRun inspect allowance next rest later)

/-- This relates independently recursive executions, including stopped
prefixes and failed inspections with their actual partially written store. -/
theorem register_refines_stack
    (inspect : Store → Pair → Inspection Pair Store Fault)
    (allowance : Nat) (pair : Pair) (pending : List Pair) (store : Store) :
    (registerRun inspect allowance pair pending store).outcome =
        (stackRun inspect allowance (pair :: pending) store).outcome ∧
    (registerRun inspect allowance pair pending store).inspected =
        (stackRun inspect allowance (pair :: pending) store).inspected ∧
    (registerRun inspect allowance pair pending store).pushes ≤
        (stackRun inspect allowance (pair :: pending) store).pushes ∧
    (registerRun inspect allowance pair pending store).pops ≤
        (stackRun inspect allowance (pair :: pending) store).pops := by
  induction allowance generalizing pair pending store with
  | zero => simp [registerRun, stackRun, terminal]
  | succ allowance ih =>
      cases result : inspect store pair with
      | failed later => simp [registerRun, stackRun, result, record, terminal]
      | fault error later => simp [registerRun, stackRun, result, record, terminal]
      | next later children =>
          cases children with
          | cons child siblings =>
              obtain ⟨outcome, inspected, pushes, pops⟩ := ih child (siblings ++ pending) later
              simp only [registerRun, stackRun, result, List.cons_append, record,
                List.length_cons]
              exact ⟨outcome, congrArg (pair :: ·) inspected, by omega, by omega⟩
          | nil =>
              cases pending with
              | nil => simp [registerRun, stackRun, result, record, terminal]
              | cons next rest =>
                  obtain ⟨outcome, inspected, pushes, pops⟩ := ih next rest later
                  simp only [registerRun, stackRun, result, List.nil_append, record,
                    List.length_nil, Nat.zero_add]
                  exact ⟨outcome, congrArg (pair :: ·) inspected, pushes, by omega⟩

/-- Entering a nonempty reference worklist costs its initial push as well.
The lowering removes at least this write, under the stated stack model. -/
theorem avoids_initial_push
    (inspect : Store → Pair → Inspection Pair Store Fault)
    (allowance : Nat) (pair : Pair) (pending : List Pair) (store : Store) :
    (registerRun inspect allowance pair pending store).pushes <
      1 + (stackRun inspect allowance (pair :: pending) store).pushes := by
  have bound := (register_refines_stack inspect allowance pair pending store).2.2.1
  omega

/-- One inspection can expose more work than fits in the current allowance.
The exact ordered residual, including both children and the older suffix,
is retained; it is not replaced by a replay of the root. -/
theorem retained_children (inspect : Store → Pair → Inspection Pair Store Fault)
    (pair child : Pair) (siblings pending : List Pair) (store later : Store)
    (result : inspect store pair = .next later (child :: siblings)) :
    (registerRun inspect 1 pair pending store).outcome =
      .paused (child :: (siblings ++ pending)) later := by
  simp [registerRun, result, record, terminal]

namespace Controls

def inspect : Nat → Nat → Inspection Nat Nat Nat
  | store, 0 => .next (store + 1) [1, 2]
  | store, 1 => .next (store * 2) []
  | store, 2 => .next (store + 3) []
  | store, 3 => .failed (store + 7)
  | store, _ => .fault 9 (store + 11)

example : registerRun inspect 3 0 [] 0 = ⟨.complete 5, [0, 1, 2], 1, 1⟩ := by decide
example : stackRun inspect 3 [0] 0 = ⟨.complete 5, [0, 1, 2], 2, 3⟩ := by decide

theorem child_order_matters :
    (registerRun inspect 3 0 [] 0).outcome ≠
      (registerRun inspect 2 2 [1] 1).outcome := by decide

theorem failure_keeps_partial_store :
    (registerRun inspect 1 3 [] 2).outcome = .failed 9 := by decide

theorem fault_keeps_partial_store :
    (registerRun inspect 1 4 [] 2).outcome = .fault 9 13 := by decide

end Controls
end Mettapedia.Machines.UnificationWorklist

#print axioms Mettapedia.Machines.UnificationWorklist.register_refines_stack
#print axioms Mettapedia.Machines.UnificationWorklist.avoids_initial_push
#print axioms Mettapedia.Machines.UnificationWorklist.retained_children
#print axioms Mettapedia.Machines.UnificationWorklist.Controls.child_order_matters
#print axioms Mettapedia.Machines.UnificationWorklist.Controls.failure_keeps_partial_store
#print axioms Mettapedia.Machines.UnificationWorklist.Controls.fault_keeps_partial_store

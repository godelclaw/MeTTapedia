import Mettapedia.Logic.LP.RuntimeTerm

/-!
# Small-step runtime unification

This is the executable graph unifier used by the LP/Prolog runtime.  Its
algorithmic structure is adapted from SWI-Prolog V10.1.9
`src/pl-prims.c` (`unify_simple_ptrs`, `do_unify`, `unify_ptrs`) and
`src/pl-wam.c` (`__do_undo`), pinned by
`Logic/Prolog/SWI/SWI_PROVENANCE.json`.

The representation is Lean-native rather than a transcription of SWI's word
tags.  The semantic mechanisms are the same:

* dereference variable chains before comparing cells;
* point the higher-addressed unbound variable toward the lower one;
* process compound arguments left-to-right through an explicit agenda;
* remember compound pairs so rational trees do not make comparison loop; and
* trail every binding and unwind one entry per rollback step.

The public stepper is total.  A step budget returns a still-running machine;
it never fabricates failure or completion.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeUnification

open RuntimeTerm

/-- Why the machine is unwinding to its entry trail mark. -/
inductive RollbackReason where
  | unificationFailure
  | runtimeError (error : MemoryError)

/-- Comparison and rollback are distinct observable machine phases. -/
inductive Phase where
  | compare
  | rollback (reason : RollbackReason)

/-- One live unification activation. -/
structure Configuration (σ : LPSignature) where
  memory : Memory σ
  agenda : List (Addr × Addr)
  visited : List (Addr × Addr)
  entryMark : Nat
  phase : Phase

/-- A terminal result retains the memory reached at the boundary.  Failure
and errors have already rolled it back to `entryMark`. -/
inductive Terminal (σ : LPSignature) where
  | success (memory : Memory σ)
  | failure (memory : Memory σ)
  | runtimeError (error : MemoryError) (memory : Memory σ)

/-- Running and terminal configurations are structurally distinct. -/
inductive Machine (σ : LPSignature) where
  | running (configuration : Configuration σ)
  | terminal (result : Terminal σ)

/-- Start one transactional unification at the current trail mark. -/
def start {σ : LPSignature} (memory : Memory σ) (left right : Addr) : Machine σ :=
  .running {
    memory
    agenda := [(left, right)]
    visited := []
    entryMark := memory.trailMark
    phase := .compare
  }

private def orderedPair (left right : Addr) : Addr × Addr :=
  if left ≤ right then (left, right) else (right, left)

private def seen (visited : List (Addr × Addr)) (left right : Addr) : Bool :=
  visited.contains (orderedPair left right)

private def beginRollback {σ : LPSignature}
    (configuration : Configuration σ) (reason : RollbackReason) : Machine σ :=
  .running { configuration with agenda := [], phase := .rollback reason }

private def afterBinding {σ : LPSignature}
    (configuration : Configuration σ) (rest : List (Addr × Addr))
    (variableAddress : Addr) (identity : σ.vars) (target : Addr) : Machine σ :=
  match configuration.memory.write variableAddress (.var identity (some target)) with
  | .ok memory => .running { configuration with memory, agenda := rest }
  | .error error => beginRollback configuration (.runtimeError error)

private def rollbackTerminal {σ : LPSignature}
    (reason : RollbackReason) (memory : Memory σ) : Machine σ :=
  match reason with
  | .unificationFailure => .terminal (.failure memory)
  | .runtimeError error => .terminal (.runtimeError error memory)

/-- Execute exactly one unification or rollback microstep.  Terminal machines
have no successor. -/
def step {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : Machine σ → Option (Machine σ)
  | .terminal _ => none
  | .running configuration =>
      match configuration.phase with
      | .rollback reason =>
          if configuration.memory.trail.size = configuration.entryMark then
            some (rollbackTerminal reason configuration.memory)
          else if configuration.entryMark < configuration.memory.trail.size then
            match configuration.memory.undoLast with
            | .ok memory => some (.running { configuration with memory })
            | .error error => some (.terminal (.runtimeError error configuration.memory))
          else
            some (.terminal (.runtimeError
              (.invalidTrailMark configuration.entryMark configuration.memory.trail.size)
              configuration.memory))
      | .compare =>
          match configuration.agenda with
          | [] => some (.terminal (.success configuration.memory))
          | (left, right) :: rest =>
              match configuration.memory.heap.deref left with
              | .error error => some (beginRollback configuration (.runtimeError error))
              | .ok (.variableCycle address) =>
                  some (beginRollback configuration
                    (.runtimeError (.variableReferenceCycle address)))
              | .ok (.root leftRoot) =>
                  match configuration.memory.heap.deref right with
                  | .error error => some (beginRollback configuration (.runtimeError error))
                  | .ok (.variableCycle address) =>
                      some (beginRollback configuration
                        (.runtimeError (.variableReferenceCycle address)))
                  | .ok (.root rightRoot) =>
                      if leftRoot = rightRoot then
                        some (.running { configuration with agenda := rest })
                      else
                        match configuration.memory.heap[leftRoot]?,
                            configuration.memory.heap[rightRoot]? with
                        | some (.var leftIdentity none), some (.var rightIdentity none) =>
                            if leftRoot < rightRoot then
                              some (afterBinding configuration rest rightRoot rightIdentity leftRoot)
                            else
                              some (afterBinding configuration rest leftRoot leftIdentity rightRoot)
                        | some (.var identity none), some _ =>
                            some (afterBinding configuration rest leftRoot identity rightRoot)
                        | some _, some (.var identity none) =>
                            some (afterBinding configuration rest rightRoot identity leftRoot)
                        | some (.const leftSymbol), some (.const rightSymbol) =>
                            if leftSymbol = rightSymbol then
                              some (.running { configuration with agenda := rest })
                            else
                              some (beginRollback configuration .unificationFailure)
                        | some (.app leftSymbol leftArgs), some (.app rightSymbol rightArgs) =>
                            if leftSymbol = rightSymbol ∧ leftArgs.size = rightArgs.size then
                              if seen configuration.visited leftRoot rightRoot then
                                some (.running { configuration with agenda := rest })
                              else
                                let arguments := leftArgs.toList.zip rightArgs.toList
                                some (.running {
                                  configuration with
                                  agenda := arguments ++ rest
                                  visited := orderedPair leftRoot rightRoot :: configuration.visited
                                })
                            else
                              some (beginRollback configuration .unificationFailure)
                        | some _, some _ =>
                            some (beginRollback configuration .unificationFailure)
                        | none, _ =>
                            some (beginRollback configuration
                              (.runtimeError (.invalidAddress leftRoot)))
                        | _, none =>
                            some (beginRollback configuration
                              (.runtimeError (.invalidAddress rightRoot)))

/-- Run at most `fuel` real microsteps.  Exhausting fuel returns the current
running state unchanged as a terminal classification: the caller can resume
with more steps. -/
def runSteps {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] : Nat → Machine σ → Machine σ
  | 0, machine => machine
  | fuel + 1, machine =>
      match step machine with
      | none => machine
      | some next => runSteps fuel next

@[simp]
theorem step_terminal {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (result : Terminal σ) :
    step (.terminal result) = none := rfl

@[simp]
theorem runSteps_zero {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (machine : Machine σ) :
    runSteps 0 machine = machine := rfl

end RuntimeUnification
end Mettapedia.Logic.LP

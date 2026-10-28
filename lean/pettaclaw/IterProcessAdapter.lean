import PolicyPipeline

/-!
# IterProcessAdapter — revision snapshots for hosted Iter processes

The weak runner and exact Iter list embedding already exist.  This file adds
only the boundary needed by a filesystem adapter: a turn captures one ordered
process list at one artifact revision.  Refresh installs an arbitrary snapshot
for a future turn; it cannot rewrite the list already executing.

Lexicographic file discovery, child-process invocation, and serialization are
executable adapter obligations.  They are intentionally not new kernel rules.
-/

namespace IterProcessAdapter

open WeakSelfHostingCore
open WeakAgentEcology

/-- One immutable turn-local view of a dynamically discovered process
directory.  `Revision` may be a digest, generation number, or other artifact
identity; the weak runner never interprets it. -/
structure Snapshot (Revision Periphery : Type) where
  revision : Revision
  processes : List (Process Periphery)

/-- Execute exactly the captured order through the existing weak runner. -/
def run {Root Revision Periphery : Type}
    (snapshot : Snapshot Revision Periphery)
    (state : Rooted Root Periphery) : Rooted Root Periphery :=
  runProcesses snapshot.processes state

theorem run_preserves_root {Root Revision Periphery : Type}
    (snapshot : Snapshot Revision Periphery)
    (state : Rooted Root Periphery) :
    (run snapshot state).root = state.root := by
  exact runProcesses_preserves_root snapshot.processes state

/-- A discovered component that fails is a local stutter; components after it
still execute in their captured order. -/
theorem failed_component_erases
    {Root Revision Periphery : Type}
    (revision : Revision) (left right : List (Process Periphery))
    (state : Rooted Root Periphery) :
    run { revision := revision,
          processes := left ++ failingProcess :: right } state =
      run { revision := revision, processes := left ++ right } state := by
  exact failed_process_erases_from_trace left right state

/-- Finish the current captured turn and install a freshly discovered
snapshot for the next one. -/
def runThenRefresh {Root Revision Periphery : Type}
    (current next : Snapshot Revision Periphery)
    (state : Rooted Root Periphery) :
    Rooted Root Periphery × Snapshot Revision Periphery :=
  (run current state, next)

/-- Refresh cannot retroactively change the process list used by the current
turn. -/
theorem current_turn_uses_captured_snapshot
    {Root Revision Periphery : Type}
    (current next : Snapshot Revision Periphery)
    (state : Rooted Root Periphery) :
    (runThenRefresh current next state).1 = run current state := by
  rfl

/-- The next turn receives the complete new snapshot, without a closed
catalogue or privileged stage names. -/
theorem next_turn_receives_refreshed_snapshot
    {Root Revision Periphery : Type}
    (current next : Snapshot Revision Periphery)
    (state : Rooted Root Periphery) :
    (runThenRefresh current next state).2 = next := by
  rfl

def fromIterSnapshot {Revision : Type} (revision : Revision)
    (transformations : List IterArchitecture.Transformation) :
    Snapshot Revision IterArchitecture.Boundary :=
  { revision := revision
    processes := transformations.map fromIter }

/-- The captured-process adapter is extensionally the reference Iter fold
when supplied the same ordered transformation outcomes. -/
theorem captured_iter_pipeline_is_exact {Root Revision : Type}
    (root : Root) (revision : Revision)
    (boundary : IterArchitecture.Boundary)
    (transformations : List IterArchitecture.Transformation) :
    (run (fromIterSnapshot revision transformations)
      ({ root := root, periphery := boundary } :
        Rooted Root IterArchitecture.Boundary)).periphery =
      IterArchitecture.applyTransformations transformations boundary := by
  exact iter_pipeline_is_exact root boundary transformations

/-- Capturing does not erase the observable ordering of noncommuting
processes. -/
theorem captured_order_is_observable :
    let state : Rooted Unit Nat := ⟨(), 1⟩
    let increment : Process Nat := hostChange (fun value => value + 1)
    let double : Process Nat := hostChange (fun value => value * 2)
    run ({ revision := (), processes := [increment, double] } :
      Snapshot Unit Nat) state ≠
    run ({ revision := (), processes := [double, increment] } :
      Snapshot Unit Nat) state := by
  exact process_order_is_expressive

end IterProcessAdapter

#print axioms IterProcessAdapter.run_preserves_root
#print axioms IterProcessAdapter.failed_component_erases
#print axioms IterProcessAdapter.current_turn_uses_captured_snapshot
#print axioms IterProcessAdapter.next_turn_receives_refreshed_snapshot
#print axioms IterProcessAdapter.captured_iter_pipeline_is_exact
#print axioms IterProcessAdapter.captured_order_is_observable

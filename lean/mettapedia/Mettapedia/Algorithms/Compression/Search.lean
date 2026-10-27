import Mettapedia.Algorithms.Compression.FairQueue
import Mettapedia.Algorithms.Compression.WholeArtifact

/-!
# Cooperative search followed by independent artifact checking

One system node denotes a cooperative producer slice. It may emit a proposal
and expose finite successor slices, including its own continuation. The queue
retains every occurrence. The checker considers every emitted proposal in order,
including those after an earlier refusal, against the original task observation.

The cost theorem concerns the actual observed prefix. It does not claim that a
budget exhausts the producer region or that an unobserved proposal is worse.
-/

namespace Mettapedia.Algorithms.Compression.Search

open Mettapedia.GSLT.Core.BranchingTemporal
open FramedTree

universe u
variable {Node : Type u} {Observation : Type} [DecidableEq Observation]

def proposals (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (fuel : Nat) (queue : FairQueue.Queue Node) : List Tree :=
  ((FairQueue.run cost system.successors fuel queue).1).filterMap
    (fun entry => system.emit entry.value)

def best (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (fuel : Nat) (queue : FairQueue.Queue Node) : Tree :=
  WholeArtifact.refine read original current (proposals system cost fuel queue)

theorem proposal_origin (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (fuel : Nat) (queue : FairQueue.Queue Node) (artifact : Tree) :
    artifact ∈ proposals system cost fuel queue ↔
      ∃ entry ∈ (FairQueue.run cost system.successors fuel queue).1,
        system.emit entry.value = some artifact := by
  simp [proposals, List.mem_filterMap]

theorem best_preserves (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (fuel : Nat) (queue : FairQueue.Queue Node) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation) :
    read (best read original current system cost fuel queue) = some observation ∧
      byteLength (best read original current system cost fuel queue) ≤ byteLength current :=
  WholeArtifact.refine_preserves read original current _ observation source currentValid

/-- Earlier rejected proposals cannot hide a later checked improvement. -/
theorem best_le_every_emitted (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (fuel : Nat) (queue : FairQueue.Queue Node) (observation : Observation)
    (source : read original = some observation) (currentValid : read current = some observation)
    (artifact : Tree) (emitted : artifact ∈ proposals system cost fuel queue)
    (valid : read artifact = some observation) :
    byteLength (best read original current system cost fuel queue) ≤ byteLength artifact :=
  WholeArtifact.refine_optimal_in_region read original current _ observation source currentValid
    artifact emitted valid

theorem proposals_add (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (first second : Nat) (queue : FairQueue.Queue Node) :
    proposals system cost (first + second) queue =
      proposals system cost first queue ++
        proposals system cost second (FairQueue.run cost system.successors first queue).2 := by
  simp only [proposals, FairQueue.run_add]
  simp

/-- Scheduling and checking both compose across a pause. The resumed best
is exactly the one obtained by checking the uninterrupted proposal prefix. -/
theorem best_resume (read : Tree → Option Observation) (original current : Tree)
    (system : BranchingSystem Node Tree) (cost : Node → Nat)
    (first second : Nat) (queue : FairQueue.Queue Node) :
    best read original current system cost (first + second) queue =
      best read original (best read original current system cost first queue)
        system cost second (FairQueue.run cost system.successors first queue).2 := by
  simp only [best, proposals_add, WholeArtifact.refine_append]

end Mettapedia.Algorithms.Compression.Search

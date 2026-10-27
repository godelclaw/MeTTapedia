import Mettapedia.Algorithms.Compression.FairSearch
import Mettapedia.Algorithms.Compression.CostedArtifact

/-! Cooperative artifact search with a task-fixed acceptance predicate.
The predicate may express a nontransitive numerical tolerance. Every proposal
and every resumed winner is checked against that fixed original task. -/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ObservedSearch

open FramedTree Mettapedia.GSLT.Core.BranchingTemporal

variable {Node : Type}

def best (valid : Tree → Bool) (current : Tree) (system : BranchingSystem Node Tree)
    (priority : Node → Nat) (fuel : Nat) (queue : FairQueue.Queue Node) : Tree :=
  CostedArtifact.refine valid byteLength current (Search.proposals system priority fuel queue)

theorem best_preserves (valid : Tree → Bool) (current : Tree) (system : BranchingSystem Node Tree)
    (priority : Node → Nat) (fuel : Nat) (queue : FairQueue.Queue Node)
    (admitted : valid current = true) :
    valid (best valid current system priority fuel queue) = true ∧
      byteLength (best valid current system priority fuel queue) ≤ byteLength current :=
  CostedArtifact.refine_preserves valid byteLength current _ admitted

theorem best_le_emitted (valid : Tree → Bool) (current : Tree) (system : BranchingSystem Node Tree)
    (priority : Node → Nat) (fuel : Nat) (queue : FairQueue.Queue Node)
    (admitted : valid current = true) (artifact : Tree)
    (present : artifact ∈ Search.proposals system priority fuel queue) (checked : valid artifact = true) :
    byteLength (best valid current system priority fuel queue) ≤ byteLength artifact :=
  CostedArtifact.refine_optimal_in_region valid byteLength current _ admitted artifact present checked

theorem best_resume (valid : Tree → Bool) (current : Tree) (system : BranchingSystem Node Tree)
    (priority : Node → Nat) (first second : Nat) (queue : FairQueue.Queue Node) :
    best valid current system priority (first + second) queue =
      best valid (best valid current system priority first queue)
        system priority second (FairQueue.run priority system.successors first queue).2 := by
  simp only [best, Search.proposals_add, CostedArtifact.refine_append]

theorem best_eventually_le_reachable (valid : Tree → Bool) (current : Tree)
    (system : BranchingSystem Node Tree) (priority : Node → Nat) (queue : FairQueue.Queue Node)
    (validQueue : FairQueue.Valid queue) {root node : Node}
    (rootMember : root ∈ queue.pending.map FairQueue.Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ system.successors parent) root node)
    (artifact : Tree) (emits : system.emit node = some artifact)
    (admitted : valid current = true) (checked : valid artifact = true) :
    ∃ fuel, byteLength (best valid current system priority fuel queue) ≤ byteLength artifact := by
  obtain ⟨fuel, serviced⟩ := FairQueue.services_reachable priority system.successors queue validQueue rootMember reachable
  obtain ⟨entry, present, same⟩ := List.mem_map.mp serviced
  exact ⟨fuel, best_le_emitted valid current system priority fuel queue admitted artifact
    ((Search.proposal_origin system priority fuel queue artifact).mpr ⟨entry, present, same ▸ emits⟩) checked⟩

theorem best_le_reachable_of_complete (valid : Tree → Bool) (current : Tree)
    (system : BranchingSystem Node Tree) (priority : Node → Nat) (queue : FairQueue.Queue Node)
    (fuel : Nat) (complete : (FairQueue.run priority system.successors fuel queue).2.pending = [])
    {root node : Node} (rootMember : root ∈ queue.pending.map FairQueue.Entry.value)
    (reachable : Relation.ReflTransGen (fun parent child => child ∈ system.successors parent) root node)
    (artifact : Tree) (emits : system.emit node = some artifact)
    (admitted : valid current = true) (checked : valid artifact = true) :
    byteLength (best valid current system priority fuel queue) ≤ byteLength artifact := by
  have serviced := FairQueue.complete_covers_reachable priority system.successors fuel queue rootMember reachable complete
  obtain ⟨entry, present, same⟩ := List.mem_map.mp serviced
  exact best_le_emitted valid current system priority fuel queue admitted artifact
    ((Search.proposal_origin system priority fuel queue artifact).mpr ⟨entry, present, same ▸ emits⟩) checked

/-- Rechecking a retained winner uses the original criterion and original
complete cost. Equality is reserved for unchanged artifacts. -/
def checkedWinner (valid : Tree → Bool) (original winner : Tree) : Prop :=
  valid original = true ∧
    (winner = original ∨ CostedArtifact.accept valid byteLength original winner = some winner)

theorem checkedWinner_iff (valid : Tree → Bool) (original winner : Tree) :
    checkedWinner valid original winner ↔
      valid original = true ∧
        (winner = original ∨ valid winner = true ∧ byteLength winner < byteLength original) := by
  simp only [checkedWinner, CostedArtifact.accept_iff, true_and]
  constructor
  · rintro ⟨source, unchanged | ⟨validSource, accepted, smaller⟩⟩
    · exact ⟨source, Or.inl unchanged⟩
    · exact ⟨source, Or.inr ⟨accepted, smaller⟩⟩
  · rintro ⟨source, unchanged | ⟨accepted, smaller⟩⟩
    · exact ⟨source, Or.inl unchanged⟩
    · exact ⟨source, Or.inr ⟨source, accepted, smaller⟩⟩

theorem checkedWinner_sound (valid : Tree → Bool) (original winner : Tree)
    (checked : checkedWinner valid original winner) :
    valid winner = true ∧ byteLength winner ≤ byteLength original := by
  obtain ⟨source, same | ⟨accepted, smaller⟩⟩ := (checkedWinner_iff valid original winner).mp checked
  · subst winner
    exact ⟨source, Nat.le_refl _⟩
  · exact ⟨accepted, Nat.le_of_lt smaller⟩

private theorem refine_same_or_smaller (valid : Tree → Bool) (current : Tree)
    (candidates : List Tree) :
    CostedArtifact.refine valid byteLength current candidates = current ∨
      byteLength (CostedArtifact.refine valid byteLength current candidates) < byteLength current := by
  induction candidates generalizing current with
  | nil => exact Or.inl rfl
  | cons candidate rest ih =>
      cases accepted : CostedArtifact.accept valid byteLength current candidate with
      | none =>
          have unchanged : CostedArtifact.step valid byteLength current candidate = current := by
            simp [CostedArtifact.step, accepted]
          simpa only [CostedArtifact.refine, unchanged] using ih current
      | some next =>
          obtain ⟨rfl, _, nextValid, smaller⟩ :=
            (CostedArtifact.accept_iff valid byteLength current candidate next).mp accepted
          have stepSame : CostedArtifact.step valid byteLength current next = next := by
            simp [CostedArtifact.step, accepted]
          apply Or.inr
          simpa only [CostedArtifact.refine, stepSame] using
            lt_of_le_of_lt (CostedArtifact.refine_preserves valid byteLength next rest nextValid).2 smaller

theorem refined_winner_checkable (valid : Tree → Bool) (original current : Tree)
    (candidates : List Tree) (retained : checkedWinner valid original current) :
    checkedWinner valid original (CostedArtifact.refine valid byteLength current candidates) := by
  have currentValid := checkedWinner_sound valid original current retained
  have finalValid := CostedArtifact.refine_preserves valid byteLength current candidates currentValid.1
  apply (checkedWinner_iff valid original _).mpr
  refine ⟨retained.1, ?_⟩
  rcases refine_same_or_smaller valid current candidates with unchanged | strict
  · rw [unchanged]
    exact ((checkedWinner_iff valid original current).mp retained).2
  · exact Or.inr ⟨finalValid.1, strict.trans_le currentValid.2⟩

end Mettapedia.Algorithms.Compression.ObservedSearch

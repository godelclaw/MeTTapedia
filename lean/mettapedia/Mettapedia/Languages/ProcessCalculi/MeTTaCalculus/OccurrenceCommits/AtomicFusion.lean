import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SequentialComposition
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Traces

/-!
# Atomic fusion across a movable interleaving

Net-effect composition alone does not license fusion in an open execution.
Here an intervening list may be moved past the second commit using the existing
trace-independence relation. The reordered execution can then be fused, retaining
the compiled initial condition. Expansion gives the converse.

This is a sufficient mover condition, not a characterization of all sound
optimizations. Full event traces still distinguish two commits from one. An
observer that hides the two internal commits and their replacement keeps its
ordered selected events under this particular transformation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The original event history is retained and related by authenticated swaps. -/
theorem regroup_trace {label : O → R} (c d : Commit O R)
    (between suffix : List (Commit O R))
    (movable : ∀ observer ∈ between, TraceIndependent label observer d) :
    TraceEq label (c :: (between ++ d :: suffix)) (c :: d :: (between ++ suffix)) :=
  (bubble (q := suffix) movable).cons c

/-- Fusion is admitted exactly on the executable original runs under the
stated mover condition, when the compiled guard is retained. -/
theorem executable_fusion_iff {label : O → R} {store : Finset O} (c d : Commit O R)
    (between suffix : List (Commit O R))
    (movable : ∀ observer ∈ between, TraceIndependent label observer d) :
    Executable label store (c :: (between ++ d :: suffix)) ↔
      (CommitPrecondition.sequential label c d).Holds label store ∧
        Executable label store (c.compose d :: (between ++ suffix)) := by
  have reorder := regroup_trace c d between suffix movable
  constructor
  · intro original
    have grouped := (reorder.executable original).1
    obtain ⟨first, second, tail⟩ :=
      (executable_cons_iff.trans (and_congr_right fun _ => executable_cons_iff)).mp grouped
    refine ⟨(CommitPrecondition.sequential_holds_iff label c d store).mpr ⟨first, second⟩,
      .cons (Commit.compose_enabled first second) ?_⟩
    rwa [Commit.compose_fire first second]
  · rintro ⟨guard, fused⟩
    obtain ⟨first, second⟩ := (CommitPrecondition.sequential_holds_iff label c d store).mp guard
    have tail := (executable_cons_iff.mp fused).2
    rw [Commit.compose_fire first second] at tail
    exact (reorder.symm.executable (.cons first (.cons second tail))).1

/-- The admitted transformation preserves the final occurrence store. -/
theorem fireList_fusion {label : O → R} {store : Finset O} (c d : Commit O R)
    (between suffix : List (Commit O R))
    (movable : ∀ observer ∈ between, TraceIndependent label observer d)
    (original : Executable label store (c :: (between ++ d :: suffix))) :
    fireList store (c.compose d :: (between ++ suffix)) =
      fireList store (c :: (between ++ d :: suffix)) := by
  obtain ⟨guard, _⟩ := (executable_fusion_iff c d between suffix movable).mp original
  obtain ⟨first, second⟩ := (CommitPrecondition.sequential_holds_iff label c d store).mp guard
  have same := ((regroup_trace c d between suffix movable).executable original).2
  simpa only [fireList_cons, Commit.compose_fire first second] using same

/-- Hiding precisely the internal events preserves the order of the retained
client events. This observation law accompanies, rather than supplies, the
executable-fusion theorem. -/
theorem fusion_selected_events (c d : Commit O R) (between suffix : List (Commit O R))
    (selected : Commit O R → Bool) (firstHidden : selected c = false)
    (secondHidden : selected d = false) (fusedHidden : selected (c.compose d) = false) :
    (c :: (between ++ d :: suffix)).filter selected =
      (c.compose d :: (between ++ suffix)).filter selected := by
  simp [firstHidden, secondHidden, fusedHidden]

/-- Without an explicit coarser observation, two events never become one
through the existing trace equivalence. -/
theorem fusion_not_traceEq (label : O → R) (c d : Commit O R) :
    ¬ TraceEq label [c, d] [c.compose d] := by
  intro same
  have lengths := same.perm.length_eq
  simp at lengths

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

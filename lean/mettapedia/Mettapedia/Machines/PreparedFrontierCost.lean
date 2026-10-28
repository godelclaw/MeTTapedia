import Mettapedia.Machines.PreparedSharedFrontier

/-!
# Cost of reconstructing nested caller suffixes

Each successive source level saves one caller and one pending equation.
If every equation independently materializes its whole caller list, its work
is the sum of those list lengths. A shared arena stores one node per caller.
These are explicit model counts, not a bound on native allocation, lookup,
effects, elapsed time or the cost of individual captured values.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedFrontierCost

open PreparedSharedFrontier SharedContinuation

def layer : Layer Nat Nat Nat := ⟨some 0, [(0, 0)], 0⟩

def suffixWork (state : Source Nat Nat Nat) : Nat :=
  (state.pending.map fun task => task.returns.length).sum

def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

theorem triangular_double (n : Nat) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => simp [triangular]
  | succ n ih =>
      simp only [triangular]
      nlinarith

theorem source_one_level (state : Source Nat Nat Nat) :
    (sourceStep state layer).returns.length = state.returns.length + 1 ∧
      (sourceStep state layer).pending.length = state.pending.length + 1 ∧
      suffixWork (sourceStep state layer) = state.returns.length + 1 + suffixWork state := by
  simp [sourceStep, sourceFrame, layer, extend,
    PreparedFrontierTransfer.lowerFrame, suffixWork, Nat.add_comm]

/-- The source retains each of the independently materialized caller lists. -/
theorem source_many_levels (state : Source Nat Nat Nat) (n : Nat) :
    (sourceBuild state (List.replicate n layer)).returns.length = state.returns.length + n ∧
      (sourceBuild state (List.replicate n layer)).pending.length = state.pending.length + n ∧
      suffixWork (sourceBuild state (List.replicate n layer)) =
        suffixWork state + n * state.returns.length + triangular n := by
  induction n generalizing state with
  | zero => simp [sourceBuild, triangular]
  | succ n ih =>
      have one := source_one_level state
      have rest := ih (sourceStep state layer)
      simp only [List.replicate_succ, sourceBuild] at ⊢
      rw [one.1, one.2.1, one.2.2] at rest
      simp only [triangular]
      rcases rest with ⟨returns, pending, work⟩
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith

def sourceStart : Source Nat Nat Nat := ⟨[], []⟩

/-- Independent suffix reconstruction has triangular work in the depth. -/
theorem separate_suffix_work (n : Nat) :
    2 * suffixWork (sourceBuild sourceStart (List.replicate n layer)) = n * (n + 1) := by
  have work := (source_many_levels sourceStart n).2.2
  have workExact : suffixWork (sourceBuild sourceStart (List.replicate n layer)) = triangular n := by
    simpa [sourceStart, suffixWork] using work
  rw [workExact]
  exact triangular_double n

def sharedStart : Shared Nat Nat Nat := ⟨[], 0, []⟩

theorem sharedStart_valid : sharedStart.Valid := by
  simp [sharedStart, Shared.Valid, Arena.Valid]

theorem callerCount_replicate (n : Nat) :
    callerCount (List.replicate n layer) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + callerCount (List.replicate n layer) = n + 1
      rw [ih]
      omega

/-- One shared caller node is retained per level, with the same pending
equation occurrences as the source. -/
theorem shared_suffix_nodes (n : Nat) :
    (sharedBuild sharedStart (List.replicate n layer)).arena.length = n ∧
      (sharedBuild sharedStart (List.replicate n layer)).pending.length = n := by
  have exactBuild := sharedBuild_exact sharedStart sharedStart_valid (List.replicate n layer)
  have nodes := exactBuild.2.2
  have decoded := congrArg (fun state : Source Nat Nat Nat => state.pending.length) exactBuild.2.1
  have sourceCount := (source_many_levels sourceStart n).2.1
  constructor
  · simpa [sharedStart, callerCount_replicate] using nodes
  · simpa [Shared.decode, sharedStart, sourceStart] using decoded.trans sourceCount

theorem three_levels_distinguish_counts :
    suffixWork (sourceBuild sourceStart (List.replicate 3 layer)) = 6 ∧
      (sharedBuild sharedStart (List.replicate 3 layer)).arena.length = 3 := by
  decide +kernel

end Mettapedia.Machines.PreparedFrontierCost

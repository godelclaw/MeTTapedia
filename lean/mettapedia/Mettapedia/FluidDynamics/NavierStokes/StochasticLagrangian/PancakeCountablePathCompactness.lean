import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.Basic

/-!
# One uniformly convergent subsequence for countably many coefficient paths

Each coordinate family has a compact closure by Arzelà--Ascoli. The
countable product is compact and first countable, giving a single
subsequence for all coordinates, not a separate subsequence per mode.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCountablePathCompactness

open scoped NNReal Topology
open Filter
open BoundedContinuousFunction

variable {α ι : Type*} [PseudoMetricSpace α] [CompactSpace α] [Countable ι]

/-- Compactness of a bounded family with a common time Lipschitz constant. -/
theorem isCompact_path_closure (f : ℕ → BoundedContinuousFunction α ℂ)
    (K : ℝ≥0) (R : ℝ) (hK : ∀ n, LipschitzWith K (f n))
    (hR : ∀ n x, ‖f n x‖ ≤ R) :
    IsCompact (closure (Set.range f)) := by
  have he : Equicontinuous (fun a : Set.range f ↦ (a.val : α → ℂ)) := by
    apply (LipschitzWith.uniformEquicontinuous _ K ?_).equicontinuous
    rintro ⟨a, n, rfl⟩
    exact hK n
  apply arzela_ascoli (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall _ _) (Set.range f)
  · intro a x ha
    obtain ⟨n, rfl⟩ := ha
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR n x
  · exact he

/-- A single increasing extraction converges in the uniform norm at
every index of the countable coordinate family. -/
theorem exists_countable_uniform_subsequence
    (f : ℕ → ι → BoundedContinuousFunction α ℂ) (K : ι → ℝ≥0) (R : ι → ℝ)
    (hK : ∀ n j, LipschitzWith (K j) (f n j))
    (hR : ∀ n j x, ‖f n j x‖ ≤ R j) :
    ∃ a : ι → BoundedContinuousFunction α ℂ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ∀ j, Tendsto (fun n ↦ f (phi n) j) atTop (𝓝 (a j)) := by
  let C : ι → Set (BoundedContinuousFunction α ℂ) := fun j ↦ closure (Set.range (fun n ↦ f n j))
  have hc (j : ι) : IsCompact (C j) :=
    isCompact_path_closure (fun n ↦ f n j) (K j) (R j) (fun n ↦ hK n j) (fun n ↦ hR n j)
  have hp := isCompact_pi_infinite hc
  obtain ⟨a, _, phi, hphi, ha⟩ := hp.tendsto_subseq
    (x := f) (fun n j ↦ subset_closure (Set.mem_range_self n))
  refine ⟨a, phi, hphi, fun j ↦ ?_⟩
  exact ((continuous_apply j).tendsto a).comp ha

theorem exists_countable_tendstoUniformly
    (f : ℕ → ι → BoundedContinuousFunction α ℂ) (K : ι → ℝ≥0) (R : ι → ℝ)
    (hK : ∀ n j, LipschitzWith (K j) (f n j))
    (hR : ∀ n j x, ‖f n j x‖ ≤ R j) :
    ∃ a : ι → BoundedContinuousFunction α ℂ, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ ∀ j, TendstoUniformly (fun n ↦ (f (phi n) j : α → ℂ)) (a j) atTop := by
  obtain ⟨a, phi, hphi, ha⟩ := exists_countable_uniform_subsequence f K R hK hR
  exact ⟨a, phi, hphi, fun j ↦ tendsto_iff_tendstoUniformly.mp (ha j)⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeCountablePathCompactness

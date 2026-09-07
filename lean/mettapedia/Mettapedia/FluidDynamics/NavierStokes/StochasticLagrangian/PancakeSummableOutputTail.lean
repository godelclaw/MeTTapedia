import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowTouchEnergy
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Vanishing exterior-output tails of summable interactions

A fixed summable majorant on frequency pairs pays all finite input sums.
As the retained output set exhausts the lattice, its exterior tail tends
to zero. No rate or bound uniform in a varying coefficient field follows.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSummableOutputTail

open Filter
open scoped Topology
open PeriodicFourierTriad

def outputTail (H : Wavevector × Wavevector → ℝ) (M : Finset Wavevector) : ℝ :=
  ∑' p : Wavevector × Wavevector, if p.1 + p.2 ∈ M then 0 else H p

theorem outputTail_nonneg (H : Wavevector × Wavevector → ℝ) (hH : ∀ p, 0 ≤ H p)
    (M : Finset Wavevector) : 0 ≤ outputTail H M :=
  tsum_nonneg (fun p ↦ by split_ifs <;> simp_all)

theorem summable_exterior_majorant (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (M : Finset Wavevector) :
    Summable (fun p : Wavevector × Wavevector ↦ if p.1 + p.2 ∈ M then 0 else H p) := by
  apply hSum.of_norm_bounded
  intro p
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hH p), hH p]

theorem finite_exterior_sum_le_outputTail (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (M : Finset Wavevector)
    (pairs : Finset (Wavevector × Wavevector)) :
    (∑ p ∈ pairs, if p.1 + p.2 ∈ M then 0 else H p) ≤ outputTail H M := by
  apply (summable_exterior_majorant H hH hSum M).sum_le_tsum
  intro p _
  split_ifs <;> simp [hH p]

theorem tendsto_outputTail (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) :
    Tendsto (outputTail H) atTop (𝓝 0) := by
  have hp (p : Wavevector × Wavevector) :
      Tendsto (fun M : Finset Wavevector ↦ if p.1 + p.2 ∈ M then 0 else H p) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({p.1 + p.2} : Finset Wavevector)] with M hM
    have hm : p.1 + p.2 ∈ M := hM (Finset.mem_singleton_self _)
    simp [hm]
  have h := tendsto_tsum_of_dominated_convergence hSum hp
    (Eventually.of_forall (fun (M : Finset Wavevector) (p : Wavevector × Wavevector) ↦
      (show ‖if p.1 + p.2 ∈ M then (0 : ℝ) else H p‖ ≤ H p by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hH p), hH p])))
  convert h using 1
  · funext M
    rfl
  · simp

theorem exists_outputTail_lt (H : Wavevector × Wavevector → ℝ)
    (hH : ∀ p, 0 ≤ H p) (hSum : Summable H) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ M : Finset Wavevector, core ⊆ M → outputTail H M < epsilon := by
  have h := (tendsto_outputTail H hH hSum).eventually (gt_mem_nhds hepsilon)
  exact eventually_atTop.mp h

end Mettapedia.FluidDynamics.NavierStokes.PancakeSummableOutputTail

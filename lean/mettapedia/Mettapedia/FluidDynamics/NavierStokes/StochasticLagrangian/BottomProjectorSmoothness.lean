import Mettapedia.Analysis.SimpleImplicitRoot
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainSpectralInvariants

/-!
# Smooth bottom spectral projectors through top-eigenvalue collisions

The bottom root is identified with a smooth implicit function. A rational
projector formula uses only that root and smooth spectral invariants, so
no differentiability of either top eigenvalue is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.BottomProjectorSmoothness

open scoped Topology ContDiff
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain StrainEigenvalueContinuity
open StrainSpectralInvariants BottomSpectralProjectorPolynomial

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def invariantNumerator (A : Op) (z : ℝ) : Op :=
  A ^ 2 - (operatorTrace A - z) • A +
    (secondInvariant A - z * operatorTrace A + z ^ 2) • 1

theorem invariantNumerator_bottom_eq (S : SymmetricStrain) :
    invariantNumerator S.1 (thirdEigenvalue S) = bottomProjectorNumerator S := by
  have ht : operatorTrace S.1 = topEigenvalue S + secondEigenvalue S + thirdEigenvalue S :=
    trace_eq_sum_orderedEigenvalues S
  apply ContinuousLinearMap.ext
  intro w
  simp only [invariantNumerator, ht, secondInvariant_eq, bottomProjectorNumerator, pow_two,
    mul_apply_eq_comp, sub_apply, add_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
  module

theorem bottomEigenlineProjector_eq_invariants (S : SymmetricStrain) (hg : 0 < bottomGap S) :
    bottomEigenlineProjector S =
      (3 * thirdEigenvalue S ^ 2 - 2 * operatorTrace S.1 * thirdEigenvalue S + secondInvariant S.1)⁻¹ •
        invariantNumerator S.1 (thirdEigenvalue S) := by
  rw [characteristicValue_bottom_derivative, invariantNumerator_bottom_eq]
  exact bottomEigenlineProjector_eq_polynomial S hg

theorem contDiff_invariantNumerator {n : ℕ∞ω} :
    ContDiff ℝ n (fun p : Op × ℝ ↦ invariantNumerator p.1 p.2) := by
  unfold invariantNumerator
  have ht := contDiff_operatorTrace (n := n)
  have h2 := contDiff_secondInvariant (n := n)
  fun_prop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {n : ℕ∞ω} (S : E → SymmetricStrain) (x : E)

theorem contDiffAt_thirdEigenvalue (hS : ContDiffAt ℝ n (fun y ↦ (S y).1) x)
    (hn : n ≠ 0) (hg : 0 < bottomGap (S x)) :
    ContDiffAt ℝ n (fun y ↦ thirdEigenvalue (S y)) x := by
  have hc : ContinuousAt S x := tendsto_subtype_rng.mpr hS.continuousAt
  apply Mettapedia.Analysis.contDiffAt_of_simple_implicit_root
    (f := fun p : E × ℝ ↦ characteristicValue (S p.1).1 p.2)
    (c := spectralWidth (S x) * bottomGap (S x))
  · exact contDiff_characteristicValue.contDiffAt.comp (x, thirdEigenvalue (S x))
      ((hS.comp (x, thirdEigenvalue (S x)) contDiffAt_fst).prodMk contDiffAt_snd)
  · exact hn
  · exact lipschitzWith_thirdEigenvalue.continuous.continuousAt.comp hc
  · exact Filter.Eventually.of_forall (fun y ↦ characteristicValue_bottom_eq_zero (S y))
  · simpa only [characteristicValue_bottom_derivative] using
      hasDerivAt_characteristicValue (S x).1 (thirdEigenvalue (S x))
  · exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le hg (bottomGap_le_spectralWidth (S x)))) (ne_of_gt hg)

theorem contDiffAt_bottomEigenlineProjector (hS : ContDiffAt ℝ n (fun y ↦ (S y).1) x)
    (hn : n ≠ 0) (hg : 0 < bottomGap (S x)) :
    ContDiffAt ℝ n (fun y ↦ bottomEigenlineProjector (S y)) x := by
  have hm := contDiffAt_thirdEigenvalue S x hS hn hg
  have ht := contDiff_operatorTrace.contDiffAt.comp x hS
  have h2 := contDiff_secondInvariant.contDiffAt.comp x hS
  have hd : ContDiffAt ℝ n (fun y ↦ 3 * thirdEigenvalue (S y) ^ 2 -
      2 * operatorTrace (S y).1 * thirdEigenvalue (S y) + secondInvariant (S y).1) x := by fun_prop
  have hne : 3 * thirdEigenvalue (S x) ^ 2 -
      2 * operatorTrace (S x).1 * thirdEigenvalue (S x) + secondInvariant (S x).1 ≠ 0 := by
    rw [characteristicValue_bottom_derivative]
    exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le hg (bottomGap_le_spectralWidth (S x)))) (ne_of_gt hg)
  have hN := contDiff_invariantNumerator.contDiffAt.comp x (hS.prodMk hm)
  apply ((hd.inv hne).smul hN).congr_of_eventuallyEq
  have hc : ContinuousAt S x := tendsto_subtype_rng.mpr hS.continuousAt
  filter_upwards [(continuous_bottomGap.continuousAt.comp hc).eventually (lt_mem_nhds hg)] with y hy
  exact bottomEigenlineProjector_eq_invariants (S y) hy

theorem contDiffAt_expandingPlaneProjector (hS : ContDiffAt ℝ n (fun y ↦ (S y).1) x)
    (hn : n ≠ 0) (hg : 0 < bottomGap (S x)) :
    ContDiffAt ℝ n (fun y ↦ expandingPlaneProjector (S y)) x :=
  contDiffAt_const.sub (contDiffAt_bottomEigenlineProjector S x hS hn hg)

end Mettapedia.FluidDynamics.NavierStokes.BottomProjectorSmoothness

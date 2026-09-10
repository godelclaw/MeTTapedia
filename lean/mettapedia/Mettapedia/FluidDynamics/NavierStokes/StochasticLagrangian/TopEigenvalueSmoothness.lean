import Mettapedia.Analysis.SimpleImplicitRoot
import Mettapedia.Analysis.SecondDerivative
import Mettapedia.Analysis.OperatorQuadraticForm
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainSpectralInvariants

/-!
# Smooth top eigenvalues and nonnegative spectral curvature

A simple top root is smooth through collisions of the lower two roots.
Its second derivative dominates the frozen top-eigenvector Rayleigh second
derivative. The curvature sign uses a variational local minimum, not a
differentiable choice of eigenvectors.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TopEigenvalueSmoothness

open scoped Topology ContDiff RealInnerProductSpace
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain PancakeTopEigenvalueDerivative
open StrainSpectralInvariants PancakeTransverseEnergyFreezing

local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem contDiffAt_topEigenvalue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ∞ω} (S : E → SymmetricStrain) (x : E)
    (hS : ContDiffAt ℝ n (fun y ↦ (S y).1) x) (hn : n ≠ 0) (hg : 0 < topGap (S x)) :
    ContDiffAt ℝ n (fun y ↦ topEigenvalue (S y)) x := by
  have hc : ContinuousAt S x := tendsto_subtype_rng.mpr hS.continuousAt
  apply Mettapedia.Analysis.contDiffAt_of_simple_implicit_root
    (f := fun p : E × ℝ ↦ characteristicValue (S p.1).1 p.2)
    (c := spectralWidth (S x) * topGap (S x))
  · exact contDiff_characteristicValue.contDiffAt.comp (x, topEigenvalue (S x))
      ((hS.comp (x, topEigenvalue (S x)) contDiffAt_fst).prodMk contDiffAt_snd)
  · exact hn
  · exact lipschitzWith_topEigenvalue.continuous.continuousAt.comp hc
  · exact Filter.Eventually.of_forall (fun y ↦ characteristicValue_top_eq_zero (S y))
  · simpa only [characteristicValue_top_derivative] using
      hasDerivAt_characteristicValue (S x).1 (topEigenvalue (S x))
  · exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le hg (topGap_le_spectralWidth (S x)))) (ne_of_gt hg)

theorem rayleigh_second_derivative (S : ℝ → SymmetricStrain) (t : ℝ)
    (hS : ContDiffAt ℝ 2 (fun h ↦ (S h).1) t) (e : R3) :
    deriv (deriv (fun h ↦ ⟪e, (S h).1 e⟫)) t = ⟪e, deriv (deriv (fun h ↦ (S h).1)) t e⟫ := by
  have h := Mettapedia.Analysis.OperatorQuadraticForm.deriv_deriv_value hS
    (w := fun _ : ℝ ↦ e) contDiffAt_const
    (Filter.Eventually.of_forall (fun h a b ↦ ((S h).2 a b).symm))
  simpa only [Mettapedia.Analysis.OperatorQuadraticForm.value, deriv_const', deriv_const,
    inner_zero_right, inner_zero_left, mul_zero, zero_add] using h

theorem rayleigh_second_derivative_le (S : ℝ → SymmetricStrain) (t : ℝ)
    (hS : ContDiffAt ℝ 2 (fun h ↦ (S h).1) t) (hg : 0 < topGap (S t))
    (e : R3) (he : ‖e‖ = 1) (hpair : (S t).1 e = topEigenvalue (S t) • e) :
    ⟪e, deriv (deriv (fun h ↦ (S h).1)) t e⟫ ≤
      deriv (deriv (fun h ↦ topEigenvalue (S h))) t := by
  have hl := contDiffAt_topEigenvalue S t hS (by norm_num) hg
  have hq : ContDiffAt ℝ 2 (fun h ↦ ⟪e, (S h).1 e⟫) t :=
    contDiffAt_const.inner ℝ (hS.clm_apply contDiffAt_const)
  have hz : topEigenvalue (S t) - ⟪e, (S t).1 e⟫ = 0 := by
    rw [hpair, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
    ring
  have hm : IsLocalMin (fun h ↦ topEigenvalue (S h) - ⟪e, (S h).1 e⟫) t := by
    apply Filter.Eventually.of_forall
    intro h
    dsimp only
    rw [hz]
    exact sub_nonneg.mpr (rayleigh_le_constructedTopEigenvalue (S h).1 (S h).2 e he)
  have hn := Mettapedia.Analysis.second_derivative_nonneg_of_isLocalMin hm (hl.continuousAt.sub hq.continuousAt)
  have hd := Mettapedia.Analysis.deriv_deriv_linearCombination hl hq 1 (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg, rayleigh_second_derivative S t hS e] at hd
  rw [hd] at hn
  linarith

end Mettapedia.FluidDynamics.NavierStokes.TopEigenvalueSmoothness

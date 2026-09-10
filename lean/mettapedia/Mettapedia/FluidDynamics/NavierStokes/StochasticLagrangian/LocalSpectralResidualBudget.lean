import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralResidual
import Mettapedia.Analysis.ODE.AbsolutelyContinuousComparison

/-!
# A source-only bound for the actual material residual

The gap-weighted residual is absolutely continuous across eigenvalue
collisions. Its source is integrable on compact local intervals, derived
from absolute continuity of the largest eigenvalue and actual PDE
regularity. Dissipative comparison then bounds residual growth by the
integrated source, without an exponential factor.

The source still depends on the evolving solution. This is not a uniform
bound in terms of the initial data or a global continuation theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralResidualBudget

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeHigherDerivativeMoments
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeStrainSpectralFrame PancakeTopEigenvalueDerivative PancakeSpectralDefectEvolution
open PancakeSpectralDefectBudget LocalMaterialStrain LocalMaterialVorticity LocalVorticityDiffusion
open LocalSpectralDefect LocalSpectralResidual

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
  {a b : ℝ} (hI : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) T)

include hB hg hSum hu hX hI

theorem absolutelyContinuousOnInterval_residualAlong :
    AbsolutelyContinuousOnInterval (residualAlong s X) a b := by
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).mono hI
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI
  exact ((absolutelyContinuousOnInterval_topEigenvalue (symmetricStrainAlong s X) a b hS).smul
    hw.absolutelyContinuousOnInterval).sub (hS.clm_apply hw).absolutelyContinuousOnInterval

/-- Integrability is proved even though a chosen top eigenvector need not
be continuous at a collision. Its scalar contraction is the almost-everywhere
eigenvalue derivative plus the eigenvalue square. -/
theorem intervalIntegrable_sourceAlong :
    IntervalIntegrable (sourceAlong s X) volume a b := by
  let S := symmetricStrainAlong s X
  let lambda := fun t ↦ topEigenvalue (S t)
  have hS := (contDiffOn_strainAlong s g hg hSum hu hB X hX).mono hI
  have hw := (contDiffOn_vorticityAlong s g hg hSum hu X hX).mono hI
  have hR := (continuousOn_strainRemainderAlong s g hg hSum hu hB X hX).mono hI
  have hf := continuousOn_diffusionAlong s g hSum hu X hX hI
  have hl := absolutelyContinuousOnInterval_topEigenvalue S a b hS
  have hsource : IntervalIntegrable (fun t ↦
      (deriv lambda t + lambda t ^ 2) • vorticityAlong s X t -
        strainRemainderAlong s X t (vorticityAlong s X t) +
          spectralResidual (strainAlong s X t) (lambda t) (diffusionAlong s X t)) volume a b :=
    (((hl.intervalIntegrable_deriv.add (hl.continuousOn.pow 2).intervalIntegrable).smul_continuousOn
      hw.continuousOn).sub (hR.clm_apply hw.continuousOn).intervalIntegrable).add
        ((hl.continuousOn.smul hf).sub (hS.continuousOn.clm_apply hf)).intervalIntegrable
  apply hsource.congr_ae
  change ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
    (deriv lambda t + lambda t ^ 2) • vorticityAlong s X t -
      strainRemainderAlong s X t (vorticityAlong s X t) +
        spectralResidual (strainAlong s X t) (lambda t) (diffusionAlong s X t) = sourceAlong s X t
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hl.ae_differentiableAt] with t ht hmem
  have htI := Set.uIoc_subset_uIcc hmem
  have hdS : HasDerivAt (fun τ ↦ (S τ).1)
      (-(S t).1 * (S t).1 + strainRemainderAlong s X t) t :=
    hasDerivAt_strainAlong s g hg hSum hu X hX t (hI htI)
  have hd := hasDerivAt_topEigenvalue_of_differentiableAt S _ t hdS (ht htI)
  rw [eigenvalueRate_strainSquare (S t).1 (strainRemainderAlong s X t) _ _
    ((orderedEigenframe (S t).1 (S t).2).eigenbasis.norm_eq_one 0)
    ((orderedEigenframe (S t).1 (S t).2).apply_eigenbasis 0)] at hd
  have he : deriv lambda t + lambda t ^ 2 =
      ⟪(orderedEigenframe (S t).1 (S t).2).eigenbasis 0,
        strainRemainderAlong s X t ((orderedEigenframe (S t).1 (S t).2).eigenbasis 0)⟫ := by
    rw [hd.deriv]
    dsimp [lambda, topEigenvalue]
    ring
  simp only [he]
  rfl

/-- Actual material residual growth is paid solely by the actual source.
There is no spectral-gap assumption and no exponential amplification factor.
The size of the source integral remains to be estimated dynamically. -/
theorem norm_residualAlong_le_initial_add_integral (hab : a ≤ b) :
    ‖residualAlong s X b‖ ≤ ‖residualAlong s X a‖ + ∫ t in a..b, ‖sourceAlong s X t‖ := by
  let A : ℝ → R3 →L[ℝ] R3 := fun t ↦
    -topEigenvalue (symmetricStrainAlong s X t) • ContinuousLinearMap.id ℝ R3
  apply Mettapedia.Analysis.ODE.norm_le_initial_add_integral_of_ae_dissipative A hab
    (absolutelyContinuousOnInterval_residualAlong s hB g hg hSum hu X hX hI)
    (intervalIntegrable_sourceAlong s hB g hg hSum hu X hX hI)
  · convert! ae_hasDerivAt_residualAlong s hB g hg hSum hu X hX hI using 1
  · intro t ht v
    have hm := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t (Set.Ioo_subset_Icc_self (hI ht))))
    have hl := topEigenvalue_symmetricStrainAlong_nonneg s X t hm
    simp only [A, smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (sq_nonneg _)

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralResidualBudget

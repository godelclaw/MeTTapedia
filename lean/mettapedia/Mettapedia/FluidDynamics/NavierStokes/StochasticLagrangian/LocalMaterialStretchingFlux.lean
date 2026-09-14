import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialStretching

/-!
# Pressure-resolved material rate of the longitudinal stretching tensor

The tensor is the actual inviscid field `-ω ⊗ Sω` before the spatial
gradient projection. Its material rate has the quadratic stretching
tensor, pressure-Hessian action, and explicit viscous product terms.
No strain-square or spin-square term remains hidden in the rate.

Material differentiation does not commute with spatial projection; this
file makes no such interchange and does not assert a global work bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStretchingFlux

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths PancakeCurlOutputTail
open PancakeHigherDerivativeMoments LocalMaterialVorticity LocalMaterialStretching
open LocalLowDiffusionBudget LocalAlignmentForcing LongitudinalGradientFlux LongitudinalJointFlux

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {ν T B : ℝ} {u₀ : FourierVelocity}

def fluxAlong (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3)
    (t : ℝ) (j : Fin 3) : R3 :=
  -(vorticityAlong s X t j • stretchingAlong s X t)

def pressureRateAlong (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3)
    (t : ℝ) (j : Fin 3) : R3 :=
  vorticityAlong s X t j • pressureHessianAlong s X t (vorticityAlong s X t)

def viscousRateAlong (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3)
    (t : ℝ) (j : Fin 3) : R3 :=
  -(diffusionAlong s X t j • stretchingAlong s X t) -
    vorticityAlong s X t j • stretchingDiffusionAlong s X t

def rateAlong (s : LocalInfiniteVelocitySolution ν u₀ T B) (X : ℝ → X3)
    (t : ℝ) (j : Fin 3) : R3 :=
  -(stretchingAlong s X t j • stretchingAlong s X t) +
    pressureRateAlong s X t j + viscousRateAlong s X t j

theorem fluxAlong_eq_fluxField (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) (hm : Summable (fourierMoment 1 (s.coefficients t))) (j : Fin 3) :
    fluxAlong s X t j = fluxField 0 (s.coefficients t) j (torusPoint (X t)) := by
  rw [fluxField_apply 0 _ hm, flux]
  simp only [mul_zero, zero_smul, add_zero]
  rfl

theorem sum_norm_fluxAlong_sq (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) :
    (∑ j : Fin 3, ‖fluxAlong s X t j‖ ^ 2) =
      ‖vorticityAlong s X t‖ ^ 2 * ‖stretchingAlong s X t‖ ^ 2 := by
  simp only [fluxAlong, norm_neg, norm_smul, mul_pow, ← Finset.sum_mul]
  rw [← PiLp.norm_sq_eq_of_L2]

/-- Exact signed work against an arbitrary tensor, before any absolute value. -/
theorem sum_inner_rateAlong (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (X : ℝ → X3) (t : ℝ) (R : Fin 3 → R3) :
    (∑ j : Fin 3, ⟪R j, rateAlong s X t j⟫) =
      -⟪∑ j, stretchingAlong s X t j • R j, stretchingAlong s X t⟫ +
        ⟪∑ j, vorticityAlong s X t j • R j,
          pressureHessianAlong s X t (vorticityAlong s X t)⟫ +
        ∑ j, ⟪R j, viscousRateAlong s X t j⟫ := by
  simp only [rateAlong, pressureRateAlong, inner_add_right, inner_neg_right,
    real_inner_smul_right, sum_inner, real_inner_smul_left,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

variable (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hX

theorem hasDerivAt_fluxAlong (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
    HasDerivAt (fun τ ↦ fluxAlong s X τ j) (rateAlong s X t j) t := by
  have hw := (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_vorticityAlong s g hg hSum hu X hX t ht)
  change HasDerivAt (fun τ ↦ vorticityAlong s X τ j)
    (stretchingAlong s X t j + diffusionAlong s X t j) t at hw
  have ha := hasDerivAt_stretchingAlong s g hg hSum hu X hX t ht
  have h := (hw.smul ha).neg
  convert! h using 1
  simp only [rateAlong, pressureRateAlong, viscousRateAlong, add_smul, smul_add, smul_neg]
  abel

theorem hasDerivAt_fluxField_material (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (j : Fin 3) :
    HasDerivAt (fun τ ↦ fluxField 0 (s.coefficients τ) j (torusPoint (X τ)))
      (rateAlong s X t j) t := by
  apply (hasDerivAt_fluxAlong s g hg hSum hu X hX t ht j).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
  exact (fluxAlong_eq_fluxField s X τ
    (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩))) j).symm

theorem hasDerivAt_fluxAlong_energy (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ ∑ j : Fin 3, ‖fluxAlong s X τ j‖ ^ 2)
      (2 * ∑ j : Fin 3, ⟪fluxAlong s X t j, rateAlong s X t j⟫) t := by
  have h := HasDerivAt.sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      (hasDerivAt_fluxAlong s g hg hSum hu X hX t ht j).norm_sq)
  convert! h using 1
  rw [Finset.mul_sum]

end Mettapedia.FluidDynamics.NavierStokes.LocalMaterialStretchingFlux

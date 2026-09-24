import Mettapedia.Analysis.SignedCrossKernelEvolution
import Mettapedia.Analysis.HighAmplitudeWeightEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityPairAngle
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityKernelTransport

/-!
# Actual signed paired-source evolution

The full vorticity is used at both endpoints; only the Biot–Savart kernel
is finitely reconstructed. Kernel transport is its actual Fourier-character
derivative. The exact source derivative retains the mean-strain commutator,
strain variation, radial amplitude growth and both viscous contributions.
No time budget or uniform kernel-derivative estimate is supplied here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories LocalLowDiffusionBudget LocalJointDiffusionBudget
open LocalAlignmentForcing LocalInitialSpectral LocalVorticityPairAngle
open VorticityStretchingKernel
open Mettapedia.Analysis.SignedCrossKernel Mettapedia.Analysis.EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem mean_fullStrain_symmetric (u : FourierVelocity) (x y : T3) (v w : R3) :
    ⟪meanStrain (fullStrainOperator u x) (fullStrainOperator u y) v, w⟫ =
      ⟪v, meanStrain (fullStrainOperator u x) (fullStrainOperator u y) w⟫ := by
  have hx := (fullSymmetricStrain u x).2 v w
  have hy := (fullSymmetricStrain u y).2 v w
  simp only [meanStrain, smul_apply, add_apply, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right]
  change ⟪v, fullStrainOperator u x w⟫ = ⟪fullStrainOperator u x v, w⟫ at hx
  change ⟪v, fullStrainOperator u y w⟫ = ⟪fullStrainOperator u y v, w⟫ at hy
  rw [← hx, ← hy]

def materialPairedRate (n : ℕ) (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (x y : T3) (v w : X3) : ℝ :=
  pairedStretchRate n (fullStrainOperator u x) (fullStrainOperator u y)
    (kernel modes (x - y)) (kernelDirectionalRate modes (x - y) (v - w))
    (fullVorticity u x) (fullVorticity u y)
    (nu • fullVorticityLaplacian u x) (nu • fullVorticityLaplacian u y)

def amplitudeWeightRate (L : ℝ) (u : FourierVelocity) (nu : ℝ) (x : T3) : ℝ :=
  L * ⟪fullVorticity u x,
    fullStrainOperator u x (fullVorticity u x) + nu • fullVorticityLaplacian u x⟫ /
      ‖fullVorticity u x‖ ^ 3

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
  (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
  (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)

include hg hSum hu hab hI ht hX hY

theorem hasDerivAt_pairedStretch_path_of_kernel (n : ℕ) (H : ℝ → R3 →L[ℝ] R3)
    (Hdot : R3 →L[ℝ] R3) (hH : HasDerivAt H Hdot t) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1)) (H τ)
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (pairedStretchRate n
        (fullStrainOperator (s.coefficients t) (torusPoint (X t)))
        (fullStrainOperator (s.coefficients t) (torusPoint (Y t))) (H t) Hdot
        (fullVorticity (s.coefficients t) (torusPoint (X t)))
        (fullVorticity (s.coefficients t) (torusPoint (Y t)))
        (nu • fullVorticityLaplacian (s.coefficients t) (torusPoint (X t)))
        (nu • fullVorticityLaplacian (s.coefficients t) (torusPoint (Y t)))) t := by
  have hwX := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hwY := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
    (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht))))
  have hm2 := summable_fourierMoment_of_le _ (by norm_num : 2 ≤ 3) hm
  exact hasDerivAt_pairedStretch n _ _ _ _ _ hwX hwY hH
    (cross_fullStrain_apply_add _ hm2 (s.transverse t) _ _ _)
    (cross_fullStrain_apply_add _ hm2 (s.transverse t) _ _ _)
    (mean_fullStrain_symmetric _ _ _)

theorem hasDerivAt_pairedStretch_path (n : ℕ) (modes : Finset Wavevector) :
    HasDerivAt (fun τ ↦ pairedStretch (2 * (n + 1))
      (kernel modes (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (materialPairedRate n modes (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
        (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  exact hasDerivAt_pairedStretch_path_of_kernel s g hg hSum hu a b hab hI X Y t ht hX hY n _ _
    (hasDerivAt_kernel_pair_path modes X Y _ _ t hX hY)

theorem hasDerivAt_highAmplitudeStretch_path_left (n : ℕ) (modes : Finset Wavevector)
    (L : ℝ) (hL : 0 < L)
    (hLa : L < ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖)
    (hxy : ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖ <
      ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖) :
    HasDerivAt (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
      (kernel modes (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (amplitudeWeightRate L (s.coefficients t) nu (torusPoint (X t)) *
          pairedStretch (2 * (n + 1)) (kernel modes (torusPoint (X t) - torusPoint (Y t)))
            (fullVorticity (s.coefficients t) (torusPoint (X t)))
            (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        (1 - lowAmplitudeWeight L (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t)))) *
          materialPairedRate n modes (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
            (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  exact (hasDerivAt_highAmplitudeWeight_of_left_lt hx hy.continuousAt hL hLa hxy).mul
    (hasDerivAt_pairedStretch_path s g hg hSum hu a b hab hI X Y t ht hX hY n modes)

theorem hasDerivAt_highAmplitudeStretch_path_right (n : ℕ) (modes : Finset Wavevector)
    (L : ℝ) (hL : 0 < L)
    (hLb : L < ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖)
    (hyx : ‖fullVorticity (s.coefficients t) (torusPoint (Y t))‖ <
      ‖fullVorticity (s.coefficients t) (torusPoint (X t))‖) :
    HasDerivAt (fun τ ↦ highAmplitudeStretch (2 * (n + 1)) L
      (kernel modes (torusPoint (X τ) - torusPoint (Y τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (X τ)))
      (fullVorticity (s.coefficients τ) (torusPoint (Y τ))))
      (amplitudeWeightRate L (s.coefficients t) nu (torusPoint (Y t)) *
          pairedStretch (2 * (n + 1)) (kernel modes (torusPoint (X t) - torusPoint (Y t)))
            (fullVorticity (s.coefficients t) (torusPoint (X t)))
            (fullVorticity (s.coefficients t) (torusPoint (Y t))) +
        (1 - lowAmplitudeWeight L (fullVorticity (s.coefficients t) (torusPoint (X t)))
          (fullVorticity (s.coefficients t) (torusPoint (Y t)))) *
          materialPairedRate n modes (s.coefficients t) nu (torusPoint (X t)) (torusPoint (Y t))
            (liftedVelocity s t (X t)) (liftedVelocity s t (Y t))) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  exact (hasDerivAt_highAmplitudeWeight_of_right_lt hx.continuousAt hy hL hLb hyx).mul
    (hasDerivAt_pairedStretch_path s g hg hSum hu a b hab hI X Y t ht hX hY n modes)

end Mettapedia.FluidDynamics.NavierStokes.LocalPairedStretchEvolution

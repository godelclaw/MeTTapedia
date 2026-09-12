import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRadialImageEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpaceTimeExtension
import Mettapedia.Analysis.SignedCrossKernelRegularity

/-!
# Signed time identity for a material radial image

For a fixed cutoff and fixed image lift, the complete signed density is
absolutely continuous along the actual local solution on a compact interior
interval with nonzero image separation. Its time increment is the integral
of all four material contributions, together. No separate sign, uniform
cutoff estimate or image-sum interchange is inferred from this identity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialImageIntegral

open MeasureTheory
open scoped ContDiff
open PeriodicFourierTriad PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeCurlOutputTail PancakeFourierMaterialPaths PancakeLocalMaterialTrajectories
open LocalLowDiffusionBudget LocalRadialImageEvolution
open Mettapedia.Analysis SignedCrossKernel
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
  (X Y : ℝ → X3) (hX : LocallyLipschitz X) (hY : LocallyLipschitz Y)

include hg hSum hu hab hI hX hY

theorem absolutelyContinuousOnInterval_sourceDensity_path (n N : ℕ) (z : R3)
    (hz : ∀ t ∈ Set.Icc a b, imageSeparation z (X t) (Y t) ≠ 0) :
    AbsolutelyContinuousOnInterval
      (fun τ ↦ sourceDensity n N z (s.coefficients τ) (X τ) (Y τ)) a b := by
  let w : ℝ × X3 → R3 := fun p ↦
    fullVorticity (LocalSpaceTimeExtension.coefficients s a b hab p.1) (torusPoint p.2)
  have hw : LocallyLipschitz w :=
    LocalSpaceTimeExtension.locallyLipschitz_fullVorticity s a b hab hI g hg hSum hu
  have hx : LocallyLipschitz (fun τ ↦ w (τ, X τ)) :=
    hw.comp (g := fun τ ↦ (τ, X τ)) (LocallyLipschitz.id.prodMk hX)
  have hy : LocallyLipschitz (fun τ ↦ w (τ, Y τ)) :=
    hw.comp (g := fun τ ↦ (τ, Y τ)) (LocallyLipschitz.id.prodMk hY)
  have hkernel : LocallyLipschitz (fun τ ↦ RadialRieszRegularization.tensor N (imageSeparation z (X τ) (Y τ))) := by
    have hk := ((RadialRieszRegularization.contDiff_tensor (d := 3) N).of_le
      (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz
    let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
    have hsep : LocallyLipschitz (fun τ ↦ imageSeparation z (X τ) (Y τ)) :=
      (LocallyLipschitz.const z).add (L.lipschitz.locallyLipschitz.comp (g := fun τ ↦ X τ - Y τ) (hX.sub hY))
    exact hk.comp hsep
  have hac := AbsolutelyContinuousComposition.of_locallyLipschitz
    (a := a) (b := b) (locallyLipschitz_pairedStretch_even (n + 1) hkernel hx hy)
  apply AbsolutelyContinuousComposition.congr hac
  intro τ hτ
  have hm : τ ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hτ
  have he := LocalSpaceTimeExtension.coefficients_eq s a b hab τ hm
  simp only [w, he]
  exact RadialRieszRegularization.pairedStretch_tensor N (2 * (n + 1))
    (EuclideanSpace.single 0 1) (by simp) (hz τ hm) _ _

theorem integrated_sourceDensity_path_identity
    (hDX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (liftedVelocity s t (X t)) t)
    (hDY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (n N : ℕ) (z : R3) (hz : ∀ t ∈ Set.Icc a b, imageSeparation z (X t) (Y t) ≠ 0) :
    IntervalIntegrable (fun τ ↦ materialRate n N z (s.coefficients τ) nu (X τ) (Y τ)) volume a b ∧
      (∫ τ in a..b, materialRate n N z (s.coefficients τ) nu (X τ) (Y τ)) =
        sourceDensity n N z (s.coefficients b) (X b) (Y b) -
          sourceDensity n N z (s.coefficients a) (X a) (Y a) := by
  have hac := absolutelyContinuousOnInterval_sourceDensity_path s g hg hSum hu a b hab hI X Y hX hY n N z hz
  have heq : ∀ᵐ t, t ∈ Set.uIcc a b →
      deriv (fun τ ↦ sourceDensity n N z (s.coefficients τ) (X τ) (Y τ)) t =
        materialRate n N z (s.coefficients t) nu (X t) (Y t) := by
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t he hmem
    have hm : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using hmem
    have ht : t ∈ Set.Ioo a b := he.mpr hm
    exact (hasDerivAt_sourceDensity_path s g hg hSum hu a b hab hI X Y t ht
      (hDX t ht) (hDY t ht) n N z (hz t hm)).deriv
  refine ⟨hac.intervalIntegrable_deriv.congr_ae ?_, ?_⟩
  · apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)
  · rw [← hac.integral_deriv_eq_sub]
    symm
    apply intervalIntegral.integral_congr_ae
    filter_upwards [heq] with t ht hmem
    exact ht (Set.uIoc_subset_uIcc hmem)

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialImageIntegral

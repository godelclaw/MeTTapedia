import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralDiffusionDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion

/-!
# Physical-data diffusion depletion and coherent damping

The spectral residual dominates the top gap times the defect, hence the
squared top gap times line misalignment. An explicit strain-gradient
condition lets half the residual damping pay the depleted viscous cost.
The condition and nonviscous source are not assumed to hold uniformly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDiffusionBudget

open scoped ComplexConjugate RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeFrequencyProjectorCommutator
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralDefectEvolution PancakeAnisotropyDepletion
open PancakeLocalInfiniteVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open LocalLowDiffusionBudget LocalSpatialTopEigenvalue LocalSpatialVorticityJets
open LocalSpectralDefectDiffusion LocalSpectralDefectBalance LocalSpatialSpectralBounds
open LocalSpectralDiffusionDepletion

local notation "T3" => UnitAddTorus (Fin 3)

theorem gap_sq_mul_misalignment_le_residualSquare (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) :
    topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2 * ‖misalignment chi modes u x‖ ^ 2 ≤
      residualSquare chi modes u x := by
  have hm := mul_le_mul_of_nonneg_left (SpectralAnisotropyEnvelope.topGap_mul_lineRemainder_sq_le
    (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x))
    (topGap_nonneg (spatialStrain modes (filteredVelocity chi u) x))
  have hz := PancakeSpectralResidualDepletion.topGap_mul_defect_le_norm_topSpectralResidual_sq
    (spatialStrain modes (filteredVelocity chi u) x) (fullVorticity u x)
  simpa only [residualSquare, LocalAlignmentForcing.residual, misalignment, pow_two, mul_assoc] using hm.trans hz

theorem depletedCost_le_half_residual (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (nu delta : ℝ) (hd : 0 < delta) (x : T3)
    (hsmall : 32 * nu * strainGradientSquare chi modes u x ≤
      delta * topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2) :
    (16 * nu / delta) * strainGradientSquare chi modes u x * ‖misalignment chi modes u x‖ ^ 2 ≤
      residualSquare chi modes u x / 2 := by
  have hcoeff : (16 * nu / delta) * strainGradientSquare chi modes u x ≤
      topGap (spatialStrain modes (filteredVelocity chi u) x) ^ 2 / 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hsmall]
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ‖misalignment chi modes u x‖)
  have hz := gap_sq_mul_misalignment_le_residualSquare chi modes u x
  nlinarith only [hm, hz]

theorem control_half_residual_bound {chi : Wavevector → ℂ} {modes outputs : Finset Wavevector}
    {u : ℝ → FourierVelocity} {nu t : ℝ} {x : T3}
    (h : LocalSpectralDefectControl.Control chi modes outputs u nu t x) (hnu : 0 ≤ nu)
    (hg : 0 < topGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (delta : ℝ) (hd : 0 < delta)
    (hsmall : 32 * nu * strainGradientSquare chi modes (u t) x ≤
      delta * topGap (spatialStrain modes (filteredVelocity chi (u t)) x) ^ 2) :
    deriv (fun h ↦ frozenEnergy chi modes u delta t x h) 0 -
        nu * energyLaplacian chi modes (u t) delta x + residualSquare chi modes (u t) x / 2 +
        nu * curvature chi modes (u t) x * ‖misalignment chi modes (u t) x‖ ^ 2 +
        nu * delta * ∑ j : Fin 3, ‖fullCurlGradient (u t) j x‖ ^ 2 ≤
      nonviscousSource chi modes outputs (u t) delta x := by
  have hp := control_depleted_bound h hnu hg delta hd
  have hc := depletedCost_le_half_residual chi modes (u t) nu delta hd x hsmall
  linarith only [hp, hc]

/-- One physical solution satisfies the original exact balance and the
depleted bound, simultaneously for all positive constant regularizations. -/
theorem exists_physical_localDepletedSpectralDiffusion (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 9 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hdiv : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∀ (chi : Wavevector → ℂ) (C : ℝ), (∀ q, ‖chi q‖ ≤ C) →
      ∀ modes outputs : Finset Wavevector, (∀ q, q ∉ modes → chi q = 0) →
      (∀ q, chi (-q) = conj (chi q)) → modes ⊆ outputs →
      (∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs) →
      (∀ k, -k ∈ modes ↔ k ∈ modes) → (∀ k ∈ modes, frequencyVec k ≠ 0) →
      ∀ (a b : ℝ), a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T →
      ∀ t ∈ Set.Ioo a b, ∀ x : T3,
        0 < topGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
        LocalSpectralDefectControl.Control chi modes outputs s.coefficients nu t x ∧
        ∀ delta > (0 : ℝ),
          deriv (fun h ↦ frozenEnergy chi modes s.coefficients delta t x h) 0 -
              nu * energyLaplacian chi modes (s.coefficients t) delta x +
              residualSquare chi modes (s.coefficients t) x +
              nu * curvature chi modes (s.coefficients t) x * ‖misalignment chi modes (s.coefficients t) x‖ ^ 2 +
              nu * delta * ∑ j : Fin 3, ‖fullCurlGradient (s.coefficients t) j x‖ ^ 2 ≤
            nonviscousSource chi modes outputs (s.coefficients t) delta x +
              (16 * nu / delta) * strainGradientSquare chi modes (s.coefficients t) x *
                ‖misalignment chi modes (s.coefficients t) x‖ ^ 2 := by
  obtain ⟨T, hT, B, hB, s, hC⟩ :=
    LocalSpectralDefectControl.exists_physical_localSpectralDefectControl nu hnu f hf hr hdiv hzero
  refine ⟨T, hT, B, hB, s, ?_⟩
  intro chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI t ht x hg
  have hc := hC chi C hchi modes outputs hcut hchir hsub hout hs hk a b hab hI t ht x hg
  exact ⟨hc, fun delta hd ↦ control_depleted_bound hc hnu.le hg delta hd⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalSpectralDiffusionBudget

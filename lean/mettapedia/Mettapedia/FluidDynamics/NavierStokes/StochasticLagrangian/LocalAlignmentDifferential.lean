import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTangency

/-!
# Alignment differentiation along instantaneously material curves

The algebraic full-field rate is the derivative of the actual alignment
energy whenever the largest strain eigenvalue is differentiable along
the curve. Only instantaneous tangency to the full velocity is needed.
The curve is not assumed to solve the material ODE at other times.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentDifferential

open scoped Topology ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeFrequencyProjectorCommutator
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeRegularizedMaterialRate
open LocalMaterialVorticity LocalFilteredSpectralDefect LocalFilteredViscousDefect
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open LocalAlignmentTransport LocalVorticityTangency

local notation "X3" => Fin 3 → ℝ

theorem hasDerivAt_alignmentEnergy_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
    (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
    (hchir : ∀ q, chi (-q) = conj (chi q))
    (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (delta a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hlambda : DifferentiableAt ℝ
      (fun τ ↦ topEigenvalue (LocalFilteredStrain.strainAlong s chi modes X τ)) t) :
    HasDerivAt (fun τ ↦ alignmentEnergy chi modes (s.coefficients τ) delta (torusPoint (X τ)))
      (materialRate chi modes outputs (s.coefficients t) delta nu (torusPoint (X t))) t := by
  have htT := hI (Set.Ioo_subset_Icc_self ht)
  have hS := LocalFilteredStrain.hasDerivAt_strainAlong s chi C hchi modes outputs
    hcut hchir hsub hout hs hk X t htT hX
  rw [remainderAlong_viscous_split s chi modes outputs hsub hcut X t, ← add_assoc] at hS
  have hw := hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  change HasDerivAt (vorticityAlong s X)
    (LocalMaterialVorticity.strainAlong s X t (vorticityAlong s X t) +
      nu • vorticityLaplacianAlong s X t) t at hw
  have hw' : HasDerivAt (vorticityAlong s X)
      ((LocalFilteredStrain.strainAlong s chi modes X t).1 (vorticityAlong s X t) +
        strainMismatchAlong s chi modes X t + nu • vorticityLaplacianAlong s X t) t := by
    apply hw.congr_deriv
    simp only [strainMismatchAlong, sub_apply]
    abel
  exact hasDerivAt_regularizedEnergy (LocalFilteredStrain.strainAlong s chi modes X)
    (vorticityAlong s X) _ _ delta t hS hw' hlambda

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentDifferential

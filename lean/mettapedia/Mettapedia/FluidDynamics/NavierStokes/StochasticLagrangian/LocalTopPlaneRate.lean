import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TopPlaneGapTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpectralFunctionDifferentiability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalClusterMaterialRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomSpectralProjectorPolynomial

/-!
# Actual top-plane gap evolution and the remaining material source

Scalar differentiability of both extreme eigenvalues is derived almost
everywhere. The resulting top-gap rate and plane-mixing contribution are
retained with their signs in the actual NS material estimate. Only the
part transverse to the expanding plane uses an absolute norm bound.
No time-integrated payment of the signed plane source is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalTopPlaneRate

open scoped Topology RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution PancakeStrainSpectralFrame
open LocalClusterAnisotropy LocalSpectralFunctionDifferentiability LocalClusterMaterialRate
open LocalAlignmentForcing LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentRegularization
open StrainEigenvalueContinuity PancakeTopEigenvalueDerivative TopPlaneGapTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def gapRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : ℝ :=
  deriv (fun h ↦ topGap (frozenStrain chi modes u t x h)) 0

def gapSource (chi : Wavevector → ℂ) (modes outputs : Finset Wavevector)
    (u : ℝ → FourierVelocity) (delta nu t : ℝ) (x : T3) : ℝ :=
  let S := spatialStrain modes (filteredVelocity chi (u t)) x
  let R := jointRemainder chi modes outputs (u t) nu x
  let w := fullVorticity (u t) x
  planeSource S R w (gapRate chi modes u t x) +
    4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect S w / bottomGap S) +
    2 * ⟪residual chi modes (u t) x, strainMismatch chi modes (u t) x + nu • fullVorticityLaplacian (u t) x⟫ +
    delta * vorticityNormRate (u t) nu x

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)

include hchi hcut hchir hsub hout hs hk

theorem hasDerivAt_frozenTopGap (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hL : ScalarDifferentiable topEigenvalue chi modes s.coefficients t x)
    (hB : ScalarDifferentiable thirdEigenvalue chi modes s.coefficients t x) :
    HasDerivAt (fun h ↦ topGap (frozenStrain chi modes s.coefficients t x h))
      (topGapStrainRate (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)
        (jointRemainder chi modes outputs (s.coefficients t) nu x)) 0 := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have h := hasDerivAt_topGap_strainEquation (frozenStrain chi modes s.coefficients t x)
    (jointRemainder chi modes outputs (s.coefficients t) nu x) 0
    (by simpa only [frozenStrain_zero] using hS) hL hB
  change HasDerivAt _ (topGapStrainRate (frozenStrain chi modes s.coefficients t x 0)
    (jointRemainder chi modes outputs (s.coefficients t) nu x)) 0 at h
  rw [frozenStrain_zero] at h
  exact h

theorem abs_jointAnisotropy_sub_planeSource_le (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hL : ScalarDifferentiable topEigenvalue chi modes s.coefficients t x)
    (hB : ScalarDifferentiable thirdEigenvalue chi modes s.coefficients t x)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) (w : R3) :
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let R := jointRemainder chi modes outputs (s.coefficients t) nu x
    |remainderAnisotropy R (topVector S) w - planeSource S R w (gapRate chi modes s.coefficients t x)| ≤
      4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect S w / bottomGap S) := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have h := abs_remainderAnisotropy_sub_planeSource_le (frozenStrain chi modes s.coefficients t x)
    (jointRemainder chi modes outputs (s.coefficients t) nu x) 0
    (by simpa only [frozenStrain_zero] using hS) hL hB
    (by simpa only [frozenStrain_zero] using hg) w
  simpa only [frozenStrain_zero, gapRate] using h

theorem ae_ae_abs_jointAnisotropy_sub_planeSource_le (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) → ∀ w : R3,
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let R := jointRemainder chi modes outputs (s.coefficients t) nu x
    |remainderAnisotropy R (topVector S) w - planeSource S R w (gapRate chi modes s.coefficients t x)| ≤
      4 * ‖R‖ * ‖w‖ * Real.sqrt (topSpectralDefect S w / bottomGap S) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB topEigenvalue 1 lipschitzWith_topEigenvalue,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB thirdEigenvalue 1 lipschitzWith_thirdEigenvalue]
    with t ht htop hbottom
  filter_upwards [htop, hbottom] with x hx hy hg w
  exact abs_jointAnisotropy_sub_planeSource_le s chi C hchi modes outputs hcut hchir hsub hout hs hk
    t (hI (Set.Ioo_subset_Icc_self ht)) x hx hy hg w

theorem ae_ae_materialRate_add_residual_le_gapSource (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) (delta : ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      materialRate chi modes outputs (s.coefficients t) delta nu x +
        ‖residual chi modes (s.coefficients t) x‖ ^ 2 ≤
      gapSource chi modes outputs s.coefficients delta nu t x := by
  filter_upwards [ae_ae_abs_jointAnisotropy_sub_planeSource_le s chi C hchi modes outputs hcut hchir
    hsub hout hs hk hB a b hab hI] with t ht
  exact ht.mono (fun x hx hg ↦ by
    have h := (abs_le.mp (hx hg (fullVorticity (s.coefficients t) x))).2
    rw [materialRate_add_residual_eq_joint]
    unfold gapSource
    linarith)

/-- The actual material projector derivatives exist almost everywhere
on the bottom-gap-separated branch, including top eigenvalue collisions. -/
theorem ae_ae_differentiableAt_frozenProjectors (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector
        (frozenStrain chi modes s.coefficients t x h)) 0 ∧
      DifferentiableAt ℝ (fun h ↦ expandingPlaneProjector
        (frozenStrain chi modes s.coefficients t x h)) 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB topEigenvalue 1 lipschitzWith_topEigenvalue,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB thirdEigenvalue 1 lipschitzWith_thirdEigenvalue]
    with t ht htop hbottom
  filter_upwards [htop, hbottom] with x hx hy hg
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk
    t (hI (Set.Ioo_subset_Icc_self ht)) x
  have hg' : 0 < bottomGap (frozenStrain chi modes s.coefficients t x 0) := by
    simpa only [frozenStrain_zero] using hg
  exact ⟨BottomSpectralProjectorPolynomial.differentiableAt_bottomEigenlineProjector
      (frozenStrain chi modes s.coefficients t x) _ 0 hS hx hy hg',
    BottomSpectralProjectorPolynomial.differentiableAt_expandingPlaneProjector
      (frozenStrain chi modes s.coefficients t x) _ 0 hS hx hy hg'⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalTopPlaneRate

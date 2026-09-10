import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalTopPlaneRate
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.BottomProjectorMotion

/-!
# Quantitative material motion of the actual expanding-plane projector

The derivative is defined from the actual frozen material path. Its
existence and bounds are derived almost everywhere, not assumed. The
remainder retains the pressure, subgrid, transport, and viscous terms.
No time-integrated bound for the remainder/gap ratio is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectorMotion

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open LocalClusterAnisotropy LocalSpectralFunctionDifferentiability
open StrainEigenvalueContinuity PancakeTopEigenvalueDerivative BottomProjectorMotion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def planeRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : R3 →L[ℝ] R3 :=
  deriv (fun h ↦ expandingPlaneProjector (frozenStrain chi modes u t x h)) 0

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)

include hchi hcut hchir hsub hout hs hk

theorem norm_planeRate_le (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hL : ScalarDifferentiable topEigenvalue chi modes s.coefficients t x)
    (hB : ScalarDifferentiable thirdEigenvalue chi modes s.coefficients t x)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) :
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    ‖planeRate chi modes s.coefficients t x‖ ≤
      2 * ‖bottomCoupling S (jointRemainder chi modes outputs (s.coefficients t) nu x)‖ / bottomGap S := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have h := norm_deriv_expandingPlaneProjector_le (frozenStrain chi modes s.coefficients t x)
    (jointRemainder chi modes outputs (s.coefficients t) nu x) 0
    (by simpa only [frozenStrain_zero] using hS) hL hB
    (by simpa only [frozenStrain_zero] using hg)
  simpa only [frozenStrain_zero, planeRate] using h

theorem abs_inner_planeRate_le (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hL : ScalarDifferentiable topEigenvalue chi modes s.coefficients t x)
    (hB : ScalarDifferentiable thirdEigenvalue chi modes s.coefficients t x)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x)) (w : R3) :
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    |⟪w, planeRate chi modes s.coefficients t x w⟫| ≤
      4 * ‖bottomCoupling S (jointRemainder chi modes outputs (s.coefficients t) nu x)‖ / bottomGap S *
        ‖bottomEigenlineProjector S w‖ * ‖expandingPlaneProjector S w‖ := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have h := abs_inner_deriv_expandingPlaneProjector_le (frozenStrain chi modes s.coefficients t x)
    (jointRemainder chi modes outputs (s.coefficients t) nu x) 0
    (by simpa only [frozenStrain_zero] using hS) hL hB
    (by simpa only [frozenStrain_zero] using hg) w
  simpa only [frozenStrain_zero, planeRate] using h

theorem ae_ae_planeRate_bounds (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let K := bottomCoupling S (jointRemainder chi modes outputs (s.coefficients t) nu x)
    ‖planeRate chi modes s.coefficients t x‖ ≤ 2 * ‖K‖ / bottomGap S ∧
      ∀ w : R3, |⟪w, planeRate chi modes s.coefficients t x w⟫| ≤
        4 * ‖K‖ / bottomGap S * ‖bottomEigenlineProjector S w‖ * ‖expandingPlaneProjector S w‖ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB topEigenvalue 1 lipschitzWith_topEigenvalue,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB thirdEigenvalue 1 lipschitzWith_thirdEigenvalue]
    with t ht htop hbottom
  filter_upwards [htop, hbottom] with x hx hy hg
  exact ⟨norm_planeRate_le s chi C hchi modes outputs hcut hchir hsub hout hs hk
      t (hI (Set.Ioo_subset_Icc_self ht)) x hx hy hg,
    abs_inner_planeRate_le s chi C hchi modes outputs hcut hchir hsub hout hs hk
      t (hI (Set.Ioo_subset_Icc_self ht)) x hx hy hg⟩

theorem ae_ae_planeRate_young_bound (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
      ∀ (w : R3) (rho : ℝ), 0 < rho →
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let K := bottomCoupling S (jointRemainder chi modes outputs (s.coefficients t) nu x)
    |⟪w, planeRate chi modes s.coefficients t x w⟫| ≤
      rho * ‖bottomEigenlineProjector S w‖ ^ 2 +
        4 * ‖K‖ ^ 2 / (rho * bottomGap S ^ 2) * ‖expandingPlaneProjector S w‖ ^ 2 := by
  filter_upwards [ae_ae_planeRate_bounds s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI] with t ht
  exact ht.mono (fun x hx hg w rho hrho ↦
    ((hx hg).2 w).trans (planeTransfer_le_weightedEnergy _ _ _ _ rho hg hrho))

theorem ae_ae_planeRate_gap_absorption (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) → ∀ w : R3,
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let K := bottomCoupling S (jointRemainder chi modes outputs (s.coefficients t) nu x)
    |⟪w, planeRate chi modes s.coefficients t x w⟫| ≤
      bottomGap S * ‖bottomEigenlineProjector S w‖ ^ 2 +
        4 * ‖K‖ ^ 2 / bottomGap S ^ 3 * ‖expandingPlaneProjector S w‖ ^ 2 := by
  filter_upwards [ae_ae_planeRate_young_bound s chi C hchi modes outputs hcut hchir hsub hout hs hk
    hB a b hab hI] with t ht
  exact ht.mono (fun x hx hg w ↦ by
    have h := hx hg w _ hg
    simpa only [pow_succ'] using h)

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectorMotion

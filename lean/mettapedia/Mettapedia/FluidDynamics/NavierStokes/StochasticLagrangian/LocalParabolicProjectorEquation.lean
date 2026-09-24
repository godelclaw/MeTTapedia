import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialSpectralRelation

/-!
# Principal diffusion cancellation for the actual moving bottom projector

The material derivative is obtained from the local Navier–Stokes strain
equation. Subtracting the actual spatial Laplacian leaves the nonviscous
remainder and an explicit mixed gradient term. The parabolic projector
rate is not tangent: both diagonal blocks retain their quadratic defect.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalParabolicProjectorEquation

open scoped Topology RealInnerProductSpace ComplexConjugate
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open PancakeFourierMaterialPaths PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeEigenframePerturbation PancakeMaterialProjectorTangent RankOneProjectorTangent
open BottomProjectorMotion LocalClusterAnisotropy LocalProjectorMotion LocalBottomEnergyDiffusion
open LocalSpatialSpectralRelation LocalAlignmentForcing PancakePhysicalLaplacian
open LocalSpectralFunctionDifferentiability LocalTopPlaneRate StrainEigenvalueContinuity

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def parabolicRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3) : Op :=
  -planeRate chi modes u t x - nu • projectorLaplacian chi modes (u t) x

def bottomEigenvalueMaterialRate (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3) : ℝ :=
  deriv (fun h ↦ thirdEigenvalue (frozenStrain chi modes u t x h)) 0

def quadraticGradient (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : Op :=
  ∑ j : Fin 3, projectorFirst chi modes u j x * projectorFirst chi modes u j x

theorem neg_planeRate_eq_deriv_bottomProjector (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (t : ℝ) (x : T3)
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    -planeRate chi modes u t x =
      deriv (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0 := by
  rw [planeRate, deriv_expandingPlaneProjector_eq_neg _ 0 hP, neg_neg]

theorem parabolicRate_constraint (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x)
    let W := parabolicRate chi modes u nu t x
    W * P + P * W = W + (2 * nu) • quadraticGradient chi modes (u t) x := by
  have hD := derivative_projector_tangent _ _ 0 hP.hasDerivAt
    (fun h ↦ lineProjector_mul_self _ (bottomVector_norm (frozenStrain chi modes u t x h)))
  rw [frozenStrain_zero, ← neg_planeRate_eq_deriv_bottomProjector chi modes u t x hP] at hD
  exact parabolic_projector_constraint chi modes (u t) x _ nu hg hD

theorem parabolicRate_bottom_block (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    let P := bottomEigenlineProjector (spatialStrain modes (filteredVelocity chi (u t)) x)
    P * parabolicRate chi modes u nu t x * P =
      (2 * nu) • (P * quadraticGradient chi modes (u t) x * P) := by
  have h := Mettapedia.Analysis.idempotent_defect_image_block _ _ _
    (lineProjector_mul_self _ (bottomVector_norm (spatialStrain modes (filteredVelocity chi (u t)) x)))
    (parabolicRate_constraint chi modes u nu t x hg hP)
  simpa only [mul_smul_comm, smul_mul_assoc] using! h

theorem parabolicRate_plane_block (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (u t)) x))
    (hP : DifferentiableAt ℝ (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes u t x h)) 0) :
    let Q := expandingPlaneProjector (spatialStrain modes (filteredVelocity chi (u t)) x)
    Q * parabolicRate chi modes u nu t x * Q =
      -(2 * nu) • (Q * quadraticGradient chi modes (u t) x * Q) := by
  have h := Mettapedia.Analysis.idempotent_defect_complement_block _ _ _
    (lineProjector_mul_self _ (bottomVector_norm (spatialStrain modes (filteredVelocity chi (u t)) x)))
    (parabolicRate_constraint chi modes u nu t x hg hP)
  dsimp only
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro w
  simp only [mul_apply_eq_comp, smul_apply, neg_apply, map_smul]
  change -(2 * nu) • ((1 - lineProjector (bottomVector _))
      (quadraticGradient chi modes (u t) x ((1 - lineProjector (bottomVector _)) w))) = _
  module

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (chi : Wavevector → ℂ) (C : ℝ) (hchi : ∀ q, ‖chi q‖ ≤ C)
  (modes outputs : Finset Wavevector) (hcut : ∀ q, q ∉ modes → chi q = 0)
  (hchir : ∀ q, chi (-q) = conj (chi q))
  (hsub : modes ⊆ outputs) (hout : ∀ k ∈ modes, ∀ l ∈ modes, k+l ∈ outputs)
  (hs : ∀ k, -k ∈ modes ↔ k ∈ modes) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)

include hchi hcut hchir hsub hout hs hk

theorem parabolicRate_spectral_relation (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3)
    (hg : 0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x))
    (hP : DifferentiableAt ℝ
      (fun h ↦ bottomEigenlineProjector (frozenStrain chi modes s.coefficients t x h)) 0)
    (hmu : ScalarDifferentiable thirdEigenvalue chi modes s.coefficients t x) :
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let P := bottomEigenlineProjector S
    let W := parabolicRate chi modes s.coefficients nu t x
    (-S.1 * S.1 + nonviscousRemainder chi modes outputs (s.coefficients t) x) * P + S.1 * W =
      (bottomEigenvalueMaterialRate chi modes s.coefficients t x -
          nu * bottomEigenvalueLaplacian chi modes (s.coefficients t) x) • P +
        thirdEigenvalue S • W + (2 * nu) • mixedGradient chi modes (s.coefficients t) x := by
  have hS := hasDerivAt_frozenStrain s chi C hchi modes outputs hcut hchir hsub hout hs hk t ht x
  have hD := bottomProjector_derivative_equation _ _ _ _ 0 hS hP.hasDerivAt hmu.hasDerivAt
  rw [frozenStrain_zero, ← neg_planeRate_eq_deriv_bottomProjector chi modes s.coefficients t x hP] at hD
  have hD' := hD
  simp only [jointRemainder, ← add_assoc] at hD'
  exact Mettapedia.Analysis.SpectralRelationDerivatives.parabolic_relation _ _ _ _ _ _ _ _ _ _ _ _ _
    hD' (laplacian_spectral_relation chi modes (s.coefficients t) x hg)

/-- Both the corrected spectral equation and the non-tangent constraint
hold on the actual local solution, almost everywhere on any interior
time interval and wherever the bottom eigenspace is isolated. -/
theorem ae_ae_parabolicRate_equations (hB : 0 ≤ B)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), ∀ᵐ x : T3,
      0 < bottomGap (spatialStrain modes (filteredVelocity chi (s.coefficients t)) x) →
    let S := spatialStrain modes (filteredVelocity chi (s.coefficients t)) x
    let P := bottomEigenlineProjector S
    let W := parabolicRate chi modes s.coefficients nu t x
    ((-S.1 * S.1 + nonviscousRemainder chi modes outputs (s.coefficients t) x) * P + S.1 * W =
      (bottomEigenvalueMaterialRate chi modes s.coefficients t x -
          nu * bottomEigenvalueLaplacian chi modes (s.coefficients t) x) • P +
        thirdEigenvalue S • W + (2 * nu) • mixedGradient chi modes (s.coefficients t) x) ∧
      (W * P + P * W = W + (2 * nu) • quadraticGradient chi modes (s.coefficients t) x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_ae_differentiableAt_frozenProjectors s chi C hchi modes outputs hcut hchir hsub hout hs hk hB a b hab hI,
    ae_ae_scalarDifferentiable s a b hab hI chi modes hB thirdEigenvalue 1 lipschitzWith_thirdEigenvalue]
    with t ht hP hmu
  filter_upwards [hP, hmu] with x hx hm hg
  exact ⟨parabolicRate_spectral_relation s chi C hchi modes outputs hcut hchir hsub hout hs hk
      t (hI (Set.Ioo_subset_Icc_self ht)) x hg (hx hg).1 hm,
    parabolicRate_constraint chi modes s.coefficients nu t x hg (hx hg).1⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalParabolicProjectorEquation

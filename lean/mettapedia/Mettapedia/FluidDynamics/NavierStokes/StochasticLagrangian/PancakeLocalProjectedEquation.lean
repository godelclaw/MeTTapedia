import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalConvectionCoefficients

/-!
# The actual local spatial equation in pressure-projected form

The projection is applied to the Fourier integrals of the actual
derivative-defined advection field. The time derivative and Laplacian are
ordinary derivatives of the same reconstructed local velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalProjectedEquation

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeInfiniteSpatialLaplacian PancakePhysicalConvectionCoefficients
open PancakeInfiniteVelocityEnvelope PancakeFixedOutputVelocityBound
open PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation PancakePeriodicVorticityEquation
open PancakeInfiniteFourierTime PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity
open PancakeHigherLocalVelocity PancakeIncomingLowSourceEnergy

local notation "T3" => UnitAddTorus (Fin 3)

/-- Fourier Leray projection of a physical field, using its actual Fourier
integrals. Summability is proved at each application to advection below. -/
def spatialLeray (f : T3 → VelocityCoefficient) : C(T3, VelocityCoefficient) :=
  fullFourierField id (fun q ↦ lerayMode q (torusFourierVelocity f q))

def spatialDivergence (f : T3 → VelocityCoefficient) (x : T3) : ℂ :=
  ∑ j : Fin 3, coordinateDerivative f j x j

theorem spatialDivergence_fullFourierField (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    spatialDivergence (fullFourierField id u) x = 0 := by
  have hu1 : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  have hdu (j : Fin 3) := summable_norm_derivativeCoefficients id u hu1 j
  have hs (j : Fin 3) : Summable (fun q ↦
      UnitAddTorus.mFourier q x * indexedDerivativeCoeff id j u q j) :=
    Pi.summable.mp (summable_pointwise_modes id _ (hdu j) x) j
  simp only [spatialDivergence, coordinateDerivative_fullFourierField id u hu1,
    fullFourierField_component id _ (hdu _), id_eq]
  rw [← Summable.tsum_finsetSum (fun j _ ↦ hs j)]
  have he (q : Wavevector) :
      (∑ j : Fin 3, UnitAddTorus.mFourier q x * indexedDerivativeCoeff id j u q j) = 0 := by
    calc
      _ = UnitAddTorus.mFourier q x * unitTorusDerivativePhase * modeDot q (u q) := by
        simp only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul, id_eq,
          modeDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hd q, mul_zero]
  simp_rw [he]
  exact tsum_zero

theorem summable_norm_projectedConvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (c : ℂ) :
    Summable (fun q ↦ ‖lerayMode q (c • infiniteConvection u q)‖) := by
  have hs := (summable_convolutionEnvelope (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu).mul_left
    (‖c‖ * 3)
  apply hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro q
  apply (norm_coefficient_sup_le_euclidean _).trans
  apply (norm_lerayMode_le q _).trans
  change ‖c • coefficientVec (infiniteConvection u q)‖ ≤ _
  rw [norm_smul]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left
      (norm_infiniteConvection_le u (fourierMoment 2 u) (fourierMoment_nonneg _ _) hu
        (fun _ ↦ le_rfl) q) (norm_nonneg c)

theorem summable_norm_viscous (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    Summable (fun q ↦ ‖unitTorusViscousVorticityCoeff nu u q‖) := by
  apply (hu.mul_left (|nu| * (2 * Real.pi)^2)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro q
  apply (norm_coefficient_sup_le_euclidean _).trans
  rw [norm_viscousCoefficient]
  have hr : ‖frequencyVec q‖^2 * ‖coefficientVec (u q)‖ ≤ fourierMoment 2 u q := by
    unfold fourierMoment
    gcongr
    exact le_add_of_nonneg_left zero_le_one
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ |nu| * (2 * Real.pi)^2)

theorem fullVelocityRHS_eq_projected_spatial (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    fullFourierField id (infiniteVelocityRHS nu u) x =
      -spatialLeray (spatialAdvection (fullFourierField id u)) x +
        (nu : ℂ) • spatialLaplacian (fullFourierField id u) x := by
  have hc :
      (fun q ↦ lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q)) =
      fun q ↦ (-1 : ℂ) • lerayMode q (unitTorusDerivativePhase • infiniteConvection u q) := by
    funext q
    rw [lerayMode_smul, lerayMode_smul, smul_smul]
    congr 1
    ring
  change fullFourierField id (fun q ↦
    lerayMode q ((-unitTorusDerivativePhase) • infiniteConvection u q) +
      unitTorusViscousVorticityCoeff nu u q) x = _
  rw [fullFourierField_add _ _ (summable_norm_projectedConvection u hu _)
    (summable_norm_viscous nu u hu)]
  simp only [ContinuousMap.add_apply]
  rw [hc, fullFourierField_smul, fullFourierField_viscous nu u hu x]
  simp only [spatialLeray, torusFourierVelocity_spatialAdvection u hu hd,
    neg_one_smul, ContinuousMap.neg_apply]

theorem spatialField_projected_equation {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ spatialField s τ x)
      (-spatialLeray (spatialAdvection (spatialField s t)) x +
        (nu : ℂ) • spatialLaplacian (spatialField s t) x) t := by
  have hm : Summable (fourierMoment 2 (s.coefficients t)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have h := spatialField_hasDerivAt_pointwise s g hg hSum hu t ht x
  rwa [fullVelocityRHS_eq_projected_spatial nu _ hm (s.transverse t) x] at h

/-- Positive viscosity and physical initial derivatives construct a local
real, divergence-free velocity satisfying the pressure-projected spatial PDE. -/
theorem exists_physical_local_projected_equation (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ⇑(spatialField s 0) = f ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x i,
          conj (spatialField s t x i) = spatialField s t x i) ∧
        (∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ x, spatialDivergence (spatialField s t) x = 0) ∧
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T → ∀ x,
          HasDerivAt (fun τ ↦ spatialField s τ x)
            (-spatialLeray (spatialAdvection (spatialField s t)) x +
              (nu : ℂ) • spatialLaplacian (spatialField s t) x) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 2 nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [coordinateJet_zero] using (hf i).1 0 0 (by omega)
  refine ⟨T, hT, B, hB, s, spatialField_initial hT.le f hc s, spatialField_reality s,
    fun t ht x ↦ ?_, spatialField_projected_equation s g hg hSum hu⟩
  exact spatialDivergence_fullFourierField _
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)) (s.transverse t) x

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalProjectedEquation

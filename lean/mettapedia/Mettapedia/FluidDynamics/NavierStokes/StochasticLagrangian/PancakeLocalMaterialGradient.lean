import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteMaterialSeries

/-!
# The actual velocity gradient along constructed-velocity trajectories

The evolving derivative series is differentiated along a real material
path. Its character-motion term cancels Eulerian advection exactly.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialGradient

open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeInfiniteMaterialSeries PancakeInfiniteDirectionalTransport PancakeCurlOutputTail
open PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative PancakeHigherDerivativeMoments
open PancakeVelocityGradientEnvelope PancakeInfiniteVelocityEnvelope PancakeCoefficientLimitEquation
open PancakeLocalVelocityGradientTime PancakeLocalGradientEquation PancakeSpatialGradientDifferentiation
open PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian

local notation "X3" => Fin 3 → ℝ

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
  (X : ℝ → X3)
  (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)

include hg hSum hu hX

theorem gradientSeries_material (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullFourierField id (indexedDerivativeCoeff id j (s.coefficients τ))
      (torusPoint (X τ)))
      (fullFourierField id (indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients t)))
          (torusPoint (X t)) +
        fullFourierField id (directionalCoeff (indexedDerivativeCoeff id j (s.coefficients t))
          (liftedVelocity s t (X t))) (torusPoint (X t))) t := by
  have hu1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu τ hτ q)
  apply hasDerivAt_fullFourierField_material
    (fun τ ↦ indexedDerivativeCoeff id j (s.coefficients τ))
    (fun τ ↦ indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients τ)))
    X (fun τ ↦ liftedVelocity s τ (X τ)) (Set.Ioo (0 : ℝ) T)
    isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q ↦ (2 * Real.pi) * g q) (fun q ↦ (2 * Real.pi) * velocityEnvelope nu g q)
    (fun q ↦ mul_nonneg (by positivity) (hg q))
    (hSum.mul_left _) ((summable_velocityEnvelope nu g hg hSum).mul_left _)
    (∑' q, g q) (tsum_nonneg hg)
  · intro τ hτ q
    apply (fourierMoment_derivative_le 1 _ j q).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu τ ⟨hτ.1.le, hτ.2.le⟩ q)
  · intro τ hτ q
    exact norm_velocityRHS_derivative_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) j q
  · exact coefficientGradient_hasDerivAt s j
  · exact hX
  · intro τ hτ
    exact norm_liftedVelocity_le s g hg hSum hu1 τ ⟨hτ.1.le, hτ.2.le⟩ (X τ)
  · exact ht

theorem spatialGradient_material (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ coordinateDerivative (spatialField s τ) j (torusPoint (X τ)))
      (-gradientProduct (spatialField s t) j (torusPoint (X t)) -
        (fun i ↦ spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) i j) +
        (nu : ℂ) • spatialLaplacian
          (fun y ↦ coordinateDerivative (spatialField s t) j y) (torusPoint (X t))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have hm1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm
  have hd1 := summable_fourierMoment_derivative 1 _ (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hm) j
  have h := gradientSeries_material s g hg hSum hu X hX j t ht
  have hr (i : Fin 3) :
      ((spatialField s t (torusPoint (X t)) i).re : ℂ) =
        spatialField s t (torusPoint (X t)) i :=
    Complex.conj_eq_iff_re.mp (spatialField_reality s t ⟨ht.1.le, ht.2.le⟩ _ i)
  have htr :
      fullFourierField id (directionalCoeff (indexedDerivativeCoeff id j (s.coefficients t))
        (liftedVelocity s t (X t))) (torusPoint (X t)) =
      spatialTransport (spatialField s t)
        (fullFourierField id (indexedDerivativeCoeff id j (s.coefficients t))) (torusPoint (X t)) :=
    fullFourierField_directionalCoeff_transport _ hd1 (spatialField s t) _ hr
  rw [htr] at h
  have he : fullFourierField id (indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients t)))
      (torusPoint (X t)) =
      coordinateDerivative (fullFourierField id (infiniteVelocityRHS nu (s.coefficients t)))
        j (torusPoint (X t)) := by
    symm
    exact coordinateDerivative_fullFourierField id _ (by
      simpa only [indexedFirstMoment_id] using summable_firstMoment_velocityRHS nu _ hm) j _
  rw [he, coordinateDerivative_velocityRHS_eq nu _ hm (s.transverse t)] at h
  rw [← coordinateDerivative_fullFourierField_eq _ hm1 j] at h
  have h' : HasDerivAt
      (fun τ ↦ fullFourierField id (indexedDerivativeCoeff id j (s.coefficients τ)) (torusPoint (X τ)))
      (-gradientProduct (spatialField s t) j (torusPoint (X t)) -
        (fun i ↦ spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) i j) +
        (nu : ℂ) • spatialLaplacian
          (fun y ↦ coordinateDerivative (spatialField s t) j y) (torusPoint (X t))) t :=
    h.congr_deriv (by simp only [spatialField]; abel)
  apply h'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  exact coordinateDerivative_fullFourierField id _ (by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_of_le _
      (by omega : 1 ≤ 3) (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩))) j _

theorem velocityGradient_material (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ spatialVelocityGradient (spatialField s τ) (torusPoint (X τ)))
      (-spatialVelocityGradient (spatialField s t) (torusPoint (X t)) *
          spatialVelocityGradient (spatialField s t) (torusPoint (X t)) -
        spatialHessian (spatialPressure (s.coefficients t)) (torusPoint (X t)) +
        (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (spatialField s t)) (torusPoint (X t))) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := (hasDerivAt_pi.mp (spatialGradient_material s g hg hSum hu X hX j t ht)) i
  simpa only [Matrix.neg_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    spatialVelocityGradient, matrixLaplacian, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    gradientProduct_eq_matrixSquare] using h

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalMaterialGradient

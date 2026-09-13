import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalHelicityCenterEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets

/-!
# Actual material evolution of the vorticity gradient

Differentiate the full infinite Fourier equation and include character
motion along the actual velocity trajectory. A common fourth Fourier
moment justifies these local derivatives. It is not a global derivative
bound or a budget supplied by initial kinetic energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityGradientEvolution

open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeInfiniteMaterialSeries PancakeInfiniteDirectionalTransport PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeHigherDerivativeMoments PancakeInfiniteVelocityEnvelope
open PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeIncomingLowSourceEnergy PancakeFrequencyProjectorCommutator PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakePeriodicVorticityEquation
open LocalSpatialVorticityJets LocalVorticityDiffusion VelocityRHSMoments
open PancakeInfiniteSpatialLaplacian PancakeLocalProjectedEquation LocalHelicityCenterEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem fourierMoment_gradientCurl_le (m : ℕ) (u : FourierVelocity) (j : Fin 3) (q : Wavevector) :
    fourierMoment m (indexedDerivativeCoeff id j (fourierCurl u)) q ≤
      (2 * Real.pi) ^ 2 * fourierMoment (m + 2) u q := by
  calc
    _ ≤ (2 * Real.pi) * fourierMoment (m + 1) (fourierCurl u) q :=
      fourierMoment_derivative_le m _ j q
    _ ≤ (2 * Real.pi) * ((2 * Real.pi) * fourierMoment (m + 2) u q) :=
      mul_le_mul_of_nonneg_left (fourierMoment_curl_le (m + 1) u q) (by positivity)
    _ = _ := by ring

theorem norm_gradientCurl_velocityRHS_le (ν : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, fourierMoment 4 u q ≤ g q) (j : Fin 3) (q : Wavevector) :
    ‖indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν u)) q‖ ≤
      (2 * Real.pi) ^ 2 * velocityEnvelope ν g q := by
  apply (norm_coefficient_sup_le_euclidean _).trans
  have hc := fourierMoment_gradientCurl_le 0 (infiniteVelocityRHS ν u) j q
  simp only [fourierMoment, pow_zero, one_mul, Nat.zero_add] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left
    (fourierMoment_infiniteVelocityRHS_le 2 ν u g hg hSum hu q) (sq_nonneg _))

variable {ν T B : ℝ} {u₀ : FourierVelocity}

theorem gradientCurlSeries_material (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullFourierField id (indexedDerivativeCoeff id j (fourierCurl (s.coefficients τ)))
      (torusPoint (X τ)))
      (fullFourierField id (indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν (s.coefficients t))))
          (torusPoint (X t)) +
        fullFourierField id (directionalCoeff (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t)))
          (liftedVelocity s t (X t))) (torusPoint (X t))) t := by
  have hu1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 4) q).trans (hu τ hτ q)
  apply hasDerivAt_fullFourierField_material
    (fun τ ↦ indexedDerivativeCoeff id j (fourierCurl (s.coefficients τ)))
    (fun τ ↦ indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν (s.coefficients τ))))
    X (fun τ ↦ liftedVelocity s τ (X τ)) (Set.Ioo (0 : ℝ) T)
    isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q ↦ (2 * Real.pi) ^ 2 * g q) (fun q ↦ (2 * Real.pi) ^ 2 * velocityEnvelope ν g q)
    (fun q ↦ mul_nonneg (sq_nonneg _) (hg q))
    (hSum.mul_left _) ((summable_velocityEnvelope ν g hg hSum).mul_left _)
    (∑' q, g q) (tsum_nonneg hg)
  · intro τ hτ q
    apply (fourierMoment_gradientCurl_le 1 _ j q).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ ⟨hτ.1.le, hτ.2.le⟩ q)
  · intro τ hτ q
    exact norm_gradientCurl_velocityRHS_le ν _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) j q
  · intro τ hτ q i
    simpa only [indexedDerivativeCoeff, Pi.smul_apply, smul_eq_mul, id_eq] using
      (hasDerivAt_fourierCurl s.coefficients _ τ q (s.equation τ hτ q) i).const_mul
        (unitTorusDerivativePhase * (q j : ℂ))
  · exact hX
  · intro τ hτ
    exact norm_liftedVelocity_le s g hg hSum hu1 τ ⟨hτ.1.le, hτ.2.le⟩ (X τ)
  · exact ht

/-- Full coefficient evolution plus the derivative from moving the evaluation point. -/
def gradientMaterialRate (ν : ℝ) (u : FourierVelocity) (v : X3) (j : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM
    (fullFourierField id (indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν u))) x +
      fullFourierField id (directionalCoeff (indexedDerivativeCoeff id j (fourierCurl u)) v) x)

theorem hasDerivAt_fullCurlGradient_material (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullCurlGradient (s.coefficients τ) j (torusPoint (X τ)))
      (gradientMaterialRate ν (s.coefficients t) (liftedVelocity s t (X t)) j (torusPoint (X t))) t :=
  complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    (gradientCurlSeries_material s g hg hSum hu X hX j t ht)

/-- The ordinary spatial Laplacian of the reconstructed gradient coefficient field. -/
def gradientLaplacian (u : FourierVelocity) (j : Fin 3) (x : T3) : R3 :=
  complexRealPartEuclideanCLM
    (spatialLaplacian (fullFourierField id (indexedDerivativeCoeff id j (fourierCurl u))) x)

theorem gradientCurl_velocityRHS_eq (ν : ℝ) (u : FourierVelocity) (j : Fin 3) :
    indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS ν u)) =
      indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS 0 u)) +
        unitTorusViscousVorticityCoeff ν (indexedDerivativeCoeff id j (fourierCurl u)) := by
  rw [infiniteVelocityRHS_eq_zero_add_viscous, LocalFilteredVorticity.fourierCurl_add,
    funext (curl_viscous u ν)]
  ext q i
  simp [indexedDerivativeCoeff, unitTorusViscousVorticityCoeff]
  ring

theorem gradientMaterialRate_eq_inviscid_add_diffusion (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (v : X3) (j : Fin 3) (x : T3) :
    gradientMaterialRate ν u v j x = gradientMaterialRate 0 u v j x + ν • gradientLaplacian u j x := by
  have hc2 : Summable (fourierMoment 2 (indexedDerivativeCoeff id j (fourierCurl u))) :=
    (hu.mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le (fourierMoment_nonneg _ _)
      (fourierMoment_gradientCurl_le 2 u j)
  have h0 : Summable (fun q ↦ ‖indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS 0 u)) q‖) :=
    ((summable_velocityEnvelope 0 (fourierMoment 4 u) (fourierMoment_nonneg _ _) hu).mul_left
      ((2 * Real.pi) ^ 2)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (norm_gradientCurl_velocityRHS_le 0 u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl) j)
  unfold gradientMaterialRate
  rw [gradientCurl_velocityRHS_eq]
  change complexRealPartEuclideanCLM (fullFourierField id (fun q ↦
    indexedDerivativeCoeff id j (fourierCurl (infiniteVelocityRHS 0 u)) q +
      unitTorusViscousVorticityCoeff ν (indexedDerivativeCoeff id j (fourierCurl u)) q) x + _) = _
  rw [fullFourierField_add _ _ h0 (summable_norm_viscous ν _ hc2)]
  simp only [ContinuousMap.add_apply, fullFourierField_viscous ν _ hc2 x, map_add]
  have hs (z : VelocityCoefficient) :
      complexRealPartEuclideanCLM ((ν : ℂ) • z) = ν • complexRealPartEuclideanCLM z := by
    ext i
    simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]
  rw [hs]
  unfold gradientLaplacian
  abel

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityGradientEvolution

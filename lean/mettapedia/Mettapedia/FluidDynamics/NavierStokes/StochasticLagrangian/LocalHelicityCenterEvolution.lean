import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVariableHelicityCenter
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VelocityRHSMoments
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredVorticity
import Mettapedia.Analysis.RegularizedProjection

/-!
# Material evolution of the regularized helicity center

The center is evaluated on the actual local solution and its material
trajectories. Its time derivative is obtained by differentiating the full
equation twice in space, not by prescribing a transport law for the center.
The common Fourier envelope justifies these local derivatives; it is not an
initial-data bound on the resulting source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterEvolution

open scoped Topology RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeInfiniteMaterialSeries PancakeInfiniteDirectionalTransport PancakeCurlOutputTail
open PancakeInfiniteFourierDerivative PancakeHigherDerivativeMoments PancakeInfiniteVelocityEnvelope
open PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeIncomingLowSourceEnergy PancakeFrequencyProjectorCommutator
open PancakeIndexedFourierMoments
open PancakeDyadicDirectionEvolution PancakeInfiniteSpatialCurl
open PancakeTransverseEnergyFreezing
open PancakeInfiniteSpatialLaplacian PancakeLocalProjectedEquation
open PancakePeriodicVorticityEquation LocalJointDiffusionBudget
open LocalLowDiffusionBudget LocalMaterialVorticity LocalVorticityDiffusion
open LocalWeightedCurlCancellation LocalVariableHelicityCenter VelocityRHSMoments

local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem fourierMoment_doubleCurl_le (m : ℕ) (u : FourierVelocity) (q : Wavevector) :
    fourierMoment m (fourierCurl (fourierCurl u)) q ≤
      (2 * Real.pi) ^ 2 * fourierMoment (m + 2) u q := by
  calc
    _ ≤ (2 * Real.pi) * fourierMoment (m + 1) (fourierCurl u) q :=
      fourierMoment_curl_le m _ q
    _ ≤ (2 * Real.pi) * ((2 * Real.pi) * fourierMoment (m + 2) u q) :=
      mul_le_mul_of_nonneg_left (fourierMoment_curl_le (m + 1) u q) (by positivity)
    _ = _ := by ring

theorem norm_doubleCurl_velocityRHS_le (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, fourierMoment 4 u q ≤ g q) (q : Wavevector) :
    ‖fourierCurl (fourierCurl (infiniteVelocityRHS nu u)) q‖ ≤
      (2 * Real.pi) ^ 2 * velocityEnvelope nu g q := by
  apply (norm_coefficient_sup_le_euclidean _).trans
  have hc := fourierMoment_doubleCurl_le 0 (infiniteVelocityRHS nu u) q
  simp only [fourierMoment, pow_zero, one_mul, Nat.zero_add] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left
    (fourierMoment_infiniteVelocityRHS_le 2 nu u g hg hSum hu q) (sq_nonneg _))

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem doubleCurlSeries_material (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullFourierField id (fourierCurl (fourierCurl (s.coefficients τ)))
      (torusPoint (X τ)))
      (fullFourierField id (fourierCurl (fourierCurl (infiniteVelocityRHS nu (s.coefficients t))))
          (torusPoint (X t)) +
        fullFourierField id (directionalCoeff (fourierCurl (fourierCurl (s.coefficients t)))
          (liftedVelocity s t (X t))) (torusPoint (X t))) t := by
  have hu1 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 4) q).trans (hu τ hτ q)
  apply hasDerivAt_fullFourierField_material
    (fun τ ↦ fourierCurl (fourierCurl (s.coefficients τ)))
    (fun τ ↦ fourierCurl (fourierCurl (infiniteVelocityRHS nu (s.coefficients τ))))
    X (fun τ ↦ liftedVelocity s τ (X τ)) (Set.Ioo (0 : ℝ) T)
    isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q ↦ (2 * Real.pi) ^ 2 * g q) (fun q ↦ (2 * Real.pi) ^ 2 * velocityEnvelope nu g q)
    (fun q ↦ mul_nonneg (sq_nonneg _) (hg q))
    (hSum.mul_left _) ((summable_velocityEnvelope nu g hg hSum).mul_left _)
    (∑' q, g q) (tsum_nonneg hg)
  · intro τ hτ q
    apply (fourierMoment_doubleCurl_le 1 _ q).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ ⟨hτ.1.le, hτ.2.le⟩ q)
  · intro τ hτ q
    exact norm_doubleCurl_velocityRHS_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) q
  · intro τ hτ q i
    exact hasDerivAt_fourierCurl _ _ τ q
      (hasDerivAt_fourierCurl s.coefficients _ τ q (s.equation τ hτ q)) i
  · exact hX
  · intro τ hτ
    exact norm_liftedVelocity_le s g hg hSum hu1 τ ⟨hτ.1.le, hτ.2.le⟩ (X τ)
  · exact ht

/-- The material rate of `curl omega`, with both Eulerian and path-motion
terms reconstructed from the actual velocity coefficients. -/
def curlVorticityMaterialRate (nu : ℝ) (u : FourierVelocity) (v : X3)
    (x : UnitAddTorus (Fin 3)) : R3 :=
  complexRealPartEuclideanCLM
    (fullFourierField id (fourierCurl (fourierCurl (infiniteVelocityRHS nu u))) x +
      fullFourierField id (directionalCoeff (fourierCurl (fourierCurl u)) v) x)

theorem infiniteVelocityRHS_eq_zero_add_viscous (nu : ℝ) (u : FourierVelocity) :
    infiniteVelocityRHS nu u = infiniteVelocityRHS 0 u + unitTorusViscousVorticityCoeff nu u := by
  ext q i
  simp [infiniteVelocityRHS, unitTorusViscousVorticityCoeff]

theorem doubleCurl_velocityRHS_eq (nu : ℝ) (u : FourierVelocity) :
    fourierCurl (fourierCurl (infiniteVelocityRHS nu u)) =
      fourierCurl (fourierCurl (infiniteVelocityRHS 0 u)) +
        unitTorusViscousVorticityCoeff nu (fourierCurl (fourierCurl u)) := by
  rw [infiniteVelocityRHS_eq_zero_add_viscous, LocalFilteredVorticity.fourierCurl_add,
    LocalFilteredVorticity.fourierCurl_add, funext (curl_viscous u nu),
    funext (curl_viscous (fourierCurl u) nu)]

/-- The highest-order viscous term is exactly the ordinary Laplacian of
`curl omega`. The inviscid term still includes material transport. -/
theorem curlVorticityMaterialRate_eq_inviscid_add_diffusion (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 4 u)) (v : X3) (x : UnitAddTorus (Fin 3)) :
    curlVorticityMaterialRate nu u v x = curlVorticityMaterialRate 0 u v x +
      nu • fullVorticityLaplacian (fourierCurl u) x := by
  have hc2 := summable_fourierMoment_curl 2 _ (summable_fourierMoment_curl 3 u hu)
  have hc1 := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (summable_fourierMoment_curl 3 u hu)
  have h0 : Summable (fun q ↦ ‖fourierCurl (fourierCurl (infiniteVelocityRHS 0 u)) q‖) :=
    ((summable_velocityEnvelope 0 (fourierMoment 4 u) (fourierMoment_nonneg _ _) hu).mul_left
      ((2 * Real.pi) ^ 2)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        (norm_doubleCurl_velocityRHS_le 0 u _ (fourierMoment_nonneg _ _) hu (fun _ ↦ le_rfl))
  unfold curlVorticityMaterialRate
  rw [doubleCurl_velocityRHS_eq]
  change complexRealPartEuclideanCLM (fullFourierField id (fun q ↦
    fourierCurl (fourierCurl (infiniteVelocityRHS 0 u)) q +
      unitTorusViscousVorticityCoeff nu (fourierCurl (fourierCurl u)) q) x + _) = _
  rw [fullFourierField_add _ _ h0 (summable_norm_viscous nu _ hc2)]
  simp only [ContinuousMap.add_apply, fullFourierField_viscous nu _ hc2 x,
    fullVorticityLaplacian, spatialCurl_velocity _ hc1, map_add]
  have hs (z : VelocityCoefficient) :
      complexRealPartEuclideanCLM ((nu : ℂ) • z) = nu • complexRealPartEuclideanCLM z := by
    ext i
    simp [complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]
  rw [hs]
  abel

theorem hasDerivAt_curlVorticityAlong (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullVorticity (fourierCurl (s.coefficients τ)) (torusPoint (X τ)))
      (curlVorticityMaterialRate nu (s.coefficients t) (liftedVelocity s t (X t))
        (torusPoint (X t))) t := by
  have h := complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    (doubleCurlSeries_material s g hg hSum hu X hX t ht)
  change HasDerivAt (fun τ ↦ complexRealPartEuclideanCLM
    (fullFourierField id (fourierCurl (fourierCurl (s.coefficients τ))) (torusPoint (X τ)))) _ t at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  have hm2 := summable_fourierMoment_of_le _ (by omega : 2 ≤ 4)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩))
  simp only [fullVorticity, spatialCurl_velocity _ (summable_fourierMoment_curl 1 _ hm2)]

/-- Quotient-rule source for the regularized center along the actual flow.
Neither of the two material rates is assumed to vanish. -/
def regularizedCenterMaterialRate (δ : ℝ) (a b da db : R3) : ℝ :=
  ((⟪da, b⟫ + ⟪a, db⟫) * (δ + ‖a‖ ^ 2) -
    ⟪a, b⟫ * (2 * ⟪a, da⟫)) / (δ + ‖a‖ ^ 2) ^ 2

theorem regularizedCenterMaterialRate_add (δ : ℝ) (a b da db ea eb : R3) :
    regularizedCenterMaterialRate δ a b (da + ea) (db + eb) =
      regularizedCenterMaterialRate δ a b da db + regularizedCenterMaterialRate δ a b ea eb := by
  simp only [regularizedCenterMaterialRate, inner_add_left, inner_add_right]
  ring

theorem regularizedCenterMaterialRate_smul (δ c : ℝ) (a b da db : R3) :
    regularizedCenterMaterialRate δ a b (c • da) (c • db) =
      c * regularizedCenterMaterialRate δ a b da db := by
  simp only [regularizedCenterMaterialRate, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The quotient-rule source is a pairing with the centered defect and its
rate. No absolute values are introduced by this rewriting. -/
theorem regularizedCenterMaterialRate_eq_defect (δ : ℝ) (hδ : 0 < δ) (a b da db : R3) :
    regularizedCenterMaterialRate δ a b da db =
      (⟪da, b - (⟪a, b⟫ / (δ + ‖a‖ ^ 2)) • a⟫ +
        ⟪a, db - (⟪a, b⟫ / (δ + ‖a‖ ^ 2)) • da⟫) / (δ + ‖a‖ ^ 2) := by
  have hden : δ + ‖a‖ ^ 2 ≠ 0 := by positivity
  simp only [regularizedCenterMaterialRate, inner_sub_right, real_inner_smul_right,
    real_inner_comm da a]
  field_simp
  ring

/-- Even common amplitude evolution contributes when the center is
regularized. This is an algebraic identity, not an assumed solution family. -/
theorem regularizedCenterMaterialRate_proportional (δ ρ : ℝ) (a da : R3) :
    regularizedCenterMaterialRate δ a (ρ • a) da (ρ • da) =
      2 * δ * ρ * ⟪a, da⟫ / (δ + ‖a‖ ^ 2) ^ 2 := by
  simp only [regularizedCenterMaterialRate, real_inner_smul_right, real_inner_comm da a,
    real_inner_self_eq_norm_sq]
  ring

theorem hasDerivAt_regularizedCenter_material (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ regularizedCenter δ (s.coefficients τ) (torusPoint (X τ)))
      (regularizedCenterMaterialRate δ (vorticityAlong s X t)
        (fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t)))
        (strainAlong s X t (vorticityAlong s X t) + diffusionAlong s X t)
        (curlVorticityMaterialRate nu (s.coefficients t) (liftedVelocity s t (X t))
          (torusPoint (X t)))) t := by
  have hu3 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have ha := hasDerivAt_vorticityAlong s g hg hSum hu3 X hX t ht
  have hb := hasDerivAt_curlVorticityAlong s g hg hSum hu X hX t ht
  have hden : δ + ‖vorticityAlong s X t‖ ^ 2 ≠ 0 := by positivity
  have hd := (ha.inner ℝ hb).fun_div ((hasDerivAt_const t δ).fun_add ha.norm_sq) hden
  simpa only [regularizedCenter, regularizedCenterMaterialRate, vorticityAlong,
    fullVorticity, spatialField, zero_add, add_comm] using hd

/-- The minimum of the regularized curl residual at the actual fields. -/
def regularizedResidualEnergy (δ : ℝ) (u : FourierVelocity) (x : UnitAddTorus (Fin 3)) : ℝ :=
  Mettapedia.Analysis.RegularizedProjection.energy δ (fullVorticity u x)
    (fullVorticity (fourierCurl u) x)

/-- The center's time derivative cancels from this energy, but the full
material vorticity and curl-vorticity rates remain. -/
theorem hasDerivAt_regularizedResidualEnergy_material
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ regularizedResidualEnergy δ (s.coefficients τ) (torusPoint (X τ)))
      (2 * ⟪fullVorticity (fourierCurl (s.coefficients t)) (torusPoint (X t)) -
          regularizedCenter δ (s.coefficients t) (torusPoint (X t)) • vorticityAlong s X t,
        curlVorticityMaterialRate nu (s.coefficients t) (liftedVelocity s t (X t)) (torusPoint (X t)) -
          regularizedCenter δ (s.coefficients t) (torusPoint (X t)) •
            (strainAlong s X t (vorticityAlong s X t) + diffusionAlong s X t)⟫) t := by
  have hu3 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q :=
    fun τ hτ q ↦ (fourierMoment_mono _ (by omega : 3 ≤ 4) q).trans (hu τ hτ q)
  have ha := hasDerivAt_vorticityAlong s g hg hSum hu3 X hX t ht
  have hb := hasDerivAt_curlVorticityAlong s g hg hSum hu X hX t ht
  simpa only [regularizedResidualEnergy, Mettapedia.Analysis.RegularizedProjection.residual,
    Mettapedia.Analysis.RegularizedProjection.coefficient, regularizedCenter,
    vorticityAlong, fullVorticity, spatialField] using
    Mettapedia.Analysis.RegularizedProjection.hasDerivAt_energy δ hδ ha hb

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterEvolution

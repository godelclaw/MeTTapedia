import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteVelocityEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalSpatialVelocity

/-!
# Time differentiation in the continuous-field norm

A summable common derivative envelope justifies time differentiation of
the actual Fourier series on an open interval. Applied to the constructed
velocity evolution, this gives its spatially uniform time derivative.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierTime

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierTranslationCurve
open PancakeInfiniteFourierDerivative PancakeInfiniteVelocityEnvelope
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeSobolevAbsoluteTail
open PancakeCoefficientLimitEquation PancakeCurlOutputTail PancakeIndexedFourierMoments
open PancakeHigherLocalVelocity PancakeContinuousCoordinateJet PancakeArbitraryDataBlocks
open PancakeVelocityPathLimit PancakeGalerkinCoefficientLimit
open scoped ComplexConjugate

local notation "T3" => UnitAddTorus (Fin 3)

def modeFieldCLM (q : Wavevector) : VelocityCoefficient →L[ℂ] C(T3, VelocityCoefficient) :=
  LinearMap.mkContinuous {
    toFun := modeField q
    map_add' := by intro a b; ext x; simp [modeField, smul_add]
    map_smul' := by intro c a; exact modeField_smul q a c }
    1 (fun a ↦ by
      change ‖modeField q a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using norm_modeField_le q a)

theorem hasDerivAt_modeField (u : ℝ → FourierVelocity) (du : FourierVelocity)
    (q : Wavevector) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun τ ↦ u τ q i) (du q i) t) :
    HasDerivAt (fun τ ↦ modeField q (u τ q)) (modeField q (du q)) t :=
  ((modeFieldCLM q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)

/-- The value and derivative are sums in the continuous-field Banach space,
not merely pointwise sums of scalar derivatives. -/
theorem hasDerivAt_fullFourierField_time (u du : ℝ → FourierVelocity)
    (I : Set ℝ) (hI : IsOpen I) (hc : IsPreconnected I)
    (g : Wavevector → ℝ) (hSum : Summable g)
    (hd : ∀ τ ∈ I, ∀ q i, HasDerivAt (fun r ↦ u r q i) (du τ q i) τ)
    (hb : ∀ τ ∈ I, ∀ q, ‖du τ q‖ ≤ g q)
    (t : ℝ) (ht : t ∈ I) (hu : Summable (fun q ↦ ‖u t q‖)) :
    HasDerivAt (fun τ ↦ fullFourierField id (u τ)) (fullFourierField id (du t)) t := by
  exact hasDerivAt_tsum_of_isPreconnected hSum hI hc
    (fun q τ hτ ↦ hasDerivAt_modeField u (du τ) q τ (hd τ hτ q))
    (fun q τ hτ ↦ (norm_modeField_le q _).trans (hb τ hτ q))
    ht (summable_modeField id (u t) hu) ht

theorem spatialField_hasDerivAt {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (spatialField s)
      (fullFourierField id (infiniteVelocityRHS nu (s.coefficients t))) t := by
  apply hasDerivAt_fullFourierField_time s.coefficients
    (fun τ ↦ infiniteVelocityRHS nu (s.coefficients τ))
    (Set.Ioo (0 : ℝ) T) isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (velocityEnvelope nu g) (summable_velocityEnvelope nu g hg hSum) s.equation
  · intro τ hτ q
    exact (norm_coefficient_sup_le_euclidean _).trans
      (norm_infiniteVelocityRHS_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) q)
  · exact ht
  · exact PancakeSobolevAbsoluteTail.summable_norm_coefficients _ B
      (s.sobolev_bound t ⟨ht.1.le, ht.2.le⟩)

theorem spatialField_hasDerivAt_pointwise {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ spatialField s τ x)
      (fullFourierField id (infiniteVelocityRHS nu (s.coefficients t)) x) t :=
  (ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).hasFDerivAt.comp_hasDerivAt t
    (spatialField_hasDerivAt s g hg hSum hu t ht)

theorem continuous_velocityRHS_component {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ infiniteVelocityRHS nu (s.coefficients t) q i) := by
  have he :
      (fun t : Set.Icc (0 : ℝ) T ↦ infiniteVelocityRHS nu (s.coefficients t) q i) =
      fun t ↦ velocityPath nu q (infiniteSolutionPaths s) i t := by
    funext t
    exact (velocityPath_apply nu q (infiniteSolutionPaths s) B hB
      (fun t F ↦ s.sobolev_bound t t.2 F) i t).symm
  rw [he]
  exact (velocityPath nu q (infiniteSolutionPaths s) i).continuous

theorem continuous_velocityRHS_field {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (infiniteVelocityRHS nu (s.coefficients t))) := by
  apply continuous_tsum
    (fun q ↦ (modeFieldCLM q).continuous.comp (continuous_pi (continuous_velocityRHS_component s hB q)))
    (summable_velocityEnvelope nu g hg hSum)
  intro q t
  exact (norm_modeField_le q _).trans ((norm_coefficient_sup_le_euclidean _).trans
    (norm_infiniteVelocityRHS_le nu _ g hg hSum (hu t t.2) q))

theorem continuous_velocityRHS_spaceTime {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
    (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      fullFourierField id (infiniteVelocityRHS nu (s.coefficients z.1)) z.2) := by
  have hc := continuous_velocityRHS_field s hB g hg hSum hu
  exact continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd)

/-- Initial physical data construct both the evolution and the common
envelope needed for its continuous-field time derivative. -/
theorem exists_physical_local_timeDerivative (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ⇑(spatialField s 0) = f ∧
        ∀ t, t ∈ Set.Ioo (0 : ℝ) T →
          HasDerivAt (spatialField s)
            (fullFourierField id (infiniteVelocityRHS nu (s.coefficients t))) t := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 2 nu hnu f hf hr hd hzero
  have hc (i : Fin 3) : Continuous (fun x ↦ f x i) := by
    simpa only [PancakeContinuousCoordinateJet.coordinateJet_zero] using (hf i).1 0 0 (by omega)
  exact ⟨T, hT, B, hB, s, spatialField_initial hT.le f hc s,
    spatialField_hasDerivAt s g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeInfiniteFourierTime

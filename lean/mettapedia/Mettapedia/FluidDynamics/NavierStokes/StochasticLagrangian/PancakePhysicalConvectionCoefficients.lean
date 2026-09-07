import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteSpatialLaplacian

/-!
# Fourier coefficients of actual spatial advection

Termwise Fourier integration of a continuous product identifies the
convolution. Incompressibility then transfers its derivative from the
advected input to the output frequency used by the infinite equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalConvectionCoefficients

open MeasureTheory
open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeIndexedFourierMoments
open PancakeSpatialCoefficientRecovery PancakePhysicalFourierDerivative
open PancakeCurlOutputTail PancakeInfiniteVelocityEnvelope PancakeCoefficientLimitEquation
open PancakeInfiniteSpatialLaplacian PancakeFourierPressureStrain PancakeSobolevFiberEnvelope
open PancakePeriodicVorticityEquation PancakeArbitraryDataBlocks

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_mul_component (u : FourierVelocity)
    (hu : Summable (fun k ↦ ‖u k‖)) (f : C(T3, ℂ)) (q : Wavevector) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ fullFourierField id u x i * f x) q =
      ∑' k, u k i * UnitAddTorus.mFourierCoeff f (q-k) := by
  have hs : Summable (fun k ↦ ‖u k i‖) :=
    hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ norm_le_pi_norm (u k) i)
  have hint (k : Wavevector) :
      Integrable (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * u k i * f x) := by
    have hc : Continuous (fun x : T3 ↦ UnitAddTorus.mFourier (-q+k) x * u k i * f x) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (k : Wavevector) :
      (∫ x : T3, ‖UnitAddTorus.mFourier (-q+k) x * u k i * f x‖) ≤ ‖u k i‖ * ‖f‖ := by
    have hp (x : T3) : ‖UnitAddTorus.mFourier (-q+k) x * u k i * f x‖ ≤ ‖u k i‖ * ‖f‖ := by
      rw [norm_mul, norm_mul, norm_character, one_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
    simpa using integral_mono (hint k).norm (integrable_const _) hp
  have hSum := (hs.mul_right ‖f‖).of_nonneg_of_le
    (fun k ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) hn
  have he := integral_tsum_of_summable_integral_norm hint hSum
  have hchar (k : Wavevector) (x : T3) :
      UnitAddTorus.mFourier (-q) x * UnitAddTorus.mFourier k x =
        UnitAddTorus.mFourier (-q+k) x := UnitAddTorus.mFourier_add.symm
  unfold UnitAddTorus.mFourierCoeff
  simp_rw [smul_eq_mul, fullFourierField_component id u hu, id_eq,
    ← tsum_mul_right, ← tsum_mul_left, ← mul_assoc, hchar]
  rw [← he]
  apply tsum_congr
  intro k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hq : -(q-k) = -q+k := by abel
  rw [hq]
  ring

def spatialAdvection (f : T3 → VelocityCoefficient) (x : T3) : VelocityCoefficient :=
  ∑ j : Fin 3, f x j • coordinateDerivative f j x

theorem mFourierCoeff_spatialAdvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hd : ∀ k, modeDot k (u k) = 0) (q : Wavevector) (i : Fin 3) :
    UnitAddTorus.mFourierCoeff (fun x ↦ spatialAdvection (fullFourierField id u) x i) q =
      unitTorusDerivativePhase * infiniteConvection u q i := by
  have hu1 : Summable (indexedFirstMoment id u) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_of_second u hu
  have hu0 := summable_norm_coefficients id u hu1
  have hdu (j : Fin 3) := summable_norm_derivativeCoefficients id u hu1 j
  let f (j : Fin 3) : C(T3, ℂ) :=
    ⟨fun x ↦ fullFourierField id (indexedDerivativeCoeff id j u) x i, by fun_prop⟩
  have hc (j : Fin 3) : Continuous (fun x : T3 ↦ fullFourierField id u x j * f j x) := by fun_prop
  have hint (j : Fin 3) : Integrable (fun x : T3 ↦
      UnitAddTorus.mFourier (-q) x * (fullFourierField id u x j * f j x)) :=
    (((UnitAddTorus.mFourier (-q)).continuous).mul (hc j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he :
      UnitAddTorus.mFourierCoeff (fun x ↦ spatialAdvection (fullFourierField id u) x i) q =
      ∑ j : Fin 3, UnitAddTorus.mFourierCoeff
        (fun x ↦ fullFourierField id u x j * f j x) q := by
    simp only [UnitAddTorus.mFourierCoeff, spatialAdvection, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, coordinateDerivative_fullFourierField id u hu1, Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun j _ ↦ hint j)
  rw [he]
  simp_rw [mFourierCoeff_mul_component u hu0]
  have hfc (j : Fin 3) (k : Wavevector) :
      UnitAddTorus.mFourierCoeff (f j) (q-k) =
        unitTorusDerivativePhase * ((q-k) j : ℂ) * u (q-k) i := by
    exact mFourierCoeff_fullFourierField_component _ (hdu j) (q-k) i
  simp_rw [hfc]
  have hs (j : Fin 3) : Summable (fun k ↦
      u k j * (unitTorusDerivativePhase * ((q-k) j : ℂ) * u (q-k) i)) := by
    have hdj := (hdu j).comp_injective (i := fun k ↦ q-k) (fun _ _ h ↦ sub_right_injective h)
    have hb : ∀ k, ‖u k j‖ ≤ ∑' k, ‖u k‖ :=
      fun k ↦ (norm_le_pi_norm (u k) j).trans (hu0.le_tsum k (fun _ _ ↦ norm_nonneg _))
    apply (hdj.mul_left (∑' k, ‖u k‖)).of_norm_bounded
    intro k
    rw [norm_mul]
    exact mul_le_mul (hb k) (norm_le_pi_norm (indexedDerivativeCoeff id j u (q-k)) i)
      (norm_nonneg _) (tsum_nonneg (fun _ ↦ norm_nonneg _))
  rw [← Summable.tsum_finsetSum (fun j _ ↦ hs j)]
  change _ = unitTorusDerivativePhase * ∑' k, outputFiber q u k i
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hm : modeDot (q-k) (u k) = modeDot q (u k) := by
    have hq : q = k + (q-k) := by abel
    conv_rhs => rw [hq, modeDot_add_wavevector, hd k, zero_add]
  calc
    _ = unitTorusDerivativePhase * (modeDot (q-k) (u k) * u (q-k) i) := by
      simp only [modeDot, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [hm]; rfl

theorem torusFourierVelocity_spatialAdvection (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) :
    torusFourierVelocity (spatialAdvection (fullFourierField id u)) =
      fun q ↦ unitTorusDerivativePhase • infiniteConvection u q := by
  ext q i
  exact mFourierCoeff_spatialAdvection u hu hd q i

end Mettapedia.FluidDynamics.NavierStokes.PancakePhysicalConvectionCoefficients

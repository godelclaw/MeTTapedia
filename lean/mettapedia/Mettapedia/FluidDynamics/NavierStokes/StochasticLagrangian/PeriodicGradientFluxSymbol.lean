import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalGradientFlux

/-!
# Fourier symbol of the gradient-active tensor projection

The projection acts on the spatial derivative index, not on the vector
output index. Its symbol is `n_j * sum_l n_l J_l / |n|²`, with zero
mean mode. The identity below identifies this explicit multiplier with
the Hilbert projection using actual translation derivatives.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxSymbol

open scoped RealInnerProductSpace
open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakePeriodicCoherentSplit
open PancakeFourierTranslationCurve PancakeInfiniteFourierTime
open PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution PancakeFrequencyProjectorCommutator PancakePeriodicComplexStretch

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def realModeCLM (n : Wavevector) : VelocityCoefficient →L[ℝ] C(T3, R3) :=
  (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).comp
    ((modeFieldCLM n).restrictScalars ℝ)

def realMode (n : Wavevector) (a : VelocityCoefficient) : C(T3, R3) := realModeCLM n a

theorem realMode_apply (n : Wavevector) (a : VelocityCoefficient) (x : T3) :
    realMode n a x = complexRealPartEuclideanCLM (modeField n a x) := rfl

theorem hasDerivAt_realMode (n : Wavevector) (a : VelocityCoefficient)
    (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ realMode n a (x + coordinateShift j t))
      (realMode n ((unitTorusDerivativePhase * (n j : ℂ)) • a)
        (x + coordinateShift j h)) h := by
  have hd := (ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).hasFDerivAt.comp_hasDerivAt h
    (hasDerivAt_translationCurve {n} (fun _ ↦ a) j h)
  have he := complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt h hd
  change HasDerivAt (fun t ↦ complexRealPartEuclideanCLM (translationCurve {n} (fun _ ↦ a) j t x))
    (complexRealPartEuclideanCLM (translationCurve {n} (derivativeCoeff j (fun _ ↦ a)) j h x)) h at he
  simpa only [translationCurve_apply, fourierField, Finset.sum_singleton,
    derivativeCoeff, realMode_apply] using he

def modeJet (n : Wavevector) (a : VelocityCoefficient) : TranslationJet (Fin 3) R3 where
  value := realMode n a
  gradient j := realMode n ((unitTorusDerivativePhase * (n j : ℂ)) • a)
  hasDerivAt j x h := by
    have hs : Mettapedia.Analysis.UnitTorusWeakDerivative.coordinateShift j = coordinateShift j := by
      funext t; rfl
    simpa only [hs] using hasDerivAt_realMode n a j x h

def contraction (n : Wavevector) (J : Fin 3 → VelocityCoefficient) : VelocityCoefficient :=
  ∑ j, (n j : ℂ) • J j

def projectedCoeff (n : Wavevector) (J : Fin 3 → VelocityCoefficient)
    (j : Fin 3) : VelocityCoefficient :=
  ((n j : ℂ) / modeSquare n) • contraction n J

def potentialCoeff (n : Wavevector) (J : Fin 3 → VelocityCoefficient) : VelocityCoefficient :=
  (unitTorusDerivativePhase * modeSquare n)⁻¹ • contraction n J

theorem projectedCoeff_zero (J : Fin 3 → VelocityCoefficient) : projectedCoeff 0 J = 0 := by
  funext j
  simp [projectedCoeff]

theorem potential_derivative (n : Wavevector) (J : Fin 3 → VelocityCoefficient) (j : Fin 3) :
    (unitTorusDerivativePhase * (n j : ℂ)) • potentialCoeff n J = projectedCoeff n J j := by
  unfold potentialCoeff projectedCoeff
  rw [smul_smul]
  congr 1
  simp only [mul_inv_rev, div_eq_mul_inv]
  field_simp [unitTorusDerivativePhase_ne_zero]

theorem contraction_projectedCoeff (n : Wavevector) (J : Fin 3 → VelocityCoefficient) :
    contraction n (projectedCoeff n J) = contraction n J := by
  by_cases hn : n = 0
  · subst n
    simp [contraction]
  have hs := modeSquare_ne_zero_of_frequencyVec_ne_zero (frequencyVec_ne_zero hn)
  ext i
  simp only [contraction, projectedCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_three]
  field_simp
  simp only [modeSquare, Fin.sum_univ_three]
  ring

theorem residual_derivative_sum (n : Wavevector) (J : Fin 3 → VelocityCoefficient) :
    (∑ j, (unitTorusDerivativePhase * (n j : ℂ)) • (J j - projectedCoeff n J j)) = 0 := by
  have he : (∑ j, (unitTorusDerivativePhase * (n j : ℂ)) • (J j - projectedCoeff n J j)) =
      unitTorusDerivativePhase • (contraction n J - contraction n (projectedCoeff n J)) := by
    simp [contraction, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  rw [he, contraction_projectedCoeff, sub_self, smul_zero]

theorem gradientProjection_realMode (n : Wavevector) (J : Fin 3 → VelocityCoefficient) :
    gradientProjection (toTensorL2 (fun j ↦ realMode n (J j))) =
      toTensorL2 (fun j ↦ realMode n (projectedCoeff n J j)) := by
  let K := fun j ↦ realMode n (projectedCoeff n J j)
  have hK : toTensorL2 K ∈ (gradientSpace (d := Fin 3) (E := R3)).toSubmodule := by
    simpa only [modeJet, potential_derivative] using gradient_mem (modeJet n (potentialCoeff n J))
  have hfix : gradientProjection (toTensorL2 K) = toTensorL2 K :=
    (gradientSpace (d := Fin 3) (E := R3)).toSubmodule.starProjection_eq_self_iff.mpr hK
  have hz := gradientProjection_eq_zero_of_divergence_zero
    (fun j ↦ realMode n (J j - projectedCoeff n J j))
    (fun j ↦ realMode n ((unitTorusDerivativePhase * (n j : ℂ)) • (J j - projectedCoeff n J j)))
    (by
      intro j x h
      have hs : Mettapedia.Analysis.UnitTorusWeakDerivative.coordinateShift j = coordinateShift j := by
        funext t; rfl
      simpa only [hs] using hasDerivAt_realMode n (J j - projectedCoeff n J j) j x h)
    (by
      intro x
      change (∑ j, realModeCLM n ((unitTorusDerivativePhase * (n j : ℂ)) •
        (J j - projectedCoeff n J j)) x) = 0
      rw [← ContinuousMap.sum_apply, ← map_sum, residual_derivative_sum, map_zero]
      rfl)
  have he : toTensorL2 (fun j ↦ realMode n (J j - projectedCoeff n J j)) =
      toTensorL2 (fun j ↦ realMode n (J j)) - toTensorL2 K := by
    simp only [toTensorL2]
    rw [← map_sub]
    congr 1
    funext j
    exact (realModeCLM n).map_sub _ _
  rw [he] at hz
  change gradientProjectionCLM (d := Fin 3) (E := R3) (_ - _) = 0 at hz
  rw [map_sub] at hz
  change gradientProjection _ - gradientProjection (toTensorL2 K) = 0 at hz
  rw [hfix] at hz
  exact sub_eq_zero.mp hz

theorem summable_realModes (J : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    Summable (fun n ↦ fun j ↦ realMode n (J j n)) := by
  apply Pi.summable.mpr
  intro j
  exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).summable
    (PancakeInfiniteFourierDerivative.summable_modeField id (J j) (hJ j))

theorem realFields_eq_tsum (J : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    (fun j ↦ LongitudinalVorticityTime.realField (J j)) =
      ∑' n, fun j ↦ realMode n (J j n) := by
  funext j
  rw [tsum_apply (summable_realModes J hJ)]
  exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).map_tsum
    (PancakeInfiniteFourierDerivative.summable_modeField id (J j) (hJ j))

/-- The explicit multiplier series converges in tensor `L²` and equals
the actual projection, without a finite Fourier cutoff. -/
theorem gradientProjection_fullFourier (J : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    gradientProjection (toTensorL2 (fun j ↦ LongitudinalVorticityTime.realField (J j))) =
      ∑' n, toTensorL2 (fun j ↦ realMode n (projectedCoeff n (fun l ↦ J l n) j)) := by
  rw [realFields_eq_tsum J hJ]
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (∑' n, fun j ↦ realMode n (J j n)) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_realModes J hJ)]
  exact tsum_congr (fun n ↦ gradientProjection_realMode n (fun j ↦ J j n))

theorem summable_projectedModes (J : Fin 3 → FourierVelocity)
    (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    Summable (fun n ↦ toTensorL2 (fun j ↦ realMode n (projectedCoeff n (fun l ↦ J l n) j))) := by
  have h := ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).summable (summable_realModes J hJ)
  change Summable (fun n ↦ gradientProjection (toTensorL2 (fun j ↦ realMode n (J j n)))) at h
  simpa only [gradientProjection_realMode] using h

/-- Repeated output frequencies are permitted, in particular when the
index is a pair or triple of interacting input frequencies. -/
theorem gradientProjection_indexedFourier {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    gradientProjection (toTensorL2 (fun j ↦
      (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
        (PancakeInfiniteFourierDerivative.fullFourierField freq (J j)))) =
      ∑' n, toTensorL2 (fun j ↦ realMode (freq n) (projectedCoeff (freq n) (fun l ↦ J l n) j)) := by
  have hs : Summable (fun n ↦ fun j ↦ realMode (freq n) (J j n)) := by
    apply Pi.summable.mpr
    intro j
    exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).summable
      (PancakeInfiniteFourierDerivative.summable_modeField freq (J j) (hJ j))
  have he : (fun j ↦ (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
      (PancakeInfiniteFourierDerivative.fullFourierField freq (J j))) =
      ∑' n, fun j ↦ realMode (freq n) (J j n) := by
    funext j
    rw [tsum_apply hs]
    exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).map_tsum
      (PancakeInfiniteFourierDerivative.summable_modeField freq (J j) (hJ j))
  rw [he]
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (∑' n, fun j ↦ realMode (freq n) (J j n)) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  exact tsum_congr (fun n ↦ gradientProjection_realMode (freq n) (fun j ↦ J j n))

theorem contraction_rankOne (n : Wavevector) (a b : VelocityCoefficient) :
    contraction n (fun j ↦ a j • b) = modeDot n a • b := by
  simp only [contraction, modeDot, smul_smul, Finset.sum_smul]

theorem summable_indexedProjectedModes {ι : Type*} (freq : ι → Wavevector)
    (J : Fin 3 → ι → VelocityCoefficient) (hJ : ∀ j, Summable (fun n ↦ ‖J j n‖)) :
    Summable (fun n ↦ toTensorL2 (fun j ↦ realMode (freq n)
      (projectedCoeff (freq n) (fun l ↦ J l n) j))) := by
  have hs : Summable (fun n ↦ fun j ↦ realMode (freq n) (J j n)) := by
    apply Pi.summable.mpr
    intro j
    exact (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).summable
      (PancakeInfiniteFourierDerivative.summable_modeField freq (J j) (hJ j))
  have h := ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))).summable hs
  change Summable (fun n ↦ gradientProjection (toTensorL2 (fun j ↦ realMode (freq n) (J j n)))) at h
  simpa only [gradientProjection_realMode] using h

/-- Transversality cancels the input frequency before any norm is taken. -/
theorem projectedCoeff_rankOne_of_transverse (k l : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot k a = 0) (j : Fin 3) :
    projectedCoeff (k + l) (fun m ↦ a m • b) j =
      (((k + l) j : ℂ) / modeSquare (k + l) * modeDot l a) • b := by
  rw [projectedCoeff, contraction_rankOne, PancakeFourierPressureStrain.modeDot_add_wavevector,
    ha, zero_add, smul_smul]

theorem gradientProjection_rankOne_eq_zero (n : Wavevector) (a b : VelocityCoefficient)
    (ha : modeDot n a = 0) :
    gradientProjection (toTensorL2 (fun j ↦ realMode n (a j • b))) = 0 := by
  rw [gradientProjection_realMode]
  simp only [projectedCoeff, contraction_rankOne, ha, zero_smul, smul_zero]
  change tensorEmbedding (d := Fin 3) (E := R3) (fun j ↦ realModeCLM n 0) = 0
  simp only [map_zero]
  exact map_zero _

end Mettapedia.FluidDynamics.NavierStokes.PeriodicGradientFluxSymbol

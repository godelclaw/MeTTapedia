import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxGramBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityTime
import Mettapedia.Analysis.ODE.DampedGramSeriesEvolution

/-!
# Summable envelopes for the actual exchanged modes and their sources

These uniform bounds justify infinite correlated sums on local smooth
solution intervals. They are convergence bounds, not initial-data
control of the signed Gram work. The useful exchange cancellation is
retained in the modes themselves rather than replaced by these bounds.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxModeEnvelope

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeIndexedFourierMoments PancakePhysicalSixthDecay
open PancakeFixedOutputVelocityBound PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative
open PancakeDyadicDirectionEvolution PeriodicGradientFluxSymbol PeriodicGradientFluxTriple
open FourierVorticityPairDynamics ExchangedFluxModeDynamics
open PancakeGalerkinKineticEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def embeddingConstant : ℝ :=
  ‖tensorEmbedding (d := Fin 3) (E := R3)‖ *
    ‖complexRealPartEuclideanCLM.compLeftContinuous ℝ T3‖

theorem embeddingConstant_nonneg : 0 ≤ embeddingConstant := by
  unfold embeddingConstant
  positivity

theorem norm_tensorModeCLM_le (n : Wavevector) (A : Fin 3 → VelocityCoefficient) :
    ‖tensorModeCLM n A‖ ≤ embeddingConstant * ‖A‖ := by
  change ‖gradientProjection (toTensorL2 (fun j ↦ realMode n (A j)))‖ ≤ _
  apply (norm_gradientProjection_le _).trans
  apply ((tensorEmbedding (d := Fin 3) (E := R3)).le_opNorm _).trans
  have h : ‖fun j ↦ realMode n (A j)‖ ≤
      ‖complexRealPartEuclideanCLM.compLeftContinuous ℝ T3‖ * ‖A‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact ((complexRealPartEuclideanCLM.compLeftContinuous ℝ T3).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((norm_modeField_le n (A j)).trans (norm_le_pi_norm A j))
        (norm_nonneg _))
  simpa only [embeddingConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left h (norm_nonneg (tensorEmbedding (d := Fin 3) (E := R3)))

theorem norm_differenceCLM_le (p : TripleIndex) (a : VelocityCoefficient) :
    ‖differenceCLM p a‖ ≤ 6 * ‖a‖ := by
  have h (k : Wavevector) : ‖lerayMode k a‖ ≤ 3 * ‖a‖ :=
    (norm_coefficient_sup_le_euclidean _).trans ((norm_lerayMode_le k a).trans
      (norm_coefficientVec_le_three a ‖a‖ (norm_nonneg _) (norm_le_pi_norm a)))
  rw [differenceCLM_apply]
  exact (norm_sub_le _ _).trans (by linarith [h p.2.1, h p.2.2])

theorem norm_coefficientCross_le (a b : VelocityCoefficient) :
    ‖coefficientCross a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  have h (i j k l : Fin 3) : ‖a i * b j - a k * b l‖ ≤ 2 * ‖a‖ * ‖b‖ := by
    calc
      _ ≤ ‖a i‖ * ‖b j‖ + ‖a k‖ * ‖b l‖ := by simpa only [norm_mul] using norm_sub_le (a i * b j) (a k * b l)
      _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * ‖b‖ := add_le_add
        (mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b j) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (norm_le_pi_norm a k) (norm_le_pi_norm b l) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i <;> simpa [coefficientCross] using h _ _ _ _

theorem norm_mode_le (u : FourierVelocity) (p : TripleIndex) :
    ‖mode u p‖ ≤ 6 * embeddingConstant *
      (‖fourierCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖)) := by
  have h : ‖tensorCoeff u p‖ ≤
      6 * (‖fourierCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖)) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simp only [tensorCoeff, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc
      _ ≤ (1 / 2 : ℝ) * (‖fourierCurl u p.1‖ *
        (6 * (2 * ‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖))) := by
        gcongr
        · exact norm_le_pi_norm _ _
        · exact (norm_differenceCLM_le p _).trans
            (mul_le_mul_of_nonneg_left (norm_coefficientCross_le _ _) (by norm_num))
      _ = _ := by ring
  exact (norm_tensorModeCLM_le _ _).trans (by
    convert mul_le_mul_of_nonneg_left h embeddingConstant_nonneg using 1; ring)

theorem norm_sourceMode_le (u : FourierVelocity) (p : TripleIndex) :
    ‖sourceMode u p‖ ≤ 6 * embeddingConstant *
      (‖nonlinearCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) +
       ‖fourierCurl u p.1‖ * (‖nonlinearCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) +
       ‖fourierCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖nonlinearCurl u p.2.2‖)) := by
  have hc : ‖pairCross u p.2.1 p.2.2‖ ≤ 2 * ‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖ :=
    norm_coefficientCross_le _ _
  have hs : ‖pairSource u p.2.1 p.2.2‖ ≤
      2 * ‖nonlinearCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖ +
      2 * ‖fourierCurl u p.2.1‖ * ‖nonlinearCurl u p.2.2‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_coefficientCross_le _ _) (norm_coefficientCross_le _ _))
  have h : ‖sourceTensor u p‖ ≤ 6 *
      (‖nonlinearCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) +
       ‖fourierCurl u p.1‖ * (‖nonlinearCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖) +
       ‖fourierCurl u p.1‖ * (‖fourierCurl u p.2.1‖ * ‖nonlinearCurl u p.2.2‖)) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    calc
      _ ≤ (1 / 2 : ℝ) *
        (‖nonlinearCurl u p.1 j‖ * ‖differenceCLM p (pairCross u p.2.1 p.2.2)‖ +
         ‖fourierCurl u p.1 j‖ * ‖differenceCLM p (pairSource u p.2.1 p.2.2)‖) := by
        simpa only [sourceTensor, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
          mul_le_mul_of_nonneg_left (norm_add_le
            (nonlinearCurl u p.1 j • differenceCLM p (pairCross u p.2.1 p.2.2))
            (fourierCurl u p.1 j • differenceCLM p (pairSource u p.2.1 p.2.2)))
            (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ ≤ (1 / 2 : ℝ) *
        (‖nonlinearCurl u p.1‖ * (6 * (2 * ‖fourierCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖)) +
         ‖fourierCurl u p.1‖ * (6 * (2 * ‖nonlinearCurl u p.2.1‖ * ‖fourierCurl u p.2.2‖ +
          2 * ‖fourierCurl u p.2.1‖ * ‖nonlinearCurl u p.2.2‖))) := by
        gcongr
        · exact norm_le_pi_norm _ _
        · exact (norm_differenceCLM_le p _).trans (mul_le_mul_of_nonneg_left hc (by norm_num))
        · exact norm_le_pi_norm _ _
        · exact (norm_differenceCLM_le p _).trans (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = _ := by ring
  exact (norm_tensorModeCLM_le _ _).trans (by
    convert mul_le_mul_of_nonneg_left h embeddingConstant_nonneg using 1; ring)

def cubicEnvelope (a : Wavevector → ℝ) (p : TripleIndex) : ℝ :=
  6 * embeddingConstant * (a p.1 * (a p.2.1 * a p.2.2))

def sourceEnvelope (a b : Wavevector → ℝ) (p : TripleIndex) : ℝ :=
  6 * embeddingConstant *
    (b p.1 * (a p.2.1 * a p.2.2) + a p.1 * (b p.2.1 * a p.2.2) +
      a p.1 * (a p.2.1 * b p.2.2))

theorem summable_cubicEnvelope (a : Wavevector → ℝ)
    (ha : ∀ q, 0 ≤ a q) (hsa : Summable a) : Summable (cubicEnvelope a) :=
  (hsa.mul_of_nonneg (hsa.mul_of_nonneg hsa ha ha) ha
    (fun p ↦ mul_nonneg (ha p.1) (ha p.2))).mul_left _

theorem summable_sourceEnvelope (a b : Wavevector → ℝ)
    (ha : ∀ q, 0 ≤ a q) (hb : ∀ q, 0 ≤ b q) (hsa : Summable a) (hsb : Summable b) :
    Summable (sourceEnvelope a b) :=
  (((hsb.mul_of_nonneg (hsa.mul_of_nonneg hsa ha ha) hb
    (fun p ↦ mul_nonneg (ha p.1) (ha p.2))).add
    (hsa.mul_of_nonneg (hsb.mul_of_nonneg hsa hb ha) ha
      (fun p ↦ mul_nonneg (hb p.1) (ha p.2)))).add
    (hsa.mul_of_nonneg (hsa.mul_of_nonneg hsb ha hb) ha
      (fun p ↦ mul_nonneg (ha p.1) (hb p.2)))).mul_left _

theorem triple_norm_le (x y z : VelocityCoefficient) {a b c : ℝ}
    (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ b) (hz : ‖z‖ ≤ c) :
    ‖x‖ * (‖y‖ * ‖z‖) ≤ a * (b * c) :=
  mul_le_mul hx (mul_le_mul hy hz (norm_nonneg _) ((norm_nonneg _).trans hy))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans hx)

theorem norm_mode_le_cubicEnvelope (u : FourierVelocity) (a : Wavevector → ℝ)
    (ha : ∀ q, ‖fourierCurl u q‖ ≤ a q) (p : TripleIndex) :
    ‖mode u p‖ ≤ cubicEnvelope a p := by
  exact (norm_mode_le u p).trans (mul_le_mul_of_nonneg_left
    (triple_norm_le _ _ _ (ha _) (ha _) (ha _))
    (mul_nonneg (by norm_num) embeddingConstant_nonneg))

theorem norm_sourceMode_le_sourceEnvelope (u : FourierVelocity) (a b : Wavevector → ℝ)
    (ha : ∀ q, ‖fourierCurl u q‖ ≤ a q) (hb : ∀ q, ‖nonlinearCurl u q‖ ≤ b q)
    (p : TripleIndex) : ‖sourceMode u p‖ ≤ sourceEnvelope a b p := by
  exact (norm_sourceMode_le u p).trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add
      (triple_norm_le _ _ _ (hb _) (ha _) (ha _))
      (triple_norm_le _ _ _ (ha _) (hb _) (ha _)))
      (triple_norm_le _ _ _ (ha _) (ha _) (hb _)))
    (mul_nonneg (by norm_num) embeddingConstant_nonneg))

open PancakeLocalInfiniteVelocity PancakeHigherDerivativeMoments PancakeInfiniteVelocityEnvelope
open PancakeInfiniteSpatialCurl PancakeCurlOutputTail

/-- Both envelopes are constructed from the common local third velocity moment. -/
theorem exists_summable_mode_source_envelopes {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hsg : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q) :
    ∃ a b : TripleIndex → ℝ, Summable a ∧ Summable b ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ p,
        ‖mode (s.coefficients t) p‖ ≤ a p ∧ ‖sourceMode (s.coefficients t) p‖ ≤ b p := by
  let w : Wavevector → ℝ := fun q ↦ (2 * Real.pi) * g q
  let v : Wavevector → ℝ := fun q ↦ (2 * Real.pi) * velocityEnvelope 0 g q
  have hw0 (q : Wavevector) : 0 ≤ w q := mul_nonneg (by positivity) (hg q)
  have hv0 (q : Wavevector) : 0 ≤ v q :=
    mul_nonneg (by positivity) (velocityEnvelope_nonneg 0 g hg q)
  have hsw : Summable w := hsg.mul_left _
  have hsv : Summable v := (summable_velocityEnvelope 0 g hg hsg).mul_left _
  refine ⟨cubicEnvelope w, sourceEnvelope w v, summable_cubicEnvelope w hw0 hsw,
    summable_sourceEnvelope w v hw0 hv0 hsw hsv, ?_⟩
  intro t ht p
  have hw (q : Wavevector) : ‖fourierCurl (s.coefficients t) q‖ ≤ w q := by
    have h := norm_indexedCurl_le_firstMoment id (s.coefficients t) q
    simp only [indexedFirstMoment_id, indexedCurlCoeff, id_eq] at h
    change ‖fourierCurl (s.coefficients t) q‖ ≤ (2 * Real.pi) * fourierMoment 1 (s.coefficients t) q at h
    exact h.trans (mul_le_mul_of_nonneg_left
      ((fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu t ht q)) (by positivity))
  have hv (q : Wavevector) : ‖nonlinearCurl (s.coefficients t) q‖ ≤ v q :=
    LocalVorticityTime.norm_curl_velocityRHS_le 0 _ g hg hsg (hu t ht) q
  exact ⟨norm_mode_le_cubicEnvelope _ w hw p, norm_sourceMode_le_sourceEnvelope _ w v hw hv p⟩

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxModeEnvelope

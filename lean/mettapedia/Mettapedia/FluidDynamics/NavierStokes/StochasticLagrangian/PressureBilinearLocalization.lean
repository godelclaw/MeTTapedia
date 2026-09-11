import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePairInputStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierLocalizationDivergence
import Mettapedia.Analysis.FiniteFiberLinearMap
import Mettapedia.Analysis.FiniteGroupedConvolutionEnergy

/-!
# The actual one-input pressure localization commutator

Localizing a pressure convolution differs from localizing its first
vorticity input by an explicit three-frequency commutator. The energy
bound pays the scalar cutoff's first-derivative energy, the first
input's inverse-frequency l1 norm, and the second input's l1 norm.
No assumption of divergence-freeness after localization is made.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakePeriodicComplexStretch
open PancakeFiniteFourierLocalization ComplexPressurePair ComplexPressureMisalignment
open ComplexPressureConvolution PressurePairInputStability FourierResolventSmoothing FourierEllipticProductEnergy
open Mettapedia.Analysis Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def tiltPairLeftLinear (e : R3) (p k : Wavevector) (v : VelocityCoefficient) :
    VelocityCoefficient →ₗ[ℂ] C3 where
  toFun w := tiltPair e p k w v
  map_add' w z := tiltPair_add_left e p k w z v
  map_smul' c w := tiltPair_smul_left c e p k w v

def localizedOutput (e : R3) (A P K : Finset Wavevector) (c : Wavevector → ℂ)
    (w v : FourierVelocity) : Wavevector → C3 :=
  vectorConvolution A (finiteCutoffOutputModes P K) c (pairConvolution e P K w v)

def localizedSource (e : R3) (A P K : Finset Wavevector) (c : Wavevector → ℂ)
    (w v : FourierVelocity) : Wavevector → C3 :=
  pairConvolution e (finiteCutoffOutputModes A P) K (finiteCutoffConvolutionCoeff A P c w) v

def commutatorCoefficient (e : R3) (A P K : Finset Wavevector) (c : Wavevector → ℂ)
    (w v : FourierVelocity) (q : Wavevector) : C3 :=
  ∑ t ∈ (P ×ˢ K) ×ˢ A with t.1.1 + t.1.2 + t.2 = q,
    c t.2 • (tiltPair e t.1.1 t.1.2 (w t.1.1) (v t.1.2) -
      tiltPair e (t.2 + t.1.1) t.1.2 (w t.1.1) (v t.1.2))

theorem localizedOutput_eq_triple_sum (e : R3) (A P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) :
    localizedOutput e A P K c w v q =
      ∑ p ∈ P, ∑ k ∈ K, ∑ a ∈ A,
        if p + k + a = q then c a • tiltPair e p k (w p) (v k) else 0 := by
  have hf (a : Wavevector) :
      (∑ o ∈ finiteCutoffOutputModes P K,
        if a + o = q then c a • pairConvolution e P K w v o else 0) =
      ∑ pk ∈ P ×ˢ K,
        if a + (pk.1 + pk.2) = q then c a • tiltPair e pk.1 pk.2 (w pk.1) (v pk.2) else 0 := by
    let L (o : Wavevector) : C3 →ₗ[ℂ] C3 := if a + o = q then c a • LinearMap.id else 0
    have h := sum_apply_fiberwise (P ×ˢ K) (finiteCutoffOutputModes P K)
      (fun pk ↦ pk.1 + pk.2) (fun pk ↦ tiltPair e pk.1 pk.2 (w pk.1) (v pk.2)) L
      (fun pk hpk ↦ (mem_finiteCutoffOutputModes_iff P K _).mpr
        ⟨pk.1, (Finset.mem_product.mp hpk).1, pk.2, (Finset.mem_product.mp hpk).2, rfl⟩)
    have hL (o : Wavevector) (z : C3) : L o z = if a + o = q then c a • z else 0 := by
      unfold L
      split_ifs <;> rfl
    simpa only [hL, pairConvolution] using h
  unfold localizedOutput vectorConvolution
  simp only [Finset.sum_filter, Finset.sum_product, hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  rw [add_comm a (p + k)]

theorem localizedSource_eq_triple_sum (e : R3) (A P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) :
    localizedSource e A P K c w v q =
      ∑ p ∈ P, ∑ k ∈ K, ∑ a ∈ A,
        if p + k + a = q then c a • tiltPair e (a + p) k (w p) (v k) else 0 := by
  have hf (k : Wavevector) :
      (∑ l ∈ finiteCutoffOutputModes A P,
        if l + k = q then tiltPair e l k (finiteCutoffConvolutionCoeff A P c w l) (v k) else 0) =
      ∑ ap ∈ A ×ˢ P,
        if ap.1 + ap.2 + k = q then c ap.1 • tiltPair e (ap.1 + ap.2) k (w ap.2) (v k) else 0 := by
    let L (l : Wavevector) : VelocityCoefficient →ₗ[ℂ] C3 :=
      if l + k = q then tiltPairLeftLinear e l k (v k) else 0
    have h := sum_apply_fiberwise (A ×ˢ P) (finiteCutoffOutputModes A P)
      (fun ap ↦ ap.1 + ap.2) (fun ap ↦ c ap.1 • w ap.2) L
      (fun ap hap ↦ (mem_finiteCutoffOutputModes_iff A P _).mpr
        ⟨ap.1, (Finset.mem_product.mp hap).1, ap.2, (Finset.mem_product.mp hap).2, rfl⟩)
    have hL (l : Wavevector) (z : VelocityCoefficient) :
        L l z = if l + k = q then tiltPair e l k z (v k) else 0 := by
      unfold L
      split_ifs <;> rfl
    simpa only [hL, tiltPair_smul_left, finiteCutoffConvolutionCoeff] using h
  unfold localizedSource pairConvolution
  simp only [Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  simp only [hf, Finset.sum_product]
  calc
    _ = ∑ k ∈ K, ∑ p ∈ P, ∑ a ∈ A,
        if a + p + k = q then c a • tiltPair e (a + p) k (w p) (v k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      rw [show a + p + k = p + k + a by abel]

theorem localizedOutput_sub_localizedSource (e : R3) (A P K : Finset Wavevector)
    (c : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) :
    localizedOutput e A P K c w v q - localizedSource e A P K c w v q =
      commutatorCoefficient e A P K c w v q := by
  rw [localizedOutput_eq_triple_sum, localizedSource_eq_triple_sum]
  simp only [commutatorCoefficient, Finset.sum_filter, Finset.sum_product,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [smul_sub]

theorem norm_commutator_term_le (e : R3) (he : ‖e‖ = 1) (a p k : Wavevector)
    (c : ℂ) (w v : VelocityCoefficient) (hw : p = 0 → w = 0) :
    ‖c • (tiltPair e p k w v - tiltPair e (a + p) k w v)‖ ≤
      (12 * (‖coefficientVec w‖ / ‖frequencyVec p‖) * ‖coefficientVec v‖) *
        (‖frequencyVec a‖ * ‖c‖) := by
  by_cases hp : p = 0
  · rw [hw hp]
    have hz (l : Wavevector) : tiltPair e l k 0 v = 0 := (tiltPairLeftLinear e l k v).map_zero
    simp only [hz, sub_zero, smul_zero, norm_zero]
    positivity
  have hn := norm_pos_iff.mpr (frequencyVec_ne_zero hp)
  have h := norm_tiltPair_sub_left_mul_frequency_le e he p (a + p) k w v
  have ha : frequencyVec (p - (a + p)) = -frequencyVec a := by
    rw [show p - (a + p) = -a by abel]
    ext i
    simp [frequencyVec, coefficientVec, wavevectorCoefficient]
  rw [ha, norm_neg] at h
  have hd : ‖tiltPair e p k w v - tiltPair e (a + p) k w v‖ ≤
      12 * (‖coefficientVec w‖ / ‖frequencyVec p‖) * ‖coefficientVec v‖ * ‖frequencyVec a‖ := by
    calc
      _ ≤ (12 * ‖frequencyVec a‖ * ‖coefficientVec w‖ * ‖coefficientVec v‖) / ‖frequencyVec p‖ :=
        (le_div_iff₀ hn).mpr h
      _ = _ := by ring
  rw [norm_smul]
  have hc := mul_le_mul_of_nonneg_left hd (norm_nonneg c)
  nlinarith only [hc]

theorem commutator_energy_le (e : R3) (he : ‖e‖ = 1) (A P K Q : Finset Wavevector)
    (c : Wavevector → ℂ) (w v : FourierVelocity) (hw : w 0 = 0)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, ∀ a ∈ A, p + k + a ∈ Q) :
    (∑ q ∈ Q, ‖commutatorCoefficient e A P K c w v q‖ ^ 2) ≤
      144 * (∑ p ∈ P, ‖coefficientVec (w p)‖ / ‖frequencyVec p‖) ^ 2 *
        (∑ k ∈ K, ‖coefficientVec (v k)‖) ^ 2 * coordinateEnergy A c := by
  have h := FiniteGroupedConvolutionEnergy.sum_norm_sq_le (P ×ˢ K) A Q
    (fun pk ↦ pk.1 + pk.2)
    (fun pk ↦ 12 * (‖coefficientVec (w pk.1)‖ / ‖frequencyVec pk.1‖) * ‖coefficientVec (v pk.2)‖)
    (fun a ↦ ‖frequencyVec a‖ * ‖c a‖)
    (fun pk a ↦ c a • (tiltPair e pk.1 pk.2 (w pk.1) (v pk.2) -
      tiltPair e (a + pk.1) pk.2 (w pk.1) (v pk.2)))
    (fun _ _ ↦ by positivity)
    (fun pk _ a _ ↦ norm_commutator_term_le e he a pk.1 pk.2 (c a) (w pk.1) (v pk.2)
      (fun hp ↦ by simpa only [hp] using hw))
    (fun pk hpk a ha ↦ hQ _ (Finset.mem_product.mp hpk).1 _ (Finset.mem_product.mp hpk).2 a ha)
  simp only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul, mul_pow, norm_frequencyVec_eq,
    ← coordinateEnergy_eq] at h
  unfold commutatorCoefficient
  simpa only [norm_frequencyVec_eq, show (12 : ℝ) ^ 2 = 144 by norm_num] using h

end Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization

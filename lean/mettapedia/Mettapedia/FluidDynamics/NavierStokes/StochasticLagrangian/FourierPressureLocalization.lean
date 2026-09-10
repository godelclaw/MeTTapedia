import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressurePatchEnergy

/-!
# Angular pressure gain with the localization commutator retained

A cutoff does not commute with the pressure-tilt multiplier. The exact
commutator is estimated in coefficient energy with no mode-count factor.
If the pressure frequencies are at least `kappa`, its cost is quadratic
in the cutoff's first Fourier moment divided by `kappa`.

A cone hypothesis on the pressure frequencies, not on the vorticity at a
point, yields the angular main term. The cutoff radius explicitly widens
that gain. No uniform bound for the adaptive cutoffs is assumed or proved.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization

open scoped BigOperators RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFiniteFourierLocalization PancakeViscousMisalignmentAbsorption
open PancakeQuadraticFourierSupport RealFourierLocalizationEnergy FourierPressurePatchEnergy
open FourierPressureCommutator FourierPressureTiltEnergy FourierPressureTraceSymbol PressureTiltSymbol
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

def tracePatchEnergy (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  scalarEnergy (finiteCutoffOutputModes c.support outputs)
    (scalarConvolution c.support outputs c (realTraceAmplitude chi u))

def tiltCommutatorEnergy (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) : ℝ :=
  vectorEnergy (finiteCutoffOutputModes c.support outputs)
    (commutatorCoefficient c.support outputs c (realTraceAmplitude chi u) (complexTiltSymbol e))

/-- Localized trace energy where the actual tilt symbol exceeds `eta`.
This is a symbol threshold, not a hypothesis on vorticity alignment. -/
def tiltTailTraceEnergy (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (eta : ℝ) : ℝ :=
  scalarEnergy ((finiteCutoffOutputModes c.support outputs).filter
    (fun q ↦ eta < ‖complexTiltSymbol e q‖))
    (scalarConvolution c.support outputs c (realTraceAmplitude chi u))

def cutoffFrequencyMass (c : FourierCoeff (Fin 3)) : ℝ := ∑ p ∈ c.support, ‖c p‖ * ‖realFrequency p‖

theorem cutoffFrequencyMass_nonneg (c : FourierCoeff (Fin 3)) : 0 ≤ cutoffFrequencyMass c :=
  Finset.sum_nonneg (fun _ _ ↦ by positivity)

theorem localized_tiltCoefficient_eq (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (q : Wavevector) :
    coefficientVec (localizedCoefficient c outputs (tiltCoefficient chi u e) q) =
      vectorConvolution c.support outputs c (fun k ↦ realTraceAmplitude chi u k • complexTiltSymbol e k) q := by
  unfold localizedCoefficient finiteCutoffConvolutionCoeff vectorConvolution
  simp only [coefficientVec, WithLp.toLp_sum]
  apply Finset.sum_congr rfl
  intro pk _
  change c pk.1 • coefficientVec (PancakeRealFourierProjection.realSymmetricCoeff
    (tiltCoefficient chi u e) pk.2) = _
  rw [realSymmetric_tiltCoefficient_eq]

theorem frozenPatchEnergy_eq (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) :
    frozenPatchEnergy c chi outputs u e = vectorEnergy (finiteCutoffOutputModes c.support outputs)
      (vectorConvolution c.support outputs c (fun k ↦ realTraceAmplitude chi u k • complexTiltSymbol e k)) := by
  unfold frozenPatchEnergy localizedEnergy fullEnergy vectorEnergy
  simp only [← norm_coefficientVec_sq, localized_tiltCoefficient_eq]

theorem frozenPatchEnergy_le_main_add_commutator (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (eta : ℝ)
    (hm : ∀ q ∈ finiteCutoffOutputModes c.support outputs, ‖complexTiltSymbol e q‖ ≤ eta) :
    frozenPatchEnergy c chi outputs u e ≤
      2 * eta ^ 2 * tracePatchEnergy c chi outputs u + 2 * tiltCommutatorEnergy c chi outputs u e := by
  rw [frozenPatchEnergy_eq]
  exact localized_multiplier_energy_le _ _ _ _ _ _ eta hm

/-- No pressure cone is assumed. Every mode is retained: small-symbol
modes receive the angular gain, and the rest enter the explicit tail. -/
theorem frozenPatchEnergy_le_with_tail (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1)
    (eta : ℝ) (heta : 0 ≤ eta) :
    frozenPatchEnergy c chi outputs u e ≤
      2 * eta ^ 2 * tracePatchEnergy c chi outputs u +
        2 * tiltTailTraceEnergy c chi outputs u e eta +
        2 * tiltCommutatorEnergy c chi outputs u e := by
  rw [frozenPatchEnergy_eq]
  have h := localized_multiplier_energy_le_with_tail c.support outputs
    (finiteCutoffOutputModes c.support outputs) c (realTraceAmplitude chi u)
    (complexTiltSymbol e) eta 1 heta (fun q _ ↦ by
      rw [complexTiltSymbol, norm_complexifyVector]
      exact norm_tiltSymbol_le_one e (realFrequency q) he)
  simpa only [one_pow, mul_one, tracePatchEnergy, tiltTailTraceEnergy, tiltCommutatorEnergy] using h

theorem norm_complexTiltSymbol_sub_le (e : R3) (he : ‖e‖ = 1) (p k : Wavevector)
    (kappa : ℝ) (hkappa : 0 < kappa) (hk : kappa ≤ ‖realFrequency k‖) :
    ‖complexTiltSymbol e k - complexTiltSymbol e (p + k)‖ ≤ 4 * ‖realFrequency p‖ / kappa := by
  have hk0 : realFrequency k ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hkappa.trans_le hk))
  change ‖complexifyVector (tiltSymbol e (realFrequency k)) -
    complexifyVector (tiltSymbol e (realFrequency (p + k)))‖ ≤ _
  rw [← complexifyVector_sub, norm_complexifyVector]
  have h := norm_tiltSymbol_sub_le e (realFrequency k) (realFrequency (p + k)) he hk0
  rw [realFrequency_add, show realFrequency k - (realFrequency p + realFrequency k) =
    -realFrequency p by abel, norm_neg] at h
  simpa only [realFrequency_add] using h.trans (div_le_div_of_nonneg_left (by positivity) hkappa hk)

theorem tiltCommutatorEnergy_le (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (hk : ∀ k ∈ outputs, kappa ≤ ‖realFrequency k‖)
    (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    tiltCommutatorEnergy c chi outputs u e ≤
      16 / kappa ^ 2 * cutoffFrequencyMass c ^ 2 * hessianEnergy chi outputs u := by
  have h := commutator_energy_le c.support outputs (finiteCutoffOutputModes c.support outputs)
    c (realTraceAmplitude chi u) (complexTiltSymbol e) (fun p ↦ 4 * ‖realFrequency p‖ / kappa)
    (fun _ _ ↦ by positivity) (fun p _ k hmem ↦ norm_complexTiltSymbol_sub_le e he p k kappa hkappa (hk k hmem))
    (fun p hp k hmem ↦ (mem_finiteCutoffOutputModes_iff _ _ _).mpr ⟨p, hp, k, hmem, rfl⟩)
  have hmass : (∑ p ∈ c.support, ‖c p‖ * (4 * ‖realFrequency p‖ / kappa)) =
      (4 / kappa) * cutoffFrequencyMass c := by
    unfold cutoffFrequencyMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hmass] at h
  calc
    _ ≤ ((4 / kappa) * cutoffFrequencyMass c) ^ 2 * scalarEnergy outputs (realTraceAmplitude chi u) := h
    _ ≤ ((4 / kappa) * cutoffFrequencyMass c) ^ 2 * hessianEnergy chi outputs u :=
      mul_le_mul_of_nonneg_left (scalarEnergy_realTraceAmplitude_le chi outputs u hs) (sq_nonneg _)
    _ = _ := by ring

/-- Cutoff frequencies widen the cone gain by their relative size. The
formula is valid without a smallness assumption on that size. -/
theorem norm_complexTiltSymbol_output_le (c : FourierCoeff (Fin 3)) (outputs : Finset Wavevector)
    (e : R3) (he : ‖e‖ = 1) (eta kappa radius : ℝ) (heta : 0 ≤ eta) (hkappa : 0 < kappa)
    (hk : ∀ k ∈ outputs, kappa ≤ ‖realFrequency k‖)
    (hcone : ∀ k ∈ outputs, ⟪realFrequency k, e⟫ ^ 2 ≤ eta ^ 2 * ‖realFrequency k‖ ^ 2)
    (hwidth : ∀ p ∈ c.support, ‖realFrequency p‖ ≤ radius)
    (q : Wavevector) (hq : q ∈ finiteCutoffOutputModes c.support outputs) :
    ‖complexTiltSymbol e q‖ ≤ eta + 4 * radius / kappa := by
  obtain ⟨p, hp, k, hmem, rfl⟩ := (mem_finiteCutoffOutputModes_iff _ _ _).mp hq
  have hm : ‖complexTiltSymbol e k‖ ≤ eta := by
    rw [complexTiltSymbol, norm_complexifyVector]
    exact (sq_le_sq₀ (norm_nonneg _) heta).mp (norm_tiltSymbol_sq_le e (realFrequency k) he eta (hcone k hmem))
  have hv := norm_complexTiltSymbol_sub_le e he p k kappa hkappa (hk k hmem)
  have hw := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hwidth p hp) (by norm_num : (0 : ℝ) ≤ 4)) hkappa.le
  have hn := norm_le_norm_sub_add (complexTiltSymbol e (p + k)) (complexTiltSymbol e k)
  rw [norm_sub_rev] at hn
  linarith only [hm, hv, hw, hn]

/-- A spatially weighted pressure cone estimate with its actual cutoff
commutator cost. Both the input cone and Fourier cutoff width are explicit. -/
theorem frozenPatchEnergy_le_of_cone (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1)
    (eta kappa radius : ℝ) (heta : 0 ≤ eta) (hkappa : 0 < kappa)
    (hk : ∀ k ∈ outputs, kappa ≤ ‖realFrequency k‖)
    (hcone : ∀ k ∈ outputs, ⟪realFrequency k, e⟫ ^ 2 ≤ eta ^ 2 * ‖realFrequency k‖ ^ 2)
    (hwidth : ∀ p ∈ c.support, ‖realFrequency p‖ ≤ radius)
    (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    frozenPatchEnergy c chi outputs u e ≤
      2 * (eta + 4 * radius / kappa) ^ 2 * tracePatchEnergy c chi outputs u +
        32 / kappa ^ 2 * cutoffFrequencyMass c ^ 2 * hessianEnergy chi outputs u := by
  have h1 := frozenPatchEnergy_le_main_add_commutator c chi outputs u e _
    (norm_complexTiltSymbol_output_le c outputs e he eta kappa radius heta hkappa hk hcone hwidth)
  have h2 := tiltCommutatorEnergy_le c chi outputs u e he kappa hkappa hk hs
  calc
    _ ≤ 2 * (eta + 4 * radius / kappa) ^ 2 * tracePatchEnergy c chi outputs u +
        2 * tiltCommutatorEnergy c chi outputs u e := h1
    _ ≤ 2 * (eta + 4 * radius / kappa) ^ 2 * tracePatchEnergy c chi outputs u +
        2 * (16 / kappa ^ 2 * cutoffFrequencyMass c ^ 2 * hessianEnergy chi outputs u) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureLocalization

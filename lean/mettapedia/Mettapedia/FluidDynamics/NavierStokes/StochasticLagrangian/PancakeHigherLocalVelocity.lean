import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherGalerkinWindow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalInfiniteVelocity

/-!
# Actual infinite velocity solutions with constructed higher-order control

The higher-order bound and the nonlinear equation refer to the same
coefficient curve. A sufficiently high order also constructs a common
summable absolute-moment envelope on the positive local interval.
No global-in-time moment bound is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherLocalVelocity

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet PancakeCurlOutputTail
open PancakeLocalVelocityExistence PancakeLocalInfiniteVelocity
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties PancakeCoefficientLimitEquation
open PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate PancakeHigherGalerkinWindow
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeLatticeDecayEnvelope

/-- The constructor exposes its coefficients so all higher-order estimates
remain attached to the very curve satisfying the infinite equation. -/
def localInfiniteVelocitySolutionOfOrder (m : ℕ) (hm : 2 ≤ m)
    {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (hphi : StrictMono phi) (hT : 0 ≤ T) (hzero : u₀ 0 = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ B) :
    LocalInfiniteVelocitySolution nu u₀ T B := by
  have hE₂ : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B :=
    fun n t ht ↦ (sobolevEnergy_le_velocityEnergy m hm _ _).trans (hE n t ht)
  refine {
    coefficients := coefficientCurve a hT
    continuous := continuous_coefficientCurve a hT
    initial := ?_
    reality := fun t q ↦ limitField_reality s phi a h (Set.projIcc 0 T hT t) q
    transverse := fun t q ↦ limitField_transverse s phi a h (Set.projIcc 0 T hT t) q
    zero := fun t ↦ limitField_zero s phi a h (Set.projIcc 0 T hT t)
    sobolev_bound := ?_
    equation := fun t ht q i ↦ coefficientLimit_hasDerivAt s phi a h hphi hT B hB hE₂ q i t ht }
  · rw [coefficientCurve_apply a hT 0 ⟨le_rfl, hT⟩]
    exact limitField_initial s phi a h hphi hT hzero
  · intro t ht F
    rw [coefficientCurve_apply a hT t ht]
    exact limitField_finite_sobolev_bound s phi a h B hE₂ ⟨t, ht⟩ F

theorem localInfiniteVelocitySolutionOfOrder_bound (m : ℕ) (hm : 2 ≤ m)
    {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (hphi : StrictMono phi) (hT : 0 ≤ T) (hzero : u₀ 0 = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ B)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (F : Finset Wavevector) :
    velocityEnergy m F
      ((localInfiniteVelocitySolutionOfOrder m hm s phi a h hphi hT hzero B hB hE).coefficients t) ≤
      B := by
  change velocityEnergy m F (coefficientCurve a hT t) ≤ B
  rw [coefficientCurve_apply a hT t ht]
  exact limitField_finite_order_bound m s phi a h B hE ⟨t, ht⟩ F

local notation "T3" => UnitAddTorus (Fin 3)

theorem exists_physical_higher_localVelocity (m : ℕ) (hm : 2 ≤ m)
    (nu : ℝ) (hnu : 0 < nu) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (m+2) (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
        ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ F, velocityEnergy m F (s.coefficients t) ≤ B := by
  obtain ⟨T, hT, B, hB, s, a, phi, hphi, hE, ha, _⟩ :=
    exists_physical_order_coefficient_limit m hm nu hnu f hf hr hd
  exact ⟨T, hT, B, hB,
    localInfiniteVelocitySolutionOfOrder m hm s phi a ha hphi hT.le hzero B hB hE,
    localInfiniteVelocitySolutionOfOrder_bound m hm s phi a ha hphi hT.le hzero B hB hE⟩

theorem orderMoment_le_sqrt_energy (m : ℕ) (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, velocityEnergy m F u ≤ B) (k : Wavevector) :
    fourierMoment m u k ≤ Real.sqrt B := by
  have hk := hB {k}
  change (∑ q ∈ ({k} : Finset Wavevector), (orderWeight m q * amplitude u q)^2) ≤ B at hk
  simp only [Finset.sum_singleton] at hk
  change orderWeight m k * amplitude u k ≤ Real.sqrt B
  exact (Real.le_sqrt (mul_nonneg (orderWeight_pos m k).le (norm_nonneg _))
    ((sq_nonneg _).trans hk)).mpr hk

/-- Four extra powers turn a pointwise energy bound into a common summable
absolute-moment envelope; this bound applies uniformly to the whole interval. -/
theorem orderMoment_le_latticeEnvelope (p : ℕ) (u : FourierVelocity) (B : ℝ)
    (hB : ∀ F : Finset Wavevector, velocityEnergy (p+4) F u ≤ B) (k : Wavevector) :
    fourierMoment p u k ≤ Real.sqrt B * latticeDecayWeight k := by
  have h := orderMoment_le_sqrt_energy (p+4) u B hB k
  have hd : 0 < (1 + ‖frequencyVec k‖)^4 := by positivity
  rw [latticeDecayWeight, mul_one_div, le_div_iff₀ hd]
  simpa only [fourierMoment, pow_add, mul_assoc, mul_comm, mul_left_comm] using h

theorem exists_physical_localMomentEnvelope (p : ℕ) (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (p+6) (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (torusFourierVelocity f) T B,
      ∃ g : Wavevector → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
        ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment p (s.coefficients t) k ≤ g k := by
  obtain ⟨T, hT, B, hB, s, hs⟩ :=
    exists_physical_higher_localVelocity (p+4) (by omega) nu hnu f hf hr hd hzero
  refine ⟨T, hT, B, hB, s, fun k ↦ Real.sqrt B * latticeDecayWeight k,
    fun k ↦ mul_nonneg (Real.sqrt_nonneg B) (latticeDecayWeight_pos k).le,
    summable_latticeDecayWeight.mul_left _, fun t ht k ↦ ?_⟩
  exact orderMoment_le_latticeEnvelope p _ B (hs t ht) k

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherLocalVelocity

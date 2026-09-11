import Mettapedia.Analysis.FiniteFourierConcentration
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierProductEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalFourierDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicOperatorKernel

/-!
# Mean-zero periodic Fourier packets obstruct an energy-only product bound

Modulation moves a Dirichlet packet to positive frequencies without changing
its magnitude. Its square energy grows linearly and its fourth-power energy
at least cubically. This refutes a generic energy-only product estimate, not
an estimate using the linked Navier--Stokes dynamics or a blowup theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration

open MeasureTheory PeriodicFourierTriad PancakeMisalignmentEnergyBridge
open PancakeFiniteFourierLocalization FourierProductEnergy PancakePhysicalFourierDerivative
open Mettapedia.Analysis.FiniteMultiplierLocalization Mettapedia.Analysis.FiniteFourierConcentration

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def frequencyAxis : ℤ →+ Wavevector where
  toFun k j := if j = 0 then k else 0
  map_zero' := by ext j; simp
  map_add' k l := by ext j; by_cases h : j = 0 <;> simp [h]

theorem frequencyAxis_injective : Function.Injective frequencyAxis := by
  intro k l h
  simpa [frequencyAxis] using congrFun h 0

def packet (n : ℕ) (x : T3) : ℂ :=
  UnitAddTorus.mFourier (frequencyAxis (2 * n + 1)) x *
    finiteScalarFourierReconstruction (intervalModes frequencyAxis n) (fun _ ↦ (1 : ℂ)) x

theorem continuous_packet (n : ℕ) : Continuous (packet n) :=
  (UnitAddTorus.mFourier _).continuous.mul (continuous_finiteScalarFourierReconstruction _ _)

theorem norm_packet (n : ℕ) (x : T3) :
    ‖packet n x‖ = ‖finiteScalarFourierReconstruction (intervalModes frequencyAxis n) (fun _ ↦ (1 : ℂ)) x‖ := by
  simp only [packet, norm_mul, norm_character, one_mul]

theorem packet_eq_sum (n : ℕ) (x : T3) :
    packet n x = ∑ k ∈ intervalModes frequencyAxis n,
      UnitAddTorus.mFourier (frequencyAxis (2 * n + 1) + k) x := by
  simp only [packet, finiteScalarFourierReconstruction, mul_one, Finset.mul_sum, UnitAddTorus.mFourier_add]

theorem packet_frequency_bounds (n : ℕ) (k : Wavevector) (hk : k ∈ intervalModes frequencyAxis n) :
    ∃ r : ℤ, frequencyAxis (2 * n + 1) + k = frequencyAxis r ∧
      2 * (n : ℤ) + 1 ≤ r ∧ r ≤ 4 * n + 1 := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
  have hs' := Finset.mem_Icc.mp hs
  exact ⟨2 * n + 1 + s, (frequencyAxis.map_add _ _).symm, by omega, by omega⟩

theorem integral_packet (n : ℕ) : (∫ x : T3, packet n x) = 0 := by
  simp_rw [packet_eq_sum]
  rw [integral_finsetSum _ (fun k _ ↦
    (UnitAddTorus.mFourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
  have h0 : frequencyAxis (2 * n + 1) + frequencyAxis r ≠ 0 := by
    rw [← map_add]
    intro h
    have h' := frequencyAxis_injective (h.trans frequencyAxis.map_zero.symm)
    have hr' := Finset.mem_Icc.mp hr
    omega
  simp only [PancakePeriodicOperatorKernel.integral_mFourier, if_neg h0]

theorem integral_norm_packet_sq (n : ℕ) : (∫ x : T3, ‖packet n x‖ ^ 2) = 2 * n + 1 := by
  simp_rw [norm_packet]
  rw [← scalarEnergy_eq_integral, scalarEnergy_intervalModes frequencyAxis frequencyAxis_injective]

theorem integral_norm_packet_four_ge (n : ℕ) :
    ((n : ℝ) + 1) ^ 3 ≤ ∫ x : T3, ‖packet n x‖ ^ 4 := by
  have h := scalarEnergy_intervalConvolution_ge frequencyAxis frequencyAxis_injective n
  change _ ≤ scalarEnergy (finiteCutoffOutputModes _ _) _ at h
  rw [scalarEnergy_convolution_eq_integral] at h
  simpa only [norm_packet, ← pow_add] using h

theorem exists_packet_productEnergy_gt (C : ℝ) :
    ∃ n : ℕ, C * (∫ x : T3, ‖packet n x‖ ^ 2) ^ 2 < ∫ x : T3, ‖packet n x‖ ^ 4 := by
  obtain ⟨n, h⟩ := exists_intervalConvolution_energy_gt frequencyAxis frequencyAxis_injective C
  refine ⟨n, ?_⟩
  change _ < scalarEnergy (finiteCutoffOutputModes _ _) _ at h
  rw [scalarEnergy_convolution_eq_integral, scalarEnergy_intervalModes frequencyAxis frequencyAxis_injective] at h
  simpa only [norm_packet, ← pow_add, ← integral_norm_packet_sq] using h

/-- Even the zero-mean continuous periodic class admits no such constant.
The witnesses above are explicit finite trigonometric polynomials. -/
theorem not_exists_uniform_productEnergy_bound :
    ¬ ∃ C : ℝ, ∀ f : C(T3, ℂ), (∫ x : T3, f x) = 0 →
      (∫ x : T3, ‖f x‖ ^ 4) ≤ C * (∫ x : T3, ‖f x‖ ^ 2) ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_packet_productEnergy_gt C
  exact (not_lt_of_ge (hC ⟨packet n, continuous_packet n⟩ (integral_packet n))) hn

/-- Concentration persists when every witness has exactly unit square
energy. The fields remain mean zero after normalization. -/
theorem exists_unit_energy_fourthEnergy_gt (C : ℝ) :
    ∃ f : C(T3, ℂ), (∫ x : T3, f x) = 0 ∧
      (∫ x : T3, ‖f x‖ ^ 2) = 1 ∧ C < ∫ x : T3, ‖f x‖ ^ 4 := by
  obtain ⟨n, hn⟩ := exists_packet_productEnergy_gt C
  let E : ℝ := 2 * n + 1
  have hE : 0 < E := by dsimp only [E]; positivity
  let f : C(T3, ℂ) := ⟨fun x ↦ (Real.sqrt E)⁻¹ • packet n x, continuous_const.smul (continuous_packet n)⟩
  have hnorm (x : T3) : ‖f x‖ ^ 2 = E⁻¹ * ‖packet n x‖ ^ 2 := by
    simp only [f, ContinuousMap.coe_mk, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt hE.le]
  have hnorm4 (x : T3) : ‖f x‖ ^ 4 = (E ^ 2)⁻¹ * ‖packet n x‖ ^ 4 := by
    calc
      _ = (‖f x‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hnorm, mul_pow, inv_pow]; ring
  have henergy : (∫ x : T3, ‖f x‖ ^ 2) = 1 := by
    simp_rw [hnorm]
    rw [integral_const_mul, integral_norm_packet_sq]
    exact inv_mul_cancel₀ hE.ne'
  have hfour : (∫ x : T3, ‖f x‖ ^ 4) = (E ^ 2)⁻¹ * ∫ x : T3, ‖packet n x‖ ^ 4 := by
    simp_rw [hnorm4]
    exact integral_const_mul _ _
  refine ⟨f, ?_, henergy, ?_⟩
  · change (∫ x : T3, (Real.sqrt E)⁻¹ • packet n x) = 0
    rw [integral_smul, integral_packet, smul_zero]
  · rw [hfour]
    rw [integral_norm_packet_sq] at hn
    have h := mul_lt_mul_of_pos_left hn (inv_pos.mpr (sq_pos_of_pos hE))
    have hid : (E ^ 2)⁻¹ * (C * (2 * (n : ℝ) + 1) ^ 2) = C := by
      change (E ^ 2)⁻¹ * (C * E ^ 2) = C
      rw [mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ hE.ne'), mul_one]
    rwa [hid] at h

end Mettapedia.FluidDynamics.NavierStokes.PeriodicFourierProductConcentration

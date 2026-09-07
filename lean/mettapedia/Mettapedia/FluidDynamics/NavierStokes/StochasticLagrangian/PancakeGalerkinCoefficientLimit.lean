import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoefficientEquicontinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCountablePathCompactness
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevTimeBudget

/-!
# A constructed subsequential Fourier coefficient limit

The centered nonzero boxes exhaust the physical frequencies. A single
subsequence of the constructed Galerkin family converges uniformly in time
at every Fourier component. No nonlinear equation for the limit is asserted
before the nonlinear passage to the limit is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinCoefficientLimit

open scoped BigOperators ComplexConjugate NNReal Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeArbitraryDataBlocks PancakeLocalVelocityExistence
open PancakeViscousMisalignmentAbsorption PancakeCoefficientEquicontinuity
open PancakeCountablePathCompactness PancakeSobolevWeights PancakeSobolevVelocityRate
open PancakeSobolevTimeBudget PancakeContinuousCoordinateJet

def galerkinModes (n : ℕ) : Finset Wavevector := (wavevectorBox n).erase 0

theorem galerkinModes_symmetric (n : ℕ) (q : Wavevector) :
    -q ∈ galerkinModes n ↔ q ∈ galerkinModes n := by
  simp [galerkinModes, Finset.mem_erase, mem_wavevectorBox_iff, Pi.neg_apply]

theorem galerkinModes_nonzero (n : ℕ) (q : Wavevector) (hq : q ∈ galerkinModes n) :
    frequencyVec q ≠ 0 :=
  frequencyVec_ne_zero (Finset.mem_erase.mp hq).1

theorem eventually_mem_galerkinModes (q : Wavevector) (hq : q ≠ 0) :
    ∀ᶠ n in atTop, q ∈ galerkinModes n := by
  refine eventually_atTop.mpr ⟨(q 0).natAbs + (q 1).natAbs + (q 2).natAbs, fun n hn ↦ ?_⟩
  apply Finset.mem_erase.mpr ⟨hq, ?_⟩
  rw [mem_wavevectorBox_iff]
  intro i
  rw [Int.abs_eq_natAbs]
  have hi : (q i).natAbs ≤ n := by
    fin_cases i
    · change (q 0).natAbs ≤ n
      omega
    · change (q 1).natAbs ≤ n
      omega
    · change (q 2).natAbs ≤ n
      omega
  exact_mod_cast hi

theorem galerkinModes_mono : Monotone galerkinModes := by
  intro n m hnm q hq
  obtain ⟨h0, hq⟩ := Finset.mem_erase.mp hq
  apply Finset.mem_erase.mpr ⟨h0, ?_⟩
  rw [mem_wavevectorBox_iff] at hq ⊢
  intro i
  exact (hq i).trans (by exact_mod_cast hnm)

theorem fullEnergy_le_sobolevEnergy (M : Finset Wavevector) (u : FourierVelocity) :
    fullEnergy M u ≤ sobolevEnergy M u := by
  rw [fullEnergy, sobolevEnergy_eq]
  apply Finset.sum_le_sum
  intro q hq
  have hw : 1 ≤ weight q := by
    unfold weight
    nlinarith [norm_nonneg (frequencyVec q)]
  have he : 0 ≤ coefficientEnergy (u q) := by
    rw [← norm_coefficientVec_sq]
    positivity
  nlinarith [mul_nonneg (show 0 ≤ weight q ^ 2 - 1 by nlinarith) he]

abbrev CoefficientLimit (T : ℝ) :=
  Wavevector → Fin 3 → BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ

/-- A common kinetic bound suffices for one time-uniform subsequence
simultaneously at every coefficient. -/
theorem exists_coefficient_subsequence {nu T : ℝ} {u₀ : FourierVelocity}
    (M : ℕ → Finset Wavevector) (s : ∀ n, LocalVelocitySolution (M n) nu u₀ T)
    (hk : ∀ n q, q ∈ M n → frequencyVec q ≠ 0) (U : ℝ) (hU : 0 ≤ U)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T → fullEnergy (M n) ((s n).coefficients t) ≤ U) :
    ∃ a : CoefficientLimit T, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ q i, TendstoUniformly
        (fun n (t : Set.Icc (0 : ℝ) T) ↦ (s (phi n)).coefficients t q i) (a q i) atTop := by
  let K : Wavevector × Fin 3 → ℝ≥0 := fun p ↦
    ⟨outputSpeed nu U p.1, outputSpeed_nonneg nu U p.1 hU⟩
  obtain ⟨a, phi, hphi, ha⟩ := exists_countable_tendstoUniformly
    (fun n (p : Wavevector × Fin 3) ↦ coefficientPath (s n) p.1 p.2) K (fun _ ↦ Real.sqrt U)
    (fun n p ↦ coefficientPath_lipschitz (s n) (hk n) U hU (hE n) p.1 p.2)
    (fun n p t ↦ coefficient_component_le_of_energy (s n) t U (hE n t t.2) p.1 p.2)
  exact ⟨fun q i ↦ a (q, i), phi, hphi, fun q i ↦ ha (q, i)⟩

local notation "T3" => UnitAddTorus (Fin 3)

/-- The common coefficient limit is extracted from solutions constructed
from the physical initial field; the future trajectories are not inputs. -/
theorem exists_physical_galerkin_coefficient_limit (nu : ℝ) (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 6 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ k, modeDot k (torusFourierVelocity f k) = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∃ H ≥ (0 : ℝ),
      ∃ s : ∀ n, LocalVelocitySolution (galerkinModes n) nu (torusFourierVelocity f) T,
      ∃ a : CoefficientLimit T, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ n t, t ∈ Set.Icc (0 : ℝ) T →
        sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B ∧
        nu * (2 * Real.pi)^2 *
          (∫ r in (0 : ℝ)..t, sobolevDissipation (galerkinModes n) ((s n).coefficients r)) ≤ H) ∧
      ∀ q i, TendstoUniformly
        (fun n (t : Set.Icc (0 : ℝ) T) ↦ (s (phi n)).coefficients t q i) (a q i) atTop := by
  obtain ⟨T, hT, B, hB, H, hH, hs⟩ := exists_common_physical_solution_with_budget nu hnu f hf hr hd
  choose s hb using fun n ↦ hs (galerkinModes n) (galerkinModes_symmetric n) (galerkinModes_nonzero n)
  obtain ⟨a, phi, hphi, ha⟩ := exists_coefficient_subsequence galerkinModes s
    galerkinModes_nonzero B hB (fun n t ht ↦
      (fullEnergy_le_sobolevEnergy _ _).trans (hb n t ht).1)
  exact ⟨T, hT, B, hB, H, hH, s, a, phi, hphi, hb, ha⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinCoefficientLimit

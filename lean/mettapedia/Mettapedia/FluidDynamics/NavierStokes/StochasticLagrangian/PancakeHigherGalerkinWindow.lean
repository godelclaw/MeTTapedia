import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherSobolevWindow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherInitialEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoefficientLimitProperties

/-!
# A common higher-order interval and its actual coefficient limit

For each fixed order, actual finite velocity solutions have one positive
interval and bound independent of the cutoff. The same bound passes to any
coefficient limit of that family, without replacing that limit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeHigherGalerkinWindow

open scoped BigOperators ComplexConjugate Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeBlockReality PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet
open PancakePhysicalFieldReconstruction PancakeLocalVelocityExistence
open PancakeFiniteVelocityContinuation PancakeSobolevVelocityRate PancakeSobolevWeights
open PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate PancakeHigherSobolevWindow
open PancakeHigherInitialEnergy PancakeQuadraticGrowthWindow
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties

theorem sobolevEnergy_le_velocityEnergy (m : ℕ) (hm : 2 ≤ m)
    (M : Finset Wavevector) (u : FourierVelocity) :
    sobolevEnergy M u ≤ velocityEnergy m M u := by
  change (∑ q ∈ M, (weight q * amplitude u q)^2) ≤
    ∑ q ∈ M, (orderWeight m q * amplitude u q)^2
  apply Finset.sum_le_sum
  intro q hq
  apply pow_le_pow_left₀ (mul_nonneg (weight_pos q).le (norm_nonneg _))
  exact mul_le_mul_of_nonneg_right (orderWeight_lower m hm q) (norm_nonneg _)

theorem exists_common_order_solution (m : ℕ) (hm : 2 ≤ m) (nu : ℝ) (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M u₀ ≤ B₀) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ q, -q ∈ M ↔ q ∈ M) → (∀ q ∈ M, frequencyVec q ≠ 0) →
      ∃ s : LocalVelocitySolution M nu u₀ T,
        ∀ t ∈ Set.Icc (0 : ℝ) T, velocityEnergy m M (s.coefficients t) ≤ B := by
  let T := timeWindow (orderGrowthConstant m nu) B₀
  have hT : 0 < T := timeWindow_pos _ _ (orderGrowthConstant_nonneg m nu hnu) hB₀
  refine ⟨T, hT, 2 * (B₀+1), by positivity, fun M hs hk ↦ ?_⟩
  obtain ⟨s⟩ := exists_finiteHorizon_velocitySolution M nu hnu.le u₀ hs hk hr
    (fun q _ ↦ hd q) T hT.le
  exact ⟨s, fun t ht ↦ localSolution_order_bound m hm s hnu hk B₀ hB₀ (hE₀ M) t ht ht.2⟩

local notation "T3" => UnitAddTorus (Fin 3)

/-- Order m+2 physical derivatives construct the order-m initial energy
and all future finite trajectories; neither is an extra hypothesis. -/
theorem exists_common_physical_order_solution (m : ℕ) (hm : 2 ≤ m)
    (nu : ℝ) (hnu : 0 < nu) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (m+2) (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∀ M : Finset Wavevector,
      (∀ q, -q ∈ M ↔ q ∈ M) → (∀ q ∈ M, frequencyVec q ≠ 0) →
      ∃ s : LocalVelocitySolution M nu (torusFourierVelocity f) T,
        ∀ t ∈ Set.Icc (0 : ℝ) T, velocityEnergy m M (s.coefficients t) ≤ B := by
  obtain ⟨B₀, hB₀, hE₀⟩ := exists_physical_orderEnergy_bound m f hf
  exact exists_common_order_solution m hm nu hnu _ (torusFourierVelocity_conjugate f hr)
    hd B₀ hB₀ hE₀

theorem velocityEnergy_of_support_le (m : ℕ) (M F : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, q ∉ M → u q = 0) :
    velocityEnergy m F u ≤ velocityEnergy m M u := by
  rw [velocityEnergy_eq, velocityEnergy_eq]
  have he : (∑ q ∈ F ∩ M, orderWeight m q ^ 2 * coefficientEnergy (u q)) =
      ∑ q ∈ F, orderWeight m q ^ 2 * coefficientEnergy (u q) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    have hM : q ∉ M := fun hm ↦ hn (Finset.mem_inter.mpr ⟨hq, hm⟩)
    rw [hs q hM]
    simp [coefficientEnergy]
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro q hq hn
  rw [← norm_coefficientVec_sq]
  positivity

theorem continuous_velocityEnergy (m : ℕ) (F : Finset Wavevector) :
    Continuous (velocityEnergy m F) := by
  change Continuous (fun u : FourierVelocity ↦ velocityEnergy m F u)
  simp only [velocityEnergy_eq, coefficientEnergy]
  fun_prop

theorem limitField_finite_order_bound (m : ℕ) {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (B : ℝ) (hB : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ B)
    (t : Set.Icc (0 : ℝ) T) (F : Finset Wavevector) :
    velocityEnergy m F (limitField a t) ≤ B := by
  have hn := ((continuous_velocityEnergy m F).tendsto (limitField a t)).comp
    (tendsto_limitField s phi a h t)
  apply le_of_tendsto hn
  exact Eventually.of_forall (fun n ↦
    (velocityEnergy_of_support_le m _ F _ ((s (phi n)).support t)).trans (hB (phi n) t t.2))

/-- A single extracted coefficient limit retains the higher-order bound. -/
theorem exists_physical_order_coefficient_limit (m : ℕ) (hm : 2 ≤ m)
    (nu : ℝ) (hnu : 0 < nu) (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (m+2) (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : ∀ n, LocalVelocitySolution (galerkinModes n) nu (torusFourierVelocity f) T,
      ∃ a : CoefficientLimit T, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ n t, t ∈ Set.Icc (0 : ℝ) T →
        velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ B) ∧
      IsCoefficientLimit s phi a ∧
      ∀ t F, velocityEnergy m F (limitField a t) ≤ B := by
  obtain ⟨T, hT, B, hB, hs⟩ := exists_common_physical_order_solution m hm nu hnu f hf hr hd
  choose s hb using fun n ↦ hs (galerkinModes n) (galerkinModes_symmetric n) (galerkinModes_nonzero n)
  obtain ⟨a, phi, hphi, ha⟩ := exists_coefficient_subsequence galerkinModes s
    galerkinModes_nonzero B hB (fun n t ht ↦
      (fullEnergy_le_sobolevEnergy _ _).trans
        ((sobolevEnergy_le_velocityEnergy m hm _ _).trans (hb n t ht)))
  exact ⟨T, hT, B, hB, s, a, phi, hphi, hb, ha,
    limitField_finite_order_bound m s phi a ha B hb⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeHigherGalerkinWindow

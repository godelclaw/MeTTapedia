import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinCoefficientLimit

/-!
# Physical constraints and Sobolev energy of the coefficient limit

The extracted coefficient field retains reality, transversality, zero
mean, and its nonzero initial coefficients. Its weighted second-order
energy is summable and bounded, proved from finite partial sums.
These properties do not yet assert the nonlinear evolution equation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientLimitProperties

open scoped BigOperators ComplexConjugate Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeFrequencyProjectorCommutator PancakeLocalVelocityExistence
open PancakeGalerkinCoefficientLimit PancakeSobolevWeights PancakeSobolevVelocityRate

def limitField {T : ℝ} (a : CoefficientLimit T) (t : Set.Icc (0 : ℝ) T) : FourierVelocity :=
  fun q i ↦ a q i t

def IsCoefficientLimit {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) : Prop :=
  ∀ q i, TendstoUniformly
    (fun n (t : Set.Icc (0 : ℝ) T) ↦ (s (phi n)).coefficients t q i) (a q i) atTop

variable {nu T : ℝ} {u₀ : FourierVelocity}
  (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
  (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)

include h

theorem tendsto_limitField (t : Set.Icc (0 : ℝ) T) :
    Tendsto (fun n ↦ (s (phi n)).coefficients t) atTop (𝓝 (limitField a t)) :=
  tendsto_pi_nhds.mpr (fun q ↦ tendsto_pi_nhds.mpr (fun i ↦ (h q i).tendsto_at t))

theorem limitField_reality (t : Set.Icc (0 : ℝ) T) (q : Wavevector) :
    limitField a t (-q) = coefficientConjugate (limitField a t q) := by
  ext i
  have hn := (h (-q) i).tendsto_at t
  have hc := Complex.continuous_conj.tendsto (a q i t) |>.comp ((h q i).tendsto_at t)
  have he (n : ℕ) : (s (phi n)).coefficients t (-q) i =
      conj ((s (phi n)).coefficients t q i) := congrFun ((s (phi n)).reality t q) i
  exact tendsto_nhds_unique hn (hc.congr' (Eventually.of_forall (fun n ↦ (he n).symm)))

theorem limitField_transverse (t : Set.Icc (0 : ℝ) T) (q : Wavevector) :
    modeDot q (limitField a t q) = 0 := by
  have hc : Continuous (fun u : FourierVelocity ↦ modeDot q (u q)) := by
    unfold modeDot
    fun_prop
  have hn := (hc.tendsto (limitField a t)).comp (tendsto_limitField s phi a h t)
  have he (n : ℕ) : modeDot q ((s (phi n)).coefficients t q) = 0 := by
    by_cases hq : q ∈ galerkinModes (phi n)
    · exact (s (phi n)).transverse t q hq
    · rw [(s (phi n)).support t q hq]
      simp [modeDot]
  exact tendsto_nhds_unique hn
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n ↦ (he n).symm)))

theorem limitField_zero (t : Set.Icc (0 : ℝ) T) : limitField a t 0 = 0 := by
  ext i
  have hn := (h 0 i).tendsto_at t
  have he (n : ℕ) : (s (phi n)).coefficients t 0 i = 0 := by
    rw [(s (phi n)).support t 0 (by simp [galerkinModes])]
    rfl
  exact tendsto_nhds_unique hn
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n ↦ (he n).symm)))

theorem limitField_initial_nonzero (hphi : StrictMono phi) (hT : 0 ≤ T)
    (q : Wavevector) (hq : q ≠ 0) : limitField a ⟨0, le_rfl, hT⟩ q = u₀ q := by
  ext i
  have hn := (h q i).tendsto_at ⟨0, le_rfl, hT⟩
  have he : ∀ᶠ n in atTop, (s (phi n)).coefficients 0 q i = u₀ q i := by
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_mem_galerkinModes q hq)] with n hn
    exact congrFun ((s (phi n)).initial q hn) i
  exact tendsto_nhds_unique hn
    (tendsto_const_nhds.congr' (Filter.Eventually.mono he (fun _ hi ↦ hi.symm)))

theorem limitField_initial (hphi : StrictMono phi) (hT : 0 ≤ T) (hzero : u₀ 0 = 0) :
    limitField a ⟨0, le_rfl, hT⟩ = u₀ := by
  funext q
  by_cases hq : q = 0
  · subst q
    exact (limitField_zero s phi a h _).trans hzero.symm
  · exact limitField_initial_nonzero s phi a h hphi hT q hq

omit h in
theorem sobolevEnergy_of_support_le (M F : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ M → u q = 0) : sobolevEnergy F u ≤ sobolevEnergy M u := by
  rw [sobolevEnergy_eq, sobolevEnergy_eq]
  have he : (∑ q ∈ F ∩ M, weight q ^ 2 * coefficientEnergy (u q)) =
      ∑ q ∈ F, weight q ^ 2 * coefficientEnergy (u q) := by
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

omit h in
theorem continuous_sobolevEnergy (F : Finset Wavevector) :
    Continuous (sobolevEnergy F) := by
  change Continuous (fun u : FourierVelocity ↦ sobolevEnergy F u)
  simp only [sobolevEnergy_eq, coefficientEnergy]
  fun_prop

theorem limitField_finite_sobolev_bound (B : ℝ)
    (hB : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (t : Set.Icc (0 : ℝ) T) (F : Finset Wavevector) :
    sobolevEnergy F (limitField a t) ≤ B := by
  have hn := ((continuous_sobolevEnergy F).tendsto (limitField a t)).comp
    (tendsto_limitField s phi a h t)
  apply le_of_tendsto hn
  exact Eventually.of_forall (fun n ↦
    (sobolevEnergy_of_support_le _ F _ ((s (phi n)).support t)).trans (hB (phi n) t t.2))

/-- The infinite weighted energy is an actual summable series, bounded by
the common finite energy allowance. -/
theorem limitField_summable_sobolev (B : ℝ)
    (hB : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (t : Set.Icc (0 : ℝ) T) :
    Summable (fun q ↦ (weight q * amplitude (limitField a t) q)^2) ∧
      (∑' q, (weight q * amplitude (limitField a t) q)^2) ≤ B := by
  have hb (F : Finset Wavevector) :
      (∑ q ∈ F, (weight q * amplitude (limitField a t) q)^2) ≤ B :=
    limitField_finite_sobolev_bound s phi a h B hB t F
  exact ⟨summable_of_sum_le (fun _ ↦ sq_nonneg _) hb,
    Real.tsum_le_of_sum_le (fun _ ↦ sq_nonneg _) hb⟩

end Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientLimitProperties

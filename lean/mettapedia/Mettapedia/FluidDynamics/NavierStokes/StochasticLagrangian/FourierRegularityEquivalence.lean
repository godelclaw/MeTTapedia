import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSmallData

/-!
# The open input is exactly periodic regularity

For admissible data of order `m ≥ 7`, each finite-horizon bound consumed by
the continuation theorems holds if and only if the data have a global
solution:

* `nonempty_globalSolution_iff_vorticitySup`: the time integral of the
  vorticity supremum;
* `nonempty_globalSolution_iff_highBlockSum`: the time integral of the
  high-block sum `D_Q`;
* `nonempty_globalSolution_iff_meanEnergy`: the eighth vorticity moment.

The forward direction uses uniqueness: every tame solution is a restriction of
the global one, whose integrands are continuous and hence bounded on each
finite horizon. The remaining hypothesis of the lane's conditional route is
therefore neither weaker nor stronger than global regularity of the data.
`PeriodicRegularity m` states that regularity for all admissible data; it is
a definition, not an assumption, and it is open.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierRegularityEquivalence

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeHigherSobolevVelocityRate
open PancakeCurlOutputTail PancakeLocalInfiniteVelocity PancakeBlockReality
open PancakeHigherDerivativeMoments
open FourierTameContinuation FourierVorticitySupContinuation FourierDyadicBlockContinuation
open FourierUniqueness FourierGlobalSolution
open LocalVorticityEighthMoment (meanEnergy)

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- Every tame solution is a restriction of the global solution. -/
theorem TameSolutionOn.coefficients_eq_global (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) {T : ℝ} (c : TameSolutionOn nu m u₀ T) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : c.coefficients t = g.coefficients t :=
  coefficients_eq_of_lt hm hnu c (g.toTame T) ht.1 ht.2 ht.2

/-- Along a global solution, a continuous integrand is bounded on `[0, H]`. -/
theorem exists_bound_on (f : ℝ → ℝ) {H : ℝ} (hf : ContinuousOn f (Icc 0 H)) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) H, f t ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨max C 0, le_max_right _ _, fun t ht ↦
    (le_abs_self _).trans ((Real.norm_eq_abs (f t) ▸ hC t ht).trans (le_max_left _ _))⟩

/-- A global solution has a local envelope on every finite horizon. -/
theorem GlobalSolution.local_envelope (hm : 7 ≤ m) (g : GlobalSolution nu m u₀) (H : ℝ) :
    ∃ B, ∃ s : LocalInfiniteVelocitySolution nu u₀ H B, s.coefficients = g.coefficients ∧
      ∃ e : Wavevector → ℝ, (∀ k, 0 ≤ e k) ∧ Summable e ∧
        ∀ t ∈ Icc (0 : ℝ) H, ∀ k, fourierMoment 3 (s.coefficients t) k ≤ e k :=
  local_envelope_at hm (g.toTame (H + 1)) (by linarith)

/-- The integral bound follows from a bound on the integrand along the global
solution. -/
theorem integral_bound_of_global (hm : 7 ≤ m) (hnu : 0 < nu) (g : GlobalSolution nu m u₀)
    (φ : FourierVelocity → ℝ) (H : ℝ) (hc : ContinuousOn (fun t ↦ φ (g.coefficients t)) (Icc 0 H)) :
    ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, φ (c.coefficients t) ≤ A := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on _ hc
  refine ⟨H * M, fun T hT c τ hτ ↦ ?_⟩
  have hτH : τ ≤ H := hτ.2.le.trans hT
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 H := Icc_subset_Icc le_rfl hτH
  have hcongr : (∫ t in (0 : ℝ)..τ, φ (c.coefficients t)) =
      ∫ t in (0 : ℝ)..τ, φ (g.coefficients t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hτ.1] at ht
    rw [TameSolutionOn.coefficients_eq_global hm hnu g c ⟨ht.1, ht.2.trans_lt hτ.2⟩]
  rw [hcongr]
  calc ∫ t in (0 : ℝ)..τ, φ (g.coefficients t) ≤ ∫ _t in (0 : ℝ)..τ, M :=
        intervalIntegral.integral_mono_on hτ.1 ((hc.mono hsub).intervalIntegrable_of_Icc hτ.1)
          intervalIntegrable_const fun t ht ↦ hM t (hsub ht)
    _ = τ * M := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ H * M := mul_le_mul_of_nonneg_right hτH hM0

section Equivalences

variable (hm : 7 ≤ m) (hnu : 0 < nu) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
  (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
  (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
include hm hnu hr hd hz hE₀0 hE₀

/-- **Global solution ⟺ bounded `∫ ‖ω‖_∞` on every finite horizon.** -/
theorem nonempty_globalSolution_iff_vorticitySup :
    Nonempty (GlobalSolution nu m u₀) ↔
      ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) ≤ A := by
  refine ⟨fun ⟨g⟩ H _ ↦ ?_,
    nonempty_globalSolution_of_vorticitySup hm hnu hr hd hz hE₀0 hE₀⟩
  obtain ⟨B, s, hs, e, _, hSum, hu⟩ := GlobalSolution.local_envelope hm g H
  have hu2 : ∀ t ∈ Icc (0 : ℝ) H, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ e k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu t ht k)
  have hc := continuousOn_vorticitySup s e hSum hu2
  rw [hs] at hc
  exact integral_bound_of_global hm hnu g vorticitySup H hc

/-- **Global solution ⟺ bounded `∫ D_Q` on every finite horizon.** -/
theorem nonempty_globalSolution_iff_highBlockSum (Q : ℕ) :
    Nonempty (GlobalSolution nu m u₀) ↔
      ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, highBlockSum Q (c.coefficients t) ≤ A := by
  refine ⟨fun ⟨g⟩ H _ ↦ ?_,
    nonempty_globalSolution_of_highBlockSum hm hnu hr hd hz hE₀0 hE₀ Q⟩
  obtain ⟨B, s, hs, e, he, hSum, hu⟩ := GlobalSolution.local_envelope hm g H
  have hu1 : ∀ t ∈ Icc (0 : ℝ) H, ∀ k, fourierMoment 1 (s.coefficients t) k ≤ e k :=
    fun t ht k ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) k).trans (hu t ht k)
  have hc := continuousOn_highBlockSum s Q e he hSum hu1
  rw [hs] at hc
  exact integral_bound_of_global hm hnu g (highBlockSum Q) H hc

/-- **Global solution ⟺ bounded eighth moment on every finite horizon.** -/
theorem nonempty_globalSolution_iff_meanEnergy :
    Nonempty (GlobalSolution nu m u₀) ↔
      ∀ H, 0 < H → ∃ K₈, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, meanEnergy (c.coefficients τ) ≤ K₈ := by
  refine ⟨fun ⟨g⟩ H _ ↦ ?_,
    nonempty_globalSolution_of_meanEnergy hm hnu hr hd hz hE₀0 hE₀⟩
  obtain ⟨B, s, hs, e, _, hSum, hu⟩ := GlobalSolution.local_envelope hm g H
  have hc := LocalVorticityEighthMoment.continuousOn_meanEnergy s e hSum hu
  rw [hs] at hc
  obtain ⟨M, _, hM⟩ := exists_bound_on _ hc
  refine ⟨M, fun T hT c τ hτ ↦ ?_⟩
  rw [TameSolutionOn.coefficients_eq_global hm hnu g c hτ]
  exact hM τ ⟨hτ.1, hτ.2.le.trans hT⟩

end Equivalences

/-- Admissible data of order `m`: real, transverse, mean-zero Fourier data of
finite order-`m` energy. -/
def Admissible (m : ℕ) (u₀ : FourierVelocity) : Prop :=
  (∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) ∧ (∀ q, modeDot q (u₀ q) = 0) ∧ u₀ 0 = 0 ∧
    ∃ E₀, ∀ F, velocityEnergy m F u₀ ≤ E₀

/-- **OPEN.** Global regularity of the periodic problem in the Fourier class of
order `m`: every admissible datum has a global solution, for every positive
viscosity. This is a definition, not an assumption. -/
def PeriodicRegularity (m : ℕ) : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ → Nonempty (GlobalSolution nu m u₀)

/-- The open regularity statement is exactly the finite-horizon bound on
`∫ ‖ω‖_∞` for all admissible data. -/
theorem periodicRegularity_iff_vorticitySup (hm : 7 ≤ m) :
    PeriodicRegularity m ↔ ∀ nu : ℝ, 0 < nu → ∀ u₀ : FourierVelocity, Admissible m u₀ →
      ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
        ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) ≤ A := by
  refine forall₂_congr fun nu hnu ↦ forall₂_congr fun u₀ hu ↦ ?_
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  exact nonempty_globalSolution_iff_vorticitySup hm hnu hr hd hz hE₀0 hE₀

/-- Small admissible data are regular, unconditionally. -/
theorem admissible_small_regular (m : ℕ) (hm : 5 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    {u₀ : FourierVelocity} (hu : Admissible (m + 2) u₀)
    (hsmall : ∀ F, velocityEnergy m F u₀ ≤ FourierSmallData.smallRadius m nu ^ 2 / 8) :
    Nonempty (GlobalSolution nu (m + 2) u₀) := by
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  exact FourierSmallData.nonempty_globalSolution_of_small m hm hnu u₀ hr hd hz hE₀0 hE₀ hsmall

end Mettapedia.FluidDynamics.NavierStokes.FourierRegularityEquivalence

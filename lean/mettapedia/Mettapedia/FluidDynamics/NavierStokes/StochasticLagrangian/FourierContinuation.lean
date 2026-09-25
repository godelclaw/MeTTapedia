import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeHigherLocalVelocity
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Continuation of the Fourier velocity solutions

The Galerkin-limit solutions have an explicit lifespan `window m ν B₀` that
depends only on a bound `B₀` for the order-`m` velocity energy of their data.
Each limit curve also has, at its initial time, the one-sided derivative
prescribed by the equation: the actual right-hand side is a continuous path
on the closed interval, so the endpoint derivative follows from the interior
equation.

Consequently a solution on `[0, T)` whose order-`m` energy stays below `M`
extends. Restarting at `max 0 (T - δ/2)`, with `δ = window m ν M`, and gluing
at that single time gives a solution on `[0, T + δ/2)`. The glued solution
agrees with the original one up to the restart time. No uniqueness theorem is
used. Bounding the order-`m` energy up to a candidate singular time is not
supplied here; that remains the analytic obligation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierContinuation

open scoped BigOperators Topology ComplexConjugate
open Filter Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeBlockReality PancakeArbitraryDataBlocks
open PancakeLocalVelocityExistence PancakeFiniteVelocityContinuation
open PancakeSobolevWeights PancakeSobolevVelocityRate
open PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate PancakeHigherSobolevWindow
open PancakeQuadraticGrowthWindow PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeVelocityPathLimit PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity
open PancakeHigherGalerkinWindow PancakeHigherLocalVelocity
open PancakeContinuousCoordinateJet PancakePhysicalFieldReconstruction PancakeCurlOutputTail

/-- The explicit lifespan attached to an order-`m` energy bound. -/
abbrev window (m : ℕ) (nu B : ℝ) : ℝ := timeWindow (orderGrowthConstant m nu) B

theorem window_pos (m : ℕ) {nu B : ℝ} (hnu : 0 < nu) (hB : 0 ≤ B) :
    0 < window m nu B :=
  timeWindow_pos _ _ (orderGrowthConstant_nonneg m nu hnu) hB

/-! ### Galerkin solutions on the explicit window -/

theorem exists_window_order_solution (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M u₀ ≤ B₀)
    (M : Finset Wavevector) (hs : ∀ q, -q ∈ M ↔ q ∈ M)
    (hk : ∀ q ∈ M, frequencyVec q ≠ 0) :
    ∃ s : LocalVelocitySolution M nu u₀ (window m nu B₀),
      ∀ t ∈ Icc (0 : ℝ) (window m nu B₀),
        velocityEnergy m M (s.coefficients t) ≤ 2 * (B₀ + 1) := by
  obtain ⟨s⟩ := exists_finiteHorizon_velocitySolution M nu hnu.le u₀ hs hk hr
    (fun q _ ↦ hd q) (window m nu B₀) (window_pos m hnu hB₀).le
  exact ⟨s, fun t ht ↦ localSolution_order_bound m hm s hnu hk B₀ hB₀ (hE₀ M) t ht ht.2⟩

theorem exists_window_limit (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M u₀ ≤ B₀) :
    ∃ s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ (window m nu B₀),
    ∃ a : CoefficientLimit (window m nu B₀), ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ n t, t ∈ Icc (0 : ℝ) (window m nu B₀) →
        velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ 2 * (B₀ + 1)) ∧
      IsCoefficientLimit s phi a := by
  choose s hb using fun n ↦ exists_window_order_solution m hm hnu u₀ hr hd hB₀ hE₀
    (galerkinModes n) (galerkinModes_symmetric n) (galerkinModes_nonzero n)
  obtain ⟨a, phi, hphi, ha⟩ := exists_coefficient_subsequence galerkinModes s
    galerkinModes_nonzero (2 * (B₀ + 1)) (by positivity) (fun n t ht ↦
      (fullEnergy_le_sobolevEnergy _ _).trans
        ((sobolevEnergy_le_velocityEnergy m hm _ _).trans (hb n t ht)))
  exact ⟨s, a, phi, hphi, hb, ha⟩

/-! ### The equation at the initial time -/

/-- The limit curve has the derivative prescribed by the equation from the
right at its initial time. -/
theorem coefficientCurve_hasDerivWithinAt_zero {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (hphi : StrictMono phi) (hT : 0 < T) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) :
    HasDerivWithinAt (fun τ ↦ coefficientCurve a hT.le τ q i)
      (infiniteVelocityRHS nu (coefficientCurve a hT.le 0) q i) (Ici 0) 0 := by
  have hLim := limitField_finite_sobolev_bound s phi a h B hE
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) T, HasDerivAt (fun τ ↦ coefficientCurve a hT.le τ q i)
      (Set.IccExtend hT.le (velocityPath nu q a i) x) x := by
    intro x hx
    have hd := coefficientLimit_hasDerivAt s phi a h hphi hT.le B hB hE q i x hx
    rw [Set.IccExtend_of_mem hT.le _ ⟨hx.1.le, hx.2.le⟩,
      velocityPath_apply nu q a B hB hLim,
      ← coefficientCurve_apply a hT.le x ⟨hx.1.le, hx.2.le⟩]
    exact hd
  have hcont : Continuous (Set.IccExtend hT.le (velocityPath nu q a i)) :=
    (velocityPath nu q a i).continuous.Icc_extend'
  have hval : Set.IccExtend hT.le (velocityPath nu q a i) 0 =
      infiniteVelocityRHS nu (coefficientCurve a hT.le 0) q i := by
    rw [Set.IccExtend_of_mem hT.le _ ⟨le_rfl, hT.le⟩,
      velocityPath_apply nu q a B hB hLim,
      coefficientCurve_apply a hT.le 0 ⟨le_rfl, hT.le⟩]
  rw [← hval]
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 T)
    (fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt)
    (continuous_coefficientCurve a hT.le q i).continuousWithinAt
    (Ioo_mem_nhdsGT hT) ?_
  have hlim : Tendsto (Set.IccExtend hT.le (velocityPath nu q a i)) (𝓝[>] 0)
      (𝓝 (Set.IccExtend hT.le (velocityPath nu q a i) 0)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hT] with x hx
  exact (hderiv x hx).deriv.symm

/-- **Restart.** Admissible Fourier data with order-`m` energy at most `B₀`
start a solution on the explicit window, with the energy bound `2(B₀+1)`,
the equation at interior times, and the one-sided equation at time zero. -/
theorem exists_restart (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M u₀ ≤ B₀) :
    ∃ c : ℝ → FourierVelocity,
      (∀ q i, Continuous (fun t ↦ c t q i)) ∧ c 0 = u₀ ∧
      (∀ t q, c t (-q) = coefficientConjugate (c t q)) ∧
      (∀ t q, modeDot q (c t q) = 0) ∧ (∀ t, c t 0 = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) (window m nu B₀), ∀ F,
        velocityEnergy m F (c t) ≤ 2 * (B₀ + 1)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (window m nu B₀), ∀ q i,
        HasDerivAt (fun τ ↦ c τ q i) (infiniteVelocityRHS nu (c t) q i) t) ∧
      (∀ q i, HasDerivWithinAt (fun τ ↦ c τ q i)
        (infiniteVelocityRHS nu (c 0) q i) (Ici 0) 0) := by
  obtain ⟨s, a, phi, hphi, hb, ha⟩ := exists_window_limit m hm hnu u₀ hr hd hB₀ hE₀
  have hT := window_pos m hnu hB₀
  have hB : (0 : ℝ) ≤ 2 * (B₀ + 1) := by positivity
  let sol := localInfiniteVelocitySolutionOfOrder m hm s phi a ha hphi hT.le hz
    (2 * (B₀ + 1)) hB hb
  have hE₂ : ∀ n t, t ∈ Icc (0 : ℝ) (window m nu B₀) →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ 2 * (B₀ + 1) :=
    fun n t ht ↦ (sobolevEnergy_le_velocityEnergy m hm _ _).trans (hb n t ht)
  refine ⟨sol.coefficients, sol.continuous, sol.initial, sol.reality, sol.transverse,
    sol.zero, fun t ht F ↦ localInfiniteVelocitySolutionOfOrder_bound m hm s phi a ha hphi
      hT.le hz (2 * (B₀ + 1)) hB hb t ht F, sol.equation, fun q i ↦ ?_⟩
  exact coefficientCurve_hasDerivWithinAt_zero s phi a ha hphi hT (2 * (B₀ + 1)) hB hE₂ q i

/-! ### Gluing at one time -/

theorem glue_hasDerivAt {f g : ℝ → ℂ} {t₁ : ℝ} {e : ℂ}
    (hf : HasDerivAt f e t₁) (hg : HasDerivWithinAt g e (Ici 0) 0) (h0 : g 0 = f t₁) :
    HasDerivAt (fun t ↦ if t ≤ t₁ then f t else g (t - t₁)) e t₁ := by
  have hleft : HasDerivWithinAt (fun t ↦ if t ≤ t₁ then f t else g (t - t₁)) e
      (Iic t₁) t₁ :=
    hf.hasDerivWithinAt.congr (fun x hx ↦ by simp [show x ≤ t₁ from hx]) (by simp)
  have hshift : HasDerivWithinAt (fun t ↦ g (t - t₁)) e (Ici t₁) t₁ := by
    have hin : HasDerivWithinAt (fun t : ℝ ↦ t - t₁) 1 (Ici t₁) t₁ :=
      ((hasDerivAt_id t₁).sub_const t₁).hasDerivWithinAt
    have hg' : HasDerivWithinAt g e (Ici 0) (t₁ - t₁) := by simpa using hg
    have := HasDerivWithinAt.scomp (h := fun t : ℝ ↦ t - t₁) t₁ hg' hin
      (fun x (hx : x ∈ Ici t₁) ↦ mem_Ici.mpr (sub_nonneg.mpr (mem_Ici.mp hx)))
    simpa [Function.comp_def] using this
  have hright : HasDerivWithinAt (fun t ↦ if t ≤ t₁ then f t else g (t - t₁)) e
      (Ici t₁) t₁ := by
    refine hshift.congr (fun x hx ↦ ?_) (by simp [h0])
    rcases eq_or_lt_of_le (show t₁ ≤ x from hx) with h | h
    · subst h
      simp [h0]
    · simp [not_le.mpr h]
  have := hleft.union hright
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-! ### Solutions on half-open intervals and their continuation -/

/-- A Fourier velocity solution on `[0, T)`: continuous coefficients, the
constraints at every time, local Sobolev bounds before `T`, and the infinite
equation at every interior time. -/
structure SolutionOn (nu : ℝ) (u₀ : FourierVelocity) (T : ℝ) where
  coefficients : ℝ → FourierVelocity
  continuous : ∀ q i, Continuous (fun t ↦ coefficients t q i)
  initial : coefficients 0 = u₀
  reality : ∀ t q, coefficients t (-q) = coefficientConjugate (coefficients t q)
  transverse : ∀ t q, modeDot q (coefficients t q) = 0
  zero : ∀ t, coefficients t 0 = 0
  sobolev_local : ∀ S < T, ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
    sobolevEnergy F (coefficients t) ≤ B
  equation : ∀ t ∈ Ioo (0 : ℝ) T, ∀ q i,
    HasDerivAt (fun τ ↦ coefficients τ q i) (infiniteVelocityRHS nu (coefficients t) q i) t

/-- Every closed-interval local solution restricts to a half-open one. -/
def _root_.Mettapedia.FluidDynamics.NavierStokes.PancakeLocalInfiniteVelocity.LocalInfiniteVelocitySolution.toSolutionOn
    {nu T B : ℝ} {u₀ : FourierVelocity} (s : LocalInfiniteVelocitySolution nu u₀ T B) :
    SolutionOn nu u₀ T where
  coefficients := s.coefficients
  continuous := s.continuous
  initial := s.initial
  reality := s.reality
  transverse := s.transverse
  zero := s.zero
  sobolev_local := fun _ hS ↦ ⟨B, fun t ht F ↦ s.sobolev_bound t ⟨ht.1, ht.2.trans hS.le⟩ F⟩
  equation := s.equation

/-- A restarted curve on `[0, δ)`: the constraints, a Sobolev bound on
`[0, δ]`, the equation at interior times, and the one-sided equation at
time zero. -/
structure RestartData (nu : ℝ) (v : FourierVelocity) (δ : ℝ) where
  curve : ℝ → FourierVelocity
  continuous : ∀ q i, Continuous (fun t ↦ curve t q i)
  initial : curve 0 = v
  reality : ∀ t q, curve t (-q) = coefficientConjugate (curve t q)
  transverse : ∀ t q, modeDot q (curve t q) = 0
  zero : ∀ t, curve t 0 = 0
  sobolev : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) δ, ∀ F : Finset Wavevector,
    sobolevEnergy F (curve t) ≤ B
  equation : ∀ t ∈ Ioo (0 : ℝ) δ, ∀ q i,
    HasDerivAt (fun τ ↦ curve τ q i) (infiniteVelocityRHS nu (curve t) q i) t
  start : ∀ q i, HasDerivWithinAt (fun τ ↦ curve τ q i)
    (infiniteVelocityRHS nu (curve 0) q i) (Ici 0) 0

/-- **Gluing.** A restart at `t₁ < T` of a solution on `[0, T)` gives a
solution on `[0, T')` for every `T' ≤ t₁ + δ`; its coefficients are the old
ones up to `t₁` and the restarted ones afterwards. -/
def SolutionOn.glue {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ} (c : SolutionOn nu u₀ T)
    {t₁ δ T' : ℝ} (ht₁0 : 0 ≤ t₁) (ht₁T : t₁ < T)
    (d : RestartData nu (c.coefficients t₁) δ) (hT' : T' ≤ t₁ + δ) :
    SolutionOn nu u₀ T' where
  coefficients := fun t ↦ if t ≤ t₁ then c.coefficients t else d.curve (t - t₁)
  continuous := fun q i ↦ by
    have hc : Continuous (fun t ↦ if t ≤ t₁ then c.coefficients t q i else d.curve (t - t₁) q i) :=
      Continuous.if_le (c.continuous q i)
        ((d.continuous q i).comp (continuous_id.sub continuous_const)) continuous_id
        continuous_const (fun x hx ↦ by
          have hx' : x = t₁ := hx
          subst hx'
          simp [d.initial])
    refine hc.congr fun t ↦ ?_
    by_cases h : t ≤ t₁ <;> simp [h]
  initial := by simp [ht₁0, c.initial]
  reality := fun t q ↦ by
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      exact c.reality t q
    · simp only [h, ↓reduceIte]
      exact d.reality (t - t₁) q
  transverse := fun t q ↦ by
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      exact c.transverse t q
    · simp only [h, ↓reduceIte]
      exact d.transverse (t - t₁) q
  zero := fun t ↦ by
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      exact c.zero t
    · simp only [h, ↓reduceIte]
      exact d.zero (t - t₁)
  sobolev_local := fun S hS ↦ by
    obtain ⟨Bc, hBc⟩ := c.sobolev_local t₁ ht₁T
    obtain ⟨Bd, hBd⟩ := d.sobolev
    refine ⟨max Bc Bd, fun t ht F ↦ ?_⟩
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      exact (hBc t ⟨ht.1, h⟩ F).trans (le_max_left _ _)
    · simp only [h, ↓reduceIte]
      exact (hBd (t - t₁) ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩ F).trans
        (le_max_right _ _)
  equation := fun t ht q i ↦ by
    rcases lt_trichotomy t t₁ with h | h | h
    · have hev : (fun τ ↦ (if τ ≤ t₁ then c.coefficients τ else d.curve (τ - t₁)) q i) =ᶠ[𝓝 t]
          fun τ ↦ c.coefficients τ q i := by
        filter_upwards [Iio_mem_nhds h] with τ hτ
        simp [(show τ < t₁ from hτ).le]
      have hc := (c.equation t ⟨ht.1, lt_trans h ht₁T⟩ q i).congr_of_eventuallyEq hev
      simpa [le_of_lt h] using hc
    · rw [h] at ht ⊢
      have hfun : (fun τ ↦ (if τ ≤ t₁ then c.coefficients τ else d.curve (τ - t₁)) q i) =
          fun τ ↦ if τ ≤ t₁ then c.coefficients τ q i else d.curve (τ - t₁) q i := by
        funext τ
        by_cases h' : τ ≤ t₁ <;> simp [h']
      rw [hfun]
      have hg : HasDerivWithinAt (fun τ ↦ d.curve τ q i)
          (infiniteVelocityRHS nu (c.coefficients t₁) q i) (Ici 0) 0 := by
        simpa [d.initial] using d.start q i
      simpa using glue_hasDerivAt (c.equation t₁ ⟨ht.1, ht₁T⟩ q i) hg (by simp [d.initial])
    · have hev : (fun τ ↦ (if τ ≤ t₁ then c.coefficients τ else d.curve (τ - t₁)) q i) =ᶠ[𝓝 t]
          fun τ ↦ d.curve (τ - t₁) q i := by
        filter_upwards [Ioi_mem_nhds h] with τ hτ
        simp [not_le.mpr (show t₁ < τ from hτ)]
      have hd := (d.equation (t - t₁) ⟨by linarith, by linarith [ht.2]⟩ q i).comp_sub_const t t₁
      have hc := hd.congr_of_eventuallyEq hev
      simpa [not_le.mpr h] using hc

theorem SolutionOn.glue_coefficients {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}
    (c : SolutionOn nu u₀ T) {t₁ δ T' : ℝ} (ht₁0 : 0 ≤ t₁) (ht₁T : t₁ < T)
    (d : RestartData nu (c.coefficients t₁) δ) (hT' : T' ≤ t₁ + δ) (t : ℝ) :
    (c.glue ht₁0 ht₁T d hT').coefficients t =
      if t ≤ t₁ then c.coefficients t else d.curve (t - t₁) := rfl

/-- The restart of `exists_restart`, packaged, with its order-`m` bound. -/
theorem exists_restartData (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (v : FourierVelocity) (hr : ∀ q, v (-q) = coefficientConjugate (v q))
    (hd : ∀ q, modeDot q (v q) = 0) (hz : v 0 = 0) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M v ≤ B₀) :
    ∃ d : RestartData nu v (window m nu B₀),
      ∀ t ∈ Icc (0 : ℝ) (window m nu B₀), ∀ F,
        velocityEnergy m F (d.curve t) ≤ 2 * (B₀ + 1) := by
  obtain ⟨d, hdcont, hd0, hdre, hdtr, hdz, hdE, hdeq, hdend⟩ :=
    exists_restart m hm hnu v hr hd hz hB₀ hE₀
  let D : RestartData nu v (window m nu B₀) :=
    { curve := d
      continuous := hdcont
      initial := hd0
      reality := hdre
      transverse := hdtr
      zero := hdz
      sobolev := ⟨2 * (B₀ + 1), fun t ht F ↦
        (sobolevEnergy_le_velocityEnergy m hm F _).trans (hdE t ht F)⟩
      equation := hdeq
      start := hdend }
  exact ⟨D, hdE⟩

/-- **Continuation.** A solution on `[0, T)` whose order-`m` energy stays at
most `M` extends to `[0, T + δ/2)`, `δ = window m ν M`. The extension agrees
with the original solution up to `T - δ/2`, and its order-`m` energy stays at
most `2(M+1)`. -/
theorem SolutionOn.extend (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    {u₀ : FourierVelocity} {T : ℝ} (hT : 0 < T) (c : SolutionOn nu u₀ T)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients t) ≤ M) :
    ∃ c' : SolutionOn nu u₀ (T + window m nu M / 2),
      (∀ t ≤ T - window m nu M / 2, c'.coefficients t = c.coefficients t) ∧
      ∀ t ∈ Ico (0 : ℝ) (T + window m nu M / 2), ∀ F,
        velocityEnergy m F (c'.coefficients t) ≤ 2 * (M + 1) := by
  set δ := window m nu M with hδdef
  have hδ : 0 < δ := window_pos m hnu hM0
  set t₁ := max 0 (T - δ / 2) with ht₁def
  have ht₁0 : 0 ≤ t₁ := le_max_left _ _
  have ht₁T : t₁ < T := max_lt hT (by linarith)
  have ht₁end : T + δ / 2 ≤ t₁ + δ := by
    rcases le_total 0 (T - δ / 2) with h | h
    · rw [ht₁def, max_eq_right h]
      linarith
    · rw [ht₁def, max_eq_left h]
      linarith
  obtain ⟨d, hdE⟩ := exists_restartData m hm hnu (c.coefficients t₁) (c.reality t₁)
    (c.transverse t₁) (c.zero t₁) hM0 (hM t₁ ⟨ht₁0, ht₁T⟩)
  refine ⟨c.glue ht₁0 ht₁T d ht₁end, fun t ht ↦ ?_, fun t ht F ↦ ?_⟩
  · have hle : t ≤ t₁ := le_trans ht (le_max_right _ _)
    simp [SolutionOn.glue_coefficients, hle]
  · rw [SolutionOn.glue_coefficients]
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      linarith [hM t ⟨ht.1, lt_of_le_of_lt h ht₁T⟩ F]
    · simp only [h, ↓reduceIte]
      exact hdE (t - t₁) ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩ F

/-! ### Existence from admissible physical data and the blowup alternative -/

local notation "T3" => UnitAddTorus (Fin 3)

/-- Admissible physical data start a solution on a positive half-open interval. -/
theorem exists_solutionOn (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet (m + 2) (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ), ∃ c : SolutionOn nu (torusFourierVelocity f) T,
      ∀ t ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients t) ≤ B := by
  obtain ⟨T, hT, B, hB, s, hs⟩ :=
    exists_physical_higher_localVelocity m hm nu hnu f hf hr hd hzero
  exact ⟨T, hT, B, hB, s.toSolutionOn, fun t ht F ↦ hs t ⟨ht.1, ht.2.le⟩ F⟩

/-- **Blowup alternative.** If `Tmax` bounds every existence time, a solution on
`[0, T)` whose order-`m` energy stays at most `M` satisfies
`T + window m ν M / 2 ≤ Tmax`. -/
theorem SolutionOn.add_half_window_le_of_maximal (m : ℕ) (hm : 2 ≤ m) {nu : ℝ}
    (hnu : 0 < nu) {u₀ : FourierVelocity} {Tmax : ℝ}
    (hmax : ∀ S : ℝ, SolutionOn nu u₀ S → S ≤ Tmax)
    {T : ℝ} (hT : 0 < T) (c : SolutionOn nu u₀ T) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients t) ≤ M) :
    T + window m nu M / 2 ≤ Tmax := by
  obtain ⟨c', -, -⟩ := c.extend m hm hnu hT hM0 hM
  exact hmax _ c'

/-- **Blowup rate.** Under the same maximality, every energy bound `M` on
`[0, T)` satisfies `M + 1 ≥ 1 / (4 (C + 1) (Tmax - T))` with
`C = orderGrowthConstant m ν`. Hence the order-`m` energy of solutions
approaching a finite maximal time is unbounded, at least like
`1 / (Tmax - T)`. -/
theorem SolutionOn.orderEnergy_rate_of_maximal (m : ℕ) (hm : 2 ≤ m) {nu : ℝ}
    (hnu : 0 < nu) {u₀ : FourierVelocity} {Tmax : ℝ}
    (hmax : ∀ S : ℝ, SolutionOn nu u₀ S → S ≤ Tmax)
    {T : ℝ} (hT : 0 < T) (c : SolutionOn nu u₀ T) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients t) ≤ M) :
    1 / (4 * (orderGrowthConstant m nu + 1) * (Tmax - T)) ≤ M + 1 := by
  have hle := c.add_half_window_le_of_maximal m hm hnu hmax hT hM0 hM
  have hC : 0 ≤ orderGrowthConstant m nu := orderGrowthConstant_nonneg m nu hnu
  have hw : 0 < window m nu M := window_pos m hnu hM0
  have hgap : 0 < Tmax - T := by linarith
  have hwin : window m nu M = 1 / (2 * (orderGrowthConstant m nu + 1) * (M + 1)) := rfl
  rw [hwin] at hle
  have hpos : 0 < 2 * (orderGrowthConstant m nu + 1) * (M + 1) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have h2 : 1 / (2 * (orderGrowthConstant m nu + 1) * (M + 1)) ≤ 2 * (Tmax - T) := by
    linarith
  rw [div_le_iff₀ hpos] at h2
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.FourierContinuation

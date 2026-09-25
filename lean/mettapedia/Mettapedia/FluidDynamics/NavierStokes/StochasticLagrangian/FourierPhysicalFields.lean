import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTimeRegularity

/-!
# Smooth physical fields from smooth-rapid coefficient curves

For a coefficient curve `c`, the physical velocity at `x ∈ ℝ³` and time `t` is

```text
v(x, t) = Re ∑ₖ exp(2π i ⟨k, x⟩) c_k(t).
```

When `c` is smooth-rapid of every order on each interval `[0, S]`, every mode is
smooth in time with rapidly decaying iterated derivatives, the characters have
iterated derivatives of size `(6π (1 + |k|))ⁿ`, and the Leibniz rule gives a
summable bound for every term. Smoothness of series up to the boundary then
makes `v` smooth on `ℝ³ × [0, ∞)`, including the initial time, as the official
statement requires.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPhysicalFields

open scoped BigOperators Topology ContDiff
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeFourierMaterialPaths
open PancakeDyadicDirectionEvolution PancakePeriodicVorticityEquation PancakePeriodicComplexStretch
open FourierTimeRegularity Mettapedia.Analysis.SmoothSeriesClosure

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section Modes

variable {S : ℝ}

theorem hasDerivWithinAt_mode {a a' : ℝ → FourierVelocity} {s : Set ℝ} {t : ℝ}
    (h : ∀ k i, HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) s t) (k : Wavevector) :
    HasDerivWithinAt (fun τ ↦ a τ k) (a' t k) s t :=
  hasDerivWithinAt_pi.mpr fun i ↦ h k i

theorem norm_le_moment (u : FourierVelocity) (N : ℕ) (k : Wavevector) :
    (1 + ‖frequencyVec k‖) ^ N * ‖u k‖ ≤ fourierMoment N u k := by
  unfold fourierMoment
  exact mul_le_mul_of_nonneg_left
    (PancakeIndexedFourierMoments.norm_coefficient_sup_le_euclidean _) (by positivity)

/-- **Modewise smoothness and rapidly decaying iterated derivatives.** -/
theorem smoothRapid_modes (hS : 0 < S) : ∀ (j : ℕ) {a : ℝ → FourierVelocity},
    SmoothRapid j a (Icc 0 S) →
      (∀ k, ContDiffOn ℝ j (fun τ ↦ a τ k) (Icc 0 S)) ∧
      (∀ i ≤ j, ∀ N : ℕ, ∃ C, ∀ t ∈ Icc (0 : ℝ) S, ∀ k,
        (1 + ‖frequencyVec k‖) ^ N * ‖iteratedDerivWithin i (fun τ ↦ a τ k) (Icc 0 S) t‖ ≤ C)
  | 0, a, ha => by
    refine ⟨fun k ↦ ?_, fun i hi N ↦ ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      exact continuousOn_pi.mpr fun l ↦ ha.1 k l
    · have hi0 : i = 0 := by omega
      subst hi0
      obtain ⟨C, hC⟩ := ha.2 N
      exact ⟨C, fun t ht k ↦ by
        simpa only [iteratedDerivWithin_zero] using (norm_le_moment _ N k).trans (hC t ht k)⟩
  | j + 1, a, ha => by
    obtain ⟨hb, a', ha', hj⟩ := ha
    obtain ⟨hcd, hbd⟩ := smoothRapid_modes hS j hj
    have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) S) := uniqueDiffOn_Icc hS
    have hderiv : ∀ k, ∀ t ∈ Icc (0 : ℝ) S,
        derivWithin (fun τ ↦ a τ k) (Icc 0 S) t = a' t k :=
      fun k t ht ↦ (hasDerivWithinAt_mode (ha' t ht) k).derivWithin (hs t ht)
    refine ⟨fun k ↦ ?_, fun i hi N ↦ ?_⟩
    · have hcast : ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiffOn_succ_iff_derivWithin hs]
      refine ⟨fun t ht ↦ (hasDerivWithinAt_mode (ha' t ht) k).differentiableWithinAt,
        fun h ↦ by simp at h, ?_⟩
      exact (hcd k).congr fun t ht ↦ hderiv k t ht
    · rcases i with _ | i
      · obtain ⟨C, hC⟩ := hb.2 N
        exact ⟨C, fun t ht k ↦ by
          simpa only [iteratedDerivWithin_zero] using (norm_le_moment _ N k).trans (hC t ht k)⟩
      · obtain ⟨C, hC⟩ := hbd i (by omega) N
        refine ⟨C, fun t ht k ↦ ?_⟩
        rw [iteratedDerivWithin_succ',
          iteratedDerivWithin_congr (n := i) (fun τ hτ ↦ hderiv k τ hτ) ht]
        exact hC t ht k

theorem smoothRapid_contDiffOn (hS : 0 < S) {a : ℝ → FourierVelocity}
    (ha : ∀ j, SmoothRapid j a (Icc 0 S)) (k : Wavevector) :
    ContDiffOn ℝ ∞ (fun τ ↦ a τ k) (Icc 0 S) :=
  contDiffOn_infty.mpr fun j ↦ (smoothRapid_modes hS j (ha j)).1 k

theorem smoothRapid_derivBound (hS : 0 < S) {a : ℝ → FourierVelocity}
    (ha : ∀ j, SmoothRapid j a (Icc 0 S)) (i N : ℕ) :
    ∃ C, ∀ t ∈ Icc (0 : ℝ) S, ∀ k,
      (1 + ‖frequencyVec k‖) ^ N * ‖iteratedDerivWithin i (fun τ ↦ a τ k) (Icc 0 S) t‖ ≤ C :=
  (smoothRapid_modes hS i (ha i)).2 i le_rfl N

end Modes

section Characters

/-- The real linear functional `x ↦ ∑ᵢ kᵢ xᵢ` on `ℝ³`. -/
def modeFunctional (k : Wavevector) : ℝ³ →L[ℝ] ℝ :=
  ∑ i : Fin 3, (k i : ℝ) • (EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ)

theorem modeFunctional_apply (k : Wavevector) (x : ℝ³) :
    modeFunctional k x = realModeDot k (WithLp.ofLp x) := by
  simp [modeFunctional, realModeDot]

theorem abs_coord_le (k : Wavevector) (i : Fin 3) : |(k i : ℝ)| ≤ ‖frequencyVec k‖ := by
  have h := PiLp.norm_apply_le (frequencyVec k) i
  have e : ‖(frequencyVec k) i‖ = |(k i : ℝ)| := by
    simp [frequencyVec, coefficientVec, wavevectorCoefficient, Complex.norm_intCast]
  rw [e] at h
  exact h

theorem norm_modeFunctional_le (k : Wavevector) : ‖modeFunctional k‖ ≤ 3 * ‖frequencyVec k‖ := by
  unfold modeFunctional
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin 3, ‖(k i : ℝ) • (EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ)‖
      ≤ ∑ _i : Fin 3, ‖frequencyVec k‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul, Real.norm_eq_abs]
        have hp : ‖(EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
            simpa using PiLp.norm_apply_le x i
        calc |(k i : ℝ)| * ‖(EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ)‖ ≤ ‖frequencyVec k‖ * 1 :=
              mul_le_mul (abs_coord_le k i) hp (norm_nonneg _) (norm_nonneg _)
          _ = ‖frequencyVec k‖ := mul_one _
    _ = 3 * ‖frequencyVec k‖ := by simp

/-- The unit-speed phase `s ↦ exp(2π i s)`. -/
def phaseFun (s : ℝ) : ℂ := Complex.exp (unitTorusDerivativePhase * (s : ℂ))

theorem contDiff_phaseFun : ContDiff ℝ ∞ phaseFun :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

theorem norm_phaseFun (s : ℝ) : ‖phaseFun s‖ = 1 := by
  have h : unitTorusDerivativePhase * (s : ℂ) = ((2 * Real.pi * s : ℝ) : ℂ) * Complex.I := by
    simp [unitTorusDerivativePhase]
    ring
  rw [phaseFun, h]
  exact Complex.norm_exp_ofReal_mul_I _

theorem iteratedDeriv_phaseFun (n : ℕ) :
    iteratedDeriv n phaseFun = fun s ↦ unitTorusDerivativePhase ^ n * phaseFun s := by
  induction n with
  | zero => funext s; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h : HasDerivAt (fun s : ℝ ↦ unitTorusDerivativePhase ^ n * phaseFun s)
        (unitTorusDerivativePhase ^ n * (phaseFun s * (unitTorusDerivativePhase * 1))) s :=
      (((hasDerivAt_id s).ofReal_comp.const_mul unitTorusDerivativePhase).cexp).const_mul _
    rw [h.deriv]
    ring

theorem norm_iteratedFDeriv_phaseFun (n : ℕ) (s : ℝ) :
    ‖iteratedFDeriv ℝ n phaseFun s‖ = (2 * Real.pi) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_phaseFun, norm_mul, norm_pow,
    PancakeIncomingLowSourceEnergy.norm_derivativePhase, norm_phaseFun, mul_one]

/-- The Fourier character `x ↦ exp(2π i ⟨k, x⟩)` on `ℝ³`. -/
def character (k : Wavevector) (x : ℝ³) : ℂ := phaseFun (modeFunctional k x)

theorem contDiff_character (k : Wavevector) : ContDiff ℝ ∞ (character k) :=
  contDiff_phaseFun.comp (modeFunctional k).contDiff

theorem norm_character (k : Wavevector) (x : ℝ³) : ‖character k x‖ = 1 := norm_phaseFun _

theorem character_eq_mFourier (k : Wavevector) (x : ℝ³) :
    character k x = UnitAddTorus.mFourier k (torusPoint (WithLp.ofLp x)) := by
  rw [mFourier_torusPoint, character, phaseFun, modeFunctional_apply]

/-- **Derivative bounds for the characters.** -/
theorem norm_iteratedFDeriv_character_le (k : Wavevector) (n : ℕ) (x : ℝ³) :
    ‖iteratedFDeriv ℝ n (character k) x‖ ≤ (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n := by
  have he : character k = phaseFun ∘ (modeFunctional k) := rfl
  rw [he, (modeFunctional k).iteratedFDeriv_comp_right contDiff_phaseFun x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_phaseFun, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL := norm_modeFunctional_le k
  have hL' : ‖modeFunctional k‖ ≤ 3 * (1 + ‖frequencyVec k‖) := by linarith [norm_nonneg (frequencyVec k)]
  calc (2 * Real.pi) ^ n * ‖modeFunctional k‖ ^ n
      ≤ (2 * Real.pi) ^ n * (3 * (1 + ‖frequencyVec k‖)) ^ n := by gcongr
    _ = (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n := by rw [← mul_pow]; ring_nf

end Characters

section Velocity

variable {S : ℝ}

/-- The pointwise bilinear map `(z, w) ↦ Re (z • w)`. -/
def realSmul : ℂ →L[ℝ] VelocityCoefficient →L[ℝ] ℝ³ :=
  (ContinuousLinearMap.compL ℝ VelocityCoefficient VelocityCoefficient ℝ³
    complexRealPartEuclideanCLM).comp (ContinuousLinearMap.lsmul ℝ ℂ)

theorem realSmul_apply (z : ℂ) (w : VelocityCoefficient) :
    realSmul z w = complexRealPartEuclideanCLM (z • w) := rfl

/-- The physical velocity of a coefficient curve. -/
def physVelocity (c : ℝ → FourierVelocity) (x : ℝ³) (t : ℝ) : ℝ³ :=
  complexRealPartEuclideanCLM (∑' k, character k x • c t k)

/-- One term of the velocity series. -/
def velocityTerm (c : ℝ → FourierVelocity) (k : Wavevector) (p : ℝ³ × ℝ) : ℝ³ :=
  realSmul (character k p.1) (c p.2 k)

theorem closure_slab (hS : 0 < S) :
    closure (univ ×ˢ Ioo (0 : ℝ) S : Set (ℝ³ × ℝ)) = univ ×ˢ Icc 0 S := by
  rw [closure_prod_eq, closure_univ, closure_Ioo hS.ne]

theorem slab_eq_preimage : (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ)) =
    (ContinuousLinearMap.snd ℝ ℝ³ ℝ) ⁻¹' Icc 0 S := by
  ext p
  simp

theorem contDiffOn_mode_snd (hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) (k : Wavevector) :
    ContDiffOn ℝ ∞ (fun p : ℝ³ × ℝ ↦ c p.2 k) (univ ×ˢ Icc 0 S) := by
  rw [slab_eq_preimage]
  exact (smoothRapid_contDiffOn hS hc k).comp_continuousLinearMap _

theorem contDiffOn_velocityTerm (hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) (k : Wavevector) :
    ContDiffOn ℝ ∞ (velocityTerm c k) (univ ×ˢ Icc 0 S) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ³ × ℝ ↦ realSmul (character k p.1)) (univ ×ˢ Icc 0 S) :=
    (realSmul.contDiff.comp ((contDiff_character k).comp contDiff_fst)).contDiffOn
  exact h1.clm_apply (contDiffOn_mode_snd hS hc k)

theorem norm_iteratedFDerivWithin_character_fst_le (hS : 0 < S) (k : Wavevector) (n : ℕ)
    {p : ℝ³ × ℝ} (hp : p ∈ (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ))) :
    ‖iteratedFDerivWithin ℝ n (fun q : ℝ³ × ℝ ↦ character k q.1) (univ ×ˢ Icc 0 S) p‖ ≤
      (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n := by
  have hs : UniqueDiffOn ℝ (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ)) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hS)
  have hcd : ContDiff ℝ ∞ (fun q : ℝ³ × ℝ ↦ character k q.1) :=
    (contDiff_character k).comp contDiff_fst
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs (hcd.contDiffAt.of_le (by simp)) hp]
  have he : (fun q : ℝ³ × ℝ ↦ character k q.1) =
      character k ∘ (ContinuousLinearMap.fst ℝ ℝ³ ℝ) := rfl
  rw [he, (ContinuousLinearMap.fst ℝ ℝ³ ℝ).iteratedFDeriv_comp_right (contDiff_character k) p
    (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfst : ‖(ContinuousLinearMap.fst ℝ ℝ³ ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  calc ‖iteratedFDeriv ℝ n (character k) ((ContinuousLinearMap.fst ℝ ℝ³ ℝ) p)‖ *
        ‖(ContinuousLinearMap.fst ℝ ℝ³ ℝ)‖ ^ n
      ≤ (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ n * 1 ^ n :=
        mul_le_mul (norm_iteratedFDeriv_character_le k n _)
          (pow_le_pow_left₀ (norm_nonneg _) hfst n) (by positivity) (by positivity)
    _ = _ := by rw [one_pow, mul_one]

theorem norm_iteratedFDerivWithin_mode_snd_le (hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) (k : Wavevector) (n : ℕ)
    {p : ℝ³ × ℝ} (hp : p ∈ (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ))) :
    ‖iteratedFDerivWithin ℝ n (fun q : ℝ³ × ℝ ↦ c q.2 k) (univ ×ˢ Icc 0 S) p‖ ≤
      ‖iteratedDerivWithin n (fun τ ↦ c τ k) (Icc 0 S) p.2‖ := by
  have hsI : UniqueDiffOn ℝ (Icc (0 : ℝ) S) := uniqueDiffOn_Icc hS
  have hs : UniqueDiffOn ℝ ((ContinuousLinearMap.snd ℝ ℝ³ ℝ) ⁻¹' Icc (0 : ℝ) S) := by
    rw [← slab_eq_preimage]
    exact uniqueDiffOn_univ.prod hsI
  have hp' : (ContinuousLinearMap.snd ℝ ℝ³ ℝ) p ∈ Icc (0 : ℝ) S := hp.2
  have he : (fun q : ℝ³ × ℝ ↦ c q.2 k) = (fun τ ↦ c τ k) ∘ (ContinuousLinearMap.snd ℝ ℝ³ ℝ) := rfl
  rw [slab_eq_preimage, he, (ContinuousLinearMap.snd ℝ ℝ³ ℝ).iteratedFDerivWithin_comp_right
    (smoothRapid_contDiffOn hS hc k) hsI hs hp' (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  have hsnd : ‖(ContinuousLinearMap.snd ℝ ℝ³ ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le _ _ _
  calc ‖iteratedDerivWithin n (fun τ ↦ c τ k) (Icc 0 S) ((ContinuousLinearMap.snd ℝ ℝ³ ℝ) p)‖ *
        ‖(ContinuousLinearMap.snd ℝ ℝ³ ℝ)‖ ^ n
      ≤ ‖iteratedDerivWithin n (fun τ ↦ c τ k) (Icc 0 S) p.2‖ * 1 ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsnd n) (norm_nonneg _)
    _ = _ := by rw [one_pow, mul_one]

/-- **Summable bounds for the velocity terms.** -/
theorem velocityTerm_bound (hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) (n : ℕ) :
    ∃ K, ∀ k, ∀ p ∈ (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ)),
      ‖iteratedFDerivWithin ℝ n (velocityTerm c k) (univ ×ˢ Icc 0 S) p‖ ≤
        K * latticeDecayWeight k := by
  have hs : UniqueDiffOn ℝ (univ ×ˢ Icc (0 : ℝ) S : Set (ℝ³ × ℝ)) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hS)
  choose D hD using fun i : ℕ ↦ smoothRapid_derivBound hS hc i (n + 4)
  set K := ‖realSmul‖ * ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * (6 * Real.pi) ^ i * max (D (n - i)) 0 with hK
  refine ⟨K, fun k p hp ↦ ?_⟩
  have hw1 : 1 ≤ 1 + ‖frequencyVec k‖ := by linarith [norm_nonneg (frequencyVec k)]
  have hw0 : 0 < 1 + ‖frequencyVec k‖ := by linarith
  have hB := ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear realSmul
    (f := fun q : ℝ³ × ℝ ↦ character k q.1) (g := fun q : ℝ³ × ℝ ↦ c q.2 k)
    ((contDiff_character k).comp contDiff_fst).contDiffOn (contDiffOn_mode_snd hS hc k) hs hp
    (n := n) (by simp)
  refine hB.trans ?_
  rw [hK, mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (norm_nonneg realSmul)
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 := norm_iteratedFDerivWithin_character_fst_le hS k i hp
  have h2 := norm_iteratedFDerivWithin_mode_snd_le hS hc k (n - i) hp
  have h3 := hD (n - i) p.2 hp.2 k
  have hdec : ‖iteratedDerivWithin (n - i) (fun τ ↦ c τ k) (Icc 0 S) p.2‖ ≤
      max (D (n - i)) 0 / (1 + ‖frequencyVec k‖) ^ (n + 4) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [le_max_left (D (n - i)) 0, mul_comm ((1 + ‖frequencyVec k‖) ^ (n + 4))
      ‖iteratedDerivWithin (n - i) (fun τ ↦ c τ k) (Icc 0 S) p.2‖]
  have hpow : (1 + ‖frequencyVec k‖) ^ i ≤ (1 + ‖frequencyVec k‖) ^ n :=
    pow_le_pow_right₀ hw1 hin
  have hD0 : 0 ≤ max (D (n - i)) 0 := le_max_right _ _
  calc (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (fun q : ℝ³ × ℝ ↦ character k q.1) (univ ×ˢ Icc 0 S) p‖ *
        ‖iteratedFDerivWithin ℝ (n - i) (fun q : ℝ³ × ℝ ↦ c q.2 k) (univ ×ˢ Icc 0 S) p‖
      ≤ (n.choose i : ℝ) * (6 * Real.pi * (1 + ‖frequencyVec k‖)) ^ i *
          (max (D (n - i)) 0 / (1 + ‖frequencyVec k‖) ^ (n + 4)) := by
        gcongr
        exact h2.trans hdec
    _ = (n.choose i : ℝ) * (6 * Real.pi) ^ i * max (D (n - i)) 0 *
          ((1 + ‖frequencyVec k‖) ^ i / (1 + ‖frequencyVec k‖) ^ (n + 4)) := by
        rw [mul_pow]
        ring
    _ ≤ (n.choose i : ℝ) * (6 * Real.pi) ^ i * max (D (n - i)) 0 * latticeDecayWeight k := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        unfold latticeDecayWeight
        rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_add]
        calc (1 + ‖frequencyVec k‖) ^ i * (1 + ‖frequencyVec k‖) ^ 4
            ≤ (1 + ‖frequencyVec k‖) ^ n * (1 + ‖frequencyVec k‖) ^ 4 := by gcongr
          _ = _ := rfl

theorem summable_character_smul (_hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) (x : ℝ³) :
    Summable (fun k ↦ character k x • c t k) := by
  obtain ⟨C, hC⟩ := (hc 0).2 4
  refine (summable_latticeDecayWeight.mul_left C).of_norm_bounded fun k ↦ ?_
  rw [norm_smul, norm_character, one_mul]
  have h := (norm_le_moment (c t) 0 k).trans ((fourierMoment_le_decay (fun k ↦ hC t ht k) k))
  simpa using h

/-- **Smoothness of the physical velocity on a closed slab.** -/
theorem contDiffOn_physVelocity_slab (hS : 0 < S) {c : ℝ → FourierVelocity}
    (hc : ∀ j, SmoothRapid j c (Icc 0 S)) :
    ContDiffOn ℝ ∞ (↿(physVelocity c)) (univ ×ˢ Icc 0 S) := by
  have hU : IsOpen (univ ×ˢ Ioo (0 : ℝ) S : Set (ℝ³ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hUc : Convex ℝ (univ ×ˢ Ioo (0 : ℝ) S : Set (ℝ³ × ℝ)) := convex_univ.prod (convex_Ioo 0 S)
  have hne : (univ ×ˢ Ioo (0 : ℝ) S : Set (ℝ³ × ℝ)).Nonempty :=
    ⟨(0, S / 2), mem_univ _, by constructor <;> linarith⟩
  choose K hK using velocityTerm_bound hS hc
  have h := contDiffOn_tsum_closure hU hUc hne (f := velocityTerm c) (N := ⊤)
    (v := fun n k ↦ K n * latticeDecayWeight k)
    (by rw [closure_slab hS]; exact fun k ↦ contDiffOn_velocityTerm hS hc k)
    (fun n _ ↦ summable_latticeDecayWeight.mul_left _)
    (by rw [closure_slab hS]; exact fun n _ k p hp ↦ hK n k p hp)
  rw [closure_slab hS] at h
  refine h.congr fun p hp ↦ ?_
  change complexRealPartEuclideanCLM (∑' k, character k p.1 • c p.2 k) = ∑' k, velocityTerm c k p
  rw [ContinuousLinearMap.map_tsum _ (summable_character_smul hS hc hp.2 p.1)]
  rfl

/-- **Smoothness of the physical velocity on `ℝ³ × [0, ∞)`.** -/
theorem contDiffOn_physVelocity {c : ℝ → FourierVelocity}
    (hc : ∀ S, 0 < S → ∀ j, SmoothRapid j c (Icc 0 S)) :
    ContDiffOn ℝ ∞ (↿(physVelocity c)) (univ ×ˢ Ici 0) := by
  intro p hp
  have hS : (0 : ℝ) < p.2 + 1 := by linarith [hp.2.out]
  have h := contDiffOn_physVelocity_slab hS (hc _ hS) p ⟨mem_univ _, hp.2, by linarith⟩
  refine h.mono_of_mem_nhdsWithin ?_
  have hnhds : (univ ×ˢ Iio (p.2 + 1) : Set (ℝ³ × ℝ)) ∈ 𝓝 p :=
    (isOpen_univ.prod isOpen_Iio).mem_nhds ⟨mem_univ _, by simp⟩
  filter_upwards [inter_mem_nhdsWithin _ hnhds] with q hq
  exact ⟨mem_univ _, hq.1.2, le_of_lt hq.2.2⟩

end Velocity

end Mettapedia.FluidDynamics.NavierStokes.FourierPhysicalFields

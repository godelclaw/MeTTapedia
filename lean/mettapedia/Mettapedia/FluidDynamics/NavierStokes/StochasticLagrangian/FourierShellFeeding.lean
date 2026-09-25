import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticitySource

/-!
# The shell-feeding inequality: high frequencies are fed only from below

Without forcing, the source of the mode `k` of the vorticity is the
convolution of the velocity with itself. If `|k| ≥ 2^(Q+1)`, every pair
`(p, k - p)` of the convolution has a member with `|p| ≥ 2^Q`: content above
the scale `2^(Q+1)` is produced only from content above the scale `2^Q`.
Combined with the relaxation inequality this gives, along every tame
solution,

```text
∫₀ᴴ W_{≥Q+1}(ω) ≤ R_{Q+1}(ω₀) + (12 / ν) ∫₀ᴴ V_{≥Q}(u) V(u),
```

where `V(u) = ∑_k |u_k|` is the velocity Wiener norm, `V_{≥Q}` its part above
`2^Q`, and `W_{≥Q+1}(ω)` the vorticity Wiener norm above `2^(Q+1)`. The
transverse Biot–Savart bound `|u_k| ≤ |ω_k| / (2π|k|)` turns the right side
into vorticity norms with the factor `1 / (2π 2^Q)`: the feeding rate of the
next shell is the Reynolds number of the scale `2^(-Q)`. The inequality is the
unforced ingredient: with a force there would be one more source term at every
scale.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierShellFeeding

open scoped BigOperators Topology
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy PancakeArbitraryDataBlocks
open PancakePeriodicVorticityEquation PancakePeriodicComplexStretch PancakeIndexedFourierMoments
open PancakeInfinitePressureCoefficients PancakeHigherDerivativeMoments
open FourierDyadicBlockContinuation FourierTimeRegularity FourierSpatialCalculus
open FourierRelaxation FourierVorticitySource FourierTameContinuation PancakeZeroModeCurlBridge

section Lattice

theorem modeSquareNat_cast (k : Wavevector) : (modeSquareNat k : ℝ) = ‖frequencyVec k‖ ^ 2 := by
  rw [norm_frequencyVec_sq, modeSquareNat]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp

theorem four_pow_eq_sq (Q : ℕ) : (4 : ℝ) ^ Q = ((2 : ℝ) ^ Q) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- Modes above the scale `2^Q` have norm at least `2^Q`. -/
theorem two_pow_le_norm {Q : ℕ} {k : Wavevector} (hk : 4 ^ Q ≤ modeSquareNat k) :
    (2 : ℝ) ^ Q ≤ ‖frequencyVec k‖ := by
  have h : ((2 : ℝ) ^ Q) ^ 2 ≤ ‖frequencyVec k‖ ^ 2 := by
    rw [← four_pow_eq_sq, ← modeSquareNat_cast]
    exact_mod_cast hk
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

theorem norm_lt_two_pow {Q : ℕ} {k : Wavevector} (hk : modeSquareNat k < 4 ^ Q) :
    ‖frequencyVec k‖ < (2 : ℝ) ^ Q := by
  have h : ‖frequencyVec k‖ ^ 2 < ((2 : ℝ) ^ Q) ^ 2 := by
    rw [← four_pow_eq_sq, ← modeSquareNat_cast]
    exact_mod_cast hk
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h

/-- **Support of the convolution.** A pair summing to a mode above `2^(Q+1)`
has a member above `2^Q`. -/
theorem high_pair {Q : ℕ} {k : Wavevector} (hk : 4 ^ (Q + 1) ≤ modeSquareNat k) (p : Wavevector) :
    4 ^ Q ≤ modeSquareNat p ∨ 4 ^ Q ≤ modeSquareNat (k - p) := by
  by_contra h
  push Not at h
  have h1 := norm_lt_two_pow h.1
  have h2 := norm_lt_two_pow h.2
  have hk' := two_pow_le_norm hk
  have e : frequencyVec k = frequencyVec p + frequencyVec (k - p) := by
    rw [← frequencyVec_add, add_sub_cancel]
  have h3 : ‖frequencyVec k‖ ≤ ‖frequencyVec p‖ + ‖frequencyVec (k - p)‖ := by
    rw [e]
    exact norm_add_le _ _
  have h4 : (2 : ℝ) ^ (Q + 1) = 2 ^ Q + 2 ^ Q := by ring
  linarith

end Lattice

section Norms

variable {u : FourierVelocity} {g : Wavevector → ℝ}

/-- The velocity Wiener norm `∑_k |u_k|`. -/
def velocityWiener (u : FourierVelocity) : ℝ := ∑' k, ‖coefficientVec (u k)‖

/-- The velocity Wiener norm above the scale `2^Q`. -/
def velocityWienerAbove (Q : ℕ) (u : FourierVelocity) : ℝ :=
  ∑' k, if 4 ^ Q ≤ modeSquareNat k then ‖coefficientVec (u k)‖ else 0

theorem envelope_summable_norm (he : MomentEnvelope u g) :
    Summable (fun k ↦ ‖coefficientVec (u k)‖) :=
  he.summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) he.norm_le

theorem envelope_summable_norm_above (he : MomentEnvelope u g) (Q : ℕ) :
    Summable (fun k ↦ if 4 ^ Q ≤ modeSquareNat k then ‖coefficientVec (u k)‖ else 0) :=
  (envelope_summable_norm he).of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity)
    (fun k ↦ by split_ifs <;> simp)

theorem velocityWiener_nonneg (u : FourierVelocity) : 0 ≤ velocityWiener u :=
  tsum_nonneg fun _ ↦ norm_nonneg _

theorem velocityWienerAbove_nonneg (Q : ℕ) (u : FourierVelocity) : 0 ≤ velocityWienerAbove Q u :=
  tsum_nonneg fun k ↦ by split_ifs <;> positivity

theorem envelope_velocityWiener_le (he : MomentEnvelope u g) :
    velocityWiener u ≤ ∑' k, g k :=
  (envelope_summable_norm he).tsum_le_tsum he.norm_le he.summable

theorem envelope_norm_le_velocityWiener (he : MomentEnvelope u g) (k : Wavevector) :
    ‖coefficientVec (u k)‖ ≤ velocityWiener u :=
  (envelope_summable_norm he).le_tsum k fun _ _ ↦ norm_nonneg _

/-- A finite sum of translates of the coefficient norms is bounded by the Wiener norm. -/
theorem envelope_sum_norm_sub_le (he : MomentEnvelope u g) (K : Finset Wavevector)
    (p : Wavevector) : ∑ k ∈ K, ‖coefficientVec (u (k - p))‖ ≤ velocityWiener u := by
  have hinj : Set.InjOn (fun k ↦ k - p) ↑K := fun _ _ _ _ h ↦ sub_left_injective h
  rw [← Finset.sum_image (f := fun r ↦ ‖coefficientVec (u r)‖) hinj]
  exact (envelope_summable_norm he).sum_le_tsum _ fun _ _ ↦ norm_nonneg _

end Norms

section Source

variable {u : FourierVelocity} {g : Wavevector → ℝ}

/-- The high-source term: the convolution restricted to the sources above `2^Q`. -/
def highSourceTerm (Q : ℕ) (u : FourierVelocity) (k p : Wavevector) : ℝ :=
  (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) * ‖coefficientVec (u (k - p))‖

theorem highSourceTerm_nonneg (Q : ℕ) (u : FourierVelocity) (k p : Wavevector) :
    0 ≤ highSourceTerm Q u k p := by
  unfold highSourceTerm
  split_ifs
  · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · simp

theorem envelope_summable_highSourceTerm (he : MomentEnvelope u g) (Q : ℕ) (k : Wavevector) :
    Summable (fun p ↦ highSourceTerm Q u k p) := by
  refine ((envelope_summable_norm he).mul_right (velocityWiener u)).of_nonneg_of_le
    (fun p ↦ highSourceTerm_nonneg Q u k p) fun p ↦ ?_
  unfold highSourceTerm
  split_ifs
  · exact mul_le_mul_of_nonneg_left (envelope_norm_le_velocityWiener he _) (norm_nonneg _)
  · simp only [zero_mul]
    exact mul_nonneg (norm_nonneg _) (velocityWiener_nonneg u)

/-- **The convolution above `2^(Q+1)` is fed from above `2^Q`.** -/
theorem envelope_norm_conv_le_high (he : MomentEnvelope u g) (Q : ℕ) {k : Wavevector}
    (hk : 4 ^ (Q + 1) ≤ modeSquareNat k) :
    ‖coefficientVec (conv u u k)‖ ≤
      ‖frequencyVec k‖ * (2 * ∑' p, highSourceTerm Q u k p) := by
  have hsv := he.summable_convTerm k
  have hterm : ∀ p, ‖coefficientVec (modeDot k (u p) • u (k - p))‖ ≤
      ‖frequencyVec k‖ * (‖coefficientVec (u p)‖ * ‖coefficientVec (u (k - p))‖) := by
    intro p
    rw [norm_cv_smul]
    have h := PancakeLowPressureBudget.norm_modeDot_le k (u p)
    calc ‖modeDot k (u p)‖ * ‖coefficientVec (u (k - p))‖
        ≤ (‖frequencyVec k‖ * ‖coefficientVec (u p)‖) * ‖coefficientVec (u (k - p))‖ := by gcongr
      _ = _ := by ring
  have hsn : Summable (fun p ↦ ‖coefficientVec (modeDot k (u p) • u (k - p))‖) :=
    (((envelope_summable_norm he).mul_right (velocityWiener u)).mul_left ‖frequencyVec k‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun p ↦ (hterm p).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (envelope_norm_le_velocityWiener he _) (norm_nonneg _)) (norm_nonneg _))
  have hs2 : Summable (fun p ↦ ‖coefficientVec (u p)‖ * ‖coefficientVec (u (k - p))‖) :=
    ((envelope_summable_norm he).mul_right (velocityWiener u)).of_nonneg_of_le (fun _ ↦ by positivity)
      fun p ↦ mul_le_mul_of_nonneg_left (envelope_norm_le_velocityWiener he _) (norm_nonneg _)
  -- the series of the convolution
  rw [conv_self, infiniteConvection_eq_of_summable hsv]
  have e : coefficientVec (∑' p, modeDot k (u p) • u (k - p)) =
      ∑' p, coefficientVec (modeDot k (u p) • u (k - p)) :=
    (EuclideanSpace.equiv (Fin 3) ℂ).symm.map_tsum
  rw [e]
  -- the pair bound: each product is at most the sum of its two high-source versions
  let σ : Wavevector ≃ Wavevector := Equiv.subLeft k
  have hsH := envelope_summable_highSourceTerm he Q k
  have hsHσ : Summable (fun p ↦ highSourceTerm Q u k (k - p)) := hsH.comp_injective σ.injective
  have hpair : ∀ p, ‖coefficientVec (u p)‖ * ‖coefficientVec (u (k - p))‖ ≤
      highSourceTerm Q u k p + highSourceTerm Q u k (k - p) := by
    intro p
    unfold highSourceTerm
    rw [sub_sub_cancel]
    rcases high_pair hk p with h | h
    · rw [ite_eq_left h]
      have : 0 ≤ (if 4 ^ Q ≤ modeSquareNat (k - p) then ‖coefficientVec (u (k - p))‖ else 0) *
          ‖coefficientVec (u p)‖ := by split_ifs <;> positivity
      linarith
    · rw [ite_eq_left h]
      have : 0 ≤ (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
          ‖coefficientVec (u (k - p))‖ := by split_ifs <;> positivity
      linarith [mul_comm ‖coefficientVec (u (k - p))‖ ‖coefficientVec (u p)‖]
  have hσ : ∑' p, highSourceTerm Q u k (k - p) = ∑' p, highSourceTerm Q u k p :=
    σ.tsum_eq (fun p ↦ highSourceTerm Q u k p)
  calc ‖∑' p, coefficientVec (modeDot k (u p) • u (k - p))‖
      ≤ ∑' p, ‖coefficientVec (modeDot k (u p) • u (k - p))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' p, ‖frequencyVec k‖ * (‖coefficientVec (u p)‖ * ‖coefficientVec (u (k - p))‖) :=
        hsn.tsum_le_tsum hterm (hs2.mul_left _)
    _ = ‖frequencyVec k‖ * ∑' p, ‖coefficientVec (u p)‖ * ‖coefficientVec (u (k - p))‖ :=
        tsum_mul_left
    _ ≤ ‖frequencyVec k‖ * ∑' p, (highSourceTerm Q u k p + highSourceTerm Q u k (k - p)) :=
        mul_le_mul_of_nonneg_left (hs2.tsum_le_tsum hpair (hsH.add hsHσ)) (norm_nonneg _)
    _ = ‖frequencyVec k‖ * (2 * ∑' p, highSourceTerm Q u k p) := by
        rw [hsH.tsum_add hsHσ, hσ]
        ring

/-- **The sharp source mass above `2^(Q+1)`.** -/
theorem envelope_sharp_mass_le_high (he : MomentEnvelope u g) {nu : ℝ} (hnu : 0 < nu)
    (Q : ℕ) {k : Wavevector} (hk : 4 ^ (Q + 1) ≤ modeSquareNat k) :
    sharpWeight nu k * vorticityMass u k ≤ 12 / nu * ∑' p, highSourceTerm Q u k p := by
  have hk0 : k ≠ 0 := by
    intro h
    subst h
    simp [modeSquareNat] at hk
  have hn1 := one_le_norm_frequencyVec hk0
  have hn0 : 0 < ‖frequencyVec k‖ := by linarith
  have hS : 0 ≤ ∑' p, highSourceTerm Q u k p := tsum_nonneg fun p ↦ highSourceTerm_nonneg Q u k p
  have h1 : vorticityMass u k ≤ 2 * Real.pi * fourierMoment 1 (nonlinear u) k :=
    norm_coefficientVec_fourierCurl_le (nonlinear u) k
  have h2 : fourierMoment 1 (nonlinear u) k ≤
      (1 + ‖frequencyVec k‖) * (2 * Real.pi * ‖coefficientVec (conv u u k)‖) := by
    have e : fourierMoment 1 (nonlinear u) k =
        (1 + ‖frequencyVec k‖) * ‖coefficientVec (nonlinear u k)‖ := by
      unfold fourierMoment; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (norm_nonlinear_le u k) (by positivity)
  have h3 := envelope_norm_conv_le_high he Q hk
  have hw : sharpWeight nu k = 3 / (4 * Real.pi ^ 2 * nu * ‖frequencyVec k‖ ^ 2) := rfl
  have hkne : ‖frequencyVec k‖ ≠ 0 := hn0.ne'
  have hnune : nu ≠ 0 := hnu.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hv : vorticityMass u k ≤ (2 * Real.pi) ^ 2 * (1 + ‖frequencyVec k‖) * ‖frequencyVec k‖ *
      (2 * ∑' p, highSourceTerm Q u k p) := by
    calc vorticityMass u k ≤ 2 * Real.pi * fourierMoment 1 (nonlinear u) k := h1
      _ ≤ 2 * Real.pi * ((1 + ‖frequencyVec k‖) * (2 * Real.pi * ‖coefficientVec (conv u u k)‖)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * Real.pi * ((1 + ‖frequencyVec k‖) *
            (2 * Real.pi * (‖frequencyVec k‖ * (2 * ∑' p, highSourceTerm Q u k p)))) := by
          gcongr
      _ = _ := by ring
  have hratio : (1 + ‖frequencyVec k‖) / ‖frequencyVec k‖ ≤ 2 := by
    rw [div_le_iff₀ hn0]
    linarith
  rw [hw]
  calc 3 / (4 * Real.pi ^ 2 * nu * ‖frequencyVec k‖ ^ 2) * vorticityMass u k
      ≤ 3 / (4 * Real.pi ^ 2 * nu * ‖frequencyVec k‖ ^ 2) *
          ((2 * Real.pi) ^ 2 * (1 + ‖frequencyVec k‖) * ‖frequencyVec k‖ *
            (2 * ∑' p, highSourceTerm Q u k p)) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ = 6 / nu * ((1 + ‖frequencyVec k‖) / ‖frequencyVec k‖) * ∑' p, highSourceTerm Q u k p := by
        field_simp
        ring
    _ ≤ 6 / nu * 2 * ∑' p, highSourceTerm Q u k p := by
        gcongr
    _ = _ := by ring

theorem mem_shell_high {Q n : ℕ} {k : Wavevector} (hk : k ∈ dyadicShellModes (Q + 1 + n)) :
    4 ^ (Q + 1) ≤ modeSquareNat k := by
  have h := ((mem_dyadicShellModes_iff_pow_four _ k).mp hk).1
  calc 4 ^ (Q + 1) ≤ 4 ^ (Q + 1 + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ modeSquareNat k := h

/-- **The shell-feeding bound for the source.** The source above `2^(Q+1)` is
at most `12/ν` times the velocity Wiener norm above `2^Q` times the velocity
Wiener norm. -/
theorem envelope_vorticitySourceSum_le (he : MomentEnvelope u g) {nu : ℝ} (hnu : 0 < nu)
    (Q : ℕ) :
    vorticitySourceSum nu (Q + 1) u ≤ 12 / nu * velocityWienerAbove Q u * velocityWiener u := by
  unfold vorticitySourceSum
  refine Real.tsum_le_of_sum_range_le (fun n ↦ Finset.sum_nonneg fun k _ ↦
    mul_nonneg (sharpWeight_nonneg hnu k) (vorticityMass_nonneg u k)) fun N ↦ ?_
  -- the finite shells form the annulus
  rw [← Finset.sum_biUnion (pairwiseDisjoint_shells (Q + 1) N)]
  have hann : ∀ k ∈ annulusModes (Q + 1) N, 4 ^ (Q + 1) ≤ modeSquareNat k := by
    intro k hk
    obtain ⟨n, _, hn⟩ := Finset.mem_biUnion.mp hk
    exact mem_shell_high hn
  calc ∑ k ∈ annulusModes (Q + 1) N, sharpWeight nu k * vorticityMass u k
      ≤ ∑ k ∈ annulusModes (Q + 1) N, 12 / nu * ∑' p, highSourceTerm Q u k p :=
        Finset.sum_le_sum fun k hk ↦ envelope_sharp_mass_le_high he hnu Q (hann k hk)
    _ = 12 / nu * ∑' p, (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
          ∑ k ∈ annulusModes (Q + 1) N, ‖coefficientVec (u (k - p))‖ := by
        rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun k _ ↦ envelope_summable_highSourceTerm he Q k]
        congr 1
        refine tsum_congr fun p ↦ ?_
        unfold highSourceTerm
        rw [Finset.mul_sum]
    _ ≤ 12 / nu * ∑' p, (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
          velocityWiener u := by
        have hs2 : Summable (fun p ↦ (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
            velocityWiener u) := (envelope_summable_norm_above he Q).mul_right _
        have hpt : ∀ p, (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
            ∑ k ∈ annulusModes (Q + 1) N, ‖coefficientVec (u (k - p))‖ ≤
            (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) * velocityWiener u :=
          fun p ↦ mul_le_mul_of_nonneg_left (envelope_sum_norm_sub_le he _ p) (by split_ifs <;> positivity)
        have hs1 : Summable (fun p ↦ (if 4 ^ Q ≤ modeSquareNat p then ‖coefficientVec (u p)‖ else 0) *
            ∑ k ∈ annulusModes (Q + 1) N, ‖coefficientVec (u (k - p))‖) :=
          hs2.of_nonneg_of_le (fun p ↦ mul_nonneg (by split_ifs <;> positivity)
            (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)) hpt
        exact mul_le_mul_of_nonneg_left (hs1.tsum_le_tsum hpt hs2) (by positivity)
    _ = _ := by
        rw [tsum_mul_right, mul_assoc]
        rfl

end Source

section Feeding

variable {nu T B : ℝ} {u₀ : FourierVelocity} {g : Wavevector → ℝ}
variable {s : LocalInfiniteVelocitySolution nu u₀ T B}

theorem continuousOn_velocityWiener (he : Envelope s g) :
    ContinuousOn (fun t ↦ velocityWiener (s.coefficients t)) (Icc 0 T) := by
  unfold velocityWiener
  refine continuousOn_tsum (fun k ↦ ?_) he.summable fun k t ht ↦ ?_
  · exact ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
      (continuousOn_pi.mpr fun i ↦ (s.continuous k i).continuousOn)).norm
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (MomentEnvelope.norm_le ⟨he.nonneg, he.summable, he.bound t ht⟩ k)

theorem continuousOn_velocityWienerAbove (he : Envelope s g) (Q : ℕ) :
    ContinuousOn (fun t ↦ velocityWienerAbove Q (s.coefficients t)) (Icc 0 T) := by
  unfold velocityWienerAbove
  refine continuousOn_tsum (fun k ↦ ?_) he.summable fun k t ht ↦ ?_
  · split_ifs
    · exact ((EuclideanSpace.equiv (Fin 3) ℂ).symm.continuous.comp_continuousOn
        (continuousOn_pi.mpr fun i ↦ (s.continuous k i).continuousOn)).norm
    · exact continuousOn_const
  · split_ifs
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact (MomentEnvelope.norm_le ⟨he.nonneg, he.summable, he.bound t ht⟩ k)
    · rw [norm_zero]
      exact he.nonneg k

/-- **The shell-feeding inequality along a local solution.** -/
theorem integral_wienerHigh_succ_le_local (hB : 0 ≤ B) (hnu : 0 < nu) (he : Envelope s g)
    (Q : ℕ) {H : ℝ} (hH : H ∈ Icc (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, wienerHigh (Q + 1) (s.coefficients t) ≤
      relaxConst nu (Q + 1) u₀ + 12 / nu * ∫ t in (0 : ℝ)..H,
        velocityWienerAbove Q (s.coefficients t) * velocityWiener (s.coefficients t) := by
  have h1 := integral_wienerHigh_le_local hB hnu he (Q + 1) hH
  have hsub : Icc (0 : ℝ) H ⊆ Icc 0 T := Icc_subset_Icc le_rfl hH.2
  have hc1 : ContinuousOn (fun t ↦ vorticitySourceSum nu (Q + 1) (s.coefficients t)) (Icc 0 H) :=
    (continuousOn_vorticitySourceSum hB hnu he (Q + 1) (hH.1.trans hH.2)).mono hsub
  have hc2 : ContinuousOn (fun t ↦ velocityWienerAbove Q (s.coefficients t) *
      velocityWiener (s.coefficients t)) (Icc 0 H) :=
    ((continuousOn_velocityWienerAbove he Q).mono hsub).mul ((continuousOn_velocityWiener he).mono hsub)
  have h2 : ∫ t in (0 : ℝ)..H, vorticitySourceSum nu (Q + 1) (s.coefficients t) ≤
      ∫ t in (0 : ℝ)..H, 12 / nu * (velocityWienerAbove Q (s.coefficients t) *
        velocityWiener (s.coefficients t)) := by
    refine intervalIntegral.integral_mono_on hH.1 (hc1.intervalIntegrable_of_Icc hH.1)
      ((continuousOn_const.mul hc2).intervalIntegrable_of_Icc hH.1) fun t ht ↦ ?_
    have := (envelope_vorticitySourceSum_le ⟨he.nonneg, he.summable, he.bound t (hsub ht)⟩
      hnu Q)
    linarith [this, mul_assoc (12 / nu) (velocityWienerAbove Q (s.coefficients t))
      (velocityWiener (s.coefficients t))]
  rw [intervalIntegral.integral_const_mul] at h2
  linarith

/-- **The shell-feeding inequality along a tame solution.** -/
theorem integral_wienerHigh_succ_le (m : ℕ) (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) (Q : ℕ) {H : ℝ} (hH : H ∈ Ico (0 : ℝ) T) :
    ∫ t in (0 : ℝ)..H, wienerHigh (Q + 1) (c.coefficients t) ≤
      relaxConst nu (Q + 1) u₀ + 12 / nu * ∫ t in (0 : ℝ)..H,
        velocityWienerAbove Q (c.coefficients t) * velocityWiener (c.coefficients t) := by
  obtain ⟨S, hHS, _, B, s, hsc, g, hg0, hg, hu⟩ := exists_local_envelope m hm c H hH
  have hB : 0 ≤ B :=
    le_trans (PancakeSobolevWeights.energy_nonneg ∅ _)
      (s.sobolev_bound 0 ⟨le_rfl, hH.1.trans hHS.le⟩ ∅)
  have he : Envelope s g := ⟨hg0, hg, hu⟩
  rw [← hsc]
  exact integral_wienerHigh_succ_le_local hB hnu he Q ⟨hH.1, hHS.le⟩

end Feeding

section Reynolds

variable {u : FourierVelocity} {g : Wavevector → ℝ}

/-- **The transverse Biot–Savart bound.** A zero-mean transverse coefficient
is bounded by its vorticity over `2π|k|`. -/
theorem norm_le_curl_div (hu0 : u 0 = 0) (htr : ∀ k, modeDot k (u k) = 0) {k : Wavevector}
    (hk : k ≠ 0) :
    ‖coefficientVec (u k)‖ ≤ ‖coefficientVec (fourierCurl u k)‖ / (2 * Real.pi * ‖frequencyVec k‖) := by
  have hbs : unitTorusBiotSavartAmp k (fourierCurl u k) = u k :=
    physicalBiotSavart_fourierCurl_meanZero u hu0 k (htr k)
  have hn := one_le_norm_frequencyVec hk
  have hn0 : 0 < ‖frequencyVec k‖ := by linarith
  rw [← hbs]
  unfold unitTorusBiotSavartAmp complexBiotSavartAmp
  rw [norm_cv_smul, norm_cv_smul, norm_neg, norm_inv,
    PancakeIncomingLowSourceEnergy.norm_derivativePhase, norm_div, norm_one,
    FourierTimeRegularity.norm_modeSquare]
  have h := PancakeSameSectorDissipation.norm_cross_le k (fourierCurl u k)
  have hkne : ‖frequencyVec k‖ ≠ 0 := hn0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [le_div_iff₀ (by positivity)]
  calc (2 * Real.pi)⁻¹ * (1 / ‖frequencyVec k‖ ^ 2 *
        ‖coefficientVec (coefficientCross (wavevectorCoefficient k) (fourierCurl u k))‖) *
        (2 * Real.pi * ‖frequencyVec k‖)
      ≤ (2 * Real.pi)⁻¹ * (1 / ‖frequencyVec k‖ ^ 2 *
          (‖frequencyVec k‖ * ‖coefficientVec (fourierCurl u k)‖)) *
          (2 * Real.pi * ‖frequencyVec k‖) := by gcongr
    _ = ‖coefficientVec (fourierCurl u k)‖ := by
        field_simp

/-- **The velocity Wiener norm above `2^Q` is the vorticity Wiener norm over `2π 2^Q`.** -/
theorem velocityWienerAbove_le (he : MomentEnvelope u g) (hu0 : u 0 = 0)
    (htr : ∀ k, modeDot k (u k) = 0) (Q : ℕ) :
    velocityWienerAbove Q u ≤ (1 / (2 * Real.pi * 2 ^ Q)) *
      ∑' k, if 4 ^ Q ≤ modeSquareNat k then curlMass u k else 0 := by
  unfold velocityWienerAbove
  rw [← tsum_mul_left]
  refine (envelope_summable_norm_above he Q).tsum_le_tsum (fun k ↦ ?_) ?_
  · split_ifs with hk
    · have hk0 : k ≠ 0 := by
        intro h
        subst h
        simp [modeSquareNat] at hk
      have h2 := two_pow_le_norm hk
      have hpos : (0 : ℝ) < 2 * Real.pi * 2 ^ Q := by positivity
      calc ‖coefficientVec (u k)‖
          ≤ ‖coefficientVec (fourierCurl u k)‖ / (2 * Real.pi * ‖frequencyVec k‖) :=
            norm_le_curl_div hu0 htr hk0
        _ ≤ ‖coefficientVec (fourierCurl u k)‖ / (2 * Real.pi * 2 ^ Q) := by
            gcongr
        _ = _ := by unfold curlMass; ring
    · simp
  · refine ((he.summable.mul_left (2 * Real.pi)).mul_left (1 / (2 * Real.pi * 2 ^ Q))).of_nonneg_of_le
      (fun k ↦ ?_) fun k ↦ ?_
    · split_ifs
      · exact mul_nonneg (by positivity) (curlMass_nonneg u k)
      · simp
    · split_ifs
      · exact mul_le_mul_of_nonneg_left (he.norm_curl_le k) (by positivity)
      · simp only [mul_zero]
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (he.nonneg k))

end Reynolds

end Mettapedia.FluidDynamics.NavierStokes.FourierShellFeeding

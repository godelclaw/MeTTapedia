import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarRegularity
import Mettapedia.Analysis.SmoothSeriesClosure

/-!
# Time regularity of the Fourier solutions

A coefficient curve is *smooth-rapid* of order `j` on a closed time interval
when it is `j` times differentiable there, mode by mode and one-sidedly at the
endpoints, with every derivative continuous and rapidly decaying in the
wavevector uniformly in time. The bilinear convection and the viscous term
preserve this class, so a solution whose coefficients decay rapidly on
`[0, S]` is smooth-rapid of every order there: its right-hand side is again
smooth-rapid, and it is the derivative of the solution. This is the time
regularity needed for smooth physical fields, up to the initial time.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTimeRegularity

open scoped BigOperators Topology
open Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope PancakeLowPressureBudget
open PancakePeriodicVorticityEquation PancakeFixedOutputVelocityBound PancakeHigherDerivativeMoments
open Mettapedia.Analysis.SmoothSeriesClosure

section Rapid

/-- Uniform rapid decay on a set of times. -/
def RapidOn (a : ℝ → FourierVelocity) (s : Set ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ t ∈ s, ∀ k, fourierMoment n (a t) k ≤ C

theorem fourierMoment_add_four (n : ℕ) (u : FourierVelocity) (k : Wavevector) :
    fourierMoment (n + 4) u k = (1 + ‖frequencyVec k‖) ^ 4 * fourierMoment n u k := by
  unfold fourierMoment
  ring

theorem fourierMoment_le_decay {u : FourierVelocity} {n : ℕ} {C : ℝ}
    (h : ∀ k, fourierMoment (n + 4) u k ≤ C) (k : Wavevector) :
    fourierMoment n u k ≤ C * latticeDecayWeight k := by
  have hp : 0 < (1 + ‖frequencyVec k‖) ^ 4 := by positivity
  have h1 := h k
  rw [fourierMoment_add_four] at h1
  unfold latticeDecayWeight
  rw [mul_one_div, le_div_iff₀ hp]
  linarith

theorem norm_le_sum_components (v : VelocityCoefficient) :
    ‖coefficientVec v‖ ≤ ∑ i : Fin 3, ‖v i‖ := by
  have hs : 0 ≤ ∑ i : Fin 3, ‖v i‖ := by positivity
  have h2 : ‖coefficientVec v‖ ^ 2 ≤ (∑ i : Fin 3, ‖v i‖) ^ 2 := by
    rw [norm_coefficientVec_sq]
    simp only [coefficientEnergy, Fin.sum_univ_three, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (v 0), norm_nonneg (v 1), norm_nonneg (v 2),
      mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 1)),
      mul_nonneg (norm_nonneg (v 0)) (norm_nonneg (v 2)),
      mul_nonneg (norm_nonneg (v 1)) (norm_nonneg (v 2))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hs two_ne_zero).mp h2

theorem weight_le_mul (q p : Wavevector) :
    1 + ‖frequencyVec q‖ ≤ (1 + ‖frequencyVec p‖) * (1 + ‖frequencyVec (q - p)‖) := by
  have hq : frequencyVec q = frequencyVec p + frequencyVec (q - p) := by
    rw [← frequencyVec_add]
    congr 1
    abel
  have h := norm_add_le (frequencyVec p) (frequencyVec (q - p))
  rw [← hq] at h
  nlinarith [mul_nonneg (norm_nonneg (frequencyVec p)) (norm_nonneg (frequencyVec (q - p)))]

end Rapid

section Convolution

/-- The bilinear convection `∑ₚ (q · aₚ) b_{q-p}`. -/
def conv (a b : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  fun i ↦ ∑' p, modeDot q (a p) * b (q - p) i

theorem conv_self (u : FourierVelocity) : conv u u = infiniteConvection u := rfl

/-- The weighted convection term. -/
theorem weighted_conv_term_le (a b : FourierVelocity) (n : ℕ) (q p : Wavevector) (i : Fin 3) :
    (1 + ‖frequencyVec q‖) ^ n * ‖modeDot q (a p) * b (q - p) i‖ ≤
      fourierMoment (n + 1) a p * fourierMoment (n + 1) b (q - p) := by
  have h1 : ‖modeDot q (a p)‖ ≤ (1 + ‖frequencyVec q‖) * ‖coefficientVec (a p)‖ :=
    (norm_modeDot_le q (a p)).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have h2 : ‖b (q - p) i‖ ≤ ‖coefficientVec (b (q - p))‖ :=
    PiLp.norm_apply_le (coefficientVec (b (q - p))) i
  have hw := weight_le_mul q p
  have hw1 : (1 + ‖frequencyVec q‖) ^ (n + 1) ≤
      (1 + ‖frequencyVec p‖) ^ (n + 1) * (1 + ‖frequencyVec (q - p)‖) ^ (n + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hw _
  rw [norm_mul]
  calc (1 + ‖frequencyVec q‖) ^ n * (‖modeDot q (a p)‖ * ‖b (q - p) i‖)
      ≤ (1 + ‖frequencyVec q‖) ^ n * (((1 + ‖frequencyVec q‖) * ‖coefficientVec (a p)‖) *
          ‖coefficientVec (b (q - p))‖) := by gcongr
    _ = (1 + ‖frequencyVec q‖) ^ (n + 1) *
          (‖coefficientVec (a p)‖ * ‖coefficientVec (b (q - p))‖) := by ring
    _ ≤ ((1 + ‖frequencyVec p‖) ^ (n + 1) * (1 + ‖frequencyVec (q - p)‖) ^ (n + 1)) *
          (‖coefficientVec (a p)‖ * ‖coefficientVec (b (q - p))‖) := by gcongr
    _ = _ := by unfold fourierMoment; ring

/-- A summable envelope for the convection terms of rapid fields. -/
theorem conv_term_le_env {a b : FourierVelocity} {n : ℕ} {A B : ℝ}
    (hA : ∀ p, fourierMoment (n + 5) a p ≤ A) (hB : ∀ r, fourierMoment (n + 1) b r ≤ B)
    (_hB0 : 0 ≤ B) (q p : Wavevector) (i : Fin 3) :
    (1 + ‖frequencyVec q‖) ^ n * ‖modeDot q (a p) * b (q - p) i‖ ≤
      A * B * latticeDecayWeight p := by
  refine (weighted_conv_term_le a b n q p i).trans ?_
  have hd := fourierMoment_le_decay (n := n + 1) (by simpa [add_assoc] using hA) p
  calc fourierMoment (n + 1) a p * fourierMoment (n + 1) b (q - p)
      ≤ (A * latticeDecayWeight p) * B :=
        mul_le_mul hd (hB _) (fourierMoment_nonneg _ _ _)
          (by nlinarith [fourierMoment_nonneg (n + 1) a p])
    _ = A * B * latticeDecayWeight p := by ring

theorem summable_conv_term {a b : FourierVelocity} {n : ℕ} {A B : ℝ}
    (hA : ∀ p, fourierMoment (n + 5) a p ≤ A) (hB : ∀ r, fourierMoment (n + 1) b r ≤ B)
    (hB0 : 0 ≤ B) (q : Wavevector) (i : Fin 3) :
    Summable (fun p ↦ modeDot q (a p) * b (q - p) i) := by
  refine (summable_latticeDecayWeight.mul_left (A * B)).of_norm_bounded fun p ↦ ?_
  have h := conv_term_le_env hA hB hB0 q p i
  have hw : 1 ≤ (1 + ‖frequencyVec q‖) ^ n := one_le_pow₀ (by linarith [norm_nonneg (frequencyVec q)])
  calc ‖modeDot q (a p) * b (q - p) i‖ ≤ (1 + ‖frequencyVec q‖) ^ n *
        ‖modeDot q (a p) * b (q - p) i‖ := le_mul_of_one_le_left (norm_nonneg _) hw
    _ ≤ _ := h

/-- **Rapid decay of the convection.** -/
theorem fourierMoment_conv_le {a b : FourierVelocity} {n : ℕ} {A B : ℝ}
    (hA : ∀ p, fourierMoment (n + 5) a p ≤ A) (hB : ∀ r, fourierMoment (n + 1) b r ≤ B)
    (hB0 : 0 ≤ B) (q : Wavevector) :
    fourierMoment n (conv a b) q ≤ 3 * (A * B * ∑' p, latticeDecayWeight p) := by
  unfold fourierMoment
  have hcomp : ∀ i, (1 + ‖frequencyVec q‖) ^ n * ‖conv a b q i‖ ≤
      A * B * ∑' p, latticeDecayWeight p := by
    intro i
    have hs := summable_conv_term hA hB hB0 q i
    have hns : Summable (fun p ↦ ‖modeDot q (a p) * b (q - p) i‖) :=
      (summable_latticeDecayWeight.mul_left (A * B)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
        fun p ↦ (le_mul_of_one_le_left (norm_nonneg _)
          (one_le_pow₀ (by linarith [norm_nonneg (frequencyVec q)]))).trans
          (conv_term_le_env hA hB hB0 q p i)
    calc (1 + ‖frequencyVec q‖) ^ n * ‖conv a b q i‖
        ≤ (1 + ‖frequencyVec q‖) ^ n * ∑' p, ‖modeDot q (a p) * b (q - p) i‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hns) (by positivity)
      _ = ∑' p, (1 + ‖frequencyVec q‖) ^ n * ‖modeDot q (a p) * b (q - p) i‖ :=
          (tsum_mul_left).symm
      _ ≤ ∑' p, A * B * latticeDecayWeight p :=
          (hns.mul_left _).tsum_le_tsum (fun p ↦ conv_term_le_env hA hB hB0 q p i)
            (summable_latticeDecayWeight.mul_left _)
      _ = A * B * ∑' p, latticeDecayWeight p := tsum_mul_left
  calc (1 + ‖frequencyVec q‖) ^ n * ‖coefficientVec (conv a b q)‖
      ≤ (1 + ‖frequencyVec q‖) ^ n * ∑ i : Fin 3, ‖conv a b q i‖ :=
        mul_le_mul_of_nonneg_left (norm_le_sum_components _) (by positivity)
    _ = ∑ i : Fin 3, (1 + ‖frequencyVec q‖) ^ n * ‖conv a b q i‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin 3, A * B * ∑' p, latticeDecayWeight p := Finset.sum_le_sum fun i _ ↦ hcomp i
    _ = 3 * (A * B * ∑' p, latticeDecayWeight p) := by simp

end Convolution

section OneDim

/-- Termwise differentiation of a series of curves on a closed interval. -/
theorem hasDerivWithinAt_tsum_Icc {α F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {S : ℝ} (hS : 0 < S) {g g' : α → ℝ → F} {u : α → ℝ} (hu : Summable u)
    (hg : ∀ i, ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt (g i) (g' i t) (Icc 0 S) t)
    (hg'c : ∀ i, ContinuousOn (g' i) (Icc 0 S))
    (hg'b : ∀ i, ∀ t ∈ Icc (0 : ℝ) S, ‖g' i t‖ ≤ u i)
    (hgc : ContinuousOn (fun t ↦ ∑' i, g i t) (Icc 0 S))
    (hsum : ∀ t ∈ Icc (0 : ℝ) S, Summable (fun i ↦ g i t)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) :
    HasDerivWithinAt (fun τ ↦ ∑' i, g i τ) (∑' i, g' i t) (Icc 0 S) t := by
  have hcl : closure (Ioo (0 : ℝ) S) = Icc 0 S := closure_Ioo hS.ne
  let L : F →L[ℝ] (ℝ →L[ℝ] F) := ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)
  have hLn : ∀ v : F, ‖L v‖ = ‖v‖ := by
    intro v
    change ‖(1 : ℝ →L[ℝ] ℝ).smulRight v‖ = ‖v‖
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul]
  have h := hasFDerivWithinAt_tsum_closure (U := Ioo (0 : ℝ) S) isOpen_Ioo (convex_Ioo 0 S)
    (nonempty_Ioo.mpr hS) (g := g) (g' := fun i τ ↦ L (g' i τ)) hu
    (by rw [hcl]; exact fun i τ hτ ↦ (hg i τ hτ).hasFDerivWithinAt)
    (by rw [hcl]; exact fun i ↦ L.continuous.comp_continuousOn (hg'c i))
    (by rw [hcl]; exact fun i τ hτ ↦ (hLn _).le.trans (hg'b i τ hτ))
    (by rw [hcl]; exact hgc) (by rw [hcl]; exact hsum) (by rw [hcl]; exact ht)
  rw [hcl] at h
  have hs' : Summable (fun i ↦ g' i t) := hu.of_norm_bounded fun i ↦ hg'b i t ht
  rw [← L.map_tsum hs'] at h
  exact h

end OneDim

section SmoothRapid

/-- Modewise continuity on a set of times. -/
def ContOn (a : ℝ → FourierVelocity) (s : Set ℝ) : Prop := ∀ k i, ContinuousOn (fun t ↦ a t k i) s

/-- `j` modewise derivatives within `s`, each continuous and uniformly rapidly decaying. -/
def SmoothRapid : ℕ → (ℝ → FourierVelocity) → Set ℝ → Prop
  | 0, a, s => ContOn a s ∧ RapidOn a s
  | j + 1, a, s => (ContOn a s ∧ RapidOn a s) ∧ ∃ a' : ℝ → FourierVelocity,
      (∀ t ∈ s, ∀ k i, HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) s t) ∧ SmoothRapid j a' s

theorem SmoothRapid.base {j : ℕ} {a : ℝ → FourierVelocity} {s : Set ℝ} (h : SmoothRapid j a s) :
    ContOn a s ∧ RapidOn a s := by
  cases j with
  | zero => exact h
  | succ j => exact h.1

theorem SmoothRapid.mono : ∀ {j : ℕ} {a : ℝ → FourierVelocity} {s : Set ℝ},
    SmoothRapid (j + 1) a s → SmoothRapid j a s
  | 0, _, _, h => h.1
  | j + 1, _, _, h => by
    obtain ⟨hb, a', ha', hj⟩ := h
    exact ⟨hb, a', ha', SmoothRapid.mono hj⟩

theorem RapidOn.add {a b : ℝ → FourierVelocity} {s : Set ℝ} (ha : RapidOn a s) (hb : RapidOn b s) :
    RapidOn (fun t ↦ a t + b t) s := by
  intro n
  obtain ⟨A, hA⟩ := ha n
  obtain ⟨B, hB⟩ := hb n
  refine ⟨A + B, fun t ht k ↦ ?_⟩
  have h : fourierMoment n (a t + b t) k ≤ fourierMoment n (a t) k + fourierMoment n (b t) k := by
    unfold fourierMoment
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact norm_add_le (coefficientVec (a t k)) (coefficientVec (b t k))
  exact h.trans (add_le_add (hA t ht k) (hB t ht k))

theorem SmoothRapid.add : ∀ {j : ℕ} {a b : ℝ → FourierVelocity} {s : Set ℝ},
    SmoothRapid j a s → SmoothRapid j b s → SmoothRapid j (fun t ↦ a t + b t) s
  | 0, _, _, _, ha, hb => ⟨fun k i ↦ (ha.1 k i).add (hb.1 k i), ha.2.add hb.2⟩
  | j + 1, _, _, _, ha, hb => by
    obtain ⟨hab, a', ha', hja⟩ := ha
    obtain ⟨hbb, b', hb', hjb⟩ := hb
    exact ⟨⟨fun k i ↦ (hab.1 k i).add (hbb.1 k i), hab.2.add hbb.2⟩, fun t k ↦ a' t k + b' t k,
      fun t ht k i ↦ (ha' t ht k i).add (hb' t ht k i), SmoothRapid.add hja hjb⟩

/-- Modewise application of complex-linear maps with polynomial norm growth
preserves the class. -/
theorem SmoothRapid.map_mode (M : Wavevector → VelocityCoefficient →L[ℂ] VelocityCoefficient)
    {K : ℝ} {d : ℕ} (hK : 0 ≤ K)
    (hM : ∀ q v, ‖coefficientVec (M q v)‖ ≤ K * (1 + ‖frequencyVec q‖) ^ d * ‖coefficientVec v‖) :
    ∀ {j : ℕ} {a : ℝ → FourierVelocity} {s : Set ℝ},
      SmoothRapid j a s → SmoothRapid j (fun t q ↦ M q (a t q)) s := by
  have hrapid : ∀ {a : ℝ → FourierVelocity} {s : Set ℝ}, RapidOn a s →
      RapidOn (fun t q ↦ M q (a t q)) s := by
    intro a s ha n
    obtain ⟨C, hC⟩ := ha (n + d)
    refine ⟨K * C, fun t ht k ↦ ?_⟩
    have h := hC t ht k
    unfold fourierMoment at h ⊢
    calc (1 + ‖frequencyVec k‖) ^ n * ‖coefficientVec (M k (a t k))‖
        ≤ (1 + ‖frequencyVec k‖) ^ n * (K * (1 + ‖frequencyVec k‖) ^ d *
            ‖coefficientVec (a t k)‖) := mul_le_mul_of_nonneg_left (hM k _) (by positivity)
      _ = K * ((1 + ‖frequencyVec k‖) ^ (n + d) * ‖coefficientVec (a t k)‖) := by ring
      _ ≤ K * C := mul_le_mul_of_nonneg_left h hK
  have hcont : ∀ {a : ℝ → FourierVelocity} {s : Set ℝ}, ContOn a s →
      ContOn (fun t q ↦ M q (a t q)) s := by
    intro a s ha k i
    have hv : ContinuousOn (fun t ↦ a t k) s := continuousOn_pi.mpr fun l ↦ ha k l
    exact (continuous_apply i).comp_continuousOn
      (((M k).restrictScalars ℝ).continuous.comp_continuousOn hv)
  have hderiv : ∀ {a a' : ℝ → FourierVelocity} {s : Set ℝ} {t : ℝ},
      (∀ k i, HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) s t) →
      ∀ k i, HasDerivWithinAt (fun τ ↦ M k (a τ k) i) (M k (a' t k) i) s t := by
    intro a a' s t ha k i
    have hv : HasDerivWithinAt (fun τ ↦ a τ k) (a' t k) s t := hasDerivWithinAt_pi.mpr fun l ↦ ha k l
    have hM := ((M k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hv
    exact (hasDerivWithinAt_pi.mp hM) i
  intro j
  induction j with
  | zero => exact fun ha ↦ ⟨hcont ha.1, hrapid ha.2⟩
  | succ j ih =>
    intro a s ha
    obtain ⟨hb, a', ha', hj⟩ := ha
    exact ⟨⟨hcont hb.1, hrapid hb.2⟩, fun t q ↦ M q (a' t q),
      fun t ht k i ↦ hderiv (ha' t ht) k i, ih hj⟩

end SmoothRapid

section Convection

variable {S : ℝ}

/-- The convection of two coefficient curves. -/
def convCurve (a b : ℝ → FourierVelocity) : ℝ → FourierVelocity := fun t q ↦ conv (a t) (b t) q

theorem hasDerivWithinAt_modeDot {a a' : ℝ → FourierVelocity} {s : Set ℝ} {t : ℝ}
    (ha : ∀ k i, HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) s t) (q p : Wavevector) :
    HasDerivWithinAt (fun τ ↦ modeDot q (a τ p)) (modeDot q (a' t p)) s t := by
  unfold modeDot
  exact HasDerivWithinAt.fun_sum fun j _ ↦ (ha p j).const_mul _

theorem continuousOn_modeDot {a : ℝ → FourierVelocity} {s : Set ℝ} (ha : ContOn a s)
    (q p : Wavevector) : ContinuousOn (fun τ ↦ modeDot q (a τ p)) s := by
  unfold modeDot
  exact continuousOn_finsetSum _ fun j _ ↦ continuousOn_const.mul (ha p j)

/-- Uniform constants for rapid fields at a given order. -/
theorem RapidOn.bound {a : ℝ → FourierVelocity} {s : Set ℝ} (ha : RapidOn a s) (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ s, ∀ k, fourierMoment n (a t) k ≤ C := by
  obtain ⟨C, hC⟩ := ha n
  exact ⟨max C 0, le_max_right _ _, fun t ht k ↦ (hC t ht k).trans (le_max_left _ _)⟩

/-- A uniform summable envelope for the convection terms of two rapid curves. -/
theorem conv_env {a b : ℝ → FourierVelocity} {s : Set ℝ} (ha : RapidOn a s) (hb : RapidOn b s) :
    ∃ E, 0 ≤ E ∧ ∀ t ∈ s, ∀ q p i, ‖modeDot q (a t p) * b t (q - p) i‖ ≤ E * latticeDecayWeight p := by
  obtain ⟨A, hA0, hA⟩ := ha.bound 5
  obtain ⟨B, hB0, hB⟩ := hb.bound 1
  refine ⟨A * B, mul_nonneg hA0 hB0, fun t ht q p i ↦ ?_⟩
  have h := conv_term_le_env (n := 0) (hA t ht) (hB t ht) hB0 q p i
  simpa using h

theorem conv_base {a b : ℝ → FourierVelocity} {s : Set ℝ} (ha : ContOn a s ∧ RapidOn a s)
    (hb : ContOn b s ∧ RapidOn b s) : ContOn (convCurve a b) s ∧ RapidOn (convCurve a b) s := by
  refine ⟨fun q i ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨E, _, hE⟩ := conv_env ha.2 hb.2
    exact continuousOn_tsum (fun p ↦ (continuousOn_modeDot ha.1 q p).mul (hb.1 (q - p) i))
      (summable_latticeDecayWeight.mul_left E) (fun p t ht ↦ hE t ht q p i)
  · obtain ⟨A, _, hA⟩ := ha.2.bound (n + 5)
    obtain ⟨B, hB0, hB⟩ := hb.2.bound (n + 1)
    exact ⟨3 * (A * B * ∑' p, latticeDecayWeight p), fun t ht q ↦
      fourierMoment_conv_le (hA t ht) (hB t ht) hB0 q⟩

/-- **Product rule for the convection.** -/
theorem conv_hasDerivWithinAt (hS : 0 < S) {a a' b b' : ℝ → FourierVelocity}
    (ha : ContOn a (Icc 0 S) ∧ RapidOn a (Icc 0 S)) (hb : ContOn b (Icc 0 S) ∧ RapidOn b (Icc 0 S))
    (ha' : ContOn a' (Icc 0 S) ∧ RapidOn a' (Icc 0 S))
    (hb' : ContOn b' (Icc 0 S) ∧ RapidOn b' (Icc 0 S))
    (hda : ∀ t ∈ Icc (0 : ℝ) S, ∀ k i, HasDerivWithinAt (fun τ ↦ a τ k i) (a' t k i) (Icc 0 S) t)
    (hdb : ∀ t ∈ Icc (0 : ℝ) S, ∀ k i, HasDerivWithinAt (fun τ ↦ b τ k i) (b' t k i) (Icc 0 S) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) (q : Wavevector) (i : Fin 3) :
    HasDerivWithinAt (fun τ ↦ convCurve a b τ q i)
      (convCurve a' b t q i + convCurve a b' t q i) (Icc 0 S) t := by
  obtain ⟨E₁, hE₁0, hE₁⟩ := conv_env ha'.2 hb.2
  obtain ⟨E₂, hE₂0, hE₂⟩ := conv_env ha.2 hb'.2
  obtain ⟨E₀, _, hE₀⟩ := conv_env ha.2 hb.2
  have hs1 : ∀ τ ∈ Icc (0 : ℝ) S, Summable (fun p ↦ modeDot q (a' τ p) * b τ (q - p) i) :=
    fun τ hτ ↦ (summable_latticeDecayWeight.mul_left E₁).of_norm_bounded fun p ↦ hE₁ τ hτ q p i
  have hs2 : ∀ τ ∈ Icc (0 : ℝ) S, Summable (fun p ↦ modeDot q (a τ p) * b' τ (q - p) i) :=
    fun τ hτ ↦ (summable_latticeDecayWeight.mul_left E₂).of_norm_bounded fun p ↦ hE₂ τ hτ q p i
  have h := hasDerivWithinAt_tsum_Icc (S := S) hS (u := fun p ↦ (E₁ + E₂) * latticeDecayWeight p)
    (g := fun p τ ↦ modeDot q (a τ p) * b τ (q - p) i)
    (g' := fun p τ ↦ modeDot q (a' τ p) * b τ (q - p) i + modeDot q (a τ p) * b' τ (q - p) i)
    (summable_latticeDecayWeight.mul_left _)
    (fun p τ hτ ↦ (hasDerivWithinAt_modeDot (hda τ hτ) q p).mul (hdb τ hτ (q - p) i))
    (fun p ↦ ((continuousOn_modeDot ha'.1 q p).mul (hb.1 (q - p) i)).add
      ((continuousOn_modeDot ha.1 q p).mul (hb'.1 (q - p) i)))
    (fun p τ hτ ↦ (norm_add_le _ _).trans (by
      have := hE₁ τ hτ q p i
      have := hE₂ τ hτ q p i
      nlinarith [latticeDecayWeight_pos p]))
    ((conv_base ha hb).1 q i)
    (fun τ hτ ↦ (summable_latticeDecayWeight.mul_left E₀).of_norm_bounded fun p ↦ hE₀ τ hτ q p i)
    ht
  have hsum : (∑' p, (modeDot q (a' t p) * b t (q - p) i + modeDot q (a t p) * b' t (q - p) i)) =
      convCurve a' b t q i + convCurve a b' t q i :=
    (hs1 t ht).tsum_add (hs2 t ht)
  rw [hsum] at h
  exact h

/-- **The convection preserves the smooth-rapid class.** -/
theorem SmoothRapid.convCurve (hS : 0 < S) : ∀ {j : ℕ} {a b : ℝ → FourierVelocity},
    SmoothRapid j a (Icc 0 S) → SmoothRapid j b (Icc 0 S) →
      SmoothRapid j (FourierTimeRegularity.convCurve a b) (Icc 0 S)
  | 0, _, _, ha, hb => conv_base ha hb
  | j + 1, a, b, ha, hb => by
    have ha0 := ha
    have hb0 := hb
    obtain ⟨hab, a', ha', hja⟩ := ha
    obtain ⟨hbb, b', hb', hjb⟩ := hb
    refine ⟨conv_base hab hbb, fun t q ↦ FourierTimeRegularity.convCurve a' b t q +
      FourierTimeRegularity.convCurve a b' t q, fun t ht q i ↦ ?_, ?_⟩
    · exact conv_hasDerivWithinAt hS hab hbb hja.base hjb.base ha' hb' ht q i
    · exact SmoothRapid.add (SmoothRapid.convCurve hS hja (SmoothRapid.mono hb0))
        (SmoothRapid.convCurve hS (SmoothRapid.mono ha0) hjb)

end Convection

section RightHandSide

theorem lerayMode_add (q : Wavevector) (v w : VelocityCoefficient) :
    lerayMode q (v + w) = lerayMode q v + lerayMode q w := by
  unfold lerayMode
  split_ifs
  · rfl
  · ext i
    simp only [Pi.add_apply, modeDot, mul_add, Finset.sum_add_distrib]
    ring

/-- The Leray-projected phase multiple, as a complex-linear map. -/
def nonlinearMap (q : Wavevector) : VelocityCoefficient →L[ℂ] VelocityCoefficient :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ lerayMode q ((-unitTorusDerivativePhase) • v)
      map_add' := fun v w ↦ by rw [smul_add, lerayMode_add]
      map_smul' := fun c v ↦ by
        rw [RingHom.id_apply, smul_comm, FourierSymmetry.lerayMode_smul] }

/-- The viscous multiplier, as a complex-linear map. -/
def viscousMap (nu : ℝ) (q : Wavevector) : VelocityCoefficient →L[ℂ] VelocityCoefficient :=
  ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • ContinuousLinearMap.id ℂ _

theorem norm_nonlinearMap_le (q : Wavevector) (v : VelocityCoefficient) :
    ‖coefficientVec (nonlinearMap q v)‖ ≤ 2 * Real.pi * (1 + ‖frequencyVec q‖) ^ 0 *
      ‖coefficientVec v‖ := by
  change ‖coefficientVec (lerayMode q ((-unitTorusDerivativePhase) • v))‖ ≤ _
  refine (norm_lerayMode_le q _).trans (le_of_eq ?_)
  have h : coefficientVec ((-unitTorusDerivativePhase) • v) =
      (-unitTorusDerivativePhase) • coefficientVec v := rfl
  rw [h, norm_smul, norm_neg, PancakeIncomingLowSourceEnergy.norm_derivativePhase]
  ring

theorem norm_modeSquare (q : Wavevector) : ‖modeSquare q‖ = ‖frequencyVec q‖ ^ 2 := by
  have hs : modeSquare q = ((∑ i : Fin 3, (q i : ℝ) ^ 2 : ℝ) : ℂ) := by
    simp [modeSquare, sq, Complex.ofReal_sum]
  rw [hs, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_frequencyVec_sq]

theorem norm_viscousMap_le (nu : ℝ) (q : Wavevector) (v : VelocityCoefficient) :
    ‖coefficientVec (viscousMap nu q v)‖ ≤ |nu| * (2 * Real.pi) ^ 2 * (1 + ‖frequencyVec q‖) ^ 2 *
      ‖coefficientVec v‖ := by
  have h : coefficientVec (viscousMap nu q v) =
      ((nu : ℂ) * unitTorusDerivativePhase ^ 2 * modeSquare q) • coefficientVec v := rfl
  rw [h, norm_smul, norm_mul, norm_mul, norm_pow, PancakeIncomingLowSourceEnergy.norm_derivativePhase,
    Complex.norm_real, Real.norm_eq_abs, norm_modeSquare]
  have hq : ‖frequencyVec q‖ ^ 2 ≤ (1 + ‖frequencyVec q‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
  have h0 : 0 ≤ |nu| * (2 * Real.pi) ^ 2 := by positivity
  calc |nu| * (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * ‖coefficientVec v‖
      ≤ |nu| * (2 * Real.pi) ^ 2 * (1 + ‖frequencyVec q‖) ^ 2 * ‖coefficientVec v‖ := by gcongr
    _ = _ := rfl

/-- The right-hand side of the Fourier system along a curve. -/
def rhsCurve (nu : ℝ) (a : ℝ → FourierVelocity) : ℝ → FourierVelocity :=
  fun t q ↦ infiniteVelocityRHS nu (a t) q

theorem rhsCurve_eq (nu : ℝ) (a : ℝ → FourierVelocity) :
    rhsCurve nu a = fun t ↦ (fun q ↦ nonlinearMap q (convCurve a a t q)) +
      (fun q ↦ viscousMap nu q (a t q)) := by
  funext t q
  rfl

/-- **The right-hand side preserves the smooth-rapid class.** -/
theorem SmoothRapid.rhsCurve {S : ℝ} (hS : 0 < S) (nu : ℝ) {j : ℕ} {a : ℝ → FourierVelocity}
    (ha : SmoothRapid j a (Icc 0 S)) : SmoothRapid j (FourierTimeRegularity.rhsCurve nu a) (Icc 0 S) := by
  rw [rhsCurve_eq]
  have h1 := SmoothRapid.map_mode nonlinearMap (K := 2 * Real.pi) (d := 0) (by positivity)
    norm_nonlinearMap_le (SmoothRapid.convCurve hS ha ha)
  have h2 := SmoothRapid.map_mode (viscousMap nu) (K := |nu| * (2 * Real.pi) ^ 2) (d := 2)
    (by positivity) (norm_viscousMap_le nu) ha
  exact SmoothRapid.add h1 h2

end RightHandSide

section Solution

/-- **The one-sided equation at every time.** A coefficient curve that is
continuous, rapidly decaying on `[0, S]` and solves the Fourier system on
`(0, T)` with `S < T` solves it within `[0, S]` at every time of `[0, S]`,
including the initial time. -/
theorem hasDerivWithinAt_of_solution {nu T S : ℝ} (hS : 0 < S) (hST : S < T)
    {c : ℝ → FourierVelocity} (hcont : ∀ k i, Continuous (fun t ↦ c t k i))
    (hrapid : RapidOn c (Icc 0 S))
    (heq : ∀ t ∈ Ioo (0 : ℝ) T, ∀ q i,
      HasDerivAt (fun τ ↦ c τ q i) (infiniteVelocityRHS nu (c t) q i) t) :
    ∀ t ∈ Icc (0 : ℝ) S, ∀ q i, HasDerivWithinAt (fun τ ↦ c τ q i)
      (FourierTimeRegularity.rhsCurve nu c t q i) (Icc 0 S) t := by
  have h0 : SmoothRapid 0 c (Icc 0 S) := ⟨fun k i ↦ (hcont k i).continuousOn, hrapid⟩
  have hrhs0 := SmoothRapid.rhsCurve hS nu h0
  intro t ht q i
  rcases ht.1.eq_or_lt with h | h
  · subst h
    have hd : HasDerivWithinAt (fun τ ↦ c τ q i) (FourierTimeRegularity.rhsCurve nu c 0 q i)
        (Ici 0) 0 := by
      refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo 0 S)
        (fun x hx ↦ (heq x ⟨hx.1, hx.2.trans hST⟩ q i).differentiableAt.differentiableWithinAt)
        (hcont q i).continuousWithinAt (Ioo_mem_nhdsGT hS) ?_
      have hc : ContinuousWithinAt (fun τ ↦ FourierTimeRegularity.rhsCurve nu c τ q i)
          (Icc 0 S) 0 := hrhs0.1 q i 0 ⟨le_rfl, hS.le⟩
      have ht : Tendsto (fun τ ↦ FourierTimeRegularity.rhsCurve nu c τ q i) (𝓝[>] 0)
          (𝓝 (FourierTimeRegularity.rhsCurve nu c 0 q i)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
        exact hc.tendsto.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
      refine ht.congr' ?_
      rw [← nhdsWithin_Ioo_eq_nhdsGT hS]
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact ((heq x ⟨hx.1, hx.2.trans hST⟩ q i).deriv).symm
    exact hd.mono Icc_subset_Ici_self
  · exact (heq t ⟨h, ht.2.trans_lt hST⟩ q i).hasDerivWithinAt

/-- **Time regularity of the solutions.** A coefficient curve that is
continuous, rapidly decaying on `[0, S]` and solves the Fourier system on
`(0, T)` with `S < T` is smooth-rapid of every order on `[0, S]`, one-sidedly at
the initial time. -/
theorem smoothRapid_of_solution {nu T S : ℝ} (hS : 0 < S) (hST : S < T)
    {c : ℝ → FourierVelocity} (hcont : ∀ k i, Continuous (fun t ↦ c t k i))
    (hrapid : RapidOn c (Icc 0 S))
    (heq : ∀ t ∈ Ioo (0 : ℝ) T, ∀ q i,
      HasDerivAt (fun τ ↦ c τ q i) (infiniteVelocityRHS nu (c t) q i) t) :
    ∀ j, SmoothRapid j c (Icc 0 S) := by
  have h0 : SmoothRapid 0 c (Icc 0 S) := ⟨fun k i ↦ (hcont k i).continuousOn, hrapid⟩
  have hder := hasDerivWithinAt_of_solution hS hST hcont hrapid heq
  intro j
  induction j with
  | zero => exact h0
  | succ j ih => exact ⟨h0, FourierTimeRegularity.rhsCurve nu c, hder, SmoothRapid.rhsCurve hS nu ih⟩

end Solution

end Mettapedia.FluidDynamics.NavierStokes.FourierTimeRegularity

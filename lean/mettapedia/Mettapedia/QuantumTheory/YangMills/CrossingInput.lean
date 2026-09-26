import Mettapedia.Combinatorics.PolymerGas.LatticeClustering
import Mettapedia.QuantumTheory.YangMills.FreeMaxwellNonClustering

/-!
# The crossing input for the stopping-scale step

The stopping-scale step of the route needs, at some block scale, an effective
measure that is a hard-core polymer gas over a block-product reference measure,
with activities small in a Kotecký–Preiss norm that carries a positive decay
rate, uniformly in the volume.  `CrossingInput` states exactly this for a family
of block lattices indexed by the volume.  Under it the truncated two-point
function of bounded block observables decays exponentially in the block
distance with constants independent of the volume (`CrossingInput.clustering`).

**Calibration.**  The input cannot hold for a family whose bounded two-point
functions, on block sets of bounded size whose separation eventually grows like
`|k|₁` as the volume grows, converge at each separation `k` to values that
dominate the field-strength two-point function of the free lattice Maxwell field
(`CrossingInput.false_of_tendsto_dominating`): uniform clustering passes to the
limit, and the free field-strength function has no exponential bound
(`FreeMaxwellNonClustering`, in every dimension `d ≥ 3`).  For `0 < t ≤ 1/2` the
expression `e^{-t σ²}(e^{t C(n)} - 1)`, the truncated two-point function of the
phase `e^{i √t F₀₁}` and its conjugate for a centred Gaussian field of covariance
`C`, controls `‖C(n)‖` up to the factor `2 e^{t σ²} / t`, because `‖C(n)‖ ≤ 1`
(`norm_fieldStrengthCorrelation_le_gaussian`).  The Gaussian covariance identity
itself and the `β → ∞` limit that would place weakly coupled four-dimensional
`U(1)` and the abelian components of five-dimensional `SU(2)` in this situation
are not formalized here, nor is the persistence of weak coupling at every scale
at finite coupling (the massless photon, the five-dimensional bulk transition).
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Filter Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.CrossingInput

variable {ι : Type*} (Blocks : ι → Type*) [∀ L, Fintype (Blocks L)]
  [∀ L, DecidableEq (Blocks L)] [∀ L, PseudoMetricSpace (Blocks L)]
  (E : Type*) [MeasurableSpace E] [Nonempty E] (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- The crossing input for a family of block lattices: for every volume `L` the
activities `K L` of the polymer representation over the block-product reference
measure `⊗ ν₀` satisfy the per-block Kotecký–Preiss smallness with a positive
rate, all constants independent of `L`. -/
structure CrossingInput (K : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ) : Prop where
  measurable_activity : ∀ L S, Measurable (K L S)
  exists_bounds : ∃ (bound : ∀ L, Finset (Blocks L) → ℝ) (rate smallness : ℝ),
    0 < rate ∧ 0 ≤ smallness ∧ smallness * Real.exp 1 ≤ 1 ∧
      (∀ L S v, ‖K L S v‖ ≤ bound L S) ∧ (∀ L, bound L ∅ = 0) ∧
      ∀ L, ActivitySmall (bound L) rate smallness

variable {Blocks E ν₀}

/-- **Clustering from the crossing input.**  With constants independent of the
volume, the truncated two-point function of bounded observables on block sets
`S₁`, `S₂` is at most `3 C₁ C₂ e^{3(|S₁|+|S₂|)} e^{-κ d(S₁, S₂)}`. -/
theorem clustering {K : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ}
    (h : CrossingInput Blocks E K) :
    ∃ κ > 0, ∀ (L : ι) (Λ : Finset (Finset (Blocks L))) (S₁ S₂ : Finset (Blocks L)),
      S₁.Nonempty → ∀ (F₁ : (S₁ → E) → ℂ) (F₂ : (S₂ → E) → ℂ) (C₁ C₂ : ℝ),
      Measurable F₁ → Measurable F₂ → (∀ v, ‖F₁ v‖ ≤ C₁) → (∀ v, ‖F₂ v‖ ≤ C₂) →
      ‖expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) (K L) Λ -
          expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω)) (K L) Λ *
            expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) (K L) Λ‖ ≤
        3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
  obtain ⟨bound, rate, smallness, hrate, hs0, hs, hle, hempty, hsmall⟩ := h.exists_bounds
  exact ⟨rate, hrate, fun L Λ S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hF₁b hF₂b =>
    norm_truncated_le_exp ν₀ (K L) (h.measurable_activity L) (bound L) (hle L) (hempty L)
      hrate.le hs0 hs (hsmall L) S₁ S₂ hS₁ F₁ hF₁ C₁ hF₁b F₂ hF₂ C₂ hF₂b Λ⟩

/-! ## Calibration -/

open Mettapedia.QuantumTheory.YangMills.FreeMaxwellNonClustering

/-- For `‖z‖ ≤ 1/2`, `‖z‖ ≤ 2 ‖e^z - 1‖`. -/
theorem norm_le_two_mul_norm_exp_sub_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖z‖ ≤ 2 * ‖Complex.exp z - 1‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := z) (by linarith)
  have hsplit : Complex.exp z - 1 - (Complex.exp z - 1 - z) = z := by ring
  have htri := norm_sub_le (Complex.exp z - 1) (Complex.exp z - 1 - z)
  rw [hsplit] at htri
  have hz2 : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith [norm_nonneg z]
  linarith

/-- **Gaussian domination.**  For `0 < t ≤ 1/2` the Gaussian truncated two-point
function `e^{-t σ²}(e^{t C(k)} - 1)` of the bounded observable `e^{i √t F₀₁}`
dominates the free field-strength two-point function. -/
theorem norm_fieldStrengthCorrelation_le_gaussian {n : ℕ} {t σ2 : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1 / 2) (k : Fin (n + 3) → ℤ) :
    ‖fieldStrengthCorrelation (n := n) k‖ ≤
      (2 * Real.exp (t * σ2) / t) *
        ‖(Real.exp (-(t * σ2)) : ℂ) *
          (Complex.exp ((t : ℂ) * fieldStrengthCorrelation k) - 1)‖ := by
  have hC := norm_fieldStrengthCorrelation_le (n := n) k
  have hz : ‖(t : ℂ) * fieldStrengthCorrelation k‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg (fieldStrengthCorrelation (n := n) k)]
  have h := norm_le_two_mul_norm_exp_sub_one hz
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [div_mul_eq_mul_div, le_div_iff₀ ht]
  have hexp : Real.exp (t * σ2) * Real.exp (-(t * σ2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ‖fieldStrengthCorrelation (n := n) k‖ * t = t * ‖fieldStrengthCorrelation k‖ := by ring
    _ ≤ 2 * ‖Complex.exp ((t : ℂ) * fieldStrengthCorrelation k) - 1‖ := h
    _ = 2 * Real.exp (t * σ2) *
          (Real.exp (-(t * σ2)) * ‖Complex.exp ((t : ℂ) * fieldStrengthCorrelation k) - 1‖) := by
        rw [show 2 * Real.exp (t * σ2) * (Real.exp (-(t * σ2)) *
            ‖Complex.exp ((t : ℂ) * fieldStrengthCorrelation k) - 1‖) =
            2 * (Real.exp (t * σ2) * Real.exp (-(t * σ2))) *
              ‖Complex.exp ((t : ℂ) * fieldStrengthCorrelation k) - 1‖ by ring, hexp, mul_one]

/-- **Calibration.**  No family satisfying the crossing input can have bounded
two-point functions on block sets of bounded size whose separation eventually
grows like `|k|₁` as the volume grows, for each fixed `k`, and whose limits
dominate the free field-strength two-point function. -/
theorem false_of_tendsto_dominating {n : ℕ} {K : ∀ L (S : Finset (Blocks L)), (S → E) → ℂ}
    (h : CrossingInput Blocks E K) {l : Filter ι} [l.NeBot]
    (Λ : ∀ L, Finset (Finset (Blocks L)))
    (S₁ S₂ : ∀ L, (Fin (n + 3) → ℤ) → Finset (Blocks L))
    (hS₁ : ∀ L k, (S₁ L k).Nonempty) (M : ℕ) (hM₁ : ∀ L k, (S₁ L k).card ≤ M)
    (hM₂ : ∀ L k, (S₂ L k).card ≤ M) (α β : ℝ) (hα : 0 < α)
    (hdist : ∀ k, ∀ᶠ L in l, α * ∑ i, |((k i : ℤ) : ℝ)| - β ≤ polymerDist (S₁ L k) (S₂ L k))
    (F₁ : ∀ L k, (S₁ L k → E) → ℂ) (F₂ : ∀ L k, (S₂ L k → E) → ℂ)
    (hF₁ : ∀ L k, Measurable (F₁ L k)) (hF₂ : ∀ L k, Measurable (F₂ L k))
    (hF₁b : ∀ L k v, ‖F₁ L k v‖ ≤ 1) (hF₂b : ∀ L k v, ‖F₂ L k v‖ ≤ 1)
    (T : (Fin (n + 3) → ℤ) → ℂ)
    (hT : ∀ k, Tendsto (fun L =>
      expectation ν₀ (fun ω => F₁ L k (restrictTo (S₁ L k) ω) * F₂ L k (restrictTo (S₂ L k) ω))
          (K L) (Λ L) -
        expectation ν₀ (fun ω => F₁ L k (restrictTo (S₁ L k) ω)) (K L) (Λ L) *
          expectation ν₀ (fun ω => F₂ L k (restrictTo (S₂ L k) ω)) (K L) (Λ L)) l (𝓝 (T k)))
    (A : ℝ) (hA : ∀ k, ‖fieldStrengthCorrelation (n := n) k‖ ≤ A * ‖T k‖) : False := by
  obtain ⟨κ, hκ, hclust⟩ := clustering (ν₀ := ν₀) h
  set K₀ : ℝ := 3 * Real.exp (6 * M + κ * β) with hK₀
  have hbound : ∀ k, ‖T k‖ ≤ K₀ * Real.exp (-(κ * α) * ∑ i, |((k i : ℤ) : ℝ)|) := by
    intro k
    refine le_of_tendsto ((continuous_norm.tendsto _).comp (hT k))
      ((hdist k).mono fun L hd => ?_)
    refine (hclust L (Λ L) (S₁ L k) (S₂ L k) (hS₁ L k) (F₁ L k) (F₂ L k) 1 1 (hF₁ L k)
      (hF₂ L k) (hF₁b L k) (hF₂b L k)).trans ?_
    have hc1 : ((S₁ L k).card : ℝ) ≤ M := by exact_mod_cast hM₁ L k
    have hc2 : ((S₂ L k).card : ℝ) ≤ M := by exact_mod_cast hM₂ L k
    rw [hK₀, mul_one, mul_one, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    nlinarith
  set A' : ℝ := max A 0 with hA'def
  have hA'nn : 0 ≤ A' := le_max_right _ _
  have hA' : ∀ k, ‖fieldStrengthCorrelation (n := n) k‖ ≤ A' * ‖T k‖ := fun k =>
    (hA k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  apply not_exponentialDecay_fieldStrengthCorrelation (n := n) (A' * K₀) (κ * α)
    (mul_pos hκ hα)
  intro k
  calc ‖fieldStrengthCorrelation (n := n) k‖ ≤ A' * ‖T k‖ := hA' k
    _ ≤ A' * (K₀ * Real.exp (-(κ * α) * ∑ i, |((k i : ℤ) : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (hbound k) hA'nn
    _ = A' * K₀ * Real.exp (-(κ * α) * ∑ i, |((k i : ℤ) : ℝ)|) := by ring

#print axioms clustering
#print axioms norm_fieldStrengthCorrelation_le_gaussian
#print axioms false_of_tendsto_dominating

end Mettapedia.QuantumTheory.YangMills.CrossingInput

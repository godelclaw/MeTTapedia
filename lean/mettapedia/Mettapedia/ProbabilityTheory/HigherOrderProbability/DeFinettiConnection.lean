import Mettapedia.ProbabilityTheory.HigherOrderProbability.LatentReuse
import Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
import Mettapedia.ProbabilityTheory.FiniteMeasureSupport
import Exchangeability.Core
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# De Finetti as Kyburg Flattening

This file packages the Bernoulli-mixture model from `Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti` as an instance of
Kyburg's higher-order probability structure (`ParametrizedDistribution`).

The key theorem is the singleton-level identification:

`flatten(pd_M n) {xs} = ENNReal.ofReal (M.prob xs)`.

This is the precise "De Finetti is Kyburg" bridge needed by the higher-order PLN story.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open scoped BigOperators ENNReal _root_.Mettapedia.ProbabilityTheory

open MeasureTheory _root_.Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.FiniteMeasureSupport

namespace DeFinettiConnection

open Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
open Mettapedia.ProbabilityTheory.Exchangeability

/-! ## Parameter space and mixing measure -/

abbrev Theta : Type := Set.Icc (0 : ℝ) 1

lemma measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1) := by
  simp [isClosed_Icc.measurableSet]

@[simp] lemma Theta.coe_mk (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((⟨x, hx⟩ : Theta) : ℝ) = x := rfl

/-- Pull a mixing measure supported on `[0,1]` back to the subtype `Theta = Icc 0 1`. -/
def mixingMeasureTheta (M : BernoulliMixture) : Measure Theta :=
  M.mixingMeasure.comap (fun θ : Theta => (θ : ℝ))

instance mixingMeasureTheta_isProbability (M : BernoulliMixture) :
    IsProbabilityMeasure (mixingMeasureTheta M) := by
  have : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  refine (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap ?_
  simpa only [Subtype.range_val, ae_iff, Set.compl_def] using M.support_unit

private theorem map_mixingMeasureTheta (M : BernoulliMixture) :
    (mixingMeasureTheta M).map (Subtype.val : Theta → ℝ) = M.mixingMeasure := by
  rw [mixingMeasureTheta, (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_comap]
  rw [Subtype.range_val]
  exact Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff, Set.compl_def] using M.support_unit)

/-- If two Bernoulli mixtures induce the same pulled-back measure on
`Theta = [0,1]`, then their original mixing measures on `ℝ` are equal. -/
theorem mixingMeasure_eq_of_mixingMeasureTheta_eq
    (M1 M2 : BernoulliMixture)
    (hΘ : mixingMeasureTheta M1 = mixingMeasureTheta M2) :
    M1.mixingMeasure = M2.mixingMeasure := by
  rw [← map_mixingMeasureTheta M1, hΘ, map_mixingMeasureTheta]

/-- A Bernoulli mixture is determined by its pulled-back mixing measure on
`Theta = [0,1]`. -/
theorem bernoulliMixture_ext_of_mixingMeasureTheta_eq
    (M1 M2 : BernoulliMixture)
    (hΘ : mixingMeasureTheta M1 = mixingMeasureTheta M2) :
    M1 = M2 := by
  have hmix : M1.mixingMeasure = M2.mixingMeasure :=
    mixingMeasure_eq_of_mixingMeasureTheta_eq M1 M2 hΘ
  cases M1 with
  | mk μ1 p1 s1 =>
    cases M2 with
    | mk μ2 p2 s2 =>
      change (BernoulliMixture.mk μ1 p1 s1 = BernoulliMixture.mk μ2 p2 s2)
      have hμ : μ1 = μ2 := by simpa using hmix
      cases hμ
      simp

/-! ## Bernoulli product kernel as a Markov kernel -/

section Kernel

variable {n : ℕ}

private lemma theta_nonneg (θ : Theta) : 0 ≤ (θ : ℝ) := θ.2.1
private lemma theta_le_one (θ : Theta) : (θ : ℝ) ≤ 1 := θ.2.2
private lemma one_sub_theta_nonneg (θ : Theta) : 0 ≤ 1 - (θ : ℝ) :=
  sub_nonneg.2 (theta_le_one θ)

private lemma bernoulliPMF_nonneg (θ : Theta) (b : Bool) :
    0 ≤ bernoulliPMF (θ : ℝ) b := by
  cases b with
  | false =>
      simpa [bernoulliPMF] using one_sub_theta_nonneg (θ := θ)
  | true =>
      simpa [bernoulliPMF] using theta_nonneg (θ := θ)

private lemma bernoulliProduct_bounds (θ : Theta) (xs : Fin n → Bool) :
    bernoulliProductPMF (θ : ℝ) xs ∈ Set.Icc 0 1 := by
  unfold bernoulliProductPMF
  refine ⟨Finset.prod_nonneg (fun i _ => bernoulliPMF_nonneg θ (xs i)),
    Finset.prod_le_one (fun i _ => bernoulliPMF_nonneg θ (xs i)) ?_⟩
  intro i _
  cases xs i <;> simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte] <;>
    linarith [θ.2.1, θ.2.2]

/-- The `ENNReal` weight of a word `xs` under a parameter `θ`. -/
def weight (θ : Theta) (xs : Fin n → Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs)

private lemma weight_cons (θ : Theta) (b : Bool) (xs : Fin n → Bool) :
    weight (n := n + 1) θ (Fin.cons b xs) =
      ENNReal.ofReal (bernoulliPMF (θ : ℝ) b) * weight (n := n) θ xs := by
  classical
  -- Split the product on `Fin (n+1)` into head and tail.
  have hprod :
      bernoulliProductPMF (θ : ℝ) (Fin.cons b xs) =
        bernoulliPMF (θ : ℝ) b * bernoulliProductPMF (θ : ℝ) xs := by
    unfold bernoulliProductPMF
    -- `Fin.prod_univ_succ` isolates the `0`-th coordinate.
    simpa using
      (Fin.prod_univ_succ (n := n)
        (f := fun i : Fin (n + 1) =>
          bernoulliPMF (θ : ℝ) ((Fin.cons b xs : Fin (n + 1) → Bool) i)))
  -- Move `ENNReal.ofReal` across multiplication; the head factor is nonnegative on `Theta`.
  have hnonneg : 0 ≤ bernoulliPMF (θ : ℝ) b := bernoulliPMF_nonneg (θ := θ) b
  simp [weight, hprod, ENNReal.ofReal_mul hnonneg]

private lemma ofReal_bernoulliPMF_add (θ : Theta) :
    ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) + ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) = 1 := by
  rw [← ENNReal.ofReal_add (bernoulliPMF_nonneg θ true) (bernoulliPMF_nonneg θ false)]
  simp [bernoulliPMF]

private lemma sum_weight_eq_one (n : ℕ) (θ : Theta) :
    (∑ xs : Fin n → Bool, weight (n := n) θ xs) = 1 := by
  classical
  have hweight (xs : Fin n → Bool) :
      weight θ xs = ∏ i, ENNReal.ofReal (bernoulliPMF (θ : ℝ) (xs i)) :=
    ENNReal.ofReal_prod_of_nonneg (fun i _ => bernoulliPMF_nonneg θ (xs i))
  have hnorm : (∑ b : Bool, ENNReal.ofReal (bernoulliPMF (θ : ℝ) b)) = 1 := by
    simpa [Fintype.sum_bool, add_comm] using ofReal_bernoulliPMF_add θ
  simp_rw [hweight]
  rw [← Fintype.prod_sum (fun _ : Fin n => fun b : Bool => ENNReal.ofReal (bernoulliPMF (θ : ℝ) b))]
  simp only [hnorm, Finset.prod_const_one]

/-- The `PMF` on `Fin n → Bool` induced by `theta`. -/
def pmf (θ : Theta) : PMF (Fin n → Bool) :=
  PMF.ofFintype (weight (n := n) θ) (sum_weight_eq_one (n := n) θ)

@[simp] lemma pmf_apply (θ : Theta) (xs : Fin n → Bool) :
    pmf (n := n) θ xs = weight (n := n) θ xs := by
  simp [pmf]

@[simp] lemma pmf_toMeasure_apply_singleton (θ : Theta) (xs : Fin n → Bool) :
    (pmf (n := n) θ).toMeasure {xs} = weight (n := n) θ xs := by
  simp [pmf]

/-- Appending Boolean prefixes factorizes the fixed-parameter Bernoulli-product
weights into prefix and suffix weights. -/
theorem weight_append (θ : Theta) {m n : ℕ}
    (xs : Fin m → Bool) (ys : Fin n → Bool) :
    weight (n := m + n) θ (Fin.append xs ys) =
      weight (n := m) θ xs * weight (n := n) θ ys := by
  have hxs : 0 ≤ bernoulliProductPMF (θ : ℝ) xs := by
    rw [bernoulliProductPMF_eq_power]
    exact mul_nonneg (pow_nonneg (theta_nonneg θ) _) (pow_nonneg (one_sub_theta_nonneg θ) _)
  have hsplit :
      bernoulliProductPMF (θ : ℝ) (Fin.append xs ys) =
        bernoulliProductPMF (θ : ℝ) xs * bernoulliProductPMF (θ : ℝ) ys := by
    rw [bernoulliProductPMF_eq_power, bernoulliProductPMF_eq_power,
      bernoulliProductPMF_eq_power, countTrue_append_fin, countFalse_append_fin,
      pow_add, pow_add]
    ring
  rw [weight, weight, weight, hsplit, ENNReal.ofReal_mul hxs]

/-- Truncating a fixed-parameter Bernoulli-product law to a shorter prefix
recovers the shorter fixed-parameter law exactly. -/
theorem pmf_map_takePrefix_eq (θ : Theta) {m n : ℕ} (hmn : m ≤ n) :
    PMF.map (Exchangeability.takePrefix (α := Bool) hmn) (pmf (n := n) θ) =
      pmf (n := m) θ := by
  classical
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h_eq : hmn = Nat.le_add_right m d := by
    apply Subsingleton.elim
  cases h_eq
  ext xs
  rw [PMF.map_apply, tsum_fintype]
  let g : (Fin (m + d) → Bool) → ℝ≥0∞ := fun ys =>
    if xs = Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d) ys
    then pmf (n := m + d) θ ys else 0
  have hg :
      (∑ b : Fin (m + d) → Bool,
        if xs = Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d) b
        then pmf (n := m + d) θ b else 0) =
      ∑ ys : Fin (m + d) → Bool, g ys := by
    rfl
  have hsum :
      (∑ ys : Fin (m + d) → Bool, g ys) =
        ∑ p : (Fin m → Bool) × (Fin d → Bool), g (Fin.append p.1 p.2) := by
    simpa [g] using
      (Fintype.sum_equiv (Fin.appendEquiv (α := Bool) m d)
        (fun p : (Fin m → Bool) × (Fin d → Bool) => g (Fin.append p.1 p.2))
        g (fun _ => rfl)).symm
  have hinner :
      ∀ p : Fin m → Bool,
        (∑ q : Fin d → Bool, g (Fin.append p q)) =
          if xs = p then pmf (n := m) θ p else 0 := by
    intro p
    by_cases hxp : xs = p
    · rw [if_pos hxp]
      calc
        ∑ q : Fin d → Bool, g (Fin.append p q)
            = ∑ q : Fin d → Bool, pmf (n := m + d) θ (Fin.append p q) := by
                apply Finset.sum_congr rfl
                intro q _hq
                have hprefix :
                    Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d)
                        (Fin.append p q) = p := by
                  ext i
                  simp [Exchangeability.takePrefix]
                simp [g, hprefix, hxp]
        _ = ∑ q : Fin d → Bool,
              weight (n := m) θ p * weight (n := d) θ q := by
                apply Finset.sum_congr rfl
                intro q _hq
                rw [pmf_apply, weight_append]
        _ = weight (n := m) θ p * ∑ q : Fin d → Bool, weight (n := d) θ q := by
                simpa using
                  (Finset.mul_sum (s := (Finset.univ : Finset (Fin d → Bool)))
                    (f := fun q : Fin d → Bool => weight (n := d) θ q)
                    (a := weight (n := m) θ p)).symm
        _ = weight (n := m) θ p := by simp [sum_weight_eq_one]
        _ = pmf (n := m) θ p := by rw [pmf_apply]
    · have hgzero : ∀ q : Fin d → Bool, g (Fin.append p q) = 0 := by
        intro q
        have hprefix :
            Exchangeability.takePrefix (α := Bool) (Nat.le_add_right m d)
                (Fin.append p q) = p := by
          ext i
          simp [Exchangeability.takePrefix]
        simp [g, hprefix, hxp]
      simp [hxp, hgzero]
  have houter :
      (∑ p : Fin m → Bool, if xs = p then pmf (n := m) θ p else 0) =
        pmf (n := m) θ xs := by
    rw [Finset.sum_eq_single xs]
    · simp
    · intro p _hp hpx
      have hneq : xs ≠ p := by
        intro h
        exact hpx h.symm
      simp [hneq]
    · intro hxs
      exact (hxs (Finset.mem_univ xs)).elim
  have hmain :
      (∑ ys : Fin (m + d) → Bool, g ys) = pmf (n := m) θ xs := by
    calc
      ∑ ys : Fin (m + d) → Bool, g ys
          = ∑ p : (Fin m → Bool) × (Fin d → Bool), g (Fin.append p.1 p.2) := hsum
      _ = ∑ p : Fin m → Bool, ∑ q : Fin d → Bool, g (Fin.append p q) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ p : Fin m → Bool, if xs = p then pmf (n := m) θ p else 0 := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact hinner p
      _ = pmf (n := m) θ xs := houter
  simpa [g] using hmain

/-- The fixed-parameter Bernoulli-product measure truncates exactly to the
shorter fixed-parameter prefix measure. -/
theorem pmf_toMeasure_map_takePrefix_eq (θ : Theta) {m n : ℕ} (hmn : m ≤ n) :
    Measure.map (Exchangeability.takePrefix (α := Bool) hmn)
      ((pmf (n := n) θ).toMeasure) =
    (pmf (n := m) θ).toMeasure := by
  simpa [pmf_map_takePrefix_eq (θ := θ) hmn] using
    (PMF.toMeasure_map (f := Exchangeability.takePrefix (α := Bool) hmn)
      (p := pmf (n := n) θ)
      (hf := Exchangeability.takePrefix_measurable (α := Bool) hmn))

private lemma measurable_weight (xs : Fin n → Bool) :
    Measurable fun θ : Theta => weight (n := n) θ xs := by
  unfold weight bernoulliProductPMF
  refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ => ?_)
  cases xs i <;> simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte]
  · exact measurable_const.sub measurable_subtype_coe
  · exact measurable_subtype_coe

private lemma measurable_pmf_toMeasure_apply (s : Set (Fin n → Bool)) :
    Measurable fun θ : Theta => (pmf (n := n) θ).toMeasure s := by
  classical
  have h : (fun θ : Theta => (pmf (n := n) θ).toMeasure s) =
      fun θ => ∑ xs, if xs ∈ s then weight θ xs else 0 := by
    funext θ
    simp [PMF.toMeasure_apply_fintype, pmf_apply, Set.indicator]
  rw [h]
  refine Finset.measurable_fun_sum _ fun xs _ => ?_
  by_cases hx : xs ∈ s <;> simp [hx, measurable_weight]

/-- The Bernoulli product kernel on `Theta` at horizon `n`. -/
def kernel (n : ℕ) : ProbabilityTheory.Kernel Theta (Fin n → Bool) :=
  { toFun := fun θ => (pmf (n := n) θ).toMeasure
    measurable' := by
      -- Use the characterization of measurability of `Measure`-valued functions.
      refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
      intro s _hs
      exact measurable_pmf_toMeasure_apply (n := n) s }

instance kernel_isMarkov (n : ℕ) : ProbabilityTheory.IsMarkovKernel (kernel (n := n)) := by
  classical
  refine ⟨fun θ => ?_⟩
  -- `PMF.toMeasure` is a probability measure.
  simpa [kernel] using (show IsProbabilityMeasure ((pmf (n := n) θ).toMeasure) from (by infer_instance))

end Kernel

/-! ## Packaging as a Kyburg parametrized distribution -/

/-- The Kyburg parametrized distribution corresponding to a Bernoulli mixture at horizon `n`. -/
def pd (M : BernoulliMixture) (n : ℕ) :
    ParametrizedDistribution Theta (Fin n → Bool) :=
  { kernel := kernel (n := n)
    kernel_isMarkov := kernel_isMarkov (n := n)
    mixingMeasure := mixingMeasureTheta M
    mixing_isProbability := inferInstance }

/-- Truncating the Kyburg/de Finetti flattened finite prefix law to a shorter
prefix recovers the shorter flattened law. -/
theorem flatten_map_takePrefix_eq (M : BernoulliMixture) {m n : ℕ} (hmn : m ≤ n) :
    Measure.map (Exchangeability.takePrefix (α := Bool) hmn)
      (ParametrizedDistribution.flatten (pd M n)) =
    ParametrizedDistribution.flatten (pd M m) := by
  ext s hs
  rw [Measure.map_apply (Exchangeability.takePrefix_measurable (α := Bool) hmn) hs]
  rw [ParametrizedDistribution.flatten_apply (pd M n)
    ((Exchangeability.takePrefix (α := Bool) hmn) ⁻¹' s)
    ((Exchangeability.takePrefix_measurable (α := Bool) hmn) hs)]
  rw [ParametrizedDistribution.flatten_apply (pd M m) s hs]
  apply lintegral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro θ
  have hθ := congrArg (fun μ : Measure (Fin m → Bool) => μ s)
    (pmf_toMeasure_map_takePrefix_eq (θ := θ) hmn)
  simpa [Measure.map_apply (Exchangeability.takePrefix_measurable (α := Bool) hmn) hs,
    pd, kernel] using hθ

/-! ## Main bridge lemma -/

theorem flatten_apply_singleton (M : BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    (ParametrizedDistribution.flatten (pd M n)) {xs}
      = ENNReal.ofReal (M.prob xs) := by
  classical
  -- Expand `flatten` as a `lintegral` of singleton masses.
  have hmeas : MeasurableSet ({xs} : Set (Fin n → Bool)) := by simp
  have hflat :
      (ParametrizedDistribution.flatten (pd M n)) {xs} =
        ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := by
    -- `flatten_apply` + the explicit kernel gives the desired integrand.
    simpa [pd, kernel, pmf_toMeasure_apply_singleton, pmf, weight] using
      (ParametrizedDistribution.flatten_apply (pd M n) {xs} hmeas)
  -- Reduce the subtype integral to a set-lintegral on `ℝ`.
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
  -- The integrand is `ENNReal.ofReal (bernoulliProductPMF θ xs)`.
  -- `lintegral_subtype_comap` converts `Θ`-integral with `comap` to a set integral.
  have hsub :
      (∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := by
    -- `mixingMeasureTheta` is `comap (↑)`.
    simpa [mixingMeasureTheta, hs] using
      (MeasureTheory.lintegral_subtype_comap (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1) hs
        (f := fun t : ℝ => ENNReal.ofReal (bernoulliProductPMF t xs)))
  have : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  have hcont : Continuous fun t : ℝ => bernoulliProductPMF t xs := by
    unfold bernoulliProductPMF
    refine continuous_finsetProd _ fun i _ => ?_
    cases xs i <;> simp only [bernoulliPMF, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hbounds : ∀ᵐ t ∂M.mixingMeasure.restrict (Set.Icc 0 1),
      bernoulliProductPMF t xs ∈ Set.Icc 0 1 :=
    ae_restrict_of_forall_mem measurableSet_Icc fun t ht => bernoulliProduct_bounds ⟨t, ht⟩ xs
  have hint := (memLp_of_bounded hbounds
    hcont.measurable.aestronglyMeasurable 1).integrable (by simp)
  have hnonneg := hbounds.mono fun _ ht => ht.1
  have hconv :
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure =
        ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := by
    -- Apply `ofReal_integral_eq_lintegral_ofReal` to the restricted measure.
    -- Then rewrite the integrals-on-sets as integrals w.r.t. `restrict` (definitionally).
    have h :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))
        (f := fun t : ℝ => bernoulliProductPMF t xs) hint hnonneg)
    simpa using h.symm
  -- Put everything together.
  calc
    (ParametrizedDistribution.flatten (pd M n)) {xs}
        = ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := hflat
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := hsub
    _ = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := hconv
    _ = ENNReal.ofReal (M.prob xs) := by simp [BernoulliMixture.prob]

/-! ## Finite-prefix probability laws -/

/-- Bernoulli-mixture finite-prefix probabilities are nonnegative.  The proof is
the analytic integral fact: on the support interval `[0,1]`, every Bernoulli
product factor is nonnegative. -/
theorem bernoulliMixture_prob_nonneg
    (M : BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    0 ≤ M.prob xs := by
  apply integral_nonneg_of_ae
  exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
    (bernoulliProduct_bounds ⟨t, ht⟩ xs).1

/-- Bernoulli-mixture finite-prefix probabilities sum to one.  This packages
the finite product normalization from `pmf`/`sum_weight_eq_one` through
Kyburg flattening: the flattened measure is a probability measure, and finite
singletons partition the prefix space. -/
theorem bernoulliMixture_prob_total
    (M : BernoulliMixture) (n : ℕ) :
    ∑ xs : (Fin n → Bool), M.prob xs = 1 := by
  classical
  have hnonneg := fun xs : Fin n → Bool => bernoulliMixture_prob_nonneg M n xs
  have hsum : (∑ xs : Fin n → Bool, ENNReal.ofReal (M.prob xs)) = 1 := by
    simp_rw [← flatten_apply_singleton M n]
    rw [← finiteMeasure_univ_eq_sum_singletons]
    exact measure_univ
  rw [← ENNReal.ofReal_sum_of_nonneg (fun xs _ => hnonneg xs)] at hsum
  simpa [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun xs _ => hnonneg xs))] using
    congrArg ENNReal.toReal hsum

/-! ## One-step observations do not determine shared-parameter executions -/

open ParametrizedDistribution
open scoped _root_.ProbabilityTheory

/-- The original length-one Bernoulli kernel, observed at its only coordinate. -/
def oneStepKernel : _root_.ProbabilityTheory.Kernel Theta Bool :=
  (kernel 1).map (fun xs => xs 0)

instance oneStepKernel_isMarkov : _root_.ProbabilityTheory.IsMarkovKernel oneStepKernel :=
  _root_.ProbabilityTheory.Kernel.IsMarkovKernel.map _ (measurable_pi_apply 0)

@[simp] theorem oneStepKernel_singleton (θ : Theta) (b : Bool) :
    oneStepKernel θ {b} = ENNReal.ofReal (bernoulliPMF (θ : ℝ) b) := by
  rw [oneStepKernel, _root_.ProbabilityTheory.Kernel.map_apply' _ (measurable_pi_apply 0) _
    (measurableSet_singleton b)]
  have hp : (fun xs : Fin 1 → Bool => xs 0) ⁻¹' {b} = {fun _ => b} := by
    ext xs
    exact ⟨fun h => funext fun i => (congrArg xs (Subsingleton.elim i 0)).trans h,
      fun h => congrFun h 0⟩
  rw [hp]
  simp [kernel, weight, bernoulliProductPMF]

def half : Theta := ⟨1 / 2, by norm_num⟩
def zero : Theta := ⟨0, by norm_num⟩
def one : Theta := ⟨1, by norm_num⟩

/-- A fresh fair coin versus a persistent choice of a deterministic coin. -/
def endpointMixing : Measure Theta :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac zero + (1 / 2 : ℝ≥0∞) • Measure.dirac one

instance endpointMixing_isProbability : IsProbabilityMeasure endpointMixing := by
  constructor
  norm_num [endpointMixing, ENNReal.inv_two_add_inv_two]

def coinExperiment (μ : Measure Theta) [IsProbabilityMeasure μ] :
    ParametrizedDistribution Theta Bool := ⟨oneStepKernel, inferInstance, μ, inferInstance⟩

theorem same_oneStep_marginal :
    flatten (coinExperiment (Measure.dirac half)) = flatten (coinExperiment endpointMixing) := by
  apply Measure.ext_of_singleton
  intro b
  rw [flatten_apply _ _ (measurableSet_singleton b),
    flatten_apply _ _ (measurableSet_singleton b)]
  simp only [coinExperiment, oneStepKernel_singleton]
  cases b <;> norm_num [endpointMixing, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac', bernoulliPMF, half, zero, one, ENNReal.ofReal_div_of_pos]

theorem fixed_half_shared_eq_fresh :
    sharedPair (coinExperiment (Measure.dirac half)) =
      freshPair (coinExperiment (Measure.dirac half)) := by
  change (Measure.dirac half).bind (oneStepKernel ×ₖ oneStepKernel) =
    ((Measure.dirac half).bind oneStepKernel).prod ((Measure.dirac half).bind oneStepKernel)
  rw [Measure.dirac_bind (oneStepKernel ×ₖ oneStepKernel).measurable,
    Measure.dirac_bind oneStepKernel.measurable, _root_.ProbabilityTheory.Kernel.prod_apply]

theorem half_pair_probability :
    freshPair (coinExperiment (Measure.dirac half)) ({true} ×ˢ {true}) = 1 / 4 := by
  rw [freshPair_apply_prod, flatten_apply _ _ (measurableSet_singleton true)]
  norm_num [coinExperiment, oneStepKernel_singleton, bernoulliPMF, half, lintegral_dirac', ENNReal.ofReal_div_of_pos, ← ENNReal.mul_inv]

theorem endpoint_shared_true_true :
    sharedPair (coinExperiment endpointMixing) ({true} ×ˢ {true}) = 1 / 2 := by
  rw [sharedPair_apply_prod _ (measurableSet_singleton true) (measurableSet_singleton true)]
  norm_num [coinExperiment, oneStepKernel_singleton, endpointMixing,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac', bernoulliPMF, zero, one]

theorem endpoint_fresh_true_true :
    freshPair (coinExperiment endpointMixing) ({true} ×ˢ {true}) = 1 / 4 := by
  rw [freshPair, ← same_oneStep_marginal]
  exact half_pair_probability

theorem endpoint_shared_true_false :
    sharedPair (coinExperiment endpointMixing) ({true} ×ˢ {false}) = 0 := by
  rw [sharedPair_apply_prod _ (measurableSet_singleton true) (measurableSet_singleton false)]
  norm_num [coinExperiment, oneStepKernel_singleton, endpointMixing,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac', bernoulliPMF, zero, one]

theorem endpoint_fresh_true_false :
    freshPair (coinExperiment endpointMixing) ({true} ×ˢ {false}) = 1 / 4 := by
  rw [freshPair_apply_prod, ← same_oneStep_marginal,
    flatten_apply _ _ (measurableSet_singleton true),
    flatten_apply _ _ (measurableSet_singleton false)]
  norm_num [coinExperiment, oneStepKernel_singleton, bernoulliPMF, half, lintegral_dirac', ENNReal.ofReal_div_of_pos, ← ENNReal.mul_inv]

/-- The same marginal can come from different shared-parameter execution laws. -/
theorem same_marginal_distinct_shared :
    sharedPair (coinExperiment (Measure.dirac half)) ≠ sharedPair (coinExperiment endpointMixing) := by
  intro h
  have he := congrArg (fun ν : Measure (Bool × Bool) => ν ({true} ×ˢ {true})) h
  rw [fixed_half_shared_eq_fresh, half_pair_probability, endpoint_shared_true_true] at he
  norm_num at he

/-- Pulling an unsupported law back to the parameter interval loses all its mass. -/
theorem unsupported_pullback_zero :
    (Measure.dirac (2 : ℝ)).comap (Subtype.val : Theta → ℝ) = 0 := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Icc).map_comap, Measure.map_zero,
    Subtype.range_val, restrict_dirac]
  norm_num

theorem zero_length_normalized (θ : Theta) : weight (n := 0) θ Fin.elim0 = 1 := by
  simp [weight, bernoulliProductPMF]

end DeFinettiConnection

end Mettapedia.ProbabilityTheory.HigherOrderProbability

import Mettapedia.InformationTheory.ConditionalMutualInformation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Finite risks and quantitative decision comparison

Actions and outcomes are separate carriers. A predictor chooses an action
minimizing its own expected loss; evaluation uses the actual outcome law.
The analytic loss/KL certificate uses exponential convexity and a Gaussian
bound on `cosh`, without identifying general loss with prediction error.
-/

noncomputable section

open Finset Real
open scoped BigOperators

namespace Mettapedia.DecisionTheory

/-- A loss in the unit interval, with action first and outcome second. -/
structure BoundedLoss (Action Outcome : Type*) where
  toFun : Action → Outcome → ℝ
  nonneg : ∀ a x, 0 ≤ toFun a x
  le_one : ∀ a x, toFun a x ≤ 1

instance {A Ω : Type*} : CoeFun (BoundedLoss A Ω) (fun _ => A → Ω → ℝ) :=
  ⟨BoundedLoss.toFun⟩

variable {A Ω : Type*} [Fintype Ω]

def expectedRisk (weights : Ω → ℝ) (loss : BoundedLoss A Ω) (action : A) : ℝ :=
  ∑ x, weights x * loss action x

def IsBayesAction (weights : Ω → ℝ) (loss : BoundedLoss A Ω) (selected : A) : Prop :=
  ∀ action, expectedRisk weights loss selected ≤ expectedRisk weights loss action

theorem expectedRisk_nonneg (weights : Ω → ℝ) (nonneg : ∀ x, 0 ≤ weights x)
    (loss : BoundedLoss A Ω) (a : A) : 0 ≤ expectedRisk weights loss a :=
  sum_nonneg fun x _ => mul_nonneg (nonneg x) (loss.nonneg a x)

theorem expectedRisk_le_mass (weights : Ω → ℝ) (nonneg : ∀ x, 0 ≤ weights x)
    (loss : BoundedLoss A Ω) (a : A) : expectedRisk weights loss a ≤ ∑ x, weights x := by
  exact sum_le_sum fun x _ => (mul_le_mul_of_nonneg_left (loss.le_one a x) (nonneg x)).trans_eq
    (mul_one _)

/-- The exponential moment of the two opposite loss corners is at most one. -/
theorem exp_opposite_corners (a : ℝ) (ha : 0 < a) :
    exp (4 * a / (a + 2) ^ 2) + exp (-(1 + a) * (4 * a / (a + 2) ^ 2)) ≤ 2 := by
  let t := 4 * a / (a + 2) ^ 2
  have denominator : a + 2 ≠ 0 := by linarith
  have exponent : -a * t / 2 + ((a + 2) * t / 2) ^ 2 / 2 = 0 := by
    dsimp [t]
    field_simp
    ring
  have representation : (exp t + exp (-(1 + a) * t)) / 2 =
      exp (-a * t / 2) * cosh ((a + 2) * t / 2) := by
    have first : exp t = exp (-a * t / 2) * exp ((a + 2) * t / 2) := by
      rw [← exp_add]; congr 1; ring
    have second : exp (-(1 + a) * t) = exp (-a * t / 2) * exp (-((a + 2) * t / 2)) := by
      rw [← exp_add]; congr 1; ring
    rw [first, second, cosh_eq]
    ring
  have bound : exp (-a * t / 2) * cosh ((a + 2) * t / 2) ≤ 1 := by
    calc
      _ ≤ exp (-a * t / 2) * exp (((a + 2) * t / 2) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (cosh_le_exp_half_sq _) (exp_pos _).le
      _ = 1 := by rw [← exp_add, exponent, exp_zero]
  linarith [representation]

/-- Convex interpolation over the square of two bounded losses. -/
theorem exp_loss_corners (u v t a : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    exp ((v - (1 + a) * u) * t) ≤
      (1 - u) * (1 - v) + (1 - u) * v * exp t +
        u * (1 - v) * exp (-(1 + a) * t) + u * v * exp (-a * t) := by
  have first := convexOn_exp.2 (Set.mem_univ (v * t))
    (Set.mem_univ ((v - (1 + a)) * t)) (sub_nonneg.mpr hu.2) hu.1
    (by ring : (1 - u) + u = 1)
  have second := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
    (sub_nonneg.mpr hv.2) hv.1 (by ring : (1 - v) + v = 1)
  have third := convexOn_exp.2 (Set.mem_univ (-(1 + a) * t)) (Set.mem_univ (-a * t))
    (sub_nonneg.mpr hv.2) hv.1 (by ring : (1 - v) + v = 1)
  simp only [smul_eq_mul] at first second third
  have one : (1 - u) * (v * t) + u * ((v - (1 + a)) * t) =
      (v - (1 + a) * u) * t := by ring
  have two : (1 - v) * 0 + v * t = v * t := by ring
  have three : (1 - v) * (-(1 + a) * t) + v * (-a * t) = (v - (1 + a)) * t := by ring
  rw [one] at first
  rw [two, exp_zero] at second
  rw [three] at third
  calc
    _ ≤ (1 - u) * exp (v * t) + u * exp ((v - (1 + a)) * t) := first
    _ ≤ (1 - u) * ((1 - v) * 1 + v * exp t) +
        u * ((1 - v) * exp (-(1 + a) * t) + v * exp (-a * t)) :=
      add_le_add (mul_le_mul_of_nonneg_left second (sub_nonneg.mpr hu.2))
        (mul_le_mul_of_nonneg_left third hu.1)
    _ = _ := by ring

/-- Model optimality controls an exponential moment of actual loss contrasts. -/
theorem exp_risk_moment (q : Ω → ℝ) (hq : ∀ x, 0 ≤ q x)
    (loss : BoundedLoss A Ω) (selected comparison : A)
    (best : expectedRisk q loss selected ≤ expectedRisk q loss comparison)
    (a : ℝ) (ha : 0 < a) :
    (∑ x, q x * exp ((loss selected x - (1 + a) * loss comparison x) *
      (4 * a / (a + 2) ^ 2))) ≤ ∑ x, q x := by
  let t := 4 * a / (a + 2) ^ 2
  let up := ∑ x, q x * (1 - loss comparison x) * loss selected x
  let down := ∑ x, q x * loss comparison x * (1 - loss selected x)
  let both := ∑ x, q x * loss comparison x * loss selected x
  have ht : 0 < t := by dsimp [t]; positivity
  have hup : 0 ≤ up := sum_nonneg fun x _ => mul_nonneg
    (mul_nonneg (hq x) (sub_nonneg.mpr (loss.le_one comparison x))) (loss.nonneg selected x)
  have hboth : 0 ≤ both := sum_nonneg fun x _ =>
    mul_nonneg (mul_nonneg (hq x) (loss.nonneg comparison x)) (loss.nonneg selected x)
  have gap : up - down = expectedRisk q loss selected - expectedRisk q loss comparison := by
    simp only [up, down, expectedRisk, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  have hupdown : up ≤ down := by linarith
  have corner := exp_opposite_corners a ha
  have negative : exp (-(1 + a) * t) ≤ 1 :=
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  have shared : exp (-a * t) ≤ 1 :=
    exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.le)
  have interpolation := sum_le_sum (s := (univ : Finset Ω)) fun x _ =>
    mul_le_mul_of_nonneg_left
      (exp_loss_corners (loss comparison x) (loss selected x) t a
        ⟨loss.nonneg _ _, loss.le_one _ _⟩ ⟨loss.nonneg _ _, loss.le_one _ _⟩) (hq x)
  have expansion : (∑ x, q x * ((1 - loss comparison x) * (1 - loss selected x) +
      (1 - loss comparison x) * loss selected x * exp t +
      loss comparison x * (1 - loss selected x) * exp (-(1 + a) * t) +
      loss comparison x * loss selected x * exp (-a * t))) =
      (∑ x, q x) + up * (exp t - 1) + down * (exp (-(1 + a) * t) - 1) +
        both * (exp (-a * t) - 1) := by
    simp only [up, down, both, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [expansion] at interpolation
  have paired := mul_nonpos_of_nonneg_of_nonpos hup
    (show exp t + exp (-(1 + a) * t) - 2 ≤ 0 by linarith)
  have residual := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hupdown)
    (sub_nonpos.mpr negative)
  have common := mul_nonpos_of_nonneg_of_nonpos hboth (sub_nonpos.mpr shared)
  nlinarith

open Mettapedia.InformationTheory.FiniteRV

/-- Finite Gibbs inequality with an explicitly bounded exponential tilt. -/
theorem expect_le_kl_of_exp_moment (p q : Ω → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hq : ∀ x, 0 ≤ q x) (total : ∑ x, p x = 1)
    (support : ∀ x, 0 < p x → 0 < q x) (f : Ω → ℝ)
    (moment : ∑ x, q x * exp (f x) ≤ 1) :
    (∑ x, p x * f x) ≤ klSum p q := by
  have gibbs := klSumOn_nonneg univ p (fun x => q x * exp (f x))
    (fun x _ => hp x) (fun x _ => mul_nonneg (hq x) (exp_pos _).le)
    (fun x _ hx => mul_pos (support x hx) (exp_pos _)) (by simpa [total] using moment)
  have term (x : Ω) : p x * log (p x / (q x * exp (f x))) =
      p x * log (p x / q x) - p x * f x := by
    by_cases zero : p x = 0
    · simp [zero]
    · have positive : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm zero)
      rw [div_mul_eq_div_div, log_div (div_pos positive (support x positive)).ne'
        (exp_pos _).ne', log_exp]
      ring
  simp only [klSumOn, term, sum_sub_distrib] at gibbs
  change _ ≤ ∑ x, p x * log (p x / q x)
  linarith

/-- A loss-optimal model action has a sharp linear loss/KL tradeoff. -/
theorem risk_kl_tradeoff (p q : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (p_total : ∑ x, p x = 1) (q_total : ∑ x, q x ≤ 1)
    (support : ∀ x, 0 < p x → 0 < q x) (loss : BoundedLoss A Ω)
    (selected comparison : A) (best : expectedRisk q loss selected ≤ expectedRisk q loss comparison)
    (a : ℝ) (ha : 0 < a) :
    expectedRisk p loss selected ≤ (1 + a) * expectedRisk p loss comparison +
      ((a + 2) ^ 2 / (4 * a)) * klSum p q := by
  let t := 4 * a / (a + 2) ^ 2
  have moment := (exp_risk_moment q hq loss selected comparison best a ha).trans q_total
  have bound := expect_le_kl_of_exp_moment p q hp hq p_total support
    (fun x => (loss selected x - (1 + a) * loss comparison x) * t) moment
  have expression : (∑ x, p x * ((loss selected x - (1 + a) * loss comparison x) * t)) =
      t * (expectedRisk p loss selected - (1 + a) * expectedRisk p loss comparison) := by
    simp only [expectedRisk, mul_sub, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [expression] at bound
  have inverse : ((a + 2) ^ 2 / (4 * a)) * t = 1 := by
    dsimp [t]
    field_simp
  have scaled := mul_le_mul_of_nonneg_left bound
    (show 0 ≤ (a + 2) ^ 2 / (4 * a) by positivity)
  rw [← mul_assoc, inverse, one_mul] at scaled
  linarith

/-- Optimize the common tradeoff, including zero loss and zero divergence. -/
theorem sharp_of_tradeoff (actual optimal divergence : ℝ) (loss_nonneg : 0 ≤ optimal)
    (div_nonneg : 0 ≤ divergence)
    (tradeoff : ∀ a : ℝ, 0 < a → actual ≤ (1 + a) * optimal +
      ((a + 2) ^ 2 / (4 * a)) * divergence) :
    actual - optimal ≤ divergence + sqrt (4 * optimal * divergence + divergence ^ 2) := by
  by_cases zero : divergence = 0
  · simp [zero] at tradeoff ⊢
    by_cases loss_zero : optimal = 0
    · simpa [loss_zero] using tradeoff 1 (by norm_num)
    · by_contra positive
      have hgap : 0 < actual - optimal := sub_pos.mpr (lt_of_not_ge positive)
      have hloss : 0 < optimal := lt_of_le_of_ne loss_nonneg (Ne.symm loss_zero)
      have small := tradeoff ((actual - optimal) / (2 * optimal)) (by positivity)
      have cancellation : ((actual - optimal) / (2 * optimal)) * optimal =
          (actual - optimal) / 2 := by field_simp
      nlinarith
  · have hd : 0 < divergence := lt_of_le_of_ne div_nonneg (Ne.symm zero)
    let r := sqrt (4 * optimal * divergence + divergence ^ 2)
    have radicand : 0 < 4 * optimal * divergence + divergence ^ 2 := by positivity
    have hr : 0 < r := sqrt_pos.mpr radicand
    have square : r ^ 2 = 4 * optimal * divergence + divergence ^ 2 := sq_sqrt radicand.le
    let a := 2 * divergence / r
    have ha : 0 < a := by dsimp [a]; positivity
    have bound := tradeoff a ha
    have coefficient : (a + 2) ^ 2 / (4 * a) = 1 + a / 4 + 1 / a := by
      field_simp
      ring
    have first : a * optimal + (a / 4) * divergence = r / 2 := by
      dsimp [a]
      field_simp
      nlinarith
    have second : divergence / a = r / 2 := by
      dsimp [a]
      field_simp
    have optimized : (1 + a) * optimal + ((a + 2) ^ 2 / (4 * a)) * divergence =
        optimal + divergence + r := by
      calc
        _ = optimal + divergence + (a * optimal + (a / 4) * divergence) + divergence / a := by
          rw [coefficient]; ring
        _ = _ := by rw [first, second]; ring
    rw [optimized] at bound
    linarith

theorem sharp_le_simple (loss divergence : ℝ) (hl : 0 ≤ loss) (hd : 0 ≤ divergence) :
    divergence + sqrt (4 * loss * divergence + divergence ^ 2) ≤
      2 * divergence + 2 * sqrt (loss * divergence) := by
  have root := sqrt_nonneg (loss * divergence)
  have square := sq_sqrt (mul_nonneg hl hd)
  have comparison : sqrt (4 * loss * divergence + divergence ^ 2) ≤
      divergence + 2 * sqrt (loss * divergence) := by
    apply (sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  linarith

theorem risk_regret_le_kl (p q : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (p_total : ∑ x, p x = 1) (q_total : ∑ x, q x ≤ 1)
    (support : ∀ x, 0 < p x → 0 < q x) (loss : BoundedLoss A Ω)
    (selected comparison : A) (best : expectedRisk q loss selected ≤ expectedRisk q loss comparison) :
    expectedRisk p loss selected - expectedRisk p loss comparison ≤
      klSum p q + sqrt (4 * expectedRisk p loss comparison * klSum p q + (klSum p q) ^ 2) :=
  sharp_of_tradeoff _ _ _ (expectedRisk_nonneg p hp loss comparison)
    (klSumOn_nonneg univ p q (fun x _ => hp x) (fun x _ => hq x)
      (fun x _ => support x) (q_total.trans_eq p_total.symm))
    (risk_kl_tradeoff p q hp hq p_total q_total support loss selected comparison best)

/-- Expected-risk regret depends only on the loss contrast, giving the full ℓ¹ bound. -/
theorem risk_regret_le_l1 (p q : Ω → ℝ) (loss : BoundedLoss A Ω) (s m : A)
    (best : expectedRisk q loss s ≤ expectedRisk q loss m) :
    expectedRisk p loss s - expectedRisk p loss m ≤ ∑ x, |p x - q x| := by
  have contrast (x : Ω) : |loss s x - loss m x| ≤ 1 := by
    rw [abs_le]
    have := loss.nonneg s x; have := loss.nonneg m x
    have := loss.le_one s x; have := loss.le_one m x
    constructor <;> linarith
  have identity : expectedRisk p loss s - expectedRisk p loss m -
      (expectedRisk q loss s - expectedRisk q loss m) =
      ∑ x, (p x - q x) * (loss s x - loss m x) := by
    simp only [expectedRisk, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  calc
    _ ≤ expectedRisk p loss s - expectedRisk p loss m -
        (expectedRisk q loss s - expectedRisk q loss m) := by linarith
    _ = _ := identity
    _ ≤ ∑ x, |p x - q x| := sum_le_sum fun x _ => by
      calc
        _ ≤ |(p x - q x) * (loss s x - loss m x)| := le_abs_self _
        _ = |p x - q x| * |loss s x - loss m x| := abs_mul _ _
        _ ≤ |p x - q x| := (mul_le_mul_of_nonneg_left (contrast x) (abs_nonneg _)).trans_eq
          (mul_one _)

/-- The Boolean minimum uses `true` to break ties. -/
def bayesBool (weights : Ω → ℝ) (loss : BoundedLoss Bool Ω) : Bool :=
  decide (expectedRisk weights loss true ≤ expectedRisk weights loss false)

theorem bayesBool_best (weights : Ω → ℝ) (loss : BoundedLoss Bool Ω) :
    IsBayesAction weights loss (bayesBool weights loss) := by
  intro a
  by_cases h : expectedRisk weights loss true ≤ expectedRisk weights loss false
  · have chosen : bayesBool weights loss = true := by simp [bayesBool, h]
    rw [chosen]
    cases a with
    | false => exact h
    | true => exact le_rfl
  · have chosen : bayesBool weights loss = false := by simp [bayesBool, h]
    rw [chosen]
    cases a with
    | false => exact le_rfl
    | true => exact (lt_of_not_ge h).le

/-- Aggregating outcomes preserves every risk when each loss respects the view. -/
theorem risk_pushforward {Observed : Type*} [Fintype Observed] [DecidableEq Observed]
    (weights : Ω → ℝ) (view : Ω → Observed) (source : BoundedLoss A Ω)
    (target : BoundedLoss A Observed) (respects : ∀ a x, target a (view x) = source a x) (a : A) :
    expectedRisk (pushforward weights view) target a = expectedRisk weights source a := by
  rw [expectedRisk, sum_pushforward_mul]
  simp only [expectedRisk, respects]

/-- Point masses show that exact risk preservation requires loss-respecting observations. -/
theorem risk_pushforward_iff {Observed : Type*} [Fintype Observed] [DecidableEq Observed]
    (view : Ω → Observed) (source : BoundedLoss A Ω) (target : BoundedLoss A Observed) :
    (∀ weights : Ω → ℝ, ∀ a, expectedRisk (pushforward weights view) target a =
      expectedRisk weights source a) ↔ ∀ a x, target a (view x) = source a x := by
  classical
  refine ⟨?_, fun h weights a => risk_pushforward weights view source target h a⟩
  intro preserved a x
  have point := preserved (fun y => if y = x then 1 else 0) a
  rw [expectedRisk, sum_pushforward_mul] at point
  simpa [expectedRisk] using point

/-- Dual linear bounds give the corresponding square-root bound, including zero cases. -/
theorem le_sqrt_of_linear_tradeoff (gap mass error : ℝ) (hm : 0 ≤ mass) (he : 0 ≤ error)
    (bound : ∀ a : ℝ, 0 < a → gap ≤ a * mass + error / (2 * a)) :
    gap ≤ sqrt (2 * mass * error) := by
  by_cases positive : 0 < gap
  · by_cases zero : mass = 0
    · have chosen := bound ((error + 1) / gap) (by positivity)
      rw [zero, mul_zero, zero_add] at chosen
      have multiplied := (le_div_iff₀ (show 0 < 2 * ((error + 1) / gap) by positivity)).mp chosen
      have cancel : gap * (2 * ((error + 1) / gap)) = 2 * (error + 1) := by field_simp
      rw [cancel] at multiplied
      linarith
    · have hmpos : 0 < mass := lt_of_le_of_ne hm (Ne.symm zero)
      let a := gap / (2 * mass)
      have ha : 0 < a := by dsimp [a]; positivity
      have chosen := bound a ha
      have cancel : a * mass = gap / 2 := by dsimp [a]; field_simp
      rw [cancel] at chosen
      have multiplied := (le_div_iff₀ (show 0 < 2 * a by positivity)).mp
        (show gap / 2 ≤ error / (2 * a) by linarith)
      have product : gap / 2 * (2 * a) = gap ^ 2 / (2 * mass) := by dsimp [a]; ring
      rw [product] at multiplied
      apply le_sqrt_of_sq_le
      simpa only [mul_comm] using
        (div_le_iff₀ (show 0 < 2 * mass by positivity)).mp multiplied
  · exact (le_of_not_gt positive).trans (sqrt_nonneg _)

/-- Complete the square in a regret-versus-total-loss comparison. -/
theorem sharp_of_quadratic (actual optimal divergence : ℝ) (hl : 0 ≤ optimal) (hd : 0 ≤ divergence)
    (bound : (actual - optimal) ^ 2 ≤ 2 * (actual + optimal) * divergence) :
    actual - optimal ≤ divergence + sqrt (4 * optimal * divergence + divergence ^ 2) := by
  have square : (actual - optimal - divergence) ^ 2 ≤ 4 * optimal * divergence + divergence ^ 2 :=
    by nlinarith
  have absolute := abs_le_of_sq_le_sq (by simpa [sq_sqrt (by positivity :
    0 ≤ 4 * optimal * divergence + divergence ^ 2)] using square)
    (sqrt_nonneg (4 * optimal * divergence + divergence ^ 2))
  linarith [(abs_le.mp absolute).2]

/-- A uniform square-root regret budget implies vanishing average regret. -/
theorem average_of_root_bound (regret : ℕ → ℝ) (budget : ℝ) (hb : 0 ≤ budget)
    (nonneg : ∀ n, 0 ≤ regret n)
    (bound : ∀ n, regret n ≤ 2 * budget + 2 * sqrt ((n : ℝ) * budget)) :
    Filter.Tendsto (fun n => regret n / n) Filter.atTop (nhds 0) := by
  have limit := (Filter.Tendsto.sqrt (tendsto_const_div_atTop_nhds_zero_nat budget)).const_mul 2
  simp only [sqrt_zero, mul_zero] at limit
  have upper_limit := (tendsto_const_div_atTop_nhds_zero_nat (2 * budget)).add limit
  simp only [add_zero] at upper_limit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper_limit
  · exact Filter.Eventually.of_forall fun n => div_nonneg (nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have root : sqrt ((n : ℝ) * budget) / n = sqrt (budget / n) := by
      apply (sq_eq_sq₀ (by positivity : 0 ≤ sqrt ((n : ℝ) * budget) / n) (sqrt_nonneg _)).mp
      rw [div_pow, sq_sqrt (by positivity), sq_sqrt (by positivity)]
      field_simp
    have divided := div_le_div_of_nonneg_right (bound n) hnpos.le
    simpa only [add_div, mul_div_assoc, root] using divided

end Mettapedia.DecisionTheory

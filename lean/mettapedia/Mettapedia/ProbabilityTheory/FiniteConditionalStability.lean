import Mettapedia.InformationTheory.Pinsker
import Mettapedia.ProbabilityTheory.FiniteEventMass

/-!
# Stability of finite conditional queries

The half-L1 event bound is inherited from the existing bounded-expectation
theorem. Conditioning can amplify that discrepancy: the denominator is the
larger of the two conditioning masses, provided both are positive. The bound
is sharp even when the distributions differ by an arbitrarily small amount.

These are changes between models. They do not assume that either model has
any conditional-independence structure.
-/

namespace Mettapedia.ProbabilityTheory.FiniteConditionalStability

open scoped BigOperators
open Mettapedia.InformationTheory
open Mettapedia.ProbabilityTheory.FiniteEventMass

variable {Ω : Type*} [Fintype Ω]

/-- Conditional probability as a finite event-mass ratio. Its numerical
zero-denominator convention is not a claim of defined conditioning there. -/
noncomputable def conditional (weight : Ω → ℝ) (event condition : Ω → Bool) : ℝ :=
  mass weight (fun world => event world && condition world) / mass weight condition

/-- Every event differs by at most half the L1 distance between normalized
finite distributions. The stronger constant uses their equal total mass. -/
theorem event_error_le_half_l1 (p q : Prob Ω) (event : Ω → Bool) :
    |mass p.1 event - mass q.1 event| ≤ (1 / 2 : ℝ) * ∑ world, |p.1 world - q.1 world| := by
  have bound := abs_expectation_sub_le_of_bounds p q
    (fun world => if event world then (1 : ℝ) else 0)
    (A := 0) (B := 1)
    (by intro world; split_ifs <;> norm_num)
    (by intro world; split_ifs <;> norm_num)
  simpa only [mass, mul_ite, mul_one, mul_zero, sub_zero] using bound

private theorem ratio_error_le_larger_carrier {a b p q δ : ℝ}
    (pPositive : 0 < p) (qPositive : 0 < q) (larger : q ≤ p)
    (bNonneg : 0 ≤ b) (bBounded : b ≤ q)
    (eventError : |a - b| ≤ δ) (complementError : |(p - a) - (q - b)| ≤ δ) :
    |a / p - b / q| ≤ δ / p := by
  have difference : a / p - b / q = (a * q - b * p) / (p * q) := by
    field_simp
  rw [difference, abs_div, abs_of_pos (mul_pos pPositive qPositive)]
  apply (div_le_iff₀ (mul_pos pPositive qPositive)).mpr
  have cancel : δ / p * (p * q) = δ * q := by field_simp
  rw [cancel]
  apply abs_le.mpr
  have positivePart := (abs_le.mp eventError).2
  have negativePart := (abs_le.mp complementError).2
  have order0 : 0 ≤ p - q := sub_nonneg.mpr larger
  have firstProduct := mul_nonneg bNonneg order0
  have secondProduct := mul_nonneg (sub_nonneg.mpr bBounded) order0
  constructor <;> nlinarith

/-- Two event-mass errors control the normalized conditional. Both the event
and its complement are taken inside the same conditioning carrier. -/
theorem ratio_error_le_max_carrier {a b p q δ : ℝ}
    (pPositive : 0 < p) (qPositive : 0 < q)
    (aNonneg : 0 ≤ a) (aBounded : a ≤ p) (bNonneg : 0 ≤ b) (bBounded : b ≤ q)
    (eventError : |a - b| ≤ δ) (complementError : |(p - a) - (q - b)| ≤ δ) :
    |a / p - b / q| ≤ δ / max p q := by
  by_cases larger : q ≤ p
  · rw [max_eq_left larger]
    exact ratio_error_le_larger_carrier pPositive qPositive larger bNonneg bBounded
      eventError complementError
  · rw [max_eq_right (le_of_not_ge larger), abs_sub_comm (a / p) (b / q)]
    apply ratio_error_le_larger_carrier qPositive pPositive (le_of_not_ge larger) aNonneg aBounded
    · simpa only [abs_sub_comm] using eventError
    · simpa only [abs_sub_comm] using complementError

theorem complement_inside (weight : Ω → ℝ) (event condition : Ω → Bool) :
    mass weight condition - mass weight (fun world => event world && condition world) =
      mass weight (fun world => !event world && condition world) := by
  have split := partition weight condition event
  have first : (fun world => condition world && event world) =
      (fun world => event world && condition world) := by
    funext world
    exact Bool.and_comm _ _
  have second : (fun world => condition world && !event world) =
      (fun world => !event world && condition world) := by
    funext world
    exact Bool.and_comm _ _
  rw [first, second] at split
  linarith

/-- Stability for arbitrary nonnegative finite weights. The supplied budget
concerns the two actual subevents, not a conclusion about their ratios. -/
theorem conditional_error_le (p q : Ω → ℝ) (event condition : Ω → Bool)
    (pNonneg : ∀ world, 0 ≤ p world) (qNonneg : ∀ world, 0 ≤ q world)
    (pPossible : 0 < mass p condition) (qPossible : 0 < mass q condition) (δ : ℝ)
    (eventError : |mass p (fun world => event world && condition world) -
        mass q (fun world => event world && condition world)| ≤ δ)
    (complementError : |mass p (fun world => !event world && condition world) -
        mass q (fun world => !event world && condition world)| ≤ δ) :
    |conditional p event condition - conditional q event condition| ≤
      δ / max (mass p condition) (mass q condition) := by
  apply ratio_error_le_max_carrier pPossible qPossible
    (nonneg p pNonneg _) (mono p pNonneg (fun _ h => by simp only [Bool.and_eq_true] at h; exact h.2))
    (nonneg q qNonneg _) (mono q qNonneg (fun _ h => by simp only [Bool.and_eq_true] at h; exact h.2)) eventError
  simpa only [complement_inside] using complementError

/-- The denominator uses the larger carrier mass; the looser factor-two
ratio perturbation estimate is unnecessary for normalized distributions. -/
theorem conditional_error_le_half_l1 (p q : Prob Ω) (event condition : Ω → Bool)
    (pPossible : 0 < mass p.1 condition) (qPossible : 0 < mass q.1 condition) :
    |conditional p.1 event condition - conditional q.1 event condition| ≤
      ((1 / 2 : ℝ) * ∑ world, |p.1 world - q.1 world|) /
        max (mass p.1 condition) (mass q.1 condition) :=
  conditional_error_le p.1 q.1 event condition p.2.1 q.2.1 pPossible qPossible _
    (event_error_le_half_l1 p q _) (event_error_le_half_l1 p q _)

/-- Pinsker supplies a divergence-based version when the source is supported
by the reference model. Without that premise the real-log expression used by
`klSum` is not a valid divergence at zero reference mass. -/
theorem conditional_error_le_pinsker (p q : Prob Ω) (event condition : Ω → Bool)
    (pPossible : 0 < mass p.1 condition) (qPossible : 0 < mass q.1 condition)
    (supported : ∀ world, 0 < p.1 world → 0 < q.1 world) :
    |conditional p.1 event condition - conditional q.1 event condition| ≤
      ((1 / 2 : ℝ) * Real.sqrt (2 * FiniteRV.klSum p.1 q.1)) /
        max (mass p.1 condition) (mass q.1 condition) := by
  have l1Nonneg : 0 ≤ ∑ world, |p.1 world - q.1 world| :=
    Finset.sum_nonneg fun world _ => abs_nonneg _
  have l1Bound : (∑ world, |p.1 world - q.1 world|) ≤
      Real.sqrt (2 * FiniteRV.klSum p.1 q.1) := by
    have squared := l1_sq_le_two_klSum p q supported
    rw [← Real.sqrt_sq l1Nonneg]
    exact Real.sqrt_le_sqrt squared
  apply (conditional_error_le_half_l1 p q event condition pPossible qPossible).trans
  apply div_le_div_of_nonneg_right _ (pPossible.le.trans (le_max_left _ _))
  exact mul_le_mul_of_nonneg_left l1Bound (by norm_num)

namespace Controls

def rareLeft (ε : ℝ) (nonnegative : 0 ≤ ε) (bounded : ε ≤ 1) : Prob (Fin 3) :=
  ⟨![ε, 0, 1 - ε], by
    constructor
    · intro world
      fin_cases world <;> simp <;> linarith
    · simp [Fin.sum_univ_succ]⟩

def rareRight (ε : ℝ) (nonnegative : 0 ≤ ε) (bounded : ε ≤ 1) : Prob (Fin 3) :=
  ⟨![0, ε, 1 - ε], by
    constructor
    · intro world
      fin_cases world <;> simp <;> linarith
    · simp [Fin.sum_univ_succ]⟩

/-- Arbitrarily rare conditioning makes arbitrarily close models disagree
maximally on the conditional. This attains the carrier-scaled bound. -/
theorem rare_conditioning_attains_bound (ε : ℝ) (positive : 0 < ε) (bounded : ε ≤ 1) :
    let p := rareLeft ε positive.le bounded
    let q := rareRight ε positive.le bounded
    let event := fun world : Fin 3 => decide (world = 0)
    let condition := fun world : Fin 3 => decide (world ≠ 2)
    |conditional p.1 event condition - conditional q.1 event condition| = 1 ∧
      ((1 / 2 : ℝ) * ∑ world, |p.1 world - q.1 world|) = ε ∧
      mass p.1 condition = ε ∧ mass q.1 condition = ε := by
  simp [rareLeft, rareRight, conditional, mass, Fin.sum_univ_succ,
    abs_of_nonneg positive.le, div_self positive.ne']
  ring

end Controls

end Mettapedia.ProbabilityTheory.FiniteConditionalStability

/-
Knuth–Skilling slice of the probability hypercube. See the aggregator
`Mettapedia/ProbabilityTheory/Hypercube/KnuthSkilling.lean` for the overview.
-/
import KnuthSkilling.Additive.Axioms.SandwichSeparation
import Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets
import Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Neighbors
import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Order.Basic

/-!
# Interval arithmetic, finite models and refinement

Interval bounds, finite rational distributions and tropical operations are
separate concrete constructions. Nested bounded intervals share a point;
vanishing width makes that point unique. Neither completeness nor a diagram
label establishes countable additivity or a full probability-measure model.

`EventBounds` deliberately asserts only pointwise bounds and normalization.
Its precise readouts need additional additive laws. The capability table is
an explicitly authored toy classification, not a theorem about implementability.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Theory

open Classical
-- `_root_.` forces the standalone K&S package; the enclosing
-- `…Hypercube.KnuthSkilling` namespace would otherwise shadow `KnuthSkilling`.
open _root_.KnuthSkilling
open _root_.KnuthSkilling.KnuthSkillingAlgebra
open _root_.KnuthSkilling.KnuthSkillingAlgebraBase

section ImpreciseProbability

/-- An interval probability [lower, upper] with full validity constraints -/
structure IntervalProb where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper
  nonneg : 0 ≤ lower
  le_one : upper ≤ 1

namespace IntervalProb

/-- The point probability as a special case [p, p] -/
def point (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) : IntervalProb where
  lower := p
  upper := p
  valid := le_refl p
  nonneg := hp_nonneg
  le_one := hp_le_one

/-- The zero probability [0, 0] -/
def zero : IntervalProb := point 0 (le_refl 0) (by norm_num)

/-- The one probability [1, 1] -/
def one : IntervalProb := point 1 (by norm_num) (le_refl 1)

/-- The vacuous/ignorance probability [0, 1] -/
def vacuous : IntervalProb where
  lower := 0
  upper := 1
  valid := by norm_num
  nonneg := le_refl 0
  le_one := le_refl 1

/-- Width of the interval (measure of imprecision) -/
def width (p : IntervalProb) : ℝ := p.upper - p.lower

/-- An interval is precise iff its width is zero -/
def isPrecise (p : IntervalProb) : Prop := p.width = 0

theorem point_isPrecise (p : ℝ) (hp₁ : 0 ≤ p) (hp₂ : p ≤ 1) :
    (point p hp₁ hp₂).isPrecise := by
  simp [isPrecise, width, point]

/-- Independent product of interval probabilities (AND of independent events) -/
def mul (p q : IntervalProb) : IntervalProb where
  lower := p.lower * q.lower
  upper := p.upper * q.upper
  valid := by
    apply mul_le_mul p.valid q.valid q.nonneg
    exact le_trans p.nonneg p.valid
  nonneg := mul_nonneg p.nonneg q.nonneg
  le_one := by
    have h1 : p.upper ≤ 1 := p.le_one
    have h2 : q.upper ≤ 1 := q.le_one
    have h3 : 0 ≤ q.upper := le_trans q.nonneg q.valid
    calc p.upper * q.upper ≤ 1 * q.upper := by apply mul_le_mul_of_nonneg_right h1 h3
      _ = q.upper := one_mul _
      _ ≤ 1 := h2

/-- Interval addition for disjoint events (OR of mutually exclusive events) -/
def add_disjoint (p q : IntervalProb) (h : p.upper + q.upper ≤ 1) : IntervalProb where
  lower := p.lower + q.lower
  upper := p.upper + q.upper
  valid := add_le_add p.valid q.valid
  nonneg := add_nonneg p.nonneg q.nonneg
  le_one := h

/-- Complement of an interval probability (for precise complements) -/
def complement (p : IntervalProb) : IntervalProb where
  lower := 1 - p.upper
  upper := 1 - p.lower
  valid := by linarith [p.valid]
  nonneg := by linarith [p.le_one]
  le_one := by linarith [p.nonneg]

theorem complement_complement (p : IntervalProb) :
    p.complement.complement = p := by
  simp [complement]

/-- Lower endpoint; this alone supplies no belief-function laws. -/
def belief (p : IntervalProb) : ℝ := p.lower

/-- Upper endpoint. -/
def plausibility (p : IntervalProb) : ℝ := p.upper

theorem belief_le_plausibility (p : IntervalProb) : p.belief ≤ p.plausibility :=
  p.valid

/-- The interval contains a point value iff it's in [lower, upper] -/
def contains (p : IntervalProb) (x : ℝ) : Prop :=
  p.lower ≤ x ∧ x ≤ p.upper

theorem point_contains_self (x : ℝ) (h₁ : 0 ≤ x) (h₂ : x ≤ 1) :
    (point x h₁ h₂).contains x := by
  simp [contains, point]

/-- Partial order on interval probabilities: p refines q iff p is more precise -/
def refines (p q : IntervalProb) : Prop :=
  q.lower ≤ p.lower ∧ p.upper ≤ q.upper

theorem refines_trans {p q r : IntervalProb}
    (hpq : p.refines q) (hqr : q.refines r) : p.refines r := by
  simp only [refines] at *
  exact ⟨le_trans hqr.1 hpq.1, le_trans hpq.2 hqr.2⟩

theorem point_refines_containing {x : ℝ} {p : IntervalProb}
    (hx₁ : 0 ≤ x) (hx₂ : x ≤ 1) (hcontains : p.contains x) :
    (point x hx₁ hx₂).refines p := by
  simp [refines, point, contains] at *
  exact hcontains

/-- Interval conditioning: P(A|B) when A ⊆ B (so P(A∩B) = P(A))

Note: General interval conditioning requires additional hypotheses.
This simplified version requires that pAB ≤ pB (i.e., A ⊆ B in probability sense). -/
noncomputable def condition (pAB pB : IntervalProb) (hB_pos : 0 < pB.lower)
    (hAB_le_B : pAB.upper ≤ pB.lower) : IntervalProb where
  lower := pAB.lower / pB.upper
  upper := pAB.upper / pB.lower
  valid := by
    have h1 : pAB.lower ≤ pAB.upper := pAB.valid
    have h2 : pB.lower ≤ pB.upper := pB.valid
    have h3 : 0 < pB.upper := lt_of_lt_of_le hB_pos h2
    calc pAB.lower / pB.upper ≤ pAB.upper / pB.upper := by
           apply div_le_div_of_nonneg_right h1 (le_of_lt h3)
      _ ≤ pAB.upper / pB.lower := by
           apply div_le_div_of_nonneg_left (le_trans pAB.nonneg h1) hB_pos h2
  nonneg := by
    apply div_nonneg pAB.nonneg
    exact le_trans (le_of_lt hB_pos) pB.valid
  le_one := by
    rw [div_le_one hB_pos]
    exact hAB_le_B

end IntervalProb

/-- Normalized pointwise event bounds, without coherence or additivity assumptions. -/
structure EventBounds (Ω : Type*) where
  /-- Lower probability function -/
  P_lower : Set Ω → ℝ
  /-- Upper probability function -/
  P_upper : Set Ω → ℝ
  /-- Lower ≤ upper pointwise -/
  valid : ∀ A, P_lower A ≤ P_upper A
  /-- Nonnegativity -/
  nonneg : ∀ A, 0 ≤ P_lower A
  /-- Upper bounded by 1 -/
  le_one : ∀ A, P_upper A ≤ 1
  /-- Empty set has probability 0 -/
  empty_zero : P_lower ∅ = 0 ∧ P_upper ∅ = 0
  /-- Full set has probability 1 -/
  full_one : P_lower Set.univ = 1 ∧ P_upper Set.univ = 1

namespace EventBounds

variable {Ω : Type*} (C : EventBounds Ω)

/-- The interval probability of an event -/
def prob (A : Set Ω) : IntervalProb where
  lower := C.P_lower A
  upper := C.P_upper A
  valid := C.valid A
  nonneg := C.nonneg A
  le_one := C.le_one A

/-- Pointwise precision identifies lower and upper readouts. -/
def isPrecise : Prop := ∀ A, C.P_lower A = C.P_upper A

/-- Duality: P_upper(A) = 1 - P_lower(Aᶜ) (conjugacy) -/
structure Conjugate (C : EventBounds Ω) : Prop where
  conj : ∀ A, C.P_upper A = 1 - C.P_lower Aᶜ

/-- Super-additivity of lower probability (for disjoint sets) -/
structure SuperAdditive (C : EventBounds Ω) : Prop where
  superadd : ∀ A B, Disjoint A B → C.P_lower A + C.P_lower B ≤ C.P_lower (A ∪ B)

/-- Sub-additivity of upper probability (for disjoint sets) -/
structure SubAdditive (C : EventBounds Ω) : Prop where
  subadd : ∀ A B, Disjoint A B → C.P_upper (A ∪ B) ≤ C.P_upper A + C.P_upper B

end EventBounds

/-- Precision plus both finite additive inequalities yields finite additivity. -/
theorem precise_bounds_additive {Ω : Type*} (C : EventBounds Ω) (hp : C.isPrecise)
    (hl : C.SuperAdditive) (hu : C.SubAdditive) (A B : Set Ω) (hd : Disjoint A B) :
    C.P_lower (A ∪ B) = C.P_lower A + C.P_lower B := by
  have h := hu.subadd A B hd
  rw [← hp (A ∪ B), ← hp A, ← hp B] at h
  exact le_antisymm h (hl.superadd A B hd)

/-- A normalized precise readout can still fail finite additivity. -/
noncomputable def nonadditiveBounds : EventBounds Bool where
  P_lower A := if A = Set.univ then 1 else 0
  P_upper A := if A = Set.univ then 1 else 0
  valid _ := le_refl _
  nonneg A := by split_ifs <;> norm_num
  le_one A := by split_ifs <;> norm_num
  empty_zero := ⟨if_neg Set.empty_ne_univ, if_neg Set.empty_ne_univ⟩
  full_one := ⟨if_pos rfl, if_pos rfl⟩

theorem nonadditiveBounds_precise : nonadditiveBounds.isPrecise := fun _ => rfl

theorem nonadditiveBounds_not_additive :
    nonadditiveBounds.P_lower ({false} ∪ {true}) ≠
      nonadditiveBounds.P_lower {false} + nonadditiveBounds.P_lower {true} := by
  have hf : ({false} : Set Bool) ≠ Set.univ := by
    intro h; have ht : true ∈ ({false} : Set Bool) := h ▸ Set.mem_univ true
    simp at ht
  have ht : ({true} : Set Bool) ≠ Set.univ := by
    intro h; have hf : false ∈ ({true} : Set Bool) := h ▸ Set.mem_univ false
    simp at hf
  have hall : ({false} ∪ {true} : Set Bool) = Set.univ := by
    ext b; cases b <;> simp
  change (if ({false} ∪ {true} : Set Bool) = Set.univ then (1 : ℝ) else 0) ≠
    (if ({false} : Set Bool) = Set.univ then 1 else 0) +
      (if ({true} : Set Bool) = Set.univ then 1 else 0)
  rw [hall, if_pos rfl, if_neg hf, if_neg ht]
  norm_num

end ImpreciseProbability

section DiscreteProbability

/-- A discrete probability space with exact rational probabilities -/
structure DiscreteProbSpace (Ω : Type*) [Fintype Ω] where
  /-- Probability mass function (exact rational values) -/
  pmf : Ω → ℚ
  /-- Nonnegativity -/
  nonneg : ∀ ω, 0 ≤ pmf ω
  /-- Sums to 1 -/
  sum_one : ∑ ω, pmf ω = 1

namespace DiscreteProbSpace

variable {Ω : Type*} [Fintype Ω] (P : DiscreteProbSpace Ω)

/-- Probability of an event (exact rational) -/
def prob (A : Set Ω) [DecidablePred (· ∈ A)] : ℚ :=
  ∑ ω ∈ Finset.filter (· ∈ A) Finset.univ, P.pmf ω

/-- Discrete conditioning (exact rational division) -/
noncomputable def cond (A B : Set Ω) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (_hB : P.prob B ≠ 0) : ℚ :=
  P.prob (A ∩ B) / P.prob B

/-- Exact expectation (no limits needed) -/
def expect (f : Ω → ℚ) : ℚ :=
  ∑ ω, P.pmf ω * f ω

end DiscreteProbSpace

/-- Counting-based K&S algebra on positive integers -/
structure IntegerKSAlgebra where
  /-- Elements are positive integers representing "counts" -/
  count : ℕ
  count_pos : 0 < count

namespace IntegerKSAlgebra

/-- The combining operation is multiplication (of counts) -/
def mul (x y : IntegerKSAlgebra) : IntegerKSAlgebra where
  count := x.count * y.count
  count_pos := Nat.mul_pos x.count_pos y.count_pos

/-- The identity is 1 (one count) -/
def one : IntegerKSAlgebra where
  count := 1
  count_pos := Nat.one_pos

/-- Order by count -/
def le (x y : IntegerKSAlgebra) : Prop := x.count ≤ y.count

theorem mul_assoc (x y z : IntegerKSAlgebra) :
    mul (mul x y) z = mul x (mul y z) := by
  simp [mul, Nat.mul_assoc]

theorem one_mul (x : IntegerKSAlgebra) : mul one x = x := by
  simp only [mul, one, Nat.one_mul]

theorem mul_one (x : IntegerKSAlgebra) : mul x one = x := by
  simp only [mul, one, Nat.mul_one]

end IntegerKSAlgebra

end DiscreteProbability

section RefinementPath

/-- A sequence of shrinking interval probabilities -/
structure ShrinkingIntervals where
  /-- The sequence of intervals -/
  intervals : ℕ → IntervalProb
  /-- Lower bounds are non-decreasing -/
  lower_mono : ∀ n, (intervals n).lower ≤ (intervals (n + 1)).lower
  /-- Upper bounds are non-increasing -/
  upper_mono : ∀ n, (intervals (n + 1)).upper ≤ (intervals n).upper
  /-- Widths converge to zero -/
  width_to_zero : ∀ ε > 0, ∃ N, ∀ n ≥ N, (intervals n).width < ε

namespace ShrinkingIntervals

/-- Lower bounds increase across the sequence -/
theorem lower_mono_trans (S : ShrinkingIntervals) (m n : ℕ) (hmn : m ≤ n) :
    (S.intervals m).lower ≤ (S.intervals n).lower := by
  induction hmn with
  | refl => rfl
  | step _ ih => exact le_trans ih (S.lower_mono _)

/-- Upper bounds decrease across the sequence -/
theorem upper_mono_trans (S : ShrinkingIntervals) (m n : ℕ) (hmn : m ≤ n) :
    (S.intervals n).upper ≤ (S.intervals m).upper := by
  induction hmn with
  | refl => rfl
  | step _ ih => exact le_trans (S.upper_mono _) ih

/-- Lower bounds are bounded above by any upper bound -/
theorem lower_bdd_by_upper (S : ShrinkingIntervals) (m n : ℕ) :
    (S.intervals m).lower ≤ (S.intervals n).upper := by
  by_cases hmn : m ≤ n
  · exact le_trans (lower_mono_trans S m n hmn) (S.intervals n).valid
  · push Not at hmn
    exact le_trans (S.intervals m).valid (upper_mono_trans S n m (le_of_lt hmn))

/-- The limiting value (using completeness of ℝ) -/
noncomputable def limit (S : ShrinkingIntervals) : ℝ :=
  sSup (Set.range (fun n => (S.intervals n).lower))

/-- Helper: the set of lower bounds is bounded above -/
theorem lower_bdd_above (S : ShrinkingIntervals) :
    BddAbove (Set.range (fun n => (S.intervals n).lower)) := by
  use (S.intervals 0).upper
  intro x ⟨n, hn⟩
  rw [← hn]
  exact lower_bdd_by_upper S n 0

/-- Helper: the set of lower bounds is nonempty -/
theorem lower_nonempty (S : ShrinkingIntervals) :
    (Set.range (fun n => (S.intervals n).lower)).Nonempty :=
  ⟨(S.intervals 0).lower, 0, rfl⟩

/-- The limit is in [0, 1] -/
theorem limit_bounded (S : ShrinkingIntervals) : 0 ≤ S.limit ∧ S.limit ≤ 1 := by
  constructor
  · -- limit ≥ 0 because all lower bounds are ≥ 0
    apply le_csSup_of_le S.lower_bdd_above
    · use 0
    · exact (S.intervals 0).nonneg
  · -- limit ≤ 1 because all lower bounds are ≤ upper ≤ 1
    apply csSup_le S.lower_nonempty
    intro x ⟨n, hn⟩
    rw [← hn]
    exact le_trans (S.intervals n).valid (S.intervals n).le_one

/-- The limit is in all intervals -/
theorem limit_in_all_intervals (S : ShrinkingIntervals) (n : ℕ) :
    (S.intervals n).lower ≤ S.limit ∧ S.limit ≤ (S.intervals n).upper := by
  constructor
  · exact le_csSup S.lower_bdd_above ⟨n, rfl⟩
  · apply csSup_le S.lower_nonempty
    intro x ⟨m, hm⟩
    rw [← hm]
    exact lower_bdd_by_upper S m n

/-- Convert limit to a point interval probability -/
noncomputable def limitProb (S : ShrinkingIntervals) : IntervalProb :=
  IntervalProb.point S.limit S.limit_bounded.1 S.limit_bounded.2

theorem limitProb_isPrecise (S : ShrinkingIntervals) : S.limitProb.isPrecise :=
  IntervalProb.point_isPrecise S.limit S.limit_bounded.1 S.limit_bounded.2

end ShrinkingIntervals

/-- The Refinement Theorem: Shrinking intervals collapse to a point via completeness -/
theorem refinement_theorem (S : ShrinkingIntervals) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ ∀ n, (S.intervals n).contains p := by
  use S.limit
  exact ⟨S.limit_bounded.1, S.limit_bounded.2, fun n =>
    ⟨(S.limit_in_all_intervals n).1, (S.limit_in_all_intervals n).2⟩⟩

/-- The limit is unique -/
theorem refinement_unique (S : ShrinkingIntervals) (p q : ℝ)
    (hp : ∀ n, (S.intervals n).contains p)
    (hq : ∀ n, (S.intervals n).contains q) : p = q := by
  by_contra hne
  have hpos : 0 < |p - q| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := S.width_to_zero (|p - q| / 2) (by positivity)
  have hwidth := hN N (le_refl N)
  have hp_in := hp N
  have hq_in := hq N
  -- Both p and q are in interval N, but interval has width < |p - q|/2
  have h1 : |p - q| ≤ (S.intervals N).width := by
    simp only [IntervalProb.width, abs_sub_le_iff, IntervalProb.contains] at *
    constructor <;> linarith [hp_in.1, hp_in.2, hq_in.1, hq_in.2]
  linarith

end RefinementPath

section CollapseTheorems

/-- Theorem: KSSeparation implies commutativity.
    This collapses vertices 2,3,6,7 (non-commutative + separation) to empty.

    **Proof**: See `KnuthSkilling/Separation/SandwichSeparation.lean` (`ksSeparation_implies_commutative`)
    for the formal proof that `KSSeparation` forces `op x y = op y x` for all elements.

    The key insight is that the separation witnesses can be used to build an injective
    order-preserving map Θ : α → ℝ satisfying Θ(x ⊕ y) = Θ(x) + Θ(y).
    Since + is commutative on ℝ and Θ is injective, commutativity follows. -/
theorem sep_implies_comm_collapse
    (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] :
    ∀ x y : α, op x y = op y x := by
  simpa using (SandwichSeparation.ksSeparation_implies_commutative (α := α))

/-- Theorem: Density + KSSeparation implies KSSeparationStrict.
    This shows V₁₁ automatically has strict separation. -/
theorem dense_sep_implies_strict :
    ∀ (α : Type*) [KnuthSkillingAlgebra α] [KSSeparation α] [DenselyOrdered α],
      KSSeparationStrict α := by
  intro α _ _ _
  exact KSSeparation.toKSSeparationStrict_of_denselyOrdered

/-- Theorem: Non-commutative vertices (0,1,4,5) have no additive ℝ-representation.
    If Θ : α → ℝ is additive (Θ(x ⊕ y) = Θ(x) + Θ(y)) and order-reflecting,
    then op must be commutative. -/
theorem noncomm_no_real_rep (α : Type*) [KnuthSkillingAlgebra α]
    (Θ : α → ℝ) (hΘ_additive : ∀ x y, Θ (op x y) = Θ x + Θ y)
    (hΘ_reflects : ∀ x y, Θ x < Θ y ↔ x < y) :
    ∀ x y : α, op x y = op y x := by
  have horder : ∀ x y, x ≤ y ↔ Θ x ≤ Θ y := by
    intro x y
    simpa only [not_lt] using (not_congr (hΘ_reflects y x)).symm
  exact Mettapedia.ProbabilityTheory.OrderedCombination.commutative_of_representation
    ⟨Θ, horder, hΘ_additive⟩

/-- Authored capability labels, without implementation evidence. -/
inductive ToyCapability
  | Combine     -- Can only combine (no conditioning, no expectations)
  | Finite      -- Can do finite sums, exact discrete probability
  | Bounded     -- Can compute interval bounds (robust inference)
  | Full        -- Full measure theory, integration, limits
  deriving DecidableEq, Repr

/-- A toy lookup table, not a classification theorem. -/
def toyVertexCapability (v : Fin 16) : ToyCapability :=
  match v.val with
  | 0 => .Combine   -- Free monoid (non-comm)
  | 1 => .Combine   -- Dense free monoid
  | 2 => .Combine   -- EMPTY (Sep ⇒ Comm)
  | 3 => .Combine   -- EMPTY
  | 4 => .Combine   -- Complete non-comm
  | 5 => .Combine   -- Complete dense non-comm
  | 6 => .Combine   -- EMPTY
  | 7 => .Combine   -- EMPTY
  | 8 => .Finite    -- Comm Archimedean (ℤ-like)
  | 9 => .Bounded   -- Comm dense (ℚ-like, no sep)
  | 10 => .Finite   -- KSSep incomplete discrete
  | 11 => .Bounded  -- Imprecise prob (ℚ)
  | 12 => .Finite   -- Complete comm discrete
  | 13 => .Full     -- Complete comm dense
  | 14 => .Finite   -- KSSep complete discrete
  | 15 => .Full     -- Classical K&S (ℝ)
  | _ => .Combine   -- Unreachable for Fin 16

/-- Evaluate the toy table at vertex 15. -/
theorem toy_vertex15_label : toyVertexCapability ⟨15, by omega⟩ = .Full := rfl

/-- Evaluate the toy table at vertex 11. -/
theorem toy_vertex11_label : toyVertexCapability ⟨11, by omega⟩ = .Bounded := rfl

/-- Evaluate the toy table at vertex 8. -/
theorem toy_vertex8_label : toyVertexCapability ⟨8, by omega⟩ = .Finite := rfl

end CollapseTheorems

section TropicalProbability

/-- Extended reals with infinity (for tropical semiring) -/
inductive TropicalReal
  | finite (x : ℝ)
  | infinity

namespace TropicalReal

/-- Tropical addition is minimum -/
def add (x y : TropicalReal) : TropicalReal :=
  match x, y with
  | infinity, _ => y
  | _, infinity => x
  | finite a, finite b => finite (min a b)

/-- Tropical multiplication is ordinary addition -/
def mul (x y : TropicalReal) : TropicalReal :=
  match x, y with
  | infinity, _ => infinity
  | _, infinity => infinity
  | finite a, finite b => finite (a + b)

/-- Tropical zero (additive identity) is ∞ -/
def zero : TropicalReal := infinity

/-- Tropical one (multiplicative identity) is 0 -/
def one : TropicalReal := finite 0

theorem add_comm (x y : TropicalReal) : add x y = add y x := by
  cases x <;> cases y <;> simp [add, min_comm]

theorem add_assoc (x y z : TropicalReal) : add (add x y) z = add x (add y z) := by
  cases x <;> cases y <;> cases z <;> simp [add, min_assoc]

theorem mul_comm (x y : TropicalReal) : mul x y = mul y x := by
  cases x <;> cases y <;> simp [mul, _root_.add_comm]

theorem mul_assoc (x y z : TropicalReal) : mul (mul x y) z = mul x (mul y z) := by
  cases x <;> cases y <;> cases z <;> simp [mul, _root_.add_assoc]

theorem add_zero (x : TropicalReal) : add x zero = x := by
  cases x <;> rfl

theorem mul_one (x : TropicalReal) : mul x one = x := by
  cases x <;> simp [mul, one, _root_.add_zero]

/-- Tropical "cost" of an event: nonnegative extended real -/
structure TropicalCost where
  cost : TropicalReal
  nonneg : match cost with
    | .infinity => True
    | .finite c => 0 ≤ c

end TropicalReal

end TropicalProbability

section QuantumConnection

end QuantumConnection

end Mettapedia.ProbabilityTheory.Hypercube.KnuthSkilling.Theory

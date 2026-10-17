import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Image
import Mathlib.Data.NNReal.Basic
import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

/-!
# Nondeterminism and probability: no distributive law, and the repair

**No-go.**  There is no distributive law of finite probability distributions
over finite sets (a natural `λ : D (P X) → P (D X)` satisfying the two unit
laws), even restricted to endomaps of one four-element type
(`no_distributiveLaw`).  The argument is Plotkin's, as given by Varacca and
Winskel (*Distributing probability over non-determinism*, Proposition 3.2) and
by Zwart and Marsden (*No-go theorems for distributive laws*, Counterexample
3.1): take `Ξ = ½·{a, b} + ½·{c, d}` and trace it along three maps.  Two of
them force every distribution in `λ Ξ` to be a point mass; the third forces one
of them to be `½·a + ½·c`.  The maps are `Distribution.map` and `Finset.image`,
and the distributions are Mathlib's `PMF`.

The argument uses idempotence of both choices: `½·A + ½·A = A` for
probability, `A ∪ A = A` for sets.

**Repair.**  Keep probabilistic choice and make nondeterministic choice
additive, as answers already are.  In the weighted answer monad over the
nonnegative reals (`Ans ℝ≥0`), nondeterministic choice is `+`, probabilistic
choice is the convex combination `p • A + (1 - p) • B`, and both are algebraic
operations of one commutative monad (`Ans.add_bind`, `convex_bind`,
`Ans.bind_comm`); weighting distributes over nondeterministic choice
(`smul_distrib_choice`), probabilistic choice is idempotent (`convex_idem`),
and nondeterministic choice is not (`choice_not_idem`).  The distributive axiom
of convex semilattices, `(A + B) ⊕ C = (A ⊕ C) + (B ⊕ C)`, holds only for
idempotent choice (`convex_semilattice_axiom_fails`); for additive choice the
alternative `C` is counted once more on the right (`convex_choice_left`).  No law between two monads
is needed: there is one monad.  Sets of possibilities are a readout, the
support, which is a monad morphism into sets (`Ans.support_bind`); it
identifies the two choices (`support_convex`), which is the information the
no-go shows cannot be kept when both choices are idempotent.  Keeping sets of
distributions requires convexity instead (the convex powerset monad of Jacobs,
and of Goy and Petrişan by a weak distributive law).
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.NondeterminismProbability

open scoped NNReal ENNReal

/-- Distributions are compared classically, within this development. -/
noncomputable scoped instance (X : Type) : DecidableEq (PMF X) := Classical.decEq _

/-- A candidate distributive law of distributions over finite sets on one type:
natural along every endomap, with both unit laws. -/
structure DistributiveLaw (X : Type) [DecidableEq X] where
  law : PMF (Finset X) → Finset (PMF X)
  natural : ∀ (f : X → X) (Ξ : PMF (Finset X)),
    law (Ξ.map (Finset.image f)) = (law Ξ).image (PMF.map f)
  unit_pure : ∀ A : Finset X, law (PMF.pure A) = A.image PMF.pure
  unit_singleton : ∀ μ : PMF X, law (μ.map fun x => {x}) = {μ}

/-- Four points. -/
inductive Point
  | a
  | b
  | c
  | d
  deriving DecidableEq

open Point

/-- The three maps of the counterexample. -/
def f₁ : Point → Point
  | a => a | b => b | c => a | d => b

def f₂ : Point → Point
  | a => a | b => b | c => b | d => a

def f₃ : Point → Point
  | a => a | b => a | c => c | d => c

/-- A fair coin. -/
noncomputable def coin : PMF Bool := PMF.uniformOfFintype Bool

theorem support_coin : coin.support = Set.univ :=
  PMF.support_uniformOfFintype Bool

/-- `Ξ = ½·{a, b} + ½·{c, d}`. -/
noncomputable def Ξ : PMF (Finset Point) := coin.map fun bit => if bit then {a, b} else {c, d}

/-- `½·a + ½·c`. -/
noncomputable def ν : PMF Point := coin.map fun bit => if bit then a else c

theorem map_Ξ (f : Point → Point) :
    Ξ.map (Finset.image f) = coin.map fun bit => if bit then ({a, b} : Finset Point).image f
      else ({c, d} : Finset Point).image f := by
  rw [Ξ, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> rfl

theorem map_Ξ_f₁ : Ξ.map (Finset.image f₁) = PMF.pure {a, b} := by
  rw [map_Ξ]
  have : (fun bit : Bool => if bit then ({a, b} : Finset Point).image f₁
      else ({c, d} : Finset Point).image f₁) = Function.const Bool {a, b} := by
    funext bit
    cases bit <;> decide
  rw [this, PMF.map_const]

theorem map_Ξ_f₂ : Ξ.map (Finset.image f₂) = PMF.pure {a, b} := by
  rw [map_Ξ]
  have : (fun bit : Bool => if bit then ({a, b} : Finset Point).image f₂
      else ({c, d} : Finset Point).image f₂) = Function.const Bool {a, b} := by
    funext bit
    cases bit <;> decide
  rw [this, PMF.map_const]

theorem map_Ξ_f₃ : Ξ.map (Finset.image f₃) = ν.map fun x => {x} := by
  rw [map_Ξ, ν, PMF.map_comp]
  congr 1
  funext bit
  cases bit <;> decide

theorem support_ν : a ∈ ν.support ∧ c ∈ ν.support := by
  rw [ν, PMF.support_map, support_coin]
  exact ⟨⟨true, trivial, rfl⟩, ⟨false, trivial, rfl⟩⟩

/-- A distribution whose image along `f` is a point mass lives on one fibre. -/
theorem fibre_of_map_eq_pure {f : Point → Point} {μ : PMF Point} {y : Point}
    (h : μ.map f = PMF.pure y) {x : Point} (member : x ∈ μ.support) : f x = y := by
  have : f x ∈ (μ.map f).support := by
    rw [PMF.support_map]
    exact ⟨x, member, rfl⟩
  rw [h, PMF.support_pure] at this
  exact this

/-- `f₁` and `f₂` together separate the points. -/
theorem separate (x y : Point) (one : f₁ x = f₁ y) (two : f₂ x = f₂ y) : x = y := by
  cases x <;> cases y <;> first | rfl | (simp [f₁, f₂] at one two)

theorem mem_pure_pair {μ : PMF Point} (member : μ ∈ ({PMF.pure a, PMF.pure b} : Finset (PMF Point))) :
    ∃ y, μ = PMF.pure y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact ⟨a, rfl⟩
  · exact ⟨b, rfl⟩

/-- **No distributive law of distributions over finite sets.** -/
theorem no_distributiveLaw : IsEmpty (DistributiveLaw Point) := by
  constructor
  intro L
  have pair : ({a, b} : Finset Point).image PMF.pure = {PMF.pure a, PMF.pure b} := by
    simp [Finset.image_insert, Finset.image_singleton]
  have one : (L.law Ξ).image (PMF.map f₁) = {PMF.pure a, PMF.pure b} := by
    rw [← L.natural, map_Ξ_f₁, L.unit_pure, pair]
  have two : (L.law Ξ).image (PMF.map f₂) = {PMF.pure a, PMF.pure b} := by
    rw [← L.natural, map_Ξ_f₂, L.unit_pure, pair]
  have three : (L.law Ξ).image (PMF.map f₃) = {ν} := by
    rw [← L.natural, map_Ξ_f₃, L.unit_singleton]
  -- some distribution of `λ Ξ` is sent to `ν` by `f₃`
  obtain ⟨μ, member, toν⟩ := Finset.mem_image.1 (by rw [three]; exact Finset.mem_singleton_self ν)
  -- its images along `f₁` and `f₂` are point masses
  obtain ⟨y₁, h₁⟩ := mem_pure_pair (by rw [← one]; exact Finset.mem_image_of_mem _ member)
  obtain ⟨y₂, h₂⟩ := mem_pure_pair (by rw [← two]; exact Finset.mem_image_of_mem _ member)
  -- so its support has one point
  have single : ∀ x ∈ μ.support, ∀ y ∈ μ.support, x = y := fun x hx y hy =>
    separate x y ((fibre_of_map_eq_pure h₁ hx).trans (fibre_of_map_eq_pure h₁ hy).symm)
      ((fibre_of_map_eq_pure h₂ hx).trans (fibre_of_map_eq_pure h₂ hy).symm)
  -- but its image along `f₃` charges both `a` and `c`
  obtain ⟨hasA, hasC⟩ := support_ν
  rw [← toν, PMF.support_map] at hasA hasC
  obtain ⟨x, hx, fx⟩ := hasA
  obtain ⟨y, hy, fy⟩ := hasC
  have := single x hx y hy
  subst this
  rw [fx] at fy
  exact absurd fy (by decide)

/-! ## The repair: one monad with both choices -/

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

variable {X : Type*}

/-- Probabilistic choice: the convex combination. -/
noncomputable def convex (p : ℝ≥0) (first second : Ans ℝ≥0 X) : Ans ℝ≥0 X :=
  p • first + (1 - p) • second

/-- **Weighting distributes over nondeterministic choice.** -/
theorem smul_distrib_choice (p : ℝ≥0) (first second : Ans ℝ≥0 X) :
    p • (first + second) = p • first + p • second :=
  smul_add p first second

/-- Probabilistic choice with a nondeterministic left alternative: the right
alternative is counted once on the left and twice on the right. -/
theorem convex_choice_left (p : ℝ≥0) (first second third : Ans ℝ≥0 X) :
    convex p (first + second) third + (1 - p) • third =
      convex p first third + convex p second third := by
  simp only [convex, smul_add]
  abel

/-- **The convex-semilattice distributive axiom needs idempotent choice**:
`(A + B) ⊕ C = (A ⊕ C) + (B ⊕ C)` fails for additive choice, because `C` is
duplicated on the right. -/
theorem convex_semilattice_axiom_fails (x : X) :
    convex (1 / 2) (0 + 0) (Ans.pure x) ≠
      convex (1 / 2) 0 (Ans.pure x) + convex (1 / 2) 0 (Ans.pure x) := by
  intro same
  have := congrArg (fun A : Ans ℝ≥0 X => A x) same
  simp only [convex, add_zero, smul_zero, zero_add, Finsupp.coe_add, Finsupp.coe_smul,
    Pi.add_apply, Pi.smul_apply, Ans.pure, Finsupp.single_eq_same, smul_eq_mul, mul_one] at this
  have half : (1 : ℝ≥0) - 1 / 2 = 1 / 2 := by
    rw [tsub_eq_iff_eq_add_of_le (by norm_num)]
    norm_num
  rw [half] at this
  norm_num at this

/-- **Probabilistic choice is idempotent** when `p ≤ 1`. -/
theorem convex_idem {p : ℝ≥0} (le : p ≤ 1) (answers : Ans ℝ≥0 X) :
    convex p answers answers = answers := by
  rw [convex, ← add_smul, add_tsub_cancel_of_le le, one_smul]

/-- **Nondeterministic choice is not idempotent.** -/
theorem choice_not_idem (x : X) : (Ans.pure x : Ans ℝ≥0 X) + Ans.pure x ≠ Ans.pure x := by
  intro same
  have := congrArg (fun A : Ans ℝ≥0 X => A x) same
  simp [Ans.pure] at this

/-- Probabilistic choice is an algebraic operation: bind distributes over it. -/
theorem convex_bind {Y : Type*} (p : ℝ≥0) (first second : Ans ℝ≥0 X) (f : X → Ans ℝ≥0 Y) :
    Ans.bind (convex p first second) f = convex p (Ans.bind first f) (Ans.bind second f) := by
  rw [convex, Ans.add_bind, Ans.smul_bind, Ans.smul_bind, convex]

/-- **The support readout identifies the two choices**: for `0 < p < 1` the
possibilities of a probabilistic choice are those of the nondeterministic
choice. -/
theorem support_convex [DecidableEq X] {p : ℝ≥0} (pos : 0 < p) (lt : p < 1)
    (first second : Ans ℝ≥0 X) :
    (convex p first second).support = (first + second).support := by
  have q : (1 : ℝ≥0) - p ≠ 0 := (tsub_pos_of_lt lt).ne'
  ext x
  simp only [convex, Finsupp.mem_support_iff, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, ne_eq, add_eq_zero, mul_eq_zero, pos.ne', q, false_or]

end Mettapedia.CategoryTheory.NondeterminismProbability

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Relation

/-!
# Two bookkeeping facts about the square rung

Both are stated away from the square itself, because neither uses anything
about squares: one is finite arithmetic over the naturals, the other is a
statement about a reachability relation covered by two sets.

* **Zero targets descend additively.**  If the profile-resolved count upstairs
  is the sum of the two reduction counts profile by profile, then the same
  holds after summing over any finite set of target profiles, and — because
  the summands are naturals — the total vanishes exactly when both reduction
  totals vanish.  So the square rung for a positivity target is additive
  rather than dynamical: if a square instance has no seed, neither reduction
  has one.
* **The connected-union criterion.**  If the colouring set is covered by two
  sides, each of which is internally connected, the whole reconfiguration
  relation is connected exactly when one side is empty or some path joins the
  two sides.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SquareLadder

/-! ## Zero targets descend additively -/

variable {Profile : Type*}

/-- Profilewise additivity sums to additivity over any finite target set. -/
theorem sum_eq_add_of_profilewise (targets : Finset Profile)
    {countUp countLeft countRight : Profile → ℕ}
    (hadd : ∀ profile, countUp profile = countLeft profile + countRight profile) :
    ∑ profile ∈ targets, countUp profile =
      (∑ profile ∈ targets, countLeft profile) +
        (∑ profile ∈ targets, countRight profile) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun profile _ => hadd profile

/-- **Zero targets descend additively.**  The total over a finite target set
vanishes exactly when both reduction totals vanish, because all summands are
natural numbers. -/
theorem sum_eq_zero_iff_of_profilewise (targets : Finset Profile)
    {countUp countLeft countRight : Profile → ℕ}
    (hadd : ∀ profile, countUp profile = countLeft profile + countRight profile) :
    (∑ profile ∈ targets, countUp profile) = 0 ↔
      (∑ profile ∈ targets, countLeft profile) = 0 ∧
        (∑ profile ∈ targets, countRight profile) = 0 := by
  rw [sum_eq_add_of_profilewise targets hadd]
  omega

/-- The descent used by the rung: a zero total upstairs is a zero total on
each side, so a least zero-target instance descends through both reductions. -/
theorem left_and_right_eq_zero_of_up_eq_zero (targets : Finset Profile)
    {countUp countLeft countRight : Profile → ℕ}
    (hadd : ∀ profile, countUp profile = countLeft profile + countRight profile)
    (hzero : (∑ profile ∈ targets, countUp profile) = 0) :
    (∑ profile ∈ targets, countLeft profile) = 0 ∧
      (∑ profile ∈ targets, countRight profile) = 0 :=
  (sum_eq_zero_iff_of_profilewise targets hadd).1 hzero

/-! ## The connected-union criterion -/

section ConnectedUnion

variable {State : Type*} (step : State → State → Prop)
  (left right : Set State)

/-- Reachability by the reconfiguration relation. -/
abbrev Reach : State → State → Prop := Relation.ReflTransGen step

/-- Kempe switches are reversible, so reachability in the reconfiguration
graph is symmetric.  The source states the criterion for a graph, where this
is implicit; here it is an explicit hypothesis. -/
theorem reach_symm (hsymm : ∀ x y : State, step x y → step y x) {x y : State}
    (hreach : Reach step x y) : Reach step y x := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Relation.ReflTransGen.single (hsymm _ _ hstep)).trans ih

/-- **Sufficiency.**  With both sides internally connected and covering the
whole colouring set, a cross path joins everything: go inside your own side to
the path's endpoint, cross it in whichever direction is needed, then go inside
the far side. -/
theorem reach_of_cross (hsymm : ∀ x y : State, step x y → step y x)
    (hcover : ∀ state, state ∈ left ∨ state ∈ right)
    (hleft : ∀ x ∈ left, ∀ y ∈ left, Reach step x y)
    (hright : ∀ x ∈ right, ∀ y ∈ right, Reach step x y)
    {p q : State} (hp : p ∈ left) (hq : q ∈ right)
    (hcross : Reach step p q) :
    ∀ x y : State, Reach step x y := by
  intro x y
  rcases hcover x with hx | hx <;> rcases hcover y with hy | hy
  · exact hleft x hx y hy
  · exact ((hleft x hx p hp).trans hcross).trans (hright q hq y hy)
  · exact ((hright x hx q hq).trans (reach_symm step hsymm hcross)).trans
      (hleft p hp y hy)
  · exact hright x hx y hy

/-- **One side empty.**  If a side is empty the other is everything, so
internal connectedness is connectedness. -/
theorem reach_of_left_empty
    (hcover : ∀ state, state ∈ left ∨ state ∈ right)
    (hright : ∀ x ∈ right, ∀ y ∈ right, Reach step x y)
    (hempty : ∀ state, state ∉ left) :
    ∀ x y : State, Reach step x y := by
  intro x y
  exact hright x ((hcover x).resolve_left (hempty x)) y
    ((hcover y).resolve_left (hempty y))

/-- **Necessity.**  If everything is connected then any two nonempty sides are
joined by a path. -/
theorem cross_of_reach (hreach : ∀ x y : State, Reach step x y)
    {p q : State} (_hp : p ∈ left) (_hq : q ∈ right) : Reach step p q :=
  hreach p q

end ConnectedUnion

end GoertzelV24SquareLadder

end Mettapedia.GraphTheory.FourColor

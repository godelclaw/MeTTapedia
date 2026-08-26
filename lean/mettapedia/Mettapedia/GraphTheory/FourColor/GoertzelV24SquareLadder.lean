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

/-! ## The target-aware criterion

Full connectivity is stronger than the route needs.  With a target set of
states, what matters is that every state can reach a target, and that splits
by side: a state already in a target-bearing side is finished by the sidewise
statement, and a state in a target-free side needs only to reach some
target-bearing side first. -/

section TargetAware

variable {State Side : Type*} (step : State → State → Prop)
  (sides : Side → Set State) (target : Set State)

/-- Reachability that stays inside a set. -/
abbrev ReachIn (region : Set State) : State → State → Prop :=
  Relation.ReflTransGen (fun x y => step x y ∧ x ∈ region ∧ y ∈ region)

/-- Staying inside is a special case of reaching. -/
theorem reach_of_reachIn {region : Set State} {x y : State}
    (hreach : ReachIn step region x y) : Reach step x y := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (Relation.ReflTransGen.single hstep.1)

/-- A side bears a target when some target state lies in it. -/
def TargetBearing (s : Side) : Prop := ∃ w ∈ target, w ∈ sides s

/-- **The target-aware criterion.**  Given the sidewise statement, reaching a
target from everywhere is exactly the ability of each target-free side to
reach some target-bearing side. -/
theorem reach_target_iff_targetFree_reaches_bearing
    (hcover : ∀ x : State, ∃ s, x ∈ sides s)
    (hsidewise : ∀ s : Side, TargetBearing sides target s →
      ∀ x ∈ sides s, ∃ w, w ∈ target ∧ w ∈ sides s ∧
        ReachIn step (sides s) x w) :
    (∀ x : State, ∃ w ∈ target, Reach step x w) ↔
      (∀ s : Side, ¬ TargetBearing sides target s → ∀ x ∈ sides s,
        ∃ t : Side, TargetBearing sides target t ∧
          ∃ y ∈ sides t, Reach step x y) := by
  constructor
  · intro hglobal s _hfree x _hx
    obtain ⟨w, hw, hreach⟩ := hglobal x
    obtain ⟨t, ht⟩ := hcover w
    exact ⟨t, ⟨w, hw, ht⟩, w, ht, hreach⟩
  · intro hcross x
    obtain ⟨s, hs⟩ := hcover x
    by_cases hbearing : TargetBearing sides target s
    · obtain ⟨w, hw, _, hreach⟩ := hsidewise s hbearing x hs
      exact ⟨w, hw, reach_of_reachIn step hreach⟩
    · obtain ⟨t, hbear, y, hy, hxy⟩ := hcross s hbearing x hs
      obtain ⟨w, hw, _, hreach⟩ := hsidewise t hbear y hy
      exact ⟨w, hw, hxy.trans (reach_of_reachIn step hreach)⟩

end TargetAware

/-! ## Square-side path lifting

The lifting mechanism is a projection from one side onto the reduction's
colourings.  Surjectivity, connected fibres, and the lifting of every legal
edge to a path together carry connectedness downstairs to connectedness
upstairs.  Establishing the three properties for the square is the graph-level
work; the consequence is general and is proved here. -/

section PathLifting

variable {Upper Lower : Type*} (upperStep : Upper → Upper → Prop)
  (lowerStep : Lower → Lower → Prop) (project : Upper → Lower)

/-- The three properties the square layer must supply for one reduction
side. -/
structure SidePathLifting : Prop where
  /-- Every colouring of the reduction expands to the side. -/
  surjective : Function.Surjective project
  /-- The local fibre over a colouring is connected by side moves. -/
  connectedFibres : ∀ x y : Upper, project x = project y →
    Relation.ReflTransGen upperStep x y
  /-- Every legal edge downstairs lifts to a path upstairs. -/
  liftsEdges : ∀ x : Upper, ∀ b : Lower, lowerStep (project x) b →
    ∃ y : Upper, project y = b ∧ Relation.ReflTransGen upperStep x y

variable {upperStep lowerStep project}

/-- A path downstairs lifts to a path upstairs from any chosen start. -/
theorem lift_path (hlift : SidePathLifting upperStep lowerStep project)
    {a b : Lower} (hpath : Relation.ReflTransGen lowerStep a b) :
    ∀ x : Upper, project x = a →
      ∃ y : Upper, project y = b ∧ Relation.ReflTransGen upperStep x y := by
  induction hpath with
  | refl => exact fun x hx => ⟨x, hx, Relation.ReflTransGen.refl⟩
  | tail _hpath hstep ih =>
      intro x hx
      obtain ⟨y, hy, hxy⟩ := ih x hx
      obtain ⟨z, hz, hyz⟩ := hlift.liftsEdges y _ (by rw [hy]; exact hstep)
      exact ⟨z, hz, hxy.trans hyz⟩

/-- **Square-side path lifting.**  Connectedness of the reduction's
reconfiguration graph implies connectedness of the side. -/
theorem reflTransGen_of_sidePathLifting
    (hlift : SidePathLifting upperStep lowerStep project)
    (hlower : ∀ a b : Lower, Relation.ReflTransGen lowerStep a b)
    (x y : Upper) : Relation.ReflTransGen upperStep x y := by
  obtain ⟨z, hz, hxz⟩ := lift_path hlift (hlower (project x) (project y)) x rfl
  exact hxz.trans (hlift.connectedFibres z y hz)

end PathLifting

end GoertzelV24SquareLadder

end Mettapedia.GraphTheory.FourColor

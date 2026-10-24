import Mettapedia.OSLF.Framework.DerivedModalities
import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Basic

/-!
# Backward search: the least solution of `X = goal ∨ ◇X`

OSLF derives the step-future modality from the reduction span, `◇ = ∃_src ∘ tgt*`. Read on
predicates, `◇ φ` is the set of states with a step into `φ`: a pre-image. Searching backward from
a goal is therefore iterating `◇`. The states that can reach the goal (`Reaches`) are the least
solution of `X = goal ∨ ◇ X`:

- `reaches_stage`, `reaches_least`: `Reaches` is a prefixed point of `stage goal`, and below every
  other one; in the poset of predicates it is the initial algebra of `stage goal`.
- `reaches_eq_lfp`: it is the least fixed point.
- `reaches_iff_chain`: it is the union of the initial chain `⊥ ≤ stage ⊥ ≤ stage² ⊥ ≤ …`, whose
  `n`-th member is "reaches the goal in fewer than `n` steps". Searching level by level, oldest
  first, enumerates exactly this chain.

The chain needs no more than `ω` steps for a structural reason: `◇` is a left adjoint
(`derived_galois`, `◇ ⊣ □`), so it preserves every union, and the union of the chain is already a
fixed point (`stage_iSup_chain`). No finiteness or decidability is assumed; the reduction span may
be infinite and infinitely branching backward.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardSearch

open Mettapedia.OSLF.Framework.DerivedModalities

variable {X : Type*} (span : ReductionSpan X) (goal : X → Prop)

/-- **The states that can reach the goal**: the goal, or a step into such a state. -/
inductive Reaches : X → Prop
  | goal {state : X} : goal state → Reaches state
  | step (event : span.Edge) : Reaches (span.target event) → Reaches (span.source event)

/-- One stage of backward search: the goal, or a step into the current set. -/
def stage (current : X → Prop) : X → Prop :=
  fun state => goal state ∨ derivedDiamond span current state

theorem stage_mono : Monotone (stage span goal) := by
  intro first second le state holds
  rcases holds with atGoal | ⟨event, starts, inside⟩
  · exact Or.inl atGoal
  · exact Or.inr ⟨event, starts, le _ inside⟩

/-- The stage as an order homomorphism of predicates. -/
def stageHom : (X → Prop) →o (X → Prop) := ⟨stage span goal, stage_mono span goal⟩

/-- **The initial chain**: nothing, then the stage applied again and again. -/
def chain : Nat → X → Prop
  | 0 => fun _ => False
  | count + 1 => stage span goal (chain count)

variable {span goal}

/-! ## The initial algebra -/

/-- `Reaches` is closed under the stage. -/
theorem reaches_stage : stage span goal (Reaches span goal) ≤ Reaches span goal := by
  intro state holds
  rcases holds with atGoal | ⟨event, starts, inside⟩
  · exact .goal atGoal
  · rw [← starts]; exact .step event inside

/-- **`Reaches` lies below every set closed under the stage**: it is the initial algebra. -/
theorem reaches_least {closed : X → Prop} (prefixed : stage span goal closed ≤ closed) :
    Reaches span goal ≤ closed := by
  intro state reaches
  induction reaches with
  | goal atGoal => exact prefixed _ (Or.inl atGoal)
  | step event _ ih => exact prefixed _ (Or.inr ⟨event, rfl, ih⟩)

/-- **`Reaches` is the least fixed point of the stage.** -/
theorem reaches_eq_lfp : Reaches span goal = OrderHom.lfp (stageHom span goal) := by
  apply le_antisymm
  · exact reaches_least (OrderHom.map_lfp (stageHom span goal)).le
  · exact OrderHom.lfp_le _ reaches_stage

theorem reaches_fixed : stage span goal (Reaches span goal) = Reaches span goal := by
  rw [reaches_eq_lfp]
  exact OrderHom.map_lfp (stageHom span goal)

/-! ## The initial chain -/

theorem chain_le_reaches : ∀ count, chain span goal count ≤ Reaches span goal
  | 0 => fun _ holds => holds.elim
  | count + 1 => (stage_mono span goal (chain_le_reaches count)).trans reaches_stage

theorem chain_mono_succ : ∀ count, chain span goal count ≤ chain span goal (count + 1)
  | 0 => fun _ holds => holds.elim
  | count + 1 => stage_mono span goal (chain_mono_succ count)

theorem chain_mono : Monotone (chain span goal) :=
  monotone_nat_of_le_succ chain_mono_succ

/-- **Reaching the goal is lying on the initial chain**: a state reaches the goal in `n` steps
exactly when it enters the chain at stage `n + 1`. -/
theorem reaches_iff_chain {state : X} : Reaches span goal state ↔ ∃ count, chain span goal count state := by
  constructor
  · intro reaches
    induction reaches with
    | goal atGoal => exact ⟨1, Or.inl atGoal⟩
    | step event _ ih =>
      obtain ⟨count, inside⟩ := ih
      exact ⟨count + 1, Or.inr ⟨event, rfl, inside⟩⟩
  · rintro ⟨count, inside⟩
    exact chain_le_reaches count _ inside

/-- **Why `ω` stages suffice**: `◇` is a left adjoint, so it preserves the union of the chain, and
that union is already closed under the stage. -/
theorem stage_iSup_chain :
    stage span goal (⨆ count, chain span goal count) = ⨆ count, chain span goal (count + 1) := by
  have preserved : derivedDiamond span (⨆ count, chain span goal count) =
      ⨆ count, derivedDiamond span (chain span goal count) :=
    (derived_galois span).l_iSup
  funext state
  simp only [stage, preserved, iSup_apply, iSup_Prop_eq, chain]
  apply propext
  constructor
  · rintro (atGoal | ⟨count, inside⟩)
    · exact ⟨0, Or.inl atGoal⟩
    · exact ⟨count, Or.inr inside⟩
  · rintro ⟨count, atGoal | inside⟩
    · exact Or.inl atGoal
    · exact Or.inr ⟨count, inside⟩

/-- The union of the initial chain is the least fixed point. -/
theorem iSup_chain_eq_reaches : (⨆ count, chain span goal count) = Reaches span goal := by
  apply le_antisymm
  · exact iSup_le chain_le_reaches
  · apply reaches_least
    rw [stage_iSup_chain]
    exact iSup_le fun count => le_iSup (chain span goal) (count + 1)


/-! ## Spans that agree on an invariant -/

/-- **Reaching a goal depends only on the steps from the states that matter**: two spans whose steps
agree on an invariant closed under the first one's steps reach the same goals from it. -/
theorem reaches_transfer {first second : ReductionSpan X} (good : X → Prop)
    (closed : ∀ event : first.Edge, good (first.source event) → good (first.target event))
    (agree : ∀ source target, good source →
      ((∃ event : first.Edge, first.source event = source ∧ first.target event = target) ↔
        ∃ event : second.Edge, second.source event = source ∧ second.target event = target))
    {state : X} (stateGood : good state) : Reaches first goal state ↔ Reaches second goal state := by
  constructor
  · intro reaches
    induction reaches with
    | goal atGoal => exact .goal atGoal
    | step event _ ih =>
      obtain ⟨other, starts, ends⟩ := (agree _ _ stateGood).mp ⟨event, rfl, rfl⟩
      rw [← starts]
      exact .step other (ends ▸ ih (closed event stateGood))
  · intro reaches
    induction reaches with
    | goal atGoal => exact .goal atGoal
    | step event _ ih =>
      obtain ⟨other, starts, ends⟩ := (agree _ _ stateGood).mpr ⟨event, rfl, rfl⟩
      have targetGood : good (second.target event) := by
        rw [← ends]; exact closed other (starts ▸ stateGood)
      rw [← starts]
      exact .step other (ends ▸ ih targetGood)

/-! ## Spans between good states -/

/-- The steps of a span between good states. -/
def between (base : ReductionSpan X) (good : X → Prop) : ReductionSpan X where
  Edge := {event : base.Edge // good (base.source event) ∧ good (base.target event)}
  source event := base.source event.1
  target event := base.target event.1

/-- **Two spans with the same steps between good states have the same backward box over them.** -/
theorem box_between_transfer {first second : ReductionSpan X} (good : X → Prop)
    (agree : ∀ source target, good source → good target →
      ((∃ event : first.Edge, first.source event = source ∧ first.target event = target) ↔
        ∃ event : second.Edge, second.source event = source ∧ second.target event = target))
    (property : X → Prop) (state : X) :
    derivedBox (between first good) property state ↔ derivedBox (between second good) property state := by
  constructor
  · rintro holds ⟨event, sourceGood, targetGood⟩ ends
    obtain ⟨matched, starts, stops⟩ := (agree _ _ sourceGood targetGood).mpr ⟨event, rfl, rfl⟩
    show property (second.source event)
    rw [← starts]
    exact holds ⟨matched, starts ▸ sourceGood, stops ▸ targetGood⟩ (stops.trans ends)
  · rintro holds ⟨event, sourceGood, targetGood⟩ ends
    obtain ⟨matched, starts, stops⟩ := (agree _ _ sourceGood targetGood).mp ⟨event, rfl, rfl⟩
    show property (first.source event)
    rw [← starts]
    exact holds ⟨matched, starts ▸ sourceGood, stops ▸ targetGood⟩ (stops.trans ends)


/-- A run that stays among good states is a run between them. -/
theorem reaches_between_of_closed {base : ReductionSpan X} {good : X → Prop}
    (closed : ∀ event : base.Edge, good (base.source event) → good (base.target event)) {state : X}
    (stateGood : good state) (reaches : Reaches base goal state) : Reaches (between base good) goal state := by
  revert stateGood
  induction reaches with
  | goal atGoal => exact fun _ => .goal atGoal
  | step event _ ih =>
    intro sourceGood
    exact Reaches.step (span := between base good) ⟨event, sourceGood, closed event sourceGood⟩
      (ih (closed event sourceGood))

/-- Runs between good states are runs between better ones. -/
theorem reaches_between_mono {base : ReductionSpan X} {small large : X → Prop} (within : ∀ state, small state → large state)
    {state : X} (reaches : Reaches (between base small) goal state) : Reaches (between base large) goal state := by
  induction reaches with
  | goal atGoal => exact .goal atGoal
  | step event _ ih =>
    exact Reaches.step (span := between base large) ⟨event.1, within _ event.2.1, within _ event.2.2⟩ ih

end Mettapedia.OSLF.Framework.BackwardSearch

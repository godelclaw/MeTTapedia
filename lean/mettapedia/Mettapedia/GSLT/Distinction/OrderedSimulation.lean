import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation

/-!
# Ordered relations between nondeterministic machines

A nondeterministic machine whose step returns its successor occurrences as an
ordered list, with a halting test, runs a frontier: every occurrence advances
in place, an occurrence without successors stays, and an entirely halted
frontier stays. Individual halted occurrences are inert under the explicit
halting-stability premise used by `runFrontier_distribute`. Two such machines are
compared on their actual states, not on answer sets or endpoints.

* **Ordered simulations** (`OrderedSimulation`).  Related states agree on
  halting, and their successor lists are related position by position: equal
  length, the same order, every occurrence kept, equal-looking occurrences not
  merged.  The relation need not be a function.
* **Complete frontiers** (`OrderedSimulation.runFrontier`).  At every fuel,
  related frontiers are related position by position, so pending occurrences
  and their order are transported, not only halted ones
  (`OrderedSimulation.answers`).
* **Two-sided by construction** (`OrderedSimulation.symm`).  Position-by-
  position relation of successor lists lifts source occurrences to the target
  and target occurrences to the source; relations compose
  (`OrderedSimulation.comp`).
* **Functional instances** (`OrderedSimulation.ofMap`,
  `OrderedSimulation.runFrontier_map`): a map that commutes with the step lists
  and the halting test is the graph special case.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

universe u v w

/-- An ordered nondeterministic machine: successor occurrences in order, and a
halting test. -/
structure OrderedSystem (State : Type u) where
  step : State → List State
  halted : State → Bool

namespace OrderedSystem

variable {State : Type u} (system : OrderedSystem State)

/-- One frontier advance: a state without successors stays. -/
def advance (state : State) : List State :=
  match system.step state with
  | [] => [state]
  | next => next

/-- Run a frontier until it has halted or the fuel is spent. -/
def runFrontier : ℕ → List State → List State
  | 0, states => states
  | fuel + 1, states =>
      if states.all system.halted then states else runFrontier fuel (states.flatMap system.advance)

/-- The complete frontier, including halted and pending occurrences, is the
residual. Splitting a budget continues that frontier rather than reloading its
initial states. -/
theorem runFrontier_add (first second : ℕ) (states : List State) :
    system.runFrontier (first + second) states =
      system.runFrontier second (system.runFrontier first states) := by
  induction first generalizing states with
  | zero => simp only [Nat.zero_add, runFrontier]
  | succ first ih =>
      rw [show first + 1 + second = (first + second) + 1 by omega]
      by_cases stopped : states.all system.halted = true
      · cases second <;> simp only [runFrontier, stopped, if_true]
      · simp [runFrontier, stopped, ih]

theorem runFrontier_halted (fuel : ℕ) (states : List State)
    (halted : states.all system.halted = true) : system.runFrontier fuel states = states := by
  cases fuel <;> simp only [runFrontier, halted, if_true]

/-- Local halting must have no successors to justify distributing a synchronous
frontier across independently serviced blocks. `OrderedSystem` itself does not
silently impose that condition. -/
theorem halted_frontier_advance
    (stable : ∀ state, system.halted state = true → system.step state = [])
    (states : List State) (halted : states.all system.halted = true) :
    states.flatMap system.advance = states := by
  induction states with
  | nil => rfl
  | cons state states ih =>
      simp only [List.all_cons, Bool.and_eq_true] at halted
      simp only [List.flatMap_cons, advance, stable state halted.1, List.singleton_append,
        ih halted.2]

theorem runFrontier_succ
    (stable : ∀ state, system.halted state = true → system.step state = [])
    (fuel : ℕ) (states : List State) :
    system.runFrontier (fuel + 1) states =
      system.runFrontier fuel (states.flatMap system.advance) := by
  by_cases halted : states.all system.halted = true
  · rw [halted_frontier_advance system stable states halted]
    rw [runFrontier_halted system _ states halted, runFrontier_halted system _ states halted]
  · simp [runFrontier, halted]

theorem runFrontier_append
    (stable : ∀ state, system.halted state = true → system.step state = [])
    (fuel : ℕ) (first second : List State) :
    system.runFrontier fuel (first ++ second) =
      system.runFrontier fuel first ++ system.runFrontier fuel second := by
  induction fuel generalizing first second with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFrontier_succ system stable, List.flatMap_append, ih]

@[simp] theorem runFrontier_nil (fuel : ℕ) : system.runFrontier fuel [] = [] := by
  cases fuel <;> simp only [runFrontier, List.all_nil, if_true]

/-- Independent local runs reproduce the synchronous frontier precisely when
halted states are inert. Blocks stay in source order and duplicates remain. -/
theorem runFrontier_distribute
    (stable : ∀ state, system.halted state = true → system.step state = [])
    (fuel : ℕ) (states : List State) :
    system.runFrontier fuel states =
      states.flatMap (fun state => system.runFrontier fuel [state]) := by
  induction states with
  | nil => exact runFrontier_nil system fuel
  | cons state states ih =>
      rw [show state :: states = [state] ++ states from rfl,
        runFrontier_append system stable, ih]
      rfl

end OrderedSystem

/-- **An ordered simulation**: related states agree on halting, and their
successor occurrences are related position by position. -/
structure OrderedSimulation {S : Type u} {T : Type v} (source : OrderedSystem S)
    (target : OrderedSystem T) (related : S → T → Prop) : Prop where
  halted : ∀ {state state'}, related state state' → target.halted state' = source.halted state
  step : ∀ {state state'}, related state state' →
    List.Forall₂ related (source.step state) (target.step state')

namespace OrderedSimulation

variable {S : Type u} {T : Type v} {source : OrderedSystem S} {target : OrderedSystem T}
  {related : S → T → Prop}

theorem forall₂_flatMap {α : Type u} {β : Type v} {γ : Type u} {δ : Type v}
    {first : α → β → Prop} {second : γ → δ → Prop} {f : α → List γ} {g : β → List δ}
    {left : List α} {right : List β} (lists : List.Forall₂ first left right)
    (pointwise : ∀ {a b}, first a b → List.Forall₂ second (f a) (g b)) :
    List.Forall₂ second (left.flatMap f) (right.flatMap g) := by
  induction lists with
  | nil => exact List.Forall₂.nil
  | cons head _ ih => exact List.rel_append (pointwise head) ih

theorem advance (simulation : OrderedSimulation source target related) {state : S} {state' : T}
    (relatedStates : related state state') :
    List.Forall₂ related (source.advance state) (target.advance state') := by
  have steps := simulation.step relatedStates
  unfold OrderedSystem.advance
  generalize source.step state = sourceSteps at steps ⊢
  generalize target.step state' = targetSteps at steps ⊢
  cases steps with
  | nil => exact List.Forall₂.cons relatedStates List.Forall₂.nil
  | cons head rest => exact List.Forall₂.cons head rest

theorem all_halted (simulation : OrderedSimulation source target related) {states : List S}
    {states' : List T} (lists : List.Forall₂ related states states') :
    states'.all target.halted = states.all source.halted := by
  induction lists with
  | nil => rfl
  | cons head _ ih => simp [List.all_cons, simulation.halted head, ih]

/-- **Complete frontiers are related at every fuel**, position by position. -/
theorem runFrontier (simulation : OrderedSimulation source target related) (fuel : ℕ)
    {states : List S} {states' : List T} (lists : List.Forall₂ related states states') :
    List.Forall₂ related (source.runFrontier fuel states) (target.runFrontier fuel states') := by
  induction fuel generalizing states states' with
  | zero => exact lists
  | succ fuel ih =>
      simp only [OrderedSystem.runFrontier, simulation.all_halted lists]
      split
      · exact lists
      · exact ih (forall₂_flatMap lists simulation.advance)

/-- **Answers are related in order**, for any outcome readings related on
related states. -/
theorem answers {A : Type w} {B : Type w} (simulation : OrderedSimulation source target related)
    {outcome : S → Option A} {outcome' : T → Option B} {agree : A → B → Prop}
    (outcomes : ∀ {state state'}, related state state' → Option.Rel agree (outcome state) (outcome' state'))
    (fuel : ℕ) {state : S} {state' : T} (relatedStates : related state state') :
    List.Forall₂ agree ((source.runFrontier fuel [state]).filterMap outcome)
      ((target.runFrontier fuel [state']).filterMap outcome') := by
  have frontiers := simulation.runFrontier fuel (List.Forall₂.cons relatedStates List.Forall₂.nil)
  generalize source.runFrontier fuel [state] = sourceFrontier at frontiers ⊢
  generalize target.runFrontier fuel [state'] = targetFrontier at frontiers ⊢
  induction frontiers with
  | nil => exact List.Forall₂.nil
  | @cons first second _ _ head _ ih =>
      have pair := outcomes head
      rw [List.filterMap_cons, List.filterMap_cons]
      cases sourceOutcome : outcome first with
      | none =>
          cases targetOutcome : outcome' second with
          | none => exact ih
          | some _ =>
              rw [sourceOutcome, targetOutcome] at pair
              cases pair
      | some _ =>
          cases targetOutcome : outcome' second with
          | none =>
              rw [sourceOutcome, targetOutcome] at pair
              cases pair
          | some _ =>
              rw [sourceOutcome, targetOutcome] at pair
              cases pair with
              | some agreed => exact List.Forall₂.cons agreed ih

theorem forall₂_swap {α : Type u} {β : Type v} {relation : α → β → Prop} {left : List α}
    {right : List β} (lists : List.Forall₂ relation left right) :
    List.Forall₂ (fun b a => relation a b) right left := by
  induction lists with
  | nil => exact List.Forall₂.nil
  | cons head _ ih => exact List.Forall₂.cons head ih

/-- **Ordered simulations are two-sided**: the converse relation simulates
back. -/
theorem symm (simulation : OrderedSimulation source target related) :
    OrderedSimulation target source (fun state' state => related state state') where
  halted relatedStates := (simulation.halted relatedStates).symm
  step relatedStates := forall₂_swap (simulation.step relatedStates)

theorem forall₂_comp {α : Type u} {β : Type v} {γ : Type w} {first : α → β → Prop}
    {second : β → γ → Prop} {left : List α} {middle : List β} {right : List γ}
    (one : List.Forall₂ first left middle) (two : List.Forall₂ second middle right) :
    List.Forall₂ (Relation.Comp first second) left right := by
  induction one generalizing right with
  | nil => cases two; exact List.Forall₂.nil
  | cons head _ ih =>
      cases two with
      | cons head' rest' => exact List.Forall₂.cons ⟨_, head, head'⟩ (ih rest')

/-- Ordered simulations compose. -/
theorem comp {W : Type w} {third : OrderedSystem W} {next : T → W → Prop}
    (first : OrderedSimulation source target related)
    (second : OrderedSimulation target third next) :
    OrderedSimulation source third (Relation.Comp related next) where
  halted := by
    rintro _ _ ⟨middle, one, two⟩
    exact (second.halted two).trans (first.halted one)
  step := by
    rintro _ _ ⟨middle, one, two⟩
    exact forall₂_comp (first.step one) (second.step two)

/-- A map commuting with the step lists and the halting test is an ordered
simulation of its graph. -/
theorem ofMap (map : S → T) (steps : ∀ state, target.step (map state) = (source.step state).map map)
    (halts : ∀ state, target.halted (map state) = source.halted state) :
    OrderedSimulation source target (fun state state' => state' = map state) where
  halted := by
    rintro state _ rfl
    exact halts state
  step := by
    rintro state _ rfl
    rw [steps, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun _ _ => rfl

/-- The graph instance recovers the functional frontier equation. -/
theorem runFrontier_map (map : S → T)
    (steps : ∀ state, target.step (map state) = (source.step state).map map)
    (halts : ∀ state, target.halted (map state) = source.halted state) (fuel : ℕ)
    (states : List S) :
    target.runFrontier fuel (states.map map) = (source.runFrontier fuel states).map map := by
  have related := (ofMap map steps halts).runFrontier fuel
    (states := states) (states' := states.map map)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
  have functional : ∀ {left : List S} {right : List T},
      List.Forall₂ (fun state state' => state' = map state) left right → right = left.map map := by
    intro left right lists
    induction lists with
    | nil => rfl
    | cons head _ ih => rw [head, ih, List.map_cons]
  exact functional related

end OrderedSimulation

end Mettapedia.GSLT.Distinction

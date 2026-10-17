import Mathlib.Data.List.Forall2
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Logic.Function.Iterate
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
* **Depth-first prefixes** (`OrderedSystem.expandFirst`,
  `OrderedSimulation.expandFirst_iterate`): the same simulation transports
  every unfinished prefix, retaining stuck occurrences and ordered alternatives.
* **Occurrence simulations** (`OccurrenceSimulation`). Related states agree on
  halting, and successor occurrences are related as bags (`Multiset.Rel`):
  multiplicity stays, and the two enumerations may differ. Every ordered
  simulation is an occurrence simulation. Synchronous `runFrontier` transports
  the whole frontier bag, including a client's full observation of each
  occurrence. Depth-first prefixes remain theorems of the ordered simulation.
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

/-- Expand the first running occurrence, retaining the halted prefix and the
remaining alternatives in order. As in `runFrontier`, a running occurrence
without successors stays visible; it cannot disappear as a successful return. -/
def expandFirst : List State → List State
  | [] => []
  | state :: rest =>
      if system.halted state then state :: expandFirst rest
      else system.advance state ++ rest

theorem expandFirst_append_of_all_halted {left : List State}
    (halted : left.all system.halted = true) (right : List State) :
    system.expandFirst (left ++ right) = left ++ system.expandFirst right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at halted
      simp [expandFirst, halted.1, ih halted.2]

theorem expandFirst_append_of_running {left : List State}
    (running : left.all system.halted = false) (right : List State) :
    system.expandFirst (left ++ right) = system.expandFirst left ++ right := by
  induction left with
  | nil => simp at running
  | cons head tail ih =>
      by_cases halted : system.halted head = true
      · simp only [List.all_cons, halted, Bool.true_and] at running
        simp [expandFirst, halted, ih running]
      · simp [expandFirst, halted]

theorem expandFirst_of_all_halted {states : List State}
    (halted : states.all system.halted = true) : system.expandFirst states = states := by
  simpa [expandFirst] using system.expandFirst_append_of_all_halted halted []

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

/-- The first running occurrence is selected at the same position on both
sides, including equal-looking alternatives at distinct positions. -/
theorem expandFirst (simulation : OrderedSimulation source target related)
    {states : List S} {states' : List T} (lists : List.Forall₂ related states states') :
    List.Forall₂ related (source.expandFirst states) (target.expandFirst states') := by
  induction lists with
  | nil => exact .nil
  | cons head rest ih =>
      simp only [OrderedSystem.expandFirst, simulation.halted head]
      split
      · exact .cons head ih
      · exact List.rel_append (simulation.advance head) rest

/-- Ordered simulation preserves every depth-first prefix, without requiring
that either computation terminates. -/
theorem expandFirst_iterate (simulation : OrderedSimulation source target related)
    (count : ℕ) {states : List S} {states' : List T}
    (lists : List.Forall₂ related states states') :
    List.Forall₂ related ((source.expandFirst)^[count] states)
      ((target.expandFirst)^[count] states') := by
  induction count generalizing states states' with
  | zero => exact lists
  | succ count ih =>
      simp only [Function.iterate_succ_apply]
      exact ih (simulation.expandFirst lists)

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

private theorem graph_frontier_eq (map : S → T) {left : List S} {right : List T}
    (lists : List.Forall₂ (fun state state' => state' = map state) left right) :
    right = left.map map := by
  induction lists with
  | nil => rfl
  | cons head _ ih => rw [head, ih, List.map_cons]

/-- The graph instance transports every depth-first prefix. -/
theorem expandFirst_iterate_map (map : S → T)
    (steps : ∀ state, target.step (map state) = (source.step state).map map)
    (halts : ∀ state, target.halted (map state) = source.halted state) (count : ℕ)
    (states : List S) :
    (target.expandFirst)^[count] (states.map map) =
      ((source.expandFirst)^[count] states).map map := by
  exact graph_frontier_eq map ((ofMap map steps halts).expandFirst_iterate count
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl)))

/-- The graph instance recovers the functional frontier equation. -/
theorem runFrontier_map (map : S → T)
    (steps : ∀ state, target.step (map state) = (source.step state).map map)
    (halts : ∀ state, target.halted (map state) = source.halted state) (fuel : ℕ)
    (states : List S) :
    target.runFrontier fuel (states.map map) = (source.runFrontier fuel states).map map := by
  have related := (ofMap map steps halts).runFrontier fuel
    (states := states) (states' := states.map map)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun _ _ => rfl))
  exact graph_frontier_eq map related

end OrderedSimulation

/-- **An occurrence simulation**: related states agree on halting, and their
successor occurrences are related as a bag. Lists stay the implementation of
`step`; the two enumerations may differ. Multiplicity is part of the relation. -/
structure OccurrenceSimulation {S : Type u} {T : Type v} (source : OrderedSystem S)
    (target : OrderedSystem T) (related : S → T → Prop) : Prop where
  halted : ∀ {state state'}, related state state' → target.halted state' = source.halted state
  step : ∀ {state state'}, related state state' →
    Multiset.Rel related (source.step state) (target.step state')

namespace OccurrenceSimulation

variable {S : Type u} {T : Type v} {source : OrderedSystem S} {target : OrderedSystem T}
  {related : S → T → Prop}

/-- Position-by-position related lists are related as occurrence bags. -/
theorem forall₂_multisetRel {α : Type u} {β : Type v} {r : α → β → Prop}
    {as : List α} {bs : List β} (lists : List.Forall₂ r as bs) : Multiset.Rel r as bs := by
  induction lists with
  | nil => exact .zero
  | cons head _ ih => exact .cons head ih

/-- List `flatMap` is Mathlib's multiset `bind` on the occurrence bags. -/
private theorem rel_flatMap.{uα, uβ, uγ, uδ} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    {δ : Type uδ} {r : α → β → Prop} {p : γ → δ → Prop} {f : α → List γ} {g : β → List δ}
    {left : List α} {right : List β} (lists : Multiset.Rel r left right)
    (pointwise : ∀ {a b}, r a b → Multiset.Rel p (f a) (g b)) :
    Multiset.Rel p (left.flatMap f) (right.flatMap g) := by
  simpa [Multiset.coe_bind] using Multiset.rel_bind (fun {_a _b} h => pointwise h) lists

private theorem multisetRel_comp {α : Type u} {β : Type v} {γ : Type w}
    {r : α → β → Prop} {s : β → γ → Prop} {as : Multiset α} {bs : Multiset β}
    {cs : Multiset γ} (one : Multiset.Rel r as bs) (two : Multiset.Rel s bs cs) :
    Multiset.Rel (Relation.Comp r s) as cs := by
  induction bs using Multiset.induction_on generalizing as cs with
  | empty =>
      rw [Multiset.rel_zero_right.mp one, Multiset.rel_zero_left.mp two]
      exact .zero
  | cons _ _ ih =>
      obtain ⟨a, as', ha, rest, rfl⟩ := Multiset.rel_cons_right.mp one
      obtain ⟨c, cs', hc, rest', rfl⟩ := Multiset.rel_cons_left.mp two
      exact .cons ⟨_, ha, hc⟩ (ih rest rest')

private theorem filterMap_eq_flatMap_toList.{uα, uβ} {α : Type uα} {β : Type uβ}
    (f : α → Option β) :
    ∀ l : List α, l.filterMap f = l.flatMap (fun a => (f a).toList)
  | [] => rfl
  | a :: l => by
      rw [List.filterMap_cons, List.flatMap_cons, filterMap_eq_flatMap_toList f l]
      cases f a <;> rfl

/-- Every ordered simulation is an occurrence simulation. Position-by-position
successor lists are bags with that order forgotten and every occurrence kept. -/
theorem ofOrdered (simulation : OrderedSimulation source target related) :
    OccurrenceSimulation source target related where
  halted := simulation.halted
  step := fun relatedStates => forall₂_multisetRel (simulation.step relatedStates)

/-- The identity relation is an occurrence simulation. -/
theorem refl {State : Type u} (system : OrderedSystem State) :
    OccurrenceSimulation system system (· = ·) where
  halted := by
    rintro _ _ rfl
    rfl
  step := by
    rintro _ _ rfl
    exact Multiset.rel_eq_refl

/-- **Occurrence simulations are two-sided**: the converse relation simulates back. -/
theorem symm (simulation : OccurrenceSimulation source target related) :
    OccurrenceSimulation target source (fun state' state => related state state') where
  halted relatedStates := (simulation.halted relatedStates).symm
  step relatedStates := (Multiset.rel_flip).mpr (simulation.step relatedStates)

/-- Occurrence simulations compose, through Mathlib's relational composition. -/
theorem comp {W : Type w} {third : OrderedSystem W} {next : T → W → Prop}
    (first : OccurrenceSimulation source target related)
    (second : OccurrenceSimulation target third next) :
    OccurrenceSimulation source third (Relation.Comp related next) where
  halted := by
    rintro _ _ ⟨middle, one, two⟩
    exact (second.halted two).trans (first.halted one)
  step := by
    rintro _ _ ⟨middle, one, two⟩
    exact multisetRel_comp (first.step one) (second.step two)

/-- A related advance keeps a bag of related occurrences. An empty successor
list retains the related state as a singleton, so a stuck occurrence stays. -/
theorem advance (simulation : OccurrenceSimulation source target related) {state : S} {state' : T}
    (relatedStates : related state state') :
    Multiset.Rel related (source.advance state) (target.advance state') := by
  have steps := simulation.step relatedStates
  cases sourceSteps : source.step state with
  | nil =>
      rw [sourceSteps] at steps
      have targetBag : (target.step state' : Multiset T) = 0 :=
        Multiset.rel_zero_left.mp (by simpa only [Multiset.coe_nil] using steps)
      have targetSteps : target.step state' = [] := (Multiset.coe_eq_zero _).mp targetBag
      simp only [OrderedSystem.advance, sourceSteps, targetSteps]
      exact .cons relatedStates .zero
  | cons head tail =>
      cases targetSteps : target.step state' with
      | nil =>
          rw [sourceSteps, targetSteps] at steps
          have sourceBag : (head :: tail : Multiset S) = 0 :=
            Multiset.rel_zero_right.mp (by simpa only [Multiset.coe_nil] using steps)
          cases (Multiset.coe_eq_zero _).mp sourceBag
      | cons _ _ =>
          simp only [OrderedSystem.advance, sourceSteps, targetSteps]
          rw [sourceSteps, targetSteps] at steps
          exact steps

/-- Related frontier bags agree on whether every occurrence has halted. -/
theorem all_halted (simulation : OccurrenceSimulation source target related) {states : List S}
    {states' : List T} (lists : Multiset.Rel related states states') :
    states'.all target.halted = states.all source.halted := by
  suffices states.all source.halted = true ↔ states'.all target.halted = true by
    cases sourceHalted : states.all source.halted <;>
      cases targetHalted : states'.all target.halted <;> simp_all
  constructor
  · intro sourceHalted
    rw [List.all_eq_true] at sourceHalted ⊢
    intro state' member
    have reversed := (Multiset.rel_flip).mpr lists
    obtain ⟨state, stateMember, relatedStates⟩ :=
      Multiset.exists_mem_of_rel_of_mem reversed (Multiset.mem_coe.mpr member)
    exact (simulation.halted relatedStates).trans
      (sourceHalted state (Multiset.mem_coe.mp stateMember))
  · intro targetHalted
    rw [List.all_eq_true] at targetHalted ⊢
    intro state member
    obtain ⟨state', state'Member, relatedStates⟩ :=
      Multiset.exists_mem_of_rel_of_mem lists (Multiset.mem_coe.mpr member)
    exact (simulation.halted relatedStates).symm.trans
      (targetHalted state' (Multiset.mem_coe.mp state'Member))

/-- **Complete frontier bags agree at every source-depth budget.** Each fuel
value is one synchronous round of `runFrontier` on both machines. Pending,
stuck, and halted occurrences stay in the bag. `OrderedSystem.runFrontier_add`
remains the split of one worker's own budget. -/
theorem runFrontier (simulation : OccurrenceSimulation source target related) (fuel : ℕ)
    {states : List S} {states' : List T} (lists : Multiset.Rel related states states') :
    Multiset.Rel related (source.runFrontier fuel states) (target.runFrontier fuel states') := by
  induction fuel generalizing states states' with
  | zero => exact lists
  | succ fuel ih =>
      cases halted : states.all source.halted with
      | true =>
          simp only [OrderedSystem.runFrontier, simulation.all_halted lists, halted, if_true]
          exact lists
      | false =>
          simp only [OrderedSystem.runFrontier, simulation.all_halted lists, halted]
          exact ih (rel_flatMap lists simulation.advance)

/-- A client reading of every frontier occurrence lifts to the occurrence bags.
`agree` relates the whole observation, so the reading can carry bindings and
provenance. Pending, stuck, and halted occurrences each contribute a reading. -/
theorem observe {A : Type w} {B : Type w} (simulation : OccurrenceSimulation source target related)
    {read : S → A} {read' : T → B} {agree : A → B → Prop}
    (reads : ∀ {state state'}, related state state' → agree (read state) (read' state'))
    (fuel : ℕ) {states : List S} {states' : List T}
    (lists : Multiset.Rel related states states') :
    Multiset.Rel agree ((source.runFrontier fuel states).map read)
      ((target.runFrontier fuel states').map read') := by
  rw [← Multiset.map_coe, ← Multiset.map_coe]
  exact Multiset.rel_map.mpr
    ((simulation.runFrontier fuel lists).mono fun _ _ _ _ relatedStates => reads relatedStates)

/-- Successful outcome readings that agree on related states lift to bags.
Agreement is on the whole outcome value. An occurrence whose reading is empty
on one side is empty on the other, and it stays present in `runFrontier`. -/
theorem outcomes {A : Type w} {B : Type w} (simulation : OccurrenceSimulation source target related)
    {outcome : S → Option A} {outcome' : T → Option B} {agree : A → B → Prop}
    (compatible : ∀ {state state'}, related state state' →
      Option.Rel agree (outcome state) (outcome' state'))
    (fuel : ℕ) {states : List S} {states' : List T}
    (lists : Multiset.Rel related states states') :
    Multiset.Rel agree ((source.runFrontier fuel states).filterMap outcome)
      ((target.runFrontier fuel states').filterMap outcome') := by
  rw [filterMap_eq_flatMap_toList outcome, filterMap_eq_flatMap_toList outcome']
  refine rel_flatMap (simulation.runFrontier fuel lists) ?_
  intro state state' relatedStates
  have pair := compatible relatedStates
  cases sourceReading : outcome state with
  | none =>
      cases targetReading : outcome' state' with
      | none =>
          rw [sourceReading, targetReading] at pair
          cases pair
          exact .zero
      | some _ =>
          rw [sourceReading, targetReading] at pair
          cases pair
  | some _ =>
      cases targetReading : outcome' state' with
      | none =>
          rw [sourceReading, targetReading] at pair
          cases pair
      | some _ =>
          rw [sourceReading, targetReading] at pair
          cases pair with
          | some agreed => exact .cons agreed .zero

end OccurrenceSimulation

namespace OccurrenceControls

/- Finite machines whose successor facts are the step lists of those machines. -/

inductive Chip where
  | root | left | right | extra
  deriving DecidableEq, Repr

def chipHalted : Chip → Bool
  | .root => false
  | _ => true

/-- Successors enumerated left, then right. -/
def orderedPair : OrderedSystem Chip where
  step
    | .root => [.left, .right]
    | _ => []
  halted := chipHalted

/-- The same successors enumerated right, then left. -/
def reorderedPair : OrderedSystem Chip where
  step
    | .root => [.right, .left]
    | _ => []
  halted := chipHalted

/-- Drops the right-hand occurrence. -/
def deletingPair : OrderedSystem Chip where
  step
    | .root => [.left]
    | _ => []
  halted := chipHalted

/-- Adds an occurrence the source does not produce. -/
def inventingPair : OrderedSystem Chip where
  step
    | .root => [.left, .right, .extra]
    | _ => []
  halted := chipHalted

/-- The occurrence chosen first by one ordered expansion of the root. -/
def firstOnce (system : OrderedSystem Chip) : Option Chip :=
  (system.expandFirst [Chip.root]).head?

/-- The two enumerations of the root are the same bag. -/
theorem reordered_step_bags :
    orderedPair.step Chip.root = [Chip.left, Chip.right] ∧
    reorderedPair.step Chip.root = [Chip.right, Chip.left] ∧
    (Multiset.ofList (orderedPair.step Chip.root)) = Multiset.ofList (reorderedPair.step Chip.root) := by
  refine ⟨rfl, rfl, ?_⟩
  exact Quotient.sound (List.Perm.swap Chip.right Chip.left [])

/-- Different local enumerations are an occurrence simulation. The successor
premise is `reordered_step_bags`, read off the two `step` lists. -/
theorem reordered_occurrence : OccurrenceSimulation orderedPair reorderedPair (· = ·) where
  halted := by
    rintro _ _ rfl
    rfl
  step := by
    rintro state _ rfl
    cases state with
    | root => exact Multiset.rel_eq.mpr reordered_step_bags.2.2
    | left =>
        rw [show orderedPair.step Chip.left = [] from rfl, show reorderedPair.step Chip.left = [] from rfl]
        exact .zero
    | right =>
        rw [show orderedPair.step Chip.right = [] from rfl,
          show reorderedPair.step Chip.right = [] from rfl]
        exact .zero
    | extra =>
        rw [show orderedPair.step Chip.extra = [] from rfl,
          show reorderedPair.step Chip.extra = [] from rfl]
        exact .zero

/-- Every synchronous round of the reordered machines keeps the frontier bag. -/
theorem reordered_frontiers (fuel : ℕ) :
    Multiset.Rel Eq (Multiset.ofList (orderedPair.runFrontier fuel [Chip.root]))
      (Multiset.ofList (reorderedPair.runFrontier fuel [Chip.root])) :=
  reordered_occurrence.runFrontier fuel (.cons rfl .zero)

/-- The whole local observation of a chip: which occurrence it is, and whether
that occurrence has halted. -/
structure ChipRead where
  chip : Chip
  halted : Bool
  deriving DecidableEq, Repr

def chipRead (system : OrderedSystem Chip) (state : Chip) : ChipRead where
  chip := state
  halted := system.halted state

/-- Full observations of the reordered frontiers agree as bags at every fuel. -/
theorem reordered_full_observations (fuel : ℕ) :
    Multiset.Rel Eq
      (Multiset.ofList ((orderedPair.runFrontier fuel [Chip.root]).map (chipRead orderedPair)))
      (Multiset.ofList ((reorderedPair.runFrontier fuel [Chip.root]).map (chipRead reorderedPair))) := by
  refine reordered_occurrence.observe ?reads fuel (.cons rfl .zero)
  intro state _state' relatedStates
  cases relatedStates
  cases state <;> rfl

/-- Permuting successors preserves the one-round occurrence bag and changes the
first occurrence chosen by the ordered expansion. -/
theorem permuted_successors_change_first :
    orderedPair.expandFirst [Chip.root] = [Chip.left, Chip.right] ∧
    reorderedPair.expandFirst [Chip.root] = [Chip.right, Chip.left] ∧
    firstOnce orderedPair = some Chip.left ∧
    firstOnce reorderedPair = some Chip.right ∧
    (orderedPair.runFrontier 1 [Chip.root] : Multiset Chip) =
      (reorderedPair.runFrontier 1 [Chip.root] : Multiset Chip) ∧
    orderedPair.runFrontier 0 [Chip.root] = [Chip.root] ∧
    orderedPair.halted Chip.root = false ∧
    ¬ OrderedSimulation orderedPair reorderedPair (· = ·) := by
  have sourceExpanded : orderedPair.expandFirst [Chip.root] = [Chip.left, Chip.right] := by
    rw [OrderedSystem.expandFirst, show orderedPair.halted Chip.root = false from rfl,
      OrderedSystem.advance, show orderedPair.step Chip.root = [Chip.left, Chip.right] from rfl]
    rfl
  have targetExpanded : reorderedPair.expandFirst [Chip.root] = [Chip.right, Chip.left] := by
    rw [OrderedSystem.expandFirst, show reorderedPair.halted Chip.root = false from rfl,
      OrderedSystem.advance, show reorderedPair.step Chip.root = [Chip.right, Chip.left] from rfl]
    rfl
  have sourceFrontier : orderedPair.runFrontier 1 [Chip.root] = [Chip.left, Chip.right] := by
    rw [OrderedSystem.runFrontier, show ([Chip.root].all orderedPair.halted) = false from rfl,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, OrderedSystem.advance,
      show orderedPair.step Chip.root = [Chip.left, Chip.right] from rfl]
    rfl
  have targetFrontier : reorderedPair.runFrontier 1 [Chip.root] = [Chip.right, Chip.left] := by
    rw [OrderedSystem.runFrontier, show ([Chip.root].all reorderedPair.halted) = false from rfl,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, OrderedSystem.advance,
      show reorderedPair.step Chip.root = [Chip.right, Chip.left] from rfl]
    rfl
  refine ⟨sourceExpanded, targetExpanded, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · rw [firstOnce, sourceExpanded]; rfl
  · rw [firstOnce, targetExpanded]; rfl
  · rw [sourceFrontier, targetFrontier]
    exact Quotient.sound (List.Perm.swap Chip.right Chip.left [])
  · intro simulation
    have relatedLists := simulation.step (rfl : Chip.root = Chip.root)
    rw [show orderedPair.step Chip.root = [Chip.left, Chip.right] from rfl,
      show reorderedPair.step Chip.root = [Chip.right, Chip.left] from rfl] at relatedLists
    cases relatedLists with
    | cons head _ => cases head

inductive Node where
  | start
  | copy (index : Fin 2)
  deriving DecidableEq, Repr

def payload : Node → Bool
  | .start => false
  | .copy _ => true

def nodeHalted : Node → Bool
  | .start => false
  | .copy _ => true

/-- One step produces two occurrences with equal payload and distinct indices. -/
def twoCopies : OrderedSystem Node where
  step
    | .start => [.copy 0, .copy 1]
    | .copy _ => []
  halted := nodeHalted

/-- Keeps one of those two equal-payload occurrences. -/
def oneCopy : OrderedSystem Node where
  step
    | .start => [.copy 0]
    | .copy _ => []
  halted := nodeHalted

/-- The full reading of a node: its index, when it is a produced copy, and its
payload. Equal payloads stay attached to distinct indices. -/
structure NodeRead where
  index : Option (Fin 2)
  payload : Bool
  deriving DecidableEq, Repr

def nodeRead : Node → NodeRead
  | .start => { index := none, payload := false }
  | .copy index => { index := some index, payload := true }

/-- Duplicate equal payloads remain two occurrences, and the identity simulation
keeps both through one synchronous round. -/
theorem duplicate_payloads_remain_distinct :
    twoCopies.step Node.start = [Node.copy 0, Node.copy 1] ∧
    payload (Node.copy 0) = true ∧
    payload (Node.copy 1) = true ∧
    Node.copy 0 ≠ Node.copy 1 ∧
    (twoCopies.step Node.start : Multiset Node).card = 2 ∧
    twoCopies.runFrontier 1 [Node.start] = [Node.copy 0, Node.copy 1] ∧
    (twoCopies.runFrontier 1 [Node.start]).map nodeRead =
      [nodeRead (Node.copy 0), nodeRead (Node.copy 1)] ∧
    (nodeRead (Node.copy 0)).payload = (nodeRead (Node.copy 1)).payload ∧
    (nodeRead (Node.copy 0)).index ≠ (nodeRead (Node.copy 1)).index ∧
    OccurrenceSimulation twoCopies twoCopies (· = ·) := by
  have frontier : twoCopies.runFrontier 1 [Node.start] = [Node.copy 0, Node.copy 1] := by
    rw [OrderedSystem.runFrontier, show ([Node.start].all twoCopies.halted) = false from rfl,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, OrderedSystem.advance,
      show twoCopies.step Node.start = [Node.copy 0, Node.copy 1] from rfl]
    rfl
  refine ⟨rfl, rfl, rfl, ?_, ?_, frontier, ?_, rfl, ?_, OccurrenceSimulation.refl twoCopies⟩
  · decide
  · rw [show twoCopies.step Node.start = [Node.copy 0, Node.copy 1] from rfl]
    rfl
  · rw [frontier]; rfl
  · decide

inductive Stuck where
  | here
  deriving DecidableEq, Repr

/-- A running occurrence whose successor list is empty. -/
def stuckSystem : OrderedSystem Stuck where
  step _ := []
  halted _ := false

/-- A running occurrence with no successor stays on its own frontier at every fuel. -/
theorem stuck_retained :
    stuckSystem.halted Stuck.here = false ∧
    stuckSystem.step Stuck.here = [] ∧
    stuckSystem.advance Stuck.here = [Stuck.here] ∧
    (∀ fuel, stuckSystem.runFrontier fuel [Stuck.here] = [Stuck.here]) ∧
    OccurrenceSimulation stuckSystem stuckSystem (· = ·) := by
  refine ⟨rfl, rfl, rfl, ?_, OccurrenceSimulation.refl stuckSystem⟩
  intro fuel
  induction fuel with
  | zero => rfl
  | succ _ ih =>
      rw [OrderedSystem.runFrontier, show ([Stuck.here].all stuckSystem.halted) = false from rfl,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, OrderedSystem.advance,
        show stuckSystem.step Stuck.here = [] from rfl]
      exact ih

/-- Dropping one successor occurrence is not an occurrence simulation. -/
theorem deletion_not_occurrence :
    deletingPair.step Chip.root = [Chip.left] ∧
    orderedPair.step Chip.root = [Chip.left, Chip.right] ∧
    ¬ OccurrenceSimulation orderedPair deletingPair (· = ·) := by
  refine ⟨rfl, rfl, ?_⟩
  intro simulation
  have cards := Multiset.card_eq_card_of_rel (simulation.step (rfl : Chip.root = Chip.root))
  rw [show orderedPair.step Chip.root = [Chip.left, Chip.right] from rfl,
    show deletingPair.step Chip.root = [Chip.left] from rfl] at cards
  simp only [Multiset.coe_card, List.length_cons, List.length_nil] at cards
  cases cards

/-- Inventing an extra successor occurrence is not an occurrence simulation. -/
theorem invention_not_occurrence :
    inventingPair.step Chip.root = [Chip.left, Chip.right, Chip.extra] ∧
    orderedPair.step Chip.root = [Chip.left, Chip.right] ∧
    ¬ OccurrenceSimulation orderedPair inventingPair (· = ·) := by
  refine ⟨rfl, rfl, ?_⟩
  intro simulation
  have cards := Multiset.card_eq_card_of_rel (simulation.step (rfl : Chip.root = Chip.root))
  rw [show orderedPair.step Chip.root = [Chip.left, Chip.right] from rfl,
    show inventingPair.step Chip.root = [Chip.left, Chip.right, Chip.extra] from rfl] at cards
  simp only [Multiset.coe_card, List.length_cons, List.length_nil] at cards
  cases cards

/-- Collapsing two equal-payload occurrences into one is not an occurrence
simulation, including under the relation that compares only payloads. -/
theorem deduplication_not_occurrence :
    payload (Node.copy 0) = payload (Node.copy 1) ∧
    twoCopies.step Node.start = [Node.copy 0, Node.copy 1] ∧
    oneCopy.step Node.start = [Node.copy 0] ∧
    ¬ OccurrenceSimulation twoCopies oneCopy (fun left right => payload left = payload right) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro simulation
  have roots : payload Node.start = payload Node.start := rfl
  have cards := Multiset.card_eq_card_of_rel (simulation.step roots)
  rw [show twoCopies.step Node.start = [Node.copy 0, Node.copy 1] from rfl,
    show oneCopy.step Node.start = [Node.copy 0] from rfl] at cards
  simp only [Multiset.coe_card, List.length_cons, List.length_nil] at cards
  cases cards

end OccurrenceControls

end Mettapedia.GSLT.Distinction

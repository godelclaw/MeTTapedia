import Mettapedia.GSLT.Distinction.OrderedSimulation
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Native types of ordered machines

An ordered machine lists the successors of each state in order and tests
halting. Read as a rewrite system on its states, with equality as the
equations, it is a GSLT. With an observation family it is a one-label step
system, so every Hennessy--Milner formula over those observations is a native
type of the machine.

An ordered simulation relates successor lists position by position. Every
successor of one state is related to a successor of the other, in both
directions, so the simulation is a bisimulation between the two step systems.
When it also respects the observations, related states have the same native
types (`nativeType_iff_of_simulation`). Halting is always respected
(`halting_nativeType_iff`). The representation layers of a machine that are
related by ordered simulations therefore satisfy the same native types.

An occurrence simulation relates those successor lists as bags. The same
formulas transport without a positional alignment
(`sat_iff_of_occurrence_simulation`), and the ordered theorems are that result
applied to `OccurrenceSimulation.ofOrdered`. Halting observations give
`halting_nativeType_iff_of_occurrence_simulation`.

Ordinary Hennessy--Milner formulas do not see multiplicity. One successor and
two equal successors can satisfy the same formulas and the same observations
while an identity occurrence simulation fails.

The controls relate a three-state machine to a renamed copy, transport a formula
along that simulation, and show that no ordered simulation relates two states
that a formula separates. The positive occurrence control uses the imported
`OccurrenceControls` machines and `reordered_occurrence`. A one-successor
machine and a two-equal-successor machine agree on every existing formula and
are not related by an identity occurrence simulation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.OrderedSystemNativeTypes

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner Mettapedia.GSLT.Distinction
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

universe u v w

/-- An ordered machine read as a rewrite system: a step goes to any listed
successor, and the equations are equality. -/
def gslt {State : Type u} (system : OrderedSystem State) : GSLT where
  Term := State
  equations := ⟨Eq, eq_equivalence⟩
  rewrites source target := target ∈ system.step source
  rewrites_resp_left := by
    intro _ _ _ equal step
    obtain rfl : _ = _ := equal
    exact ⟨_, step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    obtain rfl : _ = _ := equal
    exact step

/-- The one-label step system of an ordered machine over an observation family. -/
def stepSystem {State : Type u} (system : OrderedSystem State) {Atom : Type w}
    (observes : Atom → State → Prop) : System (gslt system) where
  Atom := Atom
  observes := observes
  observes_resp := by
    intro _ _ _ equal
    obtain rfl : _ = _ := equal
    exact Iff.rfl
  Label := Unit
  act _ source target := target ∈ system.step source
  act_resp_left := by
    intro _ _ _ _ equal step
    obtain rfl : _ = _ := equal
    exact ⟨_, step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    obtain rfl : _ = _ := equal
    exact step

/-- Halting as the one observation. -/
def halts {State : Type u} (system : OrderedSystem State) (_ : Unit) (state : State) : Prop :=
  system.halted state = true

theorem forall₂_forth {α : Type u} {β : Type v} {related : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ related left right →
      ∀ {item : α}, item ∈ left → ∃ item' ∈ right, related item item'
  | _, _, .nil, _, member => nomatch member
  | _, _, .cons head tail, _, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, List.mem_cons_self .., head⟩
    · obtain ⟨item', inRight, relatedItems⟩ := forall₂_forth tail later
      exact ⟨item', List.mem_cons_of_mem _ inRight, relatedItems⟩

theorem forall₂_back {α : Type u} {β : Type v} {related : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ related left right →
      ∀ {item' : β}, item' ∈ right → ∃ item ∈ left, related item item'
  | _, _, .nil, _, member => nomatch member
  | _, _, .cons head tail, _, member => by
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, List.mem_cons_self .., head⟩
    · obtain ⟨item, inLeft, relatedItems⟩ := forall₂_back tail later
      exact ⟨item, List.mem_cons_of_mem _ inLeft, relatedItems⟩

variable {S : Type u} {T : Type v} {source : OrderedSystem S} {target : OrderedSystem T}
  {related : S → T → Prop}

/-- **Formulas transport along an occurrence simulation.** Successor witnesses
come from `Multiset.Rel` in both directions. The two successor lists need not
be aligned. -/
theorem sat_iff_of_occurrence_simulation
    (simulation : OccurrenceSimulation source target related)
    {Atom : Type w} {observes : Atom → S → Prop} {observes' : Atom → T → Prop}
    (agree : ∀ atom {state state'}, related state state' → (observes atom state ↔ observes' atom state')) :
    ∀ (formula : Formula Atom Unit) {state : S} {state' : T}, related state state' →
      ((stepSystem source observes).sat formula state ↔ (stepSystem target observes').sat formula state')
  | .top, _, _, _ => Iff.rfl
  | .atom atom, _, _, relatedStates => agree atom relatedStates
  | .conj left right, _, _, relatedStates =>
    and_congr (sat_iff_of_occurrence_simulation simulation agree left relatedStates)
      (sat_iff_of_occurrence_simulation simulation agree right relatedStates)
  | .neg inner, _, _, relatedStates =>
    not_congr (sat_iff_of_occurrence_simulation simulation agree inner relatedStates)
  | .dia _ inner, _, _, relatedStates => by
    have lists := simulation.step relatedStates
    constructor
    · rintro ⟨next, member, holds⟩
      obtain ⟨next', member', relatedNext⟩ :=
        Multiset.exists_mem_of_rel_of_mem lists (Multiset.mem_coe.mpr member)
      exact ⟨next', Multiset.mem_coe.mp member',
        (sat_iff_of_occurrence_simulation simulation agree inner relatedNext).mp holds⟩
    · rintro ⟨next', member', holds⟩
      obtain ⟨next, member, relatedNext⟩ :=
        Multiset.exists_mem_of_rel_of_mem ((Multiset.rel_flip).mpr lists)
          (Multiset.mem_coe.mpr member')
      exact ⟨next, Multiset.mem_coe.mp member,
        (sat_iff_of_occurrence_simulation simulation agree inner relatedNext).mpr holds⟩

/-- **Native types transport along an occurrence simulation.** These are the
ordinary formula native types, read at related states. -/
theorem nativeType_iff_of_occurrence_simulation
    (simulation : OccurrenceSimulation source target related)
    {Atom : Type w} {observes : Atom → S → Prop} {observes' : Atom → T → Prop}
    (agree : ∀ atom {state state'}, related state state' → (observes atom state ↔ observes' atom state'))
    (formula : Formula Atom Unit) {state : S} {state' : T} (relatedStates : related state state') :
    (gsltOSLF (gslt source)).satisfies (S := ()) state
        (formulaNativeType (stepSystem source observes) formula).pred ↔
      (gsltOSLF (gslt target)).satisfies (S := ()) state'
        (formulaNativeType (stepSystem target observes') formula).pred :=
  sat_iff_of_occurrence_simulation simulation agree formula relatedStates

/-- Halting is an observation an occurrence simulation always respects, so
native types over `halts` transport along every occurrence simulation. -/
theorem halting_nativeType_iff_of_occurrence_simulation
    (simulation : OccurrenceSimulation source target related)
    (formula : Formula Unit Unit) {state : S} {state' : T} (relatedStates : related state state') :
    (gsltOSLF (gslt source)).satisfies (S := ()) state
        (formulaNativeType (stepSystem source (halts source)) formula).pred ↔
      (gsltOSLF (gslt target)).satisfies (S := ()) state'
        (formulaNativeType (stepSystem target (halts target)) formula).pred :=
  nativeType_iff_of_occurrence_simulation simulation
    (fun _ _ _ relatedStates => by
      simp only [halts]
      rw [simulation.halted relatedStates])
    formula relatedStates

/-- **Formulas transport.** An ordered simulation that respects the observations
relates states satisfying the same Hennessy--Milner formulas. This is the
occurrence transport applied to `OccurrenceSimulation.ofOrdered`. -/
theorem sat_iff_of_simulation (simulation : OrderedSimulation source target related)
    {Atom : Type w} {observes : Atom → S → Prop} {observes' : Atom → T → Prop}
    (agree : ∀ atom {state state'}, related state state' → (observes atom state ↔ observes' atom state')) :
    ∀ (formula : Formula Atom Unit) {state : S} {state' : T}, related state state' →
      ((stepSystem source observes).sat formula state ↔ (stepSystem target observes').sat formula state') :=
  sat_iff_of_occurrence_simulation (OccurrenceSimulation.ofOrdered simulation) agree

/-- **Native types transport.** -/
theorem nativeType_iff_of_simulation (simulation : OrderedSimulation source target related)
    {Atom : Type w} {observes : Atom → S → Prop} {observes' : Atom → T → Prop}
    (agree : ∀ atom {state state'}, related state state' → (observes atom state ↔ observes' atom state'))
    (formula : Formula Atom Unit) {state : S} {state' : T} (relatedStates : related state state') :
    (gsltOSLF (gslt source)).satisfies (S := ()) state
        (formulaNativeType (stepSystem source observes) formula).pred ↔
      (gsltOSLF (gslt target)).satisfies (S := ()) state'
        (formulaNativeType (stepSystem target observes') formula).pred :=
  nativeType_iff_of_occurrence_simulation (OccurrenceSimulation.ofOrdered simulation)
    agree formula relatedStates

/-- Every ordered simulation respects halting, so native types over halting
transport along every ordered simulation. -/
theorem halting_nativeType_iff (simulation : OrderedSimulation source target related)
    (formula : Formula Unit Unit) {state : S} {state' : T} (relatedStates : related state state') :
    (gsltOSLF (gslt source)).satisfies (S := ()) state
        (formulaNativeType (stepSystem source (halts source)) formula).pred ↔
      (gsltOSLF (gslt target)).satisfies (S := ()) state'
        (formulaNativeType (stepSystem target (halts target)) formula).pred :=
  halting_nativeType_iff_of_occurrence_simulation (OccurrenceSimulation.ofOrdered simulation)
    formula relatedStates

/-! ## Controls -/

namespace Controls

/-- `0` branches to `1` and `2`; `1` halts; `2` loops. -/
def machine : OrderedSystem (Fin 3) where
  step state := if state = 0 then [1, 2] else if state = 2 then [2] else []
  halted state := state == 1

/-- The same machine with its states renamed by `k ↦ 2 - k`. -/
def renamed : OrderedSystem (Fin 3) where
  step state := if state = 2 then [1, 0] else if state = 0 then [0] else []
  halted state := state == 1

def rename (state : Fin 3) : Fin 3 := 2 - state

theorem renamed_simulation :
    OrderedSimulation machine renamed (fun state state' => state' = rename state) :=
  OrderedSimulation.ofMap rename (by decide) (by decide)

/-- "Some successor halts." -/
def canHalt : Formula Unit Unit := .dia () (.atom ())

theorem machine_canHalt : (stepSystem machine (halts machine)).sat canHalt (0 : Fin 3) := by
  show ∃ next, next ∈ machine.step 0 ∧ machine.halted next = true
  exact ⟨1, by decide, by decide⟩

/-- Positive control: the renamed start state satisfies the formula, by transport
rather than by computation. -/
theorem renamed_canHalt : (stepSystem renamed (halts renamed)).sat canHalt (2 : Fin 3) :=
  (halting_nativeType_iff renamed_simulation canHalt (state := 0) (state' := 2) (by decide)).mp
    machine_canHalt

theorem renamed_loop_cannot_halt : ¬ (stepSystem renamed (halts renamed)).sat canHalt (0 : Fin 3) := by
  show ¬ ∃ next, next ∈ renamed.step 0 ∧ renamed.halted next = true
  decide

/-- Negative control: no ordered simulation relates the start state to the renamed
machine's looping state, because a formula separates them. -/
theorem no_simulation_to_loop :
    ¬ ∃ relation : Fin 3 → Fin 3 → Prop, OrderedSimulation machine renamed relation ∧ relation 0 0 := by
  rintro ⟨relation, simulation, relatedStates⟩
  exact renamed_loop_cannot_halt
    ((halting_nativeType_iff simulation canHalt relatedStates).mp machine_canHalt)

/-- Positive control: the imported reordered root satisfies "some successor
halts" by transport along `OccurrenceControls.reordered_occurrence`. The source
fact is `Chip.left` on `orderedPair.step`. -/
theorem reordered_transports_canHalt :
    (stepSystem OccurrenceControls.orderedPair (halts OccurrenceControls.orderedPair)).sat
        canHalt OccurrenceControls.Chip.root ∧
      (stepSystem OccurrenceControls.reorderedPair (halts OccurrenceControls.reorderedPair)).sat
        canHalt OccurrenceControls.Chip.root := by
  have sourceHolds :
      (stepSystem OccurrenceControls.orderedPair (halts OccurrenceControls.orderedPair)).sat
        canHalt OccurrenceControls.Chip.root := by
    show ∃ next, next ∈ OccurrenceControls.orderedPair.step OccurrenceControls.Chip.root ∧
      OccurrenceControls.orderedPair.halted next = true
    refine ⟨OccurrenceControls.Chip.left, ?_, rfl⟩
    rw [show OccurrenceControls.orderedPair.step OccurrenceControls.Chip.root =
      [OccurrenceControls.Chip.left, OccurrenceControls.Chip.right] from rfl]
    exact List.mem_cons_self ..
  refine ⟨sourceHolds, ?_⟩
  exact (sat_iff_of_occurrence_simulation OccurrenceControls.reordered_occurrence
      (fun _ state _ related => by
        cases related
        cases state <;> rfl)
      canHalt rfl).mp sourceHolds

/-- One successor, or two occurrences of that same successor. Both copies halt. -/
inductive Node where
  | start | copy
  deriving DecidableEq, Repr

def oneSuccessor : OrderedSystem Node where
  step
    | .start => [.copy]
    | .copy => []
  halted
    | .start => false
    | .copy => true

def twoEqualSuccessors : OrderedSystem Node where
  step
    | .start => [.copy, .copy]
    | .copy => []
  halted
    | .start => false
    | .copy => true

/-- Negative control: one successor and two equal successors agree on halting
and on every existing Hennessy--Milner formula, and an identity occurrence
simulation fails because those `step` bags have different cardinality. -/
theorem multiplicity_invisible_to_formulas :
    oneSuccessor.step Node.start = [Node.copy] ∧
    twoEqualSuccessors.step Node.start = [Node.copy, Node.copy] ∧
    (∀ state, oneSuccessor.halted state = twoEqualSuccessors.halted state) ∧
    (∀ formula : Formula Unit Unit, ∀ state,
      (stepSystem oneSuccessor (halts oneSuccessor)).sat formula state ↔
        (stepSystem twoEqualSuccessors (halts twoEqualSuccessors)).sat formula state) ∧
    ¬ OccurrenceSimulation oneSuccessor twoEqualSuccessors (· = ·) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro state
    cases state <;> rfl
  · intro formula state
    induction formula generalizing state with
    | top => rfl
    | atom _ => cases state <;> rfl
    | conj _ _ left right => exact and_congr (left state) (right state)
    | neg _ inner => exact not_congr (inner state)
    | dia _ inner ih =>
        cases state with
        | copy =>
            constructor
            · rintro ⟨next, member, _⟩
              have member' : next ∈ oneSuccessor.step Node.copy := member
              rw [show oneSuccessor.step Node.copy = [] from rfl] at member'
              cases member'
            · rintro ⟨next, member, _⟩
              have member' : next ∈ twoEqualSuccessors.step Node.copy := member
              rw [show twoEqualSuccessors.step Node.copy = [] from rfl] at member'
              cases member'
        | start =>
            constructor
            · rintro ⟨next, member, holds⟩
              have member' : next ∈ oneSuccessor.step Node.start := member
              rw [show oneSuccessor.step Node.start = [Node.copy] from rfl] at member'
              rcases List.mem_cons.mp member' with rfl | later
              · exact ⟨Node.copy, List.mem_cons.mpr (Or.inl rfl), (ih Node.copy).mp holds⟩
              · cases later
            · rintro ⟨next, member, holds⟩
              have member' : next ∈ twoEqualSuccessors.step Node.start := member
              rw [show twoEqualSuccessors.step Node.start = [Node.copy, Node.copy] from rfl] at member'
              rcases List.mem_cons.mp member' with rfl | later
              · exact ⟨Node.copy, List.mem_cons.mpr (Or.inl rfl), (ih Node.copy).mpr holds⟩
              · rcases List.mem_cons.mp later with rfl | empty
                · exact ⟨Node.copy, List.mem_cons.mpr (Or.inl rfl), (ih Node.copy).mpr holds⟩
                · cases empty
  · intro simulation
    have cards := Multiset.card_eq_card_of_rel (simulation.step (rfl : Node.start = Node.start))
    rw [show oneSuccessor.step Node.start = [Node.copy] from rfl,
      show twoEqualSuccessors.step Node.start = [Node.copy, Node.copy] from rfl] at cards
    simp only [Multiset.coe_card, List.length_cons, List.length_nil] at cards
    cases cards

end Controls

end Mettapedia.OSLF.Framework.OrderedSystemNativeTypes

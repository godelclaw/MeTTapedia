import Mettapedia.GSLT.Distinction.OrderedSimulation
import Mettapedia.GSLT.Distinction.OrderedSimulationSpans
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Ordered simulations up to ranked administration

`OrderedSimulation` relates two ordered nondeterministic machines in lockstep:
one source step, one target step, successor lists related position by
position.  An implementation rarely runs in lockstep.  It spends administrative
steps (matching candidates, loading frames, unpacking cells) between the steps
the specification describes, may realize one branching source step as a tree of
smaller branchings, and may try alternatives that fail without ever standing
for a source occurrence.  `OrderedSimulationSpans` records why lockstep frontiers
cannot absorb such stuttering, and why boundary clocks have to be supplied.

This module constructs finite administrative boundary paths from a rank.
It does not construct a primitive scheduler or a total-work bound.

* **Settling** (`OrderedSystem.settle`).  An administrative state is replaced by
  the settled forms of its successors, in order; a stable state is kept; an
  administrative state without successors disappears.  Settling is the target's
  own execution, read at stable states.
* **Ranked administration** (`OrderedSystem.AdministrationRanked`).  Every
  administrative step decreases a rank.  Then settling with fuel past the rank
  reaches only stable states (`settle_stable`), every settled state is reached
  by at most `rank` administrative steps (`settle_reach`,
  `AdministrativeReach.count_le_rank`), and an administrative loop admits no
  rank.  Administration therefore cannot diverge, while genuine source
  divergence remains possible.
* **Block simulations** (`BlockSimulation`).  A target state stands for an
  ordered block of source occurrences.  A stable target state stands for exactly
  one occurrence and agrees with it on halting; its successors split that
  occurrence's successor list into consecutive blocks.  An administrative state
  splits its own block among its successors. An empty block may represent a
  rejected candidate only under an additional observation and erasure licence.
* **Lockstep is the special case** (`OrderedSimulation.toBlockSimulation`,
  `OrderedSystem.saturate_all_stable`): with no administrative states, every
  ordered simulation is a block simulation, and saturation changes nothing.
* **Saturation** (`BlockSimulation.saturated`).  Under ranked administration, a
  block simulation is an `OrderedSimulation` from the source to the saturated
  target (`OrderedSystem.saturate`: one primitive step, then settling).  Every
  existing theorem about ordered simulations then applies to this saturated
  target: complete frontiers at every macro-step fuel, answers in order,
  the converse direction, successor counts, depth-first prefixes.

The primitive target and its saturation are different machines. Native boundary
decoding, scheduling and total-work accounting require separate laws. The block
contract compares halting flags; value, fault, waiting and effect observations
need their own agreement. In particular, assigning an unstable terminal an empty
block can erase it: the controls construct such a halted fault. A runtime
instance must keep observable terminals stable or justify each erased state as
an unobservable rejected candidate, and preserve committed histories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

universe u v w x

namespace OrderedSystem

variable {State : Type u} (system : OrderedSystem State)

/-- Settle at most `fuel` administrative layers: a stable state is kept, an
administrative state is replaced by the settled forms of its successors, in
order. An administrative state without successors disappears. Calling it a
failed, unobservable alternative requires an additional observation contract;
this definition does not inspect its halting flag or effects. -/
def settle (stable : State → Bool) : ℕ → State → List State
  | 0, state => [state]
  | fuel + 1, state =>
      if stable state then [state] else (system.step state).flatMap (settle stable fuel)

/-- Administration is ranked when every administrative step decreases the rank. -/
def AdministrationRanked (stable : State → Bool) (rank : State → ℕ) : Prop :=
  ∀ state, stable state = false → ∀ next ∈ system.step state, rank next < rank state

/-- The target read at stable states: one primitive step, then each successor is
settled with fuel past its rank. -/
def saturate (stable : State → Bool) (rank : State → ℕ) : OrderedSystem State where
  step state := (system.step state).flatMap fun next => system.settle stable (rank next + 1) next
  halted := system.halted

/-- A chain of administrative steps of the given length. -/
inductive AdministrativeReach (stable : State → Bool) : ℕ → State → State → Prop where
  | here {state : State} : AdministrativeReach stable 0 state state
  | step {count : ℕ} {state middle last : State} :
      stable state = false → middle ∈ system.step state →
        AdministrativeReach stable count middle last →
          AdministrativeReach stable (count + 1) state last

variable {system}

@[simp] theorem settle_zero (stable : State → Bool) (state : State) :
    system.settle stable 0 state = [state] := rfl

theorem settle_of_stable {stable : State → Bool} (fuel : ℕ) {state : State}
    (isStable : stable state = true) : system.settle stable fuel state = [state] := by
  cases fuel <;> simp [settle, isStable]

theorem settle_succ_of_administrative {stable : State → Bool} (fuel : ℕ) {state : State}
    (administrative : stable state = false) :
    system.settle stable (fuel + 1) state =
      (system.step state).flatMap (system.settle stable fuel) := by
  simp [settle, administrative]

/-- Every settled state is reached by administrative steps, no more than the fuel. -/
theorem settle_reach {stable : State → Bool} (fuel : ℕ) {state last : State}
    (member : last ∈ system.settle stable fuel state) :
    ∃ count ≤ fuel, system.AdministrativeReach stable count state last := by
  induction fuel generalizing state with
  | zero =>
      simp only [settle_zero, List.mem_singleton] at member
      subst member
      exact ⟨0, le_rfl, .here⟩
  | succ fuel ih =>
      cases isStable : stable state
      · rw [settle_succ_of_administrative fuel isStable, List.mem_flatMap] at member
        obtain ⟨middle, middleStep, settled⟩ := member
        obtain ⟨count, bound, reach⟩ := ih settled
        exact ⟨count + 1, Nat.succ_le_succ bound, .step isStable middleStep reach⟩
      · rw [settle_of_stable (fuel + 1) isStable, List.mem_singleton] at member
        subst member
        exact ⟨0, Nat.zero_le _, .here⟩

/-- Under ranked administration, an administrative chain is no longer than the
rank of its start. -/
theorem AdministrativeReach.count_le_rank {stable : State → Bool} {rank : State → ℕ}
    (ranked : system.AdministrationRanked stable rank) {count : ℕ} {state last : State}
    (reach : system.AdministrativeReach stable count state last) :
    count + rank last ≤ rank state := by
  induction reach with
  | here => simp
  | step administrative member _ ih =>
      have decrease := ranked _ administrative _ member
      omega

/-- Settling with fuel past the rank reaches only stable states. -/
theorem settle_stable {stable : State → Bool} {rank : State → ℕ}
    (ranked : system.AdministrationRanked stable rank) (fuel : ℕ) {state last : State}
    (bound : rank state < fuel) (member : last ∈ system.settle stable fuel state) :
    stable last = true := by
  induction fuel generalizing state with
  | zero => exact absurd bound (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases isStable : stable state
      · rw [settle_succ_of_administrative fuel isStable, List.mem_flatMap] at member
        obtain ⟨middle, middleStep, settled⟩ := member
        have decrease := ranked state isStable middle middleStep
        exact ih (by omega) settled
      · rw [settle_of_stable (fuel + 1) isStable, List.mem_singleton] at member
        subst member
        exact isStable

/-- An administrative loop admits no rank. -/
theorem not_ranked_of_loop {stable : State → Bool} {state : State}
    (administrative : stable state = false) (loop : state ∈ system.step state)
    (rank : State → ℕ) : ¬ system.AdministrationRanked stable rank :=
  fun ranked => Nat.lt_irrefl _ (ranked state administrative state loop)

end OrderedSystem

/-- Every element of the right list is related to some element of the left one. -/
theorem forall₂_right_mem {A : Type u} {B : Type v} {related : A → B → Prop} {left : List A}
    {right : List B} (lists : List.Forall₂ related left right) {target : B}
    (member : target ∈ right) : ∃ source ∈ left, related source target := by
  induction lists with
  | nil => cases member
  | cons head _ ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨source, sourceMember, pair⟩ := ih member
        exact ⟨source, List.mem_cons_of_mem _ sourceMember, pair⟩

/-- Relate a flattened list of blocks to the targets' expansions, block by block. -/
theorem forall₂_flatten_of_blocks {A : Type u} {B : Type v} {block : List A → B → Prop}
    {related : A → B → Prop} {expand : B → List B} {blocks : List (List A)} {targets : List B}
    (lists : List.Forall₂ block blocks targets)
    (each : ∀ {occurrences target}, target ∈ targets → block occurrences target →
      List.Forall₂ related occurrences (expand target)) :
    List.Forall₂ related blocks.flatten (targets.flatMap expand) := by
  induction lists with
  | nil => exact .nil
  | @cons occurrences target restBlocks restTargets head _ ih =>
      rw [List.flatten_cons, List.flatMap_cons]
      exact List.rel_append (each (List.mem_cons_self ..) head)
        (ih fun member related => each (List.mem_cons_of_mem _ member) related)

/-- **An ordered simulation up to administration.** `block occurrences target`
says that the target state stands for the ordered block `occurrences` of source
states. A stable state stands for exactly one occurrence, agrees with it on
halting, and splits its successors into consecutive blocks; an administrative
state splits its own block among its successors. -/
structure BlockSimulation {S : Type u} {T : Type v} (source : OrderedSystem S)
    (target : OrderedSystem T) (stable : T → Bool) (block : List S → T → Prop) : Prop where
  stable_single : ∀ {occurrences : List S} {target' : T}, block occurrences target' →
    stable target' = true → ∃ state, occurrences = [state] ∧ target.halted target' = source.halted state
  stable_step : ∀ {state : S} {target' : T}, block [state] target' → stable target' = true →
    ∃ blocks : List (List S), List.Forall₂ block blocks (target.step target') ∧
      blocks.flatten = source.step state
  administrative_split : ∀ {occurrences : List S} {target' : T}, block occurrences target' →
    stable target' = false →
      ∃ blocks : List (List S), List.Forall₂ block blocks (target.step target') ∧
        blocks.flatten = occurrences

namespace BlockSimulation

variable {S : Type u} {T : Type v} {source : OrderedSystem S} {target : OrderedSystem T}
  {stable : T → Bool} {block : List S → T → Prop} {rank : T → ℕ}

/-- The relation read at stable states: a stable target state standing for one
source occurrence. -/
abbrev StableRelated (stable : T → Bool) (block : List S → T → Prop) (state : S) (target' : T) : Prop :=
  block [state] target' ∧ stable target' = true

/-- Settling a target state past its rank yields exactly its block, one stable
representative per occurrence, in order. -/
theorem block_settle (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) (fuel : ℕ) {occurrences : List S}
    {target' : T} (bound : rank target' < fuel) (blocked : block occurrences target') :
    List.Forall₂ (StableRelated stable block) occurrences (target.settle stable fuel target') := by
  induction fuel generalizing occurrences target' with
  | zero => exact absurd bound (Nat.not_lt_zero _)
  | succ fuel ih =>
      cases isStable : stable target'
      · rw [OrderedSystem.settle_succ_of_administrative fuel isStable]
        obtain ⟨blocks, lists, flattened⟩ := simulation.administrative_split blocked isStable
        rw [← flattened]
        exact forall₂_flatten_of_blocks lists fun member next => by
          have decrease := ranked target' isStable _ member
          exact ih (by omega) next
      · rw [OrderedSystem.settle_of_stable (fuel + 1) isStable]
        obtain ⟨state, single, _⟩ := simulation.stable_single blocked isStable
        subst single
        exact .cons ⟨blocked, isStable⟩ .nil

/-- Loading one source occurrence computes exactly one stable boundary,
including its block relation. An empty or duplicated loading is ruled out. -/
theorem loaded_boundary (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) {state : S} {initial : T}
    (loaded : block [state] initial) :
    ∃ boundary, target.settle stable (rank initial + 1) initial = [boundary] ∧
      StableRelated stable block state boundary := by
  have lists := simulation.block_settle ranked _ (Nat.lt_succ_self _) loaded
  generalize target.settle stable (rank initial + 1) initial = boundaries at lists
  cases lists with
  | cons pair tail =>
    cases tail
    exact ⟨_, rfl, pair⟩

/-- **A block simulation under ranked administration is an ordered simulation
of the saturated target.** -/
theorem saturated (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) :
    OrderedSimulation source (target.saturate stable rank) (StableRelated stable block) where
  halted := by
    rintro state target' ⟨blocked, isStable⟩
    obtain ⟨state', single, halts⟩ := simulation.stable_single blocked isStable
    obtain rfl : state = state' := List.singleton_inj.mp single
    exact halts
  step := by
    rintro state target' ⟨blocked, isStable⟩
    obtain ⟨blocks, lists, flattened⟩ := simulation.stable_step blocked isStable
    show List.Forall₂ _ (source.step state)
      ((target.step target').flatMap fun next => target.settle stable (rank next + 1) next)
    rw [← flattened]
    exact forall₂_flatten_of_blocks lists fun _ next =>
      simulation.block_settle ranked _ (Nat.lt_succ_self _) next

/-- **Complete frontiers are related at every fuel.** A source state is related
to the settled form of a target state standing for it, which may itself start
with administration (loading); from there the source frontier and the saturated
target frontier agree position by position, pending occurrences included. -/
theorem frontiers (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) (fuel : ℕ) {state : S} {initial : T}
    (loaded : block [state] initial) :
    List.Forall₂ (StableRelated stable block) (source.runFrontier fuel [state])
      ((target.saturate stable rank).runFrontier fuel
        (target.settle stable (rank initial + 1) initial)) :=
  (simulation.saturated ranked).runFrontier fuel
    (simulation.block_settle ranked _ (Nat.lt_succ_self _) loaded)

/-- The same frontiers related from the implementation back to the
specification: every saturated target occurrence stands for a source one. -/
theorem frontiers_back (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) (fuel : ℕ) {state : S} {initial : T}
    (loaded : block [state] initial) :
    List.Forall₂ (fun target' state' => StableRelated stable block state' target')
      ((target.saturate stable rank).runFrontier fuel
        (target.settle stable (rank initial + 1) initial))
      (source.runFrontier fuel [state]) :=
  (simulation.saturated ranked).symm.runFrontier fuel
    (OrderedSimulation.forall₂_swap (simulation.block_settle ranked _ (Nat.lt_succ_self _) loaded))

/-- The saturated target keeps the number of successor occurrences: equal-looking
alternatives are not merged. -/
theorem successor_card_eq (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) {state : S} {target' : T}
    (related : StableRelated stable block state target') :
    (source.step state).length = ((target.saturate stable rank).step target').length :=
  ((simulation.saturated ranked).step related).length_eq

/-- Every occurrence of a saturated frontier from a loaded state is stable. -/
theorem frontier_stable (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank) (fuel : ℕ) {state : S} {initial : T}
    (loaded : block [state] initial) {target' : T}
    (member : target' ∈ (target.saturate stable rank).runFrontier fuel
      (target.settle stable (rank initial + 1) initial)) :
    stable target' = true := by
  obtain ⟨_, _, pair⟩ := forall₂_right_mem (simulation.frontiers ranked fuel loaded) member
  exact pair.2

end BlockSimulation

/-! ## Sequential joins at explicit stable boundaries -/

/-- A concrete decoder between a saturated boundary and the next source
machine. The equations apply only at stable states; no primitive scheduling or
composite rank is part of this interface. -/
structure StableBoundaryAdapter {T : Type v} {M : Type w}
    (target : OrderedSystem T) (stable : T → Bool) (rank : T → ℕ)
    (middle : OrderedSystem M) where
  decode : T → M
  steps : ∀ state, stable state = true →
    middle.step (decode state) = ((target.saturate stable rank).step state).map decode
  halts : ∀ state, stable state = true → middle.halted (decode state) = target.halted state

namespace StableBoundaryAdapter

variable {T : Type v} {M : Type w} {target : OrderedSystem T}
  {stable : T → Bool} {rank : T → ℕ} {middle : OrderedSystem M}

/-- The actual decoder equations construct the boundary simulation. -/
theorem simulation (adapter : StableBoundaryAdapter target stable rank middle)
    (ranked : target.AdministrationRanked stable rank) :
    OrderedSimulation (target.saturate stable rank) middle
      (fun state decoded => stable state = true ∧ decoded = adapter.decode state) where
  halted := by
    rintro state _ ⟨isStable, rfl⟩
    exact adapter.halts state isStable
  step := by
    rintro state _ ⟨isStable, rfl⟩
    rw [adapter.steps state isStable, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro next member
    obtain ⟨initial, _, settled⟩ := List.mem_flatMap.mp member
    exact ⟨OrderedSystem.settle_stable ranked _ (Nat.lt_succ_self _) settled, rfl⟩

end StableBoundaryAdapter

namespace OrderedSystem

/-- Primitive composition requires every primitive successor at a stable
boundary to remain stable. Ranked administration alone does not imply this. -/
def PrimitiveStepClosed {T : Type v} (target : OrderedSystem T) (stable : T → Bool) : Prop :=
  ∀ state, stable state = true → ∀ next ∈ target.step state, stable next = true

/-- With primitive boundary closure the identity decoder is constructed:
saturation performs no hidden middle steps at those boundaries. -/
def primitiveBoundaryAdapter {T : Type v} (target : OrderedSystem T)
    (stable : T → Bool) (rank : T → ℕ) (closed : target.PrimitiveStepClosed stable) :
    StableBoundaryAdapter target stable rank target where
  decode := id
  steps := by
    intro state isStable
    change target.step state =
      ((target.step state).flatMap fun next => target.settle stable (rank next + 1) next).map id
    rw [List.map_id]
    have each : (target.step state).flatMap (fun next => target.settle stable (rank next + 1) next) =
        (target.step state).flatMap (fun next => [next]) :=
      List.flatMap_congr fun next member => settle_of_stable _ (closed state isStable next member)
    rw [each, List.flatMap_singleton']
  halts := fun _ _ => rfl

end OrderedSystem

namespace BlockSimulation

/-- Composition when the second source is literally the first saturated
machine. This proves a saturated join, not a primitive-runtime join. -/
theorem comp_saturated {S : Type u} {T : Type v} {U : Type w}
    {source : OrderedSystem S} {middle : OrderedSystem T} {target : OrderedSystem U}
    {stableM : T → Bool} {rankM : T → ℕ} {blockM : List S → T → Prop}
    {stableT : U → Bool} {rankT : U → ℕ} {blockT : List T → U → Prop}
    (first : BlockSimulation source middle stableM blockM)
    (rankedM : middle.AdministrationRanked stableM rankM)
    (second : BlockSimulation (middle.saturate stableM rankM) target stableT blockT)
    (rankedT : target.AdministrationRanked stableT rankT) :
    OrderedSimulation source (target.saturate stableT rankT)
      (Relation.Comp (StableRelated stableM blockM) (StableRelated stableT blockT)) :=
  (first.saturated rankedM).comp (second.saturated rankedT)

/-- Join independently represented stable boundaries through an actual
decoder. Each layer retains its own administrative rank and cost obligations. -/
theorem sequential {S : Type u} {T : Type v} {M : Type w} {U : Type x}
    {source : OrderedSystem S} {middle : OrderedSystem T} {next : OrderedSystem M}
    {target : OrderedSystem U} {stableM : T → Bool} {rankM : T → ℕ}
    {blockM : List S → T → Prop} {stableT : U → Bool} {rankT : U → ℕ}
    {blockT : List M → U → Prop}
    (first : BlockSimulation source middle stableM blockM)
    (rankedM : middle.AdministrationRanked stableM rankM)
    (adapter : StableBoundaryAdapter middle stableM rankM next)
    (second : BlockSimulation next target stableT blockT)
    (rankedT : target.AdministrationRanked stableT rankT) :
    OrderedSimulation source (target.saturate stableT rankT)
      (Relation.Comp
        (Relation.Comp (StableRelated stableM blockM)
          (fun state decoded => stableM state = true ∧ decoded = adapter.decode state))
        (StableRelated stableT blockT)) :=
  ((first.saturated rankedM).comp (adapter.simulation rankedM)).comp (second.saturated rankedT)

/-- A restricted primitive middle join. `closed` rules out middle stuttering;
the final target is still read through its own saturation. No lexicographic
rank or common raw frontier clock follows from this theorem. -/
theorem comp_primitive_middle {S : Type u} {T : Type v} {U : Type w}
    {source : OrderedSystem S} {middle : OrderedSystem T} {target : OrderedSystem U}
    {stableM : T → Bool} {rankM : T → ℕ} {blockM : List S → T → Prop}
    {stableT : U → Bool} {rankT : U → ℕ} {blockT : List T → U → Prop}
    (first : BlockSimulation source middle stableM blockM)
    (rankedM : middle.AdministrationRanked stableM rankM)
    (closed : middle.PrimitiveStepClosed stableM)
    (second : BlockSimulation middle target stableT blockT)
    (rankedT : target.AdministrationRanked stableT rankT) :
    OrderedSimulation source (target.saturate stableT rankT)
      (Relation.Comp
        (Relation.Comp (StableRelated stableM blockM)
          (fun state decoded => stableM state = true ∧ decoded = state))
        (StableRelated stableT blockT)) :=
  first.sequential rankedM (middle.primitiveBoundaryAdapter stableM rankM closed) second rankedT

end BlockSimulation

/-! ## Execution-permission contexts

These constructors retain an owned context while executing its inner machine.
The caller supplies permission from its language strategy or authored contexts,
as in `DerivedContexts` and `Refocusing`. Structural syntax alone supplies no
permission. The adapter contains no frame-pop or return-to-caller transition.
-/

namespace OrderedSystem

/-- A permitted context runs the inner machine; an unpermitted context is a
held object. Its halting flag means that the held object is ready to observe,
not that its inner computation returned. -/
def inContext {C : Type w} {S : Type u} (system : OrderedSystem S)
    (permission : C → Bool) : OrderedSystem (C × S) where
  step state := if permission state.1 then (system.step state.2).map (state.1, ·) else []
  halted state := if permission state.1 then system.halted state.2 else true

def contextStable {C : Type w} {T : Type v} (permission : C → Bool)
    (stable : T → Bool) (state : C × T) : Bool :=
  if permission state.1 then stable state.2 else true

/-- Held objects and active inner readouts have distinct constructors. -/
inductive ContextReadout (C : Type w) (S : Type u) (A : Type v) where
  | held (context : C) (state : S)
  | active (context : C) (answer : A)

def contextOutcome {C : Type w} {S : Type u} {A : Type v} (permission : C → Bool)
    (outcome : S → Option A) (state : C × S) : Option (ContextReadout C S A) :=
  if permission state.1 then (outcome state.2).map (.active state.1)
  else some (.held state.1 state.2)

theorem inContext_ranked {C : Type w} {T : Type v} {target : OrderedSystem T}
    (permission : C → Bool) {stable : T → Bool} {rank : T → ℕ}
    (ranked : target.AdministrationRanked stable rank) :
    (target.inContext permission).AdministrationRanked (contextStable permission stable)
      (fun state => rank state.2) := by
  rintro ⟨context, state⟩ administrative next member
  cases permitted : permission context
  · simp [contextStable, permitted] at administrative
  · simp only [contextStable, permitted, if_true] at administrative
    simp only [inContext, permitted, if_true, List.mem_map] at member
    obtain ⟨next', member, rfl⟩ := member
    exact ranked state administrative next' member

theorem held_no_step {C : Type w} {S : Type u} (system : OrderedSystem S)
    {permission : C → Bool} {context : C} (held : permission context = false) (state : S) :
    (system.inContext permission).step (context, state) = [] ∧
      (system.inContext permission).halted (context, state) = true := by
  simp [inContext, held]

end OrderedSystem

/-- Lift an ordered simulation through the actual permission-gated machine.
Both machines retain the same context and permission. -/
theorem OrderedSimulation.inContext {C : Type w} {S : Type u} {T : Type v}
    {source : OrderedSystem S} {target : OrderedSystem T} {related : S → T → Prop}
    (simulation : OrderedSimulation source target related) (permission : C → Bool) :
    OrderedSimulation (source.inContext permission) (target.inContext permission)
      (fun left right => left.1 = right.1 ∧ related left.2 right.2) where
  halted := by
    rintro ⟨context, state⟩ ⟨context', state'⟩ ⟨rfl, pair⟩
    cases permitted : permission context <;> simp [OrderedSystem.inContext, permitted, simulation.halted pair]
  step := by
    rintro ⟨context, state⟩ ⟨context', state'⟩ ⟨rfl, pair⟩
    cases permitted : permission context
    · simp [OrderedSystem.inContext, permitted]
    · simp only [OrderedSystem.inContext, permitted, if_true,
        List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact (simulation.step pair).imp fun _ _ next => ⟨True.intro, next⟩

namespace BlockSimulation

/-- Only permitted execution contexts admit active blocks. A held object's
separate readout does not assert that evaluation under it is authorized. -/
def ContextBlock {C : Type w} {S : Type u} {T : Type v} (permission : C → Bool)
    (block : List S → T → Prop) (occurrences : List (C × S)) (state : C × T) : Prop :=
  permission state.1 = true ∧ ∃ inner, block inner state.2 ∧ occurrences = inner.map (state.1, ·)

/-- A block simulation lifts through the constructed execution-permission
adapter, retaining the complete ordered block and its context. -/
theorem inContext {C : Type w} {S : Type u} {T : Type v}
    {source : OrderedSystem S} {target : OrderedSystem T}
    {stable : T → Bool} {block : List S → T → Prop}
    (simulation : BlockSimulation source target stable block) (permission : C → Bool) :
    BlockSimulation (source.inContext permission) (target.inContext permission)
      (OrderedSystem.contextStable permission stable) (ContextBlock permission block) where
  stable_single := by
    rintro occurrences ⟨context, state⟩ ⟨permitted, inner, blocked, rfl⟩ isStable
    simp only [OrderedSystem.contextStable, permitted, if_true] at isStable
    obtain ⟨state', rfl, halts⟩ := simulation.stable_single blocked isStable
    exact ⟨(context, state'), rfl, by simp [OrderedSystem.inContext, permitted, halts]⟩
  stable_step := by
    rintro ⟨sourceContext, state'⟩ ⟨context, state⟩ ⟨permitted, inner, blocked, mapped⟩ isStable
    obtain ⟨first, rfl, pair⟩ := List.map_eq_singleton_iff.mp mapped.symm
    have contexts : context = sourceContext := congrArg Prod.fst pair
    have states : first = state' := congrArg Prod.snd pair
    subst sourceContext
    subst state'
    simp only [OrderedSystem.contextStable, permitted, if_true] at isStable
    obtain ⟨blocks, lists, flattened⟩ := simulation.stable_step blocked isStable
    refine ⟨blocks.map (List.map (context, ·)), ?_, ?_⟩
    · simp only [OrderedSystem.inContext, permitted, if_true,
        List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact lists.imp fun _ _ next => ⟨permitted, _, next, rfl⟩
    · simpa [OrderedSystem.inContext, permitted, List.map_flatten] using
        congrArg (List.map (context, ·)) flattened
  administrative_split := by
    rintro occurrences ⟨context, state⟩ ⟨permitted, inner, blocked, rfl⟩ administrative
    simp only [OrderedSystem.contextStable, permitted, if_true] at administrative
    obtain ⟨blocks, lists, flattened⟩ := simulation.administrative_split blocked administrative
    refine ⟨blocks.map (List.map (context, ·)), ?_, ?_⟩
    · simp only [OrderedSystem.inContext, permitted, if_true,
        List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact lists.imp fun _ _ next => ⟨permitted, _, next, rfl⟩
    · simpa only [List.map_flatten] using congrArg (List.map (context, ·)) flattened

end BlockSimulation

/-! ## Independent outcome, committed-readout and erasure licences -/

namespace OrderedSystem

/-- Every visible outcome remains a stable boundary. Values, faults and waits
may use independent outcome carriers; the halting Boolean supplies none of them. -/
def ObservableStable {T : Type v} {A : Type w} (stable : T → Bool)
    (outcome : T → Option A) : Prop :=
  ∀ state, outcome state ≠ none → stable state = true

/-- Administrative edges preserve the chosen committed readout, which may be
an event history, world state, authority view, or another declared observer. -/
def AdministrationPreserves {T : Type v} {A : Type w} (target : OrderedSystem T)
    (stable : T → Bool) (read : T → A) : Prop :=
  ∀ state, stable state = false → ∀ next ∈ target.step state, read next = read state

/-- No administrative edge publishes a committed event. This is separate
from preserving a ledger: a ledger equality alone need not report publication. -/
def AdministrationSilent {T : Type v} {E : Type w} (target : OrderedSystem T)
    (stable : T → Bool) (emitted : T → T → List E) : Prop :=
  ∀ state, stable state = false → ∀ next ∈ target.step state, emitted state next = []

/-- Every erased dead end is accepted by an independently declared rejection
policy. That policy must account for retained external commitments; this law
does not authenticate it or permit an empty block to discard such commitments. -/
def ErasureLicensed {T : Type v} (target : OrderedSystem T) (stable : T → Bool)
    (acceptedRejection : T → Prop) : Prop :=
  ∀ state, stable state = false → target.step state = [] → acceptedRejection state

/-- For an externally retained committed readout, a rejected leaf must agree
with that retained readout. This is an erasure obligation, in addition to the
edge preservation law. It does not assert that arbitrary histories can be
discarded when a branch vanishes. -/
def ErasurePreserves {T : Type v} {A : Type w} (target : OrderedSystem T)
    (stable : T → Bool) (committed retained : T → A) : Prop :=
  target.ErasureLicensed stable (fun state => committed state = retained state)

/-- A declared family of committed observers is preserved exactly when each
of its components is preserved. Components may have different result types;
combining them does not identify permission, evidence, duties or costs. -/
theorem administrationPreserves_family_iff {T : Type v} {Index : Type u}
    {Value : Index → Type w} (target : OrderedSystem T) (stable : T → Bool)
    (read : T → (index : Index) → Value index) :
    target.AdministrationPreserves stable read ↔
      ∀ index, target.AdministrationPreserves stable (fun state => read state index) := by
  constructor
  · intro preserves index state administrative next member
    exact congrFun (preserves state administrative next member) index
  · intro preserves state administrative next member
    funext index
    exact preserves index state administrative next member

/-- Rejection must account for every selected observer. Keeping one component
cannot license dropping an outstanding commitment in another component. -/
theorem erasurePreserves_family_iff {T : Type v} {Index : Type u}
    {Value : Index → Type w} (target : OrderedSystem T) (stable : T → Bool)
    (committed retained : T → (index : Index) → Value index) :
    target.ErasurePreserves stable committed retained ↔
      ∀ index, target.ErasurePreserves stable
        (fun state => committed state index) (fun state => retained state index) := by
  constructor
  · intro licensed index state administrative deadEnd
    exact congrFun (licensed state administrative deadEnd) index
  · intro licensed state administrative deadEnd
    funext index
    exact licensed index state administrative deadEnd

theorem AdministrativeReach.preserves {T : Type v} {A : Type w}
    {target : OrderedSystem T} {stable : T → Bool} {read : T → A}
    (preserves : target.AdministrationPreserves stable read) {count : ℕ} {state last : T}
    (reach : target.AdministrativeReach stable count state last) : read last = read state := by
  induction reach with
  | here => rfl
  | step administrative member _ ih => exact ih.trans (preserves _ administrative _ member)

/-- Every surviving settled representative retains the committed readout. -/
theorem settle_preserves {T : Type v} {A : Type w} {target : OrderedSystem T}
    {stable : T → Bool} {read : T → A} (preserves : target.AdministrationPreserves stable read)
    (fuel : ℕ) {state last : T} (member : last ∈ target.settle stable fuel state) :
    read last = read state := by
  obtain ⟨_, _, reach⟩ := target.settle_reach fuel member
  exact reach.preserves preserves

/-- A visible outcome cannot be erased or duplicated by settling. -/
theorem settle_visible {T : Type v} {A : Type w} {target : OrderedSystem T}
    {stable : T → Bool} {outcome : T → Option A} (visible : ObservableStable stable outcome)
    (fuel : ℕ) {state : T} {answer : A} (observed : outcome state = some answer) :
    target.settle stable fuel state = [state] :=
  settle_of_stable fuel (visible state (by simp [observed]))

theorem erased_outcome_absent {T : Type v} {A : Type w} {target : OrderedSystem T}
    {stable : T → Bool} {outcome : T → Option A} (visible : ObservableStable stable outcome)
    (fuel : ℕ) {state : T} (erased : target.settle stable fuel state = []) :
    outcome state = none := by
  cases observed : outcome state with
  | none => rfl
  | some answer => have kept := settle_visible (target := target) visible fuel observed; rw [kept] at erased; cases erased

end OrderedSystem

/-! ## Computed classification of the existing event machine

This adapter does not identify a deterministic event machine with a branching
source. It exposes its actual continuation edges and boundary observations.
Publication remains stable even when its event list is empty. Calls stop at a
suspended boundary; following a saved continuation requires the existing
handler laws in `ProductiveBlocks`.
-/

namespace OrderedSystem

open ProductiveBlocks

def eventSystem {T E V R : Type} (machine : Machine T E V R) : OrderedSystem T where
  step state := match machine.step state with
    | some (.silent next) | some (.publish _ next) => [next]
    | _ => []
  halted state := match machine.step state with
    | some (.finish _) | some (.fail _) | some (.call _ _) => true
    | _ => false

def eventStable {T E V R : Type} (machine : Machine T E V R) (state : T) : Bool :=
  match machine.step state with
  | some transition => !transition.administrative
  | none => true

/-- The existing finite-run outcome carrier keeps fault, suspension, and stuck
separate. A continuing one-step run has no boundary outcome yet. -/
def eventOutcome {T E V R : Type} (machine : Machine T E V R) (state : T) :
    Option (Outcome T V R) :=
  match (machine.run 1 state).2 with
  | .exhausted _ => none
  | boundary => some boundary

/-- Read the actual one-step committed event list, including fault events. -/
def eventEmitted {T E V R : Type} (machine : Machine T E V R) (state _next : T) : List E :=
  (machine.run 1 state).1

theorem event_observable_stable {T E V R : Type} (machine : Machine T E V R) :
    ObservableStable (eventStable machine) (eventOutcome machine) := by
  intro state visible
  cases step : machine.step state with
  | none => simp [eventStable, step]
  | some transition =>
    cases transition <;>
      simp [eventStable, eventOutcome, Machine.run, step, Transition.administrative] at visible ⊢

theorem event_administration_silent {T E V R : Type} (machine : Machine T E V R) :
    (eventSystem machine).AdministrationSilent (eventStable machine) (eventEmitted machine) := by
  intro state administrative next _
  cases step : machine.step state with
  | none => simp [eventStable, step] at administrative
  | some transition =>
    cases transition <;>
      simp [eventStable, step, Transition.administrative] at administrative
    simp [eventEmitted, Machine.run, step]

/-- The computed classification never erases a dead end: the only unstable
transition is an actual silent continuation, with a successor. -/
theorem event_no_erased_dead_end {T E V R : Type} (machine : Machine T E V R) :
    (eventSystem machine).ErasureLicensed (eventStable machine) (fun _ => False) := by
  intro state administrative empty
  cases step : machine.step state with
  | none => simp [eventStable, step] at administrative
  | some transition =>
    cases transition <;>
      simp [eventStable, step, Transition.administrative] at administrative
    simp [eventSystem, step] at empty

/-- The administrative paths of the constructed adapter are actual silent
prefixes of the existing event runner, with exactly the path's primitive fuel.
The endpoint remains a residual; its boundary transition has not run yet. -/
theorem event_administrative_run {T E V R : Type} (machine : Machine T E V R)
    {count : ℕ} {state last : T}
    (reach : (eventSystem machine).AdministrativeReach (eventStable machine) count state last) :
    machine.run count state = ([], .exhausted last) := by
  induction reach with
  | here => rfl
  | @step count state middle last administrative member _ ih =>
    cases step : machine.step state with
    | none => simp [eventStable, step] at administrative
    | some transition =>
      cases transition <;>
        simp [eventStable, step, Transition.administrative] at administrative
      simp only [eventSystem, step, List.mem_singleton] at member
      subst middle
      exact (machine.run_succ_silent step).trans ih

/-- Settled representatives have an actual silent-run realization within the
per-path rank bound. This supplies neither a branching total-work bound nor a
clock for composing primitive schedulers. -/
theorem event_settle_realizes {T E V R : Type} (machine : Machine T E V R) {rank : T → ℕ}
    (ranked : (eventSystem machine).AdministrationRanked (eventStable machine) rank)
    {state last : T}
    (member : last ∈ (eventSystem machine).settle (eventStable machine) (rank state + 1) state) :
    ∃ count ≤ rank state, machine.run count state = ([], .exhausted last) ∧
      eventStable machine last = true := by
  obtain ⟨count, _, reach⟩ := (eventSystem machine).settle_reach _ member
  have bound := reach.count_le_rank ranked
  exact ⟨count, by omega, event_administrative_run machine reach,
    settle_stable ranked _ (Nat.lt_succ_self _) member⟩

end OrderedSystem

/-- Ordered outcome agreement is an additional state-readout law. It neither
identifies different outcome logics nor grants erasure of primitive effects. -/
theorem BlockSimulation.outcomes {S : Type u} {T : Type v} {A B : Type w}
    {source : OrderedSystem S} {target : OrderedSystem T}
    {stable : T → Bool} {rank : T → ℕ} {block : List S → T → Prop}
    (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank)
    {outcome : S → Option A} {outcome' : T → Option B} {agree : A → B → Prop}
    (agreement : ∀ {state target'}, StableRelated stable block state target' →
      Option.Rel agree (outcome state) (outcome' target'))
    (fuel : ℕ) {state : S} {initial : T} (related : StableRelated stable block state initial) :
    List.Forall₂ agree ((source.runFrontier fuel [state]).filterMap outcome)
      (((target.saturate stable rank).runFrontier fuel [initial]).filterMap outcome') :=
  (simulation.saturated ranked).answers agreement fuel related

/-- The same independent outcome agreement after the actual ranked loading
of a single source occurrence, rather than assuming its entry is stable. -/
theorem BlockSimulation.outcomes_loaded {S : Type u} {T : Type v} {A B : Type w}
    {source : OrderedSystem S} {target : OrderedSystem T}
    {stable : T → Bool} {rank : T → ℕ} {block : List S → T → Prop}
    (simulation : BlockSimulation source target stable block)
    (ranked : target.AdministrationRanked stable rank)
    {outcome : S → Option A} {outcome' : T → Option B} {agree : A → B → Prop}
    (agreement : ∀ {state target'}, StableRelated stable block state target' →
      Option.Rel agree (outcome state) (outcome' target'))
    (fuel : ℕ) {state : S} {initial : T} (loaded : block [state] initial) :
    List.Forall₂ agree ((source.runFrontier fuel [state]).filterMap outcome)
      (((target.saturate stable rank).runFrontier fuel
        (target.settle stable (rank initial + 1) initial)).filterMap outcome') := by
  obtain ⟨boundary, settled, related⟩ := simulation.loaded_boundary ranked loaded
  rw [settled]
  exact simulation.outcomes ranked agreement fuel related

/-- Without administration, saturation is the target itself. -/
theorem OrderedSystem.saturate_all_stable {T : Type v} (target : OrderedSystem T) (rank : T → ℕ) :
    (target.saturate (fun _ => true) rank).step = target.step := by
  funext state
  simp only [OrderedSystem.saturate]
  generalize target.step state = successors
  induction successors with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, OrderedSystem.settle_of_stable _ rfl, ih]
      rfl

/-- **Lockstep is the case without administration**: every ordered simulation
is a block simulation in which every target state is stable and stands for the
one source state it is related to. -/
theorem OrderedSimulation.toBlockSimulation {S : Type u} {T : Type v} {source : OrderedSystem S}
    {target : OrderedSystem T} {related : S → T → Prop}
    (simulation : OrderedSimulation source target related) :
    BlockSimulation source target (fun _ => true)
      (fun occurrences target' => ∃ state, occurrences = [state] ∧ related state target') where
  stable_single := by
    rintro occurrences target' ⟨state, rfl, pair⟩ -
    exact ⟨state, rfl, simulation.halted pair⟩
  stable_step := by
    rintro state target' ⟨state', single, pair⟩ -
    obtain rfl := List.singleton_inj.mp single
    refine ⟨(source.step state).map fun next => [next], ?_, ?_⟩
    · rw [List.forall₂_map_left_iff]
      exact (simulation.step pair).imp fun next next' relatedNext => ⟨next, rfl, relatedNext⟩
    · generalize source.step state = successors
      induction successors with
      | nil => rfl
      | cons head tail ih => simp [ih]
  administrative_split := by
    intro _ _ _ administrative
    cases administrative

end Mettapedia.GSLT.Distinction

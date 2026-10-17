import Mettapedia.GSLT.Distinction.OrderedAdministration

/-!
# Controls for ordered simulations up to ranked administration

* **Lockstep is too strict** (`spec`, `impl`).  The specification branches into
  three occurrences in one step.  The implementation reaches them through an
  administrative state that branches again and tries an alternative that fails.
  No lockstep ordered simulation relates the two roots (`no_lockstep`), but a
  block simulation does (`impl_block`), and the saturated implementation has
  exactly the specification's successors, in order (`impl_saturated_root`).
* **Administrative divergence is excluded** (`loopSystem`): an administrative
  self-loop admits no rank (`loop_not_ranked`).
* **Genuine divergence is kept** (`spinSpec`, `spinImpl`): a specification
  that runs forever is simulated by a stable implementation loop
  (`spin_block`), with nothing to rank.
* **Merging occurrences is rejected** (`dupSpec`, `mergeImpl`).  The
  specification has two equal-looking successor occurrences; an implementation
  with one has the same set of successors but no block simulation relates the
  roots (`merge_rejected`).
* **Saturation does not preserve every raw outcome** (`faultBoundary_block`).
  An unstable halted fault can carry an empty block and disappear under settling.
  The saturated frontiers agree exactly while the raw target reaches the fault.
  Outcome observations and permission to discard empty-block branches are
  additional obligations; stable unhalted dead ends are allowed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.OrderedAdministrationControls

open OrderedSystem BlockSimulation

/-! ## Lockstep is too strict -/

inductive Spec where
  | root | a | b | c
  deriving DecidableEq, Repr

inductive Impl where
  | root | middle | failed | a | b | c
  deriving DecidableEq, Repr

/-- One step from the root to three answers. -/
def spec : OrderedSystem Spec where
  step
    | .root => [.a, .b, .c]
    | _ => []
  halted
    | .root => false
    | _ => true

/-- The implementation reaches the same answers through an administrative state
that branches again and tries a failing alternative. -/
def impl : OrderedSystem Impl where
  step
    | .root => [.middle, .c]
    | .middle => [.a, .failed, .b]
    | _ => []
  halted
    | .a | .b | .c => true
    | _ => false

def implStable : Impl → Bool
  | .middle | .failed => false
  | _ => true

def implRank : Impl → ℕ
  | .middle => 1
  | _ => 0

/-- Which source occurrences each implementation state stands for. -/
def implBlock : List Spec → Impl → Prop
  | occurrences, .root => occurrences = [.root]
  | occurrences, .middle => occurrences = [.a, .b]
  | occurrences, .failed => occurrences = []
  | occurrences, .a => occurrences = [.a]
  | occurrences, .b => occurrences = [.b]
  | occurrences, .c => occurrences = [.c]

theorem impl_ranked : impl.AdministrationRanked implStable implRank := by
  intro state administrative next member
  cases state <;> simp only [implStable, Bool.true_eq_false] at administrative
  · simp only [impl, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · simp [impl] at member

theorem impl_block : BlockSimulation spec impl implStable implBlock where
  stable_single := by
    intro occurrences target' blocked isStable
    cases target' <;> simp only [implStable, Bool.false_eq_true] at isStable <;>
      simp only [implBlock] at blocked <;> subst blocked <;> exact ⟨_, rfl, rfl⟩
  stable_step := by
    intro state target' blocked isStable
    cases target' <;> simp only [implStable, Bool.false_eq_true] at isStable <;>
      simp only [implBlock, List.cons.injEq, and_true] at blocked <;> subst blocked
    · exact ⟨[[.a, .b], [.c]], .cons rfl (.cons rfl .nil), rfl⟩
    all_goals exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro occurrences target' blocked isStable
    cases target' <;> simp only [implStable, Bool.true_eq_false] at isStable <;>
      simp only [implBlock] at blocked <;> subst blocked
    · exact ⟨[[.a], [], [.b]], .cons rfl (.cons rfl (.cons rfl .nil)), rfl⟩
    · exact ⟨[], .nil, rfl⟩

/-- The saturated implementation is an ordered simulation of the specification. -/
theorem impl_saturated :
    OrderedSimulation spec (impl.saturate implStable implRank) (StableRelated implStable implBlock) :=
  impl_block.saturated impl_ranked

/-- Saturation flattens the nested branching and drops the failed alternative. -/
theorem impl_saturated_root :
    (impl.saturate implStable implRank).step .root = [.a, .b, .c] := rfl

/-- **No lockstep ordered simulation relates the roots**: the implementation's
first step has two successors where the specification has three. -/
theorem no_lockstep :
    ¬ ∃ related : Spec → Impl → Prop, OrderedSimulation spec impl related ∧ related .root .root := by
  rintro ⟨related, simulation, roots⟩
  have lengths := (simulation.step roots).length_eq
  simp [spec, impl] at lengths

/-- The frontiers agree at every fuel, read at stable states. -/
theorem impl_frontiers (fuel : ℕ) :
    List.Forall₂ (StableRelated implStable implBlock) (spec.runFrontier fuel [.root])
      ((impl.saturate implStable implRank).runFrontier fuel
        (impl.settle implStable (implRank .root + 1) .root)) :=
  impl_block.frontiers impl_ranked fuel rfl

/-! ## Administrative divergence is excluded -/

inductive Spin where
  | spin
  deriving DecidableEq, Repr

/-- An administrative state that steps to itself. -/
def loopSystem : OrderedSystem Spin where
  step _ := [.spin]
  halted _ := false

theorem loop_not_ranked (rank : Spin → ℕ) :
    ¬ loopSystem.AdministrationRanked (fun _ => false) rank :=
  OrderedSystem.not_ranked_of_loop (system := loopSystem) (state := .spin) rfl
    (List.mem_singleton_self _) rank

/-! ## Genuine divergence is kept -/

/-- A specification that runs forever. -/
def spinSpec : OrderedSystem Spin where
  step _ := [.spin]
  halted _ := false

/-- An implementation that runs forever through a stable state. -/
def spinImpl : OrderedSystem Spin where
  step _ := [.spin]
  halted _ := false

theorem spin_ranked : spinImpl.AdministrationRanked (fun _ => true) (fun _ => 0) := by
  intro _ administrative
  cases administrative

theorem spin_block :
    BlockSimulation spinSpec spinImpl (fun _ => true) (fun occurrences _ => occurrences = [.spin]) where
  stable_single := by
    intro occurrences _ blocked _
    exact ⟨.spin, blocked, rfl⟩
  stable_step := by
    intro _ _ _ _
    exact ⟨[[.spin]], .cons rfl .nil, rfl⟩
  administrative_split := by
    intro _ _ _ administrative
    cases administrative

/-- The infinite source run is matched at every fuel. -/
theorem spin_frontiers (fuel : ℕ) :
    List.Forall₂ (StableRelated (fun _ => true) (fun occurrences (_ : Spin) => occurrences = [.spin]))
      (spinSpec.runFrontier fuel [.spin])
      ((spinImpl.saturate (fun _ => true) (fun _ => 0)).runFrontier fuel
        (spinImpl.settle (fun _ => true) 1 .spin)) :=
  spin_block.frontiers spin_ranked fuel rfl

/-! ## Merging occurrences is rejected -/

inductive Pair where
  | root | answer
  deriving DecidableEq, Repr

/-- Two equal-looking successor occurrences. -/
def dupSpec : OrderedSystem Pair where
  step
    | .root => [.answer, .answer]
    | .answer => []
  halted
    | .root => false
    | .answer => true

/-- One successor: the same set of successors, one occurrence fewer. -/
def mergeImpl : OrderedSystem Pair where
  step
    | .root => [.answer]
    | .answer => []
  halted
    | .root => false
    | .answer => true

theorem same_successor_set (state : Pair) :
    ∀ next, next ∈ dupSpec.step state ↔ next ∈ mergeImpl.step state := by
  cases state <;> simp [dupSpec, mergeImpl]

/-- **No block simulation relates the roots** when every state is stable:
the single stable successor would have to stand for two occurrences. -/
theorem merge_rejected (block : List Pair → Pair → Prop) :
    ¬ (BlockSimulation dupSpec mergeImpl (fun _ => true) block ∧ block [.root] .root) := by
  rintro ⟨simulation, roots⟩
  obtain ⟨blocks, lists, flattened⟩ := simulation.stable_step roots rfl
  simp only [mergeImpl] at lists
  cases lists with
  | cons head rest =>
      cases rest
      obtain ⟨state, single, _⟩ := simulation.stable_single head rfl
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, dupSpec] at flattened
      rw [single] at flattened
      cases flattened

/-! ## Saturation and raw terminal outcomes -/

inductive FaultBoundary where
  | root | fault
  deriving DecidableEq, Repr

/-- The source remains stuck at its unhalted root. -/
def faultBoundarySource : OrderedSystem FaultBoundary where
  step _ := []
  halted
    | .root => false
    | .fault => true

/-- The raw target reaches a halted fault after one step. -/
def faultBoundaryTarget : OrderedSystem FaultBoundary where
  step
    | .root => [.fault]
    | .fault => []
  halted
    | .root => false
    | .fault => true

def faultBoundaryStable : FaultBoundary → Bool
  | .root => true
  | .fault => false

def faultBoundaryBlock : List FaultBoundary → FaultBoundary → Prop
  | occurrences, .root => occurrences = [.root]
  | occurrences, .fault => occurrences = []

/-- A terminal administrative state has no outgoing rank obligation. -/
theorem faultBoundary_ranked :
    faultBoundaryTarget.AdministrationRanked faultBoundaryStable (fun _ => 0) := by
  intro state administrative next member
  cases state <;> simp_all [faultBoundaryStable, faultBoundaryTarget]

/-- The block laws permit an unstable halted fault to represent no occurrence. -/
theorem faultBoundary_block :
    BlockSimulation faultBoundarySource faultBoundaryTarget
      faultBoundaryStable faultBoundaryBlock where
  stable_single := by
    intro occurrences state blocked stable
    cases state with
    | root => exact ⟨.root, blocked, rfl⟩
    | fault => simp [faultBoundaryStable] at stable
  stable_step := by
    intro state target blocked stable
    cases target with
    | root =>
      obtain rfl : state = .root := List.singleton_inj.mp blocked
      exact ⟨[[]], .cons rfl .nil, rfl⟩
    | fault => simp [faultBoundaryStable] at stable
  administrative_split := by
    intro occurrences state blocked administrative
    cases state with
    | root => simp [faultBoundaryStable] at administrative
    | fault => exact ⟨[], .nil, blocked.symm⟩

theorem faultBoundary_saturated :
    OrderedSimulation faultBoundarySource
      (faultBoundaryTarget.saturate faultBoundaryStable (fun _ => 0))
      (StableRelated faultBoundaryStable faultBoundaryBlock) :=
  faultBoundary_block.saturated faultBoundary_ranked

/-- Both normalized runs retain the same stuck root at every fuel. -/
theorem faultBoundary_equal_frontiers (fuel : ℕ) :
    faultBoundarySource.runFrontier fuel [.root] =
      (faultBoundaryTarget.saturate faultBoundaryStable (fun _ => 0)).runFrontier fuel [.root] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change faultBoundarySource.runFrontier fuel [.root] =
      (faultBoundaryTarget.saturate faultBoundaryStable (fun _ => 0)).runFrontier fuel [.root]
    exact ih

/-- The actual one-step target frontier contains the fault that settling omits. -/
theorem faultBoundary_raw_fault_erased :
    faultBoundaryTarget.runFrontier 1 [.root] = [.fault] ∧
      faultBoundaryTarget.halted .fault = true ∧
      faultBoundaryTarget.settle faultBoundaryStable 1 .fault = [] ∧
      (faultBoundaryTarget.saturate faultBoundaryStable (fun _ => 0)).runFrontier 1 [.root] = [.root] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem faultBoundary_raw_frontier_differs :
    faultBoundaryTarget.runFrontier 1 [.root] ≠
      (faultBoundaryTarget.saturate faultBoundaryStable (fun _ => 0)).runFrontier 1 [.root] := by
  decide

/-- A nonempty block at a stable unhalted dead end is allowed by the contract. -/
theorem stable_stuck_block :
    BlockSimulation faultBoundarySource faultBoundarySource (fun _ => true)
      (fun occurrences state => occurrences = [state]) where
  stable_single := by
    intro occurrences state blocked _
    exact ⟨state, blocked, rfl⟩
  stable_step := by
    intro _ _ _ _
    exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro _ _ _ administrative
    cases administrative

theorem stable_stuck_root :
    faultBoundarySource.halted .root = false ∧ faultBoundarySource.step .root = [] :=
  ⟨rfl, rfl⟩

/-! ## Two independently represented saturated boundaries -/

def joinSpec : OrderedSystem Spec where
  step
    | .root => [.a, .b, .a, .c]
    | _ => []
  halted := spec.halted

def joinMiddle : OrderedSystem Impl where
  step
    | .root => [.middle, .c]
    | .middle => [.a, .failed, .b, .a]
    | _ => []
  halted := impl.halted

def joinMiddleBlock : List Spec → Impl → Prop
  | occurrences, .middle => occurrences = [.a, .b, .a]
  | occurrences, state => implBlock occurrences state

theorem joinMiddle_ranked : joinMiddle.AdministrationRanked implStable implRank := by
  intro state administrative next member
  cases state <;> simp only [implStable, Bool.true_eq_false] at administrative
  · simp only [joinMiddle, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · simp [joinMiddle] at member

theorem joinMiddle_block : BlockSimulation joinSpec joinMiddle implStable joinMiddleBlock where
  stable_single := by
    intro occurrences state blocked stable
    cases state <;> simp only [implStable, Bool.false_eq_true] at stable <;>
      simp only [joinMiddleBlock, implBlock] at blocked <;> subst blocked <;> exact ⟨_, rfl, rfl⟩
  stable_step := by
    intro source state blocked stable
    cases state <;> simp only [implStable, Bool.false_eq_true] at stable <;>
      simp only [joinMiddleBlock, implBlock, List.cons.injEq, and_true] at blocked <;> subst blocked
    · exact ⟨[[.a, .b, .a], [.c]], .cons rfl (.cons rfl .nil), rfl⟩
    all_goals exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro occurrences state blocked administrative
    cases state <;> simp only [implStable, Bool.true_eq_false] at administrative <;>
      simp only [joinMiddleBlock, implBlock] at blocked <;> subst blocked
    · exact ⟨[[.a], [], [.b], [.a]], .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))), rfl⟩
    · exact ⟨[], .nil, rfl⟩

/-- The second machine has a different primitive branching and depth. -/
inductive Lowered where
  | root | loading | fork | a | b | c
  deriving DecidableEq, Repr

def joinTarget : OrderedSystem Lowered where
  step
    | .root => [.loading]
    | .loading => [.fork, .c]
    | .fork => [.a, .b, .a]
    | _ => []
  halted
    | .a | .b | .c => true
    | _ => false

def joinStable : Lowered → Bool
  | .loading | .fork => false
  | _ => true

def joinRank : Lowered → ℕ
  | .loading => 2
  | .fork => 1
  | _ => 0

def joinBlock : List Spec → Lowered → Prop
  | occurrences, .root => occurrences = [.root]
  | occurrences, .loading => occurrences = [.a, .b, .a, .c]
  | occurrences, .fork => occurrences = [.a, .b, .a]
  | occurrences, .a => occurrences = [.a]
  | occurrences, .b => occurrences = [.b]
  | occurrences, .c => occurrences = [.c]

theorem joinTarget_ranked : joinTarget.AdministrationRanked joinStable joinRank := by
  intro state administrative next member
  cases state <;> simp only [joinStable, Bool.true_eq_false] at administrative
  · simp only [joinTarget, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · simp only [joinTarget, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide

theorem joinTarget_block : BlockSimulation joinSpec joinTarget joinStable joinBlock where
  stable_single := by
    intro occurrences state blocked stable
    cases state <;> simp only [joinStable, Bool.false_eq_true] at stable <;>
      simp only [joinBlock] at blocked <;> subst blocked <;> exact ⟨_, rfl, rfl⟩
  stable_step := by
    intro source state blocked stable
    cases state <;> simp only [joinStable, Bool.false_eq_true] at stable <;>
      simp only [joinBlock, List.cons.injEq, and_true] at blocked <;> subst blocked
    · exact ⟨[[.a, .b, .a, .c]], .cons rfl .nil, rfl⟩
    all_goals exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro occurrences state blocked administrative
    cases state <;> simp only [joinStable, Bool.true_eq_false] at administrative <;>
      simp only [joinBlock] at blocked <;> subst blocked
    · exact ⟨[[.a, .b, .a], [.c]], .cons rfl (.cons rfl .nil), rfl⟩
    · exact ⟨[[.a], [.b], [.a]], .cons rfl (.cons rfl (.cons rfl .nil)), rfl⟩

def decodeMiddle : Impl → Spec
  | .a => .a
  | .b => .b
  | .c => .c
  | _ => .root

/-- Local computed decoder equations; no correspondence is supplied as a premise. -/
def joinAdapter : StableBoundaryAdapter joinMiddle implStable implRank joinSpec where
  decode := decodeMiddle
  steps := by
    intro state stable
    cases state <;> simp only [implStable, Bool.false_eq_true] at stable <;> rfl
  halts := by
    intro state stable
    cases state <;> simp only [implStable, Bool.false_eq_true] at stable <;> rfl

def joinRelated : Spec → Lowered → Prop :=
  Relation.Comp
    (Relation.Comp (StableRelated implStable joinMiddleBlock)
      (fun state decoded => implStable state = true ∧ decoded = joinAdapter.decode state))
    (StableRelated joinStable joinBlock)

theorem joined_simulation :
    OrderedSimulation joinSpec (joinTarget.saturate joinStable joinRank) joinRelated :=
  joinMiddle_block.sequential joinMiddle_ranked joinAdapter joinTarget_block joinTarget_ranked

theorem joined_frontiers (fuel : ℕ) :
    List.Forall₂ joinRelated (joinSpec.runFrontier fuel [.root])
      ((joinTarget.saturate joinStable joinRank).runFrontier fuel [.root]) := by
  apply joined_simulation.runFrontier fuel
  exact .cons ⟨.root, ⟨.root, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, ⟨rfl, rfl⟩⟩ .nil

/-- Duplicate occurrences stay in their original positions through both joins. -/
theorem joined_duplicate_order :
    (joinMiddle.saturate implStable implRank).step .root = [.a, .b, .a, .c] ∧
      (joinTarget.saturate joinStable joinRank).step .root = [.a, .b, .a, .c] :=
  ⟨rfl, rfl⟩

/-- A distinct primitive carrier retains the caller's ownership tag. Its
steps have no administration at the declared all-stable middle boundary. -/
def ownedBoundary : OrderedSystem (ℕ × Spec) := joinSpec.inContext (fun _ => true)

def ownedBoundaryBlock (occurrences : List Spec) (state : ℕ × Spec) : Prop :=
  ∃ source, occurrences = [source] ∧ state = (9, source)

theorem ownedBoundary_block :
    BlockSimulation joinSpec ownedBoundary (fun _ => true) ownedBoundaryBlock := by
  apply OrderedSimulation.toBlockSimulation
  exact OrderedSimulation.ofMap (fun state => (9, state)) (fun _ => rfl) (fun _ => rfl)

theorem ownedBoundary_ranked :
    ownedBoundary.AdministrationRanked (fun _ => true) (fun _ => 0) := by
  intro _ administrative
  cases administrative

theorem ownedBoundary_closed : ownedBoundary.PrimitiveStepClosed (fun _ => true) := by
  intro _ _ _ _
  rfl

def ownedJoinRelated : Spec → (ℕ × Lowered) → Prop :=
  Relation.Comp
    (Relation.Comp (StableRelated (fun _ => true) ownedBoundaryBlock)
      (fun state decoded => (true : Bool) = true ∧ decoded = state))
    (StableRelated (contextStable (fun (_ : ℕ) => true) joinStable)
      (ContextBlock (fun (_ : ℕ) => true) joinBlock))

/-- The restricted primitive-middle theorem is instantiated by actual tagged
transitions, followed by a two-layer administrative implementation. -/
theorem primitive_owned_join :
    OrderedSimulation joinSpec
      ((joinTarget.inContext (fun (_ : ℕ) => true)).saturate
        (contextStable (fun (_ : ℕ) => true) joinStable) (fun state => joinRank state.2))
      ownedJoinRelated :=
  ownedBoundary_block.comp_primitive_middle ownedBoundary_ranked ownedBoundary_closed
    (joinTarget_block.inContext (fun (_ : ℕ) => true))
    (OrderedSystem.inContext_ranked (fun (_ : ℕ) => true) joinTarget_ranked)

theorem primitive_owned_frontiers (fuel : ℕ) :
    List.Forall₂ ownedJoinRelated (joinSpec.runFrontier fuel [.root])
      (((joinTarget.inContext (fun (_ : ℕ) => true)).saturate
        (contextStable (fun (_ : ℕ) => true) joinStable) (fun state => joinRank state.2)).runFrontier
          fuel [(9, .root)]) := by
  apply primitive_owned_join.runFrontier fuel
  exact .cons ⟨(9, .root), ⟨(9, .root), ⟨⟨.root, rfl, rfl⟩, rfl⟩, ⟨rfl, rfl⟩⟩,
    ⟨⟨rfl, [.root], rfl, rfl⟩, rfl⟩⟩ .nil

theorem primitive_owned_duplicate_order :
    ((joinTarget.inContext (fun (_ : ℕ) => true)).saturate
      (contextStable (fun (_ : ℕ) => true) joinStable) (fun state => joinRank state.2)).step
        (9, .root) = [(9, .a), (9, .b), (9, .a), (9, .c)] := rfl

/-- Loading is administrative before the root's productive branching. -/
def entryTarget : OrderedSystem Lowered where
  step
    | .loading => [.root]
    | .root => [.a, .b, .a, .c]
    | _ => []
  halted := joinTarget.halted

def entryStable : Lowered → Bool
  | .loading => false
  | _ => true

def entryRank : Lowered → ℕ
  | .loading => 1
  | _ => 0

def entryBlock : List Spec → Lowered → Prop
  | occurrences, .loading | occurrences, .root => occurrences = [.root]
  | _, .fork => False
  | occurrences, .a => occurrences = [.a]
  | occurrences, .b => occurrences = [.b]
  | occurrences, .c => occurrences = [.c]

theorem entry_ranked : entryTarget.AdministrationRanked entryStable entryRank := by
  intro state administrative next member
  cases state <;> simp only [entryStable, Bool.true_eq_false] at administrative
  simp only [entryTarget, List.mem_singleton] at member
  subst next
  decide

theorem entry_block : BlockSimulation joinSpec entryTarget entryStable entryBlock where
  stable_single := by
    intro occurrences state blocked stable
    cases state with
    | loading => cases stable
    | fork => exact blocked.elim
    | root | a | b | c => exact ⟨_, blocked, rfl⟩
  stable_step := by
    intro source state blocked stable
    cases state with
    | loading => cases stable
    | fork => exact blocked.elim
    | root =>
      obtain rfl := List.singleton_inj.mp blocked
      exact ⟨[[.a], [.b], [.a], [.c]], .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil))), rfl⟩
    | a | b | c =>
      obtain rfl := List.singleton_inj.mp blocked
      exact ⟨[], .nil, rfl⟩
  administrative_split := by
    intro occurrences state blocked administrative
    cases state <;> simp only [entryStable, Bool.true_eq_false] at administrative
    exact ⟨[[.root]], .cons rfl .nil, blocked.symm⟩

/-- The unique boundary is computed from an actually unstable entry. -/
theorem loaded_entry_boundary :
    ∃ boundary, entryTarget.settle entryStable (entryRank .loading + 1) .loading = [boundary] ∧
      StableRelated entryStable entryBlock .root boundary :=
  entry_block.loaded_boundary entry_ranked rfl

/-- The first primitive middle state actually enters administration, so the
restricted primitive join cannot be applied to this saturated composition. -/
theorem join_primitive_closure_rejected : ¬ joinMiddle.PrimitiveStepClosed implStable := by
  intro closed
  have bad := closed .root rfl .middle (by simp [joinMiddle])
  cases bad

theorem swapped_decoder_rejected :
    ¬ ∃ adapter : StableBoundaryAdapter joinMiddle implStable implRank joinSpec,
      adapter.decode .root = .root ∧ adapter.decode .a = .b ∧ adapter.decode .b = .a ∧
        adapter.decode .c = .c := by
  rintro ⟨adapter, root, a, b, c⟩
  have equation := adapter.steps .root rfl
  rw [root] at equation
  change [.a, .b, .a, .c] =
    [adapter.decode .a, adapter.decode .b, adapter.decode .a, adapter.decode .c] at equation
  rw [a, b, c] at equation
  cases equation

/-! ## Permission-gated contextual lifting -/

inductive EvaluationContext where
  | call | quote
  deriving DecidableEq, Repr

def mayExecute : EvaluationContext → Bool
  | .call => true
  | .quote => false

theorem contextual_block :
    BlockSimulation (spec.inContext mayExecute) (impl.inContext mayExecute)
      (contextStable mayExecute implStable) (ContextBlock mayExecute implBlock) :=
  impl_block.inContext mayExecute

theorem contextual_frontiers (fuel : ℕ) :
    List.Forall₂ (StableRelated (contextStable mayExecute implStable) (ContextBlock mayExecute implBlock))
      ((spec.inContext mayExecute).runFrontier fuel [(.call, .root)])
      (((impl.inContext mayExecute).saturate (contextStable mayExecute implStable)
        (fun state => implRank state.2)).runFrontier fuel [(.call, .root)]) := by
  apply (contextual_block.saturated (OrderedSystem.inContext_ranked mayExecute impl_ranked)).runFrontier fuel
  exact .cons ⟨⟨rfl, [.root], rfl, rfl⟩, rfl⟩ .nil

theorem quoted_root_is_held :
    (impl.inContext mayExecute).step (.quote, .root) = [] ∧
      (impl.inContext mayExecute).halted (.quote, .root) = true :=
  impl.held_no_step rfl .root

theorem held_context_has_no_active_block (occurrences : List (EvaluationContext × Spec)) (state : Impl) :
    ¬ ContextBlock mayExecute implBlock occurrences (.quote, state) := by
  rintro ⟨permitted, _⟩
  cases permitted

theorem unauthorized_inner_evaluation_rejected :
    ¬ ∃ related : (EvaluationContext × Spec) → (EvaluationContext × Impl) → Prop,
      OrderedSimulation (spec.inContext (fun _ => true)) (impl.inContext mayExecute) related ∧
        related (.quote, .root) (.quote, .root) := by
  rintro ⟨related, simulation, roots⟩
  have lengths := (simulation.step roots).length_eq
  simp [OrderedSystem.inContext, mayExecute, spec] at lengths

theorem held_readout_is_not_inner_return :
    contextOutcome mayExecute (fun (_ : Impl) => some (7 : ℕ)) (.quote, .a) =
      some (ContextReadout.held .quote .a) ∧
    contextOutcome mayExecute (fun (_ : Impl) => some (7 : ℕ)) (.quote, .a) ≠
      some (ContextReadout.active .quote 7) := by
  refine ⟨rfl, ?_⟩
  intro same
  cases same

/-! ## Independent outcome and committed-effect licences -/

def faultOutcome : FaultBoundary → Option ℕ
  | .root => none
  | .fault => some 9

theorem erased_fault_observation_rejected : ¬ ObservableStable faultBoundaryStable faultOutcome := by
  intro safe
  have bad := safe .fault (by decide)
  cases bad

/-- A fault branch with a committed event cannot be equated with an externally
retained empty ledger when it is discarded. -/
theorem erased_commitment_rejected :
    ¬ faultBoundaryTarget.ErasurePreserves faultBoundaryStable
      (fun state => match state with | .fault => [9] | .root => [])
      (fun _ => ([] : List ℕ)) := by
  intro safe
  have bad := safe .fault rfl rfl
  cases bad

theorem failed_candidate_erasure_licensed :
    impl.ErasureLicensed implStable (fun state => state = .failed) := by
  intro state administrative empty
  cases state <;> simp_all [implStable, impl]

open ProductiveBlocks

/-- An actual event machine: a silent load, duplicate publication, completion,
a fault with its own event, a suspension, and a stuck state. -/
def observableMachine : Machine ℕ ℕ ℕ ℕ where
  step
    | 0 => some (.silent 1)
    | 1 => some (.publish [7, 7] 2)
    | 2 => some (.finish 8)
    | 3 => some (.fail [9])
    | 4 => some (.call 10 2)
    | _ => none

theorem computed_event_licences :
    ObservableStable (eventStable observableMachine) (eventOutcome observableMachine) ∧
    (eventSystem observableMachine).AdministrationSilent (eventStable observableMachine)
      (eventEmitted observableMachine) ∧
    (eventSystem observableMachine).ErasureLicensed (eventStable observableMachine) (fun _ => False) :=
  ⟨event_observable_stable observableMachine, event_administration_silent observableMachine,
    event_no_erased_dead_end observableMachine⟩

theorem actual_event_boundary_readouts :
    eventStable observableMachine 0 = false ∧
    eventStable observableMachine 1 = true ∧
    eventEmitted observableMachine 1 2 = [7, 7] ∧
    eventOutcome observableMachine 2 = some (.finished 8) ∧
    eventOutcome observableMachine 3 = some (.faulted) ∧
    eventEmitted observableMachine 3 3 = [9] ∧
    eventOutcome observableMachine 4 = some (.suspended 10 2) ∧
    eventOutcome observableMachine 5 = some (.stuck 5) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem observableMachine_ranked :
    (eventSystem observableMachine).AdministrationRanked (eventStable observableMachine)
      (fun state => if state = 0 then 1 else 0) := by
  intro state administrative next member
  cases state with
  | zero =>
    simp only [eventSystem, observableMachine, List.mem_singleton] at member
    subst next
    decide
  | succ state =>
    cases state with
    | zero => cases administrative
    | succ state =>
      cases state with
      | zero => cases administrative
      | succ state =>
        cases state with
        | zero => cases administrative
        | succ state => cases state <;> simp [eventStable, observableMachine, Transition.administrative] at administrative

/-- The settled load is realized by the actual finite event runner, before
the separate stable publication transition runs. -/
theorem silent_boundary_has_actual_runner :
    ∃ count ≤ 1, observableMachine.run count 0 = ([], .exhausted 1) ∧
      eventStable observableMachine 1 = true :=
  event_settle_realizes observableMachine observableMachine_ranked
    (state := 0) (last := 1) (by decide)

def committedLedger : ℕ → List ℕ
  | 0 | 1 => [3]
  | _ => [3, 7, 7]

theorem silent_load_preserves_prior_commitment :
    (eventSystem observableMachine).AdministrationPreserves
      (eventStable observableMachine) committedLedger := by
  intro state administrative next member
  cases state with
  | zero => simp only [eventSystem, observableMachine, List.mem_singleton] at member; subst next; rfl
  | succ state =>
    cases state with
    | zero => cases administrative
    | succ state =>
      cases state with
      | zero => cases administrative
      | succ state =>
        cases state with
        | zero => cases administrative
        | succ state => cases state <;> simp [eventStable, observableMachine, Transition.administrative] at administrative

theorem settling_retains_prior_commitment :
    ∀ next ∈ (eventSystem observableMachine).settle (eventStable observableMachine) 2 0,
      committedLedger next = [3] := by
  intro next member
  exact settle_preserves silent_load_preserves_prior_commitment 2 member

theorem effectful_administration_rejected :
    ¬ (eventSystem observableMachine).AdministrationSilent (fun state => decide (state ≠ 1))
      (eventEmitted observableMachine) := by
  intro silent
  have bad := silent 1 rfl 2 (by simp [eventSystem, observableMachine])
  cases bad

theorem hidden_ledger_write_rejected :
    ¬ (eventSystem observableMachine).AdministrationPreserves (eventStable observableMachine)
      (fun state => if state = 0 then ([] : List ℕ) else [7]) := by
  intro preserved
  have bad := preserved 0 rfl 1 (by simp [eventSystem, observableMachine])
  simp at bad

def specOutcome : Spec → Option Spec
  | .root => none
  | state => some state

def implOutcome : Impl → Option Spec
  | .a => some .a
  | .b => some .b
  | .c => some .c
  | _ => none

theorem impl_visible_outcomes : ObservableStable implStable implOutcome := by
  intro state visible
  cases state <;> simp [implOutcome, implStable] at visible ⊢

theorem outcomes_agree : ∀ {state target}, StableRelated implStable implBlock state target →
    Option.Rel Eq (specOutcome state) (implOutcome target) := by
  rintro state target ⟨blocked, stable⟩
  cases target <;> simp only [implStable, Bool.false_eq_true] at stable <;>
    simp only [implBlock, List.cons.injEq, and_true] at blocked <;> subst blocked
  · exact .none
  all_goals exact .some rfl

/-- Outcome transport uses an independently proved readout law, retaining
ordered answer occurrences through the branching administrative implementation. -/
theorem impl_ordered_outcomes (fuel : ℕ) :
    List.Forall₂ Eq ((spec.runFrontier fuel [.root]).filterMap specOutcome)
      (((impl.saturate implStable implRank).runFrontier fuel [.root]).filterMap implOutcome) :=
  impl_block.outcomes impl_ranked outcomes_agree fuel ⟨rfl, rfl⟩

end Mettapedia.GSLT.Distinction.OrderedAdministrationControls

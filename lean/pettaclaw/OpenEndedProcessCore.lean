import ThreePolicyFusion

/-!
# OpenEndedProcessCore — synchronic integrity, diachronic openness

This file records the open-ended reading of the weak process core without
adding a kernel mechanism.

The ordinary kernel is polymorphic in its entire plastic periphery.  It has
two equations: every successful periphery is installed and failure stutters.
An optional observer may append events, but erasing the observer recovers the
same process trace exactly.

Replacement of the complete rooted program is a distinct, slower transition.
Within one authority regime, an admission witness cannot be forged for a
rejected candidate.  Between regimes, the authority predicate itself may be
revised and a fresh witness may admit a formerly rejected candidate.  Thus the
model combines synchronic integrity with diachronic openness.  In particular,
ordinary processes preserve the current root while every externally approved
complete successor—including one designated quiescent—is reachable.
-/

namespace OpenEndedProcessCore

open WeakSelfHostingCore

/-! ## 1. The periphery-polymorphic two-equation kernel -/

structure State (Root Periphery : Type) where
  root : Root
  periphery : Periphery

def step {Root Periphery : Type} (state : State Root Periphery) :
    Outcome Periphery → State Root Periphery
  | .success next => { state with periphery := next }
  | .failure => state

abbrev Process (Periphery : Type) := Periphery → Outcome Periphery

def invoke {Root Periphery : Type} (state : State Root Periphery)
    (process : Process Periphery) : State Root Periphery :=
  step state (process state.periphery)

def run {Root Periphery : Type} :
    List (Outcome Periphery) → State Root Periphery → State Root Periphery
  | [], state => state
  | outcome :: rest, state => run rest (step state outcome)

theorem failed_process_stutters {Root Periphery : Type}
    (state : State Root Periphery) :
    step state (.failure : Outcome Periphery) = state := by
  rfl

theorem every_successful_periphery_is_reachable {Root Periphery : Type}
    (state : State Root Periphery) (target : Periphery) :
    step state (.success target) = { state with periphery := target } := by
  rfl

theorem step_preserves_root {Root Periphery : Type}
    (state : State Root Periphery) (outcome : Outcome Periphery) :
    (step state outcome).root = state.root := by
  cases outcome <;> rfl

theorem run_preserves_root {Root Periphery : Type}
    (outcomes : List (Outcome Periphery)) (state : State Root Periphery) :
    (run outcomes state).root = state.root := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome rest ih =>
      exact (ih (step state outcome)).trans (step_preserves_root state outcome)

/-- The core cannot distinguish the origin, goal, score, or implementation of
two processes that return the same outcome on the observed periphery. -/
theorem process_origin_is_erased {Root Periphery : Type}
    (state : State Root Periphery) (left right : Process Periphery)
    (same : left state.periphery = right state.periphery) :
    invoke state left = invoke state right := by
  simp only [invoke, same]

abbrev Runner (Root Periphery : Type) :=
  State Root Periphery → Outcome Periphery → State Root Periphery

def Contract {Root Periphery : Type}
    (runner : Runner Root Periphery) : Prop :=
  (∀ state target,
      runner state (.success target) = { state with periphery := target }) ∧
  (∀ state, runner state .failure = state)

theorem step_satisfies_contract {Root Periphery : Type} :
    Contract (@step Root Periphery) := by
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- Polymorphism in the periphery adds no semantic freedom to the kernel: the
two equations still determine the runner uniquely. -/
theorem step_is_unique_contract_runner {Root Periphery : Type}
    (runner : Runner Root Periphery) (contract : Contract runner) :
    runner = @step Root Periphery := by
  funext state outcome
  cases outcome with
  | success target => exact contract.1 state target
  | failure => exact contract.2 state

/-! ## 2. Open named-coordinate assemblages are an adapter -/

abbrev Assemblage (Name Value : Type) := Name → Value

def setCoordinate {Name Value : Type} [DecidableEq Name]
    (selected : Name) (value : Value) (before : Assemblage Name Value) :
    Assemblage Name Value :=
  fun name => if name = selected then value else before name

theorem set_coordinate_selected {Name Value : Type} [DecidableEq Name]
    (selected : Name) (value : Value) (before : Assemblage Name Value) :
    setCoordinate selected value before selected = value := by
  simp [setCoordinate]

theorem set_coordinate_preserves_others {Name Value : Type}
    [DecidableEq Name] (selected other : Name) (value : Value)
    (before : Assemblage Name Value) (different : other ≠ selected) :
    setCoordinate selected value before other = before other := by
  simp [setCoordinate, different]

def coordinateProcess {Name Value : Type} [DecidableEq Name]
    (selected : Name) (value : Value) : Process (Assemblage Name Value) :=
  fun before => .success (setCoordinate selected value before)

/-- A new policy or component is represented by a name and value.  Installing
it needs no new case in `step`. -/
theorem arbitrary_named_coordinate_is_installable {Root Name Value : Type}
    [DecidableEq Name] (state : State Root (Assemblage Name Value))
    (selected : Name) (value : Value) :
    (invoke state (coordinateProcess selected value)).periphery selected =
      value := by
  simp [invoke, coordinateProcess, step, setCoordinate]

theorem named_coordinate_update_preserves_others {Root Name Value : Type}
    [DecidableEq Name] (state : State Root (Assemblage Name Value))
    (selected other : Name) (value : Value) (different : other ≠ selected) :
    (invoke state (coordinateProcess selected value)).periphery other =
      state.periphery other := by
  simp [invoke, coordinateProcess, step, setCoordinate, different]

/-- Independent named coordinates commute.  Concurrency therefore belongs to
the assemblage adapter; the kernel needs neither a scheduler case nor a fixed
enumeration of policies. -/
theorem set_distinct_coordinates_commute {Name Value : Type}
    [DecidableEq Name] (left right : Name) (leftValue rightValue : Value)
    (before : Assemblage Name Value) (different : left ≠ right) :
    setCoordinate right rightValue
        (setCoordinate left leftValue before) =
      setCoordinate left leftValue
        (setCoordinate right rightValue before) := by
  funext name
  by_cases isLeft : name = left
  · subst name
    simp [setCoordinate, different]
  · by_cases isRight : name = right
    · subst name
      simp [setCoordinate, isLeft]
    · simp [setCoordinate, isLeft, isRight]

theorem distinct_coordinate_processes_commute {Root Name Value : Type}
    [DecidableEq Name] (state : State Root (Assemblage Name Value))
    (left right : Name) (leftValue rightValue : Value)
    (different : left ≠ right) :
    invoke (invoke state (coordinateProcess left leftValue))
        (coordinateProcess right rightValue) =
      invoke (invoke state (coordinateProcess right rightValue))
        (coordinateProcess left leftValue) := by
  cases state with
  | mk root periphery =>
      simp only [invoke, coordinateProcess, step]
      exact congrArg (State.mk root)
        (set_distinct_coordinates_commute left right leftValue rightValue
          periphery different)

/-- An attention or currently-selected-policy field is ordinary plastic data.
Changing it does not execute, authorize, or otherwise alter another field. -/
theorem selection_is_only_a_coordinate_update {Root Name Value : Type}
    [DecidableEq Name] (state : State Root (Assemblage Name Value))
    (selection other : Name) (selectedValue : Value)
    (different : other ≠ selection) :
    (invoke state (coordinateProcess selection selectedValue)).periphery other =
      state.periphery other := by
  exact named_coordinate_update_preserves_others state selection other
    selectedValue different

/-! ## 3. An append-only observer is conservative -/

structure Observed (Root Periphery Event : Type) where
  current : State Root Periphery
  history : List Event

def observeStep {Root Periphery Event : Type}
    (record : Outcome Periphery → Event)
    (observed : Observed Root Periphery Event)
    (outcome : Outcome Periphery) : Observed Root Periphery Event :=
  { current := step observed.current outcome
    history := observed.history ++ [record outcome] }

def observeRun {Root Periphery Event : Type}
    (record : Outcome Periphery → Event) :
    List (Outcome Periphery) → Observed Root Periphery Event →
      Observed Root Periphery Event
  | [], observed => observed
  | outcome :: rest, observed =>
      observeRun record rest (observeStep record observed outcome)

/-- Observation cannot alter the workspace transition. -/
theorem observe_step_erases_exactly {Root Periphery Event : Type}
    (record : Outcome Periphery → Event)
    (observed : Observed Root Periphery Event)
    (outcome : Outcome Periphery) :
    (observeStep record observed outcome).current =
      step observed.current outcome := by
  rfl

theorem observe_step_is_append_only {Root Periphery Event : Type}
    (record : Outcome Periphery → Event)
    (observed : Observed Root Periphery Event)
    (outcome : Outcome Periphery) :
    ∃ suffix,
      (observeStep record observed outcome).history =
        observed.history ++ suffix := by
  exact ⟨[record outcome], rfl⟩

theorem observe_run_erases_exactly {Root Periphery Event : Type}
    (record : Outcome Periphery → Event)
    (outcomes : List (Outcome Periphery))
    (observed : Observed Root Periphery Event) :
    (observeRun record outcomes observed).current =
      run outcomes observed.current := by
  induction outcomes generalizing observed with
  | nil => rfl
  | cons outcome rest ih =>
      exact ih (observeStep record observed outcome)

theorem observe_run_history {Root Periphery Event : Type}
    (record : Outcome Periphery → Event)
    (outcomes : List (Outcome Periphery))
    (observed : Observed Root Periphery Event) :
    (observeRun record outcomes observed).history =
      observed.history ++ outcomes.map record := by
  induction outcomes generalizing observed with
  | nil => simp [observeRun]
  | cons outcome rest ih =>
      simp only [observeRun, ih, observeStep, List.map_cons]
      simp [List.append_assoc]

/-! ## 4. Unforgeable admission within a revisable authority regime -/

structure Regime (Program : Type) where
  Approved : Program → Prop

/-- A value is admitted under one named authority predicate only by carrying
evidence for that predicate.  A runtime may represent this as an opaque typed
handle; Lean records its logical content. -/
structure Admitted (Program : Type) (Approved : Program → Prop) where
  program : Program
  evidence : Approved program

theorem rejected_candidate_has_no_admission {Program : Type}
    (Approved : Program → Prop) (candidate : Program)
    (rejected : ¬ Approved candidate) :
    ¬ ∃ admitted : Admitted Program Approved,
        admitted.program = candidate := by
  intro witness
  rcases witness with ⟨admitted, rfl⟩
  exact rejected admitted.evidence

/-- There is no authority-independent operation that relabels an admitted
program as admitted under every other predicate. -/
theorem no_universal_authority_relabeling {Program : Type}
    (program : Program) :
    ¬ Nonempty (∀ (old new : Program → Prop),
        Admitted Program old → Admitted Program new) := by
  intro relabel
  rcases relabel with ⟨relabel⟩
  let admitted : Admitted Program (fun _ => True) := ⟨program, True.intro⟩
  have impossible := relabel (fun _ => True) (fun _ => False) admitted
  exact impossible.evidence

/-- Revising the authority is allowed, but the new regime must supply its own
evidence.  Rejection by the old regime is not frozen into the kernel. -/
theorem authority_revision_can_admit_a_formerly_rejected_candidate
    {Program : Type} (old new : Regime Program) (candidate : Program)
    (oldRejects : ¬ old.Approved candidate)
    (newAccepts : new.Approved candidate) :
    (¬ ∃ admitted : Admitted Program old.Approved,
        admitted.program = candidate) ∧
      (∃ admitted : Admitted Program new.Approved,
        admitted.program = candidate) := by
  constructor
  · exact rejected_candidate_has_no_admission old.Approved candidate oldRejects
  · exact ⟨⟨candidate, newAccepts⟩, rfl⟩

/-! ## 5. Ordinary root stability and admitted whole-system becoming -/

abbrev SystemHost (Root Periphery : Type) :=
  Host (State Root Periphery)

def install {Program : Type} (Approved : Program → Prop)
    (host : Host Program) (admitted : Admitted Program Approved) :
    Host Program :=
  let staged := stage host admitted.program
  promote Approved staged admitted.program ⟨rfl, admitted.evidence⟩

theorem ordinary_processes_preserve_the_current_root {Root Periphery : Type}
    (state : State Root Periphery) (process : Process Periphery) :
    (invoke state process).root = state.root := by
  exact step_preserves_root state (process state.periphery)

/-- External promotion may revise even the root.  It is not frozen by the
ordinary process law. -/
theorem every_admitted_complete_successor_is_reachable {Root Periphery : Type}
    (Approved : State Root Periphery → Prop)
    (host : SystemHost Root Periphery)
    (admitted : Admitted (State Root Periphery) Approved) :
    (install Approved host admitted).live = admitted.program := by
  rfl

theorem every_admitted_root_revision_is_reachable {Root Periphery : Type}
    (Approved : State Root Periphery → Prop)
    (host : SystemHost Root Periphery)
    (admitted : Admitted (State Root Periphery) Approved) :
    (install Approved host admitted).live.root = admitted.program.root := by
  rfl

/-- `Quiescent` is intentionally arbitrary.  It may denote graceful
termination, permanent rest, handoff, or another chosen terminal form. -/
theorem every_admitted_quiescent_successor_is_reachable
    {Root Periphery : Type}
    (Approved Quiescent : State Root Periphery → Prop)
    (host : SystemHost Root Periphery)
    (admitted : Admitted (State Root Periphery) Approved)
    (quiescent : Quiescent admitted.program) :
    Quiescent (install Approved host admitted).live := by
  exact quiescent

theorem admitted_installation_keeps_recovery_coherent
    {Root Periphery : Type}
    (Approved : State Root Periphery → Prop)
    (host : SystemHost Root Periphery)
    (admitted : Admitted (State Root Periphery) Approved) :
    (install Approved host admitted).live =
      (install Approved host admitted).lastKnownGood := by
  rfl

/-! ## 6. The existing three-policy process is one specialization -/

def fromThreePolicy {Root : Type} (state : ThreePolicyFusion.Rooted Root) :
    State Root ThreePolicyFusion.Periphery :=
  ⟨state.root, state.periphery⟩

def toThreePolicy {Root : Type}
    (state : State Root ThreePolicyFusion.Periphery) :
    ThreePolicyFusion.Rooted Root :=
  ⟨state.root, state.periphery⟩

theorem step_specializes_to_existing_three_policy_core {Root : Type}
    (state : ThreePolicyFusion.Rooted Root)
    (outcome : Outcome ThreePolicyFusion.Periphery) :
    toThreePolicy (step (fromThreePolicy state) outcome) =
      ThreePolicyFusion.processStep state outcome := by
  cases outcome <;> rfl

theorem run_specializes_to_existing_three_policy_core {Root : Type}
    (outcomes : List (Outcome ThreePolicyFusion.Periphery))
    (state : ThreePolicyFusion.Rooted Root) :
    toThreePolicy (run outcomes (fromThreePolicy state)) =
      ThreePolicyFusion.processRun outcomes state := by
  induction outcomes generalizing state with
  | nil => rfl
  | cons outcome rest ih =>
      calc
        toThreePolicy (run (outcome :: rest) (fromThreePolicy state)) =
            toThreePolicy
              (run rest (step (fromThreePolicy state) outcome)) := rfl
        _ = toThreePolicy
              (run rest
                (fromThreePolicy
                  (ThreePolicyFusion.processStep state outcome))) := by
              cases outcome <;> rfl
        _ = ThreePolicyFusion.processRun rest
              (ThreePolicyFusion.processStep state outcome) :=
            ih (ThreePolicyFusion.processStep state outcome)
        _ = ThreePolicyFusion.processRun (outcome :: rest) state := rfl

end OpenEndedProcessCore

/-! ## Axiom audit -/

#print axioms OpenEndedProcessCore.step_is_unique_contract_runner
#print axioms OpenEndedProcessCore.arbitrary_named_coordinate_is_installable
#print axioms OpenEndedProcessCore.set_distinct_coordinates_commute
#print axioms OpenEndedProcessCore.distinct_coordinate_processes_commute
#print axioms OpenEndedProcessCore.observe_run_erases_exactly
#print axioms OpenEndedProcessCore.observe_run_history
#print axioms OpenEndedProcessCore.no_universal_authority_relabeling
#print axioms OpenEndedProcessCore.authority_revision_can_admit_a_formerly_rejected_candidate
#print axioms OpenEndedProcessCore.every_admitted_root_revision_is_reachable
#print axioms OpenEndedProcessCore.every_admitted_quiescent_successor_is_reachable
#print axioms OpenEndedProcessCore.run_specializes_to_existing_three_policy_core

import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.ExecutionSpace

/-!
# Live stack storage of sequential machine composition

The original sequential machine uses disjoint stack arenas and transfers each
intermediate symbol through a temporary stack. That transfer moves cells; it
does not keep a second copy of the word. This file accounts for transition-state
storage along the actual executions. Intra-command and native allocator peaks
are separate measures.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineCompositionSpace

open Turing StateTransition ExecutionSpace StackMachineComposition
open scoped BigOperators

attribute [local implicit_reducible] StackMachineComposition.machine

/-- A step-preserving embedding with the same footprint preserves peak storage
along every finite path ending at a live configuration. Its behavior after
that endpoint is irrelevant. -/
theorem peak_embedding {Source Target : Type}
    (source : Source → Option Source) (target : Target → Option Target)
    (embed : Source → Target) (sourceSize : Source → Nat) (targetSize : Target → Nat)
    (steps : ∀ before after, source before = some after →
      target (embed before) = some (embed after))
    (sizes : ∀ state, targetSize (embed state) = sourceSize state)
    (count : Nat) (before after : Source)
    (run : (fun state : Option Source => state.bind source)^[count] (some before) = some after) :
    peak target targetSize count (some (embed before)) =
      peak source sourceSize count (some before) := by
  induction count generalizing before with
  | zero => simp [peak, footprint, sizes]
  | succ count ih =>
      rw [Function.iterate_succ_apply] at run
      cases next : source before with
      | none =>
          simp only [Option.bind_some, next, iterate_bind_none] at run
          contradiction
      | some middle =>
          simp only [Option.bind_some, next] at run
          rw [peak, peak]
          simp only [footprint, Option.elim_some, sizes, Option.bind_some, next,
            steps before middle next]
          rw [ih middle run]

variable (first second : FinTM2)
local instance : Fintype first.K := first.kFin
local instance : Fintype second.K := second.kFin
variable [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
variable (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)

theorem first_cells (state : first.Cfg) :
    stackCells (machine first second bridge) (firstConfig first second bridge state) =
      stackCells first state := by
  change (∑ key : Option (first.K ⊕ second.K), (firstStacks first second state.stk key).length) = _
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp [firstStacks, stackCells]

theorem second_cells (state : second.Cfg) :
    stackCells (machine first second bridge) (secondConfig first second bridge state) =
      stackCells second state := by
  change (∑ key : Option (first.K ⊕ second.K), (secondStacks first second state.stk key).length) = _
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp [secondStacks, stackCells]

theorem transfer_cells (phase : Option Bool) (symbol : Option (first.Γ first.k₁))
    (input temporary : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀)) :
    stackCells (machine first second bridge)
      (transferConfig first second bridge phase symbol input temporary output) =
        input.length + temporary.length + output.length := by
  change (∑ key : Option (first.K ⊕ second.K),
    ((transferConfig first second bridge phase symbol input temporary output).stk key).length) = _
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  have singleton {Keys : Type} [Fintype Keys] [DecidableEq Keys]
      (Cells : Keys → Type) (key : Keys) (word : List (Cells key)) :
      (∑ slot, (if same : slot = key then same.symm ▸ word else []).length) = word.length := by
    classical
    rw [Finset.sum_eq_single key]
    · simp
    · intro other _ different
      simp [different]
    · simp
  simp only [transferConfig]
  rw [singleton first.Γ first.k₁ input, singleton second.Γ second.k₀ output]
  omega

theorem first_peak {before after : first.Cfg} {time : Nat}
    (run : EvalsToInTime first.step before (some after) time) :
    peak (machine first second bridge).step (stackCells (machine first second bridge))
      run.steps (some (firstConfig first second bridge before)) =
        peak first.step (stackCells first) run.steps (some before) := by
  apply peak_embedding first.step _ (firstConfig first second bridge) _ _ _
    (first_cells first second bridge) run.steps before after run.evals_in_steps
  intro state next ran
  cases active : state.l with
  | none =>
      cases state with
      | mk label registers contents =>
          dsimp at active
          subst label
          simp [FinTM2.step, TM2.step] at ran
  | some label => rw [first_step first second bridge state label active, ran]; rfl

theorem second_peak {before after : second.Cfg} {time : Nat}
    (run : EvalsToInTime second.step before (some after) time) :
    peak (machine first second bridge).step (stackCells (machine first second bridge))
      run.steps (some (secondConfig first second bridge before)) =
        peak second.step (stackCells second) run.steps (some before) := by
  apply peak_embedding second.step _ (secondConfig first second bridge) _ _ _
    (second_cells first second bridge) run.steps before after run.evals_in_steps
  intro state next ran
  rw [second_step first second bridge state, ran]
  rfl

theorem scan_peak (word temporary : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) (symbol : Option (first.Γ first.k₁)) :
    peak (machine first second bridge).step (stackCells (machine first second bridge))
      (word.length + 1)
      (some (transferConfig first second bridge (some false) symbol word temporary output)) =
        word.length + temporary.length + output.length := by
  induction word generalizing temporary symbol with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, peak, footprint, Option.elim_some,
        Option.bind_some, scan_nil, transfer_cells, Nat.zero_add, max_self]
  | cons head tail ih =>
      rw [List.length_cons, Nat.add_assoc, Nat.add_comm 1 1, ← Nat.add_assoc]
      rw [peak]
      simp only [footprint, Option.elim_some, Option.bind_some, scan_cons, transfer_cells,
        List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem restore_peak (temporary input : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) (symbol : Option (first.Γ first.k₁)) :
    peak (machine first second bridge).step (stackCells (machine first second bridge))
      (temporary.length + 1)
      (some (transferConfig first second bridge (some true) symbol input temporary output)) =
        input.length + temporary.length + output.length := by
  induction temporary generalizing output symbol with
  | nil =>
      simp only [List.length_nil, peak, footprint, Option.elim_some,
        Option.bind_some, restore_nil, transfer_cells, Nat.add_zero, max_self]
  | cons head tail ih =>
      rw [List.length_cons, peak]
      simp only [footprint, Option.elim_some, Option.bind_some, restore_cons, transfer_cells,
        List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem scan_iteration (word temporary : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) (symbol : Option (first.Γ first.k₁)) :
    (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[word.length + 1]
      (some (transferConfig first second bridge (some false) symbol word temporary output)) =
        some (transferConfig first second bridge (some true) none [] (word.reverse ++ temporary) output) := by
  induction word generalizing temporary symbol with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        Option.bind_some, List.reverse_nil, List.nil_append] using
          scan_nil first second bridge symbol temporary output
  | cons head tail ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, scan_cons]
      simpa using ih (head :: temporary) (some head)

/-- Both physical passes keep exactly the intermediate word's cell count.
There is no overlap of two complete copies during the handoff. -/
theorem transfer_peak (word : List (first.Γ first.k₁)) :
    peak (machine first second bridge).step (stackCells (machine first second bridge))
      (2 * word.length + 2)
      (some (firstConfig first second bridge (haltList first word))) = word.length := by
  rw [first_halt_eq]
  have time : 2 * word.length + 2 = (word.length + 1) + (word.length + 1) := by omega
  rw [time, peak_add]
  have boundary := scan_iteration first second bridge word [] [] none
  rw [boundary, scan_peak]
  simp only [List.append_nil, List.length_nil, Nat.add_zero]
  have restored := restore_peak first second bridge word.reverse [] [] none
  simpa only [List.length_reverse, List.length_nil, Nat.zero_add, Nat.add_zero, max_self] using
    congrArg (max word.length) restored

theorem restore_iteration (temporary input : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) (symbol : Option (first.Γ first.k₁)) :
    (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[temporary.length + 1]
      (some (transferConfig first second bridge (some true) symbol input temporary output)) =
        some (transferConfig first second bridge none none input [] (temporary.reverse.map bridge ++ output)) := by
  induction temporary generalizing output symbol with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append] using
          restore_nil first second bridge symbol input output
  | cons head tail ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [Option.bind_some, restore_cons]
      simpa using ih (bridge head :: output) (some head)

/-- The transfer count is exact, including both empty-stack transitions. -/
def transferExact (word : List (first.Γ first.k₁)) :
    EvalsToInTime (machine first second bridge).step
      (firstConfig first second bridge (haltList first word))
      (some (secondConfig first second bridge (initList second (word.map bridge))))
      (2 * word.length + 2) where
  steps := 2 * word.length + 2
  evals_in_steps := by
    rw [first_halt_eq]
    have time : 2 * word.length + 2 = (word.length + 1) + (word.length + 1) := by omega
    change (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[2 * word.length + 2] _ = _
    rw [time, Function.iterate_add_apply, scan_iteration]
    simp only [List.append_nil]
    have restored := restore_iteration first second bridge word.reverse [] [] none
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at restored
    rw [restored, second_init_eq]
  steps_le_m := le_rfl

theorem first_iteration {before after : first.Cfg} {time : Nat}
    (run : EvalsToInTime first.step before (some after) time) :
    (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[run.steps]
      (some (firstConfig first second bridge before)) =
        some (firstConfig first second bridge after) :=
  (first_execution first second bridge run).evals_in_steps

theorem second_iteration {before after : second.Cfg} {time : Nat}
    (run : EvalsToInTime second.step before (some after) time) :
    (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[run.steps]
      (some (secondConfig first second bridge before)) =
        some (secondConfig first second bridge after) :=
  (second_execution first second bridge run).evals_in_steps

theorem transfer_iteration (word : List (first.Γ first.k₁)) :
    (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[2 * word.length + 2]
      (some (firstConfig first second bridge (haltList first word))) =
        some (secondConfig first second bridge (initList second (word.map bridge))) :=
  (transferExact first second bridge word).evals_in_steps

/-- The same original composition, with an explicit count for its physical
handoff. Only the execution witness is assembled here; the program is reused. -/
def joinedOutputs {input : List (first.Γ first.k₀)} {middle : List (first.Γ first.k₁)}
    {output : List (second.Γ second.k₁)} {firstTime secondTime : Nat}
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    (secondRun : TM2OutputsInTime second (middle.map bridge) (some output) secondTime) :
    TM2OutputsInTime (machine first second bridge) input (some output)
      (firstTime + 2 * middle.length + 2 + secondTime) where
  steps := firstRun.steps + (2 * middle.length + 2) + secondRun.steps
  evals_in_steps := by
    change (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[firstRun.steps + (2 * middle.length + 2) + secondRun.steps] _ = _
    rw [Nat.add_comm (firstRun.steps + _) secondRun.steps, Function.iterate_add_apply,
      Nat.add_comm firstRun.steps _, Function.iterate_add_apply, init_eq]
    rw [first_iteration first second bridge firstRun, transfer_iteration,
      second_iteration first second bridge secondRun, second_halt_eq]
    rfl
  steps_le_m := by have := firstRun.steps_le_m; have := secondRun.steps_le_m; omega

/-- Actual transition-state peak storage of sequential composition is the
maximum of the component peaks. The cleaned arenas and move-only handoff
are essential to this equation. -/
theorem joined_peak {input : List (first.Γ first.k₀)} {middle : List (first.Γ first.k₁)}
    {output : List (second.Γ second.k₁)} {firstTime secondTime : Nat}
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    (secondRun : TM2OutputsInTime second (middle.map bridge) (some output) secondTime) :
    runPeak (machine first second bridge) (joinedOutputs first second bridge firstRun secondRun) =
      max (runPeak first firstRun) (runPeak second secondRun) := by
  change peak _ _ (firstRun.steps + (2 * middle.length + 2) + secondRun.steps) _ = _
  rw [init_eq, peak_add]
  have firstBoundary := first_iteration first second bridge firstRun
  have transferBoundary := transfer_iteration first second bridge middle
  have boundary :
      (fun state : Option (machine first second bridge).Cfg => state.bind (machine first second bridge).step)^[firstRun.steps + (2 * middle.length + 2)]
        (some (firstConfig first second bridge (initList first input))) =
          some (secondConfig first second bridge (initList second (middle.map bridge))) := by
    rw [Nat.add_comm, Function.iterate_add_apply, firstBoundary, transferBoundary]
  rw [boundary, peak_add, firstBoundary, first_peak first second bridge firstRun,
    transfer_peak, second_peak first second bridge secondRun]
  change max (max (runPeak first firstRun) middle.length) (runPeak second secondRun) = _
  rw [max_eq_left (output_length_le_runPeak first firstRun)]

end Mettapedia.Computability.StackMachineCompositionSpace

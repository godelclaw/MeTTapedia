import WeakAgentEcology

/-!
# PolicyPipeline — presets are data over an open process registry

The weak process runner already supplies the complete stable semantics:
successful processes replace the periphery and failed processes stutter.  This
module adds no new runner rule.  It gives the replaceable surround a compact
way to name and compose behavior:

* a registry maps arbitrary names to processes;
* a preset is an ordered list of those names; and
* running a preset means compiling the names and using the existing runner.

No fixed enumeration of cadence, context, controller, tool, completion, or
memory roles appears here.  Such roles are ordinary registry entries.  This is
weak enough to host Iter transformations, living-agent processes, coding-agent
stages, or mixtures of them without changing the kernel or this type.
-/

namespace PolicyPipeline

open WeakSelfHostingCore
open WeakAgentEcology

/-- An open association from names to replaceable processes. -/
abbrev Registry (Name Periphery : Type) := Name → Process Periphery

/-- A dynamically populated registry may reject an unknown name explicitly. -/
abbrev PartialRegistry (Name Periphery : Type) :=
  Name → Option (Process Periphery)

/-- A policy preset is data: an ordered list of process names. -/
structure Preset (Name : Type) where
  stages : List Name
deriving Repr, DecidableEq

/-- Resolve a preset against the current registry. -/
def compile {Name Periphery : Type}
    (registry : Registry Name Periphery) (preset : Preset Name) :
    List (Process Periphery) :=
  preset.stages.map registry

/-- Resolve a preset against a partial registry, failing on the first unknown
stage instead of silently installing a default process. -/
def compileChecked {Name Periphery : Type}
    (registry : PartialRegistry Name Periphery) (preset : Preset Name) :
    Option (List (Process Periphery)) :=
  preset.stages.mapM registry

/-- Execute a compiled preset using the unchanged weak process runner. -/
def run {Root Name Periphery : Type}
    (registry : Registry Name Periphery) (preset : Preset Name)
    (state : Rooted Root Periphery) : Rooted Root Periphery :=
  runProcesses (compile registry preset) state

def runChecked {Root Name Periphery : Type}
    (registry : PartialRegistry Name Periphery) (preset : Preset Name)
    (state : Rooted Root Periphery) : Option (Rooted Root Periphery) :=
  (compileChecked registry preset).map (fun processes =>
    runProcesses processes state)

theorem unknown_singleton_is_rejected {Name Periphery : Type}
    (registry : PartialRegistry Name Periphery) (selected : Name)
    (unknown : registry selected = none) :
    compileChecked registry ⟨[selected]⟩ = none := by
  simp [compileChecked, unknown]

theorem checked_success_uses_the_same_runner {Root Name Periphery : Type}
    (registry : PartialRegistry Name Periphery) (preset : Preset Name)
    (state : Rooted Root Periphery) (processes : List (Process Periphery))
    (resolved : compileChecked registry preset = some processes) :
    runChecked registry preset state = some (runProcesses processes state) := by
  simp [runChecked, resolved]

/-- Preset composition is ordinary list concatenation. -/
def append {Name : Type} (left right : Preset Name) : Preset Name :=
  ⟨left.stages ++ right.stages⟩

theorem compile_append {Name Periphery : Type}
    (registry : Registry Name Periphery) (left right : Preset Name) :
    compile registry (append left right) =
      compile registry left ++ compile registry right := by
  simp [compile, append]

/-- Running a composite preset is exactly sequential execution of its parts. -/
theorem run_append {Root Name Periphery : Type}
    (registry : Registry Name Periphery) (left right : Preset Name)
    (state : Rooted Root Periphery) :
    run registry (append left right) state =
      run registry right (run registry left state) := by
  simp [run, compile_append, runProcesses_append]

/-- Every preset preserves the stable root, independently of its stage names. -/
theorem run_preserves_root {Root Name Periphery : Type}
    (registry : Registry Name Periphery) (preset : Preset Name)
    (state : Rooted Root Periphery) :
    (run registry preset state).root = state.root := by
  exact runProcesses_preserves_root (compile registry preset) state

/-- A failed named stage is a local stutter and may be erased from the preset. -/
theorem failed_named_stage_erases
    {Root Name Periphery : Type}
    (registry : Registry Name Periphery) (failed : Name)
    (left right : List Name) (state : Rooted Root Periphery)
    (isFailure : registry failed = (failingProcess : Process Periphery)) :
    run registry ⟨left ++ failed :: right⟩ state =
      run registry ⟨left ++ right⟩ state := by
  simp only [run, compile, List.map_append, List.map_cons, isFailure]
  exact failed_process_erases_from_trace
    (left.map registry) (right.map registry) state

/-- Replace one registry entry without changing the preset representation. -/
def install {Name Periphery : Type} [DecidableEq Name]
    (registry : Registry Name Periphery) (selected : Name)
    (replacement : Process Periphery) : Registry Name Periphery :=
  fun name => if name = selected then replacement else registry name

theorem installed_stage_is_selected
    {Name Periphery : Type} [DecidableEq Name]
    (registry : Registry Name Periphery) (selected : Name)
    (replacement : Process Periphery) :
    install registry selected replacement selected = replacement := by
  simp [install]

/-- Installing one stage leaves every differently named stage unchanged. -/
theorem stage_replacement_is_local
    {Name Periphery : Type} [DecidableEq Name]
    (registry : Registry Name Periphery) (selected other : Name)
    (replacement : Process Periphery) (different : other ≠ selected) :
    install registry selected replacement other = registry other := by
  simp [install, different]

/-- The representation imposes no closed catalogue: every process list is a
preset when processes themselves are used as names. -/
theorem every_process_pipeline_is_a_preset {Periphery : Type}
    (processes : List (Process Periphery)) :
    compile (fun process => process) (⟨processes⟩ : Preset (Process Periphery)) =
      processes := by
  simp [compile]

/-! ## Exact Iter embedding through the same preset interface -/

def fromIterRegistry :
    Registry IterArchitecture.Transformation IterArchitecture.Boundary :=
  WeakAgentEcology.fromIter

def iterPreset (transformations : List IterArchitecture.Transformation) :
    Preset IterArchitecture.Transformation :=
  ⟨transformations⟩

/-- A preset made from Patrick Iter transformations produces exactly the
reference Iter fold.  Iter is therefore hosted, not approximated by a special
kernel case. -/
theorem iter_preset_is_exact {Root : Type}
    (root : Root) (boundary : IterArchitecture.Boundary)
    (transformations : List IterArchitecture.Transformation) :
    (run fromIterRegistry (iterPreset transformations)
      ({ root := root, periphery := boundary } :
        Rooted Root IterArchitecture.Boundary)).periphery =
      IterArchitecture.applyTransformations transformations boundary := by
  exact WeakAgentEcology.iter_pipeline_is_exact root boundary transformations

/-! ## Ordering remains expressive policy -/

inductive DemoStage
  | increment
  | double
deriving Repr, DecidableEq

def demoRegistry : Registry DemoStage Nat
  | .increment => hostChange (fun value => value + 1)
  | .double => hostChange (fun value => value * 2)

theorem preset_order_is_observable :
    run demoRegistry ⟨[.increment, .double]⟩
        ({ root := (), periphery := 1 } : Rooted Unit Nat) ≠
      run demoRegistry ⟨[.double, .increment]⟩
        ({ root := (), periphery := 1 } : Rooted Unit Nat) := by
  simp [run, compile, demoRegistry, runProcesses, hostChange,
    OpenEndedProcessCore.invoke, OpenEndedProcessCore.step]

/-- No new minimality claim is needed: the preset compiler delegates to the
unique runner satisfying success replacement and failure stutter. -/
theorem runner_beneath_presets_is_unique
    {Root Periphery : Type}
    (runner : OpenEndedProcessCore.Runner Root Periphery)
    (contract : OpenEndedProcessCore.Contract runner) :
    runner = @OpenEndedProcessCore.step Root Periphery :=
  weak_runner_is_unique runner contract

end PolicyPipeline

/-! ## Axiom audit -/

#print axioms PolicyPipeline.run_append
#print axioms PolicyPipeline.unknown_singleton_is_rejected
#print axioms PolicyPipeline.checked_success_uses_the_same_runner
#print axioms PolicyPipeline.run_preserves_root
#print axioms PolicyPipeline.failed_named_stage_erases
#print axioms PolicyPipeline.stage_replacement_is_local
#print axioms PolicyPipeline.every_process_pipeline_is_a_preset
#print axioms PolicyPipeline.iter_preset_is_exact
#print axioms PolicyPipeline.preset_order_is_observable
#print axioms PolicyPipeline.runner_beneath_presets_is_unique

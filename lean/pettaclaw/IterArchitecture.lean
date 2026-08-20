import ClawArchitectures
import PresentMoment

/-!
# IterArchitecture — the current reference loop and the PettaClaw hosting gap

An executable model of the architectural core in `patham9/iter` at upstream
commit `f6f2d1e137c179cbe951defd543527c43cb97da0` (2026-08-20), compared
with the deployed PettaClaw model in `ClawArchitectures.lean` and the
restart invariant in `PresentMoment.lean`.

The model deliberately stays below Python and below any proposed rho
encoding.  It records what the reference loop actually does:

* transformations form a lexicographically ordered, failure-transactional
  fold over the LLM message/tool boundary;
* the advertised tool schemas and the executable tool snapshot are different
  objects;
* a tool written during a response becomes available after the next reload,
  not to later calls in the same response;
* every channel event has the same pacing effect, independent of origin;
* `nop` enters a timed slow wait and then starts a new autonomous burst;
* persistence saves experience but not the control state of the burst; and
* the automatic memory surface contains paths, not file contents.

The final feature record is only a necessary compatibility check.  Passing it
would not by itself prove that an adapted Iter implements PettaClaw.

Trusted boundary: correspondence between these definitions and `iter.py` is
maintained by hand, as is the existing PettaClaw model-to-code boundary.
At the pinned commit, the invalid no-tool response branch reads an undefined
`llm_result` name.  The model records the intended valid tool-calling path; it
does not turn that implementation defect into architectural semantics.
-/

namespace IterArchitecture

/-! ## Ordered, failure-transactional transformations -/

/-- The portion of an LLM request that transformations may replace.  Natural
numbers stand for opaque messages and tool-schema identities. -/
structure Boundary where
  messages : List Nat
  advertised : List Nat
deriving Repr, DecidableEq

/-- `none` models an exception, timeout, or unserializable result. -/
abbrev Transformation := Boundary → Option Boundary

/-- The reference loop keeps the old boundary when one transformation fails. -/
def applyTransformation (boundary : Boundary)
    (transformation : Transformation) : Boundary :=
  match transformation boundary with
  | some next => next
  | none => boundary

/-- Transformations run sequentially in their sorted-file order. -/
def applyTransformations : List Transformation → Boundary → Boundary
  | [], boundary => boundary
  | transformation :: rest, boundary =>
      applyTransformations rest (applyTransformation boundary transformation)

theorem failed_transformation_is_transactional (boundary : Boundary) :
    applyTransformation boundary (fun _ => none) = boundary := rfl

/-- Concatenating two transformation directories means running the first fold,
then the second fold. -/
theorem applyTransformations_append (left right : List Transformation)
    (boundary : Boundary) :
    applyTransformations (left ++ right) boundary =
      applyTransformations right (applyTransformations left boundary) := by
  induction left generalizing boundary with
  | nil => rfl
  | cons transformation rest ih =>
      simp only [List.cons_append, applyTransformations]
      exact ih (applyTransformation boundary transformation)

def appendMessage (message : Nat) : Transformation := fun boundary =>
  some { boundary with messages := boundary.messages ++ [message] }

def clearMessages : Transformation := fun boundary =>
  some { boundary with messages := [] }

def emptyBoundary : Boundary := ⟨[], []⟩

/-- Alphabetical order is semantic, not cosmetic: two valid transforms need
not commute. -/
theorem transformation_order_observable :
    applyTransformations [appendMessage 7, clearMessages] emptyBoundary ≠
      applyTransformations [clearMessages, appendMessage 7] emptyBoundary := by
  decide

/-! ## Advertisement is not authority -/

def maxTools : Nat := 30

/-- The reference loop loads only the first thirty sorted tool files. -/
def loadBounded (tools : List Nat) : List Nat := tools.take maxTools

theorem thirty_first_sorted_tool_is_omitted :
    30 ∉ loadBounded (List.range 31) := by
  decide

/-! ## The automatic memory surface is a path index -/

structure MemoryArtifact where
  name : Nat
  content : List Nat
deriving Repr, DecidableEq

/-- The current request builder enumerates memory paths.  Reading and
selecting their contents is delegated to tools or transformations. -/
def memoryListing (artifacts : List MemoryArtifact) : List Nat :=
  artifacts.map MemoryArtifact.name

/-- Two materially different memories can therefore have the same automatic
request surface.  This is not a defect in the weak loop; it identifies the
replaceable context-policy work that a hosted agent must supply. -/
theorem memory_contents_are_not_automatically_visible :
    let left : List MemoryArtifact := [⟨7, [1]⟩]
    let right : List MemoryArtifact := [⟨7, [2]⟩]
    left ≠ right ∧ memoryListing left = memoryListing right := by
  decide

/-- `loaded` is the `INOPS` snapshot used for dispatch; `advertised` is the
possibly transformed schema list sent to the model. -/
structure Catalog where
  loaded : List Nat
  advertised : List Nat
deriving Repr, DecidableEq

def executable (catalog : Catalog) (tool : Nat) : Prop :=
  tool ∈ catalog.loaded

def hide (catalog : Catalog) (tool : Nat) : Catalog :=
  { catalog with advertised := catalog.advertised.filter (fun item => item ≠ tool) }

def advertise (catalog : Catalog) (tool : Nat) : Catalog :=
  { catalog with advertised := tool :: catalog.advertised }

/-- A transformation that hides a schema does not revoke the corresponding
loaded implementation: dispatch still consults `INOPS`. -/
theorem hiding_does_not_revoke (catalog : Catalog) (hidden queried : Nat) :
    executable (hide catalog hidden) queried ↔ executable catalog queried := by
  rfl

theorem hidden_tool_remains_executable :
    let catalog : Catalog := ⟨[7], [7]⟩
    7 ∉ (hide catalog 7).advertised ∧ executable (hide catalog 7) 7 := by
  simp [hide, executable]

/-- Conversely, a transformation can advertise a schema that has no loaded
implementation; the ensuing call is rejected as unknown. -/
theorem advertised_schema_is_not_implementation :
    let catalog : Catalog := ⟨[], []⟩
    7 ∈ (advertise catalog 7).advertised ∧
      ¬ executable (advertise catalog 7) 7 := by
  simp [advertise, executable]

/-! ## Hot reload has a one-model-cycle boundary -/

/-- `disk` is the current tool directory; `loaded` is the request-local
dispatch snapshot. -/
structure ProgramStore where
  disk : List Nat
  loaded : List Nat
deriving Repr, DecidableEq

def install (store : ProgramStore) (tool : Nat) : ProgramStore :=
  { store with disk := tool :: store.disk }

def reload (store : ProgramStore) : ProgramStore :=
  { store with loaded := store.disk }

def emptyStore : ProgramStore := ⟨[], []⟩

/-- Installing through a tool call does not mutate the dispatch snapshot held
by the response currently being executed. -/
theorem installed_tool_not_live_in_same_response :
    7 ∉ (install emptyStore 7).loaded := by
  decide

/-- The next load observes the newly written implementation. -/
theorem installed_tool_live_after_reload :
    7 ∈ (reload (install emptyStore 7)).loaded := by
  decide

/-! ## Burst pacing and origin blindness -/

def maxFastSteps : Nat := 50

inductive Origin
  | human
  | sibling
  | service
deriving Repr, DecidableEq

inductive PromptKind
  | external
  | selectTask
  | autonomous
  | continueTask
deriving Repr, DecidableEq

inductive WaitKind
  | fast
  | slow
deriving Repr, DecidableEq

/-- Exact control fields from the reference loop, modulo the pending event string. -/
structure Pace where
  autonomousSteps : Nat
  newBurst : Bool
  postTaskMode : Bool
deriving Repr, DecidableEq

def bootPace : Pace := ⟨0, true, false⟩

/-- Beginning a cycle.  `Origin` is intentionally erased to presence: the
reference loop has no human/sibling distinction at this layer. -/
def beginCycle (pace : Pace) : Option Origin → Pace × PromptKind
  | some _ => (⟨0, false, false⟩, .external)
  | none =>
      if pace.newBurst then
        (⟨pace.autonomousSteps, false, true⟩, .selectTask)
      else if pace.postTaskMode then (pace, .autonomous)
      else (pace, .continueTask)

/-- End one valid tool-calling model turn.  The reference loop tests only the last tool
name for `nop`; `lastWasNop` records that exact rule. -/
def finishCycle (pace : Pace) (hadEvent lastWasNop : Bool) :
    Pace × WaitKind :=
  let used := if hadEvent then 0 else pace.autonomousSteps + 1
  if lastWasNop || decide (maxFastSteps ≤ used) then
    ({ pace with autonomousSteps := 0, newBurst := true }, .slow)
  else ({ pace with autonomousSteps := used }, .fast)

/-- Human, sibling-agent, and service events are observationally identical to
the pacing core. -/
theorem event_origins_indistinguishable (pace : Pace) (left right : Origin) :
    beginCycle pace (some left) = beginCycle pace (some right) := by
  rfl

theorem every_event_resets_fast_counter (pace : Pace) (origin : Origin) :
    (beginCycle pace (some origin)).1.autonomousSteps = 0 := rfl

/-- `nop` is a yield until the slow poll ends.  If no event arrives, the next
cycle explicitly asks the model to select a new autonomous task. -/
theorem nop_is_not_stable_rest (pace : Pace) :
    (finishCycle pace false true).2 = .slow ∧
      (beginCycle (finishCycle pace false true).1 none).2 = .selectTask := by
  simp [finishCycle, beginCycle]

/-- PettaClaw distinguishes a human arm from a sibling/service wake; Iter's
pacing core does not. -/
theorem pettaclaw_is_origin_sensitive :
    (Claws.wakeMax 60 ⟨5, 0⟩ (.human 10)).1 ≠
      (Claws.wake 60 ⟨5, 0⟩ .work).1 := by
  decide

/-- PettaClaw rest really zeroes the current burst. -/
theorem pettaclaw_rest_zeroes_current_burst :
    (Claws.wake 60 ⟨5, 0⟩ .rest).1.energy = 0 := by
  decide

/-! ## Restart persistence -/

/-- Process-local control plus persisted experience. -/
structure Runtime where
  experience : List Nat
  pace : Pace
  pending : Option Origin
deriving Repr, DecidableEq

/-- The reference loop's durable file contains experience, not pacing or pending input. -/
structure Disk where
  experience : List Nat
deriving Repr, DecidableEq

def persist (runtime : Runtime) : Disk := ⟨runtime.experience⟩

def restore (disk : Disk) : Runtime :=
  ⟨disk.experience, bootPace, none⟩

def restart (runtime : Runtime) : Runtime := restore (persist runtime)

theorem experience_survives_restart (runtime : Runtime) :
    (restart runtime).experience = runtime.experience := rfl

/-- The process boundary is not transparent on control state. -/
theorem restart_breaks_control_continuity :
    ∃ runtime : Runtime, restart runtime ≠ runtime := by
  refine ⟨⟨[1], ⟨7, false, false⟩, some .human⟩, ?_⟩
  decide

/-- With no fresh input, every restart injects the reference loop's "task completed;
select a task" prompt, even if the interrupted control state said otherwise. -/
theorem restart_selects_new_task_without_input (runtime : Runtime) :
    (beginCycle (restart runtime).pace none).2 = .selectTask := rfl

/-- In contrast, the repaired PettaClaw boundary is transparent throughout
its declared persistable window. -/
theorem pettaclaw_healthy_restart_preserves_present_moment
    (working : PresentMoment.Working)
    (within : working.lastResults.length ≤ PresentMoment.cap) :
    PresentMoment.resetH working = working :=
  PresentMoment.continuity working within

/-! ## Necessary feature check for hosting the deployed PettaClaw core -/

structure HostFeatures where
  originSensitiveArming : Bool
  agentChosenRest : Bool
  restartControlContinuity : Bool
  policyRevokesExecution : Bool
  requiredToolSurface : Bool
deriving Repr, DecidableEq

def meetsPettaCoreRequirements (features : HostFeatures) : Prop :=
  features.originSensitiveArming = true ∧
  features.agentChosenRest = true ∧
  features.restartControlContinuity = true ∧
  features.policyRevokesExecution = true ∧
  features.requiredToolSurface = true

/-- Capabilities of the unmodified reference loop, justified by the concrete results
above. -/
def iterReferenceFeatures : HostFeatures := ⟨false, false, false, false, false⟩

/-- The reference loop can carry an agent identity and call tools, but it is not a
drop-in host for the deployed PettaClaw life core. -/
theorem iter_reference_is_not_drop_in_pettaclaw_host :
    ¬ meetsPettaCoreRequirements iterReferenceFeatures := by
  simp [meetsPettaCoreRequirements, iterReferenceFeatures]

/-- A feature-level target for an adapter layer.  This theorem is intentionally
not named sufficiency: transport, memory, and model-to-code conformance remain
separate obligations. -/
def adaptedTargetFeatures : HostFeatures := ⟨true, true, true, true, true⟩

theorem adapted_target_passes_necessary_check :
    meetsPettaCoreRequirements adaptedTargetFeatures := by
  simp [meetsPettaCoreRequirements, adaptedTargetFeatures]

end IterArchitecture

/-! ## Axiom audit -/
#print axioms IterArchitecture.failed_transformation_is_transactional
#print axioms IterArchitecture.applyTransformations_append
#print axioms IterArchitecture.transformation_order_observable
#print axioms IterArchitecture.thirty_first_sorted_tool_is_omitted
#print axioms IterArchitecture.memory_contents_are_not_automatically_visible
#print axioms IterArchitecture.hiding_does_not_revoke
#print axioms IterArchitecture.hidden_tool_remains_executable
#print axioms IterArchitecture.advertised_schema_is_not_implementation
#print axioms IterArchitecture.installed_tool_not_live_in_same_response
#print axioms IterArchitecture.installed_tool_live_after_reload
#print axioms IterArchitecture.event_origins_indistinguishable
#print axioms IterArchitecture.nop_is_not_stable_rest
#print axioms IterArchitecture.pettaclaw_is_origin_sensitive
#print axioms IterArchitecture.restart_breaks_control_continuity
#print axioms IterArchitecture.pettaclaw_healthy_restart_preserves_present_moment
#print axioms IterArchitecture.iter_reference_is_not_drop_in_pettaclaw_host
#print axioms IterArchitecture.adapted_target_passes_necessary_check

import IterProcessAdapter

/-!
# MettaCodingBoundary — a native request and evidence boundary

This is the smallest structured boundary shared by a MeTTa coding policy and
an Iter transformation policy.  Iter sees and may replace model messages and
advertisements.  It never receives the captured executable or permitted
coordinates.  A separate broker turns a proposed command into exactly one
observation, appended before the next model step.

The types are deliberately generic.  The runtime may use MeTTa terms and
symbolic capability names; no provider request format or fixed tool catalogue
is part of this model.
-/

namespace MettaCodingBoundary

structure Visible (Message Capability : Type) where
  messages : List Message
  advertised : List Capability
deriving Repr, DecidableEq

structure Boundary (Message Capability : Type) where
  messages : List Message
  advertised : List Capability
  executable : List Capability
  permitted : List Capability
deriving Repr, DecidableEq

abbrev Transformation (Message Capability : Type) :=
  Visible Message Capability → Option (Visible Message Capability)

def visible {Message Capability : Type}
    (boundary : Boundary Message Capability) : Visible Message Capability :=
  ⟨boundary.messages, boundary.advertised⟩

def installVisible {Message Capability : Type}
    (boundary : Boundary Message Capability)
    (next : Visible Message Capability) : Boundary Message Capability :=
  { boundary with messages := next.messages, advertised := next.advertised }

def applyOne {Message Capability : Type}
    (transformation : Transformation Message Capability)
    (before : Visible Message Capability) : Visible Message Capability :=
  match transformation before with
  | some next => next
  | none => before

def applyAll {Message Capability : Type} :
    List (Transformation Message Capability) →
      Visible Message Capability → Visible Message Capability
  | [], before => before
  | transformation :: rest, before =>
      applyAll rest (applyOne transformation before)

def prepare {Message Capability : Type}
    (transformations : List (Transformation Message Capability))
    (boundary : Boundary Message Capability) : Boundary Message Capability :=
  installVisible boundary (applyAll transformations (visible boundary))

theorem prepare_visible_is_exact {Message Capability : Type}
    (transformations : List (Transformation Message Capability))
    (boundary : Boundary Message Capability) :
    visible (prepare transformations boundary) =
      applyAll transformations (visible boundary) := by
  rfl

theorem prepare_preserves_authority {Message Capability : Type}
    (transformations : List (Transformation Message Capability))
    (boundary : Boundary Message Capability) :
    (prepare transformations boundary).executable = boundary.executable ∧
      (prepare transformations boundary).permitted = boundary.permitted := by
  exact ⟨rfl, rfl⟩

theorem empty_preparation_is_identity {Message Capability : Type}
    (boundary : Boundary Message Capability) :
    prepare [] boundary = boundary := by
  cases boundary
  rfl

theorem applyAll_append {Message Capability : Type}
    (left right : List (Transformation Message Capability))
    (before : Visible Message Capability) :
    applyAll (left ++ right) before = applyAll right (applyAll left before) := by
  induction left generalizing before with
  | nil => rfl
  | cons transformation rest ih =>
      simp only [List.cons_append, applyAll]
      exact ih (applyOne transformation before)

def failing {Message Capability : Type} : Transformation Message Capability :=
  fun _ => none

theorem failed_transformation_erases {Message Capability : Type}
    (left right : List (Transformation Message Capability))
    (before : Visible Message Capability) :
    applyAll (left ++ failing :: right) before =
      applyAll (left ++ right) before := by
  rw [applyAll_append, applyAll_append]
  rfl

def appendMessage (message : Nat) : Transformation Nat Nat := fun before =>
  some { before with messages := before.messages ++ [message] }

def clearMessages : Transformation Nat Nat := fun before =>
  some { before with messages := [] }

theorem transformation_order_remains_expressive :
    let before : Visible Nat Nat := ⟨[], []⟩
    applyAll [appendMessage 7, clearMessages] before ≠
      applyAll [clearMessages, appendMessage 7] before := by
  decide

/-! ## Exact refinement of the reference Iter transformation fold -/

def toIterBoundary (boundary : Visible Nat Nat) :
    IterArchitecture.Boundary :=
  ⟨boundary.messages, boundary.advertised⟩

def fromIterBoundary (boundary : IterArchitecture.Boundary) :
    Visible Nat Nat :=
  ⟨boundary.messages, boundary.advertised⟩

@[simp] theorem fromIter_toIter (boundary : Visible Nat Nat) :
    fromIterBoundary (toIterBoundary boundary) = boundary := by
  cases boundary
  rfl

@[simp] theorem toIter_fromIter (boundary : IterArchitecture.Boundary) :
    toIterBoundary (fromIterBoundary boundary) = boundary := by
  cases boundary
  rfl

def liftIter (transformation : IterArchitecture.Transformation) :
    Transformation Nat Nat := fun before =>
  (transformation (toIterBoundary before)).map fromIterBoundary

theorem applyOne_liftIter (transformation : IterArchitecture.Transformation)
    (before : Visible Nat Nat) :
    applyOne (liftIter transformation) before =
      fromIterBoundary
        (IterArchitecture.applyTransformation
          (toIterBoundary before) transformation) := by
  cases result : transformation (toIterBoundary before) <;>
    simp [applyOne, liftIter, IterArchitecture.applyTransformation, result]

theorem applyAll_liftIter
    (transformations : List IterArchitecture.Transformation)
    (before : Visible Nat Nat) :
    applyAll (transformations.map liftIter) before =
      fromIterBoundary
        (IterArchitecture.applyTransformations
          transformations (toIterBoundary before)) := by
  induction transformations generalizing before with
  | nil => simp [applyAll, IterArchitecture.applyTransformations]
  | cons transformation rest ih =>
      simp only [List.map_cons, applyAll,
        IterArchitecture.applyTransformations]
      rw [ih, applyOne_liftIter, toIter_fromIter]

def prepareWithIter (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) : Boundary Nat Nat :=
  prepare (transformations.map liftIter) boundary

/-- The native MeTTa boundary runs the exact reference Iter fold on the
visible projection; the authority coordinates remain outside that fold. -/
theorem prepareWithIter_is_exact
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) :
    visible (prepareWithIter transformations boundary) =
      fromIterBoundary
        (IterArchitecture.applyTransformations transformations
          (toIterBoundary (visible boundary))) := by
  exact applyAll_liftIter transformations (visible boundary)

theorem prepareWithIter_preserves_authority
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) :
    (prepareWithIter transformations boundary).executable =
        boundary.executable ∧
      (prepareWithIter transformations boundary).permitted =
        boundary.permitted := by
  exact prepare_preserves_authority (transformations.map liftIter) boundary

/-! The runtime selects this adapter with policy data.  `false` is a genuine
disabled path, not an empty special transformation. -/
def prepareSelected (runIter : Bool)
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) : Boundary Nat Nat :=
  if runIter then prepareWithIter transformations boundary else boundary

theorem disabled_iter_request_is_identity
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) :
    prepareSelected false transformations boundary = boundary := by
  rfl

theorem enabled_iter_request_is_exact
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) :
    visible (prepareSelected true transformations boundary) =
      fromIterBoundary
        (IterArchitecture.applyTransformations transformations
          (toIterBoundary (visible boundary))) := by
  exact prepareWithIter_is_exact transformations boundary

theorem selected_request_preserves_authority
    (runIter : Bool)
    (transformations : List IterArchitecture.Transformation)
    (boundary : Boundary Nat Nat) :
    (prepareSelected runIter transformations boundary).executable =
        boundary.executable ∧
      (prepareSelected runIter transformations boundary).permitted =
        boundary.permitted := by
  cases runIter
  · exact ⟨rfl, rfl⟩
  · exact prepareWithIter_preserves_authority transformations boundary

/-! ## Brokered MeTTa command evidence -/

structure Command (Capability Payload : Type) where
  capability : Capability
  payload : Payload
deriving Repr, DecidableEq

inductive Execution (Workspace Result Error : Type)
  | success (workspace : Workspace) (result : Result)
  | failure (error : Error)
deriving Repr, DecidableEq

inductive Observation (Capability Result Error : Type)
  | succeeded (capability : Capability) (result : Result)
  | failed (capability : Capability) (error : Error)
  | denied (capability : Capability)
  | unknown (capability : Capability)
deriving Repr, DecidableEq

abbrev Executor (Capability Payload Workspace Result Error : Type) :=
  Workspace → Command Capability Payload → Execution Workspace Result Error

def broker {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (boundary : Boundary Message Capability)
    (execute : Executor Capability Payload Workspace Result Error)
    (workspace : Workspace) (command : Command Capability Payload) :
    Workspace × Observation Capability Result Error :=
  if command.capability ∈ boundary.executable then
    if command.capability ∈ boundary.permitted then
      match execute workspace command with
      | .success next result => (next, .succeeded command.capability result)
      | .failure error => (workspace, .failed command.capability error)
    else (workspace, .denied command.capability)
  else (workspace, .unknown command.capability)

theorem unknown_command_preserves_workspace
    {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (boundary : Boundary Message Capability)
    (execute : Executor Capability Payload Workspace Result Error)
    (workspace : Workspace) (command : Command Capability Payload)
    (unknown : command.capability ∉ boundary.executable) :
    broker boundary execute workspace command =
      (workspace, .unknown command.capability) := by
  simp [broker, unknown]

theorem denied_command_preserves_workspace
    {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (boundary : Boundary Message Capability)
    (execute : Executor Capability Payload Workspace Result Error)
    (workspace : Workspace) (command : Command Capability Payload)
    (known : command.capability ∈ boundary.executable)
    (denied : command.capability ∉ boundary.permitted) :
    broker boundary execute workspace command =
      (workspace, .denied command.capability) := by
  simp [broker, known, denied]

theorem failed_command_preserves_workspace
    {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (boundary : Boundary Message Capability)
    (execute : Executor Capability Payload Workspace Result Error)
    (workspace : Workspace) (command : Command Capability Payload)
    (error : Error)
    (known : command.capability ∈ boundary.executable)
    (permitted : command.capability ∈ boundary.permitted)
    (failed : execute workspace command = .failure error) :
    broker boundary execute workspace command =
      (workspace, .failed command.capability error) := by
  simp [broker, known, permitted, failed]

structure State (Message Capability Workspace : Type) where
  boundary : Boundary Message Capability
  workspace : Workspace
deriving Repr, DecidableEq

def record {Message Capability Result Error : Type}
    (encode : Observation Capability Result Error → Message)
    (boundary : Boundary Message Capability)
    (observation : Observation Capability Result Error) :
    Boundary Message Capability :=
  { boundary with messages := boundary.messages ++ [encode observation] }

def codingStep {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (encode : Observation Capability Result Error → Message)
    (execute : Executor Capability Payload Workspace Result Error)
    (state : State Message Capability Workspace)
    (command : Command Capability Payload) :
    State Message Capability Workspace :=
  let outcome := broker state.boundary execute state.workspace command
  { boundary := record encode state.boundary outcome.2
    workspace := outcome.1 }

def selectedCodingStep {Payload Workspace Result Error : Type}
    (runIter : Bool)
    (transformations : List IterArchitecture.Transformation)
    (encode : Observation Nat Result Error → Nat)
    (execute : Executor Nat Payload Workspace Result Error)
    (state : State Nat Nat Workspace) (command : Command Nat Payload) :
    State Nat Nat Workspace :=
  codingStep encode execute
    { state with
      boundary := prepareSelected runIter transformations state.boundary }
    command

/-- Every broker attempt, including denial and failure, becomes the newest
message before a later model step can inspect the state. -/
theorem coding_step_records_broker_observation
    {Message Capability Payload Workspace Result Error : Type}
    [DecidableEq Capability]
    (encode : Observation Capability Result Error → Message)
    (execute : Executor Capability Payload Workspace Result Error)
    (state : State Message Capability Workspace)
    (command : Command Capability Payload) :
    (codingStep encode execute state command).boundary.messages =
      state.boundary.messages ++
        [encode (broker state.boundary execute state.workspace command).2] := by
  rfl

/-- Request preparation and effect evidence compose without an intermediate
model step: the newest message is the broker observation over the exact
prepared request boundary. -/
theorem selected_coding_step_records_prepared_observation
    {Payload Workspace Result Error : Type}
    (runIter : Bool)
    (transformations : List IterArchitecture.Transformation)
    (encode : Observation Nat Result Error → Nat)
    (execute : Executor Nat Payload Workspace Result Error)
    (state : State Nat Nat Workspace) (command : Command Nat Payload) :
    (selectedCodingStep runIter transformations encode execute state command
      ).boundary.messages =
      (prepareSelected runIter transformations state.boundary).messages ++
        [encode
          (broker (prepareSelected runIter transformations state.boundary)
            execute state.workspace command).2] := by
  rfl

end MettaCodingBoundary

#print axioms MettaCodingBoundary.prepare_visible_is_exact
#print axioms MettaCodingBoundary.prepare_preserves_authority
#print axioms MettaCodingBoundary.empty_preparation_is_identity
#print axioms MettaCodingBoundary.failed_transformation_erases
#print axioms MettaCodingBoundary.transformation_order_remains_expressive
#print axioms MettaCodingBoundary.prepareWithIter_is_exact
#print axioms MettaCodingBoundary.prepareWithIter_preserves_authority
#print axioms MettaCodingBoundary.disabled_iter_request_is_identity
#print axioms MettaCodingBoundary.enabled_iter_request_is_exact
#print axioms MettaCodingBoundary.selected_request_preserves_authority
#print axioms MettaCodingBoundary.unknown_command_preserves_workspace
#print axioms MettaCodingBoundary.denied_command_preserves_workspace
#print axioms MettaCodingBoundary.failed_command_preserves_workspace
#print axioms MettaCodingBoundary.coding_step_records_broker_observation
#print axioms MettaCodingBoundary.selected_coding_step_records_prepared_observation

import Mettapedia.Languages.C11.ByteStorageData

/-!
# Checked data for byte/object requests and residual configurations

Numeric packets preserve the entire finite storage and catalog, original
request, allocator choice, response and retained state. Configuration
packets name the byte width and signed pointer-difference policy; resuming
under a different policy is refused. These policy checks do not stand in for
world/currentness, source-declaration or ownership-authority validation.

The codecs have both inverse laws. Executing decoded request packets is
sound for the independent object reduction. Every independent reduction
from an encoded state is realizable under a constructed allocator choice,
with exactly its heap and catalog endpoint. This endpoint guarantee is
extensional; it does not discard shadowed records from saved finite data.

The configuration data remain records, not an assumed Cesta/GSLT adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ObjectStepData

open Mettapedia.Machines.CMemory
open ByteStorageData

inductive RequestData where
  | readRepresentation (range : ByteRanges.Range)
  | writeRepresentation (address : ByteRanges.Address) (contents : List (Option Nat))
  | copyRepresentation (source : ByteRanges.Range) (target : ByteRanges.Address)
  | allocate (bytes : Nat)
  | retire (address : Option Ptr)
  | advancePointer (pointer : ArrayPointers.Pointer) (distance : Int)
  | subtractPointers (left right : ArrayPointers.Pointer)
  | elementView (pointer : ArrayPointers.Pointer)
  deriving DecidableEq, Repr

def encodeRequest {profile : Profile} : ObjectStep.Request (Byte profile) → RequestData
  | .readRepresentation range => .readRepresentation range
  | .writeRepresentation address contents => .writeRepresentation address (encodeContents contents)
  | .copyRepresentation source target => .copyRepresentation source target
  | .allocate bytes => .allocate bytes
  | .retire address => .retire address
  | .advancePointer pointer distance => .advancePointer pointer distance
  | .subtractPointers left right => .subtractPointers left right
  | .elementView pointer => .elementView pointer

def decodeRequest (profile : Profile) : RequestData → Option (ObjectStep.Request (Byte profile))
  | .readRepresentation range => some (.readRepresentation range)
  | .writeRepresentation address contents =>
      (decodeContents profile contents).map (.writeRepresentation address)
  | .copyRepresentation source target => some (.copyRepresentation source target)
  | .allocate bytes => some (.allocate bytes)
  | .retire address => some (.retire address)
  | .advancePointer pointer distance => some (.advancePointer pointer distance)
  | .subtractPointers left right => some (.subtractPointers left right)
  | .elementView pointer => some (.elementView pointer)

@[simp]
theorem decodeRequest_encode (profile : Profile) (request : ObjectStep.Request (Byte profile)) :
    decodeRequest profile (encodeRequest request) = some request := by
  cases request <;> simp [decodeRequest, encodeRequest]

theorem encodeRequest_decode (profile : Profile) (data : RequestData)
    (request : ObjectStep.Request (Byte profile)) (decoded : decodeRequest profile data = some request) :
    encodeRequest request = data := by
  cases data with
  | writeRepresentation address contents =>
      cases actual : decodeContents profile contents with
      | none => simp [decodeRequest, actual] at decoded
      | some bytes =>
          simp only [decodeRequest, actual, Option.map_some] at decoded
          cases decoded
          exact congrArg (RequestData.writeRepresentation address)
            (encodeContents_decode profile contents bytes actual)
  | readRepresentation range => cases decoded; rfl
  | copyRepresentation source target => cases decoded; rfl
  | allocate bytes => cases decoded; rfl
  | retire address => cases decoded; rfl
  | advancePointer pointer distance => cases decoded; rfl
  | subtractPointers left right => cases decoded; rfl
  | elementView pointer => cases decoded; rfl

inductive ResponseData where
  | representation (contents : List (Option Nat))
  | updated
  | allocation (address : Option Ptr)
  | pointer (pointer : ArrayPointers.Pointer)
  | difference (value : Int)
  | element (range : ByteRanges.Range)
  deriving DecidableEq, Repr

def encodeResponse {profile : Profile} : ObjectStep.Response (Byte profile) → ResponseData
  | .representation contents => .representation (encodeContents contents)
  | .updated => .updated
  | .allocation address => .allocation address
  | .pointer pointer => .pointer pointer
  | .difference value => .difference value
  | .element range => .element range

def decodeResponse (profile : Profile) : ResponseData → Option (ObjectStep.Response (Byte profile))
  | .representation contents => (decodeContents profile contents).map .representation
  | .updated => some .updated
  | .allocation address => some (.allocation address)
  | .pointer pointer => some (.pointer pointer)
  | .difference value => some (.difference value)
  | .element range => some (.element range)

@[simp]
theorem decodeResponse_encode (profile : Profile) (response : ObjectStep.Response (Byte profile)) :
    decodeResponse profile (encodeResponse response) = some response := by
  cases response <;> simp [decodeResponse, encodeResponse]

theorem encodeResponse_decode (profile : Profile) (data : ResponseData)
    (response : ObjectStep.Response (Byte profile)) (decoded : decodeResponse profile data = some response) :
    encodeResponse response = data := by
  cases data with
  | representation contents =>
      cases actual : decodeContents profile contents with
      | none => simp [decodeResponse, actual] at decoded
      | some bytes =>
          simp only [decodeResponse, actual, Option.map_some] at decoded
          cases decoded
          exact congrArg ResponseData.representation (encodeContents_decode profile contents bytes actual)
  | updated | allocation address | pointer pointer | difference value | element range =>
      cases decoded
      rfl

structure InputData where
  state : StateData
  request : RequestData
  choice : ExecutableStorage.AllocationChoice
  deriving DecidableEq, Repr

def encodeInput {profile : Profile} (input : ObjectStep.Input (Byte profile)) : InputData :=
  ⟨encodeState input.state, encodeRequest input.request, input.choice⟩

def decodeInput (profile : Profile) (data : InputData) : Option (ObjectStep.Input (Byte profile)) := do
  let state ← decodeState profile data.state
  let request ← decodeRequest profile data.request
  some ⟨state, request, data.choice⟩

@[simp]
theorem decodeInput_encode (profile : Profile) (input : ObjectStep.Input (Byte profile)) :
    decodeInput profile (encodeInput input) = some input := by
  cases input
  simp [decodeInput, encodeInput]

theorem encodeInput_decode (profile : Profile) (data : InputData) (input : ObjectStep.Input (Byte profile))
    (decoded : decodeInput profile data = some input) : encodeInput input = data := by
  cases memory : decodeState profile data.state with
  | none => simp [decodeInput, memory] at decoded
  | some state =>
      cases command : decodeRequest profile data.request with
      | none => simp [decodeInput, memory, command] at decoded
      | some request =>
          simp only [decodeInput, memory, command, bind, Option.bind_some] at decoded
          cases decoded
          have sameState := encodeState_decode profile data.state state memory
          have sameRequest := encodeRequest_decode profile data.request request command
          cases data
          simp only [encodeInput, sameState, sameRequest]

structure PolicyData where
  charBits : Nat
  differencePrecision : Nat
  differenceRepresentation : SignedRepresentation
  deriving DecidableEq, Repr

def policyData (profile : Profile) (difference : ArrayPointers.DifferenceProfile) : PolicyData :=
  ⟨profile.charBits, difference.precision, difference.representation⟩

inductive ControlData where
  | pending (input : InputData)
  | completed (response : ResponseData) (saved : StateData)
  | refused (input : InputData)
  deriving DecidableEq, Repr

def encodeControl {profile : Profile} : ObjectStep.Configuration (Byte profile) → ControlData
  | .pending input => .pending (encodeInput input)
  | .completed response saved => .completed (encodeResponse response) (encodeState saved)
  | .refused input => .refused (encodeInput input)

def decodeControl (profile : Profile) : ControlData → Option (ObjectStep.Configuration (Byte profile))
  | .pending input => (decodeInput profile input).map .pending
  | .completed response saved => do
      let actualResponse ← decodeResponse profile response
      let actualState ← decodeState profile saved
      some (.completed actualResponse actualState)
  | .refused input => (decodeInput profile input).map .refused

@[simp]
theorem decodeControl_encode (profile : Profile) (configuration : ObjectStep.Configuration (Byte profile)) :
    decodeControl profile (encodeControl configuration) = some configuration := by
  cases configuration <;> simp [decodeControl, encodeControl]

theorem encodeControl_decode (profile : Profile) (data : ControlData)
    (configuration : ObjectStep.Configuration (Byte profile))
    (decoded : decodeControl profile data = some configuration) : encodeControl configuration = data := by
  cases data with
  | pending input =>
      cases actual : decodeInput profile input with
      | none => simp [decodeControl, actual] at decoded
      | some retained =>
          simp only [decodeControl, actual, Option.map_some] at decoded
          cases decoded
          exact congrArg ControlData.pending (encodeInput_decode profile input retained actual)
  | refused input =>
      cases actual : decodeInput profile input with
      | none => simp [decodeControl, actual] at decoded
      | some retained =>
          simp only [decodeControl, actual, Option.map_some] at decoded
          cases decoded
          exact congrArg ControlData.refused (encodeInput_decode profile input retained actual)
  | completed response saved =>
      cases first : decodeResponse profile response with
      | none => simp [decodeControl, first] at decoded
      | some actualResponse =>
          cases second : decodeState profile saved with
          | none => simp [decodeControl, first, second] at decoded
          | some actualState =>
              simp only [decodeControl, first, second, bind, Option.bind_some] at decoded
              cases decoded
              simp only [encodeControl, encodeResponse_decode profile response actualResponse first,
                encodeState_decode profile saved actualState second]

structure ConfigurationData where
  policy : PolicyData
  control : ControlData
  deriving DecidableEq, Repr

def encodeConfiguration (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (configuration : ObjectStep.Configuration (Byte profile)) : ConfigurationData :=
  ⟨policyData profile difference, encodeControl configuration⟩

def decodeConfiguration (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) : Option (ObjectStep.Configuration (Byte profile)) :=
  if data.policy = policyData profile difference then decodeControl profile data.control else none

@[simp]
theorem decodeConfiguration_encode (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (configuration : ObjectStep.Configuration (Byte profile)) :
    decodeConfiguration profile difference (encodeConfiguration profile difference configuration) = some configuration := by
  simp [decodeConfiguration, encodeConfiguration]

theorem encodeConfiguration_decode (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) (configuration : ObjectStep.Configuration (Byte profile))
    (decoded : decodeConfiguration profile difference data = some configuration) :
    encodeConfiguration profile difference configuration = data := by
  unfold decodeConfiguration at decoded
  split at decoded
  · rename_i policyEqual
    have controlEqual := encodeControl_decode profile data.control configuration decoded
    cases data
    simp only [encodeConfiguration, ConfigurationData.mk.injEq]
    exact ⟨policyEqual.symm, controlEqual⟩
  · cases decoded

theorem changed_policy_refused (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) (changed : data.policy ≠ policyData profile difference) :
    decodeConfiguration profile difference data = none := by
  simp [decodeConfiguration, changed]

def executeData (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (choice : ExecutableStorage.AllocationChoice) (before : StateData) (request : RequestData) :
    Option (ResponseData × StateData) := do
  let state ← decodeState profile before
  let operation ← decodeRequest profile request
  let (response, saved) ← ObjectStep.execute difference choice state operation
  some (encodeResponse response, encodeState saved)

theorem executeData_on_encoded (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (choice : ExecutableStorage.AllocationChoice) (before : ObjectStep.State (Byte profile))
    (request : ObjectStep.Request (Byte profile)) :
    executeData profile difference choice (encodeState before) (encodeRequest request) =
      (ObjectStep.execute difference choice before request).map
        (fun result => (encodeResponse result.1, encodeState result.2)) := by
  simp only [executeData, decodeState_encode, decodeRequest_encode, bind, Option.bind_some]
  cases ObjectStep.execute difference choice before request <;> rfl

theorem executeData_sound (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (choice : ExecutableStorage.AllocationChoice) (before : StateData) (request : RequestData)
    (response : ResponseData) (after : StateData)
    (executed : executeData profile difference choice before request = some (response, after)) :
    ∃ state operation result saved,
      decodeState profile before = some state ∧ decodeRequest profile request = some operation ∧
      decodeResponse profile response = some result ∧ decodeState profile after = some saved ∧
      ObjectStep.Reduction difference (ObjectStep.represent state) operation result (ObjectStep.represent saved) := by
  cases memory : decodeState profile before with
  | none => simp [executeData, memory] at executed
  | some state =>
      cases command : decodeRequest profile request with
      | none => simp [executeData, memory, command] at executed
      | some operation =>
          cases computed : ObjectStep.execute difference choice state operation with
          | none => simp [executeData, memory, command, computed] at executed
          | some result =>
              rcases result with ⟨result, saved⟩
              simp only [executeData, memory, command, computed, bind, Option.bind_some] at executed
              cases executed
              exact ⟨state, operation, result, saved, rfl, rfl,
                decodeResponse_encode profile result, decodeState_encode profile saved,
                ObjectStep.execute_sound difference choice state saved operation result computed⟩

theorem executeData_complete (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (before : ObjectStep.State (Byte profile)) (request : ObjectStep.Request (Byte profile))
    (response : ObjectStep.Response (Byte profile)) (after : ObjectStep.SemanticState (Byte profile))
    (reduced : ObjectStep.Reduction difference (ObjectStep.represent before) request response after) :
    ∃ choice saved, executeData profile difference choice (encodeState before) (encodeRequest request) =
      some (encodeResponse response, encodeState saved) ∧ ObjectStep.represent saved = after := by
  obtain ⟨choice, saved, computed, represented⟩ := ObjectStep.execute_complete difference before request response after reduced
  exact ⟨choice, saved, by rw [executeData_on_encoded, computed]; rfl, represented⟩

inductive AdvanceData where
  | receipt (input : InputData) (response : ResponseData) (saved : ConfigurationData)
  | returned (response : ResponseData) (saved : StateData)
  | refused (input : InputData)
  deriving DecidableEq, Repr

/-- A represented configuration is advanced only under its retained policy.
The response packet includes the exact residual, not a restart request. -/
def advanceData (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) : Option AdvanceData := do
  let configuration ← decodeConfiguration profile difference data
  match configuration with
  | .pending input =>
      match ObjectStep.execute difference input.choice input.state input.request with
      | some (response, saved) =>
          some (.receipt (encodeInput input) (encodeResponse response)
            (encodeConfiguration profile difference (.completed response saved)))
      | none => some (.refused (encodeInput input))
  | .completed response saved => some (.returned (encodeResponse response) (encodeState saved))
  | .refused input => some (.refused (encodeInput input))

theorem advanceData_accepted (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (input : ObjectStep.Input (Byte profile)) (response : ObjectStep.Response (Byte profile))
    (saved : ObjectStep.State (Byte profile))
    (computed : ObjectStep.execute difference input.choice input.state input.request = some (response, saved)) :
    advanceData profile difference (encodeConfiguration profile difference (.pending input)) =
      some (.receipt (encodeInput input) (encodeResponse response)
        (encodeConfiguration profile difference (.completed response saved))) := by
  simp only [advanceData, decodeConfiguration_encode, bind, Option.bind_some, computed]

theorem advanceData_completed (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (response : ObjectStep.Response (Byte profile)) (saved : ObjectStep.State (Byte profile)) :
    advanceData profile difference (encodeConfiguration profile difference (.completed response saved)) =
      some (.returned (encodeResponse response) (encodeState saved)) := by
  simp only [advanceData, decodeConfiguration_encode, bind, Option.bind_some]

theorem advanceData_changed_policy_refused (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) (changed : data.policy ≠ policyData profile difference) :
    advanceData profile difference data = none := by
  simp only [advanceData, changed_policy_refused profile difference data changed, bind, Option.bind_none]

theorem advanceData_receipt_sound (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (data : ConfigurationData) (inputData : InputData) (responseData : ResponseData)
    (savedData : ConfigurationData)
    (advanced : advanceData profile difference data = some (.receipt inputData responseData savedData)) :
    ∃ input response saved,
      decodeConfiguration profile difference data = some (.pending input) ∧
      decodeInput profile inputData = some input ∧ decodeResponse profile responseData = some response ∧
      decodeConfiguration profile difference savedData = some (.completed response saved) ∧
      ObjectStep.Reduction difference (ObjectStep.represent input.state) input.request response
        (ObjectStep.represent saved) := by
  cases decoded : decodeConfiguration profile difference data with
  | none => simp [advanceData, decoded] at advanced
  | some configuration =>
      cases configuration with
      | completed response saved => simp [advanceData, decoded] at advanced
      | refused input => simp [advanceData, decoded] at advanced
      | pending input =>
          cases computed : ObjectStep.execute difference input.choice input.state input.request with
          | none => simp [advanceData, decoded, computed] at advanced
          | some result =>
              rcases result with ⟨response, saved⟩
              simp only [advanceData, decoded, computed, bind, Option.bind_some,
                Option.some.injEq, AdvanceData.receipt.injEq] at advanced
              obtain ⟨rfl, rfl, rfl⟩ := advanced
              exact ⟨input, response, saved, rfl, decodeInput_encode profile input,
                decodeResponse_encode profile response, decodeConfiguration_encode profile difference _,
                ObjectStep.execute_sound difference input.choice input.state saved input.request response computed⟩

theorem advanceData_receipt_complete (profile : Profile) (difference : ArrayPointers.DifferenceProfile)
    (before : ObjectStep.State (Byte profile)) (request : ObjectStep.Request (Byte profile))
    (response : ObjectStep.Response (Byte profile)) (after : ObjectStep.SemanticState (Byte profile))
    (reduced : ObjectStep.Reduction difference (ObjectStep.represent before) request response after) :
    ∃ choice saved,
      advanceData profile difference
        (encodeConfiguration profile difference (.pending ⟨before, request, choice⟩)) =
          some (.receipt (encodeInput ⟨before, request, choice⟩) (encodeResponse response)
            (encodeConfiguration profile difference (.completed response saved))) ∧
      ObjectStep.represent saved = after := by
  obtain ⟨choice, saved, computed, represented⟩ := ObjectStep.execute_complete difference before request response after reduced
  exact ⟨choice, saved, advanceData_accepted profile difference ⟨before, request, choice⟩ response saved computed,
    represented⟩

end Mettapedia.Languages.C11.ObjectStepData

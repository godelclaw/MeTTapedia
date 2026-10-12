import Mettapedia.Languages.C11.ExpressionSourceExecution
import Mettapedia.Languages.C11.ReadExpressionData

/-!
# Checked packets for located integer-expression execution

Located source syntax, typed scalar values, occurrence identities and complete
residuals have checked data representations. Occurrence identities are paths
through the source-generated sums of finite index types. The plan is always
reconstructed from the decoded expression; packets do not supply an independent
operation table or sequencing relation.

The inverse laws preserve every accepted packet, including ordered shadowed
storage records and cache occurrences. Decoding establishes representability,
not a declaration, execution history, current-world dependency or ownership
authority. Ordinary C source parsing and general source elaboration remain
separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.LocatedExpressionData

open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution

abbrev ScalarData := ReadExpression.ScalarData

def encodeScalar {model : Model} (scalar : IntegerScalar.Value model.parameters) : ScalarData :=
  ReadExpression.encodeScalar (layout := model.layout .int) scalar

def decodeScalar (model : Model) (data : ScalarData) : Option (IntegerScalar.Value model.parameters) :=
  ReadExpression.decodeScalar (model.layout .int) data

theorem decodeScalar_encode (model : Model) (scalar : IntegerScalar.Value model.parameters) :
    decodeScalar model (encodeScalar scalar) = some scalar :=
  ReadExpression.decodeScalar_encode _ _

theorem encodeScalar_decode (model : Model) (data : ScalarData)
    (scalar : IntegerScalar.Value model.parameters) (decoded : decodeScalar model data = some scalar) :
    encodeScalar scalar = data := ReadExpression.encodeScalar_decode _ _ _ decoded

structure DestinationData where
  location : ObjectAccessMemory.Lvalue
  type : IntegerType IntegerExtension
  deriving DecidableEq, Repr

def encodeDestination (selected : Destination) : DestinationData := ⟨selected.location, selected.type⟩

def decodeDestination (data : DestinationData) : Option Destination :=
  if formed : data.location.view.type = .scalar (.integer data.type) then
    some ⟨data.location, data.type, formed⟩ else none

theorem decodeDestination_encode (selected : Destination) :
    decodeDestination (encodeDestination selected) = some selected := by
  cases selected with
  | mk location type formed =>
      dsimp only [decodeDestination, encodeDestination]
      rw [dif_pos formed]

theorem encodeDestination_decode (data : DestinationData) (selected : Destination)
    (decoded : decodeDestination data = some selected) : encodeDestination selected = data := by
  by_cases formed : data.location.view.type = .scalar (.integer data.type)
  · simp only [decodeDestination, dif_pos formed] at decoded
    cases decoded
    cases data
    rfl
  · simp only [decodeDestination, dif_neg formed] at decoded
    cases decoded

inductive ExpressionData where
  | value (scalar : ScalarData)
  | load (location : DestinationData)
  | arithmetic (operator : IntegerBinaryOperator) (first second : ExpressionData)
  | cast (type : IntegerType IntegerExtension) (operand : ExpressionData)
  | assignment (location : DestinationData) (operand : ExpressionData)
  | update (location : DestinationData) (increment isPrefix : Bool)
  | comma (first second : ExpressionData)
  deriving DecidableEq, Repr

def encodeExpression {model : Model} : Expression model → ExpressionData
  | .value scalar => .value (encodeScalar scalar)
  | .load location => .load (encodeDestination location)
  | .arithmetic operator first second => .arithmetic operator (encodeExpression first) (encodeExpression second)
  | .cast type operand => .cast type (encodeExpression operand)
  | .assignment location operand => .assignment (encodeDestination location) (encodeExpression operand)
  | .update location increment isPrefix => .update (encodeDestination location) increment isPrefix
  | .comma first second => .comma (encodeExpression first) (encodeExpression second)

def decodeExpression (model : Model) : ExpressionData → Option (Expression model)
  | .value scalar => (decodeScalar model scalar).map Expression.value
  | .load location => (decodeDestination location).map Expression.load
  | .arithmetic operator first second => do
      some (.arithmetic operator (← decodeExpression model first) (← decodeExpression model second))
  | .cast type operand => (decodeExpression model operand).map (Expression.cast type)
  | .assignment location operand => do
      some (.assignment (← decodeDestination location) (← decodeExpression model operand))
  | .update location increment isPrefix => (decodeDestination location).map (fun selected => .update selected increment isPrefix)
  | .comma first second => do some (.comma (← decodeExpression model first) (← decodeExpression model second))

theorem decodeExpression_encode (model : Model) (expression : Expression model) :
    decodeExpression model (encodeExpression expression) = some expression := by
  induction expression <;> simp_all only [encodeExpression, decodeExpression, decodeScalar_encode,
    decodeDestination_encode, Option.map_some, bind, Option.bind_some]

theorem encodeExpression_decode (model : Model) (data : ExpressionData) (expression : Expression model)
    (decoded : decodeExpression model data = some expression) : encodeExpression expression = data := by
  induction data generalizing expression with
  | value scalar =>
      obtain ⟨value, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg ExpressionData.value (encodeScalar_decode _ _ _ accepted)
  | load location =>
      obtain ⟨selected, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg ExpressionData.load (encodeDestination_decode _ _ accepted)
  | arithmetic operator first second firstIH secondIH =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, leftRead, right, rightRead, rfl⟩ := decoded
      simp only [encodeExpression, firstIH _ leftRead, secondIH _ rightRead]
  | cast type operand ih =>
      obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg (ExpressionData.cast type) (ih _ accepted)
  | assignment location operand ih =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨selected, selectedRead, source, sourceRead, rfl⟩ := decoded
      simp only [encodeExpression, encodeDestination_decode _ _ selectedRead, ih _ sourceRead]
  | update location increment isPrefix =>
      obtain ⟨selected, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg (fun location => ExpressionData.update location increment isPrefix)
        (encodeDestination_decode _ _ accepted)
  | comma first second firstIH secondIH =>
      simp only [decodeExpression, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨left, leftRead, right, rightRead, rfl⟩ := decoded
      simp only [encodeExpression, firstIH _ leftRead, secondIH _ rightRead]

theorem encodeExpression_injective (model : Model) : Function.Injective (@encodeExpression model) := by
  intro first second same
  have decoded := congrArg (decodeExpression model) same
  rw [decodeExpression_encode, decodeExpression_encode] at decoded
  exact Option.some.inj decoded

inductive IndexData where
  | leaf (ordinal : Nat)
  | left (following : IndexData)
  | right (following : IndexData)
  deriving DecidableEq, Repr

private structure IndexCodec (Index : Type) where
  encode : Index → IndexData
  decode : IndexData → Option Index
  decode_encode : ∀ index, decode (encode index) = some index
  encode_decode : ∀ data index, decode data = some index → encode index = data

private def finiteCodec (count : Nat) : IndexCodec (Fin count) where
  encode index := .leaf index.val
  decode
    | .leaf ordinal => if valid : ordinal < count then some ⟨ordinal, valid⟩ else none
    | .left _ | .right _ => none
  decode_encode index := by simp only [dif_pos index.isLt]
  encode_decode data index decoded := by
    cases data with
    | left _ | right _ => cases decoded
    | leaf ordinal =>
        by_cases valid : ordinal < count
        · simp only [dif_pos valid] at decoded
          cases decoded
          rfl
        · simp only [dif_neg valid] at decoded
          cases decoded

private def sumCodec {First Second : Type} (first : IndexCodec First) (second : IndexCodec Second) :
    IndexCodec (First ⊕ Second) where
  encode
    | .inl index => .left (first.encode index)
    | .inr index => .right (second.encode index)
  decode
    | .left data => (first.decode data).map Sum.inl
    | .right data => (second.decode data).map Sum.inr
    | .leaf _ => none
  decode_encode index := by
    cases index <;> simp only [first.decode_encode, second.decode_encode, Option.map_some]
  encode_decode data index decoded := by
    cases data with
    | leaf _ => cases decoded
    | left data =>
        obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg IndexData.left (first.encode_decode _ _ accepted)
    | right data =>
        obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact congrArg IndexData.right (second.encode_decode _ _ accepted)

private def indexCodec {model : Model} (expression : Expression model) : IndexCodec (Index expression) :=
  match expression with
  | .value _ | .load _ => finiteCodec 1
  | .arithmetic _ first second | .comma first second => sumCodec (sumCodec (indexCodec first) (indexCodec second)) (finiteCodec 1)
  | .cast _ operand => sumCodec (indexCodec operand) (finiteCodec 1)
  | .assignment _ operand => sumCodec (sumCodec (indexCodec operand) (finiteCodec 1)) (finiteCodec 2)
  | .update _ _ _ => sumCodec (sumCodec (sumCodec (sumCodec (finiteCodec 1) (finiteCodec 1))
      (finiteCodec 1)) (finiteCodec 1)) (finiteCodec 2)

def encodeIndex {model : Model} (expression : Expression model) : Index expression → IndexData := (indexCodec expression).encode
def decodeIndex {model : Model} (expression : Expression model) : IndexData → Option (Index expression) := (indexCodec expression).decode

theorem decodeIndex_encode {model : Model} (expression : Expression model) (index : Index expression) :
    decodeIndex expression (encodeIndex expression index) = some index := (indexCodec expression).decode_encode index

theorem encodeIndex_decode {model : Model} (expression : Expression model) (data : IndexData) (index : Index expression)
    (decoded : decodeIndex expression data = some index) : encodeIndex expression index = data :=
  (indexCodec expression).encode_decode data index decoded

theorem encodeIndex_injective {model : Model} (expression : Expression model) : Function.Injective (encodeIndex expression) := by
  intro first second same
  have decoded := congrArg (decodeIndex expression) same
  rw [decodeIndex_encode, decodeIndex_encode] at decoded
  exact Option.some.inj decoded

private theorem decodeList_encode {Source Data : Type} (encode : Source → Data)
    (decode : Data → Option Source) (inverse : ∀ source, decode (encode source) = some source)
    (sources : List Source) : (sources.map encode).mapM decode = some sources := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp only [List.map_cons, List.mapM_cons, inverse, bind, Option.bind_some, ih, pure]

private theorem encodeList_decode {Source Data : Type} (encode : Source → Data)
    (decode : Data → Option Source)
    (inverse : ∀ data source, decode data = some source → encode source = data)
    (data : List Data) (sources : List Source) (decoded : data.mapM decode = some sources) :
    sources.map encode = data := by
  induction data generalizing sources with
  | nil => cases decoded; rfl
  | cons entry rest ih =>
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at decoded
      obtain ⟨source, accepted, following, followingRead, rfl⟩ := decoded
      simp only [List.map_cons, inverse _ _ accepted, ih _ followingRead]

inductive OutcomeData where
  | value (scalar : ScalarData)
  | loaded (scalar : ScalarData) (negativeZero : Bool)
  | stored (scalar : ScalarData)
  | arithmeticFault (type : IntegerType IntegerExtension) (reason : ArithmeticFault)
  | conversionSignal (identifier : Nat)
  | objectTrap (type : IntegerType IntegerExtension) (reason : IntegerBits.Trap)
  | paddingTrap (type : IntegerType IntegerExtension)
  deriving DecidableEq, Repr

def encodeOutcome {model : Model} : Outcome model → OutcomeData
  | .value scalar => .value (encodeScalar scalar)
  | .loaded scalar negativeZero => .loaded (encodeScalar scalar) negativeZero
  | .stored scalar => .stored (encodeScalar scalar)
  | .arithmeticFault type reason => .arithmeticFault type reason
  | .conversionSignal identifier => .conversionSignal identifier
  | .objectTrap type reason => .objectTrap type reason
  | .paddingTrap type => .paddingTrap type

def decodeOutcome (model : Model) : OutcomeData → Option (Outcome model)
  | .value scalar => (decodeScalar model scalar).map Outcome.value
  | .loaded scalar negativeZero => (decodeScalar model scalar).map (fun value => .loaded value negativeZero)
  | .stored scalar => (decodeScalar model scalar).map Outcome.stored
  | .arithmeticFault type reason => some (.arithmeticFault type reason)
  | .conversionSignal identifier => some (.conversionSignal identifier)
  | .objectTrap type reason => some (.objectTrap type reason)
  | .paddingTrap type => some (.paddingTrap type)

theorem decodeOutcome_encode (model : Model) (outcome : Outcome model) :
    decodeOutcome model (encodeOutcome outcome) = some outcome := by
  cases outcome <;> simp only [encodeOutcome, decodeOutcome, decodeScalar_encode, Option.map_some]

theorem encodeOutcome_decode (model : Model) (data : OutcomeData) (outcome : Outcome model)
    (decoded : decodeOutcome model data = some outcome) : encodeOutcome outcome = data := by
  cases data with
  | value scalar =>
      obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg OutcomeData.value (encodeScalar_decode _ _ _ accepted)
  | loaded scalar negativeZero =>
      obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg (fun scalar => OutcomeData.loaded scalar negativeZero) (encodeScalar_decode _ _ _ accepted)
  | stored scalar =>
      obtain ⟨source, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact congrArg OutcomeData.stored (encodeScalar_decode _ _ _ accepted)
  | arithmeticFault type reason | conversionSignal identifier | objectTrap type reason | paddingTrap type =>
      cases decoded
      rfl

def encodeIndices {model : Model} (expression : Expression model) (indices : List (Index expression)) : List IndexData :=
  indices.map (encodeIndex expression)

def decodeIndices {model : Model} (expression : Expression model) (data : List IndexData) : Option (List (Index expression)) :=
  data.mapM (decodeIndex expression)

theorem decodeIndices_encode {model : Model} (expression : Expression model) (indices : List (Index expression)) :
    decodeIndices expression (encodeIndices expression indices) = some indices :=
  decodeList_encode _ _ (decodeIndex_encode expression) indices

theorem encodeIndices_decode {model : Model} (expression : Expression model) (data : List IndexData)
    (indices : List (Index expression)) (decoded : decodeIndices expression data = some indices) :
    encodeIndices expression indices = data := encodeList_decode _ _ (encodeIndex_decode expression) _ _ decoded

abbrev EntryData := IndexData × OutcomeData

def encodeEntry {model : Model} (expression : Expression model) (entry : Index expression × Outcome model) : EntryData :=
  ⟨encodeIndex expression entry.1, encodeOutcome entry.2⟩

def decodeEntry {model : Model} (expression : Expression model) (data : EntryData) : Option (Index expression × Outcome model) := do
  let index ← decodeIndex expression data.1
  let outcome ← decodeOutcome model data.2
  some (index, outcome)

theorem decodeEntry_encode {model : Model} (expression : Expression model) (entry : Index expression × Outcome model) :
    decodeEntry expression (encodeEntry expression entry) = some entry := by
  cases entry
  simp only [encodeEntry, decodeEntry, decodeIndex_encode, decodeOutcome_encode, bind, Option.bind_some]

theorem encodeEntry_decode {model : Model} (expression : Expression model) (data : EntryData)
    (entry : Index expression × Outcome model) (decoded : decodeEntry expression data = some entry) :
    encodeEntry expression entry = data := by
  simp only [decodeEntry, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨index, indexed, outcome, observed, rfl⟩ := decoded
  cases data
  simp only [encodeEntry, encodeIndex_decode _ _ _ indexed, encodeOutcome_decode _ _ _ observed]

def encodeCache {model : Model} (expression : Expression model) (cache : Cache (Index expression) model) : List EntryData :=
  cache.map (encodeEntry expression)

def decodeCache {model : Model} (expression : Expression model) (data : List EntryData) : Option (Cache (Index expression) model) :=
  data.mapM (decodeEntry expression)

theorem decodeCache_encode {model : Model} (expression : Expression model) (cache : Cache (Index expression) model) :
    decodeCache expression (encodeCache expression cache) = some cache :=
  decodeList_encode _ _ (decodeEntry_encode expression) cache

theorem encodeCache_decode {model : Model} (expression : Expression model) (data : List EntryData)
    (cache : Cache (Index expression) model) (decoded : decodeCache expression data = some cache) :
    encodeCache expression cache = data := encodeList_decode _ _ (encodeEntry_decode expression) _ _ decoded

def encodeHalted {model : Model} (expression : Expression model) (halted : Option (Index expression × Outcome model)) : Option EntryData :=
  halted.map (encodeEntry expression)

def decodeHalted {model : Model} (expression : Expression model) : Option EntryData → Option (Option (Index expression × Outcome model))
  | none => some none
  | some data => (decodeEntry expression data).map some

theorem decodeHalted_encode {model : Model} (expression : Expression model) (halted : Option (Index expression × Outcome model)) :
    decodeHalted expression (encodeHalted expression halted) = some halted := by
  cases halted <;> simp only [encodeHalted, decodeHalted, Option.map_none, Option.map_some, decodeEntry_encode]

theorem encodeHalted_decode {model : Model} (expression : Expression model) (data : Option EntryData)
    (halted : Option (Index expression × Outcome model)) (decoded : decodeHalted expression data = some halted) :
    encodeHalted expression halted = data := by
  cases data with
  | none => cases decoded; rfl
  | some data =>
      obtain ⟨entry, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
      simp only [encodeHalted, Option.map_some, encodeEntry_decode _ _ _ accepted]

structure MemoryData where
  storage : ByteStorageData.StorageData
  catalog : ObjectAccessMemory.Catalog
  deriving DecidableEq, Repr

def encodeMemory {model : Model} (memory : ObjectAccessMemory.State model.characters) : MemoryData :=
  ⟨ByteStorageData.encodeStorage memory.storage, memory.catalog⟩

def decodeMemory (model : Model) (data : MemoryData) : Option (ObjectAccessMemory.State model.characters) :=
  (ByteStorageData.decodeStorage model.characters data.storage).map (fun storage => ⟨storage, data.catalog⟩)

theorem decodeMemory_encode (model : Model) (memory : ObjectAccessMemory.State model.characters) :
    decodeMemory model (encodeMemory memory) = some memory := by
  cases memory
  simp only [encodeMemory, decodeMemory, ByteStorageData.decodeStorage_encode, Option.map_some]

theorem encodeMemory_decode (model : Model) (data : MemoryData) (memory : ObjectAccessMemory.State model.characters)
    (decoded : decodeMemory model data = some memory) : encodeMemory memory = data := by
  obtain ⟨storage, accepted, rfl⟩ := Option.map_eq_some_iff.mp decoded
  cases data
  simp only [encodeMemory, ByteStorageData.encodeStorage_decode _ _ _ accepted]

structure StateData where
  pending : List IndexData
  memory : MemoryData
  cache : List EntryData
  halted : Option EntryData
  deriving DecidableEq, Repr

def encodeState {model : Model} (expression : Expression model) (state : State (Index expression) model) : StateData :=
  ⟨encodeIndices expression state.pending, encodeMemory state.memory,
    encodeCache expression state.cache, encodeHalted expression state.halted⟩

def decodeState {model : Model} (expression : Expression model) (data : StateData) : Option (State (Index expression) model) := do
  let pending ← decodeIndices expression data.pending
  let memory ← decodeMemory model data.memory
  let cache ← decodeCache expression data.cache
  let halted ← decodeHalted expression data.halted
  some ⟨pending, memory, cache, halted⟩

theorem decodeState_encode {model : Model} (expression : Expression model) (state : State (Index expression) model) :
    decodeState expression (encodeState expression state) = some state := by
  cases state
  simp only [encodeState, decodeState, decodeIndices_encode, decodeMemory_encode, decodeCache_encode,
    decodeHalted_encode, bind, Option.bind_some]

theorem encodeState_decode {model : Model} (expression : Expression model) (data : StateData)
    (state : State (Index expression) model) (decoded : decodeState expression data = some state) :
    encodeState expression state = data := by
  simp only [decodeState, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨pending, indexed, memory, stored, cache, cached, halted, stopped, rfl⟩ := decoded
  cases data
  simp only [encodeState, encodeIndices_decode _ _ _ indexed, encodeMemory_decode _ _ _ stored,
    encodeCache_decode _ _ _ cached, encodeHalted_decode _ _ _ stopped]

structure SourceConfiguration {model : Model} (expression : Expression model) where
  state : State (Index expression) model
  selections : List (Index expression)

def toExecution {model : Model} {expression : Expression model} (configuration : SourceConfiguration expression) :
    Configuration (Index expression) model := ⟨compile expression, configuration.state, configuration.selections⟩

abbrev SourcePacket (model : Model) := (expression : Expression model) × SourceConfiguration expression

structure ConfigurationData where
  expression : ExpressionData
  state : StateData
  selections : List IndexData
  deriving DecidableEq, Repr

def encodeConfiguration {model : Model} (packet : SourcePacket model) : ConfigurationData :=
  ⟨encodeExpression packet.1, encodeState packet.1 packet.2.state, encodeIndices packet.1 packet.2.selections⟩

def decodeConfiguration (model : Model) (data : ConfigurationData) : Option (SourcePacket model) := do
  let expression ← decodeExpression model data.expression
  let state ← decodeState expression data.state
  let selections ← decodeIndices expression data.selections
  some ⟨expression, ⟨state, selections⟩⟩

theorem decodeConfiguration_encode (model : Model) (packet : SourcePacket model) :
    decodeConfiguration model (encodeConfiguration packet) = some packet := by
  cases packet with
  | mk expression configuration =>
      cases configuration
      simp only [decodeConfiguration, encodeConfiguration, decodeExpression_encode, decodeState_encode,
        decodeIndices_encode, bind, Option.bind_some]

theorem encodeConfiguration_decode (model : Model) (data : ConfigurationData) (packet : SourcePacket model)
    (decoded : decodeConfiguration model data = some packet) : encodeConfiguration packet = data := by
  simp only [decodeConfiguration, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
  obtain ⟨expression, read, state, restored, selections, indexed, rfl⟩ := decoded
  cases data
  simp only [encodeConfiguration, encodeExpression_decode _ _ _ read, encodeState_decode _ _ _ restored,
    encodeIndices_decode _ _ _ indexed]

theorem encodeConfiguration_injective (model : Model) : Function.Injective (@encodeConfiguration model) := by
  intro first second same
  have decoded := congrArg (decodeConfiguration model) same
  rw [decodeConfiguration_encode, decodeConfiguration_encode] at decoded
  exact Option.some.inj decoded

def stepData (model : Model) (policy : SignedConversionPolicy) (data : ConfigurationData) :
    Option (EntryData × ConfigurationData) := do
  let packet ← decodeConfiguration model data
  match packet.2.selections with
  | [] => none
  | index :: rest =>
      let (outcome, saved) ← ExpressionEventExecution.execute policy (compile packet.1) packet.2.state index
      some (encodeEntry packet.1 (index, outcome), encodeConfiguration ⟨packet.1, ⟨saved, rest⟩⟩)

theorem stepData_sound (model : Model) (policy : SignedConversionPolicy) (before after : ConfigurationData)
    (event : EntryData) (computed : stepData model policy before = some (event, after)) :
    ∃ (expression : Expression model) (source target : SourceConfiguration expression)
      (index : Index expression) (outcome : Outcome model),
      decodeConfiguration model before = some ⟨expression, source⟩ ∧
      decodeConfiguration model after = some ⟨expression, target⟩ ∧
      decodeEntry expression event = some (index, outcome) ∧ source.selections = index :: target.selections ∧
      ExpressionSourceExecution.Advance policy expression (represent source.state) index outcome (represent target.state) := by
  obtain ⟨⟨expression, source⟩, restored, following⟩ := Option.bind_eq_some_iff.mp computed
  cases selected : source.selections with
  | nil => simp only [selected] at following; cases following
  | cons index rest =>
      simp only [selected] at following
      obtain ⟨⟨outcome, saved⟩, executed, same⟩ := Option.bind_eq_some_iff.mp following
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      exact ⟨expression, source, ⟨saved, rest⟩, index, outcome, restored,
        decodeConfiguration_encode _ _, decodeEntry_encode _ _, selected,
        ExpressionSourceExecution.execute_sound _ _ _ _ _ _ executed⟩

theorem stepData_complete (model : Model) (policy : SignedConversionPolicy) (expression : Expression model)
    (before : State (Index expression) model) (after : SemanticState (Index expression) model)
    (index : Index expression) (outcome : Outcome model) (rest : List (Index expression))
    (advanced : ExpressionSourceExecution.Advance policy expression (represent before) index outcome after) :
    ∃ saved, represent saved = after ∧
      stepData model policy (encodeConfiguration ⟨expression, ⟨before, index :: rest⟩⟩) =
        some (encodeEntry expression (index, outcome), encodeConfiguration ⟨expression, ⟨saved, rest⟩⟩) := by
  obtain ⟨saved, executed, represented⟩ := ExpressionSourceExecution.execute_complete _ _ _ _ _ _ advanced
  exact ⟨saved, represented, by simp only [stepData, decodeConfiguration_encode, executed, bind, Option.bind_some]⟩

end Mettapedia.Languages.C11.LocatedExpressionData

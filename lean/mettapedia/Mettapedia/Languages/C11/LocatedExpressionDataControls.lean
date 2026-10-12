import Mettapedia.Languages.C11.LocatedExpressionData
import Mettapedia.Languages.C11.IntegerMemoryControls

/-!
# Located expression packet and saved-state controls

The controls exercise checked scalar/destination/address packets, retained
memory and source recomputation. Assignment's returned value can precede its
store while the complete pending modification remains in the packet. The
alternative admitted order stores first. Duplicate pending/cache identities,
old selections, invalid bytes and malformed source paths are refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.LocatedExpressionDataControls

open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution LocatedExpressionData

abbrev model := IntegerMemoryControls.model
abbrev memory := IntegerMemoryControls.initial

def character : Destination := ⟨IntegerMemoryControls.character, IntegerMemoryControls.characterType, rfl⟩
def integer : Destination := ⟨IntegerMemoryControls.integer, .int, rfl⟩
def boolean : Destination := ⟨IntegerMemoryControls.boolean, .boolean, rfl⟩
abbrev value : Expression model := .value IntegerMemoryControls.seventeen
def assignment : Expression model := .assignment character (.value IntegerMemoryControls.twoFiftyFive)

def packet (expression : Expression model) (selections : List (Index expression)) : ConfigurationData :=
  encodeConfiguration ⟨expression, ⟨initialState (compile expression) memory, selections⟩⟩

def completeValue : State (Index value) model := ⟨[], memory, [(0, .value IntegerMemoryControls.seventeen)], none⟩

private def advanceData (policy : SignedConversionPolicy) : Nat → ConfigurationData → Option (List EntryData × ConfigurationData)
  | 0, data => some ([], data)
  | count + 1, data => do
      let (event, saved) ← stepData model policy data
      let (events, final) ← advanceData policy count saved
      some (event :: events, final)

def operandIndex : Index assignment := .inl (.inl 0)
def castIndex : Index assignment := .inl (.inr 0)
def storeIndex : Index assignment := .inr 0
def resultIndex : Index assignment := .inr 1
def resultFirst : ConfigurationData := packet assignment [operandIndex, castIndex, resultIndex, storeIndex]
def storeFirst : ConfigurationData := packet assignment [operandIndex, castIndex, storeIndex, resultIndex]

theorem valid_scalar_packet_keeps_type : decodeScalar model ⟨IntegerMemoryControls.characterType, -7⟩ =
    some IntegerMemoryControls.minusSeven := by cbv

theorem invalid_scalar_packet_is_refused : decodeScalar model ⟨IntegerMemoryControls.characterType, 128⟩ = none := by cbv

theorem invalid_boolean_value_is_refused : decodeScalar model ⟨.boolean, 2⟩ = none := by cbv

theorem destination_checks_claimed_integer_type :
    decodeDestination ⟨IntegerMemoryControls.character, .int⟩ = none := by cbv

theorem destination_preserves_location_and_type : decodeDestination ⟨IntegerMemoryControls.character,
    IntegerMemoryControls.characterType⟩ = some character := by cbv

theorem nested_assignment_syntax_is_checked : decodeExpression model
    (.arithmetic .add (.assignment ⟨IntegerMemoryControls.character, IntegerMemoryControls.characterType⟩
      (.value ⟨.int, 255⟩)) (.cast .int (.load ⟨IntegerMemoryControls.integer, .int⟩))) =
      some (.arithmetic .add assignment (.cast .int (.load integer))) := by cbv

theorem malformed_destination_is_refused_inside_arbitrary_syntax : decodeExpression model
    (.comma (.value ⟨.int, 17⟩) (.assignment ⟨IntegerMemoryControls.character, .int⟩ (.value ⟨.int, 2⟩))) = none := by cbv

theorem source_leaf_index_has_one_identity : decodeIndex value (.leaf 0) = some 0 := by cbv

theorem source_leaf_index_checks_bounds : decodeIndex value (.leaf 1) = none := by cbv

theorem source_leaf_rejects_sum_path : decodeIndex value (.left (.leaf 0)) = none := by cbv

theorem assignment_store_path_is_distinct :
    (encodeIndex assignment storeIndex, encodeIndex assignment resultIndex) = (.right (.leaf 0), .right (.leaf 1)) := by cbv

theorem assignment_path_checks_two_new_occurrences : decodeIndex assignment (.right (.leaf 2)) = none := by cbv

theorem source_packet_executes_with_canonical_plan : stepData model intervalReductionPolicy (packet value [0]) =
    some ((.leaf 0, .value ⟨.int, 17⟩), encodeConfiguration ⟨value, ⟨completeValue, []⟩⟩) := by cbv

theorem repeated_selected_occurrence_is_refused : stepData model intervalReductionPolicy
    (encodeConfiguration ⟨value, ⟨completeValue, [0]⟩⟩) = none := by cbv

theorem missing_selection_keeps_packet_unadvanced : stepData model intervalReductionPolicy (packet value []) = none := by cbv

theorem duplicate_pending_occurrence_is_refused : stepData model intervalReductionPolicy
    (encodeConfiguration ⟨value, ⟨⟨[0, 0], memory, [], none⟩, [0]⟩⟩) = none := by cbv

theorem pending_key_cannot_already_be_cached : stepData model intervalReductionPolicy
    (encodeConfiguration ⟨value, ⟨⟨[0], memory, [(0, .value IntegerMemoryControls.seventeen)], none⟩, [0]⟩⟩) = none := by cbv

theorem duplicate_cached_keys_are_refused : stepData model intervalReductionPolicy
    (encodeConfiguration ⟨value, ⟨⟨[], memory, [(0, .value IntegerMemoryControls.seventeen),
      (0, .value IntegerMemoryControls.seventeen)], none⟩, [0]⟩⟩) = none := by cbv

theorem invalid_byte_packet_is_refused : decodeMemory model ⟨[(7, ⟨true, [some 256]⟩)], []⟩ = none := by cbv

theorem malformed_pending_path_is_refused : decodeConfiguration model
    { (packet value [0]) with state := { (packet value [0]).state with pending := [.right (.leaf 0)] } } = none := by cbv

theorem replacing_source_cannot_keep_an_unrelated_occurrence_path : decodeConfiguration model
    { (packet value [0]) with expression := .arithmetic .add (.value ⟨.int, 17⟩) (.value ⟨.int, 2⟩) } = none := by cbv

theorem assignment_cannot_store_before_conversion : stepData model intervalReductionPolicy (packet assignment [storeIndex]) = none := by cbv

theorem assignment_result_prefix_keeps_pending_store :
    (advanceData intervalReductionPolicy 3 resultFirst).map (fun result =>
      (result.1, result.2.state.pending, result.2.state.memory)) = some
        ([(.left (.left (.leaf 0)), .value ⟨.int, 255⟩),
          (.left (.right (.leaf 0)), .value ⟨IntegerMemoryControls.characterType, -1⟩),
          (.right (.leaf 1), .value ⟨IntegerMemoryControls.characterType, -1⟩)],
          [.right (.leaf 0)], encodeMemory memory) := by cbv

theorem assignment_store_commits_the_converted_value :
    (advanceData intervalReductionPolicy 4 resultFirst).map (fun result => (result.2.state.pending, result.2.state.memory)) =
      some ([], encodeMemory IntegerMemoryControls.afterCharacterMinusOne) := by cbv

theorem store_first_order_retains_the_distinct_receipts :
    (advanceData intervalReductionPolicy 4 storeFirst).map (fun result => (result.1.drop 2, result.2.state.memory)) = some
      ([(.right (.leaf 0), .stored ⟨IntegerMemoryControls.characterType, -1⟩),
        (.right (.leaf 1), .value ⟨IntegerMemoryControls.characterType, -1⟩)],
        encodeMemory IntegerMemoryControls.afterCharacterMinusOne) := by cbv

theorem conversion_signal_retains_memory_and_halted_occurrence :
    (advanceData (signalingPolicy 9) 2 resultFirst).map (fun result => (result.2.state.memory, result.2.state.halted)) =
      some (encodeMemory memory, some (.left (.right (.leaf 0)), .conversionSignal 9)) := by cbv

theorem selected_signal_cannot_then_commit_store :
    (advanceData (signalingPolicy 9) 3 resultFirst) = none := by cbv

theorem loaded_negative_zero_flag_is_retained : decodeOutcome model (.loaded ⟨.int, 0⟩ true) =
    some (.loaded ⟨.int, ⟨0, by decide⟩⟩ true) := by cbv

theorem arithmetic_fault_keeps_its_typed_reason : decodeOutcome model (.arithmeticFault .int .divisionByZero) =
    some (.arithmeticFault .int .divisionByZero) := by cbv

end Mettapedia.Languages.C11.LocatedExpressionDataControls

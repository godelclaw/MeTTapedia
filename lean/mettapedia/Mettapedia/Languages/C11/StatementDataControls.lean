import Mettapedia.Languages.C11.StatementDataHistory
import Mettapedia.Languages.C11.StatementControls

/-!
# Packet, scheduling and historically earned residual checks

The controls distinguish lossless structural decoding from earned histories.
They retain pending stores and the future selection suffix, reject spliced
continuations and byte-valid but unearned cache values, and check scheduling
against exact snapshots. Terminal source observations and malformed packet
verdicts remain distinct. Accounts count operational steps and deliveries;
they make no statement about compiled C instruction counts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementDataControls

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData (IndexData encodeIndex encodeMemory)
open StatementData StatementDataExecution StatementDataInteraction StatementDataHistory

abbrev model := StatementControls.model
abbrev memory := StatementControls.memory
abbrev assignment := StatementControls.assignment
abbrev value := LocatedExpressionDataControls.value
abbrev resultOrder := StatementControls.resultOrder.map (encodeIndex assignment)

def nested : Statement model := .block [
  .sequence (.expression assignment) (.conditional value .breakLoop .continueLoop),
  .whileLoop value (.block [.doLoop (.returnValue (some assignment)) value]),
  .forLoop (some assignment) (some value) (some assignment) (.returnValue none)]

theorem arbitrary_nested_statement_packet_roundtrip :
    decodeStatement model (encodeStatement nested) = some nested := decodeStatement_encode _ _

def allFrames : Continuation model := .sequence nested
  (.block [nested, .empty] (.whileBody value nested (.doBody nested value
    (.forBody (some value) (some assignment) nested .stop))))

theorem all_continuation_frames_roundtrip :
    decodeContinuation model (encodeContinuation allFrames) = some allFrames := decodeContinuation_encode _ _

def expressionFrames : List (AfterExpression model) := [
  .discard allFrames, .conditional nested .empty allFrames, .whileCondition value nested allFrames,
  .doCondition nested value allFrames, .forInitial none (some assignment) nested allFrames,
  .forCondition (some value) none nested allFrames, .forIncrement none (some assignment) nested allFrames, .returnValue]

theorem all_expression_continuations_roundtrip :
    expressionFrames.map (fun following => decodeAfterExpression model (encodeAfterExpression following)) =
      expressionFrames.map some := by
  exact List.map_congr_left (fun following _ => decodeAfterExpression_encode _ _)

private def starts : Configuration model := initial
  (.conditional assignment (.returnValue none) .empty) memory resultOrder

private def initialData : ConfigurationData := encodeConfiguration starts

private def residual (count : Nat) : ConfigurationData :=
  match replay model intervalReductionPolicy initialData (List.replicate count .tick) with
  | some (_, saved) => saved
  | none => initialData

private def prefixEvents (count : Nat) : List (Option EventData) :=
  match replay model intervalReductionPolicy initialData (List.replicate count .tick) with
  | some (events, _) => events
  | none => []

def resultPrefix : ConfigurationData := residual 4

theorem result_packet_keeps_pending_store_and_unused_suffix :
    (match resultPrefix with
      | .expression _ saved _ selections => some (saved.pending, saved.memory, selections)
      | _ => none) = some ([.right (.leaf 0)], encodeMemory memory, [.right (.leaf 0)]) := by cbv

theorem resumed_packet_commits_store_before_boundary :
    (replay model intervalReductionPolicy resultPrefix [.tick, .tick]).map (fun result =>
      match result.2 with
      | .statement _ _ saved selections => some (saved, selections)
      | _ => none) = some (some (encodeMemory IntegerMemoryControls.afterCharacterMinusOne, [])) := by cbv

theorem source_and_represented_accounts_match :
    ((machineData model intervalReductionPolicy).spent (priceData model (StatementMachine.occurrencePrice intervalReductionPolicy))
      4 initialData,
     (machineData model intervalReductionPolicy).spent (priceData model (StatementMachine.boundaryPrice intervalReductionPolicy))
      6 initialData) = (3, 1) := by cbv

def historyPrefix : HistoryData :=
  ⟨encodeStatement (.conditional assignment (.returnValue none) .empty), encodeMemory memory, resultOrder,
    List.replicate 4 .tick, prefixEvents 4, resultPrefix⟩

theorem earned_prefix_restores : restore model intervalReductionPolicy historyPrefix = some resultPrefix := by cbv

theorem earned_prefix_is_structurally_representable :
    (decodeConfiguration model resultPrefix).isSome = true := by cbv

private def forgeCachedValue : ConfigurationData → ConfigurationData
  | .expression expression saved following selections => .expression expression
      {saved with cache := saved.cache.map (fun (index, _) => (index, .value ⟨.int, 0⟩))} following selections
  | configuration => configuration

def unearned : ConfigurationData := forgeCachedValue resultPrefix

theorem byte_valid_unearned_cache_still_decodes : (decodeConfiguration model unearned).isSome = true := by cbv

theorem unearned_cache_is_not_a_historical_residual :
    restore model intervalReductionPolicy {historyPrefix with retained := unearned} = none := by cbv

private def spliceContinuation : ConfigurationData → ConfigurationData
  | .expression expression saved _ selections => .expression expression saved .returnValue selections
  | configuration => configuration

theorem structurally_valid_spliced_continuation_decodes :
    (decodeConfiguration model (spliceContinuation resultPrefix)).isSome = true := by cbv

theorem spliced_source_continuation_fails_history :
    restore model intervalReductionPolicy {historyPrefix with retained := spliceContinuation resultPrefix} = none := by cbv

def waiting : ConfigurationData := encodeConfiguration
  (.expression assignment (ExpressionEventExecution.initialState (compile assignment) memory) .returnValue [])

def waitingRequest : RequestPacket :=
  ⟨⟨LocatedExpressionData.encodeExpression assignment, [encodeIndex assignment LocatedExpressionDataControls.operandIndex]⟩, waiting⟩

theorem source_ready_scheduler_request_retains_exact_state : offer model waiting = some waitingRequest := by cbv

theorem pending_source_request_is_the_machine_suspension :
    stepData model intervalReductionPolicy waiting = some (.call waitingRequest.request waiting) :=
  offer_machine_call _ _ _ _ source_ready_scheduler_request_retains_exact_state

def response : ResponseData := ⟨waiting, encodeIndex assignment LocatedExpressionDataControls.operandIndex⟩

def delivered : ConfigurationData := encodeConfiguration
  (.expression assignment (ExpressionEventExecution.initialState (compile assignment) memory) .returnValue
    [encodeIndex assignment LocatedExpressionDataControls.operandIndex])

theorem delivery_retains_memory_and_source_residual : respond model waiting waitingRequest response = some delivered := by cbv

theorem disabled_store_cannot_be_delivered_before_conversion :
    respond model waiting waitingRequest ⟨waiting, encodeIndex assignment LocatedExpressionDataControls.storeIndex⟩ = none := by cbv

theorem reply_cannot_reuse_an_already_supplied_snapshot : respond model delivered waitingRequest response = none := by cbv

private def changeMemory : ConfigurationData → ConfigurationData
  | .expression expression saved following selections => .expression expression
      {saved with memory := encodeMemory IntegerMemoryControls.afterCharacterMinusOne} following selections
  | configuration => configuration

theorem stale_byte_valid_memory_still_has_a_representation :
    (decodeConfiguration model (changeMemory waiting)).isSome = true := by cbv

theorem stale_memory_snapshot_is_refused : respond model (changeMemory waiting) waitingRequest response = none := by cbv

theorem spliced_response_snapshot_is_refused :
    respond model waiting waitingRequest {response with snapshot := changeMemory waiting} = none := by cbv

theorem fabricated_enabled_table_is_refused :
    respond model waiting {waitingRequest with request := {waitingRequest.request with enabled := []}} response = none := by cbv

private def duplicatePending : ConfigurationData → ConfigurationData
  | .expression expression saved following selections => .expression expression
      {saved with pending := saved.pending ++ saved.pending} following selections
  | configuration => configuration

theorem duplicate_pending_packet_decodes_but_cannot_schedule :
    (decodeConfiguration model (duplicatePending waiting)).isSome = true ∧ offer model (duplicatePending waiting) = none := by cbv

private def overlapCache : ConfigurationData → ConfigurationData
  | .expression expression saved following selections => .expression expression
      {saved with cache := [(encodeIndex assignment LocatedExpressionDataControls.operandIndex, .value ⟨.int, 255⟩)]}
      following selections
  | configuration => configuration

theorem pending_cache_overlap_cannot_schedule : offer model (overlapCache waiting) = none := by cbv

private def duplicateCache : ConfigurationData → ConfigurationData
  | .expression expression saved following selections => .expression expression
      {saved with cache := saved.cache ++ saved.cache} following selections
  | configuration => configuration

theorem duplicated_cache_is_refused_as_a_step : executeData model intervalReductionPolicy (duplicateCache resultPrefix) = none := by cbv

private def malformed : ConfigurationData := .flow .normal .stop ⟨[(7, ⟨true, [some 256]⟩)], []⟩ []

theorem malformed_byte_packet_has_representation_verdict :
    (machineData model intervalReductionPolicy).step malformed = some (.finish (.malformed malformed)) := by cbv

def schedulingHistory : HistoryData := ⟨encodeStatement (.returnValue (some assignment)), encodeMemory memory,
  [], [.tick], [none], waiting⟩

theorem history_from_source_restores_scheduler_suspension :
    restore model intervalReductionPolicy schedulingHistory = some waiting := by cbv

theorem checked_scheduling_retains_an_earned_history :
    (checkedRespond model intervalReductionPolicy schedulingHistory waitingRequest response).map (fun saved =>
      (saved.commands, restore model intervalReductionPolicy saved)) =
      some ([.tick, .deliver response.choice], some delivered) := by cbv

theorem delivery_and_source_occurrences_have_separate_accounts :
    (account model intervalReductionPolicy schedulingPrice waiting [.deliver response.choice, .tick],
     account model intervalReductionPolicy (sourcePrice model (StatementMachine.occurrencePrice intervalReductionPolicy))
      waiting [.deliver response.choice, .tick]) = (1, 1) := by cbv


def division : Expression model := .arithmetic .divide (.value IntegerMemoryControls.seventeen) (.value StatementControls.zero)
def divisionSelections : List IndexData := [.left (.left (.leaf 0)), .left (.right (.leaf 0)), .right (.leaf 0)]
def divisionStart : ConfigurationData := encodeConfiguration (initial (.whileLoop division nested) memory divisionSelections)

def divisionRun := replay model intervalReductionPolicy divisionStart (List.replicate 4 .tick)

def halted : ConfigurationData := match divisionRun with
  | some (_, saved) => saved
  | none => divisionStart

theorem terminal_arithmetic_packet_keeps_fault_and_control :
    stepData model intervalReductionPolicy halted = some (.finish
      (.terminal (LocatedExpressionData.encodeExpression division) (.right (.leaf 0))
        (.arithmeticFault .int .divisionByZero) halted)) := by cbv

def faultHistory : HistoryData := ⟨encodeStatement (.whileLoop division nested), encodeMemory memory, divisionSelections,
  List.replicate 4 .tick, (divisionRun.map Prod.fst).getD [], halted⟩

theorem terminal_expression_residual_has_an_earned_source_history :
    restore model intervalReductionPolicy faultHistory = some halted := by cbv

theorem changed_observation_trace_is_refused :
    restore model intervalReductionPolicy {historyPrefix with observations := []} = none := by cbv

theorem resumed_pending_store_emits_one_stored_occurrence :
    (replay model intervalReductionPolicy resultPrefix [.tick, .tick]).map (fun result =>
      result.1.filterMap (fun event => match event with
        | some (.occurrence _ index (.stored value)) => some (index, value)
        | _ => none)) = some [(.right (.leaf 0), ⟨IntegerMemoryControls.characterType, -1⟩)] := by cbv

theorem exact_split_accounts_keep_deliveries_separate :
    (account model intervalReductionPolicy (sourcePrice model (StatementMachine.occurrencePrice intervalReductionPolicy))
      initialData (List.replicate 4 .tick ++ [.tick, .tick]),
     account model intervalReductionPolicy schedulingPrice initialData (List.replicate 4 .tick ++ [.tick, .tick])) = (4, 0) := by cbv

theorem all_flow_packets_roundtrip :
    ([Flow.normal, .broken, .continued].map (fun flow => decodeConfiguration model
      (encodeConfiguration (.flow flow allFrames memory [.right (.leaf 7)])))) =
      [Flow.normal, .broken, .continued].map (fun flow => some (.flow flow allFrames memory [.right (.leaf 7)])) := by
  exact List.map_congr_left (fun flow _ => decodeConfiguration_encode _ _)

end Mettapedia.Languages.C11.StatementDataControls

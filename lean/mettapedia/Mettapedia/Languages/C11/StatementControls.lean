import Mettapedia.Languages.C11.CestaStatements
import Mettapedia.Languages.C11.LocatedExpressionDataControls

/-!
# Full-expression, structured loop and saved-control checks

The executable controls cover a returned assignment result with an outstanding
store, postfix loop tests and return, do/while order, for increment after
continue and skipped increment after break. Terminal outcomes and source
unsequenced conflicts retain their saved expression state. Unsupported CStmt
declarations and nonlocal control are refused rather than discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementControls

open IntegerMemoryModel LocatedExpressions LocatedStatements
open LocatedExpressionData (IndexData encodeIndex encodeMemory encodeOutcome)
open StatementExecution StatementMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Machine)
open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)

abbrev model := IntegerMemoryControls.model
abbrev memory := IntegerMemoryControls.initial
abbrev character := LocatedExpressionDataControls.character
abbrev integer := LocatedExpressionDataControls.integer
abbrev assignment := LocatedExpressionDataControls.assignment
abbrev resultOrder := [LocatedExpressionDataControls.operandIndex,
  LocatedExpressionDataControls.castIndex, LocatedExpressionDataControls.resultIndex,
  LocatedExpressionDataControls.storeIndex]

def zero : IntegerScalar.Value model.parameters := ⟨.int, ⟨0, by decide⟩⟩
def one : IntegerScalar.Value model.parameters := ⟨.int, ⟨1, by decide⟩⟩
def minusIntOne : IntegerScalar.Value model.parameters := ⟨.int, ⟨-1, by decide⟩⟩

private def memoryOf : Configuration model → ObjectAccessMemory.State model.characters
  | .statement _ _ memory _ | .flow _ _ memory _ | .returned _ memory _ => memory
  | .expression _ saved _ _ => saved.memory

private def returned : Configuration model → Option (Option Int)
  | .returned value _ _ => some (value.map (fun scalar => scalar.integer.value))
  | _ => none

private def pending : Configuration model → List IndexData
  | .expression expression saved _ _ => saved.pending.map (encodeIndex expression)
  | _ => []

private def terminal : Configuration model → Option LocatedExpressionData.OutcomeData
  | .expression _ saved _ _ => saved.halted.map (fun stopped => encodeOutcome stopped.2)
  | _ => none

private def selected : Configuration model → List IndexData
  | .statement _ _ _ choices | .flow _ _ _ choices | .expression _ _ _ choices | .returned _ _ choices => choices

private def advance : Nat → Configuration model → Option (Configuration model)
  | 0, configuration => some configuration
  | count + 1, configuration => do
      let (_, following) ← execute intervalReductionPolicy configuration
      advance count following

private structure Driven where
  saved : Configuration model
  receipts : List (Receipt model)
  deliveries : Nat

private def drive (policy : SignedConversionPolicy) : Nat → Configuration model → Driven
  | 0, configuration => ⟨configuration, [], 0⟩
  | count + 1, configuration =>
      match (machine model policy).step configuration with
      | some (.silent following) => drive policy count following
      | some (.publish receipts following) =>
          let child := drive policy count following
          ⟨child.saved, receipts ++ child.receipts, child.deliveries⟩
      | some (.call request saved) =>
          match request.enabled, saved with
          | first :: _, .expression expression retained continuation choices =>
              let child := drive policy count (.expression expression retained continuation (first :: choices))
              ⟨child.saved, child.receipts, child.deliveries + 1⟩
          | _, _ => ⟨saved, [], 0⟩
      | _ => ⟨configuration, [], 0⟩

private def writes (receipts : List (Receipt model)) : List Int := receipts.filterMap (fun receipt =>
  match receipt.event with
  | .occurrence _ _ (.stored scalar) => some scalar.integer.value
  | _ => none)

private def integerRead (configuration : Configuration model) : Option Int :=
  (IntegerMemoryModel.load model (memoryOf configuration) IntegerMemoryControls.integer).bind (fun loaded =>
    match loaded with
    | .value scalar _ => some scalar.integer.value
    | _ => none)

def conditionalAssignment : Configuration model := initial
  (.conditional assignment (.returnValue none) .empty) memory (resultOrder.map (encodeIndex assignment))

theorem result_occurrence_does_not_finish_controlling_expression :
    (advance 4 conditionalAssignment).map (fun configuration => (pending configuration, encodeMemory (memoryOf configuration))) =
      some ([.right (.leaf 0)], encodeMemory memory) := by cbv

theorem condition_boundary_drains_outstanding_store :
    let configuration := (drive intervalReductionPolicy 20 conditionalAssignment).saved
    (returned configuration, encodeMemory (memoryOf configuration)) =
        (some none, encodeMemory IntegerMemoryControls.afterCharacterMinusOne) := by cbv

theorem result_prefix_preserves_unconsumed_selection :
    (advance 4 conditionalAssignment).map selected = some [.right (.leaf 0)] := by cbv

def resultPrefix := (machine model intervalReductionPolicy).run 4 conditionalAssignment

def resumedResultPrefix := match resultPrefix.2 with
  | .exhausted saved => some ((machine model intervalReductionPolicy).run 2 saved)
  | _ => none

theorem result_prefix_contains_no_committed_store : writes resultPrefix.1 = [] := by cbv

theorem resumed_prefix_commits_pending_store_once :
    resumedResultPrefix.map (fun result => writes result.1) = some [-1] := by cbv

private def prefixSaved : Configuration model := match resultPrefix.2 with
  | .exhausted saved => saved
  | _ => conditionalAssignment

theorem result_prefix_is_exhausted : resultPrefix.2 = .exhausted prefixSaved := by cbv

theorem split_prefix_agrees_with_uninterrupted_machine :
    (machine model intervalReductionPolicy).run 6 conditionalAssignment =
      (resultPrefix.1 ++ ((machine model intervalReductionPolicy).run 2 prefixSaved).1,
        ((machine model intervalReductionPolicy).run 2 prefixSaved).2) := by
  have exactPause : (machine model intervalReductionPolicy).run 4 conditionalAssignment =
      (resultPrefix.1, .exhausted prefixSaved) := Prod.ext rfl result_prefix_is_exhausted
  exact resume_after_prefix intervalReductionPolicy 4 2 conditionalAssignment prefixSaved resultPrefix.1 exactPause

theorem break_skips_for_increment :
    let result := drive intervalReductionPolicy 20 (initial
      (.forLoop none none (some assignment) .breakLoop) memory)
    (writes result.receipts, encodeMemory (memoryOf result.saved)) = ([], encodeMemory memory) := by cbv

theorem empty_omitted_condition_loop_has_visible_iterations :
    let result := drive intervalReductionPolicy 6 (initial (.forLoop none none none .empty) memory)
    result.receipts.map Receipt.event = [.iteration .forLoop, .iteration .forLoop] := by cbv

def doOnce : Configuration model := initial (.doLoop (.expression assignment) (.value zero)) memory

theorem do_executes_body_before_zero_condition :
    let result := drive intervalReductionPolicy 40 doOnce
    (writes result.receipts, encodeMemory (memoryOf result.saved)) =
      ([-1], encodeMemory IntegerMemoryControls.afterCharacterMinusOne) := by cbv

theorem while_zero_skips_body :
    let result := drive intervalReductionPolicy 12 (initial (.whileLoop (.value zero) (.expression assignment)) memory)
    (writes result.receipts, encodeMemory (memoryOf result.saved)) = ([], encodeMemory memory) := by cbv

def initialTwo : Configuration model := initial
  (.sequence (.expression (.assignment integer (.value IntegerMemoryControls.two)))
    (.whileLoop (.update integer false false) .empty)) memory

theorem postfix_condition_drains_final_modification_before_exit :
    let result := drive intervalReductionPolicy 100 initialTwo
    (integerRead result.saved, writes result.receipts) = (some (-1), [2, 1, 0, -1]) := by cbv

def continueFor : Configuration model := initial
  (.forLoop (some (.assignment integer (.value one))) (some (.load integer)) (some assignment)
    (.sequence (.expression (.update integer false false))
      (.sequence .continueLoop (.expression (.assignment character (.value zero)))))) memory

theorem continue_runs_increment_and_skips_remaining_body :
    let result := drive intervalReductionPolicy 90 continueFor
    (integerRead result.saved, writes result.receipts) = (some 0, [1, 0, -1]) := by cbv

def postfixReturn : Configuration model := initial
  (.sequence (.returnValue (some (.update integer true false))) (.expression assignment)) memory

theorem return_drains_postfix_modification_and_skips_following_statement :
    let result := drive intervalReductionPolicy 40 postfixReturn
    (returned result.saved, integerRead result.saved, writes result.receipts) = (some (some 0), some 1, [1]) := by cbv

def dividingCondition : Configuration model := initial
  (.whileLoop (.arithmetic .divide (.value IntegerMemoryControls.seventeen) (.value zero)) (.expression assignment)) memory

theorem arithmetic_fault_prevents_branch_and_preserves_memory :
    let result := drive intervalReductionPolicy 30 dividingCondition
    (terminal result.saved, writes result.receipts, encodeMemory (memoryOf result.saved)) =
      (some (.arithmeticFault .int .divisionByZero), [], encodeMemory memory) := by cbv

def retiredMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(7, ⟨false, List.replicate 32 IntegerMemoryControls.zero⟩)], IntegerMemoryControls.catalog⟩

theorem invalid_memory_load_does_not_become_successful_return :
    let result := drive intervalReductionPolicy 10
      (initial (.returnValue (some (.load integer))) retiredMemory)
    (returned result.saved, writes result.receipts, encodeMemory (memoryOf result.saved)) =
      (none, [], encodeMemory retiredMemory) := by cbv

theorem conversion_signal_prevents_branch_and_store :
    let result := drive (signalingPolicy 9) 30 conditionalAssignment
    (terminal result.saved, writes result.receipts, encodeMemory (memoryOf result.saved)) =
      (some (.conversionSignal 9), [], encodeMemory memory) := by cbv

theorem scheduling_request_keeps_expression_and_memory :
    (machine model intervalReductionPolicy).step (.expression (.value one)
      (ExpressionEventExecution.initialState (compile (.value one)) memory) (.discard .stop) []) =
        some (.call ⟨.value one, [.leaf 0]⟩ (.expression (.value one)
          (ExpressionEventExecution.initialState (compile (.value one)) memory) (.discard .stop) [])) := by cbv

theorem complete_expression_boundary_keeps_unused_future_choices :
    execute intervalReductionPolicy (.expression (.value one)
      ⟨[], memory, [(0, .value one)], none⟩ (.discard .stop) [.leaf 0]) =
      some (some (.boundary .discard (.value one) one), .flow .normal .stop memory [.leaf 0]) := by cbv

private def replaceSelections (choices : List IndexData) : Configuration model → Configuration model
  | .statement statement continuation memory _ => .statement statement continuation memory choices
  | .flow flow continuation memory _ => .flow flow continuation memory choices
  | .expression expression saved continuation _ => .expression expression saved continuation choices
  | .returned value memory _ => .returned value memory choices

theorem consumed_result_cannot_repeat_while_store_is_pending :
    (advance 4 conditionalAssignment).bind (fun saved => execute intervalReductionPolicy
      (replaceSelections [.right (.leaf 1)] saved)) = none := by cbv

def stale : Configuration model := .expression assignment
  ⟨[LocatedExpressionDataControls.storeIndex], memory,
    [(LocatedExpressionDataControls.storeIndex, .stored IntegerMemoryControls.minusOne)], none⟩
  (.conditional (.returnValue none) .empty .stop) [.right (.leaf 0)]

theorem overlapping_pending_and_cached_store_cannot_branch_or_repeat : execute intervalReductionPolicy stale = none := by cbv

def conflicting : Expression model := .arithmetic .add (.update integer true false) (.load integer)

theorem unsequenced_access_is_not_admitted : ExpressionEventExecution.admissible (compile conflicting) = false := by cbv

theorem unsequenced_access_stops_before_commits :
    let result := drive intervalReductionPolicy 20 (initial (.expression conflicting) memory)
    (result.receipts, encodeMemory (memoryOf result.saved)) = ([], encodeMemory memory) := by
  have found : ∃ first second, (compile conflicting).component.evaluation.findConflict
      (compile conflicting).component.enumeration = some (first, second) := by
    cases conflict : (compile conflicting).component.evaluation.findConflict (compile conflicting).component.enumeration with
    | none =>
        have forbidden := unsequenced_access_is_not_admitted
        simp only [ExpressionEventExecution.admissible, conflict, decide_true] at forbidden
        contradiction
    | some pair => cases pair; exact ⟨_, _, rfl⟩
  obtain ⟨first, second, conflict⟩ := found
  have opening : (machine model intervalReductionPolicy).step (initial (.expression conflicting) memory) =
      some (.silent (.expression conflicting (ExpressionEventExecution.initialState (compile conflicting) memory)
        (.discard .stop) [])) := step_of_execute intervalReductionPolicy
          (initial (.expression conflicting) memory)
          (.expression conflicting (ExpressionEventExecution.initialState (compile conflicting) memory)
            (.discard .stop) []) none rfl
  have stopping := (conflict_reported intervalReductionPolicy conflicting
    (ExpressionEventExecution.initialState (compile conflicting) memory) (.discard .stop) [] first second conflict).1
  simp only [drive, opening, stopping]
  rfl

def noExpression : CanonicalTerm := .node "NoFullExpression" []
def emptyStatement : CanonicalTerm := .node "ExpressionStatement" [noExpression]

theorem actual_cstmt_empty_expression_reads : CestaStatements.readStatement model [] emptyStatement = some .empty := by
  exact CestaStatements.readStatement_complete _ _ _ _ (.expression _ _ .omitted)

theorem actual_cstmt_omitted_for_reads : CestaStatements.readStatement model []
    (.node "IterationStatement" [.node "For" [noExpression, noExpression, noExpression,
      .node "JumpStatement" [.node "Break" []]]]) = some (.forLoop none none none .breakLoop) := by
  exact CestaStatements.readStatement_complete _ _ _ _
    (.forLoop _ _ _ _ _ _ _ _ .omitted .omitted .omitted .breakLoop)

theorem actual_cstmt_nested_block_preserves_order : CestaStatements.readStatement model []
    (.node "CompoundStatement" [.node "Block" [.seq [
      .node "BlockStatement" [emptyStatement],
      .node "BlockStatement" [.node "JumpStatement" [.node "Return" [noExpression]]]]]]) =
        some (.block [.empty, .returnValue none]) := by
  exact CestaStatements.readStatement_complete _ _ _ _
    (.compound _ _ (.cons _ _ _ _ (.expression _ _ .omitted)
      (.cons _ _ _ _ (.returnValue _ _ .omitted) .nil)))

theorem declaration_is_not_erased_from_block : CestaStatements.readStatement model []
    (.node "CompoundStatement" [.node "Block" [.seq [
      .node "BlockStatement" [emptyStatement], .node "BlockDeclaration" [.node "Declaration" []]]]]) = none := by
  have unsupported : CestaStatements.readItems model []
      [.node "BlockDeclaration" [.node "Declaration" []]] = none := by
    unfold CestaStatements.readItems
    rfl
  simp only [CestaStatements.readStatement, CestaStatements.readItems,
    actual_cstmt_empty_expression_reads, unsupported, bind, Option.bind_some, Option.bind_none, Option.map_none]

theorem declaration_for_is_not_replaced_with_expression_for : CestaStatements.readStatement model []
    (.node "IterationStatement" [.node "ForDeclaration" [.node "Declaration" [],
      noExpression, noExpression, emptyStatement]]) = none := by
  unfold CestaStatements.readStatement
  rfl

theorem malformed_statement_wrapper_is_refused : CestaStatements.readStatement model []
    (.node "IterationStatement" [.node "Break" []]) = none := by
  unfold CestaStatements.readStatement
  rfl

theorem unsupported_goto_is_not_silent : CestaStatements.readStatement model []
    (.node "JumpStatement" [.node "Goto" [.text "label"]]) = none := by
  unfold CestaStatements.readStatement
  rfl

end Mettapedia.Languages.C11.StatementControls

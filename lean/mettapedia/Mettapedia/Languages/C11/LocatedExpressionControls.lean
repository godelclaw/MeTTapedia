import Mettapedia.Languages.C11.ExpressionSourceHistory
import Mettapedia.Languages.C11.IntegerMemoryControls

/-!
# Effectful integer-expression controls

The controls retain a source-generated plan and one complete mixed-width
memory. They distinguish value computation from pending stores, compare
permitted schedules, reject source-unsequenced aliases before executing
memory occurrences, and retain exact effects across a paused prefix.
Undefined arithmetic, conversion signals, object traps and refused memory
admission remain separate observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.LocatedExpressionControls

open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution
open ExpressionSourceActions ExpressionSourceExecution ExpressionSourceHistory ExpressionEventHistory
open IntegerMemoryControls

def intDestination : Destination := ⟨integer, .int, rfl⟩
def charDestination : Destination := ⟨character, characterType, rfl⟩
def boolDestination : Destination := ⟨boolean, .boolean, rfl⟩
def one : IntegerScalar.Value model.parameters := ⟨.int, ⟨1, by decide⟩⟩
def intZero : IntegerScalar.Value model.parameters := ⟨.int, ⟨0, by decide⟩⟩

def assignment : Expression model := .assignment intDestination (.value seventeen)
abbrev literalIndex : Index assignment := .inl (.inl 0)
abbrev conversionIndex : Index assignment := .inl (.inr 0)
abbrev storeIndex : Index assignment := .inr 0
abbrev valueIndex : Index assignment := .inr 1
def valueFirst : List (Index assignment) := [literalIndex, conversionIndex, valueIndex, storeIndex]
def storeFirst : List (Index assignment) := [literalIndex, conversionIndex, storeIndex, valueIndex]

def postfixUpdate : Expression model := .update intDestination true false
def prefixUpdate : Expression model := .update intDestination true true
def copyFirst : List UpdateIndex := [oldRead, oneValue, updateValue, convertedUpdate, .inr 1, .inr 0]

def scalarNumber {m : Model} (scalar : IntegerScalar.Value m.parameters) : Int := scalar.integer.value
def outcomeNumber {m : Model} (outcome : Outcome m) : Option Int := outcome.scalar.map scalarNumber
def loadedNumber (loaded : Loaded model) : Option Int := (loadedOutcome model loaded).scalar.map scalarNumber

structure Probe where
  observations : List (Option Int)
  result : Option Int
  integer : Option Int
  pending : Nat
  stores : Nat
  finished : Bool
  deriving DecidableEq, Repr

def isStore (outcome : Outcome model) : Bool := match outcome with | .stored _ => true | _ => false
def finished {expression : Expression model} :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Configuration (Index expression) model)
      (Verdict (Index expression) model) (SelectionRequest (Index expression)) → Bool
  | .finished _ => true
  | _ => false

def probe (policy : SignedConversionPolicy) (fuel : Nat) (expression : Expression model)
    (selections : List (Index expression)) : Option Probe := do
  let evaluated := (machine model policy).run fuel (begin expression initial selections)
  let saved ← endpoint evaluated.2
  some ⟨evaluated.1.map (fun receipt => outcomeNumber receipt.outcome),
    (lookupScalar saved.state.cache saved.plan.component.result).map scalarNumber,
    (IntegerMemoryModel.load model saved.state.memory integer).bind loadedNumber,
    saved.state.pending.length, (evaluated.1.filter (fun receipt => isStore receipt.outcome)).length,
    finished evaluated.2⟩

theorem assignment_value_retains_pending_store : probe intervalReductionPolicy 3 assignment valueFirst =
    some ⟨[some 17, some 17, some 17], some 17, some 0, 1, 0, false⟩ := by cbv

theorem assignment_store_first : probe intervalReductionPolicy 5 assignment storeFirst =
    some ⟨[some 17, some 17, some 17, some 17], some 17, some 17, 0, 1, true⟩ := by cbv

theorem assignment_value_first : probe intervalReductionPolicy 5 assignment valueFirst =
    some ⟨[some 17, some 17, some 17, some 17], some 17, some 17, 0, 1, true⟩ := by cbv

theorem assignment_source_does_not_order_store_and_value :
    ¬ ExpressionSourceOrder.Before assignment storeIndex valueIndex ∧
      ¬ ExpressionSourceOrder.Before assignment valueIndex storeIndex := by
  have unsequenced := assignment_store_result_unsequenced intDestination (.value seventeen)
  exact ⟨fun ordered => unsequenced.2.1 ((ExpressionSourceOrder.compiled_order_iff _ _ _).mpr ordered),
    fun ordered => unsequenced.2.2 ((ExpressionSourceOrder.compiled_order_iff _ _ _).mpr ordered)⟩

theorem postfix_old_value_precedes_pending_update : probe intervalReductionPolicy 4 postfixUpdate copyFirst =
    some ⟨[some 0, some 1, some 1, some 1], some 0, some 0, 2, 0, false⟩ := by cbv

theorem prefix_value_can_precede_store : probe intervalReductionPolicy 5 prefixUpdate copyFirst =
    some ⟨[some 0, some 1, some 1, some 1, some 1], some 1, some 0, 1, 0, false⟩ := by cbv

theorem postfix_final_old_value_and_new_memory : probe intervalReductionPolicy 7 postfixUpdate copyFirst =
    some ⟨[some 0, some 1, some 1, some 1, some 1, some 1], some 0, some 1, 0, 1, true⟩ := by cbv

theorem prefix_final_new_value_and_new_memory : probe intervalReductionPolicy 7 prefixUpdate copyFirst =
    some ⟨[some 0, some 1, some 1, some 1, some 1, some 1], some 1, some 1, 0, 1, true⟩ := by cbv

def sequenced : Expression model := .comma assignment (.load intDestination)
def occurrences (expression : Expression model) : List (Index expression) :=
  (compile expression).component.enumeration.items

theorem comma_read_observes_committed_assignment : probe intervalReductionPolicy 7 sequenced (occurrences sequenced) =
    some ⟨[some 17, some 17, some 17, some 17, some 17, some 17], some 17, some 17, 0, 1, true⟩ := by cbv

def doubleWrite : Expression model := .arithmetic .add (.assignment intDestination (.value one))
  (.assignment intDestination (.value two))
def updateRead : Expression model := .arithmetic .add postfixUpdate (.load intDestination)
def selfPostAssignment : Expression model := .assignment intDestination postfixUpdate

theorem unsequenced_writes_are_not_admitted : admissible (compile doubleWrite) = false := by cbv
theorem unsequenced_postfix_read_is_not_admitted : admissible (compile updateRead) = false := by cbv
theorem assignment_cannot_hide_postfix_modification : admissible (compile selfPostAssignment) = false := by cbv

theorem serializing_unsequenced_writes_does_not_execute_them :
    ((machine model intervalReductionPolicy).run 100 (begin doubleWrite initial (occurrences doubleWrite))).1 = [] := by cbv

theorem empty_choice_requests_enabled_occurrences :
    (machine model intervalReductionPolicy).step (begin assignment initial []) =
      some (.call ⟨[literalIndex]⟩ (begin assignment initial [])) := by cbv

theorem premature_store_refuses_without_modification :
    ((machine model intervalReductionPolicy).run 5 (begin assignment initial [storeIndex])).1 = [] := by cbv

theorem repeated_literal_is_not_replayed :
    (((machine model intervalReductionPolicy).run 5
      (begin assignment initial [literalIndex, literalIndex, conversionIndex, storeIndex, valueIndex])).1.map Receipt.index) =
        [literalIndex] := by cbv

def prefixRun := (machine model intervalReductionPolicy).run 3 (begin assignment initial valueFirst)
def resumed := do
  let saved ← endpoint prefixRun.2
  some ((machine model intervalReductionPolicy).run 2 saved)

theorem resumed_store_occurs_once :
    (resumed.map (fun run => (run.1.filter (fun receipt => isStore receipt.outcome)).length)) = some 1 := by cbv

theorem prefix_receipts_contain_no_store : (prefixRun.1.filter (fun receipt => isStore receipt.outcome)).length = 0 := by cbv

theorem resumed_occurrences_are_disjoint_from_prefix :
    (resumed.map (fun run => run.1.map Receipt.index)) = some [storeIndex] := by cbv

def narrowSignal : Expression model := .assignment charDestination (.value twoFiftyFive)

theorem conversion_signal_stops_before_store :
    (((machine model (signalingPolicy 9)).run 6 (begin narrowSignal initial (occurrences narrowSignal))).1.map Receipt.outcome) =
      [.value twoFiftyFive, .conversionSignal 9] := by cbv

theorem conversion_signal_retains_initial_memory :
    (endpoint ((machine model (signalingPolicy 9)).run 6 (begin narrowSignal initial (occurrences narrowSignal))).2).map
      (fun saved => saved.state.memory) = some initial := by cbv

def maximum : IntegerScalar.Value model.parameters := ⟨.int, ⟨2147483647, by decide⟩⟩
def overflow : Expression model := .arithmetic .add (.value maximum) (.value one)

theorem overflow_is_an_exact_terminal_occurrence :
    (((machine model intervalReductionPolicy).run 6 (begin overflow initial (occurrences overflow))).1.map Receipt.outcome) =
      [.value maximum, .value one, .arithmeticFault .int .overflow] := by cbv

def divideByZero : Expression model := .arithmetic .divide (.value one) (.value intZero)
theorem division_by_zero_is_distinct_from_refusal :
    (((machine model intervalReductionPolicy).run 6 (begin divideByZero initial (occurrences divideByZero))).1.map Receipt.outcome) =
      [.value one, .value intZero, .arithmeticFault .int .divisionByZero] := by cbv

def badBooleanMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(7, ⟨true, List.replicate 16 zero ++ some (byte 2) :: List.replicate 15 zero⟩)], catalog⟩
def booleanRead : Expression model := .load boolDestination

theorem invalid_boolean_word_retains_padding_trap :
    (((machine model intervalReductionPolicy).run 3 (begin booleanRead badBooleanMemory (occurrences booleanRead))).1.map Receipt.outcome) =
      [.paddingTrap .boolean] := by cbv

def deadMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(7, ⟨false, List.replicate 32 zero⟩)], catalog⟩
def intRead : Expression model := .load intDestination

theorem ended_lifetime_is_refused_before_receipt :
    ((machine model intervalReductionPolicy).run 3 (begin intRead deadMemory (occurrences intRead))).1 = [] := by cbv

end Mettapedia.Languages.C11.LocatedExpressionControls

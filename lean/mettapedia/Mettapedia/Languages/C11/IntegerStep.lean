import Mettapedia.Languages.C11.IntegerArithmetic
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Represented C11 integer reductions

The configuration retains one conversion or one operation on already-promoted
integer operands. Its data representation carries precisions, signed
representations, operators and values explicitly. Decoding checks precision
and operand ranges; an invalid representation has no decoded configuration.
It is not classified as undefined C execution.

The language reduction relation uses the declarative conversion and arithmetic
relations. The executable step uses their independently qualified algorithms.
A labelled driver exposes the result occurrence and then completion, using
the common prefix/residual interface. Its charge is one numeric reduction;
neither the charge nor the inspection budget measures physical arithmetic
work. Enclosing C expressions, memory, contexts, sequencing and native syntax
admission require their separate configuration and representation contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerStep

open Mettapedia.GSLT.Distinction.ProductiveBlocks

inductive Instruction where
  | conversion (input : Int) (destination : ConversionDestination)
  | binary (format : IntegerFormat) (operation : IntegerBinaryOperator)
      (left right : IntegerValue format)
  deriving DecidableEq, Repr

inductive Result where
  | conversion (outcome : ConversionOutcome)
  | binary (outcome : IntegerArithmeticOutcome)
  deriving DecidableEq, Repr

inductive Configuration where
  | pending (instruction : Instruction)
  | completed (result : Result)
  deriving DecidableEq, Repr

def execute (policy : SignedConversionPolicy) : Instruction → Result
  | .conversion input destination => .conversion (convertInteger policy input destination)
  | .binary format operation left right => .binary (evaluateIntegerBinary format operation left right)

inductive Reduction (policy : SignedConversionPolicy) : Configuration → Configuration → Prop where
  | conversion (input : Int) (destination : ConversionDestination) (outcome : ConversionOutcome)
      (converted : IntegerConverts policy input destination outcome) :
      Reduction policy (.pending (.conversion input destination)) (.completed (.conversion outcome))
  | binary (format : IntegerFormat) (operation : IntegerBinaryOperator)
      (left right : IntegerValue format) (outcome : IntegerArithmeticOutcome)
      (evaluated : IntegerBinaryEvaluation format left right operation outcome) :
      Reduction policy (.pending (.binary format operation left right)) (.completed (.binary outcome))

def step (policy : SignedConversionPolicy) : Configuration → Option Configuration
  | .pending instruction => some (.completed (execute policy instruction))
  | .completed _ => none

theorem step_sound (policy : SignedConversionPolicy) (before after : Configuration)
    (stepped : step policy before = some after) : Reduction policy before after := by
  cases before with
  | completed result => cases stepped
  | pending instruction =>
      have equality : Configuration.completed (execute policy instruction) = after := Option.some.inj stepped
      rw [← equality]
      cases instruction with
      | conversion input destination =>
          exact Reduction.conversion input destination _ (convertInteger_sound policy input destination)
      | binary format operation left right =>
          exact Reduction.binary format operation left right _
            (evaluateIntegerBinary_sound format operation left right)

theorem step_complete (policy : SignedConversionPolicy) (before after : Configuration)
    (reduced : Reduction policy before after) : step policy before = some after := by
  cases reduced with
  | conversion input destination outcome converted =>
      simp only [step, execute, convertInteger_complete policy input destination outcome converted]
  | binary format operation left right outcome evaluated =>
      simp only [step, execute,
        evaluateIntegerBinary_complete format operation left right outcome evaluated]

theorem step_iff (policy : SignedConversionPolicy) (before after : Configuration) :
    step policy before = some after ↔ Reduction policy before after :=
  ⟨step_sound policy before after, step_complete policy before after⟩

inductive FormatData where
  | unsigned (precision : Nat)
  | signed (precision : Nat) (representation : SignedRepresentation)
  deriving DecidableEq, Repr

def encodeFormat : IntegerFormat → FormatData
  | .unsigned precision _ => .unsigned precision
  | .signed precision _ representation => .signed precision representation

def decodeFormat : FormatData → Option IntegerFormat
  | .unsigned precision =>
      if positive : 0 < precision then some (.unsigned precision positive) else none
  | .signed precision representation =>
      if positive : 0 < precision then some (.signed precision positive representation) else none

theorem decodeFormat_encode (format : IntegerFormat) : decodeFormat (encodeFormat format) = some format := by
  cases format with
  | unsigned precision positive => simp only [encodeFormat, decodeFormat, dif_pos positive]
  | signed precision positive representation => simp only [encodeFormat, decodeFormat, dif_pos positive]

theorem encodeFormat_decode (data : FormatData) (format : IntegerFormat)
    (decoded : decodeFormat data = some format) : encodeFormat format = data := by
  cases data with
  | unsigned precision =>
      by_cases positive : 0 < precision
      · simp only [decodeFormat, dif_pos positive] at decoded
        cases decoded
        rfl
      · simp only [decodeFormat, dif_neg positive] at decoded
        cases decoded
  | signed precision representation =>
      by_cases positive : 0 < precision
      · simp only [decodeFormat, dif_pos positive] at decoded
        cases decoded
        rfl
      · simp only [decodeFormat, dif_neg positive] at decoded
        cases decoded

inductive DestinationData where
  | boolean
  | integer (format : FormatData)
  deriving DecidableEq, Repr

def encodeDestination : ConversionDestination → DestinationData
  | .boolean => .boolean
  | .integer format => .integer (encodeFormat format)

def decodeDestination : DestinationData → Option ConversionDestination
  | .boolean => some .boolean
  | .integer format => (decodeFormat format).map ConversionDestination.integer

theorem decodeDestination_encode (destination : ConversionDestination) :
    decodeDestination (encodeDestination destination) = some destination := by
  cases destination <;>
    simp only [encodeDestination, decodeDestination, decodeFormat_encode, Option.map_some]

theorem encodeDestination_decode (data : DestinationData) (destination : ConversionDestination)
    (decoded : decodeDestination data = some destination) : encodeDestination destination = data := by
  cases data with
  | boolean => cases decoded; rfl
  | integer wire =>
      cases formatEqual : decodeFormat wire with
      | none =>
          simp only [decodeDestination, formatEqual, Option.map_none] at decoded
          cases decoded
      | some format =>
          simp only [decodeDestination, formatEqual, Option.map_some] at decoded
          cases decoded
          exact congrArg DestinationData.integer (encodeFormat_decode wire format formatEqual)

def decodeValue (format : IntegerFormat) (integer : Int) : Option (IntegerValue format) :=
  if valid : format.Represents integer then some ⟨integer, valid⟩ else none

theorem decodeValue_encode (format : IntegerFormat) (value : IntegerValue format) :
    decodeValue format value.value = some value := by
  cases value with
  | mk integer valid => simp only [decodeValue, dif_pos valid]

theorem value_decode (format : IntegerFormat) (integer : Int) (value : IntegerValue format)
    (decoded : decodeValue format integer = some value) : value.value = integer := by
  by_cases valid : format.Represents integer
  · simp only [decodeValue, dif_pos valid] at decoded
    cases decoded
    rfl
  · simp only [decodeValue, dif_neg valid] at decoded
    cases decoded

inductive InstructionData where
  | conversion (input : Int) (destination : DestinationData)
  | binary (format : FormatData) (operation : IntegerBinaryOperator) (left right : Int)
  deriving DecidableEq, Repr

def encodeInstruction : Instruction → InstructionData
  | .conversion input destination => .conversion input (encodeDestination destination)
  | .binary format operation left right => .binary (encodeFormat format) operation left.value right.value

def decodeInstruction : InstructionData → Option Instruction
  | .conversion input destination =>
      (decodeDestination destination).map (Instruction.conversion input)
  | .binary data operation left right => do
      let format ← decodeFormat data
      let first ← decodeValue format left
      let second ← decodeValue format right
      some (.binary format operation first second)

theorem decodeInstruction_encode (instruction : Instruction) :
    decodeInstruction (encodeInstruction instruction) = some instruction := by
  cases instruction <;>
    simp only [encodeInstruction, decodeInstruction, decodeDestination_encode, Option.map_some,
      decodeFormat_encode, bind, Option.bind_some, decodeValue_encode]

theorem encodeInstruction_decode (data : InstructionData) (instruction : Instruction)
    (decoded : decodeInstruction data = some instruction) : encodeInstruction instruction = data := by
  cases data with
  | conversion input destination =>
      cases destinationEqual : decodeDestination destination with
      | none =>
          simp only [decodeInstruction, destinationEqual, Option.map_none] at decoded
          cases decoded
      | some actual =>
          simp only [decodeInstruction, destinationEqual, Option.map_some] at decoded
          cases decoded
          exact congrArg (InstructionData.conversion input)
            (encodeDestination_decode destination actual destinationEqual)
  | binary data operation left right =>
      cases formatEqual : decodeFormat data with
      | none =>
          simp only [decodeInstruction, formatEqual, bind, Option.bind_none] at decoded
          cases decoded
      | some format =>
          cases firstEqual : decodeValue format left with
          | none =>
              simp only [decodeInstruction, formatEqual, firstEqual, bind,
                Option.bind_some, Option.bind_none] at decoded
              cases decoded
          | some first =>
              cases secondEqual : decodeValue format right with
              | none =>
                  simp only [decodeInstruction, formatEqual, firstEqual, secondEqual,
                    bind, Option.bind_some, Option.bind_none] at decoded
                  cases decoded
              | some second =>
                  simp only [decodeInstruction, formatEqual, firstEqual, secondEqual,
                    bind, Option.bind_some] at decoded
                  cases decoded
                  simp only [encodeInstruction, encodeFormat_decode data format formatEqual,
                    value_decode format left first firstEqual,
                    value_decode format right second secondEqual]

inductive ConfigurationData where
  | pending (instruction : InstructionData)
  | completed (result : Result)
  deriving DecidableEq, Repr

def encode : Configuration → ConfigurationData
  | .pending instruction => .pending (encodeInstruction instruction)
  | .completed result => .completed result

def decode : ConfigurationData → Option Configuration
  | .pending instruction => (decodeInstruction instruction).map Configuration.pending
  | .completed result => some (.completed result)

theorem decode_encode (configuration : Configuration) : decode (encode configuration) = some configuration := by
  cases configuration <;>
    simp only [encode, decode, decodeInstruction_encode, Option.map_some]

theorem encode_decode (data : ConfigurationData) (configuration : Configuration)
    (decoded : decode data = some configuration) : encode configuration = data := by
  cases data with
  | completed result => cases decoded; rfl
  | pending instruction =>
      cases instructionEqual : decodeInstruction instruction with
      | none =>
          simp only [decode, instructionEqual, Option.map_none] at decoded
          cases decoded
      | some actual =>
          simp only [decode, instructionEqual, Option.map_some] at decoded
          cases decoded
          exact congrArg ConfigurationData.pending
            (encodeInstruction_decode instruction actual instructionEqual)

def stepData (policy : SignedConversionPolicy) (data : ConfigurationData) : Option ConfigurationData := do
  let before ← decode data
  let after ← step policy before
  some (encode after)

theorem stepData_sound (policy : SignedConversionPolicy) (before after : ConfigurationData)
    (stepped : stepData policy before = some after) :
    ∃ source target : Configuration, decode before = some source ∧ decode after = some target ∧
      Reduction policy source target := by
  cases beforeEqual : decode before with
  | none =>
      simp only [stepData, beforeEqual, bind, Option.bind_none] at stepped
      cases stepped
  | some source =>
      cases afterEqual : step policy source with
      | none =>
          simp only [stepData, beforeEqual, afterEqual, bind,
            Option.bind_some, Option.bind_none] at stepped
          cases stepped
      | some target =>
          simp only [stepData, beforeEqual, afterEqual, bind, Option.bind_some] at stepped
          cases stepped
          exact ⟨source, target, rfl, decode_encode target, step_sound policy source target afterEqual⟩

theorem stepData_complete (policy : SignedConversionPolicy) (before after : Configuration)
    (reduced : Reduction policy before after) :
    stepData policy (encode before) = some (encode after) := by
  simp only [stepData, decode_encode, step_complete policy before after reduced,
    bind, Option.bind_some]

theorem stepData_iff (policy : SignedConversionPolicy) (before after : ConfigurationData) :
    stepData policy before = some after ↔
      ∃ source target : Configuration, decode before = some source ∧ decode after = some target ∧
        Reduction policy source target := by
  constructor
  · exact stepData_sound policy before after
  · rintro ⟨source, target, beforeEqual, afterEqual, reduced⟩
    rw [← encode_decode before source beforeEqual, ← encode_decode after target afterEqual]
    exact stepData_complete policy source target reduced

theorem encode_injective : Function.Injective encode := by
  intro first second equal
  have decoded := congrArg decode equal
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

structure Receipt where
  instruction : Instruction
  result : Result
  deriving DecidableEq, Repr

def machine (policy : SignedConversionPolicy) : Machine Configuration Receipt Result Empty where
  step
    | .pending instruction => some (.publish [⟨instruction, execute policy instruction⟩]
        (.completed (execute policy instruction)))
    | .completed result => some (.finish result)

def ValidReceipt (policy : SignedConversionPolicy) (receipt : Receipt) : Prop :=
  Reduction policy (.pending receipt.instruction) (.completed receipt.result)

theorem execute_reduction (policy : SignedConversionPolicy) (instruction : Instruction) :
    Reduction policy (.pending instruction) (.completed (execute policy instruction)) :=
  step_sound policy _ _ rfl

theorem completed_has_no_receipts (policy : SignedConversionPolicy) (fuel : Nat) (result : Result) :
    ((machine policy).run fuel (.completed result)).1 = [] := by
  cases fuel <;> rfl

theorem run_receipts_valid (policy : SignedConversionPolicy) (fuel : Nat)
    (initial : Configuration) :
    ∀ receipt ∈ ((machine policy).run fuel initial).1, ValidReceipt policy receipt := by
  cases fuel with
  | zero => simp only [Machine.run, List.not_mem_nil, false_implies, implies_true]
  | succ fuel =>
      cases initial with
      | completed result => simp only [Machine.run, machine, List.not_mem_nil, false_implies, implies_true]
      | pending instruction =>
          intro receipt member
          change receipt ∈ [⟨instruction, execute policy instruction⟩] ++
            ((machine policy).run fuel (.completed (execute policy instruction))).1 at member
          rw [completed_has_no_receipts] at member
          simp only [List.append_nil, List.mem_singleton] at member
          subst receipt
          exact execute_reduction policy instruction

def price : Configuration → Nat
  | .pending _ => 1
  | .completed _ => 0

theorem run_one_retains_the_completed_configuration (policy : SignedConversionPolicy) (instruction : Instruction) :
    (machine policy).run 1 (.pending instruction) =
      ⟨[⟨instruction, execute policy instruction⟩], .exhausted (.completed (execute policy instruction))⟩ := rfl

theorem run_two_finishes_with_one_occurrence (policy : SignedConversionPolicy) (instruction : Instruction) :
    (machine policy).run 2 (.pending instruction) =
      ⟨[⟨instruction, execute policy instruction⟩], .finished (execute policy instruction)⟩ := rfl

theorem run_two_has_one_reduction_charge (policy : SignedConversionPolicy) (instruction : Instruction) :
    (machine policy).spent price 2 (.pending instruction) = 1 := rfl

theorem resume_after_prefix (policy : SignedConversionPolicy) (first second : Nat)
    (initial saved : Configuration) (events : List Receipt)
    (paused : (machine policy).run first initial = ⟨events, .exhausted saved⟩) :
    (machine policy).run (first + second) initial =
      (events ++ ((machine policy).run second saved).1,
        ((machine policy).run second saved).2) :=
  (machine policy).established_and_pending first second initial saved events paused

def productive (policy : SignedConversionPolicy) : (machine policy).Productive where
  rank _ := 0
  moves state := by cases state <;> simp [machine]
  silent_decreases := by
    intro state next silent
    cases state <;> simp [machine] at silent

end Mettapedia.Languages.C11.IntegerStep

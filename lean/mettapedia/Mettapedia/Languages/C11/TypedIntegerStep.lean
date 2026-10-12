import Mettapedia.Languages.C11.TypedIntegerArithmetic
import Mettapedia.Languages.C11.IntegerStep

/-!
# Represented integer reductions with source operand types

A pending reduction retains both original canonical integer types, their
values and the operator. Decoding checks each value against its original
type. Execution performs promotions and the usual arithmetic conversions,
then returns the common type and the arithmetic outcome. The data codec has
both inverse laws; its executable step corresponds in both directions to
the independently composed conversion/arithmetic judgment.

Lowering constructs an existing already-promoted numeric instruction. Its
reduction is proved, while the typed interface retains the original and
result type identities that this numeric view omits. A common labelled
driver exposes one reduction receipt and its retained terminal state.
One charged reduction includes its numeric conversions; it does not measure
compiler instructions or physical arithmetic work.

These are numeric C expression components, not whole C configurations.
Decoding constructs a valid numeric state, not proof of its execution history
or authority to publish external effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.TypedIntegerStep

universe u

open Mettapedia.GSLT.Distinction.ProductiveBlocks

structure Input {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  operation : IntegerBinaryOperator
  leftType : IntegerType Extension
  rightType : IntegerType Extension
  left : IntegerValue (leftType.format parameters)
  right : IntegerValue (rightType.format parameters)
  deriving DecidableEq, Repr

def execute {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (input : Input parameters) : TypedIntegerOutcome Extension :=
  evaluateTypedIntegerBinary parameters input.operation input.leftType input.rightType input.left input.right

inductive Configuration {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  | pending (input : Input parameters)
  | completed (outcome : TypedIntegerOutcome Extension)
  deriving DecidableEq, Repr

inductive Reduction {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) : Configuration parameters → Configuration parameters → Prop where
  | arithmetic (input : Input parameters) (outcome : TypedIntegerOutcome Extension)
      (computed : TypedIntegerBinaryEvaluation parameters policy input.operation
        input.leftType input.rightType input.left input.right outcome) :
      Reduction parameters policy (.pending input) (.completed outcome)

def step {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) : Configuration parameters → Option (Configuration parameters)
  | .pending input => some (.completed (execute parameters input))
  | .completed _ => none

theorem step_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : Configuration parameters) (stepped : step parameters before = some after) :
    Reduction parameters policy before after := by
  cases before with
  | completed outcome => cases stepped
  | pending input =>
      have equal : Configuration.completed (execute parameters input) = after := Option.some.inj stepped
      rw [← equal]
      exact .arithmetic input _ (evaluateTypedIntegerBinary_sound parameters policy _ _ _ _ _)

theorem step_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : Configuration parameters) (reduced : Reduction parameters policy before after) :
    step parameters before = some after := by
  cases reduced with
  | arithmetic input outcome computed =>
      simp only [step, execute,
        evaluateTypedIntegerBinary_complete parameters policy _ _ _ _ _ outcome computed]

theorem step_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : Configuration parameters) :
    step parameters before = some after ↔ Reduction parameters policy before after :=
  ⟨step_sound parameters policy before after, step_complete parameters policy before after⟩

structure InputData (Extension : Type u) where
  operation : IntegerBinaryOperator
  leftType : IntegerType Extension
  rightType : IntegerType Extension
  left : Int
  right : Int
  deriving DecidableEq, Repr

def encodeInput {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    (input : Input parameters) : InputData Extension :=
  ⟨input.operation, input.leftType, input.rightType, input.left.value, input.right.value⟩

def decodeInput {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (data : InputData Extension) : Option (Input parameters) :=
  match IntegerStep.decodeValue (data.leftType.format parameters) data.left with
  | none => none
  | some left =>
      match IntegerStep.decodeValue (data.rightType.format parameters) data.right with
      | none => none
      | some right => some ⟨data.operation, data.leftType, data.rightType, left, right⟩

theorem decodeInput_encode {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (input : Input parameters) : decodeInput parameters (encodeInput input) = some input := by
  cases input
  simp only [encodeInput, decodeInput, IntegerStep.decodeValue_encode]

theorem encodeInput_decode {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (data : InputData Extension) (input : Input parameters) (decoded : decodeInput parameters data = some input) :
    encodeInput input = data := by
  cases firstEqual : IntegerStep.decodeValue (data.leftType.format parameters) data.left with
  | none =>
      simp only [decodeInput, firstEqual] at decoded
      cases decoded
  | some first =>
      cases secondEqual : IntegerStep.decodeValue (data.rightType.format parameters) data.right with
      | none =>
          simp only [decodeInput, firstEqual, secondEqual] at decoded
          cases decoded
      | some second =>
          simp only [decodeInput, firstEqual, secondEqual] at decoded
          cases decoded
          cases data
          simp only [encodeInput, IntegerStep.value_decode _ _ first firstEqual,
            IntegerStep.value_decode _ _ second secondEqual]

inductive ConfigurationData (Extension : Type u) where
  | pending (input : InputData Extension)
  | completed (outcome : TypedIntegerOutcome Extension)
  deriving DecidableEq, Repr

def encode {Extension : Type u} {parameters : IntegerTypeParameters Extension} :
    Configuration parameters → ConfigurationData Extension
  | .pending input => .pending (encodeInput input)
  | .completed outcome => .completed outcome

def decode {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    ConfigurationData Extension → Option (Configuration parameters)
  | .pending input => (decodeInput parameters input).map Configuration.pending
  | .completed outcome => some (.completed outcome)

theorem decode_encode {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (configuration : Configuration parameters) : decode parameters (encode configuration) = some configuration := by
  cases configuration <;> simp only [encode, decode, decodeInput_encode, Option.map_some]

theorem encode_decode {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (data : ConfigurationData Extension) (configuration : Configuration parameters)
    (decoded : decode parameters data = some configuration) : encode configuration = data := by
  cases data with
  | completed outcome => cases decoded; rfl
  | pending input =>
      cases inputEqual : decodeInput parameters input with
      | none => simp only [decode, inputEqual, Option.map_none] at decoded; cases decoded
      | some actual =>
          simp only [decode, inputEqual, Option.map_some] at decoded
          cases decoded
          exact congrArg ConfigurationData.pending (encodeInput_decode parameters input actual inputEqual)

def stepData {Extension : Type u} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension)
    (data : ConfigurationData Extension) : Option (ConfigurationData Extension) := do
  let before ← decode parameters data
  let after ← step parameters before
  some (encode after)

theorem stepData_sound {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : ConfigurationData Extension) (stepped : stepData parameters before = some after) :
    ∃ source target : Configuration parameters, decode parameters before = some source ∧
      decode parameters after = some target ∧ Reduction parameters policy source target := by
  cases beforeEqual : decode parameters before with
  | none => simp only [stepData, beforeEqual, bind, Option.bind_none] at stepped; cases stepped
  | some source =>
      cases afterEqual : step parameters source with
      | none =>
          simp only [stepData, beforeEqual, afterEqual, bind, Option.bind_some, Option.bind_none] at stepped
          cases stepped
      | some target =>
          simp only [stepData, beforeEqual, afterEqual, bind, Option.bind_some] at stepped
          cases stepped
          exact ⟨source, target, rfl, decode_encode parameters target,
            step_sound parameters policy source target afterEqual⟩

theorem stepData_complete {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : Configuration parameters) (reduced : Reduction parameters policy before after) :
    stepData parameters (encode before) = some (encode after) := by
  simp only [stepData, decode_encode, step_complete parameters policy before after reduced, bind, Option.bind_some]

theorem stepData_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : ConfigurationData Extension) : stepData parameters before = some after ↔
    ∃ source target : Configuration parameters, decode parameters before = some source ∧
      decode parameters after = some target ∧ Reduction parameters policy source target := by
  constructor
  · exact stepData_sound parameters policy before after
  · rintro ⟨source, target, beforeEqual, afterEqual, reduced⟩
    rw [← encode_decode parameters before source beforeEqual, ← encode_decode parameters after target afterEqual]
    exact stepData_complete parameters policy source target reduced

theorem encode_injective {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    Function.Injective (@encode Extension parameters) := by
  intro first second equal
  have decoded := congrArg (decode parameters) equal
  rw [decode_encode, decode_encode] at decoded
  exact Option.some.inj decoded

def lowerInput {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (input : Input parameters) : IntegerStep.Instruction :=
  let prepared := prepareIntegerOperands parameters input.leftType input.rightType input.left input.right
  .binary (prepared.target.format parameters) input.operation prepared.left prepared.right

def lowerConfiguration {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) : Configuration parameters → IntegerStep.Configuration
  | .pending input => .pending (lowerInput parameters input)
  | .completed outcome => .completed (.binary outcome.outcome)

theorem reduction_lowering {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (before after : Configuration parameters) (reduced : Reduction parameters policy before after) :
    IntegerStep.Reduction policy (lowerConfiguration parameters before) (lowerConfiguration parameters after) := by
  cases reduced with
  | arithmetic input outcome computed =>
      have equal := evaluateTypedIntegerBinary_complete parameters policy _ _ _ _ _ outcome computed
      rw [← equal]
      exact IntegerStep.Reduction.binary _ _ _ _ _ (evaluateIntegerBinary_sound _ _ _ _)

structure Receipt {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  input : Input parameters
  outcome : TypedIntegerOutcome Extension
  deriving DecidableEq, Repr

def machine {Extension : Type} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension) :
    Machine (Configuration parameters) (Receipt parameters) (TypedIntegerOutcome Extension) Empty where
  step
    | .pending input => some (.publish [⟨input, execute parameters input⟩] (.completed (execute parameters input)))
    | .completed outcome => some (.finish outcome)

def price {Extension : Type} {parameters : IntegerTypeParameters Extension} : Configuration parameters → Nat
  | .pending _ => 1
  | .completed _ => 0

theorem run_one_retains_the_result {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (input : Input parameters) :
    (machine parameters).run 1 (.pending input) =
      ⟨[⟨input, execute parameters input⟩], .exhausted (.completed (execute parameters input))⟩ := rfl

theorem run_two_finishes {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (input : Input parameters) :
    (machine parameters).run 2 (.pending input) =
      ⟨[⟨input, execute parameters input⟩], .finished (execute parameters input)⟩ := rfl

theorem completed_has_no_receipts {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (fuel : Nat) (outcome : TypedIntegerOutcome Extension) :
    ((machine parameters).run fuel (.completed outcome)).1 = [] := by cases fuel <;> rfl

theorem run_receipts_valid {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy) (fuel : Nat)
    (initial : Configuration parameters) : ∀ receipt ∈ ((machine parameters).run fuel initial).1,
      Reduction parameters policy (.pending receipt.input) (.completed receipt.outcome) := by
  cases fuel with
  | zero => simp only [Machine.run, List.not_mem_nil, false_implies, implies_true]
  | succ fuel =>
      cases initial with
      | completed outcome => simp only [Machine.run, machine, List.not_mem_nil, false_implies, implies_true]
      | pending input =>
          intro receipt member
          change receipt ∈ [⟨input, execute parameters input⟩] ++
            ((machine parameters).run fuel (.completed (execute parameters input))).1 at member
          rw [completed_has_no_receipts] at member
          simp only [List.append_nil, List.mem_singleton] at member
          subst receipt
          exact step_sound parameters policy _ _ rfl

theorem run_two_has_one_charge {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (input : Input parameters) :
    (machine parameters).spent price 2 (.pending input) = 1 := rfl

theorem resume_after_prefix {Extension : Type} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (first second : Nat)
    (initial saved : Configuration parameters) (events : List (Receipt parameters))
    (paused : (machine parameters).run first initial = ⟨events, .exhausted saved⟩) :
    (machine parameters).run (first + second) initial =
      (events ++ ((machine parameters).run second saved).1, ((machine parameters).run second saved).2) :=
  (machine parameters).established_and_pending first second initial saved events paused

def productive {Extension : Type} [DecidableEq Extension] (parameters : IntegerTypeParameters Extension) :
    (machine parameters).Productive where
  rank _ := 0
  moves state := by cases state <;> simp [machine]
  silent_decreases := by intro state next silent; cases state <;> simp [machine] at silent

end Mettapedia.Languages.C11.TypedIntegerStep

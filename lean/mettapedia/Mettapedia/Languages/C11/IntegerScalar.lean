import Mettapedia.Languages.C11.TypedIntegerArithmetic

/-!
# Typed integer values for expression execution

A scalar retains its canonical source type and a value in that type's range.
The executable arithmetic and cast operations construct their result values
from the already proved conversion and arithmetic judgments. Arithmetic
undefined behavior remains separate from a selected implementation-defined
conversion signal. Conversion to `_Bool` uses zero/nonzero truth, not
unsigned remainder.

These are elaborated integer expression values. Floating, complex, pointer,
plain-char, enum and bit-field source adapters remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.IntegerScalar

universe u

structure Value {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  type : IntegerType Extension
  integer : IntegerValue (type.format parameters)
  deriving DecidableEq, Repr

theorem Value.ext {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    (first second : Value parameters) (type : first.type = second.type)
    (integer : first.integer.value = second.integer.value) : first = second := by
  cases first with
  | mk firstType firstInteger =>
      cases second with
      | mk secondType secondInteger =>
          cases type
          cases firstInteger
          cases secondInteger
          cases integer
          rfl

theorem reduction_value_range {format : IntegerFormat} {input result : Int}
    (reduced : ArithmeticReduction format input (.value result)) : format.Represents result := by
  cases reduced with
  | unsigned _ _ _ _ valid _ => exact valid
  | signedWithin _ _ _ _ valid => exact valid

theorem division_value_range {format : IntegerFormat} {left right result : Int} {remainder : Bool}
    (evaluated : DivisionEvaluation format left right remainder (.value result)) :
    format.Represents result := by
  cases evaluated with
  | computed _ _ _ _ _ reduced => exact reduction_value_range reduced

theorem binary_value_range {format : IntegerFormat} {left right : IntegerValue format}
    {operation : IntegerBinaryOperator} {result : Int}
    (evaluated : IntegerBinaryEvaluation format left right operation (.value result)) :
    format.Represents result := by
  cases evaluated with
  | add _ reduced => exact reduction_value_range reduced
  | subtract _ reduced => exact reduction_value_range reduced
  | multiply _ reduced => exact reduction_value_range reduced
  | divide _ evaluated => exact division_value_range evaluated
  | remainder _ evaluated => exact division_value_range evaluated

theorem typed_value_range {Extension : Type u} {parameters : IntegerTypeParameters Extension}
    {policy : SignedConversionPolicy} {operation : IntegerBinaryOperator}
    {first second : Value parameters} {type : IntegerType Extension} {result : Int}
    (evaluated : TypedIntegerBinaryEvaluation parameters policy operation first.type second.type
      first.integer second.integer ⟨type, .value result⟩) : (type.format parameters).Represents result := by
  cases evaluated with
  | evaluated _ _ _ arithmetic => exact binary_value_range arithmetic

inductive ArithmeticResult {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  | value (scalar : Value parameters)
  | undefined (type : IntegerType Extension) (reason : ArithmeticFault)
  deriving DecidableEq, Repr

def ArithmeticResult.raw {Extension : Type u} {parameters : IntegerTypeParameters Extension} :
    ArithmeticResult parameters → TypedIntegerOutcome Extension
  | .value scalar => ⟨scalar.type, .value scalar.integer.value⟩
  | .undefined type reason => ⟨type, .undefined reason⟩

theorem ArithmeticResult.raw_injective {Extension : Type u}
    (parameters : IntegerTypeParameters Extension) :
    Function.Injective (@ArithmeticResult.raw Extension parameters) := by
  intro first second same
  cases first with
  | value first =>
      cases second with
      | value second =>
          have type := congrArg TypedIntegerOutcome.type same
          have integer := congrArg TypedIntegerOutcome.outcome same
          exact congrArg ArithmeticResult.value (Value.ext first second type
            (IntegerArithmeticOutcome.value.inj integer))
      | undefined type reason => cases congrArg TypedIntegerOutcome.outcome same
  | undefined type reason =>
      cases second with
      | value scalar => cases congrArg TypedIntegerOutcome.outcome same
      | undefined otherType otherReason =>
          have typeSame := congrArg TypedIntegerOutcome.type same
          have reasonSame := IntegerArithmeticOutcome.undefined.inj (congrArg TypedIntegerOutcome.outcome same)
          cases typeSame
          cases reasonSame
          rfl

private theorem executable_binary_range {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (operation : IntegerBinaryOperator)
    (first second : Value parameters) (result : Int)
    (computed : (evaluateTypedIntegerBinary parameters operation first.type second.type
      first.integer second.integer).outcome = .value result) :
    ((evaluateTypedIntegerBinary parameters operation first.type second.type
      first.integer second.integer).type.format parameters).Represents result := by
  have evaluated := evaluateTypedIntegerBinary_sound parameters intervalReductionPolicy operation
    first.type second.type first.integer second.integer
  generalize evaluateTypedIntegerBinary parameters operation first.type second.type
    first.integer second.integer = outcome at *
  cases outcome with
  | mk type value => cases computed; exact typed_value_range evaluated

def binary {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (operation : IntegerBinaryOperator)
    (first second : Value parameters) : ArithmeticResult parameters :=
  let outcome := evaluateTypedIntegerBinary parameters operation first.type second.type first.integer second.integer
  match computed : outcome.outcome with
  | .value result => .value ⟨outcome.type, ⟨result,
      executable_binary_range parameters operation first second result computed⟩⟩
  | .undefined reason => .undefined outcome.type reason

theorem binary_raw {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (operation : IntegerBinaryOperator)
    (first second : Value parameters) :
    (binary parameters operation first second).raw =
      evaluateTypedIntegerBinary parameters operation first.type second.type first.integer second.integer := by
  unfold binary
  dsimp only
  split <;> rename_i result computed
  all_goals
    change (⟨_, _⟩ : TypedIntegerOutcome Extension) = _
    have eta (outcome : TypedIntegerOutcome Extension) (value : IntegerArithmeticOutcome)
        (same : outcome.outcome = value) : ⟨outcome.type, value⟩ = outcome := by
      cases outcome
      cases same
      rfl
    exact eta _ _ computed

def ArithmeticEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (operation : IntegerBinaryOperator)
    (first second : Value parameters) (result : ArithmeticResult parameters) : Prop :=
  TypedIntegerBinaryEvaluation parameters policy operation first.type second.type
    first.integer second.integer result.raw

theorem binary_iff {Extension : Type u} [DecidableEq Extension]
    (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (operation : IntegerBinaryOperator) (first second : Value parameters) (result : ArithmeticResult parameters) :
    binary parameters operation first second = result ↔
      ArithmeticEvaluation parameters policy operation first second result := by
  constructor
  · intro same
    have raw := binary_raw parameters operation first second
    rw [same] at raw
    exact (evaluateTypedIntegerBinary_iff parameters policy operation first.type second.type
      first.integer second.integer result.raw).mp raw.symm
  · intro evaluated
    apply ArithmeticResult.raw_injective parameters
    exact (binary_raw parameters operation first second).trans
      (evaluateTypedIntegerBinary_complete parameters policy operation first.type second.type
        first.integer second.integer result.raw evaluated)

def destination {Extension : Type u} (parameters : IntegerTypeParameters Extension) :
    IntegerType Extension → ConversionDestination
  | .boolean => .boolean
  | type => .integer (type.format parameters)

theorem conversion_value_range {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (type : IntegerType Extension) (input result : Int)
    (converted : convertInteger policy input (destination parameters type) = .value result) :
    (type.format parameters).Represents result := by
  cases type with
  | boolean =>
      by_cases zero : input = 0
      · simp [destination, convertInteger, zero] at converted
        subst result
        exact (IntegerType.boolean.format parameters).zero_representable
      · simp [destination, convertInteger, zero] at converted
        subst result
        exact (IntegerType.boolean.format parameters).one_representable
  | signed family => exact converted_value_representable policy input result _ converted
  | unsigned family => exact converted_value_representable policy input result _ converted

inductive CastResult {Extension : Type u} (parameters : IntegerTypeParameters Extension) where
  | value (scalar : Value parameters)
  | signal (identifier : Nat)
  deriving DecidableEq, Repr

def cast {Extension : Type u} (parameters : IntegerTypeParameters Extension) (policy : SignedConversionPolicy)
    (type : IntegerType Extension) (input : Value parameters) : CastResult parameters :=
  match converted : convertInteger policy input.integer.value (destination parameters type) with
  | .value result => .value ⟨type, ⟨result, conversion_value_range parameters policy type
      input.integer.value result converted⟩⟩
  | .signal identifier => .signal identifier

inductive CastEvaluation {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (type : IntegerType Extension) (input : Value parameters) :
    CastResult parameters → Prop where
  | value (result : Value parameters) (sameType : result.type = type)
      (converted : IntegerConverts policy input.integer.value (destination parameters type)
        (.value result.integer.value)) : CastEvaluation parameters policy type input (.value result)
  | signal (identifier : Nat) (converted : IntegerConverts policy input.integer.value
      (destination parameters type) (.signal identifier)) :
      CastEvaluation parameters policy type input (.signal identifier)

theorem cast_sound {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (type : IntegerType Extension) (input : Value parameters) :
    CastEvaluation parameters policy type input (cast parameters policy type input) := by
  unfold cast
  split
  · exact .value _ rfl ((convertInteger_iff policy _ _ _).mp (by assumption))
  · exact .signal _ ((convertInteger_iff policy _ _ _).mp (by assumption))

theorem cast_complete {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (type : IntegerType Extension) (input : Value parameters)
    (result : CastResult parameters) (evaluated : CastEvaluation parameters policy type input result) :
    cast parameters policy type input = result := by
  cases evaluated with
  | value result sameType converted =>
      have computed := convertInteger_complete policy _ _ _ converted
      unfold cast
      split
      · rename_i value observed
        have same := ConversionOutcome.value.inj (observed.symm.trans computed)
        exact congrArg CastResult.value (Value.ext _ result sameType.symm same)
      · rename_i identifier observed
        cases observed.symm.trans computed
  | signal identifier converted =>
      have computed := convertInteger_complete policy _ _ _ converted
      unfold cast
      split
      · rename_i value observed
        cases observed.symm.trans computed
      · rename_i actual observed
        have same := ConversionOutcome.signal.inj (observed.symm.trans computed)
        cases same
        rfl

theorem cast_iff {Extension : Type u} (parameters : IntegerTypeParameters Extension)
    (policy : SignedConversionPolicy) (type : IntegerType Extension)
    (input : Value parameters) (result : CastResult parameters) :
    cast parameters policy type input = result ↔ CastEvaluation parameters policy type input result := by
  constructor
  · rintro rfl
    exact cast_sound parameters policy type input
  · exact cast_complete parameters policy type input result

def truth {Extension : Type u} {parameters : IntegerTypeParameters Extension} (input : Value parameters) : Bool :=
  decide (input.integer.value ≠ 0)

def logicalValue {Extension : Type u} (parameters : IntegerTypeParameters Extension) (truth : Bool) :
    Value parameters :=
  ⟨.int, if truth then ⟨1, (IntegerType.int.format parameters).one_representable⟩
    else ⟨0, (IntegerType.int.format parameters).zero_representable⟩⟩

theorem logicalValue_type {Extension : Type u} (parameters : IntegerTypeParameters Extension) (truth : Bool) :
    (logicalValue parameters truth).type = .int := rfl

theorem logicalValue_integer {Extension : Type u} (parameters : IntegerTypeParameters Extension) (truth : Bool) :
    (logicalValue parameters truth).integer.value = if truth then 1 else 0 := by
  cases truth <;> rfl

end Mettapedia.Languages.C11.IntegerScalar

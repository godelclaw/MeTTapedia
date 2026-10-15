import Mettapedia.Languages.C11.ReadExpressionSyntax
import Mettapedia.Languages.C11.IntegerStep

/-!
# Independent head reductions for nonvolatile integer expressions

Head rules join typed arithmetic and conversion judgments to scoped,
effective-type-checked byte reads. Their executable counterparts construct
the value ranges and retain the actual read outcome. Trap observations and
implementation-defined conversion signals are explicit terminal outcomes.
Unavailable pure-memory operations are refused rather than classified as
arbitrary C undefined behavior.

Short-circuit and conditional rules select only an evaluated continuation.
Conditional result types are supplied by elaboration; this module does not
claim the missing source conditional-type elaboration theorem. The events
describe semantic reductions, not committed host reads or publication rights.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpression

open ObjectAccessMemory

inductive Observation where
  | read (name : String) (location : Lvalue) (outcome : IntegerObject.Outcome)
  | arithmetic (operation : IntegerBinaryOperator)
  | cast (type : IntegerType IntegerExtension)
  | truth
  | logicalNot
  | logicalAnd (selected : Bool)
  | logicalOr (selected : Bool)
  | conditional (selected : Bool)
  | comma
  | fault (reason : Fault)
  deriving DecidableEq, Repr

structure Event (layout : Layout) where
  context : Context layout
  observation : Observation
  deriving DecidableEq, Repr

def event (layout : Layout) (observation : Observation) : Event layout := ⟨[], observation⟩

def Event.under {layout : Layout} (frame : Frame layout) (observed : Event layout) : Event layout :=
  ⟨frame :: observed.context, observed.observation⟩

def layoutValue (layout : Layout) (value : IntegerValue layout.representation.integer) :
    IntegerScalar.Value layout.parameters :=
  ⟨layout.sourceType, ⟨value.value, by rw [← layout.format]; exact value.valid⟩⟩

inductive ObjectInterpretation (layout : Layout) : IntegerObject.Outcome → Expression layout → Prop where
  | value (integer : IntegerValue layout.representation.integer) (negativeZero : Bool) :
      ObjectInterpretation layout (.integer (.value integer.value negativeZero)) (.value (layoutValue layout integer))
  | trap (reason : IntegerBits.Trap) :
      ObjectInterpretation layout (.integer (.trap reason)) (.fault (.objectTrap reason))
  | paddingTrap : ObjectInterpretation layout .paddingTrap (.fault .paddingTrap)

def interpretObject (layout : Layout) : IntegerObject.Outcome → Option (Expression layout)
  | .integer (.value value _) =>
      (IntegerStep.decodeValue layout.representation.integer value).map (fun integer => .value (layoutValue layout integer))
  | .integer (.trap reason) => some (.fault (.objectTrap reason))
  | .paddingTrap => some (.fault .paddingTrap)

theorem interpretObject_sound (layout : Layout) (outcome : IntegerObject.Outcome) (expression : Expression layout)
    (interpreted : interpretObject layout outcome = some expression) : ObjectInterpretation layout outcome expression := by
  cases outcome with
  | paddingTrap => simp [interpretObject] at interpreted; subst expression; exact .paddingTrap
  | integer outcome =>
      cases outcome with
      | trap reason => simp [interpretObject] at interpreted; subst expression; exact .trap reason
      | value value negativeZero =>
          cases decoded : IntegerStep.decodeValue layout.representation.integer value with
          | none => simp [interpretObject, decoded] at interpreted
          | some integer =>
              simp [interpretObject, decoded] at interpreted
              subst expression
              have same := IntegerStep.value_decode layout.representation.integer value integer decoded
              rw [← same]
              exact .value integer negativeZero

theorem interpretObject_complete (layout : Layout) (outcome : IntegerObject.Outcome) (expression : Expression layout)
    (interpreted : ObjectInterpretation layout outcome expression) : interpretObject layout outcome = some expression := by
  cases interpreted with
  | value integer negativeZero => simp [interpretObject, IntegerStep.decodeValue_encode]
  | trap reason => rfl
  | paddingTrap => rfl

theorem interpretObject_iff (layout : Layout) (outcome : IntegerObject.Outcome) (expression : Expression layout) :
    interpretObject layout outcome = some expression ↔ ObjectInterpretation layout outcome expression :=
  ⟨interpretObject_sound layout outcome expression, interpretObject_complete layout outcome expression⟩

theorem reading_interpretation_exists (layout : Layout) (state : SemanticState layout.representation.characters)
    (location : Lvalue) (outcome : IntegerObject.Outcome) (reading : Reading layout state location outcome) :
    ∃ expression, ObjectInterpretation layout outcome expression := by
  cases outcome with
  | paddingTrap => exact ⟨_, .paddingTrap⟩
  | integer outcome =>
      cases outcome with
      | trap reason => exact ⟨_, .trap reason⟩
      | value value negativeZero =>
          obtain ⟨_, _, _, _, _, bytes, _, interpreted⟩ := reading
          have represented : layout.representation.integer.Represents value := by
            cases interpreted with
            | integer _ _ _ _ integer =>
                exact IntegerBits.Reading.value_in_range _ _ _ _ integer value negativeZero rfl
          exact ⟨_, .value ⟨value, represented⟩ negativeZero⟩

inductive HeadReduction (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment) :
    Expression layout → Observation → Expression layout → Prop where
  | read (name : String) (location : Lvalue) (outcome : IntegerObject.Outcome) (after : Expression layout)
      (bound : ScopedLvalues.Binding name environment location) (reading : Reading layout memory location outcome)
      (interpreted : ObjectInterpretation layout outcome after) :
      HeadReduction layout policy memory environment (.read name) (.read name location outcome) after
  | arithmetic (operation : IntegerBinaryOperator) (first second : IntegerScalar.Value layout.parameters)
      (result : IntegerScalar.ArithmeticResult layout.parameters)
      (computed : IntegerScalar.ArithmeticEvaluation layout.parameters policy operation first second result) :
      HeadReduction layout policy memory environment (.arithmetic operation (.value first) (.value second))
        (.arithmetic operation) (arithmeticResult layout result)
  | cast (type : IntegerType IntegerExtension) (input : IntegerScalar.Value layout.parameters)
      (result : IntegerScalar.CastResult layout.parameters)
      (converted : IntegerScalar.CastEvaluation layout.parameters policy type input result) :
      HeadReduction layout policy memory environment (.cast type (.value input)) (.cast type) (castResult layout result)
  | truth (input : IntegerScalar.Value layout.parameters) :
      HeadReduction layout policy memory environment (.truth (.value input)) .truth
        (logical layout (IntegerScalar.truth input))
  | logicalNot (input : IntegerScalar.Value layout.parameters) :
      HeadReduction layout policy memory environment (.logicalNot (.value input)) .logicalNot
        (logical layout (!IntegerScalar.truth input))
  | andFalse (input : IntegerScalar.Value layout.parameters) (second : Expression layout)
      (zero : input.integer.value = 0) :
      HeadReduction layout policy memory environment (.logicalAnd (.value input) second) (.logicalAnd false)
        (logical layout false)
  | andTrue (input : IntegerScalar.Value layout.parameters) (second : Expression layout)
      (nonzero : input.integer.value ≠ 0) :
      HeadReduction layout policy memory environment (.logicalAnd (.value input) second) (.logicalAnd true) (.truth second)
  | orTrue (input : IntegerScalar.Value layout.parameters) (second : Expression layout)
      (nonzero : input.integer.value ≠ 0) :
      HeadReduction layout policy memory environment (.logicalOr (.value input) second) (.logicalOr true) (logical layout true)
  | orFalse (input : IntegerScalar.Value layout.parameters) (second : Expression layout)
      (zero : input.integer.value = 0) :
      HeadReduction layout policy memory environment (.logicalOr (.value input) second) (.logicalOr false) (.truth second)
  | conditionalTrue (type : IntegerType IntegerExtension) (input : IntegerScalar.Value layout.parameters)
      (first second : Expression layout) (nonzero : input.integer.value ≠ 0) :
      HeadReduction layout policy memory environment (.conditional type (.value input) first second)
        (.conditional true) (.cast type first)
  | conditionalFalse (type : IntegerType IntegerExtension) (input : IntegerScalar.Value layout.parameters)
      (first second : Expression layout) (zero : input.integer.value = 0) :
      HeadReduction layout policy memory environment (.conditional type (.value input) first second)
        (.conditional false) (.cast type second)
  | comma (input : IntegerScalar.Value layout.parameters) (second : Expression layout) :
      HeadReduction layout policy memory environment (.comma (.value input) second) .comma second

def head (layout : Layout) (policy : SignedConversionPolicy) (memory : State layout.representation.characters)
    (environment : ScopedLvalues.Environment) : Expression layout → Option (Observation × Expression layout)
  | .read name => do
      let location ← ScopedLvalues.lookup environment name
      let outcome ← ObjectAccessMemory.read layout memory location
      let after ← interpretObject layout outcome
      some (.read name location outcome, after)
  | .arithmetic operation (.value first) (.value second) =>
      some (.arithmetic operation, arithmeticResult layout (IntegerScalar.binary layout.parameters operation first second))
  | .cast type (.value input) => some (.cast type, castResult layout (IntegerScalar.cast layout.parameters policy type input))
  | .truth (.value input) => some (.truth, logical layout (IntegerScalar.truth input))
  | .logicalNot (.value input) => some (.logicalNot, logical layout (!IntegerScalar.truth input))
  | .logicalAnd (.value input) second =>
      if IntegerScalar.truth input then some (.logicalAnd true, .truth second)
      else some (.logicalAnd false, logical layout false)
  | .logicalOr (.value input) second =>
      if IntegerScalar.truth input then some (.logicalOr true, logical layout true)
      else some (.logicalOr false, .truth second)
  | .conditional type (.value input) first second =>
      if IntegerScalar.truth input then some (.conditional true, .cast type first)
      else some (.conditional false, .cast type second)
  | .comma (.value _) second => some (.comma, second)
  | _ => none

theorem head_complete (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Observation)
    (reduced : HeadReduction layout policy (represent memory) environment before observed after) :
    head layout policy memory environment before = some (observed, after) := by
  cases reduced with
  | read name location outcome after bound reading interpreted =>
      simp [head, ScopedLvalues.lookup_complete _ _ _ bound, ObjectAccessMemory.read_complete _ _ _ _ reading,
        interpretObject_complete _ _ _ interpreted]
  | arithmetic operation first second result computed =>
      simp only [head, (IntegerScalar.binary_iff _ policy _ _ _ _).mpr computed]
  | cast type input result converted => simp only [head, IntegerScalar.cast_complete _ _ _ _ _ converted]
  | truth input => rfl
  | logicalNot input => rfl
  | andFalse input second zero => simp [head, IntegerScalar.truth, zero]
  | andTrue input second nonzero => simp [head, IntegerScalar.truth, nonzero]
  | orTrue input second nonzero => simp [head, IntegerScalar.truth, nonzero]
  | orFalse input second zero => simp [head, IntegerScalar.truth, zero]
  | conditionalTrue type input first second nonzero => simp [head, IntegerScalar.truth, nonzero]
  | conditionalFalse type input first second zero => simp [head, IntegerScalar.truth, zero]
  | comma input second => rfl

theorem head_sound (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Observation)
    (executed : head layout policy memory environment before = some (observed, after)) :
    HeadReduction layout policy (represent memory) environment before observed after := by
  cases before with
  | value scalar => simp [head] at executed
  | fault reason => simp [head] at executed
  | read name =>
      cases bound : ScopedLvalues.lookup environment name with
      | none => simp [head, bound] at executed
      | some location =>
          cases reading : ObjectAccessMemory.read layout memory location with
          | none => simp [head, bound, reading] at executed
          | some outcome =>
              cases interpreted : interpretObject layout outcome with
              | none => simp [head, bound, reading, interpreted] at executed
              | some result =>
                  simp [head, bound, reading, interpreted] at executed
                  obtain ⟨rfl, rfl⟩ := executed
                  exact .read _ _ _ _ (ScopedLvalues.lookup_sound _ _ _ bound)
                    (ObjectAccessMemory.read_sound _ _ _ _ reading) (interpretObject_sound _ _ _ interpreted)
  | arithmetic operation first second =>
      cases first <;> cases second <;> simp only [head, reduceCtorEq] at executed
      case value.value left right =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        exact .arithmetic _ _ _ _ ((IntegerScalar.binary_iff _ policy _ _ _ _).mp rfl)
  | cast type operand =>
      cases operand <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        exact .cast _ _ _ (IntegerScalar.cast_sound _ _ _ _)
  | truth operand =>
      cases operand <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        exact .truth _
  | logicalNot operand =>
      cases operand <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        exact .logicalNot _
  | logicalAnd first second =>
      cases first <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        by_cases zero : input.integer.value = 0
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .andFalse _ _ zero
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .andTrue _ _ zero
  | logicalOr first second =>
      cases first <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        by_cases zero : input.integer.value = 0
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .orFalse _ _ zero
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .orTrue _ _ zero
  | conditional type test first second =>
      cases test <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        by_cases zero : input.integer.value = 0
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .conditionalFalse _ _ _ _ zero
        · simp [IntegerScalar.truth, zero] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .conditionalTrue _ _ _ _ zero
  | comma first second =>
      cases first <;> simp only [head, reduceCtorEq] at executed
      case value input =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj executed)
        exact .comma _ _

theorem head_iff (layout : Layout) (policy : SignedConversionPolicy)
    (memory : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Observation) :
    head layout policy memory environment before = some (observed, after) ↔
      HeadReduction layout policy (represent memory) environment before observed after :=
  ⟨head_sound layout policy memory environment before after observed,
    head_complete layout policy memory environment before after observed⟩

theorem head_weight (layout : Layout) (policy : SignedConversionPolicy)
    (memory : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (before after : Expression layout) (observed : Observation)
    (reduced : HeadReduction layout policy memory environment before observed after) : weight after < weight before := by
  cases reduced with
  | read _ _ _ _ _ _ interpreted => cases interpreted <;> simp [weight]
  | arithmetic => simp [weight, arithmeticResult_weight]
  | cast => simp [weight, castResult_weight]
  | truth => simp [weight, logical_weight]
  | logicalNot => simp [weight, logical_weight]
  | andFalse => simp [weight, logical_weight]
  | andTrue => simp only [weight]; omega
  | orTrue => simp [weight, logical_weight]
  | orFalse => simp only [weight]; omega
  | conditionalTrue => simp only [weight]; omega
  | conditionalFalse => simp only [weight]; omega
  | comma => simp only [weight]; omega

end Mettapedia.Languages.C11.ReadExpression

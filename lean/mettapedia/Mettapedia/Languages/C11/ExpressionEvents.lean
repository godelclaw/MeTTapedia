import Mettapedia.Languages.C11.IntegerMemoryModel
import Mettapedia.Languages.C11.ValueSequencing

/-!
# Retained values and memory occurrences for C integer expressions

An occurrence consumes the previously computed values of named occurrences.
Loads retain their representation observation; stores consume a converted
value and have a separate modification receipt. Assignment results can reuse
the same converted value independently of the store's execution position.
The sequencing relation is source data, not the chronological receipt order.

This interface covers canonical integer values and already located complete
objects. Source lvalue construction, partial objects, volatile/external
actions and non-integer expressions require their own operation constructors.
These memory receipts do not grant host publication authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ExpressionEvents

open ObjectAccessMemory IntegerMemoryModel

inductive Outcome (model : Model) where
  | value (scalar : IntegerScalar.Value model.parameters)
  | loaded (scalar : IntegerScalar.Value model.parameters) (negativeZero : Bool)
  | stored (scalar : IntegerScalar.Value model.parameters)
  | arithmeticFault (type : IntegerType IntegerExtension) (reason : ArithmeticFault)
  | conversionSignal (identifier : Nat)
  | objectTrap (type : IntegerType IntegerExtension) (reason : IntegerBits.Trap)
  | paddingTrap (type : IntegerType IntegerExtension)
  deriving DecidableEq, Repr

def Outcome.scalar {model : Model} : Outcome model → Option (IntegerScalar.Value model.parameters)
  | .value scalar | .loaded scalar _ | .stored scalar => some scalar
  | .arithmeticFault _ _ | .conversionSignal _ | .objectTrap _ _ | .paddingTrap _ => none

def Outcome.terminal {model : Model} (outcome : Outcome model) : Bool := outcome.scalar.isNone

def arithmeticOutcome (model : Model) : IntegerScalar.ArithmeticResult model.parameters → Outcome model
  | .value scalar => .value scalar
  | .undefined type reason => .arithmeticFault type reason

def castOutcome (model : Model) : IntegerScalar.CastResult model.parameters → Outcome model
  | .value scalar => .value scalar
  | .signal identifier => .conversionSignal identifier

def loadedOutcome (model : Model) : Loaded model → Outcome model
  | .value scalar negativeZero => .loaded scalar negativeZero
  | .trap type reason => .objectTrap type reason
  | .paddingTrap type => .paddingTrap type

theorem arithmeticOutcome_injective (model : Model) : Function.Injective (arithmeticOutcome model) := by
  intro first second same
  cases first <;> cases second <;> simp_all [arithmeticOutcome]

theorem castOutcome_injective (model : Model) : Function.Injective (castOutcome model) := by
  intro first second same
  cases first <;> cases second <;> simp_all [castOutcome]

theorem loadedOutcome_injective (model : Model) : Function.Injective (loadedOutcome model) := by
  intro first second same
  cases first <;> cases second <;> simp_all [loadedOutcome]

inductive Operation (Index : Type) (model : Model) where
  | constant (scalar : IntegerScalar.Value model.parameters)
  | copy (source : Index)
  | load (location : Lvalue)
  | binary (operator : IntegerBinaryOperator) (first second : Index)
  | cast (type : IntegerType IntegerExtension) (source : Index)
  | store (location : Lvalue) (source : Index)
  deriving DecidableEq, Repr

def Operation.inputs {Index : Type} {model : Model} : Operation Index model → List Index
  | .constant _ | .load _ => []
  | .copy source | .cast _ source | .store _ source => [source]
  | .binary _ first second => [first, second]

def Operation.access {Index : Type} {model : Model} : Operation Index model → Sequencing.Access Identity
  | .load location => location.readEvent
  | .store location _ => location.writeEvent
  | .constant _ | .copy _ | .binary _ _ _ | .cast _ _ => .other

def Operation.map {First Second : Type} {model : Model} (rename : First → Second) :
    Operation First model → Operation Second model
  | .constant scalar => .constant scalar
  | .copy source => .copy (rename source)
  | .load location => .load location
  | .binary operator first second => .binary operator (rename first) (rename second)
  | .cast type source => .cast type (rename source)
  | .store location source => .store location (rename source)

theorem Operation.map_access {First Second : Type} {model : Model} (rename : First → Second)
    (operation : Operation First model) : (operation.map rename).access = operation.access := by
  cases operation <;> rfl

theorem Operation.map_inputs {First Second : Type} {model : Model} (rename : First → Second)
    (operation : Operation First model) : (operation.map rename).inputs = operation.inputs.map rename := by
  cases operation <;> rfl

abbrev Cache (Index : Type) (model : Model) := List (Index × Outcome model)

def lookupScalar {Index : Type} [DecidableEq Index] {model : Model}
    (cache : Cache Index model) (index : Index) : Option (IntegerScalar.Value model.parameters) :=
  (cache.lookup index).bind Outcome.scalar

def Available {Index : Type} [DecidableEq Index] {model : Model}
    (cache : Cache Index model) (index : Index) (scalar : IntegerScalar.Value model.parameters) : Prop :=
  ∃ outcome, cache.lookup index = some outcome ∧ outcome.scalar = some scalar

theorem lookupScalar_iff {Index : Type} [DecidableEq Index] {model : Model}
    (cache : Cache Index model) (index : Index) (scalar : IntegerScalar.Value model.parameters) :
    lookupScalar cache index = some scalar ↔ Available cache index scalar := by
  simp only [lookupScalar, Option.bind_eq_some_iff, Available]

structure Plan (Index : Type) (model : Model) where
  component : ValueSequencing.Component Index Identity
  operation : Index → Operation Index model
  access : ∀ index, component.evaluation.access index = (operation index).access

def Plan.InputsOrdered {Index : Type} {model : Model} (plan : Plan Index model) : Prop :=
  ∀ index source, source ∈ (plan.operation index).inputs →
    plan.component.evaluation.order.Precedes source index

end Mettapedia.Languages.C11.ExpressionEvents

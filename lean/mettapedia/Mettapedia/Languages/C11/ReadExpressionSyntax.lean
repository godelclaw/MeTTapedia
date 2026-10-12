import Mettapedia.Languages.C11.IntegerScalar
import Mettapedia.Languages.C11.ScopedLvalues

/-!
# Evaluation positions of elaborated nonvolatile integer expressions

The expression layer retains source integer types, named whole-object reads,
arithmetic, casts, logical operators, conditional selection and comma.
Arithmetic permits an advance in either operand at every nesting depth.
Logical, conditional and comma expressions advance only their first operand
until the head rule selects the continuation. Untaken branches are retained
syntax rather than evaluated work.

The executable immediate-position enumerator is exhaustive for the separately
defined frame syntax. Frames and composed contexts have strict positive work
weights. This is an expression-control component, not complete C11 source
formation: writes, calls, pointer/floating expressions and source elaboration
remain obligations of the full abstract machine. Named reads use one declared
whole-object integer layout and its canonical integer-value parameters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.ReadExpression

open ObjectAccessMemory

inductive Fault where
  | arithmetic (reason : ArithmeticFault)
  | conversionSignal (identifier : Nat)
  | objectTrap (reason : IntegerBits.Trap)
  | paddingTrap
  deriving DecidableEq, Repr

inductive Expression (layout : Layout) where
  | value (scalar : IntegerScalar.Value layout.parameters)
  | read (name : String)
  | arithmetic (operation : IntegerBinaryOperator) (first second : Expression layout)
  | cast (type : IntegerType IntegerExtension) (operand : Expression layout)
  | truth (operand : Expression layout)
  | logicalNot (operand : Expression layout)
  | logicalAnd (first second : Expression layout)
  | logicalOr (first second : Expression layout)
  | conditional (type : IntegerType IntegerExtension) (test first second : Expression layout)
  | comma (first second : Expression layout)
  | fault (reason : Fault)
  deriving DecidableEq, Repr

def arithmeticResult (layout : Layout) : IntegerScalar.ArithmeticResult layout.parameters → Expression layout
  | .value scalar => .value scalar
  | .undefined _ reason => .fault (.arithmetic reason)

def castResult (layout : Layout) : IntegerScalar.CastResult layout.parameters → Expression layout
  | .value scalar => .value scalar
  | .signal identifier => .fault (.conversionSignal identifier)

def logical (layout : Layout) (value : Bool) : Expression layout :=
  .value (IntegerScalar.logicalValue layout.parameters value)

inductive Frame (layout : Layout) where
  | arithmeticLeft (operation : IntegerBinaryOperator) (second : Expression layout)
  | arithmeticRight (operation : IntegerBinaryOperator) (first : Expression layout)
  | cast (type : IntegerType IntegerExtension)
  | truth
  | logicalNot
  | logicalAnd (second : Expression layout)
  | logicalOr (second : Expression layout)
  | conditional (type : IntegerType IntegerExtension) (first second : Expression layout)
  | comma (second : Expression layout)
  deriving DecidableEq, Repr

def Frame.plug {layout : Layout} : Frame layout → Expression layout → Expression layout
  | .arithmeticLeft operation second, first => .arithmetic operation first second
  | .arithmeticRight operation first, second => .arithmetic operation first second
  | .cast type, operand => .cast type operand
  | .truth, operand => .truth operand
  | .logicalNot, operand => .logicalNot operand
  | .logicalAnd second, first => .logicalAnd first second
  | .logicalOr second, first => .logicalOr first second
  | .conditional type first second, test => .conditional type test first second
  | .comma second, first => .comma first second

def parts {layout : Layout} : Expression layout → List (Frame layout × Expression layout)
  | .arithmetic operation first second =>
      [(.arithmeticLeft operation second, first), (.arithmeticRight operation first, second)]
  | .cast type operand => [(.cast type, operand)]
  | .truth operand => [(.truth, operand)]
  | .logicalNot operand => [(.logicalNot, operand)]
  | .logicalAnd first second => [(.logicalAnd second, first)]
  | .logicalOr first second => [(.logicalOr second, first)]
  | .conditional type test first second => [(.conditional type first second, test)]
  | .comma first second => [(.comma second, first)]
  | .value _ | .read _ | .fault _ => []

theorem parts_iff {layout : Layout} (expression : Expression layout) (frame : Frame layout)
    (child : Expression layout) : (frame, child) ∈ parts expression ↔ frame.plug child = expression := by
  cases frame <;> cases expression <;>
    simp [parts, Frame.plug, and_comm, and_left_comm]

theorem parts_sound {layout : Layout} (expression : Expression layout) (part : Frame layout × Expression layout)
    (present : part ∈ parts expression) : part.1.plug part.2 = expression :=
  (parts_iff expression part.1 part.2).mp present

theorem parts_complete {layout : Layout} (frame : Frame layout) (child : Expression layout) :
    (frame, child) ∈ parts (frame.plug child) := (parts_iff _ frame child).mpr rfl

def weight {layout : Layout} : Expression layout → Nat
  | .value _ | .fault _ => 0
  | .read _ => 1
  | .arithmetic _ first second => 1 + weight first + weight second
  | .cast _ operand | .truth operand | .logicalNot operand => 1 + weight operand
  | .logicalAnd first second | .logicalOr first second => 2 + weight first + weight second
  | .conditional _ test first second => 2 + weight test + weight first + weight second
  | .comma first second => 1 + weight first + weight second

theorem frame_weight_positive {layout : Layout} (frame : Frame layout) (child : Expression layout) :
    weight child < weight (frame.plug child) := by
  cases frame <;> simp only [Frame.plug, weight] <;> omega

theorem parts_weight {layout : Layout} (expression : Expression layout)
    (part : Frame layout × Expression layout) (present : part ∈ parts expression) :
    weight part.2 < weight expression := by
  rw [← parts_sound expression part present]
  exact frame_weight_positive part.1 part.2

theorem frame_weight_monotone {layout : Layout} (frame : Frame layout)
    (first second : Expression layout) (decreased : weight second < weight first) :
    weight (frame.plug second) < weight (frame.plug first) := by
  cases frame <;> simp only [Frame.plug, weight] <;> omega

abbrev Context (layout : Layout) := List (Frame layout)

def plug {layout : Layout} : Context layout → Expression layout → Expression layout
  | [], expression => expression
  | frame :: rest, expression => frame.plug (plug rest expression)

theorem plug_append {layout : Layout} (outer inner : Context layout) (expression : Expression layout) :
    plug (outer ++ inner) expression = plug outer (plug inner expression) := by
  induction outer with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append, plug, ih]

theorem context_weight_monotone {layout : Layout} (context : Context layout)
    (first second : Expression layout) (decreased : weight second < weight first) :
    weight (plug context second) < weight (plug context first) := by
  induction context with
  | nil => exact decreased
  | cons frame rest ih => exact frame_weight_monotone frame _ _ ih

theorem arithmeticResult_weight (layout : Layout) (result : IntegerScalar.ArithmeticResult layout.parameters) :
    weight (arithmeticResult layout result) = 0 := by cases result <;> rfl

theorem castResult_weight (layout : Layout) (result : IntegerScalar.CastResult layout.parameters) :
    weight (castResult layout result) = 0 := by cases result <;> rfl

theorem logical_weight (layout : Layout) (value : Bool) : weight (logical layout value) = 0 := rfl

end Mettapedia.Languages.C11.ReadExpression

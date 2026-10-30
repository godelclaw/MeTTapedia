import Mathlib.Tactic

/-!
# A residual computation carries its ready values in bindings

The source distinguishes an already-computed value from its pending hole and
remaining calls. Closure conversion gives every ready occurrence a private port.
The target reads those ports in its captured environment; raw source data has
an independent interpretation which can execute or change code-shaped values.
The pending hole remains a computation through nested contexts.

The refinement preserves answers and ordered committed effects, including
failure. Paths name private ports in this finite model. Native fresh-ID
allocation, graph transport, source fuel and constraint registration remain
separate correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResumptionClosure

variable {Value Op Effect : Type}
abbrev Path := List Bool

structure Observation (Value Effect : Type) where
  value : Option Value
  trace : List Effect
  deriving DecidableEq, Repr

def returned (value : Value) : Observation Value Effect := ⟨some value, []⟩

def sequence (first : Observation Value Effect)
    (body : Value → Observation Value Effect) : Observation Value Effect :=
  match first.value with
  | none => first
  | some value =>
      let next := body value
      ⟨next.value, first.trace ++ next.trace⟩

inductive Source (Value Op : Type) where
  | ready (value : Value)
  | hole
  | call (operation : Op) (left right : Source Value Op)

inductive Syntax (Value Op : Type) where
  | port (key : Path)
  | raw (value : Value)
  | hole
  | call (operation : Op) (left right : Syntax Value Op)

abbrev Env (Value : Type) := Path → Option Value

def source (operation : Op → Value → Value → Observation Value Effect)
    (hole : Observation Value Effect) : Source Value Op → Observation Value Effect
  | .ready value => returned value
  | .hole => hole
  | .call op left right =>
      sequence (source operation hole left) fun a =>
        sequence (source operation hole right) (operation op a)

def target (operation : Op → Value → Value → Observation Value Effect)
    (interpret : Value → Observation Value Effect) (hole : Observation Value Effect)
    (env : Env Value) : Syntax Value Op → Observation Value Effect
  | .port key => ⟨env key, []⟩
  | .raw value => interpret value
  | .hole => hole
  | .call op left right =>
      sequence (target operation interpret hole env left) fun a =>
        sequence (target operation interpret hole env right) (operation op a)

def shiftPorts (path : Path) : Syntax Value Op → Syntax Value Op
  | .port key => .port (path ++ key)
  | .raw value => .raw value
  | .hole => .hole
  | .call op left right => .call op (shiftPorts path left) (shiftPorts path right)

def lower : Source Value Op → Syntax Value Op
  | .ready _ => .port []
  | .hole => .hole
  | .call op left right => .call op (shiftPorts [false] (lower left)) (shiftPorts [true] (lower right))

/-- Captured values are looked up independently of the target evaluator. -/
def capture : Source Value Op → Env Value
  | .ready value, [] => some value
  | .call _ left _, false :: path => capture left path
  | .call _ _ right, true :: path => capture right path
  | _, _ => none

theorem shift_reads_child (operation : Op → Value → Value → Observation Value Effect)
    (interpret : Value → Observation Value Effect) (hole : Observation Value Effect)
    (path : Path) (term : Syntax Value Op) (env : Env Value) :
    target operation interpret hole env (shiftPorts path term) =
      target operation interpret hole (fun key => env (path ++ key)) term := by
  induction term with
  | port key => rfl
  | raw value => rfl
  | hole => rfl
  | call op left right leftIH rightIH =>
      simp only [shiftPorts, target, leftIH, rightIH]

theorem lower_refines (operation : Op → Value → Value → Observation Value Effect)
    (interpret : Value → Observation Value Effect) (hole : Observation Value Effect)
    (term : Source Value Op) :
    target operation interpret hole (capture term) (lower term) = source operation hole term := by
  induction term with
  | ready value => rfl
  | hole => rfl
  | call op left right leftIH rightIH =>
      simp only [lower, target, shift_reads_child]
      change sequence (target operation interpret hole (capture left) (lower left))
        (fun a => sequence (target operation interpret hole (capture right) (lower right))
          (operation op a)) = _
      rw [leftIH, rightIH]
      rfl

theorem ready_values_ignore_source_interpretation
    (operation : Op → Value → Value → Observation Value Effect)
    (first second : Value → Observation Value Effect) (hole : Observation Value Effect)
    (term : Source Value Op) :
    target operation first hole (capture term) (lower term) =
      target operation second hole (capture term) (lower term) := by
  rw [lower_refines, lower_refines]

theorem exact_effect_trace (operation : Op → Value → Value → Observation Value Effect)
    (interpret : Value → Observation Value Effect) (hole : Observation Value Effect)
    (term : Source Value Op) :
    (target operation interpret hole (capture term) (lower term)).trace =
      (source operation hole term).trace := by
  rw [lower_refines]

namespace Controls

inductive Datum where
  | number (n : Nat)
  | code
  | executed
  | pair (left right : Datum)
  deriving DecidableEq, Repr

def interpret : Datum → Observation Datum Nat
  | .code => ⟨some .executed, [99]⟩
  | value => returned value

def pair (_ : Unit) (left right : Datum) : Observation Datum Nat :=
  returned (.pair left right)

def held : Source Datum Unit := .call () (.ready .code) .hole

def producer : Observation Datum Nat := ⟨some (.number 7), [1]⟩

theorem captured_code_stays_data :
    target pair interpret producer (capture held) (lower held) =
      ⟨some (.pair .code (.number 7)), [1]⟩ := rfl

theorem inserting_ready_syntax_executes_again :
    target pair interpret producer (fun _ => none) (.call () (.raw .code) .hole) =
      ⟨some (.pair .executed (.number 7)), [99, 1]⟩ := rfl

theorem nested_callers_keep_the_hole_computation :
    let nested : Source Datum Unit := .call () held (.ready (.number 9))
    target pair interpret producer (capture nested) (lower nested) =
      ⟨some (.pair (.pair .code (.number 7)) (.number 9)), [1]⟩ := rfl

theorem capturing_the_hole_loses_entered_work :
    target pair interpret producer (fun _ => none) (.port []) =
      ⟨none, []⟩ ∧ source pair producer (.hole : Source Datum Unit) = producer := by
  constructor <;> rfl

theorem duplicate_values_keep_two_positions :
    let duplicate : Source Datum Unit := .call () (.ready .code) (.ready .code)
    target pair interpret producer (capture duplicate) (lower duplicate) =
      ⟨some (.pair .code .code), []⟩ := rfl

theorem failed_hole_keeps_committed_effects :
    target pair interpret (⟨none, [1, 2]⟩ : Observation Datum Nat) (capture held) (lower held) =
      ⟨none, [1, 2]⟩ := rfl

end Controls
end Mettapedia.Machines.ResumptionClosure

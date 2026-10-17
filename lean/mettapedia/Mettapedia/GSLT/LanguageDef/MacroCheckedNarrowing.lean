import Mettapedia.Languages.C11.IntegerConversion

/-!
# Checked narrowing with failure-preserving destination state

The executable range selector and independent store rules specify the
Narrowing library's success/failure contract. The target uses the existing C11
integer format owner, including signed representations and unsigned ranges.

This is a value/store contract. It does not claim to prove GCC/Clang builtins,
argument evaluation effects, C printing, or the native macro implementation.
Those boundaries are checked separately by actual-template admission and
native compilation tests.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroCheckedNarrowing

open Mettapedia.Languages.C11

set_option autoImplicit false

inductive StoreRule (format : IntegerFormat) (input before : Int) : Bool → Int → Prop where
  | accept (lower : format.lower ≤ input) (upper : input ≤ format.upper) :
      StoreRule format input before true input
  | below (outside : input < format.lower) : StoreRule format input before false before
  | above (outside : format.upper < input) : StoreRule format input before false before

def execute (format : IntegerFormat) (input before : Int) : Bool × Int :=
  if input < format.lower then (false, before)
  else if format.upper < input then (false, before)
  else (true, input)

theorem execute_sound (format : IntegerFormat) (input before : Int) :
    StoreRule format input before (execute format input before).1
      (execute format input before).2 := by
  unfold execute
  split
  · exact .below (by assumption)
  · split
    · exact .above (by assumption)
    · exact .accept (by omega) (by omega)

theorem execute_complete {format : IntegerFormat} {input before after : Int} {accepted : Bool}
    (rule : StoreRule format input before accepted after) :
    execute format input before = (accepted, after) := by
  cases rule with
  | accept lower upper => simp [execute, show ¬ input < format.lower by omega,
      show ¬ format.upper < input by omega]
  | below outside => simp [execute, outside]
  | above outside =>
      have range := format.zero_representable
      simp only [IntegerFormat.Represents] at range
      simp [execute, outside, show ¬ input < format.lower by omega]

theorem execute_accepted_iff (format : IntegerFormat) (input before : Int) :
    (execute format input before).1 = true ↔ format.Represents input := by
  unfold execute IntegerFormat.Represents
  split
  · simp only [Bool.false_eq_true, false_iff]; omega
  · split
    · simp only [Bool.false_eq_true, false_iff]; omega
    · constructor
      · intro _; exact ⟨by omega, by omega⟩
      · intro _; rfl

theorem failure_preserves_destination (format : IntegerFormat) (input before : Int)
    (failed : (execute format input before).1 = false) :
    (execute format input before).2 = before := by
  by_cases below : input < format.lower
  · simp [execute, below]
  · by_cases above : format.upper < input
    · simp [execute, below, above]
    · simp [execute, below, above] at failed

theorem success_stores_input (format : IntegerFormat) (input before : Int)
    (accepted : (execute format input before).1 = true) :
    (execute format input before).2 = input := by
  by_cases below : input < format.lower
  · simp [execute, below] at accepted
  · by_cases above : format.upper < input
    · simp [execute, below, above] at accepted
    · simp [execute, below, above]

theorem rule_deterministic {format : IntegerFormat} {input before left right : Int}
    {acceptedLeft acceptedRight : Bool}
    (one : StoreRule format input before acceptedLeft left)
    (two : StoreRule format input before acceptedRight right) :
    acceptedLeft = acceptedRight ∧ left = right := by
  have equal := (execute_complete one).symm.trans (execute_complete two)
  exact ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩

example : execute (.unsigned 8 (by decide)) 255 22 = (true, 255) := by decide
example : execute (.unsigned 8 (by decide)) 256 22 = (false, 22) := by decide
example : execute (.unsigned 8 (by decide)) (-1) 22 = (false, 22) := by decide
example : execute (.signed 7 (by decide) (.twosComplement true)) (-128) 11 =
    (true, -128) := by decide
example : execute (.signed 7 (by decide) (.twosComplement true)) (-129) 11 =
    (false, 11) := by decide
example : ¬ StoreRule (.unsigned 8 (by decide)) 256 22 true 0 := by
  intro rule
  have impossible := execute_complete rule
  have observed : execute (.unsigned 8 (by decide)) 256 22 = (false, 22) := by decide
  rw [observed] at impossible
  cases impossible

#print axioms execute_sound
#print axioms execute_complete
#print axioms execute_accepted_iff
#print axioms failure_preserves_destination
#print axioms success_stores_input
#print axioms rule_deterministic

end Mettapedia.GSLT.LanguageDef.MacroCheckedNarrowing

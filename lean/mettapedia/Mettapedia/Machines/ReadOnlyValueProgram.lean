import Mettapedia.Machines.ReadOnlyQuery

/-!
# Value selection without binding effects

A compiled value program may carry unresolved values without interpreting
their syntax or matching them against patterns. Its operations are literals,
argument reads, construction, observations, and conditional selection.

The direct interpretation below is independently compiled into the existing
read-only query language. A failed operation means accelerator refusal, not
an empty answer family. In particular an unresolved branch condition must
return to a relational evaluator. Results retain the selected values, including
their variable identities; only code, never an observation, is reusable without
validating the input snapshot.

The native compiler's node classification and ownership remain implementation
conformance obligations. This module proves the value-algebra translation.
-/

namespace Mettapedia.Machines.ReadOnlyValueProgram

open ReadOnlyQuery

structure Algebra (Value Constructor Test : Type) where
  construct : Constructor → List Value → Option Value
  observe : Test → Value → Value
  branch : Value → Option Bool

mutual
  inductive Code (Value Constructor Test : Type) where
    | literal (value : Value)
    | argument (index : Nat)
    | build (constructor : Constructor) (arguments : Arguments Value Constructor Test)
    | observe (test : Test) (operand : Code Value Constructor Test)
    | branch (condition yes no : Code Value Constructor Test)
  inductive Arguments (Value Constructor Test : Type) where
    | nil
    | cons (first : Code Value Constructor Test) (rest : Arguments Value Constructor Test)
end

section Generic

variable {Value Constructor Test : Type}

mutual
  def evaluate (algebra : Algebra Value Constructor Test) (inputs : Nat → Value) :
      Code Value Constructor Test → Option Value
    | .literal value => some value
    | .argument index => some (inputs index)
    | .build constructor arguments =>
        (evaluateArguments algebra inputs arguments).bind (algebra.construct constructor)
    | .observe test operand => (evaluate algebra inputs operand).map (algebra.observe test)
    | .branch condition yes no =>
        match (evaluate algebra inputs condition).bind algebra.branch with
        | none => none
        | some true => evaluate algebra inputs yes
        | some false => evaluate algebra inputs no
  def evaluateArguments (algebra : Algebra Value Constructor Test) (inputs : Nat → Value) :
      Arguments Value Constructor Test → Option (List Value)
    | .nil => some []
    | .cons first rest => do
        let value ← evaluate algebra inputs first
        let values ← evaluateArguments algebra inputs rest
        pure (value :: values)
end

mutual
  def query (algebra : Algebra Value Constructor Test) :
      Code Value Constructor Test → Program Nat Value (Option Value)
    | .literal value => .pure (some value)
    | .argument index => .read index fun value => .pure (some value)
    | .build constructor arguments =>
        map (fun values => values.bind (algebra.construct constructor))
          (queryArguments algebra arguments)
    | .observe test operand => map (Option.map (algebra.observe test)) (query algebra operand)
    | .branch condition yes no =>
        bind (query algebra condition) fun value =>
          match value.bind algebra.branch with
          | none => .pure none
          | some true => query algebra yes
          | some false => query algebra no
  def queryArguments (algebra : Algebra Value Constructor Test) :
      Arguments Value Constructor Test → Program Nat Value (Option (List Value))
    | .nil => .pure (some [])
    | .cons first rest =>
        bind (query algebra first) fun value =>
          match value with
          | none => .pure none
          | some value => map (Option.map (List.cons value)) (queryArguments algebra rest)
end

mutual
  theorem query_evaluates (algebra : Algebra Value Constructor Test) (inputs : Nat → Value)
      (code : Code Value Constructor Test) :
      (run inputs (query algebra code)).answer = evaluate algebra inputs code := by
    cases code with
    | literal value => rfl
    | argument index => rfl
    | build constructor arguments =>
        simp [query, run_map, evaluate, queryArguments_evaluate]
    | observe test operand =>
        simp [query, run_map, evaluate, query_evaluates]
    | branch condition yes no =>
        simp only [query, run_bind, query_evaluates]
        cases hvalue : evaluate algebra inputs condition with
        | none => simp [hvalue, evaluate, run]
        | some value =>
            cases htruth : algebra.branch value with
            | none => simp [hvalue, htruth, evaluate, run]
            | some truth =>
                cases truth <;> simp [hvalue, htruth, evaluate, query_evaluates]
  theorem queryArguments_evaluate (algebra : Algebra Value Constructor Test)
      (inputs : Nat → Value) (arguments : Arguments Value Constructor Test) :
      (run inputs (queryArguments algebra arguments)).answer =
        evaluateArguments algebra inputs arguments := by
    cases arguments with
    | nil => rfl
    | cons first rest =>
        simp only [queryArguments, run_bind, query_evaluates]
        cases hvalue : evaluate algebra inputs first with
        | none => simp [hvalue, run, evaluateArguments]
        | some value =>
            cases hrest : evaluateArguments algebra inputs rest <;>
              simp [hvalue, hrest, run_map, evaluateArguments, queryArguments_evaluate]
end

/-- The existing adaptive read certificate applies to the actual composed
value program; agreement preserves its result and its selected control path. -/
theorem evaluate_eq_of_agrees (algebra : Algebra Value Constructor Test)
    (first second : Nat → Value) (code : Code Value Constructor Test)
    (agree : Agrees second (run first (query algebra code)).reads) :
    evaluate algebra second code = evaluate algebra first code := by
  rw [← query_evaluates, ← query_evaluates]
  exact congrArg Observation.answer (run_eq_of_agrees first second (query algebra code) agree)

/-- In the adaptive input-read model, any implementation that returns the
selected argument for every environment must read that argument. No bound is
claimed on allocation, native instructions, or an unobserved value's size. -/
theorem projection_read_necessary
    (program : Program Nat Value (Option Value)) (index : Nat)
    (inputs : Nat → Value) (alternative : Value)
    (different : alternative ≠ inputs index)
    (correct : ∀ environment, (run environment program).answer = some (environment index)) :
    ∃ observed ∈ (run inputs program).reads, observed.1 = index := by
  by_contra missing
  let changed : Nat → Value := Function.update inputs index alternative
  have agree : Agrees changed (run inputs program).reads := by
    intro observed member
    have other : observed.1 ≠ index := by
      intro same
      exact missing ⟨observed, member, same⟩
    change (Function.update inputs index alternative) observed.1 = observed.2
    rw [Function.update_of_ne other]
    exact run_agrees inputs program observed member
  have same := congrArg Observation.answer (run_eq_of_agrees inputs changed program agree)
  rw [correct, correct] at same
  apply different
  simpa [changed] using Option.some.inj same

/-- The compiled projection attains that lower bound with exactly one input
read; the selected value itself is returned without a structural traversal. -/
theorem projection_reads_exactly_once (algebra : Algebra Value Constructor Test)
    (inputs : Nat → Value) (index : Nat) :
    (run inputs (query algebra (.argument index))).reads = [(index, inputs index)] := by
  rfl

end Generic

namespace Controls

inductive Value where
  | variable (identity : Nat)
  | flag (value : Bool)
  | pair (left right : Value)
  deriving DecidableEq

inductive Test where
  | isVariable

inductive Constructor where
  | pair

def algebra : Algebra Value Constructor Test where
  construct constructor values := match constructor, values with
    | .pair, [left, right] => some (.pair left right)
    | _, _ => none
  observe _ value := .flag (match value with | .variable _ => true | _ => false)
  branch value := match value with
    | .flag truth => some truth
    | .pair _ _ => some false
    | .variable _ => none

def select : Code Value Constructor Test :=
  .branch (.observe .isVariable (.argument 0)) (.argument 1) (.literal (.flag false))

theorem selected_open_identity_survives :
    evaluate algebra (fun index => .variable (index + 7)) select = some (.variable 8) := by
  decide

theorem constructor_retains_aliases :
    evaluate algebra (fun _ => .variable 7)
      (.build .pair (.cons (.argument 0) (.cons (.argument 0) .nil))) =
      some (.pair (.variable 7) (.variable 7)) := by
  decide

/-- None requests relational fallback; it is not a claim of zero answers. -/
theorem unresolved_condition_declines :
    evaluate algebra (fun _ => .variable 7)
      (.branch (.argument 0) (.literal (.flag true)) (.literal (.flag false))) = none := by
  decide

/-- Reusing an earlier answer after an input changes can choose the wrong
branch, although reusing the compiled code remains valid. -/
theorem changed_input_changes_observation :
    evaluate algebra (fun index => .variable (index + 7)) select ≠
      evaluate algebra (fun _ => .flag true) select := by
  decide

end Controls
end Mettapedia.Machines.ReadOnlyValueProgram

import Mettapedia.Machines.ExecutionControl
import Mettapedia.Machines.RegisterCode

/-!
# Computation operands lowered into prepared register regions

The common coordinate reader supplies computations and an inert binding
pattern to the prepared node builder. The source reference instead reads the
written binding or branch layout. The resulting node is lowered by the
independent register compiler, whose execution preserves values, local
bindings and refusal under its scope discipline.

This join covers branch, single-binding and ordered binding-sequence regions. Native operand
classification, root invocation arguments, byte encoding, branch flattening,
semantic source charges and C pointer ownership remain separate obligations.
RegisterCode's call fuel is not identified with source fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedComputation

open ExecutionControl

variable {L O P H V : Type}

/-- The prepared fragment distinguishes code positions from inert patterns. -/
inductive Field (L O P H : Type) where
  | code (node : RegisterCode.Node L O P H)
  | pattern (value : P)
  | bindings (values : List (P × RegisterCode.Node L O P H))

/-- The prepared builder nests each binding around the remaining region. -/
def bindMany (bindings : List (P × RegisterCode.Node L O P H))
    (body : RegisterCode.Node L O P H) : RegisterCode.Node L O P H :=
  bindings.foldr (fun binding rest => .bind binding.2 binding.1 rest) body

/-- Independent source-state sequencing of producer, match, and next binding. -/
def evalBindings (sem : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (registers : RegisterCode.Regs V) :
    List (P × RegisterCode.Node L O P H) → RegisterCode.Node L O P H →
      Option (V × RegisterCode.Regs V)
  | [], body => RegisterCode.eval sem answer registers body
  | (pattern, producer) :: rest, body =>
      (RegisterCode.eval sem answer registers producer).bind fun produced =>
        (sem.bindLet pattern produced.1 produced.2).bind fun bound =>
          evalBindings sem answer bound rest body

theorem binding_sequence_refines (sem : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (registers : RegisterCode.Regs V)
    (bindings : List (P × RegisterCode.Node L O P H))
    (body : RegisterCode.Node L O P H) :
    RegisterCode.eval sem answer registers (bindMany bindings body) =
      evalBindings sem answer registers bindings body := by
  induction bindings generalizing registers with
  | nil => rfl
  | cons binding rest ih =>
      rcases binding with ⟨pattern, producer⟩
      simp only [bindMany, List.foldr_cons, RegisterCode.eval, evalBindings]
      simp only [← ih, bindMany]

/-- Build prepared nodes from the shared request, without inspecting a
physical wrapper head or evaluating either branch. -/
def lower : Request (Field L O P H) → Option (RegisterCode.Node L O P H)
  | .sequence (.code producer) (.pattern pattern) (.code body) =>
      some (.bind producer pattern body)
  | .sequenceMany (.bindings values) (.code body) => some (bindMany values body)
  | .branch (.code condition) (.code yes) (some (.code no)) =>
      some (.ite condition yes no)
  | _ => none

/-- Source interpretation independently destructures the admitted layouts. -/
def source : Head → List (Field L O P H) → Option (RegisterCode.Node L O P H)
  | .letBinding, [.pattern pattern, .code producer, .code body] =>
      some (.bind producer pattern body)
  | .chain, [.code producer, .pattern pattern, .code body] =>
      some (.bind producer pattern body)
  | .bindings, [.bindings values, .code body] => some (bindMany values body)
  | .branch, [.code condition, .code yes, .code no] =>
      some (.ite condition yes no)
  | _, _ => none

def elaborate (head : Head) (fields : List (Field L O P H)) :
    Option (RegisterCode.Node L O P H) :=
  ((ExecutionControl.elaborate head fields.length).bind
    (fun plan => read plan fields.toArray)).bind lower

theorem elaboration_refines (head : Head) (fields : List (Field L O P H)) :
    elaborate head fields = source head fields := by
  unfold elaborate
  rw [read_elaborate]
  cases fields with
  | nil => cases head <;> rfl
  | cons a rest =>
      cases rest with
      | nil => cases head <;> cases a <;> rfl
      | cons b rest =>
          cases rest with
          | nil => cases head <;> cases a <;> cases b <;> rfl
          | cons c rest =>
              cases rest with
              | nil => cases head <;> cases a <;> cases b <;> cases c <;> rfl
              | cons d rest =>
                  cases head <;> cases a <;> cases b <;> cases c <;> rfl

/-- Every admitted source node is checked against the register compiler's
local-variable and pattern discipline. Refused source shapes remain refused. -/
theorem register_answers
    (sem : RegisterCode.Sem V L O P H) (answer : H → List V → Option V)
    (fuses : O → Nat → Bool) (head : Head) (fields : List (Field L O P H))
    (locals destination next : Nat) (scope : Finset Nat)
    (registers sourceRegisters : RegisterCode.Regs V)
    (wellScoped : ∀ node, source head fields = some node →
      RegisterCode.Scoped sem.toPatterns locals scope node)
    (inside : ∀ index ∈ scope, index < locals)
    (agree : ∀ index ∈ scope, registers index = sourceRegisters index)
    (fresh : locals ≤ next) :
    Option.Rel (fun node code => RegisterCode.Answers
      (RegisterCode.eval sem answer sourceRegisters node)
      (RegisterCode.exec sem answer code registers))
      (source head fields)
      ((elaborate head fields).map
        (fun node => (RegisterCode.compile fuses node true destination next).1)) := by
  rw [elaboration_refines]
  cases selected : source head fields with
  | none => exact .none
  | some node =>
      exact .some (RegisterCode.lower_answers sem answer fuses
        (wellScoped node selected) inside agree fresh)

/-- Source operand relocation changes neither the conditional node nor its
branch-local register computations. -/
theorem reordered_branch (condition yes no : RegisterCode.Node L O P H) :
    (ExecutionControl.read ⟨.branch, some 2, some 1, some 0⟩
      #[Field.code no, .code yes, .code condition]).bind lower =
      some (.ite condition yes no) := by
  rfl

theorem reordered_binding (producer body : RegisterCode.Node L O P H) (pattern : P) :
    (ExecutionControl.read ⟨.sequence, some 1, some 2, some 0⟩
      #[Field.code body, .code producer, .pattern pattern]).bind lower =
      some (.bind producer pattern body) := by
  rfl

/-- A code operand in the pattern place is refused rather than executed as
part of prepared pattern matching. -/
theorem executable_pattern_refused (producer pattern body : RegisterCode.Node L O P H) :
    elaborate .letBinding [.code pattern, .code producer, .code body] = none := by
  rw [elaboration_refines]
  rfl

/-- Missing coordinates cannot select an arbitrary physical source field. -/
theorem missing_condition_refused (yes no : RegisterCode.Node L O P H) :
    (ExecutionControl.read ⟨.branch, none, some 0, some 1⟩ #[Field.code yes, .code no]).bind lower = none := by
  rfl

end Mettapedia.Machines.PreparedComputation

#print axioms Mettapedia.Machines.PreparedComputation.elaboration_refines
#print axioms Mettapedia.Machines.PreparedComputation.register_answers
#print axioms Mettapedia.Machines.PreparedComputation.reordered_branch
#print axioms Mettapedia.Machines.PreparedComputation.reordered_binding
#print axioms Mettapedia.Machines.PreparedComputation.executable_pattern_refused
#print axioms Mettapedia.Machines.PreparedComputation.missing_condition_refused

#print axioms Mettapedia.Machines.PreparedComputation.binding_sequence_refines

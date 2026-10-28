import Mettapedia.Machines.RegisterCode

/-!
# Prepared term is data, including its lexical slots

The source substitutes slots into a term tree and constructs its fields.
The lowering instead emits literal, slot and construction nodes for the
existing register executor. Its result is independent of the call oracle;
reading a repeated slot preserves the same carried value twice.

Closed source chunks are literals in this fragment. Native closed-chunk
classification, quotation admission, pointer ownership and Need updates have
separate implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedSyntax

inductive Syntax (Literal : Type) where
  | datum (value : Literal)
  | saved (index : Nat)
  | form (fields : List (Syntax Literal))
  deriving Repr

variable {V L O P H : Type}

mutual
  def lower (constructor : O) : Syntax L → RegisterCode.Node L O P H
    | .datum value => .lit value
    | .saved index => .slot index
    | .form fields => .op constructor (lowerFields constructor fields)
  termination_by term => sizeOf term

  def lowerFields (constructor : O) : List (Syntax L) → List (RegisterCode.Node L O P H)
    | [] => []
    | field :: rest => lower constructor field :: lowerFields constructor rest
  termination_by fields => sizeOf fields
end

mutual
  def source (sem : RegisterCode.Sem V L O P H) (constructor : O)
      (registers : RegisterCode.Regs V) : Syntax L → Option V
    | .datum value => some (sem.lit value)
    | .saved index => registers index
    | .form fields => (sourceFields sem constructor registers fields).bind (sem.op constructor)
  termination_by term => sizeOf term

  def sourceFields (sem : RegisterCode.Sem V L O P H) (constructor : O)
      (registers : RegisterCode.Regs V) : List (Syntax L) → Option (List V)
    | [] => some []
    | field :: rest => (source sem constructor registers field).bind fun first =>
        (sourceFields sem constructor registers rest).map (first :: ·)
  termination_by fields => sizeOf fields
end

mutual
  theorem lower_refines (sem : RegisterCode.Sem V L O P H) (constructor : O)
      (answer : H → List V → Option V) (registers : RegisterCode.Regs V)
      (term : Syntax L) :
      RegisterCode.eval sem answer registers (lower constructor term) =
        (source sem constructor registers term).map (fun value => (value, registers)) := by
    cases term with
    | datum => simp [lower, source, RegisterCode.eval]
    | saved => simp [lower, source, RegisterCode.eval]
    | form fields =>
        rw [lower, RegisterCode.eval,
          lowerFields_refine sem constructor answer registers fields]
        simp only [source]
        cases sourceFields sem constructor registers fields <;> rfl
  termination_by sizeOf term
  decreasing_by all_goals simp_wf

  theorem lowerFields_refine (sem : RegisterCode.Sem V L O P H) (constructor : O)
      (answer : H → List V → Option V) (registers : RegisterCode.Regs V)
      (fields : List (Syntax L)) :
      RegisterCode.evalList sem answer registers (lowerFields constructor fields) =
        (sourceFields sem constructor registers fields).map (fun values => (values, registers)) := by
    cases fields with
    | nil => simp [lowerFields, sourceFields, RegisterCode.evalList]
    | cons field rest =>
        rw [lowerFields, RegisterCode.evalList,
          lower_refines sem constructor answer registers field]
        cases found : source sem constructor registers field with
        | none => simp [sourceFields, found]
        | some value =>
            simp only [Option.map_some, Option.bind_some]
            rw [lowerFields_refine sem constructor answer registers rest]
            simp [sourceFields, found, Function.comp_def]
  termination_by sizeOf fields
  decreasing_by all_goals (simp_wf <;> omega)
end

/-- Literal operator spellings in data do not select a call oracle. -/
theorem invocation_independent (sem : RegisterCode.Sem V L O P H) (constructor : O)
    (first second : H → List V → Option V) (registers : RegisterCode.Regs V)
    (term : Syntax L) :
    RegisterCode.eval sem first registers (lower constructor term) =
      RegisterCode.eval sem second registers (lower constructor term) := by
  rw [lower_refines, lower_refines]

/-- The builder does not replace the lexical register state. -/
theorem registers_preserved (sem : RegisterCode.Sem V L O P H) (constructor : O)
    (answer : H → List V → Option V) (registers after : RegisterCode.Regs V)
    (term : Syntax L) (value : V)
    (finished : RegisterCode.eval sem answer registers (lower constructor term) =
      some (value, after)) : after = registers := by
  rw [lower_refines] at finished
  obtain ⟨result, _, equal⟩ := Option.map_eq_some_iff.mp finished
  exact (congrArg Prod.snd equal).symm

/-- An unbound lexical slot declines rather than inventing a value or running term. -/
theorem missing_slot_refuses (sem : RegisterCode.Sem V L O P H) (constructor : O)
    (answer : H → List V → Option V) (registers : RegisterCode.Regs V)
    (index : Nat) (missing : registers index = none) :
    RegisterCode.eval sem answer registers (lower constructor (.saved index)) = none := by
  simp [lower, RegisterCode.eval, missing]

/-- Two occurrences of a lexical value remain two uses of that same value;
no invocation or fresh suspension is inserted between them. -/
theorem repeated_slot_preserves_value (sem : RegisterCode.Sem V L O P H) (constructor : O)
    (answer : H → List V → Option V) (registers : RegisterCode.Regs V)
    (index : Nat) (value : V) (present : registers index = some value) :
    RegisterCode.eval sem answer registers
        (lower constructor (.form [.saved index, .saved index])) =
      (sem.op constructor [value, value]).map (fun result => (result, registers)) := by
  rw [lower_refines]
  simp [source, sourceFields, present]

end Mettapedia.Machines.PreparedSyntax

#print axioms Mettapedia.Machines.PreparedSyntax.lower_refines
#print axioms Mettapedia.Machines.PreparedSyntax.lowerFields_refine
#print axioms Mettapedia.Machines.PreparedSyntax.invocation_independent
#print axioms Mettapedia.Machines.PreparedSyntax.registers_preserved
#print axioms Mettapedia.Machines.PreparedSyntax.missing_slot_refuses
#print axioms Mettapedia.Machines.PreparedSyntax.repeated_slot_preserves_value

import Mettapedia.Machines.ParameterizedBodyEntry

/-!
# Staged entry from captured and supplied invocation spans

The source reads one flattened syntax operand list. The target first validates
head and total arity, stages the two borrowed spans separately, and publishes
slots only after both stages succeed. Contextual and open operands refuse;
ready values retain their positions and multiplicity without interpretation.

The model includes operand-read counts and preserves the prior invocation on
refusal. Native pointer lifetime, capability revisions and complete compiler
correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InvocationSpanEntry

inductive Operand (Value : Type) where
  | ready (value : Value)
  | contextual (value : Value) (scope : Nat)
  | unbound
  deriving DecidableEq, Repr

structure Scan (Value : Type) where
  values : Option (List Value)
  reads : Nat
  deriving DecidableEq, Repr

variable {Value : Type}

def scan : List (Operand Value) → Scan Value
  | [] => ⟨some [], 0⟩
  | .ready value :: rest =>
      let suffix := scan rest
      ⟨suffix.values.map (value :: ·), suffix.reads + 1⟩
  | .contextual _ _ :: _ => ⟨none, 1⟩
  | .unbound :: _ => ⟨none, 1⟩

def combine (left right : Scan Value) : Scan Value :=
  match left.values with
  | none => left
  | some values => ⟨right.values.map (values ++ ·), left.reads + right.reads⟩

theorem scan_append (left right : List (Operand Value)) :
    scan (left ++ right) = combine (scan left) (scan right) := by
  induction left with
  | nil => simp [scan, combine]
  | cons operand rest ih =>
      cases operand with
      | contextual value scope => simp [scan, combine]
      | unbound => simp [scan, combine]
      | ready value =>
          simp only [List.cons_append, scan, ih]
          cases found : (scan rest).values with
          | none => simp [combine, found]
          | some values =>
              simp [combine, found, Option.map_map, Function.comp_def]
              omega

def reference (expected head arity : Nat) (previous : List Value)
    (operands : List (Operand Value)) : List Value × Nat × Bool :=
  if head = expected ∧ operands.length = arity then
    let observed := scan operands
    match observed.values with
    | none => (previous, observed.reads, false)
    | some values => (values, observed.reads, true)
  else (previous, 0, false)

def target (expected head arity : Nat) (previous : List Value)
    (captured supplied : List (Operand Value)) : List Value × Nat × Bool :=
  if head = expected ∧ captured.length + supplied.length = arity then
    let first := scan captured
    match first.values with
    | none => (previous, first.reads, false)
    | some capturedValues =>
        let second := scan supplied
        match second.values with
        | none => (previous, first.reads + second.reads, false)
        | some suppliedValues =>
            (capturedValues ++ suppliedValues, first.reads + second.reads, true)
  else (previous, 0, false)

theorem target_refines (expected head arity : Nat) (previous : List Value)
    (captured supplied : List (Operand Value)) :
    target expected head arity previous captured supplied =
      reference expected head arity previous (captured ++ supplied) := by
  simp only [target, reference, List.length_append]
  split
  · rw [scan_append]
    cases first : (scan captured).values <;>
      cases second : (scan supplied).values <;> simp [combine, first, second]
  · rfl

theorem refused_preserves_entry (expected head arity : Nat) (previous : List Value)
    (captured supplied : List (Operand Value))
    (refused : (target expected head arity previous captured supplied).2.2 = false) :
    (target expected head arity previous captured supplied).1 = previous := by
  by_cases shape : head = expected ∧ captured.length + supplied.length = arity
  · cases first : (scan captured).values <;>
      cases second : (scan supplied).values <;>
      simp_all [target]
  · simp [target, shape]

theorem arity_refusal_reads_nothing (expected head arity : Nat) (previous : List Value)
    (captured supplied : List (Operand Value))
    (different : captured.length + supplied.length ≠ arity) :
    target expected head arity previous captured supplied = (previous, 0, false) := by
  simp [target, different]

theorem scan_ready (values : List Value) :
    scan (values.map Operand.ready) = ⟨some values, values.length⟩ := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [scan, ih]

theorem split_ready_entry (head : Nat) (previous captured supplied : List Value) :
    target head head (captured.length + supplied.length) previous
        (captured.map Operand.ready) (supplied.map Operand.ready) =
      (captured ++ supplied, captured.length + supplied.length, true) := by
  simp [target, scan_ready]

theorem staged_environment_refines {Name : Type} [DecidableEq Name]
    (head : Nat) (parameters : List Name) (previous captured supplied : List Value)
    (locals : Nat) (lengths : parameters.length = captured.length + supplied.length) :
    ParameterizedBodyEntry.source parameters (captured ++ supplied) =
      ParameterizedBodyEntry.target parameters
        (target head head (captured.length + supplied.length) previous
          (captured.map Operand.ready) (supplied.map Operand.ready)).1 locals := by
  rw [split_ready_entry]
  exact ParameterizedBodyEntry.environments_refine parameters (captured ++ supplied)
    locals (by simpa using lengths)

section Kernel

variable {Name Call Effect Fault Delay Suspension World Worker : Type} [DecidableEq Name]

abbrev Code := ContextualCBPV.Code Value Call Effect Fault Delay Suspension

variable (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension
    (ParameterizedBodyEntry.Environment Name Value) World Worker)
    (world : World) (head : Nat) (parameters : List Name)
    (previous captured supplied : List Value) (locals : Nat)
    (elaborate : ParameterizedBodyEntry.Environment Name Value → Code
      (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension))

theorem staged_kernel_slice_refines
    (lengths : parameters.length = captured.length + supplied.length) (allowance : Nat) :
    let sourceEnv := ParameterizedBodyEntry.source parameters (captured ++ supplied)
    let targetEnv := ParameterizedBodyEntry.target parameters
      (target head head (captured.length + supplied.length) previous
        (captured.map Operand.ready) (supplied.map Operand.ready)).1 locals
    (ContextualCBPV.core sem world sourceEnv).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world sourceEnv (elaborate sourceEnv)) =
      (ContextualCBPV.core sem world targetEnv).runSlice allowance
        (ContextualCBPV.initial (Worker := Worker) world targetEnv (elaborate targetEnv)) := by
  dsimp only
  rw [staged_environment_refines head parameters previous captured supplied locals lengths]

end Kernel

namespace Controls

theorem split_preserves_order_and_duplicates :
    target 4 4 3 [99] [.ready 7, .ready 7] [.ready 9] = ([7, 7, 9], 3, true) := by
  decide +kernel

theorem late_contextual_refusal_keeps_previous :
    target 4 4 2 [7, 8] [.ready 999] [.contextual 12 5] = ([7, 8], 2, false) := by
  decide +kernel

theorem wrong_arity_precedes_operand_reads :
    target 4 4 3 [7, 8] [.contextual 12 5] [.unbound] = ([7, 8], 0, false) := by
  decide +kernel

-- A prefix-writing target would corrupt the previous invocation on refusal.
def writesBeforeAdmission (previous captured : List Nat) : List Nat :=
  captured ++ previous.drop captured.length

theorem partial_publication_is_detected :
    writesBeforeAdmission [7, 8] [999] ≠
      (target 4 4 2 [7, 8] [.ready 999] [.contextual 12 5]).1 := by
  decide +kernel

end Controls
end Mettapedia.Machines.InvocationSpanEntry

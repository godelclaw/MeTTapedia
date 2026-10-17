import Mettapedia.Computability.FramedWordValidation

/-!
# Executed mapping of complete framed words

The caller transfers each original delimited word to an unchanged finite
machine, collects its complete output, and restores the order of the resulting
framed vector. Empty fields and repeated occurrences retain their boundaries.
The cost charges every input copy, subroutine run and output transfer. The
execution theorem concerns the existing framing of encoded words; arbitrary
malformed byte admission is a separate obligation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedWordMapping
open Turing StateTransition Turing.TM2.Stmt

variable (program : FinTM2)
local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin
variable [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)]
  [Inhabited (program.Γ program.k₁)]

abbrev Input := program.Γ program.k₀
abbrev Output := program.Γ program.k₁
abbrev Key := Option (Option (Option (Option program.K)))
abbrev Extra := Option (Option (Input program)) × Option (Input program) ×
  Option (Output program) × Option (Option (Output program))
abbrev State := program.σ × Extra program
abbrev Alphabet := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet
      (StackMachineRegisters.withStackAlphabet program.Γ (Option (Output program)))
      (Option (Output program))) (Input program)) (Option (Input program))
abbrev vectorKey : Key program := none
abbrev temporaryKey : Key program := some none
abbrev accumulatorKey : Key program := some (some none)
abbrev resultKey : Key program := some (some (some none))
abbrev sourceKey (key : program.K) : Key program := some (some (some (some key)))

def initial : State program := (program.initialState, none, none, none, none)

inductive Phase (Label : Type) where
  | scan | copy | restore | run (label : Label) | collect | reverse
  | rejectTemporary | rejectAccumulator
  deriving DecidableEq, Fintype

def body (label : program.Λ) : TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  StackMachineRegisters.withStack (Cell := Option (Input program)) id
    (StackMachineRegisters.withStack (Cell := Input program) id
      (StackMachineRegisters.withStack (Cell := Option (Output program)) id
        (StackMachineRegisters.withStack (Cell := Option (Output program)) id
          (StackMachineRegisters.returning (Extra := Extra program)
            Phase.run (fun _ => Phase.collect) (program.m label)))))

def statement (phase : Phase program.Λ) :
    TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  match phase with
  | .scan => pop (vectorKey program) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .reverse)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (temporaryKey program) (fun state => (state.2.1.getD none).getD default)
            (goto fun _ => .copy)) (goto fun _ => .restore)))
  | .copy => pop (vectorKey program) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .rejectTemporary)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (temporaryKey program) (fun state => (state.2.1.getD none).getD default)
            (goto fun _ => .copy)) (goto fun _ => .restore)))
  | .restore => pop (temporaryKey program) (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (sourceKey program program.k₀) (fun state => state.2.2.1.getD default) (goto fun _ => .restore))
        (load (fun _ => initial program) (goto fun _ => .run program.main)))
  | .run label => body program label
  | .collect => pop (sourceKey program program.k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell, state.2.2.2.2))
      (branch (fun state => state.2.2.2.1.isSome)
        (push (accumulatorKey program) (fun state => some (state.2.2.2.1.getD default))
          (goto fun _ => .collect))
        (push (accumulatorKey program) (fun _ => none)
          (load (fun _ => initial program) (goto fun _ => .scan))))
  | .reverse => pop (accumulatorKey program)
      (fun state cell => (state.1, state.2.1, state.2.2.1, state.2.2.2.1, cell))
      (branch (fun state => state.2.2.2.2.isSome)
        (push (resultKey program) (fun state => state.2.2.2.2.getD none) (goto fun _ => .reverse))
        (load (fun _ => initial program) halt))
  | .rejectTemporary => pop (temporaryKey program)
      (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .rejectTemporary)
        (goto fun _ => .rejectAccumulator))
  | .rejectAccumulator => pop (accumulatorKey program)
      (fun state cell => (state.1, state.2.1, state.2.2.1, state.2.2.2.1, cell))
      (branch (fun state => state.2.2.2.2.isSome) (goto fun _ => .rejectAccumulator)
        (load (fun _ => initial program) halt))

def machine : FinTM2 where
  K := Key program
  k₀ := vectorKey program
  k₁ := resultKey program
  Γ := Alphabet program
  Γk₀Fin := inferInstance
  Λ := Phase program.Λ
  main := .scan
  σ := State program
  initialState := initial program
  m := statement program

attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt

def config (phase : Option (Phase program.Λ)) (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (temporary : List (Input program))
    (accumulator result : List (Option (Output program))) : (machine program).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => vector
    | some none => temporary
    | some (some none) => accumulator
    | some (some (some none)) => result
    | some (some (some (some key))) => contents key

local macro "field_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, initial, vectorKey, temporaryKey,
    accumulatorKey, resultKey, sourceKey, TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key with
              | none => rfl
              | some key =>
                by_cases same : key = program.k₀
                · subst key; simp [Function.update]
                · simp [Function.update, same])))

theorem scan_byte (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .scan) state contents (some head :: tail) temporary accumulator result) =
      some (config program (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) accumulator result) := by field_step

theorem copy_byte (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .copy) state contents (some head :: tail) temporary accumulator result) =
      some (config program (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) accumulator result) := by field_step

theorem copy_delimiter (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .copy) state contents (none :: tail) temporary accumulator result) =
      some (config program (some .restore) (state.1, some none, state.2.2)
        contents tail temporary accumulator result) := by field_step

theorem scan_delimiter (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .scan) state contents (none :: tail) temporary accumulator result) =
      some (config program (some .restore) (state.1, some none, state.2.2)
        contents tail temporary accumulator result) := by field_step

theorem restore_byte (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program) (tail : List (Input program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .restore) state contents vector (head :: tail) accumulator result) =
      some (config program (some .restore) (state.1, state.2.1, some head, state.2.2.2)
        (Function.update contents program.k₀ (head :: contents program.k₀)) vector tail accumulator result) := by field_step

theorem restore_empty (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .restore) state contents vector [] accumulator result) =
      some (config program (some (.run program.main))
        (initial program) contents vector [] accumulator result) := by field_step


local macro "output_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, initial, accumulatorKey,
    resultKey, sourceKey, TM2.step, TM2.stepAux]
  all_goals first
    | rfl
    | (funext key; cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key with
              | none => rfl
              | some key =>
                by_cases same : key = program.k₁
                · subst key; simp [Function.update]
                · simp [Function.update, same])))

theorem collect_byte (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Output program) (tail : List (Output program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program)))
    (present : contents program.k₁ = head :: tail) :
    (machine program).step (config program (some .collect) state contents vector [] accumulator result) =
      some (config program (some .collect)
        (state.1, state.2.1, state.2.2.1, some head, state.2.2.2.2)
        (Function.update contents program.k₁ tail) vector [] (some head :: accumulator) result) := by output_step

theorem collect_empty (state : State program) (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program)))
    (present : contents program.k₁ = []) :
    (machine program).step (config program (some .collect) state contents vector [] accumulator result) =
      some (config program (some .scan) (initial program)
        (Function.update contents program.k₁ []) vector [] (none :: accumulator) result) := by output_step

theorem scan_empty (state : State program) (contents : ∀ key, List (program.Γ key))
    (accumulator result : List (Option (Output program))) :
    (machine program).step (config program (some .scan) state contents [] [] accumulator result) =
      some (config program (some .reverse) (state.1, none, state.2.2)
        contents [] [] accumulator result) := by field_step

theorem reverse_byte (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Option (Output program)) (tail result : List (Option (Output program))) :
    (machine program).step (config program (some .reverse) state contents [] [] (head :: tail) result) =
      some (config program (some .reverse)
        (state.1, state.2.1, state.2.2.1, state.2.2.2.1, some head)
        contents [] [] tail (head :: result)) := by field_step

theorem reverse_empty (state : State program) (contents : ∀ key, List (program.Γ key))
    (result : List (Option (Output program))) :
    (machine program).step (config program (some .reverse) state contents [] [] [] result) =
      some (config program none (initial program) contents [] [] [] result) := by field_step

/-- Every original subroutine transition is retained, with both output arenas
and the unprocessed input vector held fixed. -/
theorem run_step (vector : List (Option (Input program)))
    (accumulator result : List (Option (Output program)))
    (before after : program.Cfg) (computed : program.step before = some after) :
    (machine program).step
      (config program (some (before.l.elim .collect .run))
        (before.var, none, none, none, none) before.stk vector [] accumulator result) =
      some (config program (some (after.l.elim .collect .run))
        (after.var, none, none, none, none) after.stk vector [] accumulator result) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, config, TM2.step, Option.elim_some]
      have cells : (config program (some (.run label))
          (state, none, none, none, none) contents vector [] accumulator result).stk =
          StackMachineRegisters.withStackContents (Cell := Option (Input program))
            (StackMachineRegisters.withStackContents (Cell := Input program)
              (StackMachineRegisters.withStackContents (Cell := Option (Output program))
                (StackMachineRegisters.withStackContents (Cell := Option (Output program)) contents result)
                accumulator) []) vector := by
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key <;> rfl
      trans some (TM2.stepAux (body program label) (state, none, none, none, none)
        (StackMachineRegisters.withStackContents (Cell := Option (Input program))
          (StackMachineRegisters.withStackContents (Cell := Input program)
            (StackMachineRegisters.withStackContents (Cell := Option (Output program))
              (StackMachineRegisters.withStackContents (Cell := Option (Output program)) contents result)
              accumulator) []) vector))
      · exact congrArg (fun words => some (TM2.stepAux (body program label)
          (state, none, none, none, none) words)) cells
      · unfold body
        rw [StackMachineRegisters.stepAux_withStack, StackMachineRegisters.stepAux_withStack,
          StackMachineRegisters.stepAux_withStack, StackMachineRegisters.stepAux_withStack,
          StackMachineRegisters.stepAux_returning]
        simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.returningConfig,
          Option.map_some, id_eq]
        congr 2
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key <;> rfl

noncomputable def runExecution (vector : List (Option (Input program)))
    (accumulator result : List (Option (Output program)))
    {before after : program.Cfg} {bound : Nat}
    (execution : EvalsToInTime program.step before (some after) bound) :
    EvalsToInTime (machine program).step
      (config program (some (before.l.elim .collect .run))
        (before.var, none, none, none, none) before.stk vector [] accumulator result)
      (some (config program (some (after.l.elim .collect .run))
        (after.var, none, none, none, none) after.stk vector [] accumulator result)) bound :=
  StackMachineComposition.lift_execution program.step (machine program).step
    (fun source => config program (some (source.l.elim .collect .run))
      (source.var, none, none, none, none) source.stk vector [] accumulator result)
    (run_step program vector accumulator result) execution

noncomputable def copyRun (state : State program)
    (contents : ∀ key, List (program.Γ key)) (word temporary : List (Input program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .copy) state contents (word.map some ++ none :: vector) temporary accumulator result)
      (some (config program (some .restore) (state.1, some none, state.2.2)
        contents vector (word.reverse ++ temporary) accumulator result)) (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] using
      StackMachineComposition.oneStep (copy_delimiter program state contents vector temporary accumulator result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (copy_byte program state contents head (tail.map some ++ none :: vector) temporary accumulator result)
    have rest := ih (state.1, some (some head), state.2.2) (head :: temporary)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def scanRun (state : State program)
    (word : List (Input program)) (vector : List (Option (Input program))) (accumulator result : List (Option (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .scan) state (fun _ => []) (word.map some ++ none :: vector) [] accumulator result)
      (some (config program (some .restore) (state.1, some none, state.2.2)
        (fun _ => []) vector word.reverse accumulator result)) (word.length + 1) := by
  cases word with
  | nil => simpa only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] using
      StackMachineComposition.oneStep (scan_delimiter program state (fun _ => []) vector [] accumulator result)
  | cons head tail =>
    have first := StackMachineComposition.oneStep
      (scan_byte program state (fun _ => []) head (tail.map some ++ none :: vector) [] accumulator result)
    have rest := copyRun program (state.1, some (some head), state.2.2) (fun _ => []) tail [head] vector accumulator result
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def restoreRun (state : State program)
    (contents : ∀ key, List (program.Γ key)) (temporary : List (Input program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .restore) state contents vector temporary accumulator result)
      (some (config program (some (.run program.main))
        (initial program)
        (Function.update contents program.k₀ (temporary.reverse ++ contents program.k₀)) vector [] accumulator result))
      (temporary.length + 1) := by
  induction temporary generalizing state contents with
  | nil => simpa only [List.reverse_nil, List.nil_append, Function.update_eq_self, List.length_nil] using
      StackMachineComposition.oneStep (restore_empty program state contents vector accumulator result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (restore_byte program state contents head tail vector accumulator result)
    have rest := ih (state.1, state.2.1, some head, state.2.2.2)
      (Function.update contents program.k₀ (head :: contents program.k₀))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, Function.update_self, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined



noncomputable def collectRun (state : State program)
    (contents : ∀ key, List (program.Γ key)) (word : List (Output program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program)))
    (present : contents program.k₁ = word) :
    EvalsToInTime (machine program).step
      (config program (some .collect) state contents vector [] accumulator result)
      (some (config program (some .scan) (initial program)
        (Function.update contents program.k₁ []) vector []
        (none :: (word.reverse.map some ++ accumulator)) result)) (word.length + 1) := by
  induction word generalizing state contents accumulator with
  | nil => simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.length_nil] using
      StackMachineComposition.oneStep (collect_empty program state contents vector accumulator result present)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (collect_byte program state contents head tail vector accumulator result present)
    have rest := ih (state.1, state.2.1, state.2.2.1, some head, state.2.2.2.2)
      (Function.update contents program.k₁ tail) (some head :: accumulator) (by simp)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append, List.nil_append, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def reverseRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (accumulator result : List (Option (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .reverse) state contents [] [] accumulator result)
      (some (config program none (initial program) contents [] [] [] (accumulator.reverse ++ result)))
      (accumulator.length + 1) := by
  induction accumulator generalizing state result with
  | nil => simpa only [List.reverse_nil, List.nil_append, List.length_nil] using
      StackMachineComposition.oneStep (reverse_empty program state contents result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (reverse_byte program state contents head tail result)
    have rest := ih (state.1, state.2.1, state.2.2.1, state.2.2.2.1, some head) (head :: result)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append,
      List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- Each field consumes its own original execution and stores the entire
result, including the delimiter for an empty output. -/
noncomputable def fieldRun (word : List (Input program)) (emitted : List (Output program))
    (vector : List (Option (Input program))) (accumulator result : List (Option (Output program)))
    (bound : Nat) (execution : TM2OutputsInTime program word (some emitted) bound) :
    EvalsToInTime (machine program).step
      (config program (some .scan) (initial program) (fun _ => [])
        (word.map some ++ none :: vector) [] accumulator result)
      (some (config program (some .scan) (initial program) (fun _ => []) vector []
        (none :: (emitted.reverse.map some ++ accumulator)) result))
      (bound + 2 * word.length + emitted.length + 3) := by
  have scanned := scanRun program (initial program) word vector accumulator result
  have restored := restoreRun program (program.initialState, some none, none, none, none)
    (fun _ => []) word.reverse vector accumulator result
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have walked := runExecution program vector accumulator result execution
  rw [RetainedWordExecution.source_init, RetainedWordExecution.source_halt] at walked
  simp only [Option.elim_some, Option.elim_none, RetainedWordExecution.wordContents] at walked
  have collected := collectRun program (initial program)
    (RetainedWordExecution.wordContents program program.k₁ emitted) emitted vector accumulator result
    (by simp [RetainedWordExecution.wordContents])
  simp only [RetainedWordExecution.wordContents, Function.update_idem, Function.update_eq_self] at collected
  have a := EvalsToInTime.trans _ _ _ _ _ _ scanned restored
  have b := EvalsToInTime.trans _ _ _ _ _ _ a walked
  have c := EvalsToInTime.trans _ _ _ _ _ _ b collected
  convert c using 1
  omega

def vectorClock {Value : Type} (encode : Value → List (Input program))
    (emit : Value → List (Output program)) (clock : Value → Nat) (values : List Value) : Nat :=
  (values.map (fun value => clock value + 2 * (encode value).length + (emit value).length + 3)).sum + 1

def totalClock {Value : Type} (encode : Value → List (Input program))
    (emit : Value → List (Output program)) (clock : Value → Nat) (values : List Value) : Nat :=
  vectorClock program encode emit clock values +
    (WordTemplateMachine.Indexed.frame (values.map emit)).length + 1

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)]
  [Inhabited (program.Γ program.k₁)] in
/-- Closed resource account after collecting and reversing every output. -/
theorem totalClock_eq {Value : Type} (encode : Value → List (Input program))
    (emit : Value → List (Output program)) (clock : Value → Nat) (values : List Value) :
    totalClock program encode emit clock values =
      (values.map (fun value => clock value + 2 * (encode value).length +
        2 * (emit value).length + 4)).sum + 2 := by
  induction values with
  | nil => simp [totalClock, vectorClock, WordTemplateMachine.Indexed.frame]
  | cons value rest ih =>
    simp only [totalClock, vectorClock, List.map_cons, List.sum_cons,
      WordTemplateMachine.Indexed.frame, List.flatMap_cons, List.length_append,
      List.length_map, List.length_cons, List.length_nil] at *
    omega

/-- All occurrences execute in order, even when two fields have equal bytes.
The output accumulator is a physical reversed frame, never an internal list. -/
noncomputable def vectorRun {Value : Type}
    (encode : Value → List (Input program)) (emit : Value → List (Output program)) (clock : Value → Nat)
    (runs : ∀ value, TM2OutputsInTime program (encode value) (some (emit value)) (clock value))
    (values : List Value) (accumulator result : List (Option (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .scan) (initial program) (fun _ => [])
        (WordTemplateMachine.Indexed.frame (values.map encode)) [] accumulator result)
      (some (config program (some .reverse) (initial program) (fun _ => []) [] []
        ((WordTemplateMachine.Indexed.frame (values.map emit)).reverse ++ accumulator) result))
      (vectorClock program encode emit clock values) := by
  induction values generalizing accumulator with
  | nil =>
    simpa [WordTemplateMachine.Indexed.frame, vectorClock, initial] using
      StackMachineComposition.oneStep (scan_empty program (initial program) (fun _ => []) accumulator result)
  | cons value rest ih =>
    have first := fieldRun program (encode value) (emit value)
      (WordTemplateMachine.Indexed.frame (rest.map encode)) accumulator result (clock value) (runs value)
    have last := ih (none :: ((emit value).reverse.map some ++ accumulator))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first last
    simpa [WordTemplateMachine.Indexed.frame, vectorClock, List.reverse_append, List.map_reverse,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem init_eq (input : List (Option (Input program))) :
    initList (machine program) input =
      config program (some .scan) (initial program) (fun _ => []) input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [vectorKey]
  | some key => cases key with
    | none => simp [vectorKey]
    | some key => cases key with
      | none => simp [vectorKey]
      | some key => cases key <;> simp [vectorKey]

theorem halt_eq (result : List (Option (Output program))) :
    haltList (machine program) result =
      config program none (initial program) (fun _ => []) [] [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key with
      | none => simp [resultKey]
      | some key => cases key <;> simp [resultKey]

/-- One original machine maps an arbitrary framed vector with a joined clock.
All subroutine stacks are empty after return, and no field boundary is lost. -/
noncomputable def outputs {Value : Type}
    (encode : Value → List (Input program)) (emit : Value → List (Output program)) (clock : Value → Nat)
    (runs : ∀ value, TM2OutputsInTime program (encode value) (some (emit value)) (clock value))
    (values : List Value) :
    TM2OutputsInTime (machine program) (WordTemplateMachine.Indexed.frame (values.map encode))
      (some (WordTemplateMachine.Indexed.frame (values.map emit))) (totalClock program encode emit clock values) := by
  have fields := vectorRun program encode emit clock runs values [] []
  simp only [List.append_nil] at fields
  have restored := reverseRun program (initial program) (fun _ => [])
    (WordTemplateMachine.Indexed.frame (values.map emit)).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have joined := EvalsToInTime.trans _ _ _ _ _ _ fields restored
  change EvalsToInTime _ (initList (machine program) _) (some (haltList (machine program) _)) _
  rw [init_eq, halt_eq]
  simpa only [totalClock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem finiteAlphabet (finite : ∀ key, Finite (program.Γ key)) (key : (machine program).K) :
    Finite ((machine program).Γ key) := by
  cases key with
  | none => exact inferInstanceAs (Finite (Option (Input program)))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite (Input program))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite (Option (Output program)))
      | some key => cases key with
        | none => exact inferInstanceAs (Finite (Option (Output program)))
        | some key => exact finite key

end Mettapedia.Computability.FramedWordMapping

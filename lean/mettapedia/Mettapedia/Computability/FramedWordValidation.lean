import Mettapedia.Computability.RetainedWordExecution
import Mettapedia.Computability.WordTemplateMachine

/-!
# Executing a validator on every framed word

A caller physically copies each delimited field into an unchanged subroutine,
reads its Boolean result and combines all results in original field order.
Dynamic fields remain on physical stacks. The input framing is the existing
indexed-template framing; the subroutine supplies its original image-domain
execution law. This caller introduces neither a field parser nor a semantic
validation judgment.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedWordValidation
open Turing StateTransition Turing.TM2.Stmt

variable (program : FinTM2)
local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin
variable [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)]

abbrev Input := program.Γ program.k₀
abbrev Output := program.Γ program.k₁
abbrev Key := Option (Option (Option program.K))
abbrev Extra := Option (Option (Input program)) × Option (Input program) × Option (Output program) × Bool
abbrev State := program.σ × Extra program
abbrev Alphabet := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet program.Γ (Option Bool)) (Input program)) (Option (Input program))
abbrev vectorKey : Key program := none
abbrev temporaryKey : Key program := some none
abbrev resultKey : Key program := some (some none)
abbrev sourceKey (key : program.K) : Key program := some (some (some key))

inductive Phase (Label : Type) where
  | scan | copy | restore | run (label : Label) | read | drain | finish | rejectTemporary
  deriving DecidableEq, Fintype

def body (label : program.Λ) : TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  StackMachineRegisters.withStack (Cell := Option (Input program)) id
    (StackMachineRegisters.withStack (Cell := Input program) id
      (StackMachineRegisters.withStack (Cell := Option Bool) id
        (StackMachineRegisters.returning (Extra := Extra program)
          Phase.run (fun _ => Phase.read) (program.m label))))

def statement (readResult : Output program → Bool) (phase : Phase program.Λ) :
    TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  match phase with
  | .scan => pop (vectorKey program) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .finish)
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
        (load (fun state => (program.initialState, none, none, none, state.2.2.2.2))
          (goto fun _ => .run program.main)))
  | .run label => body program label
  | .read => pop (sourceKey program program.k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell, state.2.2.2.2))
      (load (fun state => (state.1, state.2.1, state.2.2.1, state.2.2.2.1,
        state.2.2.2.2 && state.2.2.2.1.elim false readResult)) (goto fun _ => .drain))
  | .drain => pop (sourceKey program program.k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell, state.2.2.2.2))
      (branch (fun state => state.2.2.2.1.isSome) (goto fun _ => .drain)
        (load (fun state => (program.initialState, none, none, none, state.2.2.2.2)) (goto fun _ => .scan)))
  | .finish => push (resultKey program) (fun state => some state.2.2.2.2)
      (load (fun _ => (program.initialState, none, none, none, true)) halt)
  | .rejectTemporary => pop (temporaryKey program)
      (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .rejectTemporary)
        (push (resultKey program) (fun _ => some false)
          (load (fun _ => (program.initialState, none, none, none, true)) halt)))

def machine (readResult : Output program → Bool) : FinTM2 where
  K := Key program
  k₀ := vectorKey program
  k₁ := resultKey program
  Γ := Alphabet program
  Γk₀Fin := inferInstance
  Λ := Phase program.Λ
  main := .scan
  σ := State program
  initialState := (program.initialState, none, none, none, true)
  m := statement program readResult

attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt

theorem machine_body (readResult : Output program → Bool) (phase : Phase program.Λ) :
    (machine program readResult).m phase = statement program readResult phase := rfl

def config (readResult : Output program → Bool) (phase : Option (Phase program.Λ))
    (state : State program) (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (temporary : List (Input program))
    (result : List (Option Bool)) : (machine program readResult).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => vector
    | some none => temporary
    | some (some none) => result
    | some (some (some key)) => contents key

local macro "field_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, vectorKey, temporaryKey, resultKey, sourceKey,
    TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key =>
              by_cases same : key = program.k₀
              · subst key; simp [Function.update]
              · simp [Function.update, same])))

theorem scan_byte (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .scan) state contents (some head :: tail) temporary result) =
      some (config program readResult (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) result) := by field_step

theorem copy_byte (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .copy) state contents (some head :: tail) temporary result) =
      some (config program readResult (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) result) := by field_step

theorem copy_delimiter (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .copy) state contents (none :: tail) temporary result) =
      some (config program readResult (some .restore) (state.1, some none, state.2.2)
        contents tail temporary result) := by field_step

theorem scan_delimiter (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .scan) state contents (none :: tail) temporary result) =
      some (config program readResult (some .restore) (state.1, some none, state.2.2)
        contents tail temporary result) := by field_step

theorem restore_byte (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Input program) (tail : List (Input program))
    (vector : List (Option (Input program))) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .restore) state contents vector (head :: tail) result) =
      some (config program readResult (some .restore) (state.1, state.2.1, some head, state.2.2.2)
        (Function.update contents program.k₀ (head :: contents program.k₀)) vector tail result) := by field_step

theorem restore_empty (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .restore) state contents vector [] result) =
      some (config program readResult (some (.run program.main))
        (program.initialState, none, none, none, state.2.2.2.2) contents vector [] result) := by field_step

theorem read_one (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (head : Output program)
    (vector : List (Option (Input program))) (result : List (Option Bool))
    (present : contents program.k₁ = [head]) :
    (machine program readResult).step (config program readResult (some .read) state contents vector [] result) =
      some (config program readResult (some .drain)
        (state.1, state.2.1, state.2.2.1, some head, state.2.2.2.2 && readResult head)
        (Function.update contents program.k₁ []) vector [] result) := by
  simp_all [FinTM2.step, machine, statement, config, sourceKey, TM2.step, TM2.stepAux]
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key =>
        by_cases same : key = program.k₁
        · subst key; simp [Function.update]
        · simp [Function.update, same]

theorem drain_empty (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key))
    (vector : List (Option (Input program))) (result : List (Option Bool))
    (present : contents program.k₁ = []) :
    (machine program readResult).step (config program readResult (some .drain) state contents vector [] result) =
      some (config program readResult (some .scan)
        (program.initialState, none, none, none, state.2.2.2.2)
        (Function.update contents program.k₁ []) vector [] result) := by
  simp_all [FinTM2.step, machine, statement, config, sourceKey, TM2.step, TM2.stepAux]
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key =>
        by_cases same : key = program.k₁
        · subst key; simp [Function.update]
        · simp [Function.update, same]

theorem scan_empty (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .scan) state contents [] [] result) =
      some (config program readResult (some .finish) (state.1, none, state.2.2) contents [] [] result) := by field_step

theorem finish_step (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (result : List (Option Bool)) :
    (machine program readResult).step (config program readResult (some .finish) state contents [] [] result) =
      some (config program readResult none (program.initialState, none, none, none, true)
        contents [] [] (some state.2.2.2.2 :: result)) := by field_step

/-- The caller runs the existing subroutine without changing its transitions,
retaining the untouched remainder of the framed vector. -/
theorem run_step (readResult : Output program → Bool) (vector : List (Option (Input program)))
    (accumulator : Bool) (before after : program.Cfg) (computed : program.step before = some after) :
    (machine program readResult).step
      (config program readResult (some (before.l.elim .read .run))
        (before.var, none, none, none, accumulator) before.stk vector [] []) =
      some (config program readResult (some (after.l.elim .read .run))
        (after.var, none, none, none, accumulator) after.stk vector [] []) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, config, TM2.step, Option.elim_some]
      have cells : (config program readResult (some (.run label))
          (state, none, none, none, accumulator) contents vector [] []).stk =
          StackMachineRegisters.withStackContents (Cell := Option (Input program))
            (StackMachineRegisters.withStackContents (Cell := Input program)
              (StackMachineRegisters.withStackContents (Cell := Option Bool) contents []) []) vector := by
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl
      trans some (TM2.stepAux (body program label) (state, none, none, none, accumulator)
        (StackMachineRegisters.withStackContents (Cell := Option (Input program))
          (StackMachineRegisters.withStackContents (Cell := Input program)
            (StackMachineRegisters.withStackContents (Cell := Option Bool) contents []) []) vector))
      · exact congrArg (fun words => some (TM2.stepAux (body program label)
          (state, none, none, none, accumulator) words)) cells
      · unfold body
        rw [StackMachineRegisters.stepAux_withStack, StackMachineRegisters.stepAux_withStack,
          StackMachineRegisters.stepAux_withStack, StackMachineRegisters.stepAux_returning]
        simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.returningConfig,
          Option.map_some, id_eq]
        congr 2
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl

noncomputable def runExecution (readResult : Output program → Bool) (vector : List (Option (Input program)))
    (accumulator : Bool) {before after : program.Cfg} {bound : Nat}
    (execution : EvalsToInTime program.step before (some after) bound) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some (before.l.elim .read .run))
        (before.var, none, none, none, accumulator) before.stk vector [] [])
      (some (config program readResult (some (after.l.elim .read .run))
        (after.var, none, none, none, accumulator) after.stk vector [] [])) bound :=
  StackMachineComposition.lift_execution program.step (machine program readResult).step
    (fun source => config program readResult (some (source.l.elim .read .run))
      (source.var, none, none, none, accumulator) source.stk vector [] [])
    (run_step program readResult vector accumulator) execution

noncomputable def copyRun (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (word temporary : List (Input program))
    (vector : List (Option (Input program))) (result : List (Option Bool)) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .copy) state contents (word.map some ++ none :: vector) temporary result)
      (some (config program readResult (some .restore) (state.1, some none, state.2.2)
        contents vector (word.reverse ++ temporary) result)) (word.length + 1) := by
  induction word generalizing state temporary with
  | nil => simpa only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] using
      StackMachineComposition.oneStep (copy_delimiter program readResult state contents vector temporary result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (copy_byte program readResult state contents head (tail.map some ++ none :: vector) temporary result)
    have rest := ih (state.1, some (some head), state.2.2) (head :: temporary)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def scanRun (readResult : Output program → Bool) (state : State program)
    (word : List (Input program)) (vector : List (Option (Input program))) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) state (fun _ => []) (word.map some ++ none :: vector) [] [])
      (some (config program readResult (some .restore) (state.1, some none, state.2.2)
        (fun _ => []) vector word.reverse [])) (word.length + 1) := by
  cases word with
  | nil => simpa only [List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] using
      StackMachineComposition.oneStep (scan_delimiter program readResult state (fun _ => []) vector [] [])
  | cons head tail =>
    have first := StackMachineComposition.oneStep
      (scan_byte program readResult state (fun _ => []) head (tail.map some ++ none :: vector) [] [])
    have rest := copyRun program readResult (state.1, some (some head), state.2.2) (fun _ => []) tail [head] vector []
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def restoreRun (readResult : Output program → Bool) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (temporary : List (Input program))
    (vector : List (Option (Input program))) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .restore) state contents vector temporary [])
      (some (config program readResult (some (.run program.main))
        (program.initialState, none, none, none, state.2.2.2.2)
        (Function.update contents program.k₀ (temporary.reverse ++ contents program.k₀)) vector [] []))
      (temporary.length + 1) := by
  induction temporary generalizing state contents with
  | nil => simpa only [List.reverse_nil, List.nil_append, Function.update_eq_self, List.length_nil] using
      StackMachineComposition.oneStep (restore_empty program readResult state contents vector [])
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (restore_byte program readResult state contents head tail vector [])
    have rest := ih (state.1, state.2.1, some head, state.2.2.2)
      (Function.update contents program.k₀ (head :: contents program.k₀))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, Function.update_self, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined


/-- One whole field is physically copied, executed and cleared. The caller
continues even when its previous accumulated result was false. -/
noncomputable def fieldRun (readResult : Output program → Bool) (word : List (Input program))
    (head : Output program) (vector : List (Option (Input program))) (accumulator : Bool) (bound : Nat)
    (execution : TM2OutputsInTime program word (some [head]) bound) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (program.initialState, none, none, none, accumulator)
        (fun _ => []) (word.map some ++ none :: vector) [] [])
      (some (config program readResult (some .scan)
        (program.initialState, none, none, none, accumulator && readResult head)
        (fun _ => []) vector [] [])) (bound + 2 * word.length + 4) := by
  have scanned := scanRun program readResult (program.initialState, none, none, none, accumulator) word vector
  have restored := restoreRun program readResult (program.initialState, some none, none, none, accumulator)
    (fun _ => []) word.reverse vector
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have walked := runExecution program readResult vector accumulator execution
  rw [RetainedWordExecution.source_init, RetainedWordExecution.source_halt] at walked
  simp only [Option.elim_some, Option.elim_none, RetainedWordExecution.wordContents] at walked
  have read := StackMachineComposition.oneStep
    (read_one program readResult (program.initialState, none, none, none, accumulator)
      (RetainedWordExecution.wordContents program program.k₁ [head]) head vector []
      (by simp [RetainedWordExecution.wordContents]))
  have drained := StackMachineComposition.oneStep
    (drain_empty program readResult (program.initialState, none, none, some head, accumulator && readResult head)
      (fun _ => []) vector [] (by rfl))
  simp only [RetainedWordExecution.wordContents, Function.update_idem, Function.update_eq_self] at read drained
  have a := EvalsToInTime.trans _ _ _ _ _ _ scanned restored
  have b := EvalsToInTime.trans _ _ _ _ _ _ a walked
  have c := EvalsToInTime.trans _ _ _ _ _ _ b read
  have d := EvalsToInTime.trans _ _ _ _ _ _ c drained
  convert d using 1
  omega

def frameWords {Value : Type} (encode : Value → List (Input program)) (values : List Value) :
    List (Option (Input program)) := WordTemplateMachine.Indexed.frame (values.map encode)

def responses {Value : Type} (readResult : Output program → Bool) (response : Value → Output program) :
    List Value → Bool
  | [] => true
  | value :: rest => readResult (response value) && responses readResult response rest

def totalClock {Value : Type} (encode : Value → List (Input program)) (clock : Value → Nat)
    (values : List Value) : Nat :=
  (values.map (fun value => clock value + 2 * (encode value).length + 4)).sum + 2

/-- Every field executes in authored order. No accumulated false result
short-circuits a later field's original subroutine. -/
noncomputable def vectorRun {Value : Type} (readResult : Output program → Bool)
    (encode : Value → List (Input program)) (response : Value → Output program) (clock : Value → Nat)
    (runs : ∀ value, TM2OutputsInTime program (encode value) (some [response value]) (clock value))
    (values : List Value) (accumulator : Bool) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (program.initialState, none, none, none, accumulator)
        (fun _ => []) (frameWords program encode values) [] [])
      (some (config program readResult none (program.initialState, none, none, none, true)
        (fun _ => []) [] [] [some (accumulator && responses program readResult response values)]))
      (totalClock program encode clock values) := by
  induction values generalizing accumulator with
  | nil =>
    have first := StackMachineComposition.oneStep
      (scan_empty program readResult (program.initialState, none, none, none, accumulator) (fun _ => []) [])
    have last := StackMachineComposition.oneStep
      (finish_step program readResult (program.initialState, none, none, none, accumulator) (fun _ => []) [])
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first last
    simpa [frameWords, WordTemplateMachine.Indexed.frame, responses, totalClock] using joined
  | cons value rest ih =>
    have first := fieldRun program readResult (encode value) (response value)
      (frameWords program encode rest) accumulator (clock value) (runs value)
    have last := ih (accumulator && readResult (response value))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first last
    simpa [frameWords, WordTemplateMachine.Indexed.frame, responses, totalClock,
      Bool.and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem init_eq (readResult : Output program → Bool) (input : List (Option (Input program))) :
    initList (machine program readResult) input =
      config program readResult (some .scan) (program.initialState, none, none, none, true)
        (fun _ => []) input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [vectorKey]
  | some key => cases key with
    | none => simp [vectorKey]
    | some key => cases key <;> simp [vectorKey]

theorem halt_eq (readResult : Output program → Bool) (result : List (Option Bool)) :
    haltList (machine program readResult) result =
      config program readResult none (program.initialState, none, none, none, true)
        (fun _ => []) [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key <;> simp [resultKey]

/-- The input is the existing delimiter framing of complete original fields.
Each field uses its supplied original execution theorem, and every physical
copy, return, result read and cleanup is charged. -/
noncomputable def outputs {Value : Type} (readResult : Output program → Bool)
    (encode : Value → List (Input program)) (response : Value → Output program) (clock : Value → Nat)
    (runs : ∀ value, TM2OutputsInTime program (encode value) (some [response value]) (clock value))
    (values : List Value) :
    TM2OutputsInTime (machine program readResult) (frameWords program encode values)
      (some [some (responses program readResult response values)]) (totalClock program encode clock values) := by
  change EvalsToInTime _ (initList (machine program readResult) _) (some (haltList (machine program readResult) _)) _
  rw [init_eq, halt_eq]
  simpa only [Bool.true_and] using vectorRun program readResult encode response clock runs values true


local instance (readResult : Output program → Bool) : Fintype
    ((machine program readResult).Γ (machine program readResult).k₁) := by
  change Fintype (Option Bool)
  infer_instance

local instance (readResult : Output program → Bool) : Inhabited
    ((machine program readResult).Γ (machine program readResult).k₀) := by
  change Inhabited (Option (Input program))
  infer_instance

def readBoolean (result : Option Bool) : Bool := result.getD false

/-- A retaining caller preserves the complete original framed vector while
reading the validation result. This uses the existing physical retention
protocol, including its own copy and restoration costs. -/
def retainedMachine (readResult : Output program → Bool) : FinTM2 :=
  RetainedWordExecution.machine (machine program readResult) readBoolean

attribute [local implicit_reducible] retainedMachine

noncomputable def retainedOutputs {Value : Type} (readResult : Output program → Bool)
    (encode : Value → List (Input program)) (response : Value → Output program) (clock : Value → Nat)
    (runs : ∀ value, TM2OutputsInTime program (encode value) (some [response value]) (clock value))
    (values : List Value) :
    TM2OutputsInTime (retainedMachine program readResult) (frameWords program encode values)
      (some (.inr (responses program readResult response values) ::
        (frameWords program encode values).map Sum.inl))
      (totalClock program encode clock values + 3 * (frameWords program encode values).length + 5) := by
  simpa only [retainedMachine, readBoolean, Option.getD_some, List.length_nil, Nat.add_zero] using
    RetainedWordExecution.outputs (machine program readResult) readBoolean
      (frameWords program encode values) (some (responses program readResult response values)) []
      (totalClock program encode clock values)
      (outputs program readResult encode response clock runs values)

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- Field lengths include their existing physical delimiters. A quadratic
callee bound composes without charging represented numbers as unary data. -/
theorem totalClock_quadratic {Value : Type} (encode : Value → List (Input program))
    (clock : Value → Nat) (coefficient : Nat)
    (bounded : ∀ value, clock value ≤ coefficient * ((encode value).length + 1)^2)
    (values : List Value) :
    totalClock program encode clock values ≤
      (coefficient + 4) * (frameWords program encode values).length^2 + 2 := by
  induction values with
  | nil => simp [totalClock, frameWords, WordTemplateMachine.Indexed.frame]
  | cons value rest ih =>
    have head := bounded value
    have field : clock value + 2 * (encode value).length + 4 ≤
        (coefficient + 4) * ((encode value).length + 1)^2 := by
      nlinarith
    have extent : (frameWords program encode (value :: rest)).length =
        (encode value).length + 1 + (frameWords program encode rest).length := by
      simp [frameWords, WordTemplateMachine.Indexed.frame, List.flatMap_map]
      omega
    have split : totalClock program encode clock (value :: rest) =
        clock value + 2 * (encode value).length + 4 + totalClock program encode clock rest := by
      simp [totalClock]; omega
    rw [extent, split]
    nlinarith

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- Retaining the complete original vector adds physical copying, restoration
and cleanup to the same quadratic account. -/
theorem retainedClock_quadratic {Value : Type} (encode : Value → List (Input program))
    (clock : Value → Nat) (coefficient : Nat)
    (bounded : ∀ value, clock value ≤ coefficient * ((encode value).length + 1)^2)
    (values : List Value) :
    totalClock program encode clock values + 3 * (frameWords program encode values).length + 5 ≤
      (coefficient + 12) * ((frameWords program encode values).length + 1)^2 := by
  have original := totalClock_quadratic program encode clock coefficient bounded values
  nlinarith


end Mettapedia.Computability.FramedWordValidation

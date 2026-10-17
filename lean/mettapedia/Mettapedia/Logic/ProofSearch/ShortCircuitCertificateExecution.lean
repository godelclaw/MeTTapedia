import Mettapedia.Logic.ProofSearch.FirstCertificateExecution

/-!
# Search that stops checking at its first accepted certificate

A finite physical caller reads the existing framed candidate vector, invokes
an unchanged checker, and returns the first accepted original word. Rejected
candidates are cleared before the next call. After success, the unread vector
is discarded without checker calls. All copying, return, discard and cleanup
transitions are included in one clock.

`CheckedPrefix` records only actual checker executions before and including
success, so no termination premise is imposed on the unread suffix. The
singleton-response specialization computes the original `List.find?` result.
The first-success clock separates performed checker work from unread input
bytes. Candidate generation, scheduling and arbitrary malformed wire inputs
are separate obligations; this caller makes no polynomial proof-search claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.ProofSearch.ShortCircuitCertificateExecution
open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineComposition (oneStep)

variable (program : FinTM2)
  [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)]
  (readResult : program.Γ program.k₁ → Bool)
local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin

abbrev Input := program.Γ program.k₀
abbrev retained := RetainedWordExecution.machine program readResult
abbrev Key := Option (Option (Option (retained program readResult).K))
abbrev Extra := Option (Option (Input program)) × Option (Input program) × Option (Input program ⊕ Bool)
abbrev State := (retained program readResult).σ × Extra program
abbrev Alphabet := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet (retained program readResult).Γ
      (Input program ⊕ Bool)) (Input program)) (Option (Input program))
abbrev vectorKey : Key program readResult := none
abbrev temporaryKey : Key program readResult := some none
abbrev resultKey : Key program readResult := some (some none)
abbrev sourceKey (key : (retained program readResult).K) : Key program readResult := some (some (some key))

def initial : State program readResult := ((retained program readResult).initialState, none, none, none)

inductive Phase (Label : Type) where
  | scan | copy | restoreInput | run (label : Label) | read
  | discardOutput | capture | drainVector | restoreOutput | rejectTemporary
  deriving DecidableEq, Fintype

def body (label : (retained program readResult).Λ) :
    TM2.Stmt (Alphabet program readResult) (Phase (retained program readResult).Λ) (State program readResult) :=
  StackMachineRegisters.withStack (Cell := Option (Input program)) id
    (StackMachineRegisters.withStack (Cell := Input program) id
      (StackMachineRegisters.withStack (Cell := Input program ⊕ Bool) id
        (StackMachineRegisters.returning (Extra := Extra program) Phase.run (fun _ => .read)
          ((retained program readResult).m label))))

def statement (phase : Phase (retained program readResult).Λ) :
    TM2.Stmt (Alphabet program readResult) (Phase (retained program readResult).Λ) (State program readResult) :=
  match phase with
  | .scan => pop (vectorKey program readResult) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone)
        (push (resultKey program readResult) (fun _ => .inr false)
          (load (fun _ => initial program readResult) halt))
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (temporaryKey program readResult) (fun state => (state.2.1.getD none).getD default)
            (goto fun _ => .copy)) (goto fun _ => .restoreInput)))
  | .copy => pop (vectorKey program readResult) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .rejectTemporary)
        (branch (fun state => (state.2.1.getD none).isSome)
          (push (temporaryKey program readResult) (fun state => (state.2.1.getD none).getD default)
            (goto fun _ => .copy)) (goto fun _ => .restoreInput)))
  | .restoreInput => pop (temporaryKey program readResult) (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (sourceKey program readResult (retained program readResult).k₀)
          (fun state => state.2.2.1.getD default) (goto fun _ => .restoreInput))
        (load (fun _ => initial program readResult) (goto fun _ => .run (retained program readResult).main)))
  | .run label => body program readResult label
  | .read => pop (sourceKey program readResult (retained program readResult).k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell))
      (branch (fun state => match state.2.2.2 with
        | some (.inr true) => true | _ => false)
        (goto fun _ => .capture) (goto fun _ => .discardOutput))
  | .discardOutput => pop (sourceKey program readResult (retained program readResult).k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell))
      (branch (fun state => state.2.2.2.isSome) (goto fun _ => .discardOutput)
        (load (fun _ => initial program readResult) (goto fun _ => .scan)))
  | .capture => pop (sourceKey program readResult (retained program readResult).k₁)
      (fun state cell => (state.1, state.2.1, state.2.2.1, cell))
      (branch (fun state => state.2.2.2.isSome)
        (push (temporaryKey program readResult) (fun state => match state.2.2.2 with
          | some (.inl symbol) => symbol | _ => default) (goto fun _ => .capture))
        (goto fun _ => .drainVector))
  | .drainVector => pop (vectorKey program readResult) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .drainVector)
        (goto fun _ => .restoreOutput))
  | .restoreOutput => pop (temporaryKey program readResult) (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (resultKey program readResult) (fun state => .inl (state.2.2.1.getD default))
          (goto fun _ => .restoreOutput))
        (push (resultKey program readResult) (fun _ => .inr true)
          (load (fun _ => initial program readResult) halt)))
  | .rejectTemporary => pop (temporaryKey program readResult) (fun state cell => (state.1, state.2.1, cell, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome) (goto fun _ => .rejectTemporary)
        (push (resultKey program readResult) (fun _ => .inr false)
          (load (fun _ => initial program readResult) halt)))

def machine : FinTM2 where
  K := Key program readResult
  k₀ := vectorKey program readResult
  k₁ := resultKey program readResult
  Γ := Alphabet program readResult
  Γk₀Fin := inferInstance
  Λ := Phase (retained program readResult).Λ
  main := .scan
  σ := State program readResult
  initialState := initial program readResult
  m := statement program readResult

attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt
  RetainedWordExecution.machine

def config (phase : Option (Phase (retained program readResult).Λ)) (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (vector : List (Option (Input program))) (temporary : List (Input program))
    (result : List (Input program ⊕ Bool)) : (machine program readResult).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => vector
    | some none => temporary
    | some (some none) => result
    | some (some (some key)) => contents key

local macro "field_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, initial, vectorKey, temporaryKey, resultKey, sourceKey,
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
              by_cases same : key = (retained program readResult).k₀
              · subst key; simp [Function.update]
              · simp [Function.update, same])))

theorem scan_byte (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .scan) state contents (some head :: tail) temporary result) =
      some (config program readResult (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) result) := by field_step

theorem copy_byte (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Input program)
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .copy) state contents (some head :: tail) temporary result) =
      some (config program readResult (some .copy) (state.1, some (some head), state.2.2)
        contents tail (head :: temporary) result) := by field_step

theorem copy_delimiter (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .copy) state contents (none :: tail) temporary result) =
      some (config program readResult (some .restoreInput) (state.1, some none, state.2.2)
        contents tail temporary result) := by field_step

theorem scan_delimiter (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (tail : List (Option (Input program))) (temporary : List (Input program)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .scan) state contents (none :: tail) temporary result) =
      some (config program readResult (some .restoreInput) (state.1, some none, state.2.2)
        contents tail temporary result) := by field_step

theorem restore_byte (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Input program) (tail : List (Input program))
    (vector : List (Option (Input program))) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .restoreInput) state contents vector (head :: tail) result) =
      some (config program readResult (some .restoreInput) (state.1, state.2.1, some head, state.2.2.2)
        (Function.update contents (retained program readResult).k₀ (head :: contents (retained program readResult).k₀)) vector tail result) := by field_step

theorem restore_empty (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (vector : List (Option (Input program))) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step (config program readResult (some .restoreInput) state contents vector [] result) =
      some (config program readResult (some (.run (retained program readResult).main))
        ((retained program readResult).initialState, none, none, none) contents vector [] result) := by field_step


theorem run_step (vector : List (Option (Input program)))
    (before after : (retained program readResult).Cfg) (computed : (retained program readResult).step before = some after) :
    (machine program readResult).step
      (config program readResult (some (before.l.elim .read .run))
        (before.var, none, none, none) before.stk vector [] []) =
      some (config program readResult (some (after.l.elim .read .run))
        (after.var, none, none, none) after.stk vector [] []) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, config, TM2.step, Option.elim_some]
      have cells : (config program readResult (some (.run label))
          (state, none, none, none) contents vector [] []).stk =
          StackMachineRegisters.withStackContents (Cell := Option (Input program))
            (StackMachineRegisters.withStackContents (Cell := Input program)
              (StackMachineRegisters.withStackContents (Cell := Input program ⊕ Bool) contents []) []) vector := by
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl
      trans some (TM2.stepAux (body program readResult label) (state, none, none, none)
        (StackMachineRegisters.withStackContents (Cell := Option (Input program))
          (StackMachineRegisters.withStackContents (Cell := Input program)
            (StackMachineRegisters.withStackContents (Cell := Input program ⊕ Bool) contents []) []) vector))
      · exact congrArg (fun words => some (TM2.stepAux (body program readResult label)
          (state, none, none, none) words)) cells
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

noncomputable def runExecution (vector : List (Option (Input program)))
    {before after : (retained program readResult).Cfg} {bound : Nat}
    (execution : EvalsToInTime (retained program readResult).step before (some after) bound) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some (before.l.elim .read .run))
        (before.var, none, none, none) before.stk vector [] [])
      (some (config program readResult (some (after.l.elim .read .run))
        (after.var, none, none, none) after.stk vector [] [])) bound :=
  StackMachineComposition.lift_execution (retained program readResult).step (machine program readResult).step
    (fun source => config program readResult (some (source.l.elim .read .run))
      (source.var, none, none, none) source.stk vector [] [])
    (run_step program readResult vector) execution

noncomputable def copyRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (word temporary : List (Input program))
    (vector : List (Option (Input program))) (result : List (Input program ⊕ Bool)) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .copy) state contents (word.map some ++ none :: vector) temporary result)
      (some (config program readResult (some .restoreInput) (state.1, some none, state.2.2)
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

noncomputable def scanRun (state : State program readResult)
    (word : List (Input program)) (vector : List (Option (Input program))) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) state (fun _ => []) (word.map some ++ none :: vector) [] [])
      (some (config program readResult (some .restoreInput) (state.1, some none, state.2.2)
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

noncomputable def restoreRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (temporary : List (Input program))
    (vector : List (Option (Input program))) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .restoreInput) state contents vector temporary [])
      (some (config program readResult (some (.run (retained program readResult).main))
        ((retained program readResult).initialState, none, none, none)
        (Function.update contents (retained program readResult).k₀
          (temporary.reverse ++ (show List (Input program) from contents (retained program readResult).k₀))) vector [] []))
      (temporary.length + 1) := by
  induction temporary generalizing state contents with
  | nil => simpa only [List.reverse_nil, List.nil_append, Function.update_eq_self, List.length_nil] using
      StackMachineComposition.oneStep (restore_empty program readResult state contents vector [])
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (restore_byte program readResult state contents head tail vector [])
    have rest := ih (state.1, state.2.1, some head, state.2.2.2)
      (Function.update contents (retained program readResult).k₀ (head :: contents (retained program readResult).k₀))
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, Function.update_self, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined




local macro "output_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, initial, vectorKey, temporaryKey, resultKey, sourceKey,
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
              by_cases same : key = (retained program readResult).k₁
              · subst key; simp [Function.update]
              · simp [Function.update, same])))

theorem read_tag (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (tag : Bool) (word : List (Input program ⊕ Bool)) (vector : List (Option (Input program)))
    (output : contents (retained program readResult).k₁ = .inr tag :: word) :
    (machine program readResult).step
      (config program readResult (some .read) state contents vector [] []) =
    some (config program readResult (some (if tag then .capture else .discardOutput))
      (state.1, state.2.1, state.2.2.1, some (.inr tag))
      (Function.update contents (retained program readResult).k₁ word) vector [] []) := by
  cases tag <;> output_step

theorem discard_cons (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (head : Input program ⊕ Bool) (tail : List (Input program ⊕ Bool)) (vector : List (Option (Input program)))
    (output : contents (retained program readResult).k₁ = head :: tail) :
    (machine program readResult).step
      (config program readResult (some .discardOutput) state contents vector [] []) =
    some (config program readResult (some .discardOutput)
      (state.1, state.2.1, state.2.2.1, some head)
      (Function.update contents (retained program readResult).k₁ tail) vector [] []) := by output_step

theorem discard_nil (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (vector : List (Option (Input program)))
    (output : contents (retained program readResult).k₁ = []) :
    (machine program readResult).step
      (config program readResult (some .discardOutput) state contents vector [] []) =
    some (config program readResult (some .scan) (initial program readResult)
      (Function.update contents (retained program readResult).k₁ []) vector [] []) := by output_step

theorem capture_cons (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Input program)
    (tail : List (Input program ⊕ Bool)) (vector : List (Option (Input program))) (temporary : List (Input program))
    (output : contents (retained program readResult).k₁ = .inl head :: tail) :
    (machine program readResult).step
      (config program readResult (some .capture) state contents vector temporary []) =
    some (config program readResult (some .capture)
      (state.1, state.2.1, state.2.2.1, some (.inl head))
      (Function.update contents (retained program readResult).k₁ tail) vector (head :: temporary) []) := by output_step

theorem capture_nil (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (vector : List (Option (Input program)))
    (temporary : List (Input program)) (output : contents (retained program readResult).k₁ = []) :
    (machine program readResult).step
      (config program readResult (some .capture) state contents vector temporary []) =
    some (config program readResult (some .drainVector)
      (state.1, state.2.1, state.2.2.1, none)
      (Function.update contents (retained program readResult).k₁ []) vector temporary []) := by output_step

theorem drain_cons (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Option (Input program))
    (tail : List (Option (Input program))) (temporary : List (Input program)) :
    (machine program readResult).step
      (config program readResult (some .drainVector) state contents (head :: tail) temporary []) =
    some (config program readResult (some .drainVector)
      (state.1, some head, state.2.2) contents tail temporary []) := by field_step

theorem drain_nil (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (temporary : List (Input program)) :
    (machine program readResult).step
      (config program readResult (some .drainVector) state contents [] temporary []) =
    some (config program readResult (some .restoreOutput)
      (state.1, none, state.2.2) contents [] temporary []) := by field_step

theorem result_cons (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (head : Input program)
    (tail : List (Input program)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step
      (config program readResult (some .restoreOutput) state contents [] (head :: tail) result) =
    some (config program readResult (some .restoreOutput)
      (state.1, state.2.1, some head, state.2.2.2) contents [] tail (.inl head :: result)) := by field_step

theorem result_nil (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key)) (result : List (Input program ⊕ Bool)) :
    (machine program readResult).step
      (config program readResult (some .restoreOutput) state contents [] [] result) =
    some (config program readResult none (initial program readResult)
      contents [] [] (.inr true :: result)) := by field_step

theorem scan_nil :
    (machine program readResult).step
      (config program readResult (some .scan) (initial program readResult) (fun _ => []) [] [] []) =
    some (config program readResult none (initial program readResult) (fun _ => []) [] [] [.inr false]) := by field_step


noncomputable def discardRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (word : List (Input program ⊕ Bool)) (vector : List (Option (Input program)))
    (present : contents (retained program readResult).k₁ = word) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .discardOutput) state contents vector [] [])
      (some (config program readResult (some .scan) (initial program readResult)
        (Function.update contents (retained program readResult).k₁ []) vector [] [])) (word.length + 1) := by
  induction word generalizing contents state with
  | nil => exact oneStep (discard_nil program readResult state contents vector present)
  | cons head tail ih =>
    have first := oneStep (discard_cons program readResult state contents head tail vector present)
    have rest := ih (state.1, state.2.1, state.2.2.1, some head)
      (Function.update contents (retained program readResult).k₁ tail) (by simp)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def captureRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (word temporary : List (Input program)) (vector : List (Option (Input program)))
    (present : contents (retained program readResult).k₁ = word.map Sum.inl) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .capture) state contents vector temporary [])
      (some (config program readResult (some .drainVector)
        (state.1, state.2.1, state.2.2.1, none)
        (Function.update contents (retained program readResult).k₁ []) vector (word.reverse ++ temporary) []))
      (word.length + 1) := by
  induction word generalizing contents state temporary with
  | nil => simpa only [List.reverse_nil, List.nil_append, List.length_nil] using
      oneStep (capture_nil program readResult state contents vector temporary present)
  | cons head tail ih =>
    have first := oneStep (capture_cons program readResult state contents head (tail.map Sum.inl) vector temporary present)
    have rest := ih (state.1, state.2.1, state.2.2.1, some (.inl head))
      (Function.update contents (retained program readResult).k₁ (tail.map Sum.inl)) (head :: temporary) (by simp)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def drainRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (vector : List (Option (Input program))) (temporary : List (Input program)) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .drainVector) state contents vector temporary [])
      (some (config program readResult (some .restoreOutput)
        (state.1, none, state.2.2) contents [] temporary [])) (vector.length + 1) := by
  induction vector generalizing state with
  | nil => exact oneStep (drain_nil program readResult state contents temporary)
  | cons head tail ih =>
    have first := oneStep (drain_cons program readResult state contents head tail temporary)
    have rest := ih (state.1, some head, state.2.2)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def resultRun (state : State program readResult)
    (contents : ∀ key, List ((retained program readResult).Γ key))
    (temporary : List (Input program)) (result : List (Input program ⊕ Bool)) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .restoreOutput) state contents [] temporary result)
      (some (config program readResult none (initial program readResult)
        contents [] [] (.inr true :: temporary.reverse.map Sum.inl ++ result))) (temporary.length + 1) := by
  induction temporary generalizing state result with
  | nil => simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.cons_append, List.length_nil] using
      oneStep (result_nil program readResult state contents result)
  | cons head tail ih =>
    have first := oneStep (result_cons program readResult state contents head tail result)
    have rest := ih (state.1, state.2.1, some head, state.2.2.2) (.inl head :: result)
    have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [List.reverse_cons, List.map_append, List.map_singleton, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- The framed caller copies one candidate and invokes the original checker.
The checker result and unchanged candidate return on physical stacks. -/
noncomputable def candidateRun (word : List (Input program)) (vector : List (Option (Input program)))
    (head : program.Γ program.k₁) (tail : List (program.Γ program.k₁)) (bound : Nat)
    (executed : TM2OutputsInTime program word (some (head :: tail)) bound) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (initial program readResult) (fun _ => [])
        (word.map some ++ none :: vector) [] [])
      (some (config program readResult (some .read) (initial program readResult)
        (RetainedWordExecution.wordContents (retained program readResult) (retained program readResult).k₁
          (.inr (readResult head) :: word.map Sum.inl)) vector [] []))
      (bound + 5 * word.length + tail.length + 7) := by
  have copied := scanRun program readResult (initial program readResult) word vector
  have restored := restoreRun program readResult
    ((initial program readResult).1, some none, (initial program readResult).2.2) (fun _ => []) word.reverse vector
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have retainedRun := RetainedWordExecution.outputs program readResult word head tail bound executed
  have walked := runExecution program readResult vector retainedRun
  rw [RetainedWordExecution.source_init, RetainedWordExecution.source_halt] at walked
  simp only [Option.elim_some, Option.elim_none] at walked
  have joined := EvalsToInTime.trans _ _ _ _ _ _ copied restored
  have finished := EvalsToInTime.trans _ _ _ _ _ _ joined walked
  convert finished using 1 <;> try rfl
  omega


noncomputable def rejectedRun (word : List (Input program)) (vector : List (Option (Input program)))
    (head : program.Γ program.k₁) (tail : List (program.Γ program.k₁)) (bound : Nat)
    (executed : TM2OutputsInTime program word (some (head :: tail)) bound)
    (rejected : readResult head = false) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (initial program readResult) (fun _ => [])
        (word.map some ++ none :: vector) [] [])
      (some (config program readResult (some .scan) (initial program readResult) (fun _ => []) vector [] []))
      (bound + 6 * word.length + tail.length + 9) := by
  have called := candidateRun program readResult word vector head tail bound executed
  rw [rejected] at called
  have read := oneStep (read_tag program readResult (initial program readResult)
    (RetainedWordExecution.wordContents (retained program readResult) (retained program readResult).k₁
      (.inr false :: word.map Sum.inl)) false (word.map Sum.inl) vector (by simp [RetainedWordExecution.wordContents]))
  have discarded := discardRun program readResult
    ((initial program readResult).1, (initial program readResult).2.1,
      (initial program readResult).2.2.1, some (.inr false))
    (RetainedWordExecution.wordContents (retained program readResult) (retained program readResult).k₁
      (word.map Sum.inl)) (word.map Sum.inl) vector (by simp [RetainedWordExecution.wordContents])
  simp only [Bool.false_eq_true, ↓reduceIte, RetainedWordExecution.wordContents,
    Function.update_idem, Function.update_eq_self, List.length_map] at read discarded
  have joined := EvalsToInTime.trans _ _ _ _ _ _ called read
  have finished := EvalsToInTime.trans _ _ _ _ _ _ joined discarded
  convert finished using 1
  omega

noncomputable def acceptedRun (word : List (Input program)) (vector : List (Option (Input program)))
    (head : program.Γ program.k₁) (tail : List (program.Γ program.k₁)) (bound : Nat)
    (executed : TM2OutputsInTime program word (some (head :: tail)) bound)
    (accepted : readResult head = true) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (initial program readResult) (fun _ => [])
        (word.map some ++ none :: vector) [] [])
      (some (config program readResult none (initial program readResult) (fun _ => []) [] []
        (.inr true :: word.map Sum.inl)))
      (bound + 7 * word.length + tail.length + vector.length + 11) := by
  have called := candidateRun program readResult word vector head tail bound executed
  rw [accepted] at called
  have read := oneStep (read_tag program readResult (initial program readResult)
    (RetainedWordExecution.wordContents (retained program readResult) (retained program readResult).k₁
      (.inr true :: word.map Sum.inl)) true (word.map Sum.inl) vector (by simp [RetainedWordExecution.wordContents]))
  have captured := captureRun program readResult
    ((initial program readResult).1, (initial program readResult).2.1,
      (initial program readResult).2.2.1, some (.inr true))
    (RetainedWordExecution.wordContents (retained program readResult) (retained program readResult).k₁
      (word.map Sum.inl)) word [] vector (by simp [RetainedWordExecution.wordContents])
  simp only [↓reduceIte, RetainedWordExecution.wordContents, Function.update_idem,
    Function.update_eq_self, List.append_nil] at read captured
  have drained := drainRun program readResult (initial program readResult) (fun _ => []) vector word.reverse
  have restored := resultRun program readResult (initial program readResult) (fun _ => []) word.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have a := EvalsToInTime.trans _ _ _ _ _ _ called read
  have b := EvalsToInTime.trans _ _ _ _ _ _ a captured
  have c := EvalsToInTime.trans _ _ _ _ _ _ b drained
  have d := EvalsToInTime.trans _ _ _ _ _ _ c restored
  convert d using 1
  omega

theorem init_eq (vector : List (Option (Input program))) :
    initList (machine program readResult) vector =
      config program readResult (some .scan) (initial program readResult) (fun _ => []) vector [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [vectorKey]
  | some key => cases key with
    | none => simp [vectorKey]
    | some key => cases key <;> simp [vectorKey]

theorem halt_eq (result : List (Input program ⊕ Bool)) :
    haltList (machine program readResult) result =
      config program readResult none (initial program readResult) (fun _ => []) [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key <;> simp [resultKey]


/-- Use the existing indexed-template field framing. -/
def frame (words : List (List (Input program))) : List (Option (Input program)) :=
  WordTemplateMachine.Indexed.frame words

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem frame_cons (word : List (Input program)) (words : List (List (Input program))) :
    frame program (word :: words) = word.map some ++ none :: frame program words := by
  simp [frame, WordTemplateMachine.Indexed.frame, List.append_assoc]

/-- Evidence for precisely the checker calls that were made. An accepted
prefix places no termination or correctness premise on later candidates. -/
inductive CheckedPrefix : List (List (Input program)) → Option (List (Input program)) → Nat → Type where
  | exhausted : CheckedPrefix [] none 1
  | accepted (word : List (Input program)) (rest : List (List (Input program)))
      (head : program.Γ program.k₁) (tail : List (program.Γ program.k₁)) (bound : Nat)
      (executed : TM2OutputsInTime program word (some (head :: tail)) bound)
      (accepted : readResult head = true) :
      CheckedPrefix (word :: rest) (some word)
        (bound + 7 * word.length + tail.length + (frame program rest).length + 11)
  | rejected (word : List (Input program)) (rest : List (List (Input program)))
      (head : program.Γ program.k₁) (tail : List (program.Γ program.k₁)) (bound : Nat)
      (executed : TM2OutputsInTime program word (some (head :: tail)) bound)
      (rejected : readResult head = false)
      {result : Option (List (Input program))} {remaining : Nat}
      (next : CheckedPrefix rest result remaining) :
      CheckedPrefix (word :: rest) result (bound + 6 * word.length + tail.length + 9 + remaining)

noncomputable def prefixRun {words : List (List (Input program))}
    {result : Option (List (Input program))} {bound : Nat}
    (trace : CheckedPrefix program readResult words result bound) :
    EvalsToInTime (machine program readResult).step
      (config program readResult (some .scan) (initial program readResult) (fun _ => []) (frame program words) [] [])
      (some (config program readResult none (initial program readResult) (fun _ => []) [] []
        (FirstCertificateExecution.Selection.result result))) bound := by
  induction trace with
  | exhausted => exact oneStep (scan_nil program readResult)
  | accepted word rest head tail bound executed accepted =>
      simpa only [frame_cons, FirstCertificateExecution.Selection.result] using
        acceptedRun program readResult word (frame program rest) head tail bound executed accepted
  | rejected word rest head tail bound executed rejected next ih =>
      have first := rejectedRun program readResult word (frame program rest) head tail bound executed rejected
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first ih
      simpa only [frame_cons, Nat.add_comm] using joined

/-- An actual one-clock finite machine, with no checker calls after success.
Every unexamined input byte is still drained and charged. -/
noncomputable def outputs {words : List (List (Input program))}
    {result : Option (List (Input program))} {bound : Nat}
    (trace : CheckedPrefix program readResult words result bound) :
    TM2OutputsInTime (machine program readResult) (frame program words)
      (some (FirstCertificateExecution.Selection.result result)) bound := by
  change EvalsToInTime _ (initList (machine program readResult) _)
    (some (haltList (machine program readResult) _)) _
  rw [init_eq, halt_eq]
  exact prefixRun program readResult trace

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- The charged clock only includes checker calls through the first success;
the unread suffix contributes its physical byte count. -/
def searchClock (accepts : List (Input program) → Bool) (clock : List (Input program) → Nat) :
    List (List (Input program)) → Nat
  | [] => 1
  | word :: rest => if accepts word then
      clock word + 7 * word.length + (frame program rest).length + 11
    else clock word + 6 * word.length + 9 + searchClock accepts clock rest

/-- A total singleton-response checker supplies a prefix trace constructively.
Its later run witnesses do not occur in the trace after the first success. -/
noncomputable def checkedPrefix (response : List (Input program) → program.Γ program.k₁)
    (clock : List (Input program) → Nat)
    (runs : ∀ word, TM2OutputsInTime program word (some [response word]) (clock word))
    (words : List (List (Input program))) :
    CheckedPrefix program readResult words (words.find? (readResult ∘ response))
      (searchClock program (readResult ∘ response) clock words) := by
  induction words with
  | nil => exact .exhausted
  | cons word rest ih =>
    cases accepted : readResult (response word) with
    | false =>
      simpa only [List.find?_cons, Function.comp_apply, accepted, Bool.false_eq_true,
        ↓reduceIte, searchClock, List.length_nil, Nat.add_zero] using
        CheckedPrefix.rejected word rest (response word) [] (clock word) (runs word) accepted ih
    | true =>
      simpa only [List.find?_cons, Function.comp_apply, accepted, ↓reduceIte, searchClock,
        List.length_nil, Nat.add_zero] using
        CheckedPrefix.accepted word rest (response word) [] (clock word) (runs word) accepted

noncomputable def searchOutputs (response : List (Input program) → program.Γ program.k₁)
    (clock : List (Input program) → Nat)
    (runs : ∀ word, TM2OutputsInTime program word (some [response word]) (clock word))
    (words : List (List (Input program))) :
    TM2OutputsInTime (machine program readResult) (frame program words)
      (some (FirstCertificateExecution.Selection.result (words.find? (readResult ∘ response))))
      (searchClock program (readResult ∘ response) clock words) :=
  outputs program readResult (checkedPrefix program readResult response clock runs words)


omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- A returned candidate is an original member, with an actual successful
checker run. Merely enumerating or copying a word cannot certify it. -/
theorem CheckedPrefix.found {words : List (List (Input program))}
    {word : List (Input program)} {bound : Nat}
    (trace : CheckedPrefix program readResult words (some word) bound) :
    word ∈ words ∧ ∃ head tail time,
      Nonempty (TM2OutputsInTime program word (some (head :: tail)) time) ∧ readResult head = true := by
  generalize found : some word = result at trace
  induction trace with
  | exhausted => cases found
  | accepted candidate rest head tail time executed accepted =>
      cases found
      exact ⟨by simp, head, tail, time, ⟨executed⟩, accepted⟩
  | rejected candidate rest head tail time executed rejected next ih =>
      obtain ⟨member, success⟩ := ih found
      exact ⟨List.mem_cons_of_mem candidate member, success⟩

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- An eager upper account pays for every checker call and enough physical
work to cover either branch of the caller. -/
def allCallWork (clock : List (Input program) → Nat) : List (List (Input program)) → Nat
  | [] => 0
  | word :: rest => clock word + 7 * word.length + 12 + allCallWork clock rest

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem frame_length_le_allCallWork (clock : List (Input program) → Nat)
    (words : List (List (Input program))) : (frame program words).length ≤ allCallWork program clock words := by
  induction words with
  | nil => simp [frame, WordTemplateMachine.Indexed.frame, allCallWork]
  | cons word rest ih =>
      rw [frame_cons, List.length_append, List.length_map, List.length_cons, allCallWork]
      omega

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- The early-stop clock is bounded by the charged eager account. This is not
a polynomial-in-depth bound: the supplied candidate vector can be exponential. -/
theorem searchClock_le_allCallWork (accepts : List (Input program) → Bool)
    (clock : List (Input program) → Nat) (words : List (List (Input program))) :
    searchClock program accepts clock words ≤ allCallWork program clock words + 1 := by
  induction words with
  | nil => simp [searchClock, allCallWork]
  | cons word rest ih =>
      rw [searchClock, allCallWork]
      have physical := frame_length_le_allCallWork program clock rest
      split <;> omega

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- Every failed candidate before the first success pays its original checker
clock and six physical passes over its word, plus finite control. -/
theorem searchClock_rejected_append (accepts : List (Input program) → Bool)
    (clock : List (Input program) → Nat) (before after : List (List (Input program)))
    (rejected : ∀ word ∈ before, accepts word = false) :
    searchClock program accepts clock (before ++ after) =
      (before.map (fun word => clock word + 6 * word.length + 9)).sum + searchClock program accepts clock after := by
  induction before with
  | nil => simp
  | cons word rest ih =>
      have head := rejected word (by simp)
      have tail := ih (fun candidate member => rejected candidate (by simp [member]))
      simp only [List.cons_append, searchClock, head, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, tail, Nat.add_assoc]

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
/-- The first-success formula separates all performed checker work from the
unexamined suffix's byte count. No later checker clock is charged. -/
theorem searchClock_first_success (accepts : List (Input program) → Bool)
    (clock : List (Input program) → Nat) (before after : List (List (Input program)))
    (word : List (Input program)) (rejected : ∀ candidate ∈ before, accepts candidate = false)
    (accepted : accepts word = true) :
    searchClock program accepts clock (before ++ word :: after) =
      (before.map (fun candidate => clock candidate + 6 * candidate.length + 9)).sum +
        (clock word + 7 * word.length + (frame program after).length + 11) := by
  rw [searchClock_rejected_append program accepts clock before (word :: after) rejected, searchClock]
  simp only [accepted, ↓reduceIte]


/-- The caller adds only finite alphabets when all source stacks have finite
alphabets; physical word storage is not smuggled into a control alphabet. -/
theorem finiteAlphabet (originalFinite : ∀ key, Finite (program.Γ key)) :
    ∀ key, Finite ((machine program readResult).Γ key) := by
  intro key
  cases key with
  | none => exact inferInstanceAs (Finite (Option (Input program)))
  | some key => cases key with
    | none => exact inferInstanceAs (Finite (Input program))
    | some key => cases key with
      | none => exact inferInstanceAs (Finite (Input program ⊕ Bool))
      | some key => cases key with
        | none => exact inferInstanceAs (Finite (Input program ⊕ Bool))
        | some key => cases key with
          | none => exact inferInstanceAs (Finite (Input program))
          | some key => cases key with
            | none => exact inferInstanceAs (Finite (Input program))
            | some key => exact originalFinite key

end Mettapedia.Logic.ProofSearch.ShortCircuitCertificateExecution


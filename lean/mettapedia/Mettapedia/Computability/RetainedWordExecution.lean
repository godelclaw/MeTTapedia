import Mettapedia.Computability.StackMachineRegisters
import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.Computability.WordTemplateMachine

/-!
# Retaining an original word across a finite subroutine

The caller copies the original input into physical storage, executes an
unchanged subroutine on another physical copy, retains its finite result tag,
and returns that tag followed by the original word. Dynamic words never enter
control registers. Duplication, restoration and cleanup transitions are counted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.RetainedWordExecution
open Turing StateTransition
open Turing.TM2.Stmt

variable (program : FinTM2) {Tag : Type} [Fintype Tag] [Inhabited Tag]
local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin
variable [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)]

abbrev Input := program.Γ program.k₀
abbrev Output := program.Γ program.k₁
abbrev Key := Option (Option (Option program.K))
abbrev Extra := Option (Input program) × Option (Output program) × Tag
abbrev State := program.σ × Extra program (Tag := Tag)
abbrev Alphabet := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet program.Γ (Input program)) (Input program))
  (Sum (Input program) Tag)
abbrev resultKey : Key program := none
abbrev temporaryKey : Key program := some none
abbrev savedKey : Key program := some (some none)
abbrev sourceKey (key : program.K) : Key program := some (some (some key))

inductive Phase (Label : Type) where
  | scan | restore | run (label : Label) | read | discard | finish
  deriving DecidableEq, Fintype

/-- The original body is embedded with three caller stacks and finite registers.
Its halt returns to the caller's tag reader in the same physical transition. -/
def body (label : program.Λ) : TM2.Stmt (Alphabet program (Tag := Tag))
    (Phase program.Λ) (State program (Tag := Tag)) :=
  StackMachineRegisters.withStack (Cell := Sum (Input program) Tag) id
    (StackMachineRegisters.withStack (Cell := Input program) id
      (StackMachineRegisters.withStack (Cell := Input program) id
        (StackMachineRegisters.returning (Extra := Extra program (Tag := Tag))
          Phase.run (fun _ => Phase.read) (program.m label))))

/-- The concrete transition body is shared by the finite machine and direct
execution controls without evaluating finite-control enumeration witnesses. -/
def statement (readTag : Output program → Tag) (phase : Phase program.Λ) :
    TM2.Stmt (Alphabet program (Tag := Tag)) (Phase program.Λ) (State program (Tag := Tag)) :=
  match phase with
    | .scan => pop (sourceKey program program.k₀) (fun state value => (state.1, value, state.2.2))
        (branch (fun state => state.2.1.isSome)
          (push (temporaryKey program) (fun state => state.2.1.getD default)
            (push (savedKey program) (fun state => state.2.1.getD default) (goto fun _ => .scan)))
          (goto fun _ => .restore))
    | .restore => pop (temporaryKey program) (fun state value => (state.1, value, state.2.2))
        (branch (fun state => state.2.1.isSome)
          (push (sourceKey program program.k₀) (fun state => state.2.1.getD default) (goto fun _ => .restore))
          (load (fun state => (program.initialState, none, none, state.2.2.2)) (goto fun _ => .run program.main)))
    | .run label => body program label
    | .read => pop (sourceKey program program.k₁) (fun state value => (state.1, state.2.1, value, state.2.2.2))
        (load (fun state => (state.1, state.2.1, state.2.2.1,
          state.2.2.1.elim default readTag)) (goto fun _ => .discard))
    | .discard => pop (sourceKey program program.k₁) (fun state value => (state.1, state.2.1, value, state.2.2.2))
        (branch (fun state => state.2.2.1.isSome) (goto fun _ => .discard) (goto fun _ => .finish))
    | .finish => pop (savedKey program) (fun state value => (state.1, value, state.2.2))
        (branch (fun state => state.2.1.isSome)
          (push (resultKey program) (fun state => .inl (state.2.1.getD default)) (goto fun _ => .finish))
          (push (resultKey program) (fun state => .inr state.2.2.2)
            (load (fun _ => (program.initialState, none, none, default)) halt)))


def machine (readTag : Output program → Tag) : FinTM2 where
  K := Key program
  k₀ := sourceKey program program.k₀
  k₁ := resultKey program
  Γ := Alphabet program (Tag := Tag)
  Γk₀Fin := program.Γk₀Fin
  Λ := Phase program.Λ
  main := .scan
  σ := State program (Tag := Tag)
  initialState := (program.initialState, none, none, default)
  m := statement program readTag

attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt

theorem machine_body (readTag : Output program → Tag) (phase : Phase program.Λ) :
    (machine program readTag).m phase = statement program readTag phase := rfl

/-- All original stacks are present even during caller phases. -/
def config (readTag : Output program → Tag) (phase : Option (Phase program.Λ))
    (state : State program (Tag := Tag)) (contents : ∀ key, List (program.Γ key))
    (temporary saved : List (Input program)) (result : List (Sum (Input program) Tag)) :
    (machine program readTag).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => result
    | some none => temporary
    | some (some none) => saved
    | some (some (some key)) => contents key

def initialContents (word : List (Input program)) : ∀ key, List (program.Γ key) :=
  (initList program word).stk

local macro "retained_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, resultKey, temporaryKey, savedKey, sourceKey,
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

theorem scan_cons (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (head : Input program) (tail temporary saved : List (Input program))
    (result : List (Sum (Input program) Tag)) (input : contents program.k₀ = head :: tail) :
    (machine program readTag).step (config program readTag (some .scan) state contents temporary saved result) =
      some (config program readTag (some .scan) (state.1, some head, state.2.2)
        (Function.update contents program.k₀ tail) (head :: temporary) (head :: saved) result) := by
  retained_step

theorem scan_nil (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (temporary saved : List (Input program))
    (result : List (Sum (Input program) Tag)) (input : contents program.k₀ = []) :
    (machine program readTag).step (config program readTag (some .scan) state contents temporary saved result) =
      some (config program readTag (some .restore) (state.1, none, state.2.2)
        (Function.update contents program.k₀ []) temporary saved result) := by
  retained_step

theorem restore_cons (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (head : Input program) (temporary saved : List (Input program))
    (result : List (Sum (Input program) Tag)) :
    (machine program readTag).step (config program readTag (some .restore) state contents (head :: temporary) saved result) =
      some (config program readTag (some .restore) (state.1, some head, state.2.2)
        (Function.update contents program.k₀ (head :: contents program.k₀)) temporary saved result) := by retained_step

theorem restore_nil (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (saved : List (Input program))
    (result : List (Sum (Input program) Tag)) :
    (machine program readTag).step (config program readTag (some .restore) state contents [] saved result) =
      some (config program readTag (some (.run program.main))
        (program.initialState, none, none, state.2.2.2) contents [] saved result) := by retained_step

/-- The original positive transition is reused one for one. -/
theorem run_step (readTag : Output program → Tag) (saved : List (Input program))
    (before after : program.Cfg) (computed : program.step before = some after) :
    (machine program readTag).step
      (config program readTag (some (before.l.elim .read .run))
        (before.var, none, none, default) before.stk [] saved []) =
      some (config program readTag (some (after.l.elim .read .run))
        (after.var, none, none, default) after.stk [] saved []) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, config, TM2.step, Option.elim_some]
      have cells : (config program readTag (some (.run label))
          (state, none, none, default) contents [] saved []).stk =
          StackMachineRegisters.withStackContents (Cell := Sum (Input program) Tag)
            (StackMachineRegisters.withStackContents (Cell := Input program)
              (StackMachineRegisters.withStackContents (Cell := Input program) contents saved) []) [] := by
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl
      trans some (TM2.stepAux (body program (Tag := Tag) label) (state, none, none, (default : Tag))
        (StackMachineRegisters.withStackContents (Cell := Sum (Input program) Tag)
          (StackMachineRegisters.withStackContents (Cell := Input program)
            (StackMachineRegisters.withStackContents (Cell := Input program) contents saved) []) []))
      · exact congrArg (fun cellWords => some (TM2.stepAux (body program (Tag := Tag) label)
          (state, none, none, (default : Tag)) cellWords)) cells
      · unfold body
        rw [StackMachineRegisters.stepAux_withStack]
        rw [StackMachineRegisters.stepAux_withStack]
        rw [StackMachineRegisters.stepAux_withStack]
        rw [StackMachineRegisters.stepAux_returning]
        simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.returningConfig,
          Option.map_some, id_eq]
        congr 2
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key <;> rfl



/-- A single physical word occupies one original stack. -/
def wordContents (key : program.K) (word : List (program.Γ key)) : ∀ index, List (program.Γ index) :=
  Function.update (fun _ => []) key word

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem initialContents_eq (word : List (Input program)) :
    initialContents program word = wordContents program program.k₀ word := by
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [initialContents, initList, wordContents]
  · simp [initialContents, initList, wordContents, Function.update, same]

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem haltedContents_eq (word : List (Output program)) :
    (haltList program word).stk = wordContents program program.k₁ word := by
  funext key
  by_cases same : key = program.k₁
  · subst key; simp [haltList, wordContents]
  · simp [haltList, wordContents, Function.update, same]

theorem read_cons (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (head : Output program) (tail : List (Output program))
    (saved : List (Input program)) (result : List (Sum (Input program) Tag))
    (input : contents program.k₁ = head :: tail) :
    (machine program readTag).step (config program readTag (some .read) state contents [] saved result) =
      some (config program readTag (some .discard) (state.1, state.2.1, some head, readTag head)
        (Function.update contents program.k₁ tail) [] saved result) := by
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

theorem discard_cons (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (head : Output program) (tail : List (Output program))
    (saved : List (Input program)) (result : List (Sum (Input program) Tag))
    (input : contents program.k₁ = head :: tail) :
    (machine program readTag).step (config program readTag (some .discard) state contents [] saved result) =
      some (config program readTag (some .discard) (state.1, state.2.1, some head, state.2.2.2)
        (Function.update contents program.k₁ tail) [] saved result) := by
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

theorem discard_nil (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key))
    (saved : List (Input program)) (result : List (Sum (Input program) Tag))
    (input : contents program.k₁ = []) :
    (machine program readTag).step (config program readTag (some .discard) state contents [] saved result) =
      some (config program readTag (some .finish) (state.1, state.2.1, none, state.2.2.2)
        (Function.update contents program.k₁ []) [] saved result) := by
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

theorem finish_cons (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (head : Input program) (saved : List (Input program))
    (result : List (Sum (Input program) Tag)) :
    (machine program readTag).step (config program readTag (some .finish) state contents [] (head :: saved) result) =
      some (config program readTag (some .finish) (state.1, some head, state.2.2)
        contents [] saved (.inl head :: result)) := by retained_step

theorem finish_nil (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (result : List (Sum (Input program) Tag)) :
    (machine program readTag).step (config program readTag (some .finish) state contents [] [] result) =
      some (config program readTag none (program.initialState, none, none, default)
        contents [] [] (.inr state.2.2.2 :: result)) := by retained_step

noncomputable def scanRun (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (input temporary saved : List (Input program))
    (result : List (Sum (Input program) Tag)) (present : contents program.k₀ = input) :
    EvalsToInTime (machine program readTag).step
      (config program readTag (some .scan) state contents temporary saved result)
      (some (config program readTag (some .restore) (state.1, none, state.2.2)
        (Function.update contents program.k₀ []) (input.reverse ++ temporary) (input.reverse ++ saved) result))
      (input.length + 1) := by
  induction input generalizing contents state temporary saved with
  | nil =>
    simpa only [List.reverse_nil, List.nil_append, List.length_nil] using
      StackMachineComposition.oneStep (scan_nil program readTag state contents temporary saved result present)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (scan_cons program readTag state contents head tail temporary saved result present)
    have rest := ih (state.1, some head, state.2.2) (Function.update contents program.k₀ tail)
      (head :: temporary) (head :: saved) (by simp)
    have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
    simpa only [Function.update_idem, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def restoreRun (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (temporary saved : List (Input program))
    (result : List (Sum (Input program) Tag)) :
    EvalsToInTime (machine program readTag).step
      (config program readTag (some .restore) state contents temporary saved result)
      (some (config program readTag (some (.run program.main))
        (program.initialState, none, none, state.2.2.2)
        (Function.update contents program.k₀ (temporary.reverse ++ contents program.k₀)) [] saved result))
      (temporary.length + 1) := by
  induction temporary generalizing contents state with
  | nil =>
    have first := StackMachineComposition.oneStep (restore_nil program readTag state contents saved result)
    simpa only [List.reverse_nil, List.nil_append, Function.update_eq_self, List.length_nil] using first
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (restore_cons program readTag state contents head tail saved result)
    have rest := ih (state.1, some head, state.2.2)
      (Function.update contents program.k₀ (head :: contents program.k₀))
    have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
    simpa only [Function.update_idem, Function.update_self, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def discardRun (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (input : List (Output program))
    (saved : List (Input program)) (result : List (Sum (Input program) Tag))
    (present : contents program.k₁ = input) :
    EvalsToInTime (machine program readTag).step
      (config program readTag (some .discard) state contents [] saved result)
      (some (config program readTag (some .finish) (state.1, state.2.1, none, state.2.2.2)
        (Function.update contents program.k₁ []) [] saved result)) (input.length + 1) := by
  induction input generalizing contents state with
  | nil =>
      exact StackMachineComposition.oneStep
        (discard_nil program readTag state contents saved result present)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep
      (discard_cons program readTag state contents head tail saved result present)
    have rest := ih (state.1, state.2.1, some head, state.2.2.2)
      (Function.update contents program.k₁ tail) (by simp)
    have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
    simpa only [Function.update_idem, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def finishRun (readTag : Output program → Tag) (state : State program (Tag := Tag))
    (contents : ∀ key, List (program.Γ key)) (saved : List (Input program))
    (result : List (Sum (Input program) Tag)) :
    EvalsToInTime (machine program readTag).step
      (config program readTag (some .finish) state contents [] saved result)
      (some (config program readTag none (program.initialState, none, none, default)
        contents [] [] (.inr state.2.2.2 :: saved.reverse.map Sum.inl ++ result))) (saved.length + 1) := by
  induction saved generalizing state result with
  | nil => simpa only [List.reverse_nil, List.map_nil, List.nil_append, List.cons_append, List.length_nil] using
      StackMachineComposition.oneStep (finish_nil program readTag state contents result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (finish_cons program readTag state contents head tail result)
    have rest := ih (state.1, some head, state.2.2) (.inl head :: result)
    have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined


omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem source_init (word : List (Input program)) : initList program word =
    (⟨some program.main, program.initialState, wordContents program program.k₀ word⟩ : program.Cfg) := by
  exact congrArg (fun contents =>
    (⟨some program.main, program.initialState, contents⟩ : program.Cfg)) (initialContents_eq program word)

omit [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] in
theorem source_halt (word : List (Output program)) : haltList program word =
    (⟨none, program.initialState, wordContents program program.k₁ word⟩ : program.Cfg) := by
  exact congrArg (fun contents =>
    (⟨none, program.initialState, contents⟩ : program.Cfg)) (haltedContents_eq program word)

noncomputable def runExecution (readTag : Output program → Tag) (saved : List (Input program))
    {before after : program.Cfg} {bound : Nat}
    (execution : EvalsToInTime program.step before (some after) bound) :
    EvalsToInTime (machine program readTag).step
      (config program readTag (some (before.l.elim .read .run))
        (before.var, none, none, default) before.stk [] saved [])
      (some (config program readTag (some (after.l.elim .read .run))
        (after.var, none, none, default) after.stk [] saved [])) bound :=
  StackMachineComposition.lift_execution program.step (machine program readTag).step
    (fun source => config program readTag (some (source.l.elim .read .run))
      (source.var, none, none, default) source.stk [] saved [])
    (run_step program readTag saved) execution

theorem init_eq (readTag : Output program → Tag) (input : List (Input program)) :
    initList (machine program readTag) input =
      config program readTag (some .scan) (program.initialState, none, none, default)
        (wordContents program program.k₀ input) [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [sourceKey]
  | some key => cases key with
    | none => simp [sourceKey]
    | some key => cases key with
      | none => simp [sourceKey]
      | some key =>
        by_cases same : key = program.k₀
        · subst key; simp [sourceKey, wordContents]
        · simp [sourceKey, wordContents, Function.update, same]

theorem halt_eq (readTag : Output program → Tag) (result : List (Sum (Input program) Tag)) :
    haltList (machine program readTag) result =
      config program readTag none (program.initialState, none, none, default)
        (fun _ => []) [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key <;> simp [resultKey]

/-- The source subroutine supplies its actual complete run. The caller charges
all physical copies and all discarded output symbols; the returned word is
exactly the original input, not a decoded and reconstructed substitute. -/
noncomputable def outputs (readTag : Output program → Tag) (input : List (Input program))
    (head : Output program) (tail : List (Output program)) (bound : Nat)
    (execution : TM2OutputsInTime program input (some (head :: tail)) bound) :
    TM2OutputsInTime (machine program readTag) input
      (some (.inr (readTag head) :: input.map Sum.inl))
      (bound + 3 * input.length + tail.length + 5) := by
  have copied := scanRun program readTag (program.initialState, none, none, (default : Tag))
    (wordContents program program.k₀ input) input [] [] [] (by simp [wordContents])
  have restored := restoreRun program readTag (program.initialState, none, none, (default : Tag))
    (fun _ => []) input.reverse input.reverse []
  simp only [wordContents, Function.update_idem, Function.update_eq_self,
    List.append_nil, List.reverse_reverse] at copied restored
  have walked := runExecution program readTag input.reverse execution
  rw [source_init, source_halt] at walked
  simp only [Option.elim_some, Option.elim_none] at walked
  have read := StackMachineComposition.oneStep
    (read_cons program readTag (program.initialState, none, none, (default : Tag))
      (wordContents program program.k₁ (head :: tail)) head tail input.reverse [] (by simp [wordContents]))
  have discarded := discardRun program readTag (program.initialState, none, some head, readTag head)
    (Function.update (wordContents program program.k₁ (head :: tail)) program.k₁ tail)
    tail input.reverse [] (by simp)
  simp only [wordContents, Function.update_idem, Function.update_eq_self] at read discarded
  have finished := finishRun program readTag (program.initialState, none, none, readTag head)
    (fun _ => []) input.reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored finished
  have a := EvalsToInTime.trans _ (input.length + 1) (input.length + 1) _ _ _ copied restored
  have b := EvalsToInTime.trans _ (input.length + 1 + (input.length + 1)) bound _ _ _ a walked
  have c := EvalsToInTime.trans _ (bound + (input.length + 1 + (input.length + 1))) 1 _ _ _ b read
  have d := EvalsToInTime.trans _ (1 + (bound + (input.length + 1 + (input.length + 1))))
    (tail.length + 1) _ _ _ c discarded
  have e := EvalsToInTime.trans _ (tail.length + 1 + (1 + (bound + (input.length + 1 + (input.length + 1)))))
    (input.length + 1) _ _ _ d finished
  change EvalsToInTime _ (initList (machine program readTag) _) (some (haltList (machine program readTag) _)) _
  rw [init_eq, halt_eq]
  convert e using 1
  · rfl
  · omega


end Mettapedia.Computability.RetainedWordExecution


namespace Mettapedia.Computability.RetainedWordExecution.WithOutput
open Turing StateTransition
open Turing.TM2.Stmt

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
abbrev Extra := Option (Input program) × Option (Output program)
abbrev State := program.σ × Extra program
abbrev Alphabet := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet
      (StackMachineRegisters.withStackAlphabet program.Γ (Input program)) (Input program))
    (Output program)) (Sum (Input program) (Output program))
abbrev resultKey : Key program := none
abbrev outputTemporaryKey : Key program := some none
abbrev temporaryKey : Key program := some (some none)
abbrev savedKey : Key program := some (some (some none))
abbrev sourceKey (key : program.K) : Key program := some (some (some (some key)))

inductive Phase (Label : Type) where
  | scan | restore | run (label : Label) | scanOutput | restoreOutput | finish
  deriving DecidableEq, Fintype

namespace Programs

variable {K L S : Type} {Γ : K → Type}

abbrev Cells (inputKey outputKey : K) := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet
    (StackMachineRegisters.withStackAlphabet
      (StackMachineRegisters.withStackAlphabet Γ (Γ inputKey)) (Γ inputKey))
    (Γ outputKey)) (Sum (Γ inputKey) (Γ outputKey))
abbrev Registers (inputKey outputKey : K) := S × Option (Γ inputKey) × Option (Γ outputKey)

/-- The retained-word control uses only physical addresses and original
instructions. Finiteness witnesses do not enter the executable interface. -/
def body (inputKey outputKey : K) (source : L → TM2.Stmt Γ L S) (label : L) :
    TM2.Stmt (Cells (Γ := Γ) inputKey outputKey) (Phase L) (Registers (Γ := Γ) (S := S) inputKey outputKey) :=
  StackMachineRegisters.withStack (Cell := Sum (Γ inputKey) (Γ outputKey)) id
    (StackMachineRegisters.withStack (Cell := Γ outputKey) id
      (StackMachineRegisters.withStack (Cell := Γ inputKey) id
        (StackMachineRegisters.withStack (Cell := Γ inputKey) id
          (StackMachineRegisters.returning (Extra := Option (Γ inputKey) × Option (Γ outputKey))
            Phase.run (fun _ => Phase.scanOutput) (source label)))))

/-- Copy, return and cleanup phases preserve the two words separately and
execute the original subroutine without changing its transition count. -/
def statement (inputKey outputKey : K) (defaultInput : Γ inputKey) (defaultOutput : Γ outputKey)
    (initialState : S) (main : L) (source : L → TM2.Stmt Γ L S) (phase : Phase L) :
    TM2.Stmt (Cells (Γ := Γ) inputKey outputKey) (Phase L) (Registers (Γ := Γ) (S := S) inputKey outputKey) :=
  match phase with
  | .scan => pop (some (some (some (some inputKey)))) (fun state value => (state.1,value,state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (some (some none)) (fun state => state.2.1.getD defaultInput)
          (push (some (some (some none))) (fun state => state.2.1.getD defaultInput) (goto fun _ => .scan)))
        (goto fun _ => .restore))
  | .restore => pop (some (some none)) (fun state value => (state.1,value,state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (some (some (some (some inputKey)))) (fun state => state.2.1.getD defaultInput)
          (goto fun _ => .restore))
        (load (fun _ => (initialState,none,none)) (goto fun _ => .run main)))
  | .run label => body inputKey outputKey source label
  | .scanOutput => pop (some (some (some (some outputKey)))) (fun state value => (state.1,state.2.1,value))
      (branch (fun state => state.2.2.isSome)
        (push (some none) (fun state => state.2.2.getD defaultOutput)
          (goto fun _ => .scanOutput)) (goto fun _ => .restoreOutput))
  | .restoreOutput => pop (some none) (fun state value => (state.1,state.2.1,value))
      (branch (fun state => state.2.2.isSome)
        (push (none) (fun state => .inr (state.2.2.getD defaultOutput))
          (goto fun _ => .restoreOutput)) (goto fun _ => .finish))
  | .finish => pop (some (some (some none))) (fun state value => (state.1,value,state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (none) (fun state => .inl (state.2.1.getD defaultInput))
          (goto fun _ => .finish))
        (load (fun _ => (initialState,none,none)) halt))

end Programs

/-- The original subroutine returns to a physical full-output copier. -/
def body (label : program.Λ) : TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  Programs.body program.k₀ program.k₁ program.m label

/-- Both returned words stay on physical stacks; registers hold one symbol. -/
def statement (phase : Phase program.Λ) :
    TM2.Stmt (Alphabet program) (Phase program.Λ) (State program) :=
  Programs.statement program.k₀ program.k₁ default default program.initialState program.main program.m phase

def machine : FinTM2 where
  K := Key program
  k₀ := sourceKey program program.k₀
  k₁ := resultKey program
  Γ := Alphabet program
  Γk₀Fin := program.Γk₀Fin
  Λ := Phase program.Λ
  main := .scan
  σ := State program
  initialState := (program.initialState,none,none)
  m := statement program
attribute [local implicit_reducible] machine statement FinTM2.Cfg FinTM2.Stmt

theorem machine_body (phase : Phase program.Λ) :
    (machine program).m phase = statement program phase := rfl

def config (phase : Option (Phase program.Λ)) (state : State program)
    (contents : ∀ key, List (program.Γ key)) (temporary saved : List (Input program))
    (outputTemporary : List (Output program)) (result : List (Sum (Input program) (Output program))) :
    (machine program).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => result
    | some none => outputTemporary
    | some (some none) => temporary
    | some (some (some none)) => saved
    | some (some (some (some key))) => contents key

local macro "retained_output_step" : tactic => `(tactic| (
  simp_all [FinTM2.step,machine,statement,Programs.statement,config,resultKey,outputTemporaryKey,
    temporaryKey,savedKey,sourceKey,TM2.step,TM2.stepAux,Function.update]
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
              first
                | (by_cases same : key = program.k₀
                   · subst key; simp [Function.update]
                   · simp [Function.update,same])
                | (by_cases same : key = program.k₁
                   · subst key; simp [Function.update]
                   · simp [Function.update,same]))))

theorem scan_cons (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Input program) (tail temporary saved : List (Input program))
    (outputTemporary : List (Output program)) (result : List (Sum (Input program) (Output program)))
    (present : contents program.k₀ = head :: tail) :
    (machine program).step (config program (some .scan) state contents temporary saved outputTemporary result) =
      some (config program (some .scan) (state.1,some head,state.2.2)
        (Function.update contents program.k₀ tail) (head :: temporary) (head :: saved) outputTemporary result) := by
  retained_output_step

theorem scan_nil (state : State program) (contents : ∀ key, List (program.Γ key))
    (temporary saved : List (Input program)) (outputTemporary : List (Output program))
    (result : List (Sum (Input program) (Output program))) (present : contents program.k₀ = []) :
    (machine program).step (config program (some .scan) state contents temporary saved outputTemporary result) =
      some (config program (some .restore) (state.1,none,state.2.2)
        (Function.update contents program.k₀ []) temporary saved outputTemporary result) := by
  retained_output_step

theorem restore_cons (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Input program) (temporary saved : List (Input program))
    (outputTemporary : List (Output program)) (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .restore) state contents (head::temporary) saved outputTemporary result) =
      some (config program (some .restore) (state.1,some head,state.2.2)
        (Function.update contents program.k₀ (head::contents program.k₀)) temporary saved outputTemporary result) := by
  retained_output_step

theorem restore_nil (state : State program) (contents : ∀ key, List (program.Γ key))
    (saved : List (Input program)) (outputTemporary : List (Output program))
    (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .restore) state contents [] saved outputTemporary result) =
      some (config program (some (.run program.main)) (program.initialState,none,none)
        contents [] saved outputTemporary result) := by retained_output_step

theorem scanOutput_cons (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Output program) (tail outputTemporary : List (Output program))
    (temporary saved : List (Input program)) (result : List (Sum (Input program) (Output program)))
    (present : contents program.k₁ = head::tail) :
    (machine program).step (config program (some .scanOutput) state contents temporary saved outputTemporary result) =
      some (config program (some .scanOutput) (state.1,state.2.1,some head)
        (Function.update contents program.k₁ tail) temporary saved (head::outputTemporary) result) := by
  retained_output_step

theorem scanOutput_nil (state : State program) (contents : ∀ key, List (program.Γ key))
    (temporary saved : List (Input program)) (outputTemporary : List (Output program))
    (result : List (Sum (Input program) (Output program))) (present : contents program.k₁ = []) :
    (machine program).step (config program (some .scanOutput) state contents temporary saved outputTemporary result) =
      some (config program (some .restoreOutput) (state.1,state.2.1,none)
        (Function.update contents program.k₁ []) temporary saved outputTemporary result) := by
  retained_output_step

theorem restoreOutput_cons (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Output program) (tail : List (Output program)) (temporary saved : List (Input program))
    (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .restoreOutput) state contents temporary saved (head::tail) result) =
      some (config program (some .restoreOutput) (state.1,state.2.1,some head)
        contents temporary saved tail (.inr head :: result)) := by retained_output_step

theorem restoreOutput_nil (state : State program) (contents : ∀ key, List (program.Γ key))
    (temporary saved : List (Input program)) (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .restoreOutput) state contents temporary saved [] result) =
      some (config program (some .finish) (state.1,state.2.1,none) contents temporary saved [] result) := by
  retained_output_step

theorem finish_cons (state : State program) (contents : ∀ key, List (program.Γ key))
    (head : Input program) (saved : List (Input program)) (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .finish) state contents [] (head::saved) [] result) =
      some (config program (some .finish) (state.1,some head,state.2.2)
        contents [] saved [] (.inl head :: result)) := by retained_output_step

theorem finish_nil (state : State program) (contents : ∀ key, List (program.Γ key))
    (result : List (Sum (Input program) (Output program))) :
    (machine program).step (config program (some .finish) state contents [] [] [] result) =
      some (config program none (program.initialState,none,none) contents [] [] [] result) := by
  retained_output_step

/-- Every original positive transition is reused without semantic callbacks. -/
theorem run_step (saved : List (Input program))
    (before after : program.Cfg) (computed : program.step before = some after) :
    (machine program).step
      (config program (some (before.l.elim .scanOutput .run))
        (before.var,none,none) before.stk [] saved [] []) =
      some (config program (some (after.l.elim .scanOutput .run))
        (after.var,none,none) after.stk [] saved [] []) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step,TM2.step] at computed
      cases computed
      simp only [FinTM2.step,machine,statement,Programs.statement,config,TM2.step,Option.elim_some]
      have cells : (config program (some (.run label)) (state,none,none) contents [] saved [] []).stk =
          StackMachineRegisters.withStackContents (Cell:=Sum (Input program) (Output program))
            (StackMachineRegisters.withStackContents (Cell:=Output program)
              (StackMachineRegisters.withStackContents (Cell:=Input program)
                (StackMachineRegisters.withStackContents (Cell:=Input program) contents saved) []) []) [] := by
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key <;> rfl
      trans some (TM2.stepAux (body program label) (state,none,none)
        (StackMachineRegisters.withStackContents (Cell:=Sum (Input program) (Output program))
          (StackMachineRegisters.withStackContents (Cell:=Output program)
            (StackMachineRegisters.withStackContents (Cell:=Input program)
              (StackMachineRegisters.withStackContents (Cell:=Input program) contents saved) []) []) []))
      · exact congrArg (fun words => some (TM2.stepAux (body program label) (state,none,none) words)) cells
      · unfold body Programs.body
        rw [StackMachineRegisters.stepAux_withStack,StackMachineRegisters.stepAux_withStack,
          StackMachineRegisters.stepAux_withStack,StackMachineRegisters.stepAux_withStack,
          StackMachineRegisters.stepAux_returning]
        simp only [StackMachineRegisters.withStackConfig,StackMachineRegisters.returningConfig,
          Option.map_some,id_eq]
        congr 2
        funext key
        cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key => cases key with
            | none => rfl
            | some key => cases key <;> rfl


noncomputable def scanRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (input temporary saved : List (Input program)) (outputTemporary : List (Output program))
    (result : List (Sum (Input program) (Output program))) (present : contents program.k₀ = input) :
    EvalsToInTime (machine program).step
      (config program (some .scan) state contents temporary saved outputTemporary result)
      (some (config program (some .restore) (state.1,none,state.2.2)
        (Function.update contents program.k₀ []) (input.reverse++temporary) (input.reverse++saved)
        outputTemporary result)) (input.length+1) := by
  induction input generalizing contents state temporary saved with
  | nil => simpa only [List.reverse_nil,List.nil_append,List.length_nil] using
      StackMachineComposition.oneStep (scan_nil program state contents temporary saved outputTemporary result present)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep
        (scan_cons program state contents head tail temporary saved outputTemporary result present)
      have rest := ih (state.1,some head,state.2.2) (Function.update contents program.k₀ tail)
        (head::temporary) (head::saved) (by simp)
      have joined := EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ first rest
      simpa only [Function.update_idem,List.reverse_cons,List.append_assoc,List.singleton_append,
        List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

noncomputable def restoreRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (temporary saved : List (Input program)) (outputTemporary : List (Output program))
    (result : List (Sum (Input program) (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .restore) state contents temporary saved outputTemporary result)
      (some (config program (some (.run program.main)) (program.initialState,none,none)
        (Function.update contents program.k₀ (temporary.reverse++contents program.k₀))
        [] saved outputTemporary result)) (temporary.length+1) := by
  induction temporary generalizing contents state with
  | nil =>
      have first := StackMachineComposition.oneStep (restore_nil program state contents saved outputTemporary result)
      simpa only [List.reverse_nil,List.nil_append,Function.update_eq_self,List.length_nil] using first
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (restore_cons program state contents head tail saved outputTemporary result)
      have rest := ih (state.1,some head,state.2.2)
        (Function.update contents program.k₀ (head::contents program.k₀))
      have joined := EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ first rest
      simpa only [Function.update_idem,Function.update_self,List.reverse_cons,
        List.append_assoc,List.singleton_append,List.length_cons,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

noncomputable def scanOutputRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (output outputTemporary : List (Output program)) (temporary saved : List (Input program))
    (result : List (Sum (Input program) (Output program))) (present : contents program.k₁ = output) :
    EvalsToInTime (machine program).step
      (config program (some .scanOutput) state contents temporary saved outputTemporary result)
      (some (config program (some .restoreOutput) (state.1,state.2.1,none)
        (Function.update contents program.k₁ []) temporary saved (output.reverse++outputTemporary) result))
      (output.length+1) := by
  induction output generalizing contents state outputTemporary with
  | nil =>
      simpa only [List.reverse_nil,List.nil_append,List.length_nil] using
        StackMachineComposition.oneStep (scanOutput_nil program state contents temporary saved outputTemporary result present)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep
        (scanOutput_cons program state contents head tail outputTemporary temporary saved result present)
      have rest := ih (state.1,state.2.1,some head) (Function.update contents program.k₁ tail)
        (head::outputTemporary) (by simp)
      have joined := EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ first rest
      simpa only [Function.update_idem,List.reverse_cons,List.append_assoc,List.singleton_append,
        List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

noncomputable def restoreOutputRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (outputTemporary : List (Output program)) (temporary saved : List (Input program))
    (result : List (Sum (Input program) (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .restoreOutput) state contents temporary saved outputTemporary result)
      (some (config program (some .finish) (state.1,state.2.1,none) contents temporary saved []
        (outputTemporary.reverse.map Sum.inr ++ result))) (outputTemporary.length+1) := by
  induction outputTemporary generalizing state result with
  | nil => simpa only [List.reverse_nil,List.map_nil,List.nil_append,List.length_nil] using
      StackMachineComposition.oneStep (restoreOutput_nil program state contents temporary saved result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep
        (restoreOutput_cons program state contents head tail temporary saved result)
      have rest := ih (state.1,state.2.1,some head) (.inr head::result)
      have joined := EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ first rest
      simpa only [List.reverse_cons,List.map_append,List.map_singleton,List.append_assoc,
        List.singleton_append,List.cons_append,List.nil_append,List.length_cons,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

noncomputable def finishRun (state : State program) (contents : ∀ key, List (program.Γ key))
    (saved : List (Input program)) (result : List (Sum (Input program) (Output program))) :
    EvalsToInTime (machine program).step
      (config program (some .finish) state contents [] saved [] result)
      (some (config program none (program.initialState,none,none) contents [] [] []
        (saved.reverse.map Sum.inl ++ result))) (saved.length+1) := by
  induction saved generalizing state result with
  | nil => simpa only [List.reverse_nil,List.map_nil,List.nil_append,List.length_nil] using
      StackMachineComposition.oneStep (finish_nil program state contents result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (finish_cons program state contents head tail result)
      have rest := ih (state.1,some head,state.2.2) (.inl head::result)
      have joined := EvalsToInTime.trans _ 1 (tail.length+1) _ _ _ first rest
      simpa only [List.reverse_cons,List.map_append,List.map_singleton,List.append_assoc,
        List.singleton_append,List.cons_append,List.nil_append,List.length_cons,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using joined

noncomputable def runExecution (saved : List (Input program)) {before after : program.Cfg} {bound : Nat}
    (execution : EvalsToInTime program.step before (some after) bound) :
    EvalsToInTime (machine program).step
      (config program (some (before.l.elim .scanOutput .run)) (before.var,none,none) before.stk [] saved [] [])
      (some (config program (some (after.l.elim .scanOutput .run)) (after.var,none,none) after.stk [] saved [] [])) bound :=
  StackMachineComposition.lift_execution program.step (machine program).step
    (fun source => config program (some (source.l.elim .scanOutput .run))
      (source.var,none,none) source.stk [] saved [] []) (run_step program saved) execution

theorem init_eq (input : List (Input program)) : initList (machine program) input =
    config program (some .scan) (program.initialState,none,none)
      (wordContents program program.k₀ input) [] [] [] [] := by
  simp only [initList,machine,config]
  congr 1
  funext key
  cases key with
  | none => simp [sourceKey]
  | some key => cases key with
    | none => simp [sourceKey]
    | some key => cases key with
      | none => simp [sourceKey]
      | some key => cases key with
        | none => simp [sourceKey]
        | some key =>
            by_cases same : key = program.k₀
            · subst key; simp [sourceKey,wordContents]
            · simp [sourceKey,wordContents,Function.update,same]

theorem halt_eq (result : List (Sum (Input program) (Output program))) : haltList (machine program) result =
    config program none (program.initialState,none,none) (fun _ => []) [] [] [] result := by
  simp only [haltList,machine,config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key with
      | none => simp [resultKey]
      | some key => cases key <;> simp [resultKey]

/-- An actual subroutine run returns its complete output alongside an unchanged
physical input. All copies are counted and every workspace is cleared. -/
noncomputable def outputs (input : List (Input program)) (output : List (Output program)) (bound : Nat)
    (execution : TM2OutputsInTime program input (some output) bound) :
    TM2OutputsInTime (machine program) input (some (input.map Sum.inl ++ output.map Sum.inr))
      (bound+3*input.length+2*output.length+5) := by
  have copied := scanRun program (program.initialState,none,none)
    (wordContents program program.k₀ input) input [] [] [] [] (by simp [wordContents])
  have restored := restoreRun program (program.initialState,none,none)
    (fun _ => []) input.reverse input.reverse [] []
  simp only [wordContents,Function.update_idem,Function.update_eq_self,
    List.append_nil,List.reverse_reverse] at copied restored
  have walked := runExecution program input.reverse execution
  rw [source_init,source_halt] at walked
  simp only [Option.elim_some,Option.elim_none] at walked
  have scanned := scanOutputRun program (program.initialState,none,none)
    (wordContents program program.k₁ output) output [] [] input.reverse [] (by simp [wordContents])
  simp only [wordContents,Function.update_idem,Function.update_eq_self,List.append_nil] at scanned
  have returned := restoreOutputRun program (program.initialState,none,none)
    (fun _ => []) output.reverse [] input.reverse []
  have finished := finishRun program (program.initialState,none,none)
    (fun _ => []) input.reverse (output.map Sum.inr)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at restored returned finished
  have a := EvalsToInTime.trans _ (input.length+1) (input.length+1) _ _ _ copied restored
  have b := EvalsToInTime.trans _ (input.length+1+(input.length+1)) bound _ _ _ a walked
  have c := EvalsToInTime.trans _ (bound+(input.length+1+(input.length+1))) (output.length+1) _ _ _ b scanned
  have d := EvalsToInTime.trans _ (output.length+1+(bound+(input.length+1+(input.length+1))))
    (output.length+1) _ _ _ c returned
  have e := EvalsToInTime.trans _ (output.length+1+(output.length+1+(bound+(input.length+1+(input.length+1)))))
    (input.length+1) _ _ _ d finished
  change EvalsToInTime _ (initList (machine program) _) (some (haltList (machine program) _)) _
  rw [init_eq,halt_eq]
  convert e using 1
  · rfl
  · omega

end Mettapedia.Computability.RetainedWordExecution.WithOutput

namespace Mettapedia.Computability.RetainedWordExecution.WithOutput.Framed
open Turing

variable (program : FinTM2) {Γ : Type} [Fintype Γ] [Inhabited Γ]
local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin
variable [Fintype (program.Γ program.k₁)]
  [Inhabited (program.Γ program.k₀)] [Inhabited (program.Γ program.k₁)]
variable (inputAlphabet : program.Γ program.k₀ ≃ Option Γ)
  (outputAlphabet : program.Γ program.k₁ ≃ Γ)

def untag : Sum (program.Γ program.k₀) (program.Γ program.k₁) → List (Option Γ)
  | .inl value => [inputAlphabet value]
  | .inr value => [some (outputAlphabet value)]

def closeTemplate : WordTemplateMachine.Template (Option Γ) := [none,some none]

attribute [local implicit_reducible] StackMachineComposition.machine
  WithOutput.machine WordHomomorphismMachine.machine WordTemplateMachine.machine

abbrev retainedMachine := WithOutput.machine program
local instance : Fintype ((retainedMachine program).Γ (retainedMachine program).k₁) :=
  inferInstanceAs (Fintype (Sum (program.Γ program.k₀) (program.Γ program.k₁)))
local instance : Inhabited ((retainedMachine program).Γ (retainedMachine program).k₁) :=
  inferInstanceAs (Inhabited (Sum (program.Γ program.k₀) (program.Γ program.k₁)))
local instance : Inhabited ((WordHomomorphismMachine.machine
    (untag program inputAlphabet outputAlphabet)).Γ
      (WordHomomorphismMachine.machine (untag program inputAlphabet outputAlphabet)).k₀) :=
  inferInstanceAs (Inhabited (Sum (program.Γ program.k₀) (program.Γ program.k₁)))

abbrev taggedMachine := StackMachineComposition.machine (retainedMachine program)
  (WordHomomorphismMachine.machine (untag program inputAlphabet outputAlphabet))
  (Equiv.refl (Sum (program.Γ program.k₀) (program.Γ program.k₁)))
local instance : Fintype ((taggedMachine program inputAlphabet outputAlphabet).Γ
    (taggedMachine program inputAlphabet outputAlphabet).k₁) :=
  inferInstanceAs (Fintype (Option Γ))
local instance : Inhabited ((taggedMachine program inputAlphabet outputAlphabet).Γ
    (taggedMachine program inputAlphabet outputAlphabet).k₁) :=
  inferInstanceAs (Inhabited (Option Γ))

abbrev machine := StackMachineComposition.machine (taggedMachine program inputAlphabet outputAlphabet)
  (WordTemplateMachine.machine (closeTemplate (Γ:=Γ))) (Equiv.refl (Option Γ))

def outputWord (input : List (program.Γ program.k₀)) (output : List (program.Γ program.k₁)) :
    List (Option Γ) :=
  input.map inputAlphabet ++ output.map (fun symbol => some (outputAlphabet symbol)) ++ [none]

omit [Fintype Γ] [Inhabited Γ] [Fintype (program.Γ program.k₁)]
  [Inhabited (program.Γ program.k₀)] [Inhabited (program.Γ program.k₁)] in
theorem untag_exact (input : List (program.Γ program.k₀)) (output : List (program.Γ program.k₁)) :
    (input.map Sum.inl ++ output.map Sum.inr).flatMap
      (untag program inputAlphabet outputAlphabet) =
        input.map inputAlphabet ++ output.map (fun symbol => some (outputAlphabet symbol)) := by
  simp only [List.flatMap_append,List.flatMap_map]
  have left : input.flatMap (fun symbol => untag program inputAlphabet outputAlphabet (.inl symbol)) =
      input.map inputAlphabet := by induction input <;> simp_all [untag]
  have right : output.flatMap (fun symbol => untag program inputAlphabet outputAlphabet (.inr symbol)) =
      output.map (fun symbol => some (outputAlphabet symbol)) := by induction output <;> simp_all [untag]
  rw [left,right]

/-- The subroutine is unchanged; its complete output becomes one physical
field after the retained original word. Both transfers and framing are charged. -/
noncomputable def outputs (input : List (program.Γ program.k₀)) (output : List (program.Γ program.k₁))
    (bound : Nat) (executed : TM2OutputsInTime program input (some output) bound) :
    TM2OutputsInTime (machine program inputAlphabet outputAlphabet) input
      (some (outputWord program inputAlphabet outputAlphabet input output))
      (bound+23*input.length+22*output.length+23) := by
  let retainedWord : List (Sum (program.Γ program.k₀) (program.Γ program.k₁)) :=
    input.map Sum.inl ++ output.map Sum.inr
  let mappedWord := input.map inputAlphabet ++ output.map (fun symbol => some (outputAlphabet symbol))
  have retained := WithOutput.outputs program input output bound executed
  have mapped := WordHomomorphismMachine.outputs (untag program inputAlphabet outputAlphabet) retainedWord
  dsimp only [retainedWord] at mapped
  rw [untag_exact] at mapped
  have identity : retainedWord.map (Equiv.refl (Sum (program.Γ program.k₀) (program.Γ program.k₁))) =
      retainedWord := by simp
  dsimp only [retainedWord] at identity
  rw [←identity] at mapped
  have tagged := StackMachineComposition.outputs (retainedMachine program)
    (WordHomomorphismMachine.machine (untag program inputAlphabet outputAlphabet))
    (Equiv.refl _) input retainedWord mappedWord _ _ retained mapped
  have closed := WordTemplateMachine.outputs (closeTemplate (Γ:=Γ)) mappedWord
  have framing : WordTemplateMachine.instantiate (closeTemplate (Γ:=Γ)) mappedWord =
      outputWord program inputAlphabet outputAlphabet input output := by
    simp [closeTemplate,WordTemplateMachine.instantiate,outputWord,mappedWord,List.append_assoc]
  rw [framing] at closed
  have identity : mappedWord.map (Equiv.refl (Option Γ)) = mappedWord := by simp
  rw [←identity] at closed
  have joined := StackMachineComposition.outputs (taggedMachine program inputAlphabet outputAlphabet)
    (WordTemplateMachine.machine (closeTemplate (Γ:=Γ))) (Equiv.refl _)
    input mappedWord (outputWord program inputAlphabet outputAlphabet input output) _ _ tagged closed
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  simp only [retainedWord,mappedWord,closeTemplate,List.length_cons,List.length_nil,
    List.length_append,List.length_map]
  omega

end Mettapedia.Computability.RetainedWordExecution.WithOutput.Framed

import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.RetainedWordExecution

/-!
# Dispatching a finite family in one physical stack arena

A finite tag selects a statically authored program. The wrapper copies the
remaining word into the shared arena, runs the selected original instructions,
and resets its caller registers before returning. Missing selections drain the
input and return an explicit refusal. Labels may differ between programs;
dynamic words are never stored in internal control registers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.CommonArenaDispatch
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability.StackMachineRegisters

structure Family (base : FinTM2) (Index : Type) where
  alphabet : Index → base.K → Type
  cellTypes : ∀ index key, alphabet index key = base.Γ key
  Label : Index → Type
  labelFinite : ∀ index, Fintype (Label index)
  main : ∀ index, Label index
  body : ∀ index, Label index → TM2.Stmt (alphabet index) (Label index) base.σ

namespace Family
variable {Index : Type} {base : FinTM2}
local instance : Fintype (base.Γ base.k₀) := base.Γk₀Fin

def toMachine (family : Family base Index) (index : Index) : FinTM2 where
  K := base.K
  kDecidableEq := base.kDecidableEq
  kFin := base.kFin
  k₀ := base.k₀
  k₁ := base.k₁
  Γ := family.alphabet index
  Γk₀Fin := Fintype.ofEquiv (base.Γ base.k₀) (Equiv.cast (family.cellTypes index base.k₀).symm)
  Λ := family.Label index
  ΛFin := family.labelFinite index
  main := family.main index
  σ := base.σ
  σFin := base.σFin
  initialState := base.initialState
  m := family.body index

end Family
attribute [local implicit_reducible] Family.toMachine

variable {Index : Type} [Fintype Index] (base : FinTM2) (family : Family base Index)
variable (defaultInput : base.Γ base.k₀) (refusal : base.Γ base.k₁)

abbrev InputCell (base : FinTM2) (_family : Family base Index) := Sum (base.Γ base.k₀) (Option Index)
abbrev Key (base : FinTM2) := Option (Option base.K)
abbrev Cells (base : FinTM2) (family : Family base Index) := withStackAlphabet (withStackAlphabet base.Γ (base.Γ base.k₀)) (InputCell base family)
abbrev Extra (base : FinTM2) (family : Family base Index) := Option (InputCell base family) × Option (base.Γ base.k₀)
abbrev State (base : FinTM2) (family : Family base Index) := base.σ × Extra base family
abbrev inputKey (base : FinTM2) : Key base := none
abbrev transferKey (base : FinTM2) : Key base := some none
abbrev baseKey (key : base.K) : Key base := some (some key)

local instance : Fintype base.K := base.kFin
local instance : DecidableEq base.K := base.kDecidableEq
local instance : Fintype base.σ := base.σFin
local instance : Fintype (base.Γ base.k₀) := base.Γk₀Fin
local instance (index : Index) : Fintype (family.toMachine index).Λ := family.labelFinite index

inductive Phase where
  | read | copy (index : Index) | restore (index : Index)
  | run (index : Index) (label : (family.toMachine index).Λ)
  | finish | rejectInput | rejectTransfer
  deriving Fintype

omit [Fintype Index] in
/-- Each selected program shares the physical alphabet family while retaining
its own finite label type. -/
theorem cellTypes (index : Index) (key : base.K) :
    (family.toMachine index).Γ key = base.Γ key := family.cellTypes index key

def readByte : Option (InputCell base family) → Option (base.Γ base.k₀)
  | some (.inl byte) => some byte
  | _ => none

namespace Programs

/-- Embed the supplied original row body without a runtime machine bundle. -/
def embedded (instructions : ∀ index, family.Label index →
    TM2.Stmt (family.alphabet index) (family.Label index) base.σ)
    (index : Index) (label : family.Label index) :
    TM2.Stmt (Cells base family) (Phase base family) (State base family) :=
  embedStatement (fun key => some (some key)) (.run index)
    (fun state => state.1) (fun state value => (value, state.2))
    (cellTypes base family index) (goto fun _ => .finish) (instructions index label)

/-- The executable wrapper receives only finite instructions, actual stack
addresses and register values. No bundled finiteness witness is inspected. -/
def body (sourceInput sourceOutput : Key base)
    (inputType : Cells base family sourceInput = base.Γ base.k₀)
    (outputType : Cells base family sourceOutput = base.Γ base.k₁)
    (initial : base.σ) (mains : ∀ index, family.Label index)
    (instructions : ∀ index, family.Label index →
      TM2.Stmt (family.alphabet index) (family.Label index) base.σ)
    (defaultInput : base.Γ base.k₀) (refusal : base.Γ base.k₁)
    (phase : Phase base family) : TM2.Stmt (Cells base family) (Phase base family) (State base family) :=
  match phase with
  | .read => pop (inputKey base) (fun state cell => (state.1, cell, state.2.2))
      (goto fun state => match state.2.1 with
        | some (.inr (some index)) => .copy index
        | _ => .rejectInput)
  | .copy index => pop (inputKey base) (fun state cell => (state.1, cell, readByte base family cell))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .restore index)
        (branch (fun state => state.2.2.isSome)
          (push (transferKey base) (fun state => state.2.2.getD defaultInput) (goto fun _ => .copy index))
          (goto fun _ => .rejectInput)))
  | .restore index => pop (transferKey base) (fun state byte => (state.1, state.2.1, byte))
      (branch (fun state => state.2.2.isSome)
        (push sourceInput (fun state => inputType.mpr (state.2.2.getD defaultInput)) (goto fun _ => .restore index))
        (load (fun _ => (initial, none, none))
          (goto fun _ => .run index (mains index))))
  | .run index label => embedded base family instructions index label
  | .finish => load (fun _ => (initial, none, none)) halt
  | .rejectInput => pop (inputKey base) (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectTransfer))
  | .rejectTransfer => pop (transferKey base) (fun state byte => (state.1, state.2.1, byte))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectTransfer)
        (push sourceOutput (fun _ => outputType.mpr refusal)
          (load (fun _ => (initial, none, none)) halt)))

end Programs

def body (index : Index) (label : family.Label index) :=
  Programs.embedded base family family.body index label

/-- The bundled mathematical machine uses the same executable instructions. -/
def program := Programs.body base family (baseKey base base.k₀) (baseKey base base.k₁)
  rfl rfl base.initialState family.main family.body defaultInput refusal


def machine : FinTM2 where
  K := Key base
  k₀ := inputKey base
  k₁ := baseKey base base.k₁
  Γ := Cells base family
  Γk₀Fin := by change Fintype (InputCell base family); infer_instance
  Λ := Phase base family
  main := .read
  σ := State base family
  initialState := (base.initialState, none, none)
  m := program base family defaultInput refusal

attribute [local implicit_reducible] machine program

theorem machine_body (phase : Phase base family) :
    (machine base family defaultInput refusal).m phase = program base family defaultInput refusal phase := rfl

def config (phase : Option (Phase base family)) (state : State base family)
    (input : List (InputCell base family)) (transfer : List (base.Γ base.k₀))
    (contents : ∀ key, List (base.Γ key)) : (machine base family defaultInput refusal).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => input
    | some none => transfer
    | some (some key) => contents key

/-- The original row's stack words are preserved through the common physical
alphabet, including every byte of opaque arguments. -/
def originalContents (index : Index)
    (contents : ∀ key, List ((family.toMachine index).Γ key)) :
    ∀ key, List (base.Γ key) := fun key => (contents key).map (cellTypes base family index key).mp

def embeddedContents (index : Index) (input : List (InputCell base family))
    (transfer : List (base.Γ base.k₀))
    (contents : ∀ key, List ((family.toMachine index).Γ key)) :
    ∀ key, List (Cells base family key) :=
  (config base family defaultInput refusal none (base.initialState, none, none) input transfer
    (originalContents base family index contents)).stk

private theorem embeddedContents_read (index : Index) (input : List (InputCell base family))
    (transfer : List (base.Γ base.k₀))
    (contents : ∀ key, List ((family.toMachine index).Γ key)) (key : base.K) :
    embeddedContents base family defaultInput refusal index input transfer contents (baseKey base key) =
      (contents key).map (cellTypes base family index key).mp := rfl

private theorem embeddedContents_update (index : Index) (input : List (InputCell base family))
    (transfer : List (base.Γ base.k₀))
    (contents : ∀ key, List ((family.toMachine index).Γ key))
    (key : base.K) (word : List ((family.toMachine index).Γ key)) :
    embeddedContents base family defaultInput refusal index input transfer (Function.update contents key word) =
      Function.update (embeddedContents base family defaultInput refusal index input transfer contents) (baseKey base key)
        (word.map (cellTypes base family index key).mp) := by
  funext physical
  cases physical with
  | none => simp [embeddedContents, config, Function.update, baseKey]
  | some physical => cases physical with
    | none => simp [embeddedContents, config, Function.update, baseKey]
    | some original =>
      by_cases same : original = key
      · subst original; simp [embeddedContents, config, originalContents, Function.update, baseKey]
      · simp [embeddedContents, config, originalContents, Function.update, baseKey, same]

def runConfig (index : Index) (input : List (InputCell base family))
    (transfer : List (base.Γ base.k₀))
    (source : (family.toMachine index).Cfg) : (machine base family defaultInput refusal).Cfg :=
  embeddedReturningConfig (.run index) .finish (fun state => (state, none, none))
    (embeddedContents base family defaultInput refusal index input transfer) source

/-- One original program transition is one dispatcher transition. No source
semantic result is computed by this embedding. -/
theorem run_step (index : Index) (input : List (InputCell base family)) (transfer : List (base.Γ base.k₀))
    (before after : (family.toMachine index).Cfg)
    (computed : (family.toMachine index).step before = some after) :
    (machine base family defaultInput refusal).step (runConfig base family defaultInput refusal index input transfer before) =
      some (runConfig base family defaultInput refusal index input transfer after) := by
  exact step_embedStatement (baseKey base) (.run index) .finish
    (fun state => state.1) (fun state value => (value, state.2))
    (cellTypes base family index) (fun state => (state, none, none))
    (embeddedContents base family defaultInput refusal index input transfer)
    (fun _ => rfl) (fun _ _ => rfl)
    (embeddedContents_read base family defaultInput refusal index input transfer)
    (embeddedContents_update base family defaultInput refusal index input transfer)
    (family.toMachine index).m (program base family defaultInput refusal) before after
    (fun _ _ => rfl) computed


local macro "arena_step" : tactic => do
  let base := Lean.mkIdent `base
  `(tactic| (
  simp_all [FinTM2.step, machine, program, Programs.body, config, inputKey, transferKey, baseKey,
    readByte, TM2.step, TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key with
        | none => rfl
        | some key => cases key with
          | none => rfl
          | some key =>
            by_cases same : key = ($base).k₀
            · subst key; simp [Function.update]
            · simp [Function.update, same])))

theorem read_selected (index : Index) (state : State base family)
    (input : List (InputCell base family)) (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .read) state (.inr (some index) :: input) [] contents) =
      some (config base family defaultInput refusal (some (.copy index)) (state.1, some (.inr (some index)), state.2.2)
        input [] contents) := by arena_step

theorem copy_cons (index : Index) (state : State base family) (head : (base.Γ base.k₀))
    (tail : List (base.Γ base.k₀)) (transfer : List (base.Γ base.k₀)) (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some (.copy index)) state
      ((head :: tail).map Sum.inl) transfer contents) =
      some (config base family defaultInput refusal (some (.copy index)) (state.1, some (.inl head), some head)
        (tail.map Sum.inl) (head :: transfer) contents) := by arena_step

theorem copy_nil (index : Index) (state : State base family) (transfer : List (base.Γ base.k₀))
    (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some (.copy index)) state [] transfer contents) =
      some (config base family defaultInput refusal (some (.restore index)) (state.1, none, none) [] transfer contents) := by arena_step

theorem restore_cons (index : Index) (state : State base family) (head : (base.Γ base.k₀))
    (tail : List (base.Γ base.k₀)) (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some (.restore index)) state [] (head :: tail) contents) =
      some (config base family defaultInput refusal (some (.restore index)) (state.1, state.2.1, some head) [] tail
        (Function.update contents base.k₀ (head :: contents base.k₀))) := by arena_step

theorem restore_nil (index : Index) (state : State base family)
    (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some (.restore index)) state [] [] contents) =
      some (config base family defaultInput refusal (some (.run index (family.toMachine index).main))
        (base.initialState, none, none) [] [] contents) := by arena_step

theorem finish_step (state : State base family) (contents : ∀ key, List (base.Γ key)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .finish) state [] [] contents) =
      some (config base family defaultInput refusal none (base.initialState, none, none) [] [] contents) := by arena_step

noncomputable def copyRun (index : Index) (state : State base family)
    (word transfer : List (base.Γ base.k₀)) (contents : ∀ key, List (base.Γ key)) :
    StateTransition.EvalsToInTime (machine base family defaultInput refusal).step
      (config base family defaultInput refusal (some (.copy index)) state (word.map Sum.inl) transfer contents)
      (some (config base family defaultInput refusal (some (.restore index)) (state.1, none, none) []
        (word.reverse ++ transfer) contents)) (word.length + 1) := by
  induction word generalizing state transfer with
  | nil => simpa only [List.map_nil, List.reverse_nil, List.nil_append, List.length_nil] using
      Mettapedia.Computability.StackMachineComposition.oneStep (copy_nil base family defaultInput refusal index state transfer contents)
  | cons head tail ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep
        (copy_cons base family defaultInput refusal index state head tail transfer contents)
      have rest := ih (state.1, some (.inl head), some head) (head :: transfer)
      have joined := StateTransition.EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def restoreRun (index : Index) (state : State base family)
    (transfer : List (base.Γ base.k₀)) (contents : ∀ key, List (base.Γ key)) :
    StateTransition.EvalsToInTime (machine base family defaultInput refusal).step
      (config base family defaultInput refusal (some (.restore index)) state [] transfer contents)
      (some (config base family defaultInput refusal (some (.run index (family.toMachine index).main))
        (base.initialState, none, none) [] []
        (Function.update contents base.k₀ (List.append (α := (base.Γ base.k₀)) transfer.reverse (contents base.k₀)))))
      (transfer.length + 1) := by
  induction transfer generalizing state contents with
  | nil => simpa only [List.append_eq_has_append, List.reverse_nil, List.nil_append, Function.update_eq_self, List.length_nil] using
      Mettapedia.Computability.StackMachineComposition.oneStep (restore_nil base family defaultInput refusal index state contents)
  | cons head tail ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep
        (restore_cons base family defaultInput refusal index state head tail contents)
      have rest := ih (state.1, state.2.1, some head)
        (Function.update contents base.k₀ (head :: contents base.k₀))
      have joined := StateTransition.EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa only [List.append_eq_has_append, Function.update_idem, Function.update_self, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

noncomputable def runExecution (index : Index) {before after :
    (family.toMachine index).Cfg} {bound : Nat}
    (execution : StateTransition.EvalsToInTime
      (family.toMachine index).step before (some after) bound) :
    StateTransition.EvalsToInTime (machine base family defaultInput refusal).step
      (runConfig base family defaultInput refusal index [] [] before) (some (runConfig base family defaultInput refusal index [] [] after)) bound :=
  Mettapedia.Computability.StackMachineComposition.lift_execution
    (family.toMachine index).step (machine base family defaultInput refusal).step
    (runConfig base family defaultInput refusal index [] []) (run_step base family defaultInput refusal index [] []) execution


omit [Fintype Index] in
private theorem originalContents_word (index : Index) (sourceKey : base.K)
    (word : List ((family.toMachine index).Γ sourceKey)) :
    originalContents base family index
        (RetainedWordExecution.wordContents (family.toMachine index) sourceKey word) =
      RetainedWordExecution.wordContents base sourceKey (word.map (cellTypes base family index sourceKey).mp) := by
  funext key
  by_cases same : key = sourceKey
  · subst key; simp [originalContents, RetainedWordExecution.wordContents]
  · simp [originalContents, RetainedWordExecution.wordContents, Function.update, same]

theorem run_init (index : Index) (word : List ((family.toMachine index).Γ base.k₀)) :
    runConfig base family defaultInput refusal index [] []
      (initList (family.toMachine index) word) =
    config base family defaultInput refusal
      (some (.run index (family.toMachine index).main))
      (base.initialState, none, none) [] []
      (RetainedWordExecution.wordContents base base.k₀
        (word.map (cellTypes base family index base.k₀).mp)) := by
  rw [RetainedWordExecution.source_init]
  simp only [runConfig, embeddedReturningConfig, Option.elim_some, embeddedContents, config,
    originalContents_word]
  rfl

theorem run_halt (index : Index) (word : List ((family.toMachine index).Γ base.k₁)) :
    runConfig base family defaultInput refusal index [] []
      (haltList (family.toMachine index) word) =
    config base family defaultInput refusal (some .finish)
      (base.initialState, none, none) [] []
      (RetainedWordExecution.wordContents base base.k₁
        (word.map (cellTypes base family index base.k₁).mp)) := by
  rw [RetainedWordExecution.source_halt]
  simp only [runConfig, embeddedReturningConfig, Option.elim_none, embeddedContents, config,
    originalContents_word]
  rfl

theorem init_eq (input : List (InputCell base family)) :
    initList (machine base family defaultInput refusal) input =
      config base family defaultInput refusal (some .read) (base.initialState, none, none) input [] (fun _ => []) := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [inputKey]
  | some key => cases key <;> simp [inputKey]

theorem halt_eq (word : List (base.Γ base.k₁)) :
    haltList (machine base family defaultInput refusal) word =
      config base family defaultInput refusal none (base.initialState, none, none) [] []
        (RetainedWordExecution.wordContents base base.k₁ word) := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [baseKey]
  | some key => cases key with
    | none => simp [baseKey]
    | some key =>
      by_cases same : key = base.k₁
      · subst key; simp [RetainedWordExecution.wordContents, baseKey]
      · simp [RetainedWordExecution.wordContents, baseKey, Function.update, same]


theorem read_absent (state : State base family) (input : List (InputCell base family)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .read) state (.inr none :: input) [] (fun _ => [])) =
      some (config base family defaultInput refusal (some .rejectInput) (state.1, some (.inr none), state.2.2)
        input [] (fun _ => [])) := by arena_step

theorem reject_cons (state : State base family) (head : InputCell base family)
    (tail : List (InputCell base family)) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .rejectInput) state (head :: tail) [] (fun _ => [])) =
      some (config base family defaultInput refusal (some .rejectInput) (state.1, some head, state.2.2) tail [] (fun _ => [])) := by arena_step

theorem reject_nil (state : State base family) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .rejectInput) state [] [] (fun _ => [])) =
      some (config base family defaultInput refusal (some .rejectTransfer) (state.1, none, state.2.2) [] [] (fun _ => [])) := by arena_step

theorem refuse_step (state : State base family) :
    (machine base family defaultInput refusal).step (config base family defaultInput refusal (some .rejectTransfer) state [] [] (fun _ => [])) =
      some (config base family defaultInput refusal none (base.initialState, none, none) [] []
        (RetainedWordExecution.wordContents base base.k₁ [refusal])) := by
  simp [FinTM2.step, machine, program, Programs.body, config, transferKey, baseKey, TM2.step, TM2.stepAux,
    RetainedWordExecution.wordContents]
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key =>
      by_cases same : key = base.k₁
      · subst key; simp [Function.update]
      · simp [Function.update, same]

noncomputable def rejectRun (state : State base family) (input : List (InputCell base family)) :
    StateTransition.EvalsToInTime (machine base family defaultInput refusal).step
      (config base family defaultInput refusal (some .rejectInput) state input [] (fun _ => []))
      (some (config base family defaultInput refusal (some .rejectTransfer) (state.1, none, state.2.2) [] [] (fun _ => [])))
      (input.length + 1) := by
  induction input generalizing state with
  | nil => exact Mettapedia.Computability.StackMachineComposition.oneStep (reject_nil base family defaultInput refusal state)
  | cons head tail ih =>
    have first := Mettapedia.Computability.StackMachineComposition.oneStep (reject_cons base family defaultInput refusal state head tail)
    have rest := ih (state.1, some head, state.2.2)
    have joined := StateTransition.EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- A selected row executes its original finite program. Input/output casts
only identify equal physical alphabets; every copying transition is counted. -/
noncomputable def outputs_selected (index : Index)
    (input : List (base.Γ base.k₀)) (output : List (base.Γ base.k₁)) (bound : Nat)
    (source : TM2OutputsInTime (family.toMachine index)
      (input.map (cellTypes base family index base.k₀).mpr)
      (some (output.map (cellTypes base family index base.k₁).mpr)) bound) :
    TM2OutputsInTime (machine base family defaultInput refusal)
      (.inr (some index) :: input.map Sum.inl) (some output)
      (2 * input.length + bound + 4) := by
  have inputCast : (input.map (cellTypes base family index base.k₀).mpr).map
      (cellTypes base family index base.k₀).mp = input := by simp [Function.comp_def, cast_cast]
  have outputCast : (output.map (cellTypes base family index base.k₁).mpr).map
      (cellTypes base family index base.k₁).mp = output := by simp [Function.comp_def, cast_cast]
  have first := StackMachineComposition.oneStep
    (read_selected base family defaultInput refusal index (base.initialState, none, none)
      (input.map Sum.inl) (fun _ => []))
  have copied := copyRun base family defaultInput refusal index
    (base.initialState, some (.inr (some index)), none) input [] (fun _ => [])
  have restored := restoreRun base family defaultInput refusal index
    (base.initialState, none, none) input.reverse (fun _ => [])
  simp only [List.append_eq_has_append, List.append_nil, List.reverse_reverse,
    List.length_reverse] at copied restored
  have walked := runExecution base family defaultInput refusal index source
  rw [run_init, run_halt, inputCast, outputCast] at walked
  have finished := StackMachineComposition.oneStep
    (finish_step base family defaultInput refusal (base.initialState, none, none)
      (RetainedWordExecution.wordContents base base.k₁ output))
  have a := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first copied
  have b := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ a restored
  have c := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ b walked
  have d := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ c finished
  change StateTransition.EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq, halt_eq]
  convert d using 1
  omega

/-- An absent selection drains the complete remaining physical word and
returns explicit refusal with the common arena and registers cleared. -/
noncomputable def outputs_absent (input : List (base.Γ base.k₀)) :
    TM2OutputsInTime (machine base family defaultInput refusal)
      (.inr none :: input.map Sum.inl) (some [refusal]) (input.length + 3) := by
  have first := StackMachineComposition.oneStep
    (read_absent base family defaultInput refusal (base.initialState, none, none)
      (input.map Sum.inl))
  have rest := rejectRun base family defaultInput refusal
    (base.initialState, some (.inr none), none) (input.map Sum.inl)
  have last := StackMachineComposition.oneStep
    (refuse_step base family defaultInput refusal (base.initialState, none, none))
  have a := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
  have b := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ a last
  change StateTransition.EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq, halt_eq]
  convert b using 1
  simp; omega

end Mettapedia.Computability.CommonArenaDispatch

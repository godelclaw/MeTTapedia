import Mettapedia.Languages.HOLLight.GraphRelocationEmission
import Mettapedia.Languages.HOLLight.GraphAddressSequenceProgram

/-!
# Original graph relocation through physical instruction tables

The whole table retains the original payload and external-root words, earns
internal addresses with the existing sequence table, and runs the original
relocation descriptor. Physical endpoints and initial registers are explicit.
The instruction table, initialization and counted execution equal the original
machine; finiteness metadata is absent from the executable interfaces.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.GraphRelocationEmission.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
attribute [local implicit_reducible] GraphRelocationEmission.machine preparedMachine retainedMachine
  selectedAddressMachine GraphAddressSequence.machine StackMachineComposition.machine
  RetainedWordExecution.WithOutput.machine WordHomomorphismMachine.machine Indexed.machine

local instance (arity premiseCount : Nat) : Fintype ((Indexed.machine (basePlan arity premiseCount)).Γ
    (Indexed.machine (basePlan arity premiseCount)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (arity premiseCount : Nat) : Inhabited ((Indexed.machine (basePlan arity premiseCount)).Γ
    (Indexed.machine (basePlan arity premiseCount)).k₁) := inferInstanceAs (Inhabited Alphabet)
local instance (arity premiseCount internalCount : Nat) : Fintype ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Fintype ((retainedMachine arity premiseCount internalCount).Γ
    (retainedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype TaggedCell)
local instance (arity premiseCount internalCount : Nat) : Inhabited ((retainedMachine arity premiseCount internalCount).Γ
    (retainedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited TaggedCell)
local instance (arity premiseCount internalCount : Nat) : Fintype ((preparedMachine arity premiseCount internalCount).Γ
    (preparedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((preparedMachine arity premiseCount internalCount).Γ
    (preparedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def selected (arity premiseCount internalCount : Nat) : (selectedAddressMachine arity premiseCount internalCount).Λ →
    (selectedAddressMachine arity premiseCount internalCount).Stmt :=
  StackMachineComposition.Programs.body Indexed.Stack.result
    (GraphAddressSequence.Program.inputKey (offsets internalCount))
    (GraphAddressSequence.Program.mainLabel (offsets internalCount)) (0 : Alphabet) id
    (Indexed.arrayProgram (basePlan arity premiseCount).length (basePlan arity premiseCount).toArray)
    (GraphAddressSequence.Program.body (offsets internalCount))
theorem selected_eq (arity premiseCount internalCount : Nat) :
    selected arity premiseCount internalCount = (selectedAddressMachine arity premiseCount internalCount).m := by
  unfold selected
  rw [Indexed.arrayProgram_eq_program,GraphAddressSequence.Program.body_exact]
  exact StackMachineComposition.body_eq (Indexed.machine (basePlan arity premiseCount))
    (GraphAddressSequence.machine (offsets internalCount)) (Equiv.refl Alphabet)

abbrev selectedInput (arity premiseCount internalCount : Nat) : (selectedAddressMachine arity premiseCount internalCount).K :=
  some (.inl Indexed.Stack.input)
abbrev selectedResult (arity premiseCount internalCount : Nat) : (selectedAddressMachine arity premiseCount internalCount).K :=
  some (.inr (GraphAddressSequence.Program.resultKey (offsets internalCount)))
def selectedInitial (arity premiseCount internalCount : Nat) : (selectedAddressMachine arity premiseCount internalCount).σ :=
  (none,GraphAddressSequence.Program.registers (offsets internalCount),none)
def selectedMain (arity premiseCount internalCount : Nat) : (selectedAddressMachine arity premiseCount internalCount).Λ :=
  .inl (.emit ⟨0,by simp [basePlan]⟩)

def retained (arity premiseCount internalCount : Nat) : (retainedMachine arity premiseCount internalCount).Λ →
    (retainedMachine arity premiseCount internalCount).Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement (selectedInput arity premiseCount internalCount)
    (selectedResult arity premiseCount internalCount) (none : Option Alphabet) (none : Option Alphabet)
    (selectedInitial arity premiseCount internalCount) (selectedMain arity premiseCount internalCount)
    (selected arity premiseCount internalCount)
theorem retained_eq (arity premiseCount internalCount : Nat) :
    retained arity premiseCount internalCount = (retainedMachine arity premiseCount internalCount).m := by
  unfold retained
  rw [selected_eq]
  rfl

def prepared (arity premiseCount internalCount : Nat) : (preparedMachine arity premiseCount internalCount).Λ →
    (preparedMachine arity premiseCount internalCount).Stmt :=
  StackMachineComposition.Programs.body (FirstAlphabet := (retainedMachine arity premiseCount internalCount).Γ)
    none WordHomomorphismMachine.Stack.input .read (default : TaggedCell) id
    (retained arity premiseCount internalCount) (WordHomomorphismMachine.program untag)
theorem prepared_eq (arity premiseCount internalCount : Nat) :
    prepared arity premiseCount internalCount = (preparedMachine arity premiseCount internalCount).m := by
  unfold prepared
  rw [retained_eq]
  exact StackMachineComposition.body_eq (retainedMachine arity premiseCount internalCount)
    (WordHomomorphismMachine.machine untag) (Equiv.refl TaggedCell)

abbrev preparedInput (arity premiseCount internalCount : Nat) : (preparedMachine arity premiseCount internalCount).K :=
  some (.inl (some (some (some (some (selectedInput arity premiseCount internalCount))))))
abbrev preparedResult (arity premiseCount internalCount : Nat) : (preparedMachine arity premiseCount internalCount).K :=
  some (.inr WordHomomorphismMachine.Stack.result)
def preparedInitial (arity premiseCount internalCount : Nat) : (preparedMachine arity premiseCount internalCount).σ :=
  ((selectedInitial arity premiseCount internalCount,none,none),(none,none),none)

variable {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity)
  (safe : SafeBlock premiseCount internalCount block)
abbrev target := machine premiseCount internalCount block safe

def bodyWithArray (instructions : Array (Alphabet ⊕ Fin ((arity+premiseCount+1)+internalCount))) :
    (target premiseCount internalCount block safe).Λ → (target premiseCount internalCount block safe).Stmt :=
  StackMachineComposition.Programs.body (preparedResult arity premiseCount internalCount) Indexed.Stack.input
    (.emit ⟨0,by simp [template,Templates.pair]⟩) (none : Option Alphabet) id
    (prepared arity premiseCount internalCount)
    (Indexed.arrayProgram (template premiseCount internalCount block safe).length instructions)
def body : (target premiseCount internalCount block safe).Λ → (target premiseCount internalCount block safe).Stmt :=
  bodyWithArray premiseCount internalCount block safe (template premiseCount internalCount block safe).toArray
theorem body_eq : body premiseCount internalCount block safe = (target premiseCount internalCount block safe).m := by
  unfold body bodyWithArray
  rw [prepared_eq,Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq (preparedMachine arity premiseCount internalCount)
    (Indexed.machine (template premiseCount internalCount block safe)) (Equiv.refl (Option Alphabet))

def keyEquality : DecidableEq (target premiseCount internalCount block safe).K := by claim_program_key_equality
local instance : DecidableEq (target premiseCount internalCount block safe).K := keyEquality premiseCount internalCount block safe

def registerEquality : DecidableEq (target premiseCount internalCount block safe).σ := by claim_program_key_equality

def stepWithArray (instructions : Array (Alphabet ⊕ Fin ((arity+premiseCount+1)+internalCount))) :=
  @TM2.step (target premiseCount internalCount block safe).K (target premiseCount internalCount block safe).Γ
    (target premiseCount internalCount block safe).Λ (target premiseCount internalCount block safe).σ
    (keyEquality premiseCount internalCount block safe) (bodyWithArray premiseCount internalCount block safe instructions)
def step := stepWithArray premiseCount internalCount block safe (template premiseCount internalCount block safe).toArray
theorem step_eq : step premiseCount internalCount block safe = (target premiseCount internalCount block safe).step := by
  unfold step stepWithArray
  rw [show keyEquality premiseCount internalCount block safe = (target premiseCount internalCount block safe).kDecidableEq from Subsingleton.elim _ _]
  change TM2.step (body premiseCount internalCount block safe) = _
  rw [body_eq]
  rfl

abbrev inputKey : (target premiseCount internalCount block safe).K := some (.inl (preparedInput arity premiseCount internalCount))
abbrev resultKey : (target premiseCount internalCount block safe).K := some (.inr Indexed.Stack.result)
def registers : (target premiseCount internalCount block safe).σ := (preparedInitial arity premiseCount internalCount,none,none)
theorem registers_eq : registers premiseCount internalCount block safe = (target premiseCount internalCount block safe).initialState := rfl
abbrev mainLabel : (target premiseCount internalCount block safe).Λ := .inl (.inl .scan)

def initial (word : List (Option Alphabet)) : (target premiseCount internalCount block safe).Cfg where
  l := some (mainLabel premiseCount internalCount block safe)
  var := registers premiseCount internalCount block safe
  stk key := @dite (List ((target premiseCount internalCount block safe).Γ key))
    (key = inputKey premiseCount internalCount block safe)
    (keyEquality premiseCount internalCount block safe key (inputKey premiseCount internalCount block safe))
    (fun same => same.symm ▸ word) (fun _ => [])
theorem initial_eq (word : List (Option Alphabet)) :
    initial premiseCount internalCount block safe word = initList (target premiseCount internalCount block safe) word := by
  have equality : keyEquality premiseCount internalCount block safe = (target premiseCount internalCount block safe).kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [equality,registers_eq]
  unfold initList
  congr 1
  funext key
  by_cases same : key = inputKey premiseCount internalCount block safe
  · subst key
    simp [show inputKey premiseCount internalCount block safe = (target premiseCount internalCount block safe).k₀ from rfl]
  · have different : key ≠ (target premiseCount internalCount block safe).k₀ := same
    simp only [dif_neg same,dif_neg different]

def selectedKeys (arity premiseCount internalCount : Nat) : List (selectedAddressMachine arity premiseCount internalCount).K :=
  none :: (([Indexed.Stack.input,.result,.output,.temporary].map (some ∘ Sum.inl)) ++
    (GraphAddressSequence.Program.keys (offsets internalCount)).map (some ∘ Sum.inr))
private theorem selectedKeys_complete (arity premiseCount internalCount : Nat) :
    ∀ key, key ∈ selectedKeys arity premiseCount internalCount := by
  intro key
  cases key with
  | none => simp [selectedKeys]
  | some key =>
    cases key with
    | inl key => cases key <;> simp [selectedKeys]
    | inr key =>
      unfold selectedKeys
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact List.mem_map_of_mem (GraphAddressSequence.Program.all_keys (offsets internalCount) key)

def retainedKeys (arity premiseCount internalCount : Nat) : List (retainedMachine arity premiseCount internalCount).K :=
  [none,some none,some (some none),some (some (some none))] ++
    (selectedKeys arity premiseCount internalCount).map (some ∘ some ∘ some ∘ some)
private theorem retainedKeys_complete (arity premiseCount internalCount : Nat) :
    ∀ key, key ∈ retainedKeys arity premiseCount internalCount := by
  intro key
  rcases key with _ | (_ | (_ | (_ | key))) <;> simp [retainedKeys,selectedKeys_complete arity premiseCount internalCount]

def preparedKeys (arity premiseCount internalCount : Nat) : List (preparedMachine arity premiseCount internalCount).K :=
  none :: ((retainedKeys arity premiseCount internalCount).map (some ∘ Sum.inl) ++
    ([WordHomomorphismMachine.Stack.input,.output,.result].map (some ∘ Sum.inr)))
private theorem preparedKeys_complete (arity premiseCount internalCount : Nat) :
    ∀ key, key ∈ preparedKeys arity premiseCount internalCount := by
  intro key
  cases key with
  | none => simp [preparedKeys]
  | some key =>
    cases key with
    | inl key =>
      unfold preparedKeys
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      exact List.mem_map_of_mem (retainedKeys_complete arity premiseCount internalCount key)
    | inr key => cases key <;> simp [preparedKeys]

def keys : List (target premiseCount internalCount block safe).K :=
  none :: ((preparedKeys arity premiseCount internalCount).map (some ∘ Sum.inl) ++
    ([Indexed.Stack.input,.result,.output,.temporary].map (some ∘ Sum.inr)))
theorem all_keys : ∀ key, key ∈ keys premiseCount internalCount block safe := by
  intro key
  cases key with
  | none => simp [keys]
  | some key =>
    cases key with
    | inl key =>
      unfold keys
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      exact List.mem_map_of_mem (preparedKeys_complete arity premiseCount internalCount key)
    | inr key => cases key <;> simp [keys]

open StackMachineRegisters.StackSnapshot

def refresh (state : (target premiseCount internalCount block safe).Cfg) : (target premiseCount internalCount block safe).Cfg :=
  let cells := snapshot (target premiseCount internalCount block safe).Γ state.stk (keys premiseCount internalCount block safe)
  {state with stk := fun key => lookup (target premiseCount internalCount block safe).Γ cells key}
theorem refresh_eq (state : (target premiseCount internalCount block safe).Cfg) :
    refresh premiseCount internalCount block safe state = state := by
  cases state with
  | mk label savedRegisters contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot (target premiseCount internalCount block safe).Γ contents (keys premiseCount internalCount block safe) key
      (all_keys premiseCount internalCount block safe key)

def periodicRefresh (period used : Nat) (state : (target premiseCount internalCount block safe).Cfg) :
    (target premiseCount internalCount block safe).Cfg :=
  if used % period == 0 then refresh premiseCount internalCount block safe state else state
theorem periodicRefresh_eq (period used : Nat) (state : (target premiseCount internalCount block safe).Cfg) :
    periodicRefresh premiseCount internalCount block safe period used state = state := by
  unfold periodicRefresh
  split <;> simp only [refresh_eq]

def run (period : Nat) : Nat → Nat → (target premiseCount internalCount block safe).Cfg →
    Option (Nat × (target premiseCount internalCount block safe).Cfg)
  | 0,_,_ => none
  | fuel+1,used,state =>
    if state.l.isNone then some (used,state)
    else match step premiseCount internalCount block safe state with
      | none => none
      | some next => run period fuel (used+1) (periodicRefresh premiseCount internalCount block safe period (used+1) next)

theorem run_actual (period fuel used : Nat) (before : (target premiseCount internalCount block safe).Cfg)
    {count : Nat} {after : (target premiseCount internalCount block safe).Cfg}
    (completed : run premiseCount internalCount block safe period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime (target premiseCount internalCount block safe).step before (some after) (count-used),
        path.steps = count-used) ∧ after.l=none := by
  induction fuel generalizing used before with
  | zero => cases completed
  | succ fuel ih =>
    simp only [run] at completed
    split at completed
    · rename_i halted
      have pair := Option.some.inj completed
      have countSame := congrArg Prod.fst pair
      have stateSame := congrArg Prod.snd pair
      change used=count at countSame
      change before=after at stateSame
      subst count
      subst after
      refine ⟨le_rfl,?_,Option.isNone_iff_eq_none.mp halted⟩
      rw [Nat.sub_self]
      exact ⟨StateTransition.EvalsToInTime.refl (target premiseCount internalCount block safe).step before,rfl⟩
    · cases advanced : step premiseCount internalCount block safe before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some next =>
        simp only [advanced] at completed
        rw [periodicRefresh_eq] at completed
        rcases ih (used+1) next completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        have original : (target premiseCount internalCount block safe).step before=some next := by rw [← step_eq]; exact advanced
        let first : StateTransition.EvalsToInTime (target premiseCount internalCount block safe).step before (some next) 1 :=
          ⟨⟨1,by change (some before).bind (target premiseCount internalCount block safe).step=some next; exact original⟩,le_rfl⟩
        have relative : count-used=(count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans (target premiseCount internalCount block safe).step 1 (count-(used+1))
          before next (some after) first tail,?_⟩
        change tail.steps+first.steps=(count-(used+1))+1
        rw [tailCount]

end Mettapedia.Languages.HOLLight.GraphRelocationEmission.Program

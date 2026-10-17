import Mettapedia.Languages.HOLLight.GraphAddressSequence
import Mettapedia.Languages.HOLLight.ClaimCheckingProgram
import Mettapedia.Languages.HOLLight.GraphAddressAdditionProgram
import Mettapedia.Computability.FramedWordMappingProgram

/-!
# Physical instructions for graph-address sequences

The extracted instructions equal the existing composed address-sequence machine.
Exhaustive snapshots retain each original stack separately. Counted execution
refreshes the configuration by equality and counts original transitions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.GraphAddressSequence.Program
open Turing Mettapedia.Computability
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
open Mettapedia.Languages.HOLLight.GraphAddressSequence
attribute [local reducible] GraphAddressSequence.machine GraphAddressSequence.preparedMachine
  GraphAddressSequence.mappedMachine GraphAddressSequence.liftMachine
  GraphAddressAddition.machine GraphAddressAddition.projectedMachine
  GraphAddressAddition.digitMachine GraphAddressAddition.addedMachine
  GraphAddressAddition.preparedMachine GraphAddressAddition.mappedMachine GraphAddressAddition.bitMachine
  StackMachineComposition.machine FramedWordMapping.machine FramedWordMapping.body
  WordHomomorphismMachine.machine WordTemplateMachine.machine WordTemplateMachine.Indexed.machine
  BinaryWordAddition.machine StackMachineComposition.leftKey StackMachineComposition.rightKey
abbrev target (offsets : List Nat) := GraphAddressSequence.machine offsets

local instance : Fintype (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Fintype Cell)
local instance : Inhabited (liftMachine.Γ liftMachine.k₁) := inferInstanceAs (Inhabited Cell)
local instance (offsets : List Nat) : Fintype ((preparedMachine offsets).Γ (preparedMachine offsets).k₁) :=
  inferInstanceAs (Fintype Cell)
local instance (offsets : List Nat) : Inhabited ((preparedMachine offsets).Γ (preparedMachine offsets).k₁) :=
  inferInstanceAs (Inhabited Cell)
local instance : Fintype (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (GraphAddressAddition.machine.Γ GraphAddressAddition.machine.k₁) := inferInstanceAs (Inhabited Alphabet)

def preparedBody (offsets : List Nat) : (preparedMachine offsets).Λ → (preparedMachine offsets).Stmt :=
  StackMachineComposition.Programs.body WordHomomorphismMachine.Stack.result WordTemplateMachine.Stack.input
    (WordTemplateMachine.Phase.emit ⟨0,Nat.zero_lt_succ _⟩) (none : Cell) id
    (WordHomomorphismMachine.program liftImage) (WordTemplateMachine.program (plan offsets))
theorem preparedBody_exact (offsets : List Nat) : preparedBody offsets = (preparedMachine offsets).m := by
  unfold preparedBody
  exact StackMachineComposition.body_eq liftMachine (WordTemplateMachine.machine (plan offsets)) (Equiv.refl Cell)

def mappedBody : mappedMachine.Λ → mappedMachine.Stmt :=
  FramedWordMapping.Programs.body GraphAddressAddition.Program.inputKey GraphAddressAddition.Program.resultKey
    GraphAddressAddition.Program.registers GraphAddressAddition.Program.mainLabel
    (none : Option Alphabet) (0 : Alphabet) GraphAddressAddition.Program.body
theorem mappedBody_exact : mappedBody = mappedMachine.m := by
  unfold mappedBody
  rw [GraphAddressAddition.Program.body_exact]
  exact FramedWordMapping.Programs.body_eq GraphAddressAddition.machine

def body (offsets : List Nat) : (target offsets).Λ → (target offsets).Stmt :=
  StackMachineComposition.Programs.body
    (FirstAlphabet := (preparedMachine offsets).Γ) (SecondAlphabet := mappedMachine.Γ)
    (some (.inr WordTemplateMachine.Stack.input) : (preparedMachine offsets).K)
    (none : mappedMachine.K) FramedWordMapping.Phase.scan (none : Cell) id (preparedBody offsets) mappedBody

theorem body_exact (offsets : List Nat) : body offsets = (target offsets).m := by
  unfold body
  rw [preparedBody_exact,mappedBody_exact]
  exact StackMachineComposition.body_eq (preparedMachine offsets) mappedMachine (Equiv.refl Cell)

def keyEquality (offsets : List Nat) : DecidableEq (target offsets).K := by claim_program_key_equality
local instance (offsets : List Nat) : DecidableEq (target offsets).K := keyEquality offsets

def registerEquality (offsets : List Nat) : DecidableEq (target offsets).σ := by claim_program_key_equality

def step (offsets : List Nat) := @TM2.step (target offsets).K (target offsets).Γ (target offsets).Λ (target offsets).σ (keyEquality offsets) (body offsets)

theorem step_exact (offsets : List Nat) : step offsets = (target offsets).step := by
  unfold step
  rw [show keyEquality offsets = (target offsets).kDecidableEq from Subsingleton.elim _ _,body_exact offsets]
  rfl

def inputKey (offsets : List Nat) : (target offsets).K := by normalize_rule_program (target offsets).k₀
def resultKey (offsets : List Nat) : (target offsets).K := by normalize_rule_program (target offsets).k₁
def registers (offsets : List Nat) : (target offsets).σ :=
  (((none,none),none,none),(GraphAddressAddition.Program.registers,none,none,none,none),none)

theorem registers_exact (offsets : List Nat) : registers offsets = (target offsets).initialState := rfl
def mainLabel (offsets : List Nat) : (target offsets).Λ := by normalize_rule_program (target offsets).main

def initial (offsets : List Nat) (word : List Alphabet) : (target offsets).Cfg where
  l := some (mainLabel offsets)
  var := registers offsets
  stk key := if same : key = inputKey offsets then by cases same; exact word else []

theorem initial_exact (offsets : List Nat) (word : List Alphabet) : initial offsets word = initList (target offsets) word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key = inputKey offsets
  · subst key
    have original : inputKey offsets = (target offsets).k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key ≠ (target offsets).k₀ := same
    simp only [dif_neg same,dif_neg original]

def keys (offsets : List Nat) : List (target offsets).K := by claim_program_keys
local instance (offsets : List Nat) : BEq (target offsets).K := ⟨fun a b => decide (a=b)⟩
local instance (offsets : List Nat) : LawfulBEq (target offsets).K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance (offsets : List Nat) : Fintype (target offsets).K := (target offsets).kFin

theorem all_keys (offsets : List Nat) : ∀ key : (target offsets).K, key ∈ keys offsets := by
  change ∀ key : (target []).K, key ∈ keys []
  decide +kernel

theorem keys_nodup (offsets : List Nat) : (keys offsets).Nodup := by
  change (keys []).Nodup
  decide +kernel

open StackMachineRegisters.StackSnapshot

def refresh (offsets : List Nat) (state : (target offsets).Cfg) : (target offsets).Cfg :=
  let cells := snapshot (target offsets).Γ state.stk (keys offsets)
  {state with stk := fun key => lookup (target offsets).Γ cells key}

theorem refresh_exact (offsets : List Nat) (state : (target offsets).Cfg) : refresh offsets state = state := by
  cases state with
  | mk label savedRegisters contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot (target offsets).Γ contents (keys offsets) key (all_keys offsets key)


def periodicRefresh (offsets : List Nat) (period used : Nat) (state : (target offsets).Cfg) : (target offsets).Cfg :=
  if used % period == 0 then refresh offsets state else state

theorem periodicRefresh_exact (offsets : List Nat) (period used : Nat) (state : (target offsets).Cfg) :
    periodicRefresh offsets period used state = state := by
  unfold periodicRefresh
  split <;> simp only [refresh_exact]

def run (offsets : List Nat) (period : Nat) : Nat → Nat → (target offsets).Cfg → Option (Nat × (target offsets).Cfg)
  | 0, _, _ => none
  | fuel+1, used, state =>
    if state.l.isNone then some (used,state)
    else match step offsets state with
      | none => none
      | some next => run offsets period fuel (used+1) (periodicRefresh offsets period (used+1) next)


theorem run_actual (offsets : List Nat) (period fuel used : Nat) (before : (target offsets).Cfg)
    {count : Nat} {after : (target offsets).Cfg}
    (completed : run offsets period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime (target offsets).step before (some after) (count-used),
        path.steps = count-used) ∧
      after.l = none := by
  induction fuel generalizing used before with
  | zero => cases completed
  | succ fuel ih =>
    simp only [run] at completed
    split at completed
    · rename_i halted
      have pair := Option.some.inj completed
      have countSame := congrArg Prod.fst pair
      have stateSame := congrArg Prod.snd pair
      change used = count at countSame
      change before = after at stateSame
      subst count
      subst after
      refine ⟨le_rfl,?_,Option.isNone_iff_eq_none.mp halted⟩
      rw [Nat.sub_self]
      exact ⟨StateTransition.EvalsToInTime.refl (target offsets).step before,rfl⟩
    · cases advanced : step offsets before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some next =>
        simp only [advanced] at completed
        rw [periodicRefresh_exact] at completed
        rcases ih (used+1) next completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        have original : (target offsets).step before = some next := by
          rw [← step_exact]
          exact advanced
        let first : StateTransition.EvalsToInTime (target offsets).step before (some next) 1 :=
          ⟨⟨1,by change (some before).bind (target offsets).step = some next; exact original⟩,le_rfl⟩
        have relative : count-used = (count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans (target offsets).step 1 (count-(used+1))
          before next (some after) first tail,?_⟩
        change tail.steps+first.steps = (count-(used+1))+1
        rw [tailCount]


end Mettapedia.Languages.HOLLight.GraphAddressSequence.Program

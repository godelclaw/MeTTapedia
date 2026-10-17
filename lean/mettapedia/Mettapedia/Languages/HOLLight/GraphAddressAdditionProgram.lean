import Mettapedia.Languages.HOLLight.GraphAddressAddition
import Mettapedia.Languages.HOLLight.ClaimCheckingProgram

/-!
# Physical instructions for original graph-address addition

The extracted instructions equal the existing composed address machine.
Exhaustive snapshots retain each original stack separately. Counted execution
refreshes the configuration by equality and counts original transitions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.GraphAddressAddition.Program
open Turing Mettapedia.Computability
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
open Mettapedia.Languages.HOLLight.GraphAddressAddition
attribute [local reducible] GraphAddressAddition.machine GraphAddressAddition.projectedMachine
  GraphAddressAddition.digitMachine GraphAddressAddition.addedMachine
  GraphAddressAddition.preparedMachine GraphAddressAddition.mappedMachine GraphAddressAddition.bitMachine
  StackMachineComposition.machine FramedWordMapping.machine FramedWordMapping.body
  WordHomomorphismMachine.machine WordTemplateMachine.machine WordTemplateMachine.Indexed.machine
  BinaryWordAddition.machine StackMachineComposition.leftKey StackMachineComposition.rightKey
abbrev target := GraphAddressAddition.machine

def table : {instructions : target.Λ → target.Stmt // instructions = target.m} := by
  extract_rule_program target.m
def body := table.val
theorem body_exact : body = target.m := table.property

def keyEquality : DecidableEq target.K := by claim_program_key_equality
local instance : DecidableEq target.K := keyEquality

def registerEquality : DecidableEq target.σ := by claim_program_key_equality

def step := @TM2.step target.K target.Γ target.Λ target.σ keyEquality body

theorem step_exact : step = target.step := by
  unfold step
  rw [show keyEquality = target.kDecidableEq from Subsingleton.elim _ _,body_exact]
  rfl

def inputKey : target.K := by normalize_rule_program target.k₀
def resultKey : target.K := by normalize_rule_program target.k₁
def registers : target.σ := by normalize_rule_program target.initialState
def mainLabel : target.Λ := by normalize_rule_program target.main

def initial (word : List (Option Alphabet)) : target.Cfg where
  l := some mainLabel
  var := registers
  stk key := if same : key = inputKey then by cases same; exact word else []

theorem initial_exact (word : List (Option Alphabet)) : initial word = initList target word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key = inputKey
  · subst key
    have original : inputKey = target.k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key ≠ target.k₀ := same
    simp only [dif_neg same,dif_neg original]

def keys : List target.K := by claim_program_keys
local instance : BEq target.K := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K := target.kFin

theorem all_keys : ∀ key : target.K, key ∈ keys := by decide +kernel

theorem keys_nodup : keys.Nodup := by decide +kernel

open StackMachineRegisters.StackSnapshot

def refresh (state : target.Cfg) : target.Cfg :=
  let cells := snapshot target.Γ state.stk keys
  {state with stk := fun key => lookup target.Γ cells key}

theorem refresh_exact (state : target.Cfg) : refresh state = state := by
  cases state with
  | mk label savedRegisters contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot target.Γ contents keys key (all_keys key)


def periodicRefresh (period used : Nat) (state : target.Cfg) : target.Cfg :=
  if used % period == 0 then refresh state else state

theorem periodicRefresh_exact (period used : Nat) (state : target.Cfg) :
    periodicRefresh period used state = state := by
  unfold periodicRefresh
  split <;> simp only [refresh_exact]

def run (period : Nat) : Nat → Nat → target.Cfg → Option (Nat × target.Cfg)
  | 0, _, _ => none
  | fuel+1, used, state =>
    if state.l.isNone then some (used,state)
    else match step state with
      | none => none
      | some next => run period fuel (used+1) (periodicRefresh period (used+1) next)


theorem run_actual (period fuel used : Nat) (before : target.Cfg)
    {count : Nat} {after : target.Cfg}
    (completed : run period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime target.step before (some after) (count-used),
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
      exact ⟨StateTransition.EvalsToInTime.refl target.step before,rfl⟩
    · cases advanced : step before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some next =>
        simp only [advanced] at completed
        rw [periodicRefresh_exact] at completed
        rcases ih (used+1) next completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        have original : target.step before = some next := by
          rw [← step_exact]
          exact advanced
        let first : StateTransition.EvalsToInTime target.step before (some next) 1 :=
          ⟨⟨1,by change (some before).bind target.step = some next; exact original⟩,le_rfl⟩
        have relative : count-used = (count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans target.step 1 (count-(used+1))
          before next (some after) first tail,?_⟩
        change tail.steps+first.steps = (count-(used+1))+1
        rw [tailCount]


end Mettapedia.Languages.HOLLight.GraphAddressAddition.Program

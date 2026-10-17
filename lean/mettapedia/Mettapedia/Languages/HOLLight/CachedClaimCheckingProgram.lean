import Mettapedia.Languages.HOLLight.ClaimCheckingProgram
import Mettapedia.Languages.HOLLight.CachedClaimChecking
/-!
# Computed instructions for original cached source-claim checking

The executable table retains both original physical cache tables, the query
and independent source goal. Each recovered block is equal to the original
machine instruction table; computed endpoint literals avoid evaluating
bundled finiteness metadata during execution.

The evaluator counts original transitions. Fuel and snapshot period are
caller parameters, and snapshots preserve the complete configuration.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.CachedClaimCheckingProgram
open Turing
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight Mettapedia.Languages.OpenTheory
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open CachedClaimChecking
abbrev Alphabet := CachedClaimChecking.Alphabet

attribute [local reducible] FinTM2.Cfg
 CachedClaimChecking.machine CachedClaimChecking.lookupMachine CachedClaimChecking.retainedMachine
 CachedClaimChecking.successMachine CachedClaimChecking.guardedMachine CachedClaimChecking.checkMachine
 RetainedWordExecution.WithOutput.Framed.machine RetainedWordExecution.WithOutput.Framed.taggedMachine
 RetainedWordExecution.WithOutput.Framed.retainedMachine RetainedWordExecution.WithOutput.Framed.untag
 RetainedWordExecution.WithOutput.machine
 StackMachineComposition.machine StackMachineComposition.Dispatch.machine
 FramedFieldSelection.machine Indexed.machine Indexed.Alphabet WordHomomorphismMachine.machine
 WordTemplateMachine.machine ChainedCache.machine ChainedCache.firstMachine ChainedCache.secondMachine
 ChainedCache.guardedMachine ChainedCache.preparedMachine ChainedCache.taggedMachine
 ChainedCache.retainedMachine Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine EncodedTable.decodedMachine Triples.Recovery.machine

attribute [local reducible] FinTM2.Cfg ClaimCheckingMachine.machine ClaimCheckingMachine.guardedMachine ClaimCheckingMachine.successMachine ClaimCheckingMachine.preparedMachine
 ClaimCheckingMachine.claimedMachine ClaimCheckingMachine.selectedClaimMachine ClaimCheckingMachine.claimMachine ClaimCheckingMachine.sequentMachine ClaimCheckingMachine.selectedSequentMachine ClaimCheckingMachine.projectedMachine
 ClaimCheckingMachine.Comparison.machine ClaimCheckingMachine.Comparison.compareMachine
 SourceQuantifierEmission.renderMachine SourceQuantifierEmission.rawMachine
 SourceQuantifierEmission.stripStatus SourceQuantifierEmission.rawIdentity
 SourceQuantifierEmission.selectedScopeMachine SourceQuantifierEmission.savedScopeMachine
 SourceQuantifierEmission.admissionMachine
 StackMachineComposition.machine StackMachineComposition.Dispatch.machine
 StackMachineComposition.liftFirst StackMachineComposition.liftSecond StackMachineComposition.Dispatch.lift
 RetainedWordExecution.machine RetainedWordExecution.statement RetainedWordExecution.body
 RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.statement
 RetainedWordExecution.WithOutput.body
 WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine Indexed.Alphabet WordEqualityMachine.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.PrefixField.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.projectedMachine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.VisitorAdapter.machine
 Mettapedia.GSLT.LanguageDef.PatternScopeExecution.Binary.machine
 Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.machine
 ArgumentRenderingMachine.Full.machine ArgumentRenderingMachine.Routing.Pipeline.machine
 ArgumentRenderingMachine.Routing.Traversal.machine ArgumentRenderingMachine.Routing.machine
 Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Hooks.Execution.machine ArgumentRenderingMachine.Execution.machine
 RetainedWordExecution.WithOutput.Framed.untag
 StackMachineComposition.leftKey StackMachineComposition.rightKey


local instance : Fintype Alphabet := ClaimCheckingProgram.alphabet0Finite
local instance : Inhabited Alphabet := ClaimCheckingProgram.alphabet0Default
local instance : Fintype (Option Alphabet) := ClaimCheckingProgram.alphabet1Finite
local instance : Inhabited (Option Alphabet) := ClaimCheckingProgram.alphabet1Default
local instance : Fintype (Option (Option Alphabet)) := ClaimCheckingProgram.alphabet2Finite
local instance : Inhabited (Option (Option Alphabet)) := ClaimCheckingProgram.alphabet2Default
local instance : Fintype (Option Alphabet ⊕ Alphabet) := ClaimCheckingProgram.alphabet3Finite
local instance : Inhabited (Option Alphabet ⊕ Alphabet) := ClaimCheckingProgram.alphabet3Default

private theorem sequence_exact (first second : FinTM2)
    [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
    (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {firstBody : first.Λ → first.Stmt} {secondBody : second.Λ → second.Stmt}
    (firstSame : firstBody = first.m) (secondSame : secondBody = second.m) :
    StackMachineComposition.Programs.body first.k₁ second.k₀ second.main default bridge firstBody secondBody =
      (StackMachineComposition.machine first second bridge).m := by
  cases firstSame
  cases secondSame
  exact StackMachineComposition.body_eq first second bridge

abbrev target := CachedClaimChecking.machine

def framedBody {arity : Nat} (indices : List (Fin arity)) :
    (FramedFieldSelection.machine (Γ:=Alphabet) indices).Λ →
    (FramedFieldSelection.machine (Γ:=Alphabet) indices).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FirstAlphabet := (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))).Γ)
    (SecondAlphabet := (Indexed.machine (FramedFieldSelection.template (Γ:=Alphabet) indices)).Γ)
    WordHomomorphismMachine.Stack.result Indexed.Stack.input (Indexed.Phase.emit 0)
    (none : Option (Option Alphabet)) id
    (WordHomomorphismMachine.program FramedFieldSelection.liftSymbol)
    (Indexed.program (FramedFieldSelection.template indices)))
theorem framedBody_exact {arity : Nat} (indices : List (Fin arity)) :
    framedBody indices = (FramedFieldSelection.machine (Γ:=Alphabet) indices).m :=
  StackMachineComposition.body_eq
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet)))
    (Indexed.machine (FramedFieldSelection.template indices)) (Equiv.refl _)

local instance : Fintype (selection.Γ selection.k₁) := ClaimCheckingProgram.alphabet1Finite
local instance : Inhabited (selection.Γ selection.k₁) := ClaimCheckingProgram.alphabet1Default

def lookupBody : lookupMachine.Λ → lookupMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    selection.k₁ ChainedCache.machine.k₀ ChainedCache.machine.main (none : Option Alphabet) id
    (framedBody cacheIndices) ChainedCache.program)
theorem lookupBody_exact : lookupBody = lookupMachine.m :=
  sequence_exact selection ChainedCache.machine (Equiv.refl _)
    (framedBody_exact cacheIndices) ChainedCache.program_exact

local instance : Inhabited (lookupMachine.Γ lookupMachine.k₀) := by
  change Inhabited (Option Alphabet); exact ClaimCheckingProgram.alphabet1Default
local instance : Fintype (lookupMachine.Γ lookupMachine.k₁) := by
  change Fintype Alphabet; exact ClaimCheckingProgram.alphabet0Finite
local instance : Inhabited (lookupMachine.Γ lookupMachine.k₁) := by
  change Inhabited Alphabet; exact ClaimCheckingProgram.alphabet0Default

abbrev savedLookup := RetainedWordExecution.WithOutput.machine lookupMachine

def savedLookupBody : savedLookup.Λ → savedLookup.Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    lookupMachine.k₀ lookupMachine.k₁ (none : Option Alphabet) (0 : Alphabet)
    lookupMachine.initialState lookupMachine.main lookupBody)
theorem savedLookupBody_exact : savedLookupBody = savedLookup.m := by
  unfold savedLookupBody
  rw [lookupBody_exact]
  rfl

abbrev originalUntag := RetainedWordExecution.WithOutput.Framed.untag lookupMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
abbrev taggedLookup := RetainedWordExecution.WithOutput.Framed.taggedMachine lookupMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

local instance : Fintype (savedLookup.Γ savedLookup.k₁) := by
  change Fintype (Option Alphabet ⊕ Alphabet); exact ClaimCheckingProgram.alphabet3Finite
local instance : Inhabited (savedLookup.Γ savedLookup.k₁) := by
  change Inhabited (Option Alphabet ⊕ Alphabet); exact ClaimCheckingProgram.alphabet3Default

def taggedLookupBody : taggedLookup.Λ → taggedLookup.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    savedLookup.k₁ (WordHomomorphismMachine.machine originalUntag).k₀
    (WordHomomorphismMachine.machine originalUntag).main (default : Option Alphabet ⊕ Alphabet) id
    savedLookupBody (WordHomomorphismMachine.program originalUntag))
theorem taggedLookupBody_exact : taggedLookupBody = taggedLookup.m :=
  sequence_exact savedLookup (WordHomomorphismMachine.machine originalUntag) (Equiv.refl _)
    savedLookupBody_exact rfl

local instance taggedFinite : Fintype (taggedLookup.Γ taggedLookup.k₁) := by
  change Fintype (Option Alphabet); exact ClaimCheckingProgram.alphabet1Finite
local instance taggedDefault : Inhabited (taggedLookup.Γ taggedLookup.k₁) := by
  change Inhabited (Option Alphabet); exact ClaimCheckingProgram.alphabet1Default

def retainedBody : retainedMachine.Λ → retainedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    taggedLookup.k₁ (WordTemplateMachine.machine
      (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))).k₀
    (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))).main
    (none : Option Alphabet) id taggedLookupBody
    (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet))))
theorem retainedBody_exact : retainedBody = retainedMachine.m :=
  @sequence_exact taggedLookup
    (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet)))
    taggedFinite taggedDefault (Equiv.refl _) taggedLookupBody
    (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet)))
    taggedLookupBody_exact rfl

local instance : Fintype (reverseMachine.Γ reverseMachine.k₁) := by
  change Fintype (Option Alphabet); exact ClaimCheckingProgram.alphabet1Finite
local instance : Inhabited (reverseMachine.Γ reverseMachine.k₁) := by
  change Inhabited (Option Alphabet); exact ClaimCheckingProgram.alphabet1Default

def successBody : CachedClaimChecking.successMachine.Λ → CachedClaimChecking.successMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    reverseMachine.k₁ ClaimCheckingMachine.machine.k₀ ClaimCheckingProgram.mainLabel
    (none : Option Alphabet) id (framedBody reverseIndices) ClaimCheckingProgram.body)
theorem successBody_exact : successBody = CachedClaimChecking.successMachine.m :=
  sequence_exact reverseMachine ClaimCheckingMachine.machine (Equiv.refl _)
    (framedBody_exact reverseIndices) ClaimCheckingProgram.body_exact

private theorem dispatch_lift (statement : CachedClaimChecking.successMachine.Stmt) :
    StackMachineComposition.Dispatch.lift CachedClaimChecking.successMachine statement =
      StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run statement := by
  induction statement <;> simp_all only [StackMachineComposition.Dispatch.lift,StackMachineRegisters.extend]

def guardedBody (phase : CachedClaimChecking.guardedMachine.Λ) : CachedClaimChecking.guardedMachine.Stmt := by
  claim_program_literal_endpoints (match phase with
  | .run label => StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run (successBody label)
  | .read => TM2.Stmt.pop CachedClaimChecking.successMachine.k₀ (fun state value => (state.1,value))
      (TM2.Stmt.branch (fun state => state.2.any CachedClaimChecking.accept)
        (TM2.Stmt.load (fun state => (state.1,none))
          (TM2.Stmt.goto fun _ => .run CachedClaimChecking.successMachine.main))
        (TM2.Stmt.goto fun _ => .discard))
  | .discard => TM2.Stmt.pop CachedClaimChecking.successMachine.k₀ (fun state value => (state.1,value))
      (TM2.Stmt.branch (fun state => state.2.isSome) (TM2.Stmt.goto fun _ => .discard)
        (TM2.Stmt.push CachedClaimChecking.successMachine.k₁ (fun _ => false)
          (TM2.Stmt.load (fun _ => (CachedClaimChecking.successMachine.initialState,none)) TM2.Stmt.halt))))
theorem guardedBody_exact : guardedBody = CachedClaimChecking.guardedMachine.m := by
  funext phase
  cases phase with
  | read => rfl
  | discard => rfl
  | run label =>
    change StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run (successBody label) =
      StackMachineComposition.Dispatch.lift CachedClaimChecking.successMachine
        (CachedClaimChecking.successMachine.m label)
    exact (congrArg (StackMachineRegisters.extend StackMachineComposition.Dispatch.Phase.run)
      (congrFun successBody_exact label)).trans (dispatch_lift _).symm

local instance : Fintype (guardSelection.Γ guardSelection.k₁) := by
  change Fintype (Option Alphabet); exact ClaimCheckingProgram.alphabet1Finite
local instance : Inhabited (guardSelection.Γ guardSelection.k₁) := by
  change Inhabited (Option Alphabet); exact ClaimCheckingProgram.alphabet1Default

def checkBody : checkMachine.Λ → checkMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    guardSelection.k₁ CachedClaimChecking.guardedMachine.k₀ CachedClaimChecking.guardedMachine.main
    (none : Option Alphabet) id (framedBody guardIndices) guardedBody)
theorem checkBody_exact : checkBody = checkMachine.m :=
  sequence_exact guardSelection CachedClaimChecking.guardedMachine (Equiv.refl _)
    (framedBody_exact guardIndices) guardedBody_exact

local instance retainedFinite : Fintype (retainedMachine.Γ retainedMachine.k₁) := by
  change Fintype (Option Alphabet); exact ClaimCheckingProgram.alphabet1Finite
local instance retainedDefault : Inhabited (retainedMachine.Γ retainedMachine.k₁) := by
  change Inhabited (Option Alphabet); exact ClaimCheckingProgram.alphabet1Default

def body : target.Λ → target.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    retainedMachine.k₁ checkMachine.k₀ checkMachine.main (none : Option Alphabet) id
    retainedBody checkBody)
theorem body_exact : body = target.m :=
  @sequence_exact retainedMachine checkMachine retainedFinite retainedDefault
    (Equiv.refl _) retainedBody checkBody retainedBody_exact checkBody_exact


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
  stk key := if same : key=inputKey then by cases same; exact word else []
theorem initial_exact (word : List (Option Alphabet)) : initial word = initList target word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key=inputKey
  · subst key
    have original : inputKey=target.k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key≠target.k₀ := same
    simp only [dif_neg same,dif_neg original]

def keys : List target.K := by claim_program_keys
local instance : BEq target.K := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K := target.kFin

theorem all_keys : ∀ key : target.K, key∈keys := by decide +kernel
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


end Mettapedia.Languages.HOLLight.CachedClaimCheckingProgram

import Mettapedia.Computability.BinaryListAppend
import Mettapedia.Computability.RetainedWordProgram
import Mettapedia.Computability.StackMachineDispatchProgram

/-!
# Original binary list append through physical instruction tables

The whole table uses literal physical endpoints and registers with the original
selector, suffix check, retention, framing and status dispatch. Its step and
initialization equal the original machine. Explicit stack keys support complete
cleanup checks without enumerating register values. Completed codec-image runs
have the original exact word, canonical halt state and linear clock bound.
The contract concerns codec images; checking arbitrary list bodies is separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.BinaryListAppend.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
attribute [local implicit_reducible] BinaryListAppend.machine checkedSuffixMachine statusMachine
  identityMachine stripMachine rawStemMachine retainedMachine payloadMachine guardMachine restoredBody dispatchMachine
  FramedFieldSelection.machine WordHomomorphismMachine.machine Indexed.machine WordTemplateMachine.machine
  StackMachineComposition.machine StackMachineComposition.Dispatch.machine RetainedWordExecution.machine
  RetainedWordExecution.WithOutput.machine
  FramedWordSuffixRemoval.machine

local instance : Fintype ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))).Γ
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance : Inhabited ((WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))).Γ
    (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
local instance : Fintype ((WordHomomorphismMachine.machine restoreImage).Γ
    (WordHomomorphismMachine.machine restoreImage).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine restoreImage).Γ
    (WordHomomorphismMachine.machine restoreImage).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype ((FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).Γ
    (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).Γ
    (FramedFieldSelection.machine (Γ:=Alphabet) firstSelector).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (checkedSuffixMachine.Γ checkedSuffixMachine.k₁) := inferInstanceAs (Fintype SuffixCell)
local instance : Inhabited (checkedSuffixMachine.Γ checkedSuffixMachine.k₁) := ⟨.inr false⟩
local instance : Fintype (statusMachine.Γ statusMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (statusMachine.Γ statusMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (statusMachine.Γ statusMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (rawStemMachine.Γ rawStemMachine.k₀) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Fintype (rawStemMachine.Γ rawStemMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (rawStemMachine.Γ rawStemMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (rawStemMachine.Γ rawStemMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (payloadMachine.Γ payloadMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (payloadMachine.Γ payloadMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Fintype (guardMachine.Γ guardMachine.k₁) := inferInstanceAs (Fintype GuardCell)
local instance : Inhabited (guardMachine.Γ guardMachine.k₁) := ⟨.inr false⟩
local instance : Fintype (restoredBody.Γ restoredBody.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (restoredBody.Γ restoredBody.k₀) := ⟨.inr false⟩
local instance : Inhabited (restoredBody.Γ restoredBody.k₁) := inferInstanceAs (Inhabited Alphabet)

abbrev selected := FramedFieldSelection.machine (Γ:=Alphabet) firstSelector
abbrev retainedCore := RetainedWordExecution.WithOutput.machine rawStemMachine
local instance : Fintype (retainedCore.Γ retainedCore.k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance : Inhabited (retainedCore.Γ retainedCore.k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))
abbrev retainedTagged := RetainedWordExecution.WithOutput.Framed.taggedMachine rawStemMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
local instance : Fintype (retainedTagged.Γ retainedTagged.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedTagged.Γ retainedTagged.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
abbrev closeWord := RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=Alphabet)
abbrev retainedUntag := RetainedWordExecution.WithOutput.Framed.untag rawStemMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

abbrev selectedInput : selected.K := some (.inl WordHomomorphismMachine.Stack.input)
abbrev selectedResult : selected.K := some (.inr Indexed.Stack.result)
def selectedRegisters : selected.σ := ((none,none),none,none)
abbrev selectedMain : selected.Λ := .inl .read

def selectBody : selected.Λ → selected.Stmt :=
  StackMachineComposition.Programs.body WordHomomorphismMachine.Stack.result Indexed.Stack.input
    (.emit ⟨0,Nat.zero_lt_succ _⟩) (none : Option (Option Alphabet)) id
    (WordHomomorphismMachine.program (FramedFieldSelection.liftSymbol (Γ:=Alphabet)))
    (Indexed.arrayProgram (FramedFieldSelection.template (Γ:=Alphabet) firstSelector).length
      (FramedFieldSelection.template (Γ:=Alphabet) firstSelector).toArray)
theorem selectBody_eq : selectBody=selected.m := by
  unfold selectBody
  rw [Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq (WordHomomorphismMachine.machine (FramedFieldSelection.liftSymbol (Γ:=Alphabet))) (Indexed.machine (FramedFieldSelection.template (Γ:=Alphabet) firstSelector)) (Equiv.refl (Option (Option Alphabet)))

abbrev checkedInput : checkedSuffixMachine.K := some (.inl selectedInput)
abbrev checkedResult : checkedSuffixMachine.K := some (.inr FramedWordSuffixRemoval.Stack.result)
def checkedRegisters : checkedSuffixMachine.σ := (selectedRegisters,(none,none,none,none),none)
abbrev checkedMain : checkedSuffixMachine.Λ := .inl selectedMain

def checkedBody : checkedSuffixMachine.Λ → checkedSuffixMachine.Stmt :=
  StackMachineComposition.Programs.body selectedResult FramedWordSuffixRemoval.Stack.input .read
    (none : Option Alphabet) id selectBody (FramedWordSuffixRemoval.program (3 : Alphabet) 2)
theorem checkedBody_eq : checkedBody=checkedSuffixMachine.m := by
  unfold checkedBody
  rw [selectBody_eq]
  exact StackMachineComposition.body_eq selected (FramedWordSuffixRemoval.machine (3 : Alphabet) 2) (Equiv.refl (Option Alphabet))

abbrev statusInput : statusMachine.K := some (.inl checkedInput)
abbrev statusResult : statusMachine.K := some (.inr WordHomomorphismMachine.Stack.result)
def statusRegisters : statusMachine.σ := (checkedRegisters,(none,none),none)
abbrev statusMain : statusMachine.Λ := .inl checkedMain

def statusBody : statusMachine.Λ → statusMachine.Stmt :=
  StackMachineComposition.Programs.body checkedResult WordHomomorphismMachine.Stack.input .read
    (.inr false : SuffixCell) id checkedBody (WordHomomorphismMachine.program statusImage)
theorem statusBody_eq : statusBody=statusMachine.m := by
  unfold statusBody
  rw [checkedBody_eq]
  exact StackMachineComposition.body_eq checkedSuffixMachine (WordHomomorphismMachine.machine statusImage) (Equiv.refl SuffixCell)

def stripBody : stripMachine.Λ → stripMachine.Stmt :=
  StackMachineComposition.Dispatch.Programs.body WordHomomorphismMachine.Stack.input
    WordHomomorphismMachine.Stack.result (none,none) .read acceptStatus []
    (WordHomomorphismMachine.program (fun symbol : Alphabet => [symbol]))
theorem stripBody_eq : stripBody=stripMachine.m := by
  exact (StackMachineComposition.Dispatch.Programs.body_eq identityMachine acceptStatus []).symm

abbrev rawInput : rawStemMachine.K := some (.inl statusInput)
abbrev rawResult : rawStemMachine.K := some (.inr WordHomomorphismMachine.Stack.result)
def rawRegisters : rawStemMachine.σ := (statusRegisters,((none,none),none),none)
abbrev rawMain : rawStemMachine.Λ := .inl statusMain

def rawBody : rawStemMachine.Λ → rawStemMachine.Stmt :=
  StackMachineComposition.Programs.body statusResult WordHomomorphismMachine.Stack.input .read
    (0 : Alphabet) id statusBody stripBody
theorem rawBody_eq : rawBody=rawStemMachine.m := by
  unfold rawBody
  rw [statusBody_eq,stripBody_eq]
  exact StackMachineComposition.body_eq statusMachine stripMachine (Equiv.refl Alphabet)

def retainedCoreBody : retainedCore.Λ → retainedCore.Stmt :=
  RetainedWordExecution.WithOutput.Programs.statement rawInput rawResult (none : Option Alphabet)
    (0 : Alphabet) rawRegisters rawMain rawBody
theorem retainedCoreBody_eq : retainedCoreBody=retainedCore.m := by
  unfold retainedCoreBody
  rw [rawBody_eq]
  rfl

def taggedBody : retainedTagged.Λ → retainedTagged.Stmt :=
  StackMachineComposition.Programs.body (FirstAlphabet:=retainedCore.Γ) none
    WordHomomorphismMachine.Stack.input .read (.inr (0 : Alphabet) : Option Alphabet ⊕ Alphabet) id
    retainedCoreBody (WordHomomorphismMachine.program retainedUntag)
theorem taggedBody_eq : taggedBody=retainedTagged.m := by
  unfold taggedBody
  rw [retainedCoreBody_eq]
  exact StackMachineComposition.body_eq retainedCore (WordHomomorphismMachine.machine retainedUntag) (Equiv.refl (Option Alphabet ⊕ Alphabet))

abbrev retainedInput : retainedMachine.K :=
  some (.inl (some (.inl (some (some (some (some rawInput)))))))
abbrev retainedResult : retainedMachine.K := some (.inr WordTemplateMachine.Stack.input)
def retainedRegisters : retainedMachine.σ := (((rawRegisters,none,none),(none,none),none),none,none)
abbrev retainedMain : retainedMachine.Λ := .inl (.inl .scan)

def framedBody : retainedMachine.Λ → retainedMachine.Stmt :=
  StackMachineComposition.Programs.body (FirstAlphabet:=retainedTagged.Γ) (some (.inr WordHomomorphismMachine.Stack.result))
    WordTemplateMachine.Stack.input (.emit ⟨0,Nat.zero_lt_succ _⟩) (none : Option Alphabet) id
    taggedBody (WordTemplateMachine.program closeWord)
theorem framedBody_eq : framedBody=retainedMachine.m := by
  unfold framedBody
  rw [taggedBody_eq]
  exact StackMachineComposition.body_eq retainedTagged (WordTemplateMachine.machine closeWord) (Equiv.refl (Option Alphabet))

abbrev payloadInput : payloadMachine.K := some (.inl retainedInput)
abbrev payloadResult : payloadMachine.K := some (.inr Indexed.Stack.result)
def payloadRegisters : payloadMachine.σ := (retainedRegisters,none,none)
abbrev payloadMain : payloadMachine.Λ := .inl retainedMain

def payloadBody : payloadMachine.Λ → payloadMachine.Stmt :=
  StackMachineComposition.Programs.body retainedResult Indexed.Stack.input
    (.emit ⟨0,Nat.zero_lt_succ _⟩) (none : Option Alphabet) id framedBody
    (Indexed.arrayProgram appendPlan.length appendPlan.toArray)
theorem payloadBody_eq : payloadBody=payloadMachine.m := by
  unfold payloadBody
  rw [framedBody_eq,Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq retainedMachine (Indexed.machine appendPlan) (Equiv.refl (Option Alphabet))

abbrev restoredInput : restoredBody.K := some (.inl WordHomomorphismMachine.Stack.input)
abbrev restoredResult : restoredBody.K := some (.inr payloadResult)
def restoredRegisters : restoredBody.σ := ((none,none),payloadRegisters,none)
abbrev restoredMain : restoredBody.Λ := .inl .read

def restoredTable : restoredBody.Λ → restoredBody.Stmt :=
  StackMachineComposition.Programs.body WordHomomorphismMachine.Stack.result payloadInput payloadMain
    (none : Option Alphabet) id (WordHomomorphismMachine.program restoreImage) payloadBody
theorem restoredTable_eq : restoredTable=restoredBody.m := by
  unfold restoredTable
  rw [payloadBody_eq]
  exact StackMachineComposition.body_eq (WordHomomorphismMachine.machine restoreImage) payloadMachine (Equiv.refl (Option Alphabet))

def dispatchBody : dispatchMachine.Λ → dispatchMachine.Stmt :=
  StackMachineComposition.Dispatch.Programs.body restoredInput restoredResult restoredRegisters
    restoredMain acceptGuard [(0 : Alphabet)] restoredTable
theorem dispatchBody_eq : dispatchBody=dispatchMachine.m := by
  unfold dispatchBody
  rw [restoredTable_eq]
  exact (StackMachineComposition.Dispatch.Programs.body_eq restoredBody acceptGuard [(0 : Alphabet)]).symm

abbrev guardInput : guardMachine.K := some (some (some statusInput))
abbrev guardResult : guardMachine.K := none
def guardRegisters : guardMachine.σ := (statusRegisters,none,none,false)
abbrev guardMain : guardMachine.Λ := .scan

def guardBody : guardMachine.Λ → guardMachine.Stmt :=
  RetainedWordExecution.Programs.body statusInput statusResult statusRegisters statusMain
    (none : Option Alphabet) false acceptStatus statusBody
theorem guardBody_eq : guardBody=guardMachine.m := by
  unfold guardBody
  rw [statusBody_eq]
  exact RetainedWordExecution.Programs.body_eq statusMachine acceptStatus

abbrev target := BinaryListAppend.machine

def body : target.Λ → target.Stmt :=
  StackMachineComposition.Programs.body guardResult restoredInput .read
    (.inr false : GuardCell) id guardBody dispatchBody
theorem body_eq : body=target.m := by
  unfold body
  rw [guardBody_eq,dispatchBody_eq]
  exact StackMachineComposition.body_eq guardMachine dispatchMachine (Equiv.refl GuardCell)

abbrev inputKey : target.K := some (.inl guardInput)
abbrev resultKey : target.K := some (.inr restoredResult)
def registers : target.σ := (guardRegisters,(restoredRegisters,none),none)
abbrev mainLabel : target.Λ := .inl .scan
theorem registers_eq : registers=target.initialState := rfl


open Lean Elab Tactic Meta in
private partial def literalEquality (type : Expr) : MetaM Expr := do
  let type ← withTransparency .all (whnf type)
  match type.getAppFn.constName?,type.getAppArgs.toList with
  | some ``Option,[child] =>
    mkAppOptM ``Option.instDecidableEq #[some child,some (← literalEquality child)]
  | some ``Prod,[left,right] =>
    mkAppOptM `instDecidableEqProd #[some left,some right,
      some (← literalEquality left),some (← literalEquality right)]
  | some ``Sum,[left,right] =>
    mkAppOptM ``instDecidableEqSum #[some left,some right,
      some (← literalEquality left),some (← literalEquality right)]
  | some ``RetainedWordExecution.Phase,[inner] =>
    mkAppOptM ``RetainedWordExecution.instDecidableEqPhase #[some inner,some (← literalEquality inner)]
  | some ``RetainedWordExecution.WithOutput.Phase,[inner] =>
    mkAppOptM ``RetainedWordExecution.WithOutput.instDecidableEqPhase #[some inner,some (← literalEquality inner)]
  | some ``StackMachineComposition.Dispatch.Phase,[inner] =>
    mkAppOptM ``StackMachineComposition.Dispatch.instDecidableEqPhase #[some inner,some (← literalEquality inner)]
  | _,_ =>
    let literal ← withTransparency .all (reduce type false false true)
    synthInstance (← mkAppM ``DecidableEq #[literal])

open Lean Elab Tactic Meta in
elab "append_literal_equality" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    goal.assign (← literalEquality (← goal.getType).getAppArgs.back!)
  replaceMainGoal []

def keyEquality : DecidableEq target.K := by append_literal_equality
local instance : DecidableEq target.K := keyEquality
def registerEquality : DecidableEq target.σ := by append_literal_equality

abbrev SelectLabels := WordHomomorphismMachine.Phase 6 ⊕ Bool ⊕ Indexed.Phase 2 2
abbrev CheckedLabels := SelectLabels ⊕ Bool ⊕ FramedWordSuffixRemoval.Phase
abbrev StatusLabels := CheckedLabels ⊕ Bool ⊕ WordHomomorphismMachine.Phase 7
abbrev RawLabels := StatusLabels ⊕ Bool ⊕ StackMachineComposition.Dispatch.Phase (WordHomomorphismMachine.Phase 5)
abbrev TaggedLabels := RetainedWordExecution.WithOutput.Phase RawLabels ⊕ Bool ⊕ WordHomomorphismMachine.Phase 11
abbrev FramedLabels := TaggedLabels ⊕ Bool ⊕ WordTemplateMachine.Phase 2
abbrev PayloadLabels := FramedLabels ⊕ Bool ⊕ Indexed.Phase 3 3
abbrev RestoredLabels := WordHomomorphismMachine.Phase 6 ⊕ Bool ⊕ PayloadLabels
def labelEquality : DecidableEq target.Λ := by
  change DecidableEq (RetainedWordExecution.Phase StatusLabels ⊕ Bool ⊕
    StackMachineComposition.Dispatch.Phase RestoredLabels)
  append_literal_equality

def step := @TM2.step target.K target.Γ target.Λ target.σ keyEquality body
theorem step_eq : step=target.step := by
  unfold step
  rw [show keyEquality=target.kDecidableEq from Subsingleton.elim _ _]
  rw [body_eq]
  rfl

def initial (word : List (Option Alphabet)) : target.Cfg where
  l := some mainLabel
  var := registers
  stk key := @dite (List (target.Γ key)) (key=inputKey) (keyEquality key inputKey)
    (fun same => same.symm ▸ word) (fun _ => [])
theorem initial_eq (word : List (Option Alphabet)) : initial word=initList target word := by
  have sameEquality : keyEquality=target.kDecidableEq := Subsingleton.elim _ _
  unfold initial
  rw [sameEquality,registers_eq]
  unfold initList
  congr 1
  funext key
  by_cases same : key=inputKey
  · subst key
    simp [show inputKey=target.k₀ from rfl]
  · have different : key≠target.k₀ := same
    simp only [dif_neg same,dif_neg different]

private def joinedKeys {Left Right : Type} (left : List Left) (right : List Right) :
    List (Option (Left ⊕ Right)) := none::(left.map (some ∘ Sum.inl)++right.map (some ∘ Sum.inr))
private theorem joinedKeys_complete {Left Right : Type} (left : List Left) (right : List Right)
    (allLeft : ∀ key,key∈left) (allRight : ∀ key,key∈right) : ∀ key,key∈joinedKeys left right := by
  intro key
  cases key with
  | none => simp [joinedKeys]
  | some key =>
    cases key with
    | inl key =>
      unfold joinedKeys
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      exact List.mem_map_of_mem (allLeft key)
    | inr key =>
      unfold joinedKeys
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      exact List.mem_map_of_mem (allRight key)

private def homKeys : List WordHomomorphismMachine.Stack := [.input,.output,.result]
private theorem homKeys_complete : ∀ key,key∈homKeys := by intro key; cases key <;> simp [homKeys]
private def indexedKeys : List Indexed.Stack := [.input,.result,.output,.temporary]
private theorem indexedKeys_complete : ∀ key,key∈indexedKeys := by intro key; cases key <;> simp [indexedKeys]
private def suffixKeys : List FramedWordSuffixRemoval.Stack := [.input,.output,.result]
private theorem suffixKeys_complete : ∀ key,key∈suffixKeys := by intro key; cases key <;> simp [suffixKeys]
private def templateKeys : List WordTemplateMachine.Stack := [.input,.temporary,.output]
private theorem templateKeys_complete : ∀ key,key∈templateKeys := by intro key; cases key <;> simp [templateKeys]

def selectedKeys : List selected.K := joinedKeys homKeys indexedKeys
private theorem selectedKeys_complete : ∀ key,key∈selectedKeys := joinedKeys_complete _ _ homKeys_complete indexedKeys_complete
def checkedKeys : List checkedSuffixMachine.K := joinedKeys selectedKeys suffixKeys
private theorem checkedKeys_complete : ∀ key,key∈checkedKeys := joinedKeys_complete _ _ selectedKeys_complete suffixKeys_complete
def statusKeys : List statusMachine.K := joinedKeys checkedKeys homKeys
private theorem statusKeys_complete : ∀ key,key∈statusKeys := joinedKeys_complete _ _ checkedKeys_complete homKeys_complete
def rawKeys : List rawStemMachine.K := joinedKeys statusKeys homKeys
private theorem rawKeys_complete : ∀ key,key∈rawKeys := joinedKeys_complete _ _ statusKeys_complete homKeys_complete
def retainedCoreKeys : List retainedCore.K := [none,some none,some (some none),some (some (some none))]++
  rawKeys.map (some ∘ some ∘ some ∘ some)
private theorem retainedCoreKeys_complete : ∀ key,key∈retainedCoreKeys := by
  intro key
  rcases key with _ | (_ | (_ | (_ | key))) <;> simp [retainedCoreKeys,rawKeys_complete]
def taggedKeys : List retainedTagged.K := joinedKeys retainedCoreKeys homKeys
private theorem taggedKeys_complete : ∀ key,key∈taggedKeys := joinedKeys_complete _ _ retainedCoreKeys_complete homKeys_complete
def retainedKeys : List retainedMachine.K := joinedKeys taggedKeys templateKeys
private theorem retainedKeys_complete : ∀ key,key∈retainedKeys := joinedKeys_complete _ _ taggedKeys_complete templateKeys_complete
def payloadKeys : List payloadMachine.K := joinedKeys retainedKeys indexedKeys
private theorem payloadKeys_complete : ∀ key,key∈payloadKeys := joinedKeys_complete _ _ retainedKeys_complete indexedKeys_complete
def restoredKeys : List restoredBody.K := joinedKeys homKeys payloadKeys
private theorem restoredKeys_complete : ∀ key,key∈restoredKeys := joinedKeys_complete _ _ homKeys_complete payloadKeys_complete
def guardKeys : List guardMachine.K := [none,some none,some (some none)]++statusKeys.map (some ∘ some ∘ some)
private theorem guardKeys_complete : ∀ key,key∈guardKeys := by
  intro key
  rcases key with _ | (_ | (_ | key)) <;> simp [guardKeys,statusKeys_complete]
def keys : List target.K := joinedKeys guardKeys restoredKeys
theorem all_keys : ∀ key,key∈keys := joinedKeys_complete _ _ guardKeys_complete restoredKeys_complete

open StackMachineRegisters.StackSnapshot

def refresh (state : target.Cfg) : target.Cfg :=
  {state with stk := lookup target.Γ (snapshot target.Γ state.stk keys)}
theorem refresh_eq (state : target.Cfg) : refresh state=state := by
  cases state with
  | mk label savedRegisters contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot target.Γ contents keys key (all_keys key)

def periodicRefresh (period used : Nat) (state : target.Cfg) : target.Cfg :=
  if used % period == 0 then refresh state else state
theorem periodicRefresh_eq (period used : Nat) (state : target.Cfg) : periodicRefresh period used state=state := by
  unfold periodicRefresh
  split <;> simp only [refresh_eq]

def run (period : Nat) : Nat → Nat → target.Cfg → Option (Nat × target.Cfg)
  | 0,_,_ => none
  | fuel+1,used,state =>
    if state.l.isNone then some (used,state)
    else match step state with
      | none => none
      | some after => run period fuel (used+1) (periodicRefresh period (used+1) after)

theorem run_actual (period fuel used : Nat) (before : target.Cfg)
    {count : Nat} {after : target.Cfg} (completed : run period fuel used before=some (count,after)) :
    used≤count ∧ (∃ path : StateTransition.EvalsToInTime target.step before (some after) (count-used),
      path.steps=count-used) ∧ after.l=none := by
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
      exact ⟨StateTransition.EvalsToInTime.refl target.step before,rfl⟩
    · cases advanced : step before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some nextState =>
        simp only [advanced,periodicRefresh_eq] at completed
        rcases ih (used+1) nextState completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        let first : StateTransition.EvalsToInTime target.step before (some nextState) 1 :=
          ⟨⟨1,by change (some before).bind target.step=some nextState; simpa only [Option.bind_some,←step_eq] using advanced⟩,le_rfl⟩
        have relative : count-used=(count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans target.step 1 (count-(used+1)) before nextState
          (some after) first tail,?_⟩
        change tail.steps+first.steps=(count-(used+1))+1
        rw [tailCount]

variable {α : Type}

private theorem terminal_compare {Config : Type} (transition : Config → Option Config)
    {before first last : Config} (firstPath : StateTransition.EvalsTo transition before (some first))
    (lastPath : StateTransition.EvalsTo transition before (some last)) (firstHalted : transition first=none)
    (ordered : firstPath.steps≤lastPath.steps) : firstPath.steps=lastPath.steps ∧ first=last := by
  let tick := fun state : Option Config => state.bind transition
  obtain ⟨extra,splitSteps⟩ := Nat.exists_eq_add_of_le ordered
  have splitSteps' : lastPath.steps=extra+firstPath.steps := by omega
  have firstRan : tick^[firstPath.steps] (some before)=some first := firstPath.evals_in_steps
  have lastRan : tick^[lastPath.steps] (some before)=some last := lastPath.evals_in_steps
  rw [splitSteps',Function.iterate_add_apply,firstRan] at lastRan
  cases extra with
  | zero =>
    simp only [Function.iterate_zero_apply,Option.some.injEq] at lastRan
    exact ⟨by omega,lastRan⟩
  | succ extra =>
    rw [Function.iterate_succ_apply] at lastRan
    have stopped : tick (some first)=none := firstHalted
    rw [stopped,Function.iterate_fixed (show tick none=none from rfl) extra] at lastRan
    contradiction

private theorem terminal_paths_unique {Config : Type} (transition : Config → Option Config)
    {before first last : Config} (firstPath : StateTransition.EvalsTo transition before (some first))
    (lastPath : StateTransition.EvalsTo transition before (some last))
    (firstHalted : transition first=none) (lastHalted : transition last=none) :
    firstPath.steps=lastPath.steps ∧ first=last := by
  rcases Nat.le_total firstPath.steps lastPath.steps with ordered | ordered
  · exact terminal_compare transition firstPath lastPath firstHalted ordered
  · rcases terminal_compare transition lastPath firstPath lastHalted ordered with ⟨sameSteps,sameState⟩
    exact ⟨sameSteps.symm,sameState.symm⟩

theorem completed_exact (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) (earlier later : List α)
    (period fuel : Nat) {count : Nat} {after : target.Cfg}
    (completed : run period fuel 0 (initial (inputWire codec earlier later))=some (count,after)) :
    after=haltList target (resultWire codec (earlier++later)) ∧
      count≤288*((inputWire codec earlier later).length+1) := by
  rcases run_actual period fuel 0 _ completed with ⟨_,⟨path,exactCount⟩,halted⟩
  let original := BinaryListAppend.outputs codec earlier later
  let originalPath : StateTransition.EvalsTo target.step (initial (inputWire codec earlier later))
      (some (haltList target (resultWire codec (earlier++later)))) :=
    ⟨original.steps,by rw [initial_eq]; exact original.evals_in_steps⟩
  have afterStopped : target.step after=none := by
    cases after with
    | mk label values contents =>
      cases label with
      | none => rfl
      | some label => cases halted
  rcases terminal_paths_unique target.step path.toEvalsTo originalPath afterStopped (by rfl) with
    ⟨sameCount,sameState⟩
  refine ⟨sameState,?_⟩
  have same : count=original.steps := by simpa only [exactCount,Nat.sub_zero] using sameCount
  rw [same]
  exact original.steps_le_m

theorem completed_word (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) (earlier later : List α)
    (period fuel : Nat) {count : Nat} {after : target.Cfg}
    (completed : run period fuel 0 (initial (inputWire codec earlier later))=some (count,after)) :
    after.stk resultKey=resultWire codec (earlier++later) := by
  rw [(completed_exact codec earlier later period fuel completed).1]
  simp [haltList,show resultKey=target.k₁ from rfl]

theorem completed_registers (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) (earlier later : List α)
    (period fuel : Nat) {count : Nat} {after : target.Cfg}
    (completed : run period fuel 0 (initial (inputWire codec earlier later))=some (count,after)) :
    after.var=registers := by
  rw [(completed_exact codec earlier later period fuel completed).1]
  exact registers_eq.symm

theorem completed_scratch (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) (earlier later : List α)
    (period fuel : Nat) {count : Nat} {after : target.Cfg}
    (completed : run period fuel 0 (initial (inputWire codec earlier later))=some (count,after)) :
    ∀ key : target.K,key≠resultKey → after.stk key=[] := by
  rw [(completed_exact codec earlier later period fuel completed).1]
  intro key different
  have other : key≠target.k₁ := different
  simp only [haltList,dif_neg other]

theorem completed_decodes (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) (earlier later : List α)
    (period fuel : Nat) {count : Nat} {after : target.Cfg}
    (completed : run period fuel 0 (initial (inputWire codec earlier later))=some (count,after)) :
    readResult codec (after.stk resultKey)=some (earlier++later) := by
  rw [completed_word codec earlier later period fuel completed]
  exact result_readout codec (earlier++later)

end Mettapedia.Computability.BinaryListAppend.Program

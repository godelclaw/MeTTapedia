import Mettapedia.Languages.HOLLight.ChronologicalInsertion
import Mettapedia.Computability.BinaryListAppendProgram
import Mettapedia.Languages.HOLLight.ClaimCheckingProgram
import Mettapedia.Computability.PhysicalStatementCache
/-!
# Original chronological insertion instructions and exact execution

Physical instruction adapters retain original keys, endpoints, registers and
checked table equality. Sparse snapshots and earned statement caching preserve
the complete configuration and every original transition. The concrete writer
reuses the original binary append and physically packs the retained root.
The completion law has the original exact certificate and input clock.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.PhysicalInstructionAdapter
open Turing PhysicalStatementCache StackMachineRegisters.StackSnapshot

structure Program (source : FinTM2) where
  body : source.Λ → source.Stmt
  body_eq : body=source.m
  keyEquality : DecidableEq source.K
  labelEquality : DecidableEq source.Λ
  registerEquality : DecidableEq source.σ
  inputKey : source.K
  input_eq : inputKey=source.k₀
  outputKey : source.K
  output_eq : outputKey=source.k₁
  registers : source.σ
  registers_eq : registers=source.initialState
  mainLabel : source.Λ
  main_eq : mainLabel=source.main
  keys : List source.K
  all_keys : ∀ key,key∈keys

variable {source : FinTM2}

@[macro_inline] def step (program : Program source) :=
  @TM2.step source.K source.Γ source.Λ source.σ program.keyEquality program.body

theorem step_eq (program : Program source) : step program=source.step := by
  unfold step
  rw [show program.keyEquality=source.kDecidableEq from Subsingleton.elim _ _,program.body_eq]
  rfl

@[macro_inline] def initial (program : Program source) (word : List (source.Γ source.k₀)) : source.Cfg where
  l:=some program.mainLabel
  var:=program.registers
  stk key:=@dite (List (source.Γ key)) (key=program.inputKey) (program.keyEquality key program.inputKey)
    (fun same => same.symm ▸ program.input_eq.symm ▸ word) (fun _ => [])

theorem initial_eq (program : Program source) (word : List (source.Γ source.k₀)) :
    initial program word=initList source word := by
  rcases program with ⟨instructions,instructionsSame,keyEquality,labelEquality,registerEquality,
    inputKey,inputSame,outputKey,outputSame,registers,registersSame,mainLabel,mainSame,keys,allKeys⟩
  cases inputSame
  cases registersSame
  cases mainSame
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key=source.k₀
  · subst key
    simp
  · simp [same]

def sparse {Key : Type} (cells : Key → Type) (contents : ∀ key,List (cells key)) (keys : List Key) :
    List (Sigma fun key => List (cells key)) :=
  keys.filterMap (fun key => if (contents key).isEmpty then none else some ⟨key,contents key⟩)

theorem sparse_lookup {Key : Type} [DecidableEq Key] (cells : Key → Type)
    (contents : ∀ key,List (cells key)) (keys : List Key) (key : Key) :
    lookup cells (sparse cells contents keys) key=if key∈keys then contents key else [] := by
  induction keys with
  | nil => simp [sparse,lookup]
  | cons head rest ih =>
    simp [sparse] at ih
    by_cases same : head=key
    · subst head
      cases value : contents key with
      | nil => simp [sparse,value,ih]
      | cons symbol tail => simp [sparse,value,lookup]
    · cases value : contents head with
      | nil => simp [sparse,value,ih,Ne.symm same]
      | cons symbol tail => simp [sparse,value,lookup,same,ih,Ne.symm same]

@[macro_inline] def refresh (program : Program source) (state : source.Cfg) : source.Cfg :=
  {state with stk := @lookup source.K program.keyEquality source.Γ (sparse source.Γ state.stk program.keys)}

theorem refresh_eq (program : Program source) (state : source.Cfg) : refresh program state=state := by
  cases state with
  | mk label registers contents =>
    dsimp only [refresh]
    congr 1
    funext key
    have exactLookup := @sparse_lookup source.K program.keyEquality source.Γ contents program.keys key
    rw [if_pos (program.all_keys key)] at exactLookup
    exact exactLookup

def prepareCache {Key : Type} {Cells : Key → Type} {Labels Registers : Type} [DecidableEq Labels]
    (table : Labels → TM2.Stmt Cells Labels Registers)
    (cache : Option (StatementCache Cells Labels Registers table)) (label : Option Labels) :
    Option (StatementCache Cells Labels Registers table) :=
  match label with
  | none => cache
  | some label => match cache with
    | none => some (remember Cells Labels Registers table label)
    | some saved => if label=saved.label then cache else some (remember Cells Labels Registers table label)

def counted (program : Program source) (period : Nat) :
    Nat → Nat → Option (StatementCache source.Γ source.Λ source.σ program.body) → source.Cfg →
    Option (Nat × source.Cfg)
  | 0,_,_,_ => none
  | fuel+1,used,cache,state =>
    if state.l.isNone then some (used,state)
    else match @TM2.step source.K source.Γ source.Λ source.σ program.keyEquality
        (@memoized source.K source.Γ source.Λ source.σ program.labelEquality program.body
          (@prepareCache source.K source.Γ source.Λ source.σ program.labelEquality program.body cache state.l)) state with
      | none => none
      | some after => counted program period fuel (used+1)
          (@prepareCache source.K source.Γ source.Λ source.σ program.labelEquality program.body cache state.l)
          (if (used+1) % period == 0 then refresh program after else after)

theorem counted_actual (program : Program source) (period fuel used : Nat)
    (cache : Option (StatementCache source.Γ source.Λ source.σ program.body))
    (before : source.Cfg) {count : Nat} {after : source.Cfg}
    (completed : counted program period fuel used cache before=some (count,after)) :
    used≤count ∧ (∃ path : StateTransition.EvalsToInTime source.step before (some after) (count-used),
      path.steps=count-used) ∧ after.l=none := by
  induction fuel generalizing used cache before with
  | zero => cases completed
  | succ fuel ih =>
    simp only [counted,PhysicalStatementCache.memoized_step_eq] at completed
    change (if before.l.isNone then _ else match step program before with | none => _ | some _ => _)=_ at completed
    rw [step_eq] at completed
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
      exact ⟨StateTransition.EvalsToInTime.refl source.step before,rfl⟩
    · cases advanced : source.step before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some nextState =>
        simp only [advanced] at completed
        have same : (if (used+1) % period == 0 then refresh program nextState else nextState)=nextState := by
          split <;> simp only [refresh_eq]
        rw [same] at completed
        rcases ih (used+1) _ nextState completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        let first : StateTransition.EvalsToInTime source.step before (some nextState) 1 :=
          ⟨⟨1,by change (some before).bind source.step=some nextState; exact advanced⟩,le_rfl⟩
        have relative : count-used=(count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans source.step 1 (count-(used+1)) before nextState
          (some after) first tail,?_⟩
        change tail.steps+first.steps=(count-(used+1))+1
        rw [tailCount]

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

theorem terminal_paths_unique {Config : Type} (transition : Config → Option Config)
    {before first last : Config} (firstPath : StateTransition.EvalsTo transition before (some first))
    (lastPath : StateTransition.EvalsTo transition before (some last))
    (firstHalted : transition first=none) (lastHalted : transition last=none) :
    firstPath.steps=lastPath.steps ∧ first=last := by
  rcases Nat.le_total firstPath.steps lastPath.steps with ordered | ordered
  · exact terminal_compare transition firstPath lastPath firstHalted ordered
  · rcases terminal_compare transition lastPath firstPath lastHalted ordered with ⟨steps,state⟩
    exact ⟨steps.symm,state.symm⟩

theorem completed_original (program : Program source) (input : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (bound : Nat)
    (original : TM2OutputsInTime source input (some output) bound) (period fuel : Nat)
    {count : Nat} {after : source.Cfg}
    (completed : counted program period fuel 0 none (initial program input)=some (count,after)) :
    after=haltList source output ∧ count≤bound := by
  rcases counted_actual program period fuel 0 none _ completed with ⟨_,⟨path,exactCount⟩,halted⟩
  let canonical : StateTransition.EvalsTo source.step (initial program input)
      (some (haltList source output)) :=
    ⟨original.steps,by rw [initial_eq]; exact original.evals_in_steps⟩
  have stopped : source.step after=none := by
    cases after with
    | mk label values contents =>
      cases label with
      | none => rfl
      | some label => cases halted
  rcases terminal_paths_unique source.step path.toEvalsTo canonical stopped (by rfl) with ⟨sameCount,sameState⟩
  refine ⟨sameState,?_⟩
  have same : count=original.steps := by simpa only [exactCount,Nat.sub_zero] using sameCount
  rw [same]
  exact original.steps_le_m

end Mettapedia.Computability.PhysicalInstructionAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.ChronologicalInsertion.Program
open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.HOLLight Mettapedia.Languages.HOLLight.ChronologicalInsertion
open Mettapedia.Languages.HOLLight.RuleArgumentRendering.Program
attribute [local reducible] ChronologicalInsertion.machine ChronologicalInsertion.retainedMachine
  ChronologicalInsertion.rawMachine ChronologicalInsertion.appendedMachine
  BinaryListAppend.machine BinaryListAppend.checkedSuffixMachine BinaryListAppend.statusMachine
  BinaryListAppend.identityMachine BinaryListAppend.stripMachine BinaryListAppend.rawStemMachine
  BinaryListAppend.retainedMachine BinaryListAppend.payloadMachine BinaryListAppend.guardMachine
  BinaryListAppend.restoredBody BinaryListAppend.dispatchMachine
  StackMachineComposition.machine StackMachineComposition.Dispatch.machine
  StackMachineComposition.liftFirst StackMachineComposition.liftSecond StackMachineComposition.Dispatch.lift
  RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.statement
  RetainedWordExecution.WithOutput.body RetainedWordExecution.machine RetainedWordExecution.body
  RetainedWordExecution.statement RetainedWordExecution.WithOutput.Framed.untag
  WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine
  FramedFieldSelection.machine FramedWordSuffixRemoval.machine
  StackMachineComposition.leftKey StackMachineComposition.rightKey
abbrev target := ChronologicalInsertion.machine

abbrev selected := FramedFieldSelection.machine (Γ:=ChronologicalInsertion.Alphabet) selector
abbrev core := RetainedWordExecution.WithOutput.machine rawMachine
abbrev tagged := RetainedWordExecution.WithOutput.Framed.taggedMachine rawMachine
  (Equiv.refl (Option ChronologicalInsertion.Alphabet)) (Equiv.refl ChronologicalInsertion.Alphabet)

local instance : Fintype (selected.Γ selected.k₁) := inferInstanceAs (Fintype (Option ChronologicalInsertion.Alphabet))
local instance : Inhabited (selected.Γ selected.k₁) := inferInstanceAs (Inhabited (Option ChronologicalInsertion.Alphabet))
local instance : Fintype (appendedMachine.Γ appendedMachine.k₁) := inferInstanceAs (Fintype ChronologicalInsertion.Alphabet)
local instance : Inhabited (appendedMachine.Γ appendedMachine.k₁) := inferInstanceAs (Inhabited ChronologicalInsertion.Alphabet)
local instance : Fintype (rawMachine.Γ rawMachine.k₁) := inferInstanceAs (Fintype ChronologicalInsertion.Alphabet)
local instance : Inhabited (rawMachine.Γ rawMachine.k₀) := inferInstanceAs (Inhabited (Option ChronologicalInsertion.Alphabet))
local instance : Inhabited (rawMachine.Γ rawMachine.k₁) := inferInstanceAs (Inhabited ChronologicalInsertion.Alphabet)
local instance : Fintype (core.Γ core.k₁) := inferInstanceAs (Fintype (Option ChronologicalInsertion.Alphabet ⊕ ChronologicalInsertion.Alphabet))
local instance : Inhabited (core.Γ core.k₁) := ⟨.inr 0⟩
local instance : Fintype (tagged.Γ tagged.k₁) := inferInstanceAs (Fintype (Option ChronologicalInsertion.Alphabet))
local instance : Inhabited (tagged.Γ tagged.k₁) := inferInstanceAs (Inhabited (Option ChronologicalInsertion.Alphabet))
local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Fintype (Option ChronologicalInsertion.Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) := inferInstanceAs (Inhabited (Option ChronologicalInsertion.Alphabet))

attribute [local reducible] core tagged RetainedWordExecution.WithOutput.Framed.taggedMachine
  RetainedWordExecution.WithOutput.Framed.machine

def selectedTable : {instructions : selected.Λ → selected.Stmt // instructions=selected.m} := by
  extract_rule_program selected.m
def selectedBody := selectedTable.val
theorem selectedBody_eq : selectedBody=selected.m := selectedTable.property

def appendedBody : appendedMachine.Λ → appendedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    selected.k₁ BinaryListAppend.Program.inputKey BinaryListAppend.Program.mainLabel
    (none : Option ChronologicalInsertion.Alphabet) id selectedBody BinaryListAppend.Program.body)
theorem appendedBody_eq : appendedBody=appendedMachine.m := by
  unfold appendedBody
  rw [selectedBody_eq,BinaryListAppend.Program.body_eq]
  exact StackMachineComposition.body_eq selected BinaryListAppend.machine (Equiv.refl _)

def rawBody : rawMachine.Λ → rawMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    appendedMachine.k₁ BinaryListAppend.stripMachine.k₀ BinaryListAppend.stripMachine.main
    (0 : ChronologicalInsertion.Alphabet) id appendedBody BinaryListAppend.Program.stripBody)
theorem rawBody_eq : rawBody=rawMachine.m := by
  unfold rawBody
  rw [appendedBody_eq,BinaryListAppend.Program.stripBody_eq]
  exact StackMachineComposition.body_eq appendedMachine BinaryListAppend.stripMachine (Equiv.refl _)

def coreBody : core.Λ → core.Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement rawMachine.k₀ rawMachine.k₁
    (none : Option ChronologicalInsertion.Alphabet) (0 : ChronologicalInsertion.Alphabet)
    rawMachine.initialState rawMachine.main rawBody)
theorem coreBody_eq : coreBody=core.m := by
  unfold coreBody
  rw [rawBody_eq]
  rfl

abbrev untag := RetainedWordExecution.WithOutput.Framed.untag rawMachine
  (Equiv.refl (Option ChronologicalInsertion.Alphabet)) (Equiv.refl ChronologicalInsertion.Alphabet)

def taggedBody : tagged.Λ → tagged.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FirstAlphabet:=core.Γ) none WordHomomorphismMachine.Stack.input .read
    (.inr (0 : ChronologicalInsertion.Alphabet) : Option ChronologicalInsertion.Alphabet ⊕ ChronologicalInsertion.Alphabet)
    id coreBody (WordHomomorphismMachine.program untag))
theorem taggedBody_eq : taggedBody=tagged.m := by
  unfold taggedBody
  rw [coreBody_eq]
  exact StackMachineComposition.body_eq core (WordHomomorphismMachine.machine
    (RetainedWordExecution.WithOutput.Framed.untag rawMachine
      (Equiv.refl (Option ChronologicalInsertion.Alphabet)) (Equiv.refl ChronologicalInsertion.Alphabet))) (Equiv.refl _)

def framedBody : retainedMachine.Λ → retainedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FirstAlphabet:=tagged.Γ) tagged.k₁ WordTemplateMachine.Stack.input (.emit ⟨0,by decide⟩)
    (none : Option ChronologicalInsertion.Alphabet) id taggedBody
    (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=ChronologicalInsertion.Alphabet))))
theorem framedBody_eq : framedBody=retainedMachine.m := by
  unfold framedBody
  rw [taggedBody_eq]
  exact StackMachineComposition.body_eq tagged
    (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ:=ChronologicalInsertion.Alphabet))) (Equiv.refl _)

def body : target.Λ → target.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    retainedMachine.k₁ Indexed.Stack.input (.emit ⟨0,by decide⟩)
    (none : Option ChronologicalInsertion.Alphabet) id framedBody
    (Indexed.arrayProgram pack.length pack.toArray))
theorem body_eq : body=target.m := by
  unfold body
  rw [framedBody_eq,Indexed.arrayProgram_eq_program]
  exact StackMachineComposition.body_eq retainedMachine (Indexed.machine pack) (Equiv.refl _)

def keyEquality : DecidableEq target.K := by append_literal_equality
local instance : DecidableEq target.K := keyEquality
def registerEquality : DecidableEq target.σ := by append_literal_equality
def labelEquality : DecidableEq target.Λ := by append_literal_equality

def inputKey : target.K := by normalize_rule_program target.k₀
def outputKey : target.K := by normalize_rule_program target.k₁
def registers : target.σ := by normalize_rule_program target.initialState
def mainLabel : target.Λ := by normalize_rule_program target.main

def keys : List target.K := by claim_program_keys
local instance : BEq target.K := ⟨fun a b => decide (a=b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K := target.kFin
theorem all_keys : ∀ key : target.K,key∈keys := by decide +kernel

def initial (word : List (Option ChronologicalInsertion.Alphabet)) : target.Cfg where
  l:=some mainLabel
  var:=registers
  stk key:=if same : key=inputKey then same.symm ▸ word else []

theorem initial_eq (word : List (Option ChronologicalInsertion.Alphabet)) : initial word=initList target word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key=inputKey
  · subst key
    have original : inputKey=target.k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have different : key≠target.k₀ := same
    simp only [dif_neg same,dif_neg different]

def step := @TM2.step target.K target.Γ target.Λ target.σ keyEquality body
theorem step_eq : step=target.step := by
  unfold step
  rw [show keyEquality=target.kDecidableEq from Subsingleton.elim _ _,body_eq]
  rfl
def program : Mettapedia.Computability.PhysicalInstructionAdapter.Program target where
  body:=body
  body_eq:=body_eq
  keyEquality:=keyEquality
  labelEquality:=labelEquality
  registerEquality:=registerEquality
  inputKey:=inputKey
  input_eq:=by rfl
  outputKey:=outputKey
  output_eq:=by rfl
  registers:=registers
  registers_eq:=by rfl
  mainLabel:=mainLabel
  main_eq:=by rfl
  keys:=keys
  all_keys:=all_keys

theorem completed_exact (earlier later : List ProofExecution.Receipt) (root period fuel : Nat)
    {count : Nat} {after : target.Cfg}
    (completed : PhysicalInstructionAdapter.counted program period fuel 0 none
      (PhysicalInstructionAdapter.initial program (inputWire earlier later root))=some (count,after)) :
    after=haltList target (ProofDataEncoding.encodeCertificate (earlier++later,root)) ∧
      count≤500*((inputWire earlier later root).length+1) :=
  PhysicalInstructionAdapter.completed_original program _ _ _ (ChronologicalInsertion.outputs earlier later root)
    period fuel completed

end Mettapedia.Languages.HOLLight.ChronologicalInsertion.Program

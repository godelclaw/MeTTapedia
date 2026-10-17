import Mettapedia.Languages.HOLLight.SavedRootInsertion
import Mettapedia.Languages.HOLLight.AuthoredNodeDispatch
import Mettapedia.Languages.HOLLight.SharedPremiseExecution
import Mettapedia.Languages.HOLLight.ChronologicalTaskEncoding
import Mettapedia.Computability.BinaryListAppend

/-!
# Physical chronological visit transitions

The machines below operate on original binary codecs. The node packet machine
pops the pending visit, selects an authored rule, checks the original application
and child count, and writes its ordered children and close continuation ahead of
the preserved tail. The premise packet machine earns a saved root through the
original table lookup and claim checker, then writes that original natural value
onto the returned-root list. Both have counted original executions and independent
codec readouts. Separate framed-stack contracts preserve arbitrary caller data.

The source specifications are used only in proofs and readouts, never as machine
callbacks. Source arguments, proof bodies, paths and roots stay in stack words;
only authored rows and finite parser phases determine finite control.

The total branch contracts cover canonical visit-node and visit-premise packets.
They do not assert admission for arbitrary malformed words, a common task-kind
dispatcher, close/save/finish execution, an occurrence-journal update, or a whole
driver loop. The generic premise/controller contract states a scope condition.
For states reached by the original controller, `SourceScope` earns that condition
from actual admitted rule conclusions and preserves it through every task,
including close and save. The physical claim checker still executes its test.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

abbrev Alphabet := ChronologicalTaskEncoding.Alphabet
abbrev Cell := Option Alphabet
abbrev Register := Option Cell

inductive Key where
  | work | prepared | temporary | payload | saved | returned
  deriving DecidableEq, Fintype

inductive Phase where
  | pop | restorePop | push | restorePush | clearBad
  deriving DecidableEq, Fintype

/-- Task framing is already separate from original bytes. The control keeps
one cell and never decodes a dynamic task, address, path or goal into a register. -/
def statement : Phase → TM2.Stmt (fun _ : Key => Cell) Phase Register
  | .pop => pop .work (fun _ cell => cell)
      (branch Option.isSome
        (branch (fun cell => (cell.getD none).isSome)
          (push .temporary (fun cell => cell.getD none) (goto fun _ => .pop))
          (goto fun _ => .restorePop))
        (goto fun _ => .clearBad))
  | .restorePop => pop .temporary (fun _ cell => cell)
      (branch Option.isSome
        (push .payload (fun cell => cell.getD none) (goto fun _ => .restorePop))
        (load (fun _ => none) halt))
  | .push => pop .prepared (fun _ cell => cell)
      (branch Option.isSome
        (push .temporary (fun cell => cell.getD none) (goto fun _ => .push))
        (goto fun _ => .restorePush))
  | .restorePush => pop .temporary (fun _ cell => cell)
      (branch Option.isSome
        (push .work (fun cell => cell.getD none) (goto fun _ => .restorePush))
        (load (fun _ => none) halt))
  | .clearBad => pop .temporary (fun _ cell => cell)
      (branch Option.isSome (goto fun _ => .clearBad) (load (fun _ => none) halt))

def machine (pushing : Bool) : FinTM2 where
  K := Key
  k₀ := if pushing then .prepared else .work
  k₁ := if pushing then .work else .payload
  Γ _ := Cell
  main := if pushing then .push else .pop
  Λ := Phase
  σ := Register
  initialState := none
  m := statement

def config (pushing : Bool) (phase : Option Phase) (register : Register)
    (work prepared temporary payload saved returned : List Cell) : (machine pushing).Cfg where
  l := phase
  var := register
  stk key := match key with
    | .work => work | .prepared => prepared | .temporary => temporary
    | .payload => payload | .saved => saved | .returned => returned

local macro "task_stack_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, statement, config, TM2.step, TM2.stepAux] <;>
  (funext key; cases key <;> simp [Function.update])))

theorem pop_byte (pushing : Bool) (register : Register) (byte : Alphabet)
    (work prepared temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .pop) register (some byte :: work)
      prepared temporary payload saved returned) =
      some (config pushing (some .pop) (some (some byte)) work prepared
        (some byte :: temporary) payload saved returned) := by task_stack_step

theorem pop_delimiter (pushing : Bool) (register : Register)
    (work prepared temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .pop) register (none :: work)
      prepared temporary payload saved returned) =
      some (config pushing (some .restorePop) (some none) work prepared temporary payload saved returned) := by task_stack_step

theorem restore_pop_cell (pushing : Bool) (register : Register) (cell : Cell)
    (work prepared temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .restorePop) register work prepared
      (cell :: temporary) payload saved returned) =
      some (config pushing (some .restorePop) (some cell) work prepared temporary
        (cell :: payload) saved returned) := by task_stack_step

theorem restore_pop_nil (pushing : Bool) (register : Register)
    (work prepared payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .restorePop) register work prepared [] payload saved returned) =
      some (config pushing none none work prepared [] payload saved returned) := by task_stack_step

theorem push_cell (pushing : Bool) (register : Register) (cell : Cell)
    (work prepared temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .push) register work (cell :: prepared)
      temporary payload saved returned) =
      some (config pushing (some .push) (some cell) work prepared
        (cell :: temporary) payload saved returned) := by task_stack_step

theorem push_nil (pushing : Bool) (register : Register)
    (work temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .push) register work [] temporary payload saved returned) =
      some (config pushing (some .restorePush) none work [] temporary payload saved returned) := by task_stack_step

theorem restore_push_cell (pushing : Bool) (register : Register) (cell : Cell)
    (work prepared temporary payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .restorePush) register work prepared
      (cell :: temporary) payload saved returned) =
      some (config pushing (some .restorePush) (some cell) (cell :: work) prepared temporary
        payload saved returned) := by task_stack_step

theorem restore_push_nil (pushing : Bool) (register : Register)
    (work prepared payload saved returned : List Cell) :
    (machine pushing).step (config pushing (some .restorePush) register work prepared [] payload saved returned) =
      some (config pushing none none work prepared [] payload saved returned) := by task_stack_step

def restorePop_run (pushing : Bool) (temporary : List Cell) (register : Register)
    (work prepared payload saved returned : List Cell) :
    EvalsToInTime (machine pushing).step
      (config pushing (some .restorePop) register work prepared temporary payload saved returned)
      (some (config pushing none none work prepared [] (temporary.reverse ++ payload) saved returned))
      (temporary.length + 1) := by
  induction temporary generalizing register payload with
  | nil => simpa using StackMachineComposition.oneStep (restore_pop_nil pushing register work prepared payload saved returned)
  | cons cell temporary ih =>
      have first := StackMachineComposition.oneStep
        (restore_pop_cell pushing register cell work prepared temporary payload saved returned)
      have rest := ih (some cell) (cell :: payload)
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_comm] using
        EvalsToInTime.trans _ 1 (temporary.length + 1) _ _ _ first rest

def pop_run (pushing : Bool) (word : List Alphabet) (register : Register)
    (tail prepared temporary payload saved returned : List Cell) :
    EvalsToInTime (machine pushing).step
      (config pushing (some .pop) register (word.map some ++ none :: tail) prepared temporary payload saved returned)
      (some (config pushing none none tail prepared [] (temporary.reverse ++ word.map some ++ payload) saved returned))
      (2 * word.length + temporary.length + 2) := by
  induction word generalizing register temporary with
  | nil =>
      have first := StackMachineComposition.oneStep (pop_delimiter pushing register tail prepared temporary payload saved returned)
      have rest := restorePop_run pushing temporary (some none) tail prepared payload saved returned
      convert EvalsToInTime.trans _ 1 (temporary.length + 1) _ _ _ first rest using 1 <;>
        simp only [List.map_nil, List.nil_append, List.append_nil, List.length_nil]
      omega
  | cons byte word ih =>
      have first := StackMachineComposition.oneStep
        (pop_byte pushing register byte (word.map some ++ none :: tail) prepared temporary payload saved returned)
      have rest := ih (some (some byte)) (some byte :: temporary)
      convert EvalsToInTime.trans _ 1 (2 * word.length + (some byte :: temporary).length + 2) _ _ _ first rest using 1 <;>
        simp only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append, List.length_cons]
      omega

def restorePush_run (pushing : Bool) (temporary : List Cell) (register : Register)
    (work prepared payload saved returned : List Cell) :
    EvalsToInTime (machine pushing).step
      (config pushing (some .restorePush) register work prepared temporary payload saved returned)
      (some (config pushing none none (temporary.reverse ++ work) prepared [] payload saved returned))
      (temporary.length + 1) := by
  induction temporary generalizing register work with
  | nil => simpa using StackMachineComposition.oneStep (restore_push_nil pushing register work prepared payload saved returned)
  | cons cell temporary ih =>
      have first := StackMachineComposition.oneStep
        (restore_push_cell pushing register cell work prepared temporary payload saved returned)
      have rest := ih (some cell) (cell :: work)
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_comm] using
        EvalsToInTime.trans _ 1 (temporary.length + 1) _ _ _ first rest

def push_run (pushing : Bool) (workPrefix : List Cell) (register : Register)
    (work temporary payload saved returned : List Cell) :
    EvalsToInTime (machine pushing).step
      (config pushing (some .push) register work workPrefix temporary payload saved returned)
      (some (config pushing none none (temporary.reverse ++ workPrefix ++ work) [] [] payload saved returned))
      (2 * workPrefix.length + temporary.length + 2) := by
  induction workPrefix generalizing register temporary with
  | nil =>
      have first := StackMachineComposition.oneStep (push_nil pushing register work temporary payload saved returned)
      have rest := restorePush_run pushing temporary none work [] payload saved returned
      convert EvalsToInTime.trans _ 1 (temporary.length + 1) _ _ _ first rest using 1 <;>
        simp only [List.append_nil, List.length_nil]
      omega
  | cons cell workPrefix ih =>
      have first := StackMachineComposition.oneStep
        (push_cell pushing register cell work workPrefix temporary payload saved returned)
      have rest := ih (some cell) (cell :: temporary)
      convert EvalsToInTime.trans _ 1 (2 * workPrefix.length + (cell :: temporary).length + 2) _ _ _ first rest using 1 <;>
        simp only [List.cons_append, List.reverse_cons, List.append_assoc, List.nil_append, List.length_cons]
      omega

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

abbrev Alphabet := ChronologicalTaskEncoding.Alphabet
abbrev Word := List Alphabet
abbrev Slots (arity : Nat) := Fin (10 + 2 * arity)

def baseSlot (arity : Nat) (index : Fin 10) : Slots arity := ⟨index.val, by omega⟩

def goalSlot {arity : Nat} (index : Fin arity) : Slots arity := ⟨10 + 2 * index.val, by omega⟩
def proofSlot {arity : Nat} (index : Fin arity) : Slots arity := ⟨11 + 2 * index.val, by omega⟩

def metadata (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) : Fin 10 → Word :=
  ![encodeWith CertificateDataEncoding.instanceCodec ruleInstance,
    encodeWith CertificateDataEncoding.patternCodec goal,
    encodeWith (Codec.list CertificateDataEncoding.proofCodec) proofs,
    encodeWith originCodec site.origin, encodeWith (Codec.list Codec.nat) site.path,
    encodeWork tail, encodeRoots saved, encodeRoots returned,
    BinaryListAppend.stem Codec.nat site.path, [1]]

def fields {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (slot : Slots arity) : Word :=
  if small : slot.val < 10 then metadata ruleInstance goal proofs site tail saved returned ⟨slot.val, small⟩
  else
    let index : Fin arity := ⟨(slot.val - 10) / 2, by omega⟩
    if (slot.val - 10) % 2 = 0 then encodeWith CertificateDataEncoding.patternCodec (jobs index).1
    else CertificateDataEncoding.encodeProof (jobs index).2

@[simp] theorem fields_base {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (index : Fin 10) :
    fields ruleInstance goal proofs site tail saved returned jobs (baseSlot arity index) =
      metadata ruleInstance goal proofs site tail saved returned index := by
  simp only [fields, baseSlot, index.isLt, ↓reduceDIte]

@[simp] theorem fields_goal {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (index : Fin arity) :
    fields ruleInstance goal proofs site tail saved returned jobs (goalSlot index) =
      encodeWith CertificateDataEncoding.patternCodec (jobs index).1 := by
  simp [fields, goalSlot, show ¬ 10 + 2 * index.val < 10 by omega]

@[simp] theorem fields_proof {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (index : Fin arity) :
    fields ruleInstance goal proofs site tail saved returned jobs (proofSlot index) =
      CertificateDataEncoding.encodeProof (jobs index).2 := by
  have less : ¬ 11 + 2 * index.val < 10 := by omega
  have sub : 11 + 2 * index.val - 10 = 2 * index.val + 1 := by omega
  have div : (2 * index.val + 1) / 2 = index.val := by omega
  have mod : (2 * index.val + 1) % 2 = 1 := by omega
  simp [fields, proofSlot, less, sub, div, mod]

def literals {arity : Nat} (word : Word) : Indexed.Template Alphabet arity := word.map Sum.inl

def childSiteTemplate {arity : Nat} (index : Fin arity) : Indexed.Template Alphabet (10 + 2 * arity) :=
  [.inl 4, .inr (baseSlot arity 3), .inr (baseSlot arity 8)] ++ literals (4 :: encodeWith Codec.nat index.val ++ [3,2])

def visitTemplate {arity : Nat} (index : Fin arity) : Indexed.Template Alphabet (10 + 2 * arity) :=
  literals [4,3,2,4] ++ [.inr (goalSlot index), .inl 4, .inr (proofSlot index)] ++ childSiteTemplate index

theorem child_site_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (index : Fin arity) :
    Indexed.instantiate (childSiteTemplate index) (fields ruleInstance goal proofs site tail saved returned jobs) =
      encodeWith siteCodec ⟨site.origin, site.path ++ [index.val]⟩ := by
  have appended := BinaryListAppend.original_append Codec.nat site.path [index.val]
  simp only [childSiteTemplate, Indexed.instantiate_append, literals, Indexed.instantiate_literals,
    Indexed.instantiate_literal, Indexed.instantiate_hole, Indexed.instantiate_nil]
  simp only [fields_base]
  change (4 :: (encodeWith originCodec site.origin ++ (BinaryListAppend.stem Codec.nat site.path ++ []))) ++
    (4 :: encodeWith Codec.nat index.val ++ [3,2]) = _
  simp only [List.append_nil, List.cons_append, List.append_assoc]
  have singleton := BinaryListAppend.encode_cons Codec.nat index.val []
  change encodeWith (Codec.list Codec.nat) [index.val] = 4 :: (encodeWith Codec.nat index.val ++ [3,2]) at singleton
  rw [← singleton, appended]
  simp only [encodeWith, siteCodec, Codec.mapped, Codec.prod, encodeData_pair]

theorem visit_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat)
    (jobs : Fin arity → Pattern × RawOpenProof) (index : Fin arity) :
    Indexed.instantiate (visitTemplate index) (fields ruleInstance goal proofs site tail saved returned jobs) =
      encodeTask (.visit (jobs index).1 (jobs index).2 ⟨site.origin, site.path ++ [index.val]⟩) := by
  simp only [visitTemplate, Indexed.instantiate_append, literals, Indexed.instantiate_literals,
    Indexed.instantiate_hole, Indexed.instantiate_literal, fields_goal, fields_proof,
    child_site_instantiates, task_visit_wire, List.append_assoc, List.cons_append, List.nil_append]

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] WordTemplateMachine.machine StackMachineComposition.Dispatch.machine
  StackMachineComposition.machine

abbrev Alphabet := ChronologicalTaskEncoding.Alphabet

def rootWord (root : Option Nat) : List Alphabet :=
  root.elim [(0 : Alphabet)] (fun address => 1 :: encodeWith Codec.nat address)

def readRoot : List Alphabet → Option Nat
  | 1 :: body => decodeWith Codec.nat body
  | _ => none

theorem readRoot_rootWord (root : Option Nat) : readRoot (rootWord root) = root := by
  cases root with
  | none => rfl
  | some root => exact decodeWith_encodeWith Codec.nat root

def rootTemplate : WordTemplateMachine.Template Alphabet := [some 1, some 3, none]
def accept (symbol : Alphabet) := decide (symbol = 1)
def conversionMachine := StackMachineComposition.Dispatch.machine (WordTemplateMachine.machine rootTemplate) accept [(0 : Alphabet)]

theorem key_nat_word (address : Nat) : field (naturalKey address) ++ [2] = Binary.natural address := by
  simp only [field, naturalKey, List.map_map, Function.comp_def, Binary.natural]
  congr 1
  apply List.map_congr_left
  intro digit _
  by_cases zero : digit = 0 <;> simp [bit, zero]

noncomputable def conversionOutputs (root : Option Nat) :
    TM2OutputsInTime conversionMachine (physicalOutput root) (some (rootWord root))
      (20 * ((physicalOutput root).length + 1)) := by
  cases root with
  | none =>
      have run := StackMachineComposition.Dispatch.outputs_refused (WordTemplateMachine.machine rootTemplate)
        accept [(0 : Alphabet)] (0 : Alphabet) [] (by decide)
      apply WordEqualityMachine.within run
      change 2 ≤ 20 * (1 + 1)
      omega
  | some address =>
      have run := WordTemplateMachine.outputs rootTemplate (field (naturalKey address) ++ [2])
      have same : WordTemplateMachine.instantiate rootTemplate (field (naturalKey address) ++ [2]) =
          rootWord (some address) := by
        simp only [rootTemplate, WordTemplateMachine.instantiate_literal, WordTemplateMachine.instantiate_hole,
          WordTemplateMachine.instantiate_nil, List.append_nil, rootWord, Option.elim_some]
        rw [key_nat_word]
        simp only [encodeWith, Codec.nat, encodeData_atom]
      rw [same] at run
      have dispatched := StackMachineComposition.Dispatch.outputs_success
        (WordTemplateMachine.machine rootTemplate) accept [(0 : Alphabet)] (1 : Alphabet)
        (field (naturalKey address) ++ [2]) (rootWord (some address)) _ (by decide) run
      apply WordEqualityMachine.within dispatched
      simp only [rootTemplate, List.length_cons, List.length_nil, physicalOutput, Option.map_some, output, List.length_append]
      omega

local instance : Fintype (SharedPremiseExecution.machine.Γ SharedPremiseExecution.machine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (SharedPremiseExecution.machine.Γ SharedPremiseExecution.machine.k₁) := inferInstanceAs (Inhabited Alphabet)

def machine := StackMachineComposition.machine SharedPremiseExecution.machine conversionMachine (Equiv.refl Alphabet)

def clock (roots : Array Nat) (cache : Array Theorem) (query : Nat) (goal : Pattern) :=
  SharedPremiseExecution.coefficient * ((SharedPremiseExecution.inputWire roots cache query goal).length + 1)^3 +
    2 * (physicalOutput (SharedPremiseExecution.result roots cache query goal)).length + 2 +
    20 * ((physicalOutput (SharedPremiseExecution.result roots cache query goal)).length + 1)

noncomputable def outputs (roots : Array Nat) (cache : Array Theorem) (query : Nat) (goal : Pattern) :
    TM2OutputsInTime machine (SharedPremiseExecution.inputWire roots cache query goal)
      (some (rootWord (SharedPremiseExecution.result roots cache query goal))) (clock roots cache query goal) := by
  have converted := conversionOutputs (SharedPremiseExecution.result roots cache query goal)
  have joined := StackMachineComposition.outputs SharedPremiseExecution.machine conversionMachine (Equiv.refl Alphabet)
    (SharedPremiseExecution.inputWire roots cache query goal)
    (physicalOutput (SharedPremiseExecution.result roots cache query goal))
    (rootWord (SharedPremiseExecution.result roots cache query goal)) _ _
    (SharedPremiseExecution.outputs roots cache query goal) (by
      change TM2OutputsInTime conversionMachine
        ((physicalOutput (SharedPremiseExecution.result roots cache query goal)).map id) _ _
      simpa only [List.map_id] using converted)
  exact joined

theorem run_decodes (roots : Array Nat) (cache : Array Theorem) (query : Nat) (goal : Pattern)
    {word : List Alphabet}
    (finished : TM2Outputs machine (SharedPremiseExecution.inputWire roots cache query goal) (some word)) :
    readRoot word = SharedPremiseExecution.result roots cache query goal := by
  rw [StackMachineComposition.outputs_unique finished (outputs roots cache query goal).toEvalsTo]
  exact readRoot_rootWord _

variable (definition : ValidatedCalculusLanguageDef)

def savedGoalRoots (state : State definition) : Array Nat :=
  (state.saved.map (fun claim => claim.root)).toArray

theorem saved_claim_root (state : State definition) (query : Nat)
    (claim : Claim definition state.checkedPrefix) (selected : state.saved[query]? = some claim) :
    getElem? (savedGoalRoots definition state) query = some claim.root := by
  simp [savedGoalRoots, List.getElem?_map, selected]

/-- Physical lookup and claim checking earn the same address used by the
actual controller. Source scope is an explicit enclosing admission invariant. -/
theorem controller_result (state : State definition) (query : Nat) (goal : Pattern)
    (claim : Claim definition state.checkedPrefix) (selected : state.saved[query]? = some claim)
    (same : claim.goal = goal) (scope : argumentValidAt 0 goal = true) :
    SharedPremiseExecution.result (savedGoalRoots definition state) state.checkedPrefix.val.cache query goal =
      some claim.root := by
  have represents : hasClaim goal claim.out = true := same ▸ claim.represents
  have valid := of_decide_eq_true represents
  exact (SharedPremiseExecution.result_some_iff _ _ _ _ _).mpr
    ⟨saved_claim_root definition state query claim selected, claim.out, claim.found, scope, valid⟩

theorem controller_step (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (work : state.todo = .visit goal (.premise query) site :: tail)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal) :
    ChronologicalDriver.step definition (.running state) =
      .running (remember definition state site claim tail) := by
  simp only [ChronologicalDriver.step, work, selected, same, ↓reduceIte]

noncomputable def controller_execution (state : State definition) (query : Nat) (goal : Pattern)
    (claim : Claim definition state.checkedPrefix) (selected : state.saved[query]? = some claim)
    (same : claim.goal = goal) (scope : argumentValidAt 0 goal = true) :
    TM2OutputsInTime machine (SharedPremiseExecution.inputWire (savedGoalRoots definition state)
      state.checkedPrefix.val.cache query goal) (some (rootWord (some claim.root)))
      (clock (savedGoalRoots definition state) state.checkedPrefix.val.cache query goal) := by
  have run := outputs (savedGoalRoots definition state) state.checkedPrefix.val.cache query goal
  rw [controller_result definition state query goal claim selected same scope] at run
  exact run

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

variable {α : Type}

theorem instantiate_plans {arity : Nat} (plans : List (Indexed.Template Alphabet arity))
    (words : Fin arity → Word) :
    Indexed.instantiate plans.flatten words = plans.flatMap (fun plan => Indexed.instantiate plan words) := by
  induction plans with
  | nil => rfl
  | cons plan plans ih =>
      simp only [List.flatten_cons, Indexed.instantiate_append, List.flatMap_cons]
      rw [ih]

theorem list_stem (codec : Codec α) (items : List α) :
    BinaryListAppend.stem codec items = items.flatMap (fun item => 4 :: encodeWith codec item) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp [BinaryListAppend.stem, ih]

def visits {arity : Nat} (site : Site) (jobs : Fin arity → Pattern × RawOpenProof) : List Task :=
  (List.finRange arity).map (fun index => .visit (jobs index).1 (jobs index).2 ⟨site.origin, site.path ++ [index.val]⟩)

def premises {arity : Nat} (jobs : Fin arity → Pattern × RawOpenProof) : List Pattern :=
  (List.finRange arity).map (fun index => (jobs index).1)

def childWorkTemplate (arity : Nat) : Indexed.Template Alphabet (10 + 2 * arity) :=
  ((List.finRange arity).map (fun index => .inl (4 : Alphabet) :: visitTemplate index)).flatten

def premiseTemplate (arity : Nat) : Indexed.Template Alphabet (10 + 2 * arity) :=
  ((List.finRange arity).map (fun index => [.inl (4 : Alphabet), .inr (goalSlot index)])).flatten ++ literals [3,2]

def closeTemplate (arity : Nat) : Indexed.Template Alphabet (10 + 2 * arity) :=
  literals [4,3,1,2,4] ++ [.inr (baseSlot arity 1), .inl 4, .inr (baseSlot arity 0), .inl 4] ++
    premiseTemplate arity ++ [.inl 4, .inr (baseSlot arity 3), .inr (baseSlot arity 4)]

def queueTemplate (arity : Nat) : Indexed.Template Alphabet (10 + 2 * arity) :=
  literals [1,4] ++ childWorkTemplate arity ++ [.inl 4] ++ closeTemplate arity ++
    [.inr (baseSlot arity 5), .inl 4, .inr (baseSlot arity 7), .inr (baseSlot arity 6)]

theorem child_work_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    Indexed.instantiate (childWorkTemplate arity) (fields ruleInstance goal proofs site tail saved returned jobs) =
      BinaryListAppend.stem taskCodec (visits site jobs) := by
  rw [childWorkTemplate, instantiate_plans, list_stem]
  simp only [List.flatMap_map, Indexed.instantiate_literal, visit_instantiates, visits]
  rfl

theorem premise_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    Indexed.instantiate (premiseTemplate arity) (fields ruleInstance goal proofs site tail saved returned jobs) =
      encodeWith (Codec.list CertificateDataEncoding.patternCodec) (premises jobs) := by
  rw [premiseTemplate, Indexed.instantiate_append, instantiate_plans]
  simp only [List.flatMap_map, Indexed.instantiate_literal, Indexed.instantiate_hole,
    Indexed.instantiate_nil, fields_goal, literals, Indexed.instantiate_literals, List.append_nil]
  rw [BinaryListAppend.original_suffix, list_stem]
  simp only [premises, List.flatMap_map]

/-- Compiled child positions copy runtime original field bytes; no goal, proof
body, path or returned root is put into finite control metadata. -/
theorem close_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    Indexed.instantiate (closeTemplate arity) (fields ruleInstance goal proofs site tail saved returned jobs) =
      encodeTask (.close goal ruleInstance (premises jobs) site) := by
  simp only [closeTemplate, Indexed.instantiate_append, literals, Indexed.instantiate_literals,
    Indexed.instantiate_hole, Indexed.instantiate_literal, Indexed.instantiate_nil,
    fields_base, premise_instantiates]
  change [4,3,1,2,4] ++ (encodeWith CertificateDataEncoding.patternCodec goal ++
      4 :: (encodeWith CertificateDataEncoding.instanceCodec ruleInstance ++ 4 :: [])) ++
    encodeWith (Codec.list CertificateDataEncoding.patternCodec) (premises jobs) ++
      4 :: (encodeWith originCodec site.origin ++ (encodeWith (Codec.list Codec.nat) site.path ++ [])) = _
  simp only [encodeTask, encodeWith, taskCodec, putTask, siteCodec, Codec.mapped, Codec.prod, encodeData_pair,
    List.append_nil, List.cons_append, List.nil_append, List.append_assoc]
  rw [show encodeData (.atom 1) = ([3,1,2] : List Alphabet) from rfl]
  rfl

theorem queue_instantiates {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    Indexed.instantiate (queueTemplate arity) (fields ruleInstance goal proofs site tail saved returned jobs) =
      1 :: encodePacket (visits site jobs ++ .close goal ruleInstance (premises jobs) site :: tail, (returned, saved)) := by
  simp only [queueTemplate, Indexed.instantiate_append, literals, Indexed.instantiate_literals,
    child_work_instantiates, close_instantiates, Indexed.instantiate_literal,
    Indexed.instantiate_hole, Indexed.instantiate_nil, fields_base]
  change [1,4] ++ BinaryListAppend.stem taskCodec (visits site jobs) ++ [4] ++
    encodeTask (.close goal ruleInstance (premises jobs) site) ++
    (encodeWork tail ++ 4 :: (encodeRoots returned ++ (encodeRoots saved ++ []))) = _
  have joined := BinaryListAppend.original_append taskCodec (visits site jobs)
    (.close goal ruleInstance (premises jobs) site :: tail)
  rw [BinaryListAppend.encode_cons] at joined
  change BinaryListAppend.stem taskCodec (visits site jobs) ++
    4 :: (encodeTask (.close goal ruleInstance (premises jobs) site) ++ encodeWork tail) =
      encodeWork (visits site jobs ++ .close goal ruleInstance (premises jobs) site :: tail) at joined
  have packet : encodePacket (visits site jobs ++ .close goal ruleInstance (premises jobs) site :: tail, (returned, saved)) =
      4 :: (encodeWork (visits site jobs ++ .close goal ruleInstance (premises jobs) site :: tail) ++
        4 :: (encodeRoots returned ++ encodeRoots saved)) := by
    simp only [encodePacket, packetCodec, encodeWith, Codec.prod, encodeData_pair, encodeWork, workCodec, encodeRoots]
  rw [packet, ← joined]
  simp only [List.append_nil, List.cons_append, List.nil_append, List.append_assoc]

noncomputable def queueOutputs {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    TM2OutputsInTime (Indexed.machine (queueTemplate arity))
      (Indexed.argumentWire (fields ruleInstance goal proofs site tail saved returned jobs))
      (some ((1 : Alphabet) :: encodePacket (visits site jobs ++ .close goal ruleInstance (premises jobs) site :: tail, (returned, saved))))
      (4 * ((queueTemplate arity).length + 1) *
        ((Indexed.argumentWire (fields ruleInstance goal proofs site tail saved returned jobs)).length + 1)) := by
  have run := Indexed.outputs (queueTemplate arity) (fields ruleInstance goal proofs site tail saved returned jobs)
  rw [queue_instantiates] at run
  exact run

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Fields

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef

abbrev Alphabet := Binary.Alphabet
abbrev identityMachine := WordHomomorphismMachine.machine (fun symbol : Alphabet => [symbol])
def accept (symbol : Alphabet) := decide (symbol = 1)
def stripMachine := StackMachineComposition.Dispatch.machine identityMachine accept [(0 : Alphabet)]
local instance : Fintype ((CertificateDataTraversal.ProductField.machine true).Γ
    (CertificateDataTraversal.ProductField.machine true).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((CertificateDataTraversal.ProductField.machine true).Γ
    (CertificateDataTraversal.ProductField.machine true).k₁) := inferInstanceAs (Inhabited Alphabet)
local instance (second : Bool) : Fintype ((CertificateDataTraversal.ProductField.machine second).Γ
    (CertificateDataTraversal.ProductField.machine second).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (second : Bool) : Inhabited ((CertificateDataTraversal.ProductField.machine second).Γ
    (CertificateDataTraversal.ProductField.machine second).k₁) := inferInstanceAs (Inhabited Alphabet)

def machine (second : Bool) := StackMachineComposition.machine
  (CertificateDataTraversal.ProductField.machine second) stripMachine (Equiv.refl Alphabet)

noncomputable def outputs (second : Bool) (first last : Data) :
    TM2OutputsInTime (machine second) (encodeData (.pair first last))
      (some (encodeData (CertificateDataTraversal.ProductField.selected second first last)))
      (10 * ((encodeData (.pair first last)).length + 1)) := by
  let selected := CertificateDataTraversal.ProductField.selected second first last
  have parsed := (CertificateDataTraversal.ProductField.computable second).outputsFun (first,last)
  change TM2OutputsInTime (CertificateDataTraversal.ProductField.machine second)
    ((encodeData (.pair first last)).map id) (some ((1 :: encodeData selected).map id)) _ at parsed
  simp only [CertificateDataTraversal.ProductField.computable, List.map_id,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at parsed
  have copied := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (encodeData selected)
  simp only [List.flatMap_singleton'] at copied
  have stripped := StackMachineComposition.Dispatch.outputs_success identityMachine accept [(0 : Alphabet)]
    (1 : Alphabet) (encodeData selected) (encodeData selected) _ (by decide) copied
  have joined := StackMachineComposition.outputs (CertificateDataTraversal.ProductField.machine second)
    stripMachine (Equiv.refl Alphabet) (encodeData (.pair first last))
    ((1 : Alphabet) :: encodeData selected) (encodeData selected) _ _ parsed (by
      change TM2OutputsInTime stripMachine ((1 :: encodeData selected).map id) _ _
      simpa only [stripMachine, List.map_id] using stripped)
  apply WordEqualityMachine.within joined
  have bounded : (encodeData selected).length ≤ (encodeData (.pair first last)).length := by
    cases second <;> dsimp [selected, CertificateDataTraversal.ProductField.selected] <;>
      simp only [encodeData_pair, List.length_cons, List.length_append] <;> omega
  simp only [List.length_cons]
  change 4 * (encodeData (.pair first last)).length + 3 +
    2 * ((encodeData selected).length + 1) + 2 +
      (2 * (encodeData selected).length + 2 * (encodeData selected).length + 2 + 1) ≤ _
  omega

def select : List Bool → Data → Option Data
  | [], data => some data
  | second :: rest, .pair first last => select rest (if second then last else first)
  | _ :: _, .atom _ => none

/-- Endpoint alphabets accompany a composed parser without enumerating data. -/
structure Program where
  tm : FinTM2
  input : Alphabet ≃ tm.Γ tm.k₀
  output : tm.Γ tm.k₁ ≃ Alphabet

namespace Program

@[instance_reducible] def outputFinite (program : Program) : Fintype (program.tm.Γ program.tm.k₁) :=
  Fintype.ofEquiv Alphabet program.output.symm
@[instance_reducible] def outputInhabited (program : Program) : Inhabited (program.tm.Γ program.tm.k₁) := ⟨program.output.symm 0⟩
local instance (program : Program) : Fintype (program.tm.Γ program.tm.k₁) := outputFinite program
local instance (program : Program) : Inhabited (program.tm.Γ program.tm.k₀) := ⟨program.input 0⟩
local instance (program : Program) : Inhabited (program.tm.Γ program.tm.k₁) := outputInhabited program

def append (first last : Program) : Program :=
  { tm := @StackMachineComposition.machine first.tm last.tm (outputFinite first) (outputInhabited first)
      (first.output.trans last.input)
    input := first.input
    output := last.output }

abbrev Runs (program : Program) (input output : List Alphabet) (clock : Nat) : Type :=
  TM2OutputsInTime program.tm (input.map program.input.toFun) (some (output.map program.output.invFun)) clock

noncomputable def append_runs (first last : Program) (input middle output : List Alphabet) (firstClock lastClock : Nat)
    (ranFirst : Runs first input middle firstClock) (ranLast : Runs last middle output lastClock) :
    Runs (append first last) input output (firstClock + 2 * middle.length + 2 + lastClock) := by
  have joined := @StackMachineComposition.outputs first.tm last.tm (outputFinite first) (outputInhabited first)
    (first.output.trans last.input)
    (input.map first.input.toFun) (middle.map first.output.invFun) (output.map last.output.invFun)
    firstClock lastClock ranFirst (by
      have mapped : (middle.map first.output.invFun).map (first.output.trans last.input) =
          middle.map last.input.toFun := by
        rw [List.map_map]
        congr 1
        funext symbol
        exact congrArg last.input.toFun (first.output.right_inv symbol)
      rw [mapped]
      exact ranLast)
  simpa only [append, Runs, List.length_map] using joined

end Program

local instance (second : Bool) : Fintype ((machine second).Γ (machine second).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (second : Bool) : Inhabited ((machine second).Γ (machine second).k₁) := inferInstanceAs (Inhabited Alphabet)

def identityProgram : Program := ⟨identityMachine, Equiv.refl Alphabet, Equiv.refl Alphabet⟩
def fieldProgram (second : Bool) : Program := ⟨machine second, Equiv.refl Alphabet, Equiv.refl Alphabet⟩

/-- Paths are compiled finite selector descriptors. Original data stays on stacks. -/
def pathProgram : List Bool → Program
  | [] => identityProgram
  | second :: rest => (fieldProgram second).append (pathProgram rest)

noncomputable def pathOutputs (path : List Bool) (data selected : Data) (found : select path data = some selected) :
    Program.Runs (pathProgram path) (encodeData data) (encodeData selected)
      ((12 * path.length + 4) * ((encodeData data).length + 1)) := by
  induction path generalizing data with
  | nil =>
      have same := Option.some.inj found
      subst selected
      have run := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (encodeData data)
      simp only [List.flatMap_singleton'] at run
      change TM2OutputsInTime identityMachine ((encodeData data).map id)
        (some ((encodeData data).map id)) _
      simp only [List.map_id]
      apply WordEqualityMachine.within run
      simp only [List.length_nil]
      omega
  | cons second path ih =>
      cases data with
      | atom value => simp [select] at found
      | pair first last =>
          let middle := if second then last else first
          have rest := ih middle found
          have firstRun := outputs second first last
          have selectedEq : CertificateDataTraversal.ProductField.selected second first last = middle := by cases second <;> rfl
          rw [selectedEq] at firstRun
          have joined := Program.append_runs (fieldProgram second) (pathProgram path)
            (encodeData (.pair first last)) (encodeData middle) (encodeData selected)
            (10 * ((encodeData (.pair first last)).length + 1))
            ((12 * path.length + 4) * ((encodeData middle).length + 1))
            (by
              change TM2OutputsInTime (machine second) ((encodeData (.pair first last)).map id)
                (some ((encodeData middle).map id)) _
              simpa only [List.map_id] using firstRun) rest
          apply WordEqualityMachine.within joined
          have bounded : (encodeData middle).length ≤ (encodeData (.pair first last)).length := by
            cases second <;> simp only [middle, Bool.false_eq_true, ↓reduceIte, encodeData_pair, List.length_cons, List.length_append] <;> omega
          simp only [List.length_cons]
          nlinarith

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Fields

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Fields

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary

attribute [local implicit_reducible] StackMachineComposition.machine Indexed.machine

local instance (path : List Bool) : Fintype ((pathProgram path).tm.Γ (pathProgram path).tm.k₁) :=
  Program.outputFinite (pathProgram path)
local instance (path : List Bool) : Inhabited ((pathProgram path).tm.Γ (pathProgram path).tm.k₁) :=
  Program.outputInhabited (pathProgram path)
local instance (path : List Bool) : Inhabited ((pathProgram path).tm.Γ (pathProgram path).tm.k₀) :=
  ⟨(pathProgram path).input.toFun 0⟩

local instance {arity : Nat} (template : Indexed.Template Alphabet arity) :
    Fintype ((Indexed.machine template).Γ (Indexed.machine template).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (template : Indexed.Template Alphabet arity) :
    Inhabited ((Indexed.machine template).Γ (Indexed.machine template).k₁) := inferInstanceAs (Inhabited Alphabet)

/-- A physical indexed selector feeds the original-data selector chain. -/
abbrev fieldPath {arity : Nat} (index : Fin arity) (path : List Bool) :=
  StackMachineComposition.machine (Indexed.machine ([.inr index] : Indexed.Template Alphabet arity))
    (pathProgram path).tm (pathProgram path).input

local instance {arity : Nat} (index : Fin arity) (path : List Bool) :
    Fintype ((fieldPath index path).Γ (fieldPath index path).k₁) := Program.outputFinite (pathProgram path)
local instance {arity : Nat} (index : Fin arity) (path : List Bool) :
    Inhabited ((fieldPath index path).Γ (fieldPath index path).k₁) := Program.outputInhabited (pathProgram path)
local instance {arity : Nat} (index : Fin arity) (path : List Bool) :
    Inhabited ((fieldPath index path).Γ (fieldPath index path).k₀) := ⟨none⟩

def fieldClock (path : List Bool) (inputLength fieldLength : Nat) :=
  8 * (inputLength + 1) + 2 * fieldLength + 2 + (12 * path.length + 4) * (fieldLength + 1)

noncomputable def fieldPathOutputs {arity : Nat} (index : Fin arity) (path : List Bool)
    (fields : Fin arity → List Alphabet) (data selected : Data)
    (original : fields index = encodeData data) (found : select path data = some selected) :
    TM2OutputsInTime (fieldPath index path) (Indexed.argumentWire fields)
      (some ((encodeData selected).map (pathProgram path).output.invFun))
      (fieldClock path (Indexed.argumentWire fields).length (encodeData data).length) := by
  have picked := Indexed.outputs ([.inr index] : Indexed.Template Alphabet arity) fields
  simp only [Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil, List.length_cons,
    List.length_nil] at picked
  rw [original] at picked
  have parsed := pathOutputs path data selected found
  have joined := StackMachineComposition.outputs
    (Indexed.machine ([.inr index] : Indexed.Template Alphabet arity))
    (pathProgram path).tm (pathProgram path).input (Indexed.argumentWire fields)
    (encodeData data) ((encodeData selected).map (pathProgram path).output.invFun) _ _ picked parsed
  exact joined

/-- Every original input field is retained. Only a physically selected original
subtree is appended as the new field. -/
abbrev retainingPath {arity : Nat} (index : Fin arity) (path : List Bool) :=
  RetainedWordExecution.WithOutput.Framed.machine (fieldPath index path)
    (Equiv.refl (Option Alphabet)) (pathProgram path).output

theorem argumentWire_snoc {arity : Nat} (fields : Fin arity → List Alphabet) (word : List Alphabet) :
    Indexed.argumentWire (Fin.snoc fields word) = Indexed.argumentWire fields ++ word.map some ++ [none] := by
  simp only [Indexed.argumentWire, ← List.ofFn_eq_map]
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, Indexed.frame,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

noncomputable def retainingOutputs {arity : Nat} (index : Fin arity) (path : List Bool)
    (fields : Fin arity → List Alphabet) (data selected : Data)
    (original : fields index = encodeData data) (found : select path data = some selected) :
    TM2OutputsInTime (retainingPath index path) (Indexed.argumentWire fields)
      (some (Indexed.argumentWire (Fin.snoc fields (encodeData selected))))
      (fieldClock path (Indexed.argumentWire fields).length (encodeData data).length +
        23 * (Indexed.argumentWire fields).length + 22 * (encodeData selected).length + 23) := by
  have parsed := fieldPathOutputs index path fields data selected original found
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (fieldPath index path)
    (Equiv.refl (Option Alphabet)) (pathProgram path).output (Indexed.argumentWire fields)
    ((encodeData selected).map (pathProgram path).output.invFun) _ parsed
  have wordEq : RetainedWordExecution.WithOutput.Framed.outputWord (fieldPath index path)
      (Equiv.refl (Option Alphabet)) (pathProgram path).output (Indexed.argumentWire fields)
      ((encodeData selected).map (pathProgram path).output.invFun) =
        Indexed.argumentWire (Fin.snoc fields (encodeData selected)) := by
    rw [argumentWire_snoc]
    change (Indexed.argumentWire fields).map id ++
      ((encodeData selected).map (pathProgram path).output.invFun).map
        (fun symbol => some ((pathProgram path).output.toFun symbol)) ++ [none] = _
    simp only [List.map_id, List.map_map]
    congr 2
    congr 1
    funext symbol
    exact congrArg some ((pathProgram path).output.right_inv symbol)
  rw [wordEq] at retained
  simpa only [List.length_map] using retained

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Fields

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary

/-- Composed physical packet programs retain literal external delimiters. -/
structure PacketProgram where
  tm : FinTM2
  input : Option Alphabet ≃ tm.Γ tm.k₀
  output : tm.Γ tm.k₁ ≃ Option Alphabet

namespace PacketProgram
@[instance_reducible] def outputFinite (program : PacketProgram) : Fintype (program.tm.Γ program.tm.k₁) :=
  Fintype.ofEquiv (Option Alphabet) program.output.symm
@[instance_reducible] def outputInhabited (program : PacketProgram) : Inhabited (program.tm.Γ program.tm.k₁) :=
  ⟨program.output.invFun none⟩

def append (first last : PacketProgram) : PacketProgram :=
  { tm := @StackMachineComposition.machine first.tm last.tm (outputFinite first) (outputInhabited first)
      (first.output.trans last.input)
    input := first.input
    output := last.output }

abbrev Runs (program : PacketProgram) (input output : List (Option Alphabet)) (clock : Nat) : Type :=
  TM2OutputsInTime program.tm (input.map program.input.toFun) (some (output.map program.output.invFun)) clock

noncomputable def append_runs (first last : PacketProgram) (input middle output : List (Option Alphabet))
    (firstClock lastClock : Nat) (ranFirst : Runs first input middle firstClock)
    (ranLast : Runs last middle output lastClock) :
    Runs (append first last) input output (firstClock + 2 * middle.length + 2 + lastClock) := by
  have joined := @StackMachineComposition.outputs first.tm last.tm (outputFinite first) (outputInhabited first)
    (first.output.trans last.input) (input.map first.input.toFun) (middle.map first.output.invFun)
    (output.map last.output.invFun) firstClock lastClock ranFirst (by
      have mapped : (middle.map first.output.invFun).map (first.output.trans last.input) =
          middle.map last.input.toFun := by
        rw [List.map_map]
        congr 1
        funext symbol
        exact congrArg last.input.toFun (first.output.right_inv symbol)
      rw [mapped]
      exact ranLast)
  simpa only [append, Runs, List.length_map] using joined

end PacketProgram

namespace Node
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

def initialFields (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) : Fin 4 → Word :=
  ![encodeTask (.visit goal (.node ruleInstance proofs) site), encodeWork tail,
    encodeRoots saved, encodeRoots returned]

def instancePath : List Bool := [true,true,false,true,false]
def goalPath : List Bool := [true,false]
def childrenPath : List Bool := [true,true,false,true,true]
def originPath : List Bool := [true,true,true,false]
def sitePath : List Bool := [true,true,true,true]

theorem putProofs_original (proofs : List RawOpenProof) :
    CertificateDataEncoding.putProofs proofs = (Codec.list CertificateDataEncoding.proofCodec).put proofs := by
  induction proofs with
  | nil => rfl
  | cons proof proofs ih => simp only [CertificateDataEncoding.putProofs, Codec.list, Codec.putList, ih]; rfl

theorem selects_instance (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) :
    Fields.select instancePath (putTask (.visit goal (.node ruleInstance proofs) site)) =
      some (CertificateDataEncoding.instanceCodec.put ruleInstance) := rfl

theorem selects_goal (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) :
    Fields.select goalPath (putTask (.visit goal (.node ruleInstance proofs) site)) =
      some (CertificateDataEncoding.patternCodec.put goal) := rfl

theorem selects_children (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) :
    Fields.select childrenPath (putTask (.visit goal (.node ruleInstance proofs) site)) =
      some ((Codec.list CertificateDataEncoding.proofCodec).put proofs) := by
  change some (CertificateDataEncoding.putProofs proofs) = _
  rw [putProofs_original]

theorem selects_origin (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) :
    Fields.select originPath (putTask (.visit goal (.node ruleInstance proofs) site)) = some (originCodec.put site.origin) := rfl

theorem selects_site (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) :
    Fields.select sitePath (putTask (.visit goal (.node ruleInstance proofs) site)) =
      some ((Codec.list Codec.nat).put site.path) := rfl

def retainingProgram {arity : Nat} (index : Fin arity) (path : List Bool) : PacketProgram :=
  ⟨Fields.retainingPath index path, Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩

def retainClock {arity : Nat} (path : List Bool) (fields : Fin arity → Word) (original selected : Data) : Nat :=
  Fields.fieldClock path (Indexed.argumentWire fields).length (encodeData original).length +
    23 * (Indexed.argumentWire fields).length + 22 * (encodeData selected).length + 23

noncomputable def retainingProgramOutputs {arity : Nat} (index : Fin arity) (path : List Bool)
    (fields : Fin arity → Word) (data selected : Data) (original : fields index = encodeData data)
    (found : Fields.select path data = some selected) :
    PacketProgram.Runs (retainingProgram index path) (Indexed.argumentWire fields)
      (Indexed.argumentWire (Fin.snoc fields (encodeData selected))) (retainClock path fields data selected) := by
  change TM2OutputsInTime (Fields.retainingPath index path) ((Indexed.argumentWire fields).map id)
    (some ((Indexed.argumentWire (Fin.snoc fields (encodeData selected))).map id)) _
  simpa only [List.map_id, retainClock] using Fields.retainingOutputs index path fields data selected original found

end Node
end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

/-- Source values describe the wire contract; they are absent from control metadata. -/
structure Input where
  ruleInstance : RuleInstance
  goal : Pattern
  proofs : List RawOpenProof
  site : Site
  tail : List Task
  saved : List Nat
  returned : List Nat

def originalData (input : Input) := putTask (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
def startFields (input : Input) : Fin 4 → Word :=
  initialFields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned

def instanceFields (input : Input) : Fin 5 → Word := Fin.snoc (startFields input) (encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance)
def goalFields (input : Input) : Fin 6 → Word := Fin.snoc (instanceFields input) (encodeWith CertificateDataEncoding.patternCodec input.goal)
def childrenFields (input : Input) : Fin 7 → Word := Fin.snoc (goalFields input) (encodeWith (Codec.list CertificateDataEncoding.proofCodec) input.proofs)
def originFields (input : Input) : Fin 8 → Word := Fin.snoc (childrenFields input) (encodeWith originCodec input.site.origin)
def siteFields (input : Input) : Fin 9 → Word := Fin.snoc (originFields input) (encodeWith (Codec.list Codec.nat) input.site.path)

def extractProgram : PacketProgram :=
  (retainingProgram (0 : Fin 4) instancePath).append
    ((retainingProgram (0 : Fin 5) goalPath).append
      ((retainingProgram (0 : Fin 6) childrenPath).append
        ((retainingProgram (0 : Fin 7) originPath).append
          (retainingProgram (0 : Fin 8) sitePath))))

def extractClock (input : Input) : Nat :=
  retainClock instancePath (startFields input) (originalData input) (CertificateDataEncoding.instanceCodec.put input.ruleInstance) +
  2 * (Indexed.argumentWire (instanceFields input)).length + 2 +
  (retainClock goalPath (instanceFields input) (originalData input) (CertificateDataEncoding.patternCodec.put input.goal) +
  2 * (Indexed.argumentWire (goalFields input)).length + 2 +
  (retainClock childrenPath (goalFields input) (originalData input) ((Codec.list CertificateDataEncoding.proofCodec).put input.proofs) +
  2 * (Indexed.argumentWire (childrenFields input)).length + 2 +
  (retainClock originPath (childrenFields input) (originalData input) (originCodec.put input.site.origin) +
  2 * (Indexed.argumentWire (originFields input)).length + 2 +
  retainClock sitePath (originFields input) (originalData input) ((Codec.list Codec.nat).put input.site.path))))

noncomputable def extractOutputs (input : Input) :
    PacketProgram.Runs extractProgram (Indexed.argumentWire (startFields input))
      (Indexed.argumentWire (siteFields input)) (extractClock input) := by
  have first := retainingProgramOutputs (0 : Fin 4) instancePath (startFields input) (originalData input)
    (CertificateDataEncoding.instanceCodec.put input.ruleInstance) (by rfl)
    (selects_instance input.ruleInstance input.goal input.proofs input.site)
  have second := retainingProgramOutputs (0 : Fin 5) goalPath (instanceFields input) (originalData input)
    (CertificateDataEncoding.patternCodec.put input.goal) (by rfl)
    (selects_goal input.ruleInstance input.goal input.proofs input.site)
  have third := retainingProgramOutputs (0 : Fin 6) childrenPath (goalFields input) (originalData input)
    ((Codec.list CertificateDataEncoding.proofCodec).put input.proofs) (by rfl)
    (selects_children input.ruleInstance input.goal input.proofs input.site)
  have fourth := retainingProgramOutputs (0 : Fin 7) originPath (childrenFields input) (originalData input)
    (originCodec.put input.site.origin) (by rfl)
    (selects_origin input.ruleInstance input.goal input.proofs input.site)
  have fifth := retainingProgramOutputs (0 : Fin 8) sitePath (originFields input) (originalData input)
    ((Codec.list Codec.nat).put input.site.path) (by rfl)
    (selects_site input.ruleInstance input.goal input.proofs input.site)
  have lastTwo := PacketProgram.append_runs _ _ _ _ _ _ _ fourth fifth
  have lastThree := PacketProgram.append_runs _ _ _ _ _ _ _ third lastTwo
  have lastFour := PacketProgram.append_runs _ _ _ _ _ _ _ second lastThree
  have allFive := PacketProgram.append_runs _ _ _ _ _ _ _ first lastFour
  exact allFive

/-- Reordering is an executed field selection, including repeated opaque bytes. -/
def nodeIndices : List (Fin 9) := [4,5,6,7,8,1,2,3]
def rawFields (input : Input) : Fin 8 → Word :=
  ![encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance,
    encodeWith CertificateDataEncoding.patternCodec input.goal,
    encodeWith (Codec.list CertificateDataEncoding.proofCodec) input.proofs,
    encodeWith originCodec input.site.origin, encodeWith (Codec.list Codec.nat) input.site.path,
    encodeWork input.tail, encodeRoots input.saved, encodeRoots input.returned]


attribute [local implicit_reducible] FramedFieldSelection.machine

def reorderProgram : PacketProgram :=
  ⟨FramedFieldSelection.machine (Γ := Alphabet) nodeIndices,
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩

def prepareProgram := extractProgram.append reorderProgram

def prepareClock (input : Input) : Nat :=
  extractClock input + 2 * (Indexed.argumentWire (siteFields input)).length + 2 +
    (8 * nodeIndices.length + 12) * ((Indexed.argumentWire (siteFields input)).length + 1)

noncomputable def reorderOutputs (input : Input) :
    PacketProgram.Runs reorderProgram (Indexed.argumentWire (siteFields input))
      (Indexed.argumentWire (rawFields input))
      ((8 * nodeIndices.length + 12) * ((Indexed.argumentWire (siteFields input)).length + 1)) := by
  have selected := FramedFieldSelection.outputs nodeIndices (siteFields input)
  have same : Indexed.frame (nodeIndices.map (siteFields input)) = Indexed.argumentWire (rawFields input) := by
    rfl
  rw [same] at selected
  change TM2OutputsInTime (FramedFieldSelection.machine nodeIndices) ((Indexed.argumentWire (siteFields input)).map id)
    (some ((Indexed.argumentWire (rawFields input)).map id)) _
  simpa only [List.map_id] using selected

/-- The whole extraction starts on the original visit-node task and physically
retains the exact pending tail and both chronological root lists. -/
noncomputable def prepareOutputs (input : Input) :
    PacketProgram.Runs prepareProgram (Indexed.argumentWire (startFields input))
      (Indexed.argumentWire (rawFields input)) (prepareClock input) :=
  PacketProgram.append_runs extractProgram reorderProgram _ _ _ _ _ (extractOutputs input) (reorderOutputs input)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] FramedFieldSelection.machine WordTemplateMachine.machine
  StackMachineComposition.machine BinaryListAppend.rawStemMachine

def pathSelector := FramedFieldSelection.machine (Γ := Alphabet) ([4] : List (Fin 8))
def nilTemplate : WordTemplateMachine.Template (Option Alphabet) := [none,some (some 3),some (some 2),some none]

attribute [local implicit_reducible] pathSelector
local instance : Fintype (pathSelector.Γ pathSelector.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (pathSelector.Γ pathSelector.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype ((WordTemplateMachine.machine nilTemplate).Γ (WordTemplateMachine.machine nilTemplate).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((WordTemplateMachine.machine nilTemplate).Γ (WordTemplateMachine.machine nilTemplate).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def pathPairMachine := StackMachineComposition.machine pathSelector (WordTemplateMachine.machine nilTemplate)
  (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] pathPairMachine
local instance : Fintype (pathPairMachine.Γ pathPairMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (pathPairMachine.Γ pathPairMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def pathStemMachine := StackMachineComposition.machine pathPairMachine BinaryListAppend.rawStemMachine (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] pathStemMachine
local instance : Fintype (pathStemMachine.Γ pathStemMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (pathStemMachine.Γ pathStemMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (pathStemMachine.Γ pathStemMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def selectedPath (input : Input) := Indexed.frame [encodeWith (Codec.list Codec.nat) input.site.path]
def pairedPath (input : Input) := BinaryListAppend.inputWire Codec.nat input.site.path []
def pathPairClock (input : Input) :=
  20 * ((Indexed.argumentWire (rawFields input)).length + 1) +
  2 * (selectedPath input).length + 2 + 20 * ((selectedPath input).length + 1)
def pathStemClock (input : Input) := pathPairClock input + 2 * (pairedPath input).length + 2 + 80 * ((pairedPath input).length + 1)

noncomputable def pathPairOutputs (input : Input) :
    TM2OutputsInTime pathPairMachine (Indexed.argumentWire (rawFields input))
      (some (pairedPath input)) (pathPairClock input) := by
  have selected := FramedFieldSelection.outputs ([4] : List (Fin 8)) (rawFields input)
  have same : Indexed.frame (([4] : List (Fin 8)).map (rawFields input)) = selectedPath input := rfl
  rw [same] at selected
  have paired := WordTemplateMachine.outputs nilTemplate (selectedPath input)
  have constructed : WordTemplateMachine.instantiate nilTemplate (selectedPath input) = pairedPath input := by
    simp only [nilTemplate, WordTemplateMachine.instantiate_hole, WordTemplateMachine.instantiate_literal,
      WordTemplateMachine.instantiate_nil]
    simp [selectedPath, pairedPath, BinaryListAppend.inputWire, BinaryListAppend.fields,
      Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.append_assoc]
    rfl
  rw [constructed] at paired
  have joined := StackMachineComposition.outputs pathSelector (WordTemplateMachine.machine nilTemplate)
    (Equiv.refl (Option Alphabet)) (Indexed.argumentWire (rawFields input)) (selectedPath input)
    (pairedPath input) _ _ selected (by
      change TM2OutputsInTime (WordTemplateMachine.machine nilTemplate) ((selectedPath input).map id) _ _
      simpa only [List.map_id] using paired)
  exact joined

noncomputable def pathStemOutputs (input : Input) :
    TM2OutputsInTime pathStemMachine (Indexed.argumentWire (rawFields input))
      (some (BinaryListAppend.stem Codec.nat input.site.path)) (pathStemClock input) := by
  have stem := BinaryListAppend.rawStemOutputs Codec.nat input.site.path []
  exact StackMachineComposition.outputs pathPairMachine BinaryListAppend.rawStemMachine (Equiv.refl (Option Alphabet))
    (Indexed.argumentWire (rawFields input)) (pairedPath input) (BinaryListAppend.stem Codec.nat input.site.path)
    _ _ (pathPairOutputs input) (by
      change TM2OutputsInTime BinaryListAppend.rawStemMachine ((pairedPath input).map id) _ _
      simpa only [List.map_id, pairedPath] using stem)

def stemProgram : PacketProgram :=
  ⟨RetainedWordExecution.WithOutput.Framed.machine pathStemMachine (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩

def stemFields (input : Input) : Fin 9 → Word := Fin.snoc (rawFields input) (BinaryListAppend.stem Codec.nat input.site.path)
def stemClock (input : Input) := pathStemClock input + 23 * (Indexed.argumentWire (rawFields input)).length +
  22 * (BinaryListAppend.stem Codec.nat input.site.path).length + 23

noncomputable def stemOutputs (input : Input) :
    PacketProgram.Runs stemProgram (Indexed.argumentWire (rawFields input))
      (Indexed.argumentWire (stemFields input)) (stemClock input) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs pathStemMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (rawFields input))
    (BinaryListAppend.stem Codec.nat input.site.path) _ (pathStemOutputs input)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord pathStemMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (rawFields input))
      (BinaryListAppend.stem Codec.nat input.site.path) = Indexed.argumentWire (stemFields input) := by
    change (Indexed.argumentWire (rawFields input)).map id ++
      (BinaryListAppend.stem Codec.nat input.site.path).map some ++ [none] = _
    simpa only [List.map_id, stemFields] using (Fields.argumentWire_snoc (rawFields input)
      (BinaryListAppend.stem Codec.nat input.site.path)).symm
  rw [same] at retained
  change TM2OutputsInTime stemProgram.tm ((Indexed.argumentWire (rawFields input)).map id)
    (some ((Indexed.argumentWire (stemFields input)).map id)) _
  simpa only [List.map_id, stemClock, stemProgram] using retained

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

abbrev PairCell := OriginalChildJobs.PairCell
abbrev TaggedCell := Option Alphabet ⊕ PairCell
attribute [local implicit_reducible] FramedFieldSelection.machine NodeChildrenExecution.machine
  StackMachineComposition.machine WordHomomorphismMachine.machine RetainedWordExecution.WithOutput.machine

local instance : Inhabited PairCell := ⟨.inr false⟩
local instance (definition : CalculusLanguageDef) (arity : Nat) :
    Fintype ((NodeChildrenExecution.machine definition arity).Γ (NodeChildrenExecution.machine definition arity).k₁) :=
  inferInstanceAs (Fintype PairCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) :
    Inhabited ((NodeChildrenExecution.machine definition arity).Γ (NodeChildrenExecution.machine definition arity).k₁) :=
  inferInstanceAs (Inhabited PairCell)
local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9))).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9))).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def originalNode (definition : CalculusLanguageDef) (arity : Nat) :=
  StackMachineComposition.machine (FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9)))
    (NodeChildrenExecution.machine definition arity) (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] originalNode
local instance (definition : CalculusLanguageDef) (arity : Nat) : Fintype ((originalNode definition arity).Γ (originalNode definition arity).k₁) :=
  inferInstanceAs (Fintype PairCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((originalNode definition arity).Γ (originalNode definition arity).k₁) :=
  inferInstanceAs (Inhabited PairCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((originalNode definition arity).Γ (originalNode definition arity).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def originalNodeClock (definition : ValidatedCalculusLanguageDef) (input : Input) :=
  36 * ((Indexed.argumentWire (stemFields input)).length + 1) +
    2 * (NodeChildrenExecution.inputWire input.ruleInstance input.goal input.proofs).length + 2 +
      NodeChildrenExecution.clock definition input.ruleInstance input.goal input.proofs

noncomputable def originalNodeOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input) :
    TM2OutputsInTime (originalNode definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs))
      (originalNodeClock definition input) := by
  have selected := FramedFieldSelection.outputs ([0,1,2] : List (Fin 9)) (stemFields input)
  have same : Indexed.frame (([0,1,2] : List (Fin 9)).map (stemFields input)) =
      NodeChildrenExecution.inputWire input.ruleInstance input.goal input.proofs := rfl
  rw [same] at selected
  exact StackMachineComposition.outputs
    (FramedFieldSelection.machine (Γ := Alphabet) ([0,1,2] : List (Fin 9)))
    (NodeChildrenExecution.machine definition.1 arity) (Equiv.refl (Option Alphabet))
    (Indexed.argumentWire (stemFields input)) (NodeChildrenExecution.inputWire input.ruleInstance input.goal input.proofs)
    (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs) _ _ selected (by
      change TM2OutputsInTime (NodeChildrenExecution.machine definition.1 arity)
        ((NodeChildrenExecution.inputWire input.ruleInstance input.goal input.proofs).map id) _ _
      simpa only [List.map_id] using NodeChildrenExecution.outputs definition firstOrder arity input.ruleInstance input.goal input.proofs)

/-- The status is copied from the executed node machine. Each original pair
boundary is converted into separate goal and proof fields. -/
def pairImage : PairCell → List (Option Alphabet)
  | .inr accepted => [some (if accepted then 1 else 0),none]
  | .inl (some symbol) => [symbol]
  | .inl none => []

def retainedImage : TaggedCell → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr symbol => pairImage symbol

def preparedWire (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  Indexed.argumentWire (stemFields input) ++
    (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs).flatMap pairImage

def retainedNode (definition : CalculusLanguageDef) (arity : Nat) :=
  RetainedWordExecution.WithOutput.machine (originalNode definition arity)
attribute [local implicit_reducible] retainedNode
local instance (definition : CalculusLanguageDef) (arity : Nat) : Fintype ((retainedNode definition arity).Γ (retainedNode definition arity).k₁) :=
  inferInstanceAs (Fintype TaggedCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((retainedNode definition arity).Γ (retainedNode definition arity).k₁) :=
  inferInstanceAs (Inhabited TaggedCell)

def preparedMachine (definition : CalculusLanguageDef) (arity : Nat) :=
  StackMachineComposition.machine (retainedNode definition arity) (WordHomomorphismMachine.machine retainedImage)
    (Equiv.refl TaggedCell)

def taggedWire (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) : List TaggedCell :=
  (Indexed.argumentWire (stemFields input)).map Sum.inl ++
    (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs).map Sum.inr

def retainedClock (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  originalNodeClock definition input + 3 * (Indexed.argumentWire (stemFields input)).length +
    2 * (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs).length + 5

def preparedClock (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  retainedClock definition arity input + 2 * (taggedWire definition arity input).length + 2 +
    (2 * (taggedWire definition arity input).length + 2 * (preparedWire definition arity input).length + 2)

noncomputable def retainedOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input) :
    TM2OutputsInTime (retainedNode definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some (taggedWire definition arity input)) (retainedClock definition arity input) :=
  RetainedWordExecution.WithOutput.outputs (originalNode definition.1 arity)
    (Indexed.argumentWire (stemFields input))
    (NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs) _
    (originalNodeOutputs definition firstOrder arity input)

theorem image_exact (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :
    (taggedWire definition arity input).flatMap retainedImage = preparedWire definition arity input := by
  simp only [taggedWire, List.flatMap_append, List.flatMap_map, preparedWire]
  have original : (Indexed.argumentWire (stemFields input)).flatMap (fun symbol => retainedImage (.inl symbol)) =
      Indexed.argumentWire (stemFields input) := by
    simp only [retainedImage, List.flatMap_singleton']
  rw [original]
  rfl

noncomputable def projectedOutputs (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :
    TM2OutputsInTime (WordHomomorphismMachine.machine retainedImage) (taggedWire definition arity input)
      (some (preparedWire definition arity input))
      (2 * (taggedWire definition arity input).length + 2 * (preparedWire definition arity input).length + 2) := by
  have mapped := WordHomomorphismMachine.outputs retainedImage (taggedWire definition arity input)
  rw [image_exact] at mapped
  exact mapped

noncomputable def preparedOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input) :
    TM2OutputsInTime (preparedMachine definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some (preparedWire definition arity input)) (preparedClock definition arity input) := by
  have first := retainedOutputs definition firstOrder arity input
  have second := projectedOutputs definition arity input
  have joined := StackMachineComposition.outputs (retainedNode definition.1 arity)
    (WordHomomorphismMachine.machine retainedImage) (Equiv.refl TaggedCell)
    (Indexed.argumentWire (stemFields input)) (taggedWire definition arity input)
    (preparedWire definition arity input) (retainedClock definition arity input)
    (2 * (taggedWire definition arity input).length + 2 * (preparedWire definition arity input).length + 2)
    first (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine retainedImage)
        ((taggedWire definition arity input).map id) _ _
      simpa only [List.map_id] using second)
  exact joined

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

/-- Removing the pair-packet wrapper preserves every original job byte. -/
theorem pair_image_fields (cells : List (Option Alphabet)) :
    (cells.map FramedWordPairing.fieldCell).flatMap pairImage = cells := by
  simp only [List.flatMap_map, FramedWordPairing.fieldCell, pairImage, List.flatMap_singleton']

theorem pair_image_jobs (first second : List Word) :
    (FramedWordPairing.jobs first second).flatMap pairImage =
      (first.zip second).flatMap (fun pair => Indexed.frame [pair.1,pair.2]) := by
  simp only [FramedWordPairing.jobs, List.flatMap_assoc, FramedWordPairing.job,
    List.flatMap_append, pair_image_fields, List.flatMap_cons, List.flatMap_nil,
    FramedWordPairing.outerDelimiter, pairImage, List.append_nil]

theorem fields_list {arity : Nat} (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof)
    (site : Site) (tail : List Task) (saved returned : List Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    (List.finRange (10 + 2 * arity)).map (fields ruleInstance goal proofs site tail saved returned jobs) =
      (List.finRange 10).map (metadata ruleInstance goal proofs site tail saved returned) ++
        (List.finRange arity).flatMap (fun index =>
          [encodeWith CertificateDataEncoding.patternCodec (jobs index).1,
            CertificateDataEncoding.encodeProof (jobs index).2]) := by
  simp only [← List.ofFn_eq_map]
  rw [List.ofFn_add]
  have firstEq : (fun index : Fin 10 => fields ruleInstance goal proofs site tail saved returned jobs
      (index.castLE (Nat.le_add_right 10 (2 * arity)))) = metadata ruleInstance goal proofs site tail saved returned := by
    funext index
    exact fields_base ruleInstance goal proofs site tail saved returned jobs index
  rw [firstEq, List.ofFn_mul']
  congr 1
  rw [List.flatMap_def, ← List.ofFn_eq_map]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext index
  change [fields ruleInstance goal proofs site tail saved returned jobs _,
    fields ruleInstance goal proofs site tail saved returned jobs _] = _
  have firstIndex : (⟨2 * index.val + 0, by omega⟩ : Fin (2 * arity)).natAdd 10 = goalSlot index := by
    apply Fin.ext
    simp only [Fin.val_natAdd, goalSlot]
    omega
  have secondIndex : (⟨2 * index.val + 1, by omega⟩ : Fin (2 * arity)).natAdd 10 = proofSlot index := by
    apply Fin.ext
    simp only [Fin.val_natAdd, proofSlot]
    omega
  rw [firstIndex, secondIndex, fields_goal, fields_proof]

theorem wire_fields {arity : Nat} (input : Input) (jobs : Fin arity → Pattern × RawOpenProof) :
    Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs) =
      Indexed.argumentWire (stemFields input) ++ [some 1,none] ++
        ((List.finRange arity).map jobs).flatMap (fun pair => Indexed.frame
          [encodeWith CertificateDataEncoding.patternCodec pair.1, CertificateDataEncoding.encodeProof pair.2]) := by
  have first : Indexed.frame ((List.finRange 10).map
      (metadata input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned)) =
        Indexed.argumentWire (stemFields input) ++ [some 1,none] := by
    rw [stemFields, Fields.argumentWire_snoc]
    simp [Indexed.argumentWire, metadata, rawFields, Indexed.frame, List.finRange_succ, List.append_assoc]
  rw [Indexed.argumentWire, fields_list]
  have frameAppend (first last : List Word) : Indexed.frame (first ++ last) = Indexed.frame first ++ Indexed.frame last := by
    simp only [Indexed.frame, List.flatMap_append]
  rw [frameAppend, first]
  simp only [Indexed.frame, List.flatMap_assoc, List.flatMap_map]

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

abbrev GuardCell := Option Alphabet ⊕ Bool
attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  RetainedWordExecution.machine StackMachineComposition.Dispatch.machine WordHomomorphismMachine.machine

def queueStatusTemplate (arity : Nat) : Indexed.Template Alphabet (10 + 2 * arity) := [.inr (baseSlot arity 9)]
def acceptedStatus (symbol : Alphabet) : Bool := decide (symbol = 1)
local instance (arity : Nat) : Fintype ((Indexed.machine (queueStatusTemplate arity)).Γ (Indexed.machine (queueStatusTemplate arity)).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (arity : Nat) : Inhabited ((Indexed.machine (queueStatusTemplate arity)).Γ (Indexed.machine (queueStatusTemplate arity)).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def queueTagMachine (arity : Nat) := RetainedWordExecution.machine (Indexed.machine (queueStatusTemplate arity)) acceptedStatus
attribute [local implicit_reducible] queueTagMachine
local instance (arity : Nat) : Fintype ((queueTagMachine arity).Γ (queueTagMachine arity).k₁) := inferInstanceAs (Fintype GuardCell)
local instance (arity : Nat) : Inhabited ((queueTagMachine arity).Γ (queueTagMachine arity).k₁) := inferInstanceAs (Inhabited GuardCell)

def restoreImage : GuardCell → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr _ => []
local instance : Fintype ((WordHomomorphismMachine.machine restoreImage).Γ (WordHomomorphismMachine.machine restoreImage).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine restoreImage).Γ (WordHomomorphismMachine.machine restoreImage).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def queuePayloadMachine (arity : Nat) := StackMachineComposition.machine (WordHomomorphismMachine.machine restoreImage)
  (Indexed.machine (queueTemplate arity)) (Equiv.refl (Option Alphabet))
def acceptTag (symbol : GuardCell) : Bool := decide (symbol = .inr true)
def queueDispatch (arity : Nat) := StackMachineComposition.Dispatch.machine (queuePayloadMachine arity) acceptTag [(0 : Alphabet)]
def queueMachine (arity : Nat) := StackMachineComposition.machine (queueTagMachine arity) (queueDispatch arity) (Equiv.refl GuardCell)

def queueClock (arity inputLength : Nat) :=
  19 * inputLength + 23 + 4 * ((queueTemplate arity).length + 1) * (inputLength + 1)

noncomputable def queueTagOutputs {arity : Nat} (input : Input) (jobs : Fin arity → Pattern × RawOpenProof) :
    TM2OutputsInTime (queueTagMachine arity)
      (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs))
      (some (.inr true :: (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).map Sum.inl))
      (11 * (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).length + 14) := by
  let words := fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs
  have selected := Indexed.outputs (queueStatusTemplate arity) words
  have same : Indexed.instantiate (queueStatusTemplate arity) words = [(1 : Alphabet)] := by
    simp only [queueStatusTemplate, Indexed.instantiate_hole, Indexed.instantiate_nil,
      List.append_nil, words, fields_base]
    rfl
  rw [same] at selected
  have tagged := RetainedWordExecution.outputs (Indexed.machine (queueStatusTemplate arity)) acceptedStatus
    (Indexed.argumentWire words) (1 : Alphabet) [] _ selected
  apply WordEqualityMachine.within (show TM2OutputsInTime (queueTagMachine arity) (Indexed.argumentWire words)
    (some (.inr true :: (Indexed.argumentWire words).map Sum.inl)) _ from tagged)
  simp only [queueStatusTemplate, List.length_cons, List.length_nil, words]
  omega

noncomputable def queuePayloadOutputs {arity : Nat} (input : Input) (jobs : Fin arity → Pattern × RawOpenProof) :
    TM2OutputsInTime (queuePayloadMachine arity)
      ((Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).map Sum.inl)
      (some ((1 : Alphabet) :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
        (input.returned,input.saved))))
      (6 * (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).length + 4 +
        4 * ((queueTemplate arity).length + 1) * ((Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).length + 1)) := by
  let words := fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs
  have restored := WordHomomorphismMachine.outputs restoreImage ((Indexed.argumentWire words).map (Sum.inl : Option Alphabet → GuardCell))
  have same : ((Indexed.argumentWire words).map (Sum.inl : Option Alphabet → GuardCell)).flatMap restoreImage = Indexed.argumentWire words := by
    simp only [List.flatMap_map, restoreImage, List.flatMap_singleton']
  rw [same] at restored
  have ran := StackMachineComposition.outputs (WordHomomorphismMachine.machine restoreImage)
    (Indexed.machine (queueTemplate arity)) (Equiv.refl (Option Alphabet))
    ((Indexed.argumentWire words).map Sum.inl) (Indexed.argumentWire words)
    ((1 : Alphabet) :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
      (input.returned,input.saved))) _ _ restored (by
      change TM2OutputsInTime (Indexed.machine (queueTemplate arity)) ((Indexed.argumentWire words).map id) _ _
      simpa only [List.map_id] using queueOutputs input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)
  apply WordEqualityMachine.within ran
  simp only [List.length_map, words]
  omega

noncomputable def queueOutputsGuarded {arity : Nat} (input : Input) (jobs : Fin arity → Pattern × RawOpenProof) :
    TM2OutputsInTime (queueMachine arity)
      (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs))
      (some ((1 : Alphabet) :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
        (input.returned,input.saved))))
      (queueClock arity (Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs)).length) := by
  let words := fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs
  let output := 1 :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
    (input.returned,input.saved))
  have payload := queuePayloadOutputs input jobs
  have dispatched := StackMachineComposition.Dispatch.outputs_success (queuePayloadMachine arity) acceptTag [(0 : Alphabet)]
    (.inr true : GuardCell) ((Indexed.argumentWire words).map Sum.inl) output _ (by decide) payload
  have joined := StackMachineComposition.outputs (queueTagMachine arity) (queueDispatch arity) (Equiv.refl GuardCell)
    (Indexed.argumentWire words) (.inr true :: (Indexed.argumentWire words).map Sum.inl) output _ _
    (queueTagOutputs input jobs) (by
      change TM2OutputsInTime (queueDispatch arity) ((.inr true :: (Indexed.argumentWire words).map Sum.inl).map id) _ _
      simpa only [List.map_id, queueDispatch] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [queueClock, List.length_cons, List.length_map, words]
  omega

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

/-- The layout theorem uses the actual original successful rule application. -/
theorem original_positive (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (premiseCount : computedPremises.length = arity) (childCount : input.proofs.length = arity) :
    NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs =
      .inr true :: FramedWordPairing.jobs
        (computedPremises.map (encodeWith CertificateDataEncoding.patternCodec))
        (input.proofs.map CertificateDataEncoding.encodeProof) := by
  simp only [NodeChildrenExecution.resultWire, RuleNodeAdmission.result, accepted,
    Option.any_some, decide_true, ↓reduceIte, OriginalChildJobs.outputWire,
    OriginalChildJobs.fieldWords, premiseCount, childCount, FramedWordPairing.output,
    List.length_map, CertificateDataEncoding.encodeProof]

theorem prepared_positive {arity : Nat} (definition : ValidatedCalculusLanguageDef) (input : Input)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (premiseCount : computedPremises.length = arity) (childCount : input.proofs.length = arity)
    (jobs : Fin arity → Pattern × RawOpenProof)
    (originalJobs : (List.finRange arity).map jobs = computedPremises.zip input.proofs) :
    preparedWire definition arity input =
      Indexed.argumentWire (fields input.ruleInstance input.goal input.proofs input.site input.tail input.saved input.returned jobs) := by
  rw [preparedWire, original_positive definition arity input computedPremises accepted premiseCount childCount,
    wire_fields, originalJobs]
  simp only [List.flatMap_cons, pairImage, pair_image_jobs, List.zip_map, List.flatMap_map,
    ↓reduceIte, Prod.map, List.append_assoc]

attribute [local implicit_reducible] preparedMachine queueMachine StackMachineComposition.machine
local instance (definition : CalculusLanguageDef) (arity : Nat) : Fintype ((preparedMachine definition arity).Γ (preparedMachine definition arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((preparedMachine definition arity).Γ (preparedMachine definition arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def rowMachine (definition : CalculusLanguageDef) (arity : Nat) :=
  StackMachineComposition.machine (preparedMachine definition arity) (queueMachine arity) (Equiv.refl (Option Alphabet))

def rowClock (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  preparedClock definition arity input + 2 * (preparedWire definition arity input).length + 2 +
    queueClock arity (preparedWire definition arity input).length

noncomputable def rowOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (premiseCount : computedPremises.length = arity) (childCount : input.proofs.length = arity)
    (jobs : Fin arity → Pattern × RawOpenProof)
    (originalJobs : (List.finRange arity).map jobs = computedPremises.zip input.proofs) :
    TM2OutputsInTime (rowMachine definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some ((1 : Alphabet) :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
        (input.returned,input.saved)))) (rowClock definition arity input) := by
  have node := preparedOutputs definition firstOrder arity input
  have queue := queueOutputsGuarded input jobs
  have same := prepared_positive definition input computedPremises accepted premiseCount childCount jobs originalJobs
  rw [← same] at queue
  exact StackMachineComposition.outputs (preparedMachine definition.1 arity) (queueMachine arity)
    (Equiv.refl (Option Alphabet)) (Indexed.argumentWire (stemFields input)) (preparedWire definition arity input)
    ((1 : Alphabet) :: encodePacket (visits input.site jobs ++ .close input.goal input.ruleInstance (premises jobs) input.site :: input.tail,
      (input.returned,input.saved))) _ _ node (by
      change TM2OutputsInTime (queueMachine arity) ((preparedWire definition arity input).map id) _ _
      simpa only [List.map_id] using queue)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

variable {α : Type}
def listVector (items : List α) (count : Nat) (lengthEq : items.length = count) : Fin count → α :=
  fun index => items.get ⟨index.val, by omega⟩

theorem listVector_list (items : List α) (count : Nat) (lengthEq : items.length = count) :
    (List.finRange count).map (listVector items count lengthEq) = items := by
  cases lengthEq
  exact List.map_get_finRange items

def sourceJobs (computedPremises : List Pattern) (proofs : List RawOpenProof) (arity : Nat)
    (premiseCount : computedPremises.length = arity) (childCount : proofs.length = arity) : Fin arity → Pattern × RawOpenProof :=
  listVector (computedPremises.zip proofs) arity (by simp only [List.length_zip, premiseCount, childCount, Nat.min_self])

theorem sourceJobs_list (computedPremises : List Pattern) (proofs : List RawOpenProof) (arity : Nat)
    (premiseCount : computedPremises.length = arity) (childCount : proofs.length = arity) :
    (List.finRange arity).map (sourceJobs computedPremises proofs arity premiseCount childCount) = computedPremises.zip proofs :=
  listVector_list _ _ _

theorem children_finRange {arity : Nat} (site : Site) (offset : Nat) (jobs : Fin arity → Pattern × RawOpenProof) :
    children site offset ((List.finRange arity).map jobs) =
      (List.finRange arity).map (fun index => .visit (jobs index).1 (jobs index).2
        ⟨site.origin, site.path ++ [offset + index.val]⟩) := by
  induction arity generalizing offset with
  | zero => rfl
  | succ arity ih =>
      simp only [List.finRange_succ, List.map_cons, List.map_map]
      change .visit (jobs 0).1 (jobs 0).2 ⟨site.origin, site.path ++ [offset]⟩ ::
        children site (offset + 1) ((List.finRange arity).map (fun index => jobs index.succ)) = _
      rw [ih]
      simp only [Function.comp_def, Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc]
      congr 1
      apply congrArg (fun fn : Fin arity → Task => (List.finRange arity).map fn)
      funext index
      simp only [Nat.add_comm 1 index.val]

theorem visits_children {arity : Nat} (site : Site) (jobs : Fin arity → Pattern × RawOpenProof) :
    visits site jobs = children site 0 ((List.finRange arity).map jobs) := by
  simp only [visits, children_finRange, Nat.zero_add]

theorem sourceJobs_premises (computedPremises : List Pattern) (proofs : List RawOpenProof) (arity : Nat)
    (premiseCount : computedPremises.length = arity) (childCount : proofs.length = arity) :
    premises (sourceJobs computedPremises proofs arity premiseCount childCount) = computedPremises := by
  change (List.finRange arity).map (Prod.fst ∘ sourceJobs computedPremises proofs arity premiseCount childCount) = _
  rw [← List.map_map, sourceJobs_list]
  exact List.map_fst_zip (by omega)

def originalPacketProgram := prepareProgram.append stemProgram

def wholeMachine (definition : CalculusLanguageDef) (arity : Nat) :=
  @StackMachineComposition.machine originalPacketProgram.tm (rowMachine definition arity)
    (PacketProgram.outputFinite originalPacketProgram) (PacketProgram.outputInhabited originalPacketProgram)
    originalPacketProgram.output

def originalPacketClock (input : Input) := prepareClock input +
  2 * (Indexed.argumentWire (rawFields input)).length + 2 + stemClock input

def wholeClock (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input) :=
  originalPacketClock input + 2 * (Indexed.argumentWire (stemFields input)).length + 2 + rowClock definition arity input

noncomputable def originalPacketOutputs (input : Input) :
    PacketProgram.Runs originalPacketProgram (Indexed.argumentWire (startFields input))
      (Indexed.argumentWire (stemFields input)) (originalPacketClock input) :=
  PacketProgram.append_runs prepareProgram stemProgram _ _ _ _ _ (prepareOutputs input) (stemOutputs input)

noncomputable def wholeOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (premiseCount : computedPremises.length = arity) (childCount : input.proofs.length = arity) :
    TM2OutputsInTime (wholeMachine definition.1 arity) (Indexed.argumentWire (startFields input))
      (some ((1 : Alphabet) :: encodePacket
        (children input.site 0 (computedPremises.zip input.proofs) ++
          .close input.goal input.ruleInstance computedPremises input.site :: input.tail,
          (input.returned,input.saved)))) (wholeClock definition arity input) := by
  let jobs := sourceJobs computedPremises input.proofs arity premiseCount childCount
  have prepared := originalPacketOutputs input
  change TM2OutputsInTime originalPacketProgram.tm ((Indexed.argumentWire (startFields input)).map id)
    (some ((Indexed.argumentWire (stemFields input)).map id)) _ at prepared
  simp only [List.map_id] at prepared
  have row := rowOutputs definition firstOrder arity input computedPremises accepted premiseCount childCount jobs
    (sourceJobs_list computedPremises input.proofs arity premiseCount childCount)
  have visitsEq : visits input.site jobs = children input.site 0 (computedPremises.zip input.proofs) := by
    rw [visits_children, sourceJobs_list]
  have premisesEq : premises jobs = computedPremises := sourceJobs_premises _ _ _ _ _
  rw [visitsEq, premisesEq] at row
  exact @StackMachineComposition.outputs originalPacketProgram.tm (rowMachine definition.1 arity)
    (PacketProgram.outputFinite originalPacketProgram) (PacketProgram.outputInhabited originalPacketProgram)
    originalPacketProgram.output (Indexed.argumentWire (startFields input)) (Indexed.argumentWire (stemFields input))
    ((1 : Alphabet) :: encodePacket
      (children input.site 0 (computedPremises.zip input.proofs) ++
        .close input.goal input.ruleInstance computedPremises input.site :: input.tail,
        (input.returned,input.saved))) _ _ prepared (by
      change TM2OutputsInTime (rowMachine definition.1 arity) ((Indexed.argumentWire (stemFields input)).map id) _ _
      simpa only [List.map_id] using row)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  RetainedWordExecution.machine StackMachineComposition.Dispatch.machine queueTagMachine queueDispatch preparedMachine WordHomomorphismMachine.machine

local instance (arity : Nat) : Fintype ((Indexed.machine (queueStatusTemplate arity)).Γ (Indexed.machine (queueStatusTemplate arity)).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance (arity : Nat) : Inhabited ((Indexed.machine (queueStatusTemplate arity)).Γ (Indexed.machine (queueStatusTemplate arity)).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Fintype ((queueTagMachine arity).Γ (queueTagMachine arity).k₁) := inferInstanceAs (Fintype GuardCell)
local instance (arity : Nat) : Inhabited ((queueTagMachine arity).Γ (queueTagMachine arity).k₁) := inferInstanceAs (Inhabited GuardCell)
local instance (definition : CalculusLanguageDef) (arity : Nat) : Fintype ((preparedMachine definition arity).Γ (preparedMachine definition arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (definition : CalculusLanguageDef) (arity : Nat) : Inhabited ((preparedMachine definition arity).Γ (preparedMachine definition arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def refusedFields (input : Input) : Fin 10 → Word := Fin.snoc (stemFields input) [0]
def refusedWire (input : Input) := Indexed.argumentWire (refusedFields input)

theorem selector_refused (arity : Nat) (input : Input) :
    Indexed.instantiateWire (queueStatusTemplate arity) (refusedWire input) = [(0 : Alphabet)] := by
  simp only [queueStatusTemplate, Indexed.instantiateWire_hole, Indexed.instantiateWire_nil, List.append_nil]
  have selected := Indexed.select_frame (baseSlot arity 9) (⟨0, by omega⟩ : Fin (10 + 2 * arity + 1))
    ((List.finRange 10).map (refusedFields input)) (by simp only [List.length_map, List.length_finRange]; omega)
  change Indexed.select (baseSlot arity 9) ⟨0, by omega⟩ (Indexed.frame ((List.finRange 10).map (refusedFields input))) = _
  rw [selected]
  simp [baseSlot, refusedFields, Fin.snoc]

noncomputable def queueRefusedTagOutputs (arity : Nat) (input : Input) :
    TM2OutputsInTime (queueTagMachine arity) (refusedWire input)
      (some (.inr false :: (refusedWire input).map Sum.inl)) (11 * (refusedWire input).length + 14) := by
  have selected := Indexed.outputsWire (queueStatusTemplate arity) (refusedWire input)
  rw [selector_refused] at selected
  have tagged := RetainedWordExecution.outputs (Indexed.machine (queueStatusTemplate arity)) acceptedStatus
    (refusedWire input) (0 : Alphabet) [] _ selected
  apply WordEqualityMachine.within (show TM2OutputsInTime (queueTagMachine arity) (refusedWire input)
    (some (.inr false :: (refusedWire input).map Sum.inl)) _ from tagged)
  simp only [queueStatusTemplate, List.length_cons, List.length_nil]
  omega

noncomputable def queueRefusedOutputs (arity : Nat) (input : Input) :
    TM2OutputsInTime (queueMachine arity) (refusedWire input) (some [(0 : Alphabet)])
      (queueClock arity (refusedWire input).length) := by
  have refused := StackMachineComposition.Dispatch.outputs_refused (queuePayloadMachine arity) acceptTag [(0 : Alphabet)]
    (.inr false : GuardCell) ((refusedWire input).map Sum.inl) (by decide)
  have joined := StackMachineComposition.outputs (queueTagMachine arity) (queueDispatch arity) (Equiv.refl GuardCell)
    (refusedWire input) (.inr false :: (refusedWire input).map Sum.inl) [(0 : Alphabet)] _ _
    (queueRefusedTagOutputs arity input) (by
      change TM2OutputsInTime (queueDispatch arity) ((.inr false :: (refusedWire input).map Sum.inl).map id) _ _
      simpa only [List.map_id, queueDispatch] using refused)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons, List.length_map, queueClock]
  omega

theorem prepared_refused (definition : ValidatedCalculusLanguageDef) (arity : Nat) (input : Input)
    (refused : NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs = [.inr false]) :
    preparedWire definition arity input = refusedWire input := by
  rw [preparedWire, refused]
  simp only [List.flatMap_cons, List.flatMap_nil, pairImage, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    refusedWire, refusedFields, Fields.argumentWire_snoc, List.map_cons, List.map_nil, List.append_assoc]
  rfl

noncomputable def rowRefusedOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input)
    (refused : NodeChildrenExecution.resultWire definition arity input.ruleInstance input.goal input.proofs = [.inr false]) :
    TM2OutputsInTime (rowMachine definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some [(0 : Alphabet)]) (rowClock definition arity input) := by
  have node := preparedOutputs definition firstOrder arity input
  have queue := queueRefusedOutputs arity input
  have same := prepared_refused definition arity input refused
  rw [← same] at queue
  exact StackMachineComposition.outputs (preparedMachine definition.1 arity) (queueMachine arity)
    (Equiv.refl (Option Alphabet)) (Indexed.argumentWire (stemFields input)) (preparedWire definition arity input)
    [(0 : Alphabet)] _ _ node (by
      change TM2OutputsInTime (queueMachine arity) ((preparedWire definition arity input).map id) _ _
      simpa only [List.map_id] using queue)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

abbrev Row (definition : CalculusLanguageDef) := AuthoredNodeDispatch.Row definition
abbrev RowBase (definition : CalculusLanguageDef) := rowMachine definition 0

theorem rowCellTypes (definition : CalculusLanguageDef) (index : Row definition) (key : (RowBase definition).K) :
    (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).Γ key = (RowBase definition).Γ key := rfl

def rowFamily (definition : CalculusLanguageDef) : CommonArenaDispatch.Family (RowBase definition) (Row definition) where
  alphabet index := (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).Γ
  cellTypes := rowCellTypes definition
  Label index := (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).Λ
  labelFinite index := (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).ΛFin
  main index := (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).main
  body index := (rowMachine definition (AuthoredNodeDispatch.premiseArity definition index)).m

attribute [local implicit_reducible] Indexed.machine CertificateRuleAdmission.machine
  StackMachineComposition.machine RetainedWordExecution.machine rowMachine preparedMachine queueMachine
local instance : Fintype ((Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9)).Γ
    (Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9)).Γ
    (Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9)).k₁) := inferInstanceAs (Inhabited Alphabet)

def rowSelector (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9)) (CertificateRuleAdmission.machine definition) (Equiv.refl Alphabet)
attribute [local implicit_reducible] rowSelector
local instance (definition : CalculusLanguageDef) : Fintype ((rowSelector definition).Γ (rowSelector definition).k₁) :=
  inferInstanceAs (Fintype (Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((rowSelector definition).Γ (rowSelector definition).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def rowSelection (definition : CalculusLanguageDef) := RetainedWordExecution.machine (rowSelector definition)
  (CertificateRuleAdmission.ScopedApplication.readSelected definition)

def selectedWire (definition : CalculusLanguageDef) (input : Input) : List (Option Alphabet ⊕ Option (Row definition)) :=
  .inr (CertificateRuleAdmission.selected definition input.ruleInstance) :: (Indexed.argumentWire (stemFields input)).map Sum.inl

def rowSelectorClock (input : Input) := 8 * ((Indexed.argumentWire (stemFields input)).length + 1) +
  14 * (encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance).length + 17

def rowSelectionClock (input : Input) := rowSelectorClock input + 3 * (Indexed.argumentWire (stemFields input)).length +
  (encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance).length + 5

noncomputable def rowSelectorOutputs (definition : CalculusLanguageDef) (input : Input) :
    TM2OutputsInTime (rowSelector definition) (Indexed.argumentWire (stemFields input))
      (some (CertificateRuleAdmission.output definition input.ruleInstance)) (rowSelectorClock input) := by
  have picked := Indexed.outputs ([.inr 0] : Indexed.Template Alphabet 9) (stemFields input)
  have same : Indexed.instantiate ([.inr 0] : Indexed.Template Alphabet 9) (stemFields input) =
      encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance := by
    simp only [Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil]
    rfl
  rw [same] at picked
  have ran := StackMachineComposition.outputs (Indexed.machine ([.inr 0] : Indexed.Template Alphabet 9))
    (CertificateRuleAdmission.machine definition) (Equiv.refl Alphabet) (Indexed.argumentWire (stemFields input))
    (encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance) (CertificateRuleAdmission.output definition input.ruleInstance)
    _ _ picked (by
      change TM2OutputsInTime (CertificateRuleAdmission.machine definition)
        ((encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance).map id) _ _
      simpa only [List.map_id] using CertificateRuleAdmission.outputs definition input.ruleInstance)
  apply WordEqualityMachine.within ran
  simp only [rowSelectorClock, List.length_cons, List.length_nil]
  omega

noncomputable def rowSelectionOutputs (definition : CalculusLanguageDef) (input : Input) :
    TM2OutputsInTime (rowSelection definition) (Indexed.argumentWire (stemFields input))
      (some (selectedWire definition input)) (rowSelectionClock input) := by
  have selected := RetainedWordExecution.outputs (rowSelector definition)
    (CertificateRuleAdmission.ScopedApplication.readSelected definition) (Indexed.argumentWire (stemFields input))
    (.inr (CertificateRuleAdmission.selected definition input.ruleInstance))
    ((encodeWith CertificateDataEncoding.instanceCodec input.ruleInstance).map Sum.inl) _
    (rowSelectorOutputs definition input)
  simpa only [CertificateRuleAdmission.ScopedApplication.readSelected, rowSelection, selectedWire,
    rowSelectionClock, List.length_map] using selected

def rowDispatcher (definition : CalculusLanguageDef) := CommonArenaDispatch.machine (RowBase definition)
  (rowFamily definition) (none : Option Alphabet) (0 : Alphabet)
attribute [local implicit_reducible] rowSelection rowDispatcher
local instance (definition : CalculusLanguageDef) : Fintype ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option (Row definition)))

def selectedNodeMachine (definition : CalculusLanguageDef) := StackMachineComposition.machine
  (rowSelection definition) (rowDispatcher definition) (Equiv.refl (Option Alphabet ⊕ Option (Row definition)))

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] rowMachine selectedNodeMachine rowDispatcher rowSelection
  StackMachineComposition.machine
local instance (definition : CalculusLanguageDef) : Fintype ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option (Row definition)))

def positivePacket (input : Input) (computedPremises : List Pattern) : Packet :=
  (children input.site 0 (computedPremises.zip input.proofs) ++
    .close input.goal input.ruleInstance computedPremises input.site :: input.tail,
    (input.returned,input.saved))

noncomputable def rowSourceOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (arity : Nat) (input : Input)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (premiseCount : computedPremises.length = arity) (childCount : input.proofs.length = arity) :
    TM2OutputsInTime (rowMachine definition.1 arity) (Indexed.argumentWire (stemFields input))
      (some ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises))) (rowClock definition arity input) := by
  let jobs := sourceJobs computedPremises input.proofs arity premiseCount childCount
  have row := rowOutputs definition firstOrder arity input computedPremises accepted premiseCount childCount jobs
    (sourceJobs_list computedPremises input.proofs arity premiseCount childCount)
  have visitsEq : visits input.site jobs = children input.site 0 (computedPremises.zip input.proofs) := by
    rw [visits_children, sourceJobs_list]
  have premisesEq : premises jobs = computedPremises := sourceJobs_premises _ _ _ _ _
  rw [visitsEq, premisesEq] at row
  exact row

def selectedNodeClock (definition : ValidatedCalculusLanguageDef) (input : Input) :=
  rowSelectionClock input + 4 * (Indexed.argumentWire (stemFields input)).length + 8 +
    ((CertificateRuleAdmission.selected definition.1 input.ruleInstance).map
      (fun index => rowClock definition (AuthoredNodeDispatch.premiseArity definition.1 index) input)).getD 0

noncomputable def selectedPositiveOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (index : Row definition.1)
    (selected : CertificateRuleAdmission.selected definition.1 input.ruleInstance = some index)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (childCount : input.proofs.length = computedPremises.length) :
    TM2OutputsInTime (selectedNodeMachine definition.1) (Indexed.argumentWire (stemFields input))
      (some ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises))) (selectedNodeClock definition input) := by
  have premiseCount := (AuthoredNodeDispatch.selected_premise_count selected accepted).symm
  have childCount' : input.proofs.length = AuthoredNodeDispatch.premiseArity definition.1 index := childCount.trans premiseCount
  have source := rowSourceOutputs definition firstOrder (AuthoredNodeDispatch.premiseArity definition.1 index)
    input computedPremises accepted premiseCount childCount'
  have executed : TM2OutputsInTime ((rowFamily definition.1).toMachine index)
      ((Indexed.argumentWire (stemFields input)).map
        (CommonArenaDispatch.cellTypes (RowBase definition.1) (rowFamily definition.1) index (RowBase definition.1).k₀).mpr)
      (some (((1 : Alphabet) :: encodePacket (positivePacket input computedPremises)).map
        (CommonArenaDispatch.cellTypes (RowBase definition.1) (rowFamily definition.1) index (RowBase definition.1).k₁).mpr))
      (rowClock definition (AuthoredNodeDispatch.premiseArity definition.1 index) input) := by
    change TM2OutputsInTime (rowMachine definition.1 (AuthoredNodeDispatch.premiseArity definition.1 index))
      ((Indexed.argumentWire (stemFields input)).map id)
      (some (((1 : Alphabet) :: encodePacket (positivePacket input computedPremises)).map id)) _
    simpa only [List.map_id] using source
  have dispatched := CommonArenaDispatch.outputs_selected (RowBase definition.1) (rowFamily definition.1)
    (none : Option Alphabet) (0 : Alphabet) index (Indexed.argumentWire (stemFields input))
    ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises)) _ executed
  have tagged : selectedWire definition.1 input = .inr (some index) :: (Indexed.argumentWire (stemFields input)).map Sum.inl := by
    simp only [selectedWire, selected]
  rw [← tagged] at dispatched
  have joined := StackMachineComposition.outputs (rowSelection definition.1) (rowDispatcher definition.1)
    (Equiv.refl (Option Alphabet ⊕ Option (Row definition.1))) (Indexed.argumentWire (stemFields input))
    (selectedWire definition.1 input) ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises)) _ _
    (rowSelectionOutputs definition.1 input) (by
      change TM2OutputsInTime (rowDispatcher definition.1) ((selectedWire definition.1 input).map id) _ _
      simpa only [List.map_id, rowDispatcher] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [selectedNodeClock, selected, Option.map_some, Option.getD_some, selectedWire,
    List.length_cons, List.length_map]
  omega

/-- The authored row is physically selected; the caller supplies no arity. -/
def authoredMachine (definition : CalculusLanguageDef) :=
  @StackMachineComposition.machine originalPacketProgram.tm (selectedNodeMachine definition)
    (PacketProgram.outputFinite originalPacketProgram) (PacketProgram.outputInhabited originalPacketProgram)
    originalPacketProgram.output

def authoredClock (definition : ValidatedCalculusLanguageDef) (input : Input) :=
  originalPacketClock input + 2 * (Indexed.argumentWire (stemFields input)).length + 2 + selectedNodeClock definition input

noncomputable def authoredOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (childCount : input.proofs.length = computedPremises.length) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises))) (authoredClock definition input) := by
  let found := AuthoredNodeDispatch.instantiated_premise_count accepted
  let index := Classical.choose found
  have selected := (Classical.choose_spec found).1
  have prepared := originalPacketOutputs input
  change TM2OutputsInTime originalPacketProgram.tm ((Indexed.argumentWire (startFields input)).map id)
    (some ((Indexed.argumentWire (stemFields input)).map id)) _ at prepared
  simp only [List.map_id] at prepared
  have selectedRun := selectedPositiveOutputs definition firstOrder input index selected computedPremises accepted childCount
  exact @StackMachineComposition.outputs originalPacketProgram.tm (selectedNodeMachine definition.1)
    (PacketProgram.outputFinite originalPacketProgram) (PacketProgram.outputInhabited originalPacketProgram)
    originalPacketProgram.output (Indexed.argumentWire (startFields input)) (Indexed.argumentWire (stemFields input))
    ((1 : Alphabet) :: encodePacket (positivePacket input computedPremises)) _ _ prepared (by
      change TM2OutputsInTime (selectedNodeMachine definition.1) ((Indexed.argumentWire (stemFields input)).map id) _ _
      simpa only [List.map_id] using selectedRun)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] rowMachine selectedNodeMachine rowDispatcher rowSelection StackMachineComposition.machine
local instance (definition : CalculusLanguageDef) : Fintype ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option (Row definition)))
local instance (definition : CalculusLanguageDef) : Inhabited ((rowSelection definition).Γ (rowSelection definition).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option (Row definition)))

noncomputable def selectedAbsentOutputs (definition : ValidatedCalculusLanguageDef) (input : Input)
    (absent : CertificateRuleAdmission.selected definition.1 input.ruleInstance = none) :
    TM2OutputsInTime (selectedNodeMachine definition.1) (Indexed.argumentWire (stemFields input))
      (some [(0 : Alphabet)]) (selectedNodeClock definition input) := by
  have dispatched := CommonArenaDispatch.outputs_absent (RowBase definition.1) (rowFamily definition.1)
    (none : Option Alphabet) (0 : Alphabet) (Indexed.argumentWire (stemFields input))
  have tagged : selectedWire definition.1 input = .inr none :: (Indexed.argumentWire (stemFields input)).map Sum.inl := by
    simp only [selectedWire, absent]
  rw [← tagged] at dispatched
  have joined := StackMachineComposition.outputs (rowSelection definition.1) (rowDispatcher definition.1)
    (Equiv.refl (Option Alphabet ⊕ Option (Row definition.1))) (Indexed.argumentWire (stemFields input))
    (selectedWire definition.1 input) [(0 : Alphabet)] _ _ (rowSelectionOutputs definition.1 input) (by
      change TM2OutputsInTime (rowDispatcher definition.1) ((selectedWire definition.1 input).map id) _ _
      simpa only [List.map_id, rowDispatcher] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [selectedNodeClock, absent, Option.map_none, Option.getD_none, selectedWire,
    List.length_cons, List.length_map]
  omega

noncomputable def selectedRefusedOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (index : Row definition.1)
    (selected : CertificateRuleAdmission.selected definition.1 input.ruleInstance = some index)
    (refused : NodeChildrenExecution.resultWire definition (AuthoredNodeDispatch.premiseArity definition.1 index)
      input.ruleInstance input.goal input.proofs = [.inr false]) :
    TM2OutputsInTime (selectedNodeMachine definition.1) (Indexed.argumentWire (stemFields input))
      (some [(0 : Alphabet)]) (selectedNodeClock definition input) := by
  have source := rowRefusedOutputs definition firstOrder (AuthoredNodeDispatch.premiseArity definition.1 index) input refused
  have executed : TM2OutputsInTime ((rowFamily definition.1).toMachine index)
      ((Indexed.argumentWire (stemFields input)).map
        (CommonArenaDispatch.cellTypes (RowBase definition.1) (rowFamily definition.1) index (RowBase definition.1).k₀).mpr)
      (some ([(0 : Alphabet)].map
        (CommonArenaDispatch.cellTypes (RowBase definition.1) (rowFamily definition.1) index (RowBase definition.1).k₁).mpr))
      (rowClock definition (AuthoredNodeDispatch.premiseArity definition.1 index) input) := by
    change TM2OutputsInTime (rowMachine definition.1 (AuthoredNodeDispatch.premiseArity definition.1 index))
      ((Indexed.argumentWire (stemFields input)).map id) (some ([(0 : Alphabet)].map id)) _
    simpa only [List.map_id] using source
  have dispatched := CommonArenaDispatch.outputs_selected (RowBase definition.1) (rowFamily definition.1)
    (none : Option Alphabet) (0 : Alphabet) index (Indexed.argumentWire (stemFields input)) [(0 : Alphabet)] _ executed
  have tagged : selectedWire definition.1 input = .inr (some index) :: (Indexed.argumentWire (stemFields input)).map Sum.inl := by
    simp only [selectedWire, selected]
  rw [← tagged] at dispatched
  have joined := StackMachineComposition.outputs (rowSelection definition.1) (rowDispatcher definition.1)
    (Equiv.refl (Option Alphabet ⊕ Option (Row definition.1))) (Indexed.argumentWire (stemFields input))
    (selectedWire definition.1 input) [(0 : Alphabet)] _ _ (rowSelectionOutputs definition.1 input) (by
      change TM2OutputsInTime (rowDispatcher definition.1) ((selectedWire definition.1 input).map id) _ _
      simpa only [List.map_id, rowDispatcher] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [selectedNodeClock, selected, Option.map_some, Option.getD_some, selectedWire,
    List.length_cons, List.length_map]
  omega

noncomputable def authoredExecution (definition : ValidatedCalculusLanguageDef) (input : Input) (word : List Alphabet)
    (branch : TM2OutputsInTime (selectedNodeMachine definition.1) (Indexed.argumentWire (stemFields input))
      (some word) (selectedNodeClock definition input)) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some word) (authoredClock definition input) := by
  have prepared := originalPacketOutputs input
  change TM2OutputsInTime originalPacketProgram.tm ((Indexed.argumentWire (startFields input)).map id)
    (some ((Indexed.argumentWire (stemFields input)).map id)) _ at prepared
  simp only [List.map_id] at prepared
  exact @StackMachineComposition.outputs originalPacketProgram.tm (selectedNodeMachine definition.1)
    (PacketProgram.outputFinite originalPacketProgram) (PacketProgram.outputInhabited originalPacketProgram)
    originalPacketProgram.output (Indexed.argumentWire (startFields input)) (Indexed.argumentWire (stemFields input))
    word _ _ prepared (by
      change TM2OutputsInTime (selectedNodeMachine definition.1) ((Indexed.argumentWire (stemFields input)).map id) _ _
      simpa only [List.map_id] using branch)

/-- Missing rows and failed original instance admission return physical refusal. -/
noncomputable def authoredBadRuleOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input)
    (badRule : instantiateRule? definition input.ruleInstance = none) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some [(0 : Alphabet)]) (authoredClock definition input) := by
  apply authoredExecution
  cases selected : CertificateRuleAdmission.selected definition.1 input.ruleInstance with
  | none => exact selectedAbsentOutputs definition input selected
  | some index =>
      apply selectedRefusedOutputs definition firstOrder input index selected
      simp only [NodeChildrenExecution.resultWire, RuleNodeAdmission.result, badRule,
        Option.any_none, Bool.false_eq_true, ↓reduceIte]

noncomputable def authoredWrongGoalOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (computedPremises : List Pattern) (conclusion : Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,conclusion))
    (different : conclusion ≠ input.goal) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some [(0 : Alphabet)]) (authoredClock definition input) := by
  apply authoredExecution
  cases selected : CertificateRuleAdmission.selected definition.1 input.ruleInstance with
  | none => exact selectedAbsentOutputs definition input selected
  | some index =>
      apply selectedRefusedOutputs definition firstOrder input index selected
      simp only [NodeChildrenExecution.resultWire, RuleNodeAdmission.result, accepted,
        Option.any_some, different, decide_false, Bool.false_eq_true, ↓reduceIte]

noncomputable def authoredChildMismatchOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (computedPremises : List Pattern)
    (accepted : instantiateRule? definition input.ruleInstance = some (computedPremises,input.goal))
    (different : input.proofs.length ≠ computedPremises.length) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some [(0 : Alphabet)]) (authoredClock definition input) := by
  apply authoredExecution
  cases selected : CertificateRuleAdmission.selected definition.1 input.ruleInstance with
  | none => exact selectedAbsentOutputs definition input selected
  | some index =>
      have count := AuthoredNodeDispatch.selected_premise_count selected accepted
      apply selectedRefusedOutputs definition firstOrder input index selected
      simp only [NodeChildrenExecution.resultWire, RuleNodeAdmission.result, accepted,
        Option.any_some, decide_true, ↓reduceIte, OriginalChildJobs.outputWire,
        OriginalChildJobs.fieldWords, count, different, ↓reduceIte, FramedWordPairing.output]

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

def statePacket {definition : ValidatedCalculusLanguageDef} (state : ChronologicalDriver.State definition) : Packet :=
  (state.todo, (state.values.map (fun claim => claim.root), state.saved.map (fun claim => claim.root)))

def readPacket : List Alphabet → Option Packet
  | 1 :: body => decodePacket body
  | _ => none

theorem readPacket_positive (packet : Packet) : readPacket (1 :: encodePacket packet) = some packet :=
  decodePacket_encodePacket packet

def nodeStateInput {definition : ValidatedCalculusLanguageDef} (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task) : Node.Input :=
  ⟨ruleInstance,goal,proofs,site,tail,state.saved.map (fun claim => claim.root),state.values.map (fun claim => claim.root)⟩

def nodeNext {definition : ValidatedCalculusLanguageDef} (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (computedPremises : List Pattern) : ChronologicalDriver.State definition :=
  { state with todo := children site 0 (computedPremises.zip proofs) ++ .close goal ruleInstance computedPremises site :: tail }

theorem controller_node_step (definition : ValidatedCalculusLanguageDef) (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (computedPremises : List Pattern)
    (work : state.todo = .visit goal (.node ruleInstance proofs) site :: tail)
    (accepted : instantiateRule? definition ruleInstance = some (computedPremises,goal))
    (childCount : proofs.length = computedPremises.length) :
    step definition (.running state) = .running (nodeNext state ruleInstance goal proofs site tail computedPremises) := by
  simp only [step, work, accepted, ↓reduceIte, childCount]
  rfl

/-- The actual authored-node machine realizes the original controller visit
branch. Child sites, the old work tail, returned roots and saved roots are exact. -/
noncomputable def controller_node_outputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition ruleInstance = some (computedPremises,goal))
    (childCount : proofs.length = computedPremises.length) :
    TM2OutputsInTime (Node.authoredMachine definition.1)
      (Indexed.argumentWire (Node.startFields (nodeStateInput state ruleInstance goal proofs site tail)))
      (some ((1 : Alphabet) :: encodePacket (statePacket (nodeNext state ruleInstance goal proofs site tail computedPremises))))
      (Node.authoredClock definition (nodeStateInput state ruleInstance goal proofs site tail)) :=
  Node.authoredOutputs definition firstOrder (nodeStateInput state ruleInstance goal proofs site tail) computedPremises accepted childCount

theorem controller_node_readout (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (computedPremises : List Pattern)
    (accepted : instantiateRule? definition ruleInstance = some (computedPremises,goal))
    (childCount : proofs.length = computedPremises.length) (word : List Alphabet)
    (finished : TM2Outputs (Node.authoredMachine definition.1)
      (Indexed.argumentWire (Node.startFields (nodeStateInput state ruleInstance goal proofs site tail))) (some word)) :
    readPacket word = some (statePacket (nodeNext state ruleInstance goal proofs site tail computedPremises)) := by
  have exactWord := StackMachineComposition.outputs_unique finished
    (controller_node_outputs definition firstOrder state ruleInstance goal proofs site tail computedPremises accepted childCount).toEvalsTo
  rw [exactWord]
  exact readPacket_positive _

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

/-- Independent source semantics. It is not called by the finite machine. -/
def sourceResult (definition : ValidatedCalculusLanguageDef) (input : Input) : Option Packet :=
  match instantiateRule? definition input.ruleInstance with
  | none => none
  | some (computedPremises,conclusion) =>
      if conclusion = input.goal ∧ input.proofs.length = computedPremises.length
      then some (positivePacket input computedPremises) else none

def sourceWord (definition : ValidatedCalculusLanguageDef) (input : Input) : List Alphabet :=
  (sourceResult definition input).elim [0] (fun packet => 1 :: encodePacket packet)

noncomputable def totalOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) :
    TM2OutputsInTime (authoredMachine definition.1) (Indexed.argumentWire (startFields input))
      (some (sourceWord definition input)) (authoredClock definition input) := by
  cases accepted : instantiateRule? definition input.ruleInstance with
  | none =>
      simpa only [sourceWord, sourceResult, accepted, Option.elim_none] using authoredBadRuleOutputs definition firstOrder input accepted
  | some pair =>
      rcases pair with ⟨computedPremises,conclusion⟩
      by_cases same : conclusion = input.goal
      · subst conclusion
        by_cases childCount : input.proofs.length = computedPremises.length
        · simpa only [sourceWord, sourceResult, accepted, childCount, and_self, ↓reduceIte, Option.elim_some] using
            authoredOutputs definition firstOrder input computedPremises accepted childCount
        · simpa only [sourceWord, sourceResult, accepted, childCount, and_false, ↓reduceIte, Option.elim_none] using
            authoredChildMismatchOutputs definition firstOrder input computedPremises accepted childCount
      · simpa only [sourceWord, sourceResult, accepted, same, false_and, ↓reduceIte, Option.elim_none] using
          authoredWrongGoalOutputs definition firstOrder input computedPremises conclusion accepted same

theorem sourceWord_readout (definition : ValidatedCalculusLanguageDef) (input : Input) :
    readPacket (sourceWord definition input) = sourceResult definition input := by
  cases result : sourceResult definition input with
  | none => simp only [sourceWord, result, Option.elim_none]; rfl
  | some packet => simpa only [sourceWord, result, Option.elim_some] using readPacket_positive packet

/-- Every completed canonical visit-node packet has exactly the original
source success/refusal result and original ordered continuation. -/
theorem run_readout (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (word : List Alphabet)
    (finished : TM2Outputs (authoredMachine definition.1) (Indexed.argumentWire (startFields input)) (some word)) :
    readPacket word = sourceResult definition input := by
  rw [StackMachineComposition.outputs_unique finished (totalOutputs definition firstOrder input).toEvalsTo]
  exact sourceWord_readout definition input

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ChronologicalDriver ChronologicalTaskEncoding

structure TaskInput where
  query : Nat
  goal : Pattern
  site : Site
  tail : List Task
  saved : List Nat
  returned : List Nat
  roots : Array Nat
  cache : Array Theorem

def taskData (input : TaskInput) := putTask (.visit input.goal (.premise input.query) input.site)
def taskFields (input : TaskInput) : Fin 6 → List Alphabet :=
  ![encodeTask (.visit input.goal (.premise input.query) input.site),encodeWork input.tail,
    encodeRoots input.saved,encodeRoots input.returned,
    table (indexed input.roots),table (EncodedTable.rows theoremCodec input.cache)]

def goalFields (input : TaskInput) : Fin 7 → List Alphabet :=
  Fin.snoc (taskFields input) (encodeWith CertificateDataEncoding.patternCodec input.goal)
def queryFields (input : TaskInput) : Fin 8 → List Alphabet := Fin.snoc (goalFields input) (encodeWith Codec.nat input.query)
def queryPath : List Bool := [true,true,false,true]

def extractProgram : PacketProgram := (Node.retainingProgram (0 : Fin 6) Node.goalPath).append
  (Node.retainingProgram (0 : Fin 7) queryPath)

def extractClock (input : TaskInput) :=
  Node.retainClock Node.goalPath (taskFields input) (taskData input) (CertificateDataEncoding.patternCodec.put input.goal) +
  2 * (Indexed.argumentWire (goalFields input)).length + 2 +
  Node.retainClock queryPath (goalFields input) (taskData input) (Codec.nat.put input.query)

noncomputable def extractOutputs (input : TaskInput) :
    PacketProgram.Runs extractProgram (Indexed.argumentWire (taskFields input))
      (Indexed.argumentWire (queryFields input)) (extractClock input) := by
  have goal := Node.retainingProgramOutputs (0 : Fin 6) Node.goalPath (taskFields input) (taskData input)
    (CertificateDataEncoding.patternCodec.put input.goal) (by rfl) (by rfl)
  have query := Node.retainingProgramOutputs (0 : Fin 7) queryPath (goalFields input) (taskData input)
    (Codec.nat.put input.query) (by rfl) (by rfl)
  exact PacketProgram.append_runs _ _ _ _ _ _ _ goal query

attribute [local implicit_reducible] SavedRootInsertion.projection WordTemplateMachine.machine
  StackMachineComposition.machine
local instance : Fintype ((SavedRootInsertion.projection (7 : Fin 8)).Γ (SavedRootInsertion.projection (7 : Fin 8)).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((SavedRootInsertion.projection (7 : Fin 8)).Γ (SavedRootInsertion.projection (7 : Fin 8)).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def keyTemplate : WordTemplateMachine.Template Alphabet := [none,some 2]
def queryMachine := StackMachineComposition.machine (SavedRootInsertion.projection (7 : Fin 8))
  (WordTemplateMachine.machine keyTemplate) (Equiv.refl Alphabet)
attribute [local implicit_reducible] queryMachine
local instance : Fintype (queryMachine.Γ queryMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (queryMachine.Γ queryMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (queryMachine.Γ queryMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def queryWord (input : TaskInput) := field (naturalKey input.query) ++ [2]
def queryClock (input : TaskInput) := 24 * ((Indexed.argumentWire (queryFields input)).length + 1) +
  2 * (field (naturalKey input.query)).length + 2 + 12 * ((field (naturalKey input.query)).length + 1)

noncomputable def queryOutputs (input : TaskInput) :
    TM2OutputsInTime queryMachine (Indexed.argumentWire (queryFields input)) (some (queryWord input)) (queryClock input) := by
  have projected := SavedRootInsertion.projectionOutputs (7 : Fin 8) (queryFields input) input.query (by rfl)
  have terminated := WordTemplateMachine.outputs keyTemplate (field (naturalKey input.query))
  have same : WordTemplateMachine.instantiate keyTemplate (field (naturalKey input.query)) = queryWord input := by
    simp only [keyTemplate, WordTemplateMachine.instantiate_hole, WordTemplateMachine.instantiate_literal,
      WordTemplateMachine.instantiate_nil, queryWord]
  rw [same] at terminated
  exact StackMachineComposition.outputs (SavedRootInsertion.projection (7 : Fin 8))
    (WordTemplateMachine.machine keyTemplate) (Equiv.refl Alphabet) (Indexed.argumentWire (queryFields input))
    (field (naturalKey input.query)) (queryWord input) _ _ projected (by
      change TM2OutputsInTime (WordTemplateMachine.machine keyTemplate) ((field (naturalKey input.query)).map id) _ _
      simpa only [List.map_id, keyTemplate, List.length_cons, List.length_nil] using terminated)

def retainedQuery : PacketProgram :=
  ⟨RetainedWordExecution.WithOutput.Framed.machine queryMachine (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩
def preparedFields (input : TaskInput) : Fin 9 → List Alphabet := Fin.snoc (queryFields input) (queryWord input)
def retainedQueryClock (input : TaskInput) := queryClock input + 23 * (Indexed.argumentWire (queryFields input)).length +
  22 * (queryWord input).length + 23

noncomputable def retainedQueryOutputs (input : TaskInput) :
    PacketProgram.Runs retainedQuery (Indexed.argumentWire (queryFields input))
      (Indexed.argumentWire (preparedFields input)) (retainedQueryClock input) := by
  have copied := RetainedWordExecution.WithOutput.Framed.outputs queryMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (queryFields input))
    (queryWord input) _ (queryOutputs input)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord queryMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (queryFields input)) (queryWord input) =
        Indexed.argumentWire (preparedFields input) := by
    change (Indexed.argumentWire (queryFields input)).map id ++ (queryWord input).map some ++ [none] = _
    simpa only [List.map_id, preparedFields] using (Fields.argumentWire_snoc (queryFields input) (queryWord input)).symm
  rw [same] at copied
  change TM2OutputsInTime retainedQuery.tm ((Indexed.argumentWire (queryFields input)).map id)
    (some ((Indexed.argumentWire (preparedFields input)).map id)) _
  simpa only [List.map_id, retainedQuery, retainedQueryClock] using copied

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] FramedFieldSelection.machine StackMachineComposition.machine machine
local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def lookupMachine := StackMachineComposition.machine
  (FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))) machine (Equiv.refl (Option Alphabet))
attribute [local implicit_reducible] lookupMachine
local instance : Fintype (lookupMachine.Γ lookupMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (lookupMachine.Γ lookupMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (lookupMachine.Γ lookupMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def resultRoot (input : TaskInput) := SharedPremiseExecution.result input.roots input.cache input.query input.goal

def lookupClock (input : TaskInput) := 44 * ((Indexed.argumentWire (preparedFields input)).length + 1) +
  2 * (SharedPremiseExecution.inputWire input.roots input.cache input.query input.goal).length + 2 +
  clock input.roots input.cache input.query input.goal

noncomputable def lookupOutputs (input : TaskInput) :
    TM2OutputsInTime lookupMachine (Indexed.argumentWire (preparedFields input))
      (some (rootWord (resultRoot input))) (lookupClock input) := by
  have selected := FramedFieldSelection.outputs ([8,4,5,6] : List (Fin 9)) (preparedFields input)
  have same : Indexed.frame (([8,4,5,6] : List (Fin 9)).map (preparedFields input)) =
      SharedPremiseExecution.inputWire input.roots input.cache input.query input.goal := rfl
  rw [same] at selected
  exact StackMachineComposition.outputs (FramedFieldSelection.machine (Γ := Alphabet) ([8,4,5,6] : List (Fin 9))) machine
    (Equiv.refl (Option Alphabet)) (Indexed.argumentWire (preparedFields input))
    (SharedPremiseExecution.inputWire input.roots input.cache input.query input.goal) (rootWord (resultRoot input)) _ _ selected (by
      change TM2OutputsInTime machine ((SharedPremiseExecution.inputWire input.roots input.cache input.query input.goal).map id) _ _
      simpa only [List.map_id, resultRoot] using outputs input.roots input.cache input.query input.goal)

def retainedLookup : PacketProgram :=
  ⟨RetainedWordExecution.WithOutput.Framed.machine lookupMachine (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩
def resultFields (input : TaskInput) : Fin 10 → List Alphabet := Fin.snoc (preparedFields input) (rootWord (resultRoot input))
def retainedLookupClock (input : TaskInput) := lookupClock input + 23 * (Indexed.argumentWire (preparedFields input)).length +
  22 * (rootWord (resultRoot input)).length + 23

noncomputable def retainedLookupOutputs (input : TaskInput) :
    PacketProgram.Runs retainedLookup (Indexed.argumentWire (preparedFields input))
      (Indexed.argumentWire (resultFields input)) (retainedLookupClock input) := by
  have copied := RetainedWordExecution.WithOutput.Framed.outputs lookupMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (preparedFields input))
    (rootWord (resultRoot input)) _ (lookupOutputs input)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord lookupMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (preparedFields input)) (rootWord (resultRoot input)) =
        Indexed.argumentWire (resultFields input) := by
    change (Indexed.argumentWire (preparedFields input)).map id ++ (rootWord (resultRoot input)).map some ++ [none] = _
    simpa only [List.map_id, resultFields] using (Fields.argumentWire_snoc (preparedFields input) (rootWord (resultRoot input))).symm
  rw [same] at copied
  change TM2OutputsInTime retainedLookup.tm ((Indexed.argumentWire (preparedFields input)).map id)
    (some ((Indexed.argumentWire (resultFields input)).map id)) _
  simpa only [List.map_id, retainedLookup, retainedLookupClock] using copied

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] Fields.stripMachine Indexed.machine StackMachineComposition.machine

def rootBody (root : Option Nat) : List Alphabet := root.elim [0] (encodeWith Codec.nat)

noncomputable def stripRootOutputs (root : Option Nat) :
    TM2OutputsInTime Fields.stripMachine (rootWord root) (some (rootBody root))
      (6 * ((rootWord root).length + 1)) := by
  cases root with
  | none =>
      have refused := StackMachineComposition.Dispatch.outputs_refused Fields.identityMachine Fields.accept [(0 : Alphabet)]
        (0 : Alphabet) [] (by decide)
      apply WordEqualityMachine.within (show TM2OutputsInTime Fields.stripMachine (rootWord none) (some (rootBody none)) _ from refused)
      simp only [rootWord, List.length_cons, List.length_nil, Option.elim_none]
      omega
  | some address =>
      have copied := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) (encodeWith Codec.nat address)
      simp only [List.flatMap_singleton'] at copied
      have stripped := StackMachineComposition.Dispatch.outputs_success Fields.identityMachine Fields.accept [(0 : Alphabet)]
        (1 : Alphabet) (encodeWith Codec.nat address) (encodeWith Codec.nat address) _ (by decide) copied
      apply WordEqualityMachine.within (show TM2OutputsInTime Fields.stripMachine (rootWord (some address))
        (some (rootBody (some address))) _ from stripped)
      simp only [rootWord, List.length_cons, Option.elim_some]
      omega

local instance : Fintype ((Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10)).Γ
    (Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10)).Γ
    (Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10)).k₁) := inferInstanceAs (Inhabited Alphabet)

def bodyMachine := StackMachineComposition.machine (Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10))
  Fields.stripMachine (Equiv.refl Alphabet)
attribute [local implicit_reducible] bodyMachine
local instance : Fintype (bodyMachine.Γ bodyMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (bodyMachine.Γ bodyMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (bodyMachine.Γ bodyMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def bodyClock (input : TaskInput) := 8 * ((Indexed.argumentWire (resultFields input)).length + 1) +
  2 * (rootWord (resultRoot input)).length + 2 + 6 * ((rootWord (resultRoot input)).length + 1)

noncomputable def bodyOutputs (input : TaskInput) :
    TM2OutputsInTime bodyMachine (Indexed.argumentWire (resultFields input))
      (some (rootBody (resultRoot input))) (bodyClock input) := by
  have selected := Indexed.outputs ([.inr 9] : Indexed.Template Alphabet 10) (resultFields input)
  have same : Indexed.instantiate ([.inr 9] : Indexed.Template Alphabet 10) (resultFields input) = rootWord (resultRoot input) := by
    simp only [Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil]
    rfl
  rw [same] at selected
  exact StackMachineComposition.outputs (Indexed.machine ([.inr 9] : Indexed.Template Alphabet 10)) Fields.stripMachine
    (Equiv.refl Alphabet) (Indexed.argumentWire (resultFields input)) (rootWord (resultRoot input))
    (rootBody (resultRoot input)) _ _ selected (by
      change TM2OutputsInTime Fields.stripMachine ((rootWord (resultRoot input)).map id) _ _
      simpa only [List.map_id] using stripRootOutputs (resultRoot input))

def retainedBody : PacketProgram :=
  ⟨RetainedWordExecution.WithOutput.Framed.machine bodyMachine (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩
def bodyFields (input : TaskInput) : Fin 11 → List Alphabet := Fin.snoc (resultFields input) (rootBody (resultRoot input))
def retainedBodyClock (input : TaskInput) := bodyClock input + 23 * (Indexed.argumentWire (resultFields input)).length +
  22 * (rootBody (resultRoot input)).length + 23

noncomputable def retainedBodyOutputs (input : TaskInput) :
    PacketProgram.Runs retainedBody (Indexed.argumentWire (resultFields input))
      (Indexed.argumentWire (bodyFields input)) (retainedBodyClock input) := by
  have copied := RetainedWordExecution.WithOutput.Framed.outputs bodyMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (resultFields input))
    (rootBody (resultRoot input)) _ (bodyOutputs input)
  have same : RetainedWordExecution.WithOutput.Framed.outputWord bodyMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (Indexed.argumentWire (resultFields input)) (rootBody (resultRoot input)) =
        Indexed.argumentWire (bodyFields input) := by
    change (Indexed.argumentWire (resultFields input)).map id ++ (rootBody (resultRoot input)).map some ++ [none] = _
    simpa only [List.map_id, bodyFields] using (Fields.argumentWire_snoc (resultFields input) (rootBody (resultRoot input))).symm
  rw [same] at copied
  change TM2OutputsInTime retainedBody.tm ((Indexed.argumentWire (resultFields input)).map id)
    (some ((Indexed.argumentWire (bodyFields input)).map id)) _
  simpa only [List.map_id, retainedBody, retainedBodyClock] using copied

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  RetainedWordExecution.machine WordHomomorphismMachine.machine StackMachineComposition.Dispatch.machine

def positivePacket (input : TaskInput) (address : Nat) : Packet :=
  (input.tail,(address :: input.returned,input.saved))
def returnTemplate : Indexed.Template Alphabet 11 :=
  [.inl 1,.inl 4,.inr 1,.inl 4,.inl 4,.inr 10,.inr 3,.inr 2]

theorem return_instantiates (input : TaskInput) (address : Nat) (found : resultRoot input = some address) :
    Indexed.instantiate returnTemplate (bodyFields input) = 1 :: encodePacket (positivePacket input address) := by
  simp only [returnTemplate, Indexed.instantiate_literal, Indexed.instantiate_hole, Indexed.instantiate_nil]
  change 1 :: 4 :: (encodeWork input.tail ++ 4 :: 4 ::
    (rootBody (resultRoot input) ++ (encodeRoots input.returned ++ (encodeRoots input.saved ++ [])))) = _
  rw [found]
  simp only [rootBody, Option.elim_some, List.append_nil]
  simp only [encodePacket, positivePacket, packetCodec, encodeWith, Codec.prod, encodeData_pair,
    encodeRoots, encodeWork, workCodec, Codec.list, Codec.putList]
  simp only [List.cons_append, List.append_assoc]

def returnStatus : Indexed.Template Alphabet 11 := [.inr 9]
local instance : Fintype ((Indexed.machine returnStatus).Γ (Indexed.machine returnStatus).k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine returnStatus).Γ (Indexed.machine returnStatus).k₀) := inferInstanceAs (Inhabited (Option Alphabet))

def returnTagMachine := RetainedWordExecution.machine (Indexed.machine returnStatus) Fields.accept
attribute [local implicit_reducible] returnTagMachine
local instance : Fintype (returnTagMachine.Γ returnTagMachine.k₁) := inferInstanceAs (Fintype Node.GuardCell)
local instance : Inhabited (returnTagMachine.Γ returnTagMachine.k₁) := inferInstanceAs (Inhabited Node.GuardCell)

def returnTagClock (input : TaskInput) := 11 * (Indexed.argumentWire (bodyFields input)).length +
  (rootWord (resultRoot input)).tail.length + 14

noncomputable def returnTagOutputs (input : TaskInput) :
    TM2OutputsInTime returnTagMachine (Indexed.argumentWire (bodyFields input))
      (some (.inr (resultRoot input).isSome :: (Indexed.argumentWire (bodyFields input)).map Sum.inl))
      (returnTagClock input) := by
  have selected := Indexed.outputs returnStatus (bodyFields input)
  have same : Indexed.instantiate returnStatus (bodyFields input) = rootWord (resultRoot input) := by
    simp only [returnStatus, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil]
    rfl
  rw [same] at selected
  cases found : resultRoot input with
  | none =>
      rw [found] at selected
      have tagged := RetainedWordExecution.outputs (Indexed.machine returnStatus) Fields.accept
        (Indexed.argumentWire (bodyFields input)) (0 : Alphabet) [] _ selected
      change TM2OutputsInTime returnTagMachine (Indexed.argumentWire (bodyFields input))
        (some (.inr false :: (Indexed.argumentWire (bodyFields input)).map Sum.inl)) _ at tagged
      apply WordEqualityMachine.within tagged
      simp only [returnTagClock, found, rootWord, Option.elim_none, List.tail_cons, List.length_nil,
        returnStatus, List.length_cons]
      omega
  | some address =>
      rw [found] at selected
      have tagged := RetainedWordExecution.outputs (Indexed.machine returnStatus) Fields.accept
        (Indexed.argumentWire (bodyFields input)) (1 : Alphabet) (encodeWith Codec.nat address) _ selected
      change TM2OutputsInTime returnTagMachine (Indexed.argumentWire (bodyFields input))
        (some (.inr true :: (Indexed.argumentWire (bodyFields input)).map Sum.inl)) _ at tagged
      apply WordEqualityMachine.within tagged
      simp only [returnTagClock, found, rootWord, Option.elim_some, List.tail_cons,
        returnStatus, List.length_cons, List.length_nil]
      omega

local instance : Fintype ((WordHomomorphismMachine.machine Node.restoreImage).Γ (WordHomomorphismMachine.machine Node.restoreImage).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((WordHomomorphismMachine.machine Node.restoreImage).Γ (WordHomomorphismMachine.machine Node.restoreImage).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def returnPayload := StackMachineComposition.machine (WordHomomorphismMachine.machine Node.restoreImage)
  (Indexed.machine returnTemplate) (Equiv.refl (Option Alphabet))
def returnDispatch := StackMachineComposition.Dispatch.machine returnPayload Node.acceptTag [(0 : Alphabet)]
def returnMachine := StackMachineComposition.machine returnTagMachine returnDispatch (Equiv.refl Node.GuardCell)
def returnClock (input : TaskInput) := 19 * (Indexed.argumentWire (bodyFields input)).length + 23 +
  (rootWord (resultRoot input)).tail.length +
  4 * (returnTemplate.length + 1) * ((Indexed.argumentWire (bodyFields input)).length + 1)

noncomputable def returnPayloadOutputs (input : TaskInput) (address : Nat) (found : resultRoot input = some address) :
    TM2OutputsInTime returnPayload ((Indexed.argumentWire (bodyFields input)).map Sum.inl)
      (some ((1 : Alphabet) :: encodePacket (positivePacket input address)))
      (6 * (Indexed.argumentWire (bodyFields input)).length + 4 +
        4 * (returnTemplate.length + 1) * ((Indexed.argumentWire (bodyFields input)).length + 1)) := by
  have restored := WordHomomorphismMachine.outputs Node.restoreImage
    ((Indexed.argumentWire (bodyFields input)).map (Sum.inl : Option Alphabet → Node.GuardCell))
  have same : ((Indexed.argumentWire (bodyFields input)).map (Sum.inl : Option Alphabet → Node.GuardCell)).flatMap Node.restoreImage =
      Indexed.argumentWire (bodyFields input) := by
    simp only [List.flatMap_map, Node.restoreImage, List.flatMap_singleton']
  rw [same] at restored
  have packet := Indexed.outputs returnTemplate (bodyFields input)
  rw [return_instantiates input address found] at packet
  have joined := StackMachineComposition.outputs (WordHomomorphismMachine.machine Node.restoreImage) (Indexed.machine returnTemplate)
    (Equiv.refl (Option Alphabet)) ((Indexed.argumentWire (bodyFields input)).map Sum.inl) (Indexed.argumentWire (bodyFields input))
    ((1 : Alphabet) :: encodePacket (positivePacket input address)) _ _ restored (by
      change TM2OutputsInTime (Indexed.machine returnTemplate) ((Indexed.argumentWire (bodyFields input)).map id) _ _
      simpa only [List.map_id] using packet)
  apply WordEqualityMachine.within joined
  simp only [List.length_map]
  omega

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

attribute [local implicit_reducible] returnTagMachine returnDispatch StackMachineComposition.machine
  StackMachineComposition.Dispatch.machine
local instance : Fintype (returnTagMachine.Γ returnTagMachine.k₁) := inferInstanceAs (Fintype Node.GuardCell)
local instance : Inhabited (returnTagMachine.Γ returnTagMachine.k₁) := inferInstanceAs (Inhabited Node.GuardCell)

def resultPacket (input : TaskInput) : Option Packet := (resultRoot input).map (positivePacket input)
def resultWord (input : TaskInput) : List Alphabet := (resultPacket input).elim [0] (fun packet => 1 :: encodePacket packet)

noncomputable def returnPositiveOutputs (input : TaskInput) (address : Nat) (found : resultRoot input = some address) :
    TM2OutputsInTime returnMachine (Indexed.argumentWire (bodyFields input))
      (some ((1 : Alphabet) :: encodePacket (positivePacket input address))) (returnClock input) := by
  have payload := returnPayloadOutputs input address found
  have dispatched := StackMachineComposition.Dispatch.outputs_success returnPayload Node.acceptTag [(0 : Alphabet)]
    (.inr true : Node.GuardCell) ((Indexed.argumentWire (bodyFields input)).map Sum.inl)
    ((1 : Alphabet) :: encodePacket (positivePacket input address)) _ (by decide) payload
  have tagged := returnTagOutputs input
  rw [found] at tagged
  have joined := StackMachineComposition.outputs returnTagMachine returnDispatch (Equiv.refl Node.GuardCell)
    (Indexed.argumentWire (bodyFields input)) (.inr true :: (Indexed.argumentWire (bodyFields input)).map Sum.inl)
    ((1 : Alphabet) :: encodePacket (positivePacket input address)) _ _ tagged (by
      change TM2OutputsInTime returnDispatch ((.inr true :: (Indexed.argumentWire (bodyFields input)).map Sum.inl).map id) _ _
      simpa only [List.map_id, returnDispatch] using dispatched)
  apply WordEqualityMachine.within joined
  simp only [returnClock, returnTagClock, List.length_cons, List.length_map]
  omega

noncomputable def returnRefusedOutputs (input : TaskInput) (missing : resultRoot input = none) :
    TM2OutputsInTime returnMachine (Indexed.argumentWire (bodyFields input))
      (some [(0 : Alphabet)]) (returnClock input) := by
  have refused := StackMachineComposition.Dispatch.outputs_refused returnPayload Node.acceptTag [(0 : Alphabet)]
    (.inr false : Node.GuardCell) ((Indexed.argumentWire (bodyFields input)).map Sum.inl) (by decide)
  have tagged := returnTagOutputs input
  rw [missing] at tagged
  have joined := StackMachineComposition.outputs returnTagMachine returnDispatch (Equiv.refl Node.GuardCell)
    (Indexed.argumentWire (bodyFields input)) (.inr false :: (Indexed.argumentWire (bodyFields input)).map Sum.inl)
    [(0 : Alphabet)] _ _ tagged (by
      change TM2OutputsInTime returnDispatch ((.inr false :: (Indexed.argumentWire (bodyFields input)).map Sum.inl).map id) _ _
      simpa only [List.map_id, returnDispatch] using refused)
  apply WordEqualityMachine.within joined
  simp only [returnClock, returnTagClock, List.length_cons, List.length_map]
  omega

noncomputable def returnOutputs (input : TaskInput) :
    TM2OutputsInTime returnMachine (Indexed.argumentWire (bodyFields input))
      (some (resultWord input)) (returnClock input) := by
  cases found : resultRoot input with
  | none =>
      simpa only [resultWord, resultPacket, found, Option.map_none, Option.elim_none] using returnRefusedOutputs input found
  | some address =>
      simpa only [resultWord, resultPacket, found, Option.map_some, Option.elim_some] using returnPositiveOutputs input address found

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

def prepareProgram := extractProgram.append (retainedQuery.append (retainedLookup.append retainedBody))
def prepareClock (input : TaskInput) :=
  extractClock input + 2 * (Indexed.argumentWire (queryFields input)).length + 2 +
  (retainedQueryClock input + 2 * (Indexed.argumentWire (preparedFields input)).length + 2 +
  (retainedLookupClock input + 2 * (Indexed.argumentWire (resultFields input)).length + 2 + retainedBodyClock input))

noncomputable def prepareOutputs (input : TaskInput) :
    PacketProgram.Runs prepareProgram (Indexed.argumentWire (taskFields input))
      (Indexed.argumentWire (bodyFields input)) (prepareClock input) := by
  have lastTwo := PacketProgram.append_runs _ _ _ _ _ _ _ (retainedLookupOutputs input) (retainedBodyOutputs input)
  have lastThree := PacketProgram.append_runs _ _ _ _ _ _ _ (retainedQueryOutputs input) lastTwo
  exact PacketProgram.append_runs _ _ _ _ _ _ _ (extractOutputs input) lastThree

/-- Original task and context bytes drive every parser, lookup, status test and
returned-root insertion. No returned address or result flag is supplied. -/
def taskMachine := @StackMachineComposition.machine prepareProgram.tm returnMachine
  (PacketProgram.outputFinite prepareProgram) (PacketProgram.outputInhabited prepareProgram) prepareProgram.output

def taskClock (input : TaskInput) := prepareClock input + 2 * (Indexed.argumentWire (bodyFields input)).length + 2 + returnClock input

noncomputable def taskOutputs (input : TaskInput) :
    TM2OutputsInTime taskMachine (Indexed.argumentWire (taskFields input))
      (some (resultWord input)) (taskClock input) := by
  have prepared := prepareOutputs input
  change TM2OutputsInTime prepareProgram.tm ((Indexed.argumentWire (taskFields input)).map id)
    (some ((Indexed.argumentWire (bodyFields input)).map id)) _ at prepared
  simp only [List.map_id] at prepared
  exact @StackMachineComposition.outputs prepareProgram.tm returnMachine
    (PacketProgram.outputFinite prepareProgram) (PacketProgram.outputInhabited prepareProgram) prepareProgram.output
    (Indexed.argumentWire (taskFields input)) (Indexed.argumentWire (bodyFields input)) (resultWord input) _ _ prepared (by
      change TM2OutputsInTime returnMachine ((Indexed.argumentWire (bodyFields input)).map id) _ _
      simpa only [List.map_id] using returnOutputs input)

theorem resultWord_readout (input : TaskInput) : readPacket (resultWord input) = resultPacket input := by
  cases found : resultPacket input with
  | none => simp only [resultWord, found, Option.elim_none]; rfl
  | some packet => simpa only [resultWord, found, Option.elim_some] using readPacket_positive packet

/-- The original packet codec independently decodes the whole completed run. -/
theorem taskReadout (input : TaskInput) (word : List Alphabet)
    (finished : TM2Outputs taskMachine (Indexed.argumentWire (taskFields input)) (some word)) :
    readPacket word = (SharedPremiseExecution.result input.roots input.cache input.query input.goal).map
      (fun root => (input.tail,(root :: input.returned,input.saved))) := by
  rw [StackMachineComposition.outputs_unique finished (taskOutputs input).toEvalsTo, resultWord_readout]
  rfl

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding

variable (definition : ValidatedCalculusLanguageDef)

def stateTaskInput (state : State definition) (query : Nat) (goal : Pattern) (site : Site) (tail : List Task) : TaskInput :=
  ⟨query,goal,site,tail,state.saved.map (fun claim => claim.root),state.values.map (fun claim => claim.root),
    savedGoalRoots definition state,state.checkedPrefix.val.cache⟩

/-- Scope is an explicit enclosing source-admission invariant. The physical
lookup and cached claim check earn the returned address before insertion. -/
noncomputable def controllerTaskOutputs (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal)
    (scope : argumentValidAt 0 goal = true) :
    TM2OutputsInTime taskMachine (Indexed.argumentWire (taskFields (stateTaskInput definition state query goal site tail)))
      (some ((1 : Alphabet) :: encodePacket (statePacket (remember definition state site claim tail))))
      (taskClock (stateTaskInput definition state query goal site tail)) := by
  let input := stateTaskInput definition state query goal site tail
  have earned : resultRoot input = some claim.root := controller_result definition state query goal claim selected same scope
  have run := taskOutputs input
  rw [resultWord, resultPacket, earned, Option.map_some, Option.elim_some] at run
  exact run

theorem controllerTaskReadout (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal)
    (scope : argumentValidAt 0 goal = true) (word : List Alphabet)
    (finished : TM2Outputs taskMachine (Indexed.argumentWire (taskFields (stateTaskInput definition state query goal site tail))) (some word)) :
    readPacket word = some (statePacket (remember definition state site claim tail)) := by
  rw [StackMachineComposition.outputs_unique finished
    (controllerTaskOutputs definition state query goal site tail claim selected same scope).toEvalsTo]
  exact readPacket_positive _

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.PacketPop

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

def originalData (head : Task) (tail : List Task) (saved returned : List Nat) :=
  packetCodec.put (head :: tail,(returned,saved))
def originalFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 1 → List Alphabet :=
  fun _ => encodePacket (head :: tail,(returned,saved))
def taskFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 2 → List Alphabet :=
  Fin.snoc (originalFields head tail saved returned) (encodeTask head)
def tailFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 3 → List Alphabet :=
  Fin.snoc (taskFields head tail saved returned) (encodeWork tail)
def savedFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 4 → List Alphabet :=
  Fin.snoc (tailFields head tail saved returned) (encodeRoots saved)
def returnedFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 5 → List Alphabet :=
  Fin.snoc (savedFields head tail saved returned) (encodeRoots returned)
def branchFields (head : Task) (tail : List Task) (saved returned : List Nat) : Fin 4 → List Alphabet :=
  ![encodeTask head,encodeWork tail,encodeRoots saved,encodeRoots returned]

def taskPath : List Bool := [false,false]
def tailPath : List Bool := [false,true]
def savedPath : List Bool := [true,true]
def returnedPath : List Bool := [true,false]

def extractProgram : PacketProgram := (Node.retainingProgram (0 : Fin 1) taskPath).append
  ((Node.retainingProgram (0 : Fin 2) tailPath).append
    ((Node.retainingProgram (0 : Fin 3) savedPath).append (Node.retainingProgram (0 : Fin 4) returnedPath)))

def extractClock (head : Task) (tail : List Task) (saved returned : List Nat) :=
  Node.retainClock taskPath (originalFields head tail saved returned) (originalData head tail saved returned) (taskCodec.put head) +
  2 * (Indexed.argumentWire (taskFields head tail saved returned)).length + 2 +
  (Node.retainClock tailPath (taskFields head tail saved returned) (originalData head tail saved returned) (workCodec.put tail) +
  2 * (Indexed.argumentWire (tailFields head tail saved returned)).length + 2 +
  (Node.retainClock savedPath (tailFields head tail saved returned) (originalData head tail saved returned) ((Codec.list Codec.nat).put saved) +
  2 * (Indexed.argumentWire (savedFields head tail saved returned)).length + 2 +
  Node.retainClock returnedPath (savedFields head tail saved returned) (originalData head tail saved returned) ((Codec.list Codec.nat).put returned)))

noncomputable def extractOutputs (head : Task) (tail : List Task) (saved returned : List Nat) :
    PacketProgram.Runs extractProgram (Indexed.argumentWire (originalFields head tail saved returned))
      (Indexed.argumentWire (returnedFields head tail saved returned)) (extractClock head tail saved returned) := by
  have task := Node.retainingProgramOutputs (0 : Fin 1) taskPath (originalFields head tail saved returned)
    (originalData head tail saved returned) (taskCodec.put head) (by rfl) (by rfl)
  have work := Node.retainingProgramOutputs (0 : Fin 2) tailPath (taskFields head tail saved returned)
    (originalData head tail saved returned) (workCodec.put tail) (by rfl) (by rfl)
  have savedRun := Node.retainingProgramOutputs (0 : Fin 3) savedPath (tailFields head tail saved returned)
    (originalData head tail saved returned) ((Codec.list Codec.nat).put saved) (by rfl) (by rfl)
  have returnedRun := Node.retainingProgramOutputs (0 : Fin 4) returnedPath (savedFields head tail saved returned)
    (originalData head tail saved returned) ((Codec.list Codec.nat).put returned) (by rfl) (by rfl)
  have lastTwo := PacketProgram.append_runs _ _ _ _ _ _ _ savedRun returnedRun
  have lastThree := PacketProgram.append_runs _ _ _ _ _ _ _ work lastTwo
  exact PacketProgram.append_runs _ _ _ _ _ _ _ task lastThree

attribute [local implicit_reducible] FramedFieldSelection.machine

def reorderProgram : PacketProgram :=
  ⟨FramedFieldSelection.machine (Γ := Alphabet) ([1,2,3,4] : List (Fin 5)),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩
def program := extractProgram.append reorderProgram

def clock (head : Task) (tail : List Task) (saved returned : List Nat) :=
  extractClock head tail saved returned + 2 * (Indexed.argumentWire (returnedFields head tail saved returned)).length + 2 +
    44 * ((Indexed.argumentWire (returnedFields head tail saved returned)).length + 1)

noncomputable def reorderOutputs (head : Task) (tail : List Task) (saved returned : List Nat) :
    PacketProgram.Runs reorderProgram (Indexed.argumentWire (returnedFields head tail saved returned))
      (Indexed.argumentWire (branchFields head tail saved returned))
      (44 * ((Indexed.argumentWire (returnedFields head tail saved returned)).length + 1)) := by
  have selected := FramedFieldSelection.outputs ([1,2,3,4] : List (Fin 5)) (returnedFields head tail saved returned)
  have same : Indexed.frame (([1,2,3,4] : List (Fin 5)).map (returnedFields head tail saved returned)) =
      Indexed.argumentWire (branchFields head tail saved returned) := rfl
  rw [same] at selected
  change TM2OutputsInTime reorderProgram.tm ((Indexed.argumentWire (returnedFields head tail saved returned)).map id)
    (some ((Indexed.argumentWire (branchFields head tail saved returned)).map id)) _
  simpa only [reorderProgram, List.map_id, List.length_cons, List.length_nil] using selected

/-- A complete original pending-work/root packet physically yields its top task,
remaining work, saved roots and returned roots in the branch calling convention. -/
noncomputable def outputs (head : Task) (tail : List Task) (saved returned : List Nat) :
    PacketProgram.Runs program (Indexed.argumentWire (originalFields head tail saved returned))
      (Indexed.argumentWire (branchFields head tail saved returned)) (clock head tail saved returned) :=
  PacketProgram.append_runs _ _ _ _ _ _ _ (extractOutputs head tail saved returned) (reorderOutputs head tail saved returned)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.PacketPop

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

def packetMachine (definition : CalculusLanguageDef) :=
  @StackMachineComposition.machine PacketPop.program.tm (authoredMachine definition)
    (PacketProgram.outputFinite PacketPop.program) (PacketProgram.outputInhabited PacketPop.program) PacketPop.program.output

def packetClock (definition : ValidatedCalculusLanguageDef) (input : Input) :=
  PacketPop.clock (.visit input.goal (.node input.ruleInstance input.proofs) input.site) input.tail input.saved input.returned +
    2 * (Indexed.argumentWire (startFields input)).length + 2 + authoredClock definition input

/-- One whole packet-stack transition earns its top task and old tail, selects
the original authored row, executes guards/jobs, and enqueues the exact children. -/
noncomputable def packetOutputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) :
    TM2OutputsInTime (packetMachine definition.1)
      (Indexed.argumentWire (PacketPop.originalFields (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
        input.tail input.saved input.returned)) (some (sourceWord definition input)) (packetClock definition input) := by
  have popped := PacketPop.outputs (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
    input.tail input.saved input.returned
  change TM2OutputsInTime PacketPop.program.tm
    ((Indexed.argumentWire (PacketPop.originalFields (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
      input.tail input.saved input.returned)).map id)
    (some ((Indexed.argumentWire (startFields input)).map id)) _ at popped
  simp only [List.map_id] at popped
  exact @StackMachineComposition.outputs PacketPop.program.tm (authoredMachine definition.1)
    (PacketProgram.outputFinite PacketPop.program) (PacketProgram.outputInhabited PacketPop.program) PacketPop.program.output
    (Indexed.argumentWire (PacketPop.originalFields (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
      input.tail input.saved input.returned)) (Indexed.argumentWire (startFields input)) (sourceWord definition input)
    _ _ popped (by
      change TM2OutputsInTime (authoredMachine definition.1) ((Indexed.argumentWire (startFields input)).map id) _ _
      simpa only [List.map_id] using totalOutputs definition firstOrder input)

theorem packetReadout (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (input : Input) (word : List Alphabet)
    (finished : TM2Outputs (packetMachine definition.1)
      (Indexed.argumentWire (PacketPop.originalFields (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
        input.tail input.saved input.returned)) (some word)) :
    readPacket word = sourceResult definition input := by
  rw [StackMachineComposition.outputs_unique finished (packetOutputs definition firstOrder input).toEvalsTo]
  exact sourceWord_readout definition input

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Node

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open ChronologicalDriver ChronologicalTaskEncoding

def pendingTask (input : TaskInput) : Task := .visit input.goal (.premise input.query) input.site
def pendingData (input : TaskInput) := PacketPop.originalData (pendingTask input) input.tail input.saved input.returned

def contextFields (input : TaskInput) : Fin 3 → List Alphabet :=
  ![encodePacket (pendingTask input :: input.tail,(input.returned,input.saved)),
    table (indexed input.roots),table (EncodedTable.rows theoremCodec input.cache)]
def poppedTaskFields (input : TaskInput) : Fin 4 → List Alphabet := Fin.snoc (contextFields input) (encodeTask (pendingTask input))
def poppedTailFields (input : TaskInput) : Fin 5 → List Alphabet := Fin.snoc (poppedTaskFields input) (encodeWork input.tail)
def poppedSavedFields (input : TaskInput) : Fin 6 → List Alphabet := Fin.snoc (poppedTailFields input) (encodeRoots input.saved)
def poppedReturnedFields (input : TaskInput) : Fin 7 → List Alphabet := Fin.snoc (poppedSavedFields input) (encodeRoots input.returned)

def popExtractProgram : PacketProgram := (Node.retainingProgram (0 : Fin 3) PacketPop.taskPath).append
  ((Node.retainingProgram (0 : Fin 4) PacketPop.tailPath).append
    ((Node.retainingProgram (0 : Fin 5) PacketPop.savedPath).append (Node.retainingProgram (0 : Fin 6) PacketPop.returnedPath)))

def popExtractClock (input : TaskInput) :=
  Node.retainClock PacketPop.taskPath (contextFields input) (pendingData input) (taskCodec.put (pendingTask input)) +
  2 * (Indexed.argumentWire (poppedTaskFields input)).length + 2 +
  (Node.retainClock PacketPop.tailPath (poppedTaskFields input) (pendingData input) (workCodec.put input.tail) +
  2 * (Indexed.argumentWire (poppedTailFields input)).length + 2 +
  (Node.retainClock PacketPop.savedPath (poppedTailFields input) (pendingData input) ((Codec.list Codec.nat).put input.saved) +
  2 * (Indexed.argumentWire (poppedSavedFields input)).length + 2 +
  Node.retainClock PacketPop.returnedPath (poppedSavedFields input) (pendingData input) ((Codec.list Codec.nat).put input.returned)))

noncomputable def popExtractOutputs (input : TaskInput) :
    PacketProgram.Runs popExtractProgram (Indexed.argumentWire (contextFields input))
      (Indexed.argumentWire (poppedReturnedFields input)) (popExtractClock input) := by
  have task := Node.retainingProgramOutputs (0 : Fin 3) PacketPop.taskPath (contextFields input)
    (pendingData input) (taskCodec.put (pendingTask input)) (by rfl) (by rfl)
  have tail := Node.retainingProgramOutputs (0 : Fin 4) PacketPop.tailPath (poppedTaskFields input)
    (pendingData input) (workCodec.put input.tail) (by rfl) (by rfl)
  have saved := Node.retainingProgramOutputs (0 : Fin 5) PacketPop.savedPath (poppedTailFields input)
    (pendingData input) ((Codec.list Codec.nat).put input.saved) (by rfl) (by rfl)
  have returned := Node.retainingProgramOutputs (0 : Fin 6) PacketPop.returnedPath (poppedSavedFields input)
    (pendingData input) ((Codec.list Codec.nat).put input.returned) (by rfl) (by rfl)
  have lastTwo := PacketProgram.append_runs _ _ _ _ _ _ _ saved returned
  have lastThree := PacketProgram.append_runs _ _ _ _ _ _ _ tail lastTwo
  exact PacketProgram.append_runs _ _ _ _ _ _ _ task lastThree

attribute [local implicit_reducible] FramedFieldSelection.machine

def popReorderProgram : PacketProgram :=
  ⟨FramedFieldSelection.machine (Γ := Alphabet) ([3,4,5,6,1,2] : List (Fin 7)),
    Equiv.refl (Option Alphabet), Equiv.refl (Option Alphabet)⟩
def popProgram := popExtractProgram.append popReorderProgram

def popClock (input : TaskInput) := popExtractClock input + 2 * (Indexed.argumentWire (poppedReturnedFields input)).length + 2 +
  60 * ((Indexed.argumentWire (poppedReturnedFields input)).length + 1)

noncomputable def popReorderOutputs (input : TaskInput) :
    PacketProgram.Runs popReorderProgram (Indexed.argumentWire (poppedReturnedFields input))
      (Indexed.argumentWire (taskFields input)) (60 * ((Indexed.argumentWire (poppedReturnedFields input)).length + 1)) := by
  have selected := FramedFieldSelection.outputs ([3,4,5,6,1,2] : List (Fin 7)) (poppedReturnedFields input)
  have same : Indexed.frame (([3,4,5,6,1,2] : List (Fin 7)).map (poppedReturnedFields input)) =
      Indexed.argumentWire (taskFields input) := rfl
  rw [same] at selected
  change TM2OutputsInTime popReorderProgram.tm ((Indexed.argumentWire (poppedReturnedFields input)).map id)
    (some ((Indexed.argumentWire (taskFields input)).map id)) _
  simpa only [List.map_id, popReorderProgram, List.length_cons, List.length_nil] using selected

noncomputable def popOutputs (input : TaskInput) :
    PacketProgram.Runs popProgram (Indexed.argumentWire (contextFields input))
      (Indexed.argumentWire (taskFields input)) (popClock input) :=
  PacketProgram.append_runs _ _ _ _ _ _ _ (popExtractOutputs input) (popReorderOutputs input)

/-- Pending work is physically popped from its original packet. The original
saved-root table and theorem table are retained into the real lookup branch. -/
def packetMachine := @StackMachineComposition.machine popProgram.tm taskMachine
  (PacketProgram.outputFinite popProgram) (PacketProgram.outputInhabited popProgram) popProgram.output

def packetClock (input : TaskInput) := popClock input + 2 * (Indexed.argumentWire (taskFields input)).length + 2 + taskClock input

noncomputable def packetOutputs (input : TaskInput) :
    TM2OutputsInTime packetMachine (Indexed.argumentWire (contextFields input))
      (some (resultWord input)) (packetClock input) := by
  have popped := popOutputs input
  change TM2OutputsInTime popProgram.tm ((Indexed.argumentWire (contextFields input)).map id)
    (some ((Indexed.argumentWire (taskFields input)).map id)) _ at popped
  simp only [List.map_id] at popped
  exact @StackMachineComposition.outputs popProgram.tm taskMachine
    (PacketProgram.outputFinite popProgram) (PacketProgram.outputInhabited popProgram) popProgram.output
    (Indexed.argumentWire (contextFields input)) (Indexed.argumentWire (taskFields input)) (resultWord input) _ _ popped (by
      change TM2OutputsInTime taskMachine ((Indexed.argumentWire (taskFields input)).map id) _ _
      simpa only [List.map_id] using taskOutputs input)

theorem packetReadout (input : TaskInput) (word : List Alphabet)
    (finished : TM2Outputs packetMachine (Indexed.argumentWire (contextFields input)) (some word)) :
    readPacket word = (SharedPremiseExecution.result input.roots input.cache input.query input.goal).map
      (fun root => (input.tail,(root :: input.returned,input.saved))) := by
  rw [StackMachineComposition.outputs_unique finished (packetOutputs input).toEvalsTo, resultWord_readout]
  rfl

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

open Turing StateTransition Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ChronologicalDriver ChronologicalTaskEncoding

/-- The original framed work stack physically pops exactly one task. Caller
payload, prepared work and both root streams remain present in every snapshot. -/
def pop_task (task : Task) (tail : List Task) (register : Register)
    (prepared payload saved returned : List Cell) :
    EvalsToInTime (machine false).step
      (config false (some .pop) register (workStack (task :: tail)) prepared [] payload saved returned)
      (some (config false none none (workStack tail) prepared []
        ((encodeTask task).map some ++ payload) saved returned))
      (2 * (encodeTask task).length + 2) := by
  rw [workStack_cons]
  simpa only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] using
    pop_run false (encodeTask task) register (workStack tail) prepared [] payload saved returned

/-- Prefix insertion keeps the original machine-policy order and leaves the
old continuation and both root streams unchanged. Every transfer is counted. -/
def push_tasks (workPrefix tail : List Task) (register : Register) (payload saved returned : List Cell) :
    EvalsToInTime (machine true).step
      (config true (some .push) register (workStack tail) (workStack workPrefix) [] payload saved returned)
      (some (config true none none (workStack (workPrefix ++ tail)) [] [] payload saved returned))
      (2 * (workStack workPrefix).length + 2) := by
  rw [workStack_append]
  simpa only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] using
    push_run true (workStack workPrefix) register (workStack tail) [] payload saved returned

theorem pop_task_readout (task : Task) : decodeTask (encodeTask task) = some task :=
  decodeTask_encodeTask task

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open ChronologicalDriver ChronologicalTaskEncoding

noncomputable def controller_node_packet_outputs (definition : ValidatedCalculusLanguageDef)
    (firstOrder : FirstOrderCalculus definition.1) (state : ChronologicalDriver.State definition)
    (ruleInstance : RuleInstance) (goal : Pattern) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (computedPremises : List Pattern)
    (work : state.todo = .visit goal (.node ruleInstance proofs) site :: tail)
    (accepted : instantiateRule? definition ruleInstance = some (computedPremises,goal))
    (childCount : proofs.length = computedPremises.length) :
    TM2OutputsInTime (Node.packetMachine definition.1)
      (Indexed.frame [encodePacket (statePacket state)])
      (some ((1 : Alphabet) :: encodePacket (statePacket (nodeNext state ruleInstance goal proofs site tail computedPremises))))
      (Node.packetClock definition (nodeStateInput state ruleInstance goal proofs site tail)) := by
  let input := nodeStateInput state ruleInstance goal proofs site tail
  have run := Node.packetOutputs definition firstOrder input
  have output : Node.sourceWord definition input = 1 :: encodePacket (Node.positivePacket input computedPremises) := by
    simp only [Node.sourceWord, Node.sourceResult, input, nodeStateInput, accepted, childCount,
      and_self, ↓reduceIte, Option.elim_some]
  rw [output] at run
  have same : Indexed.argumentWire (PacketPop.originalFields (.visit input.goal (.node input.ruleInstance input.proofs) input.site)
      input.tail input.saved input.returned) = Indexed.frame [encodePacket (statePacket state)] := by
    simp only [Indexed.argumentWire, PacketPop.originalFields, List.finRange_succ, List.finRange_zero,
      List.map_cons, List.map_nil, statePacket, work, input, nodeStateInput]
  rw [same] at run
  exact run

namespace Premise
variable (definition : ValidatedCalculusLanguageDef)

noncomputable def controllerPacketOutputs (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal)
    (scope : argumentValidAt 0 goal = true) :
    TM2OutputsInTime packetMachine
      (Indexed.argumentWire (contextFields (stateTaskInput definition state query goal site tail)))
      (some ((1 : Alphabet) :: encodePacket (statePacket (remember definition state site claim tail))))
      (packetClock (stateTaskInput definition state query goal site tail)) := by
  let input := stateTaskInput definition state query goal site tail
  have earned : resultRoot input = some claim.root := controller_result definition state query goal claim selected same scope
  have run := packetOutputs input
  rw [resultWord, resultPacket, earned, Option.map_some, Option.elim_some] at run
  exact run

end Premise
end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Controls

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
open ChronologicalDriver ChronologicalTaskEncoding
open ChronologicalDriver.Correctness.Controls
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation.Controls

/-- The site and continuation contain data that cannot enter finite control. -/
def site : Site := ⟨("origin-λ\x00雪",17),[0,2^80+3]⟩
def ordered : Node.Input :=
  ⟨⟨twoChildRule.id,[binderValue,secondValue]⟩,judgmentP secondValue,[.premise 7,.premise 3],site,
    [.finish (judgmentP secondValue)],[17,3,17],[42,9]⟩
def repeated : Node.Input :=
  ⟨⟨twoChildRule.id,[binderValue,binderValue]⟩,judgmentP binderValue,[.premise 7,.premise 7],
    ordered.site,ordered.tail,ordered.saved,ordered.returned⟩
def nested : Node.Input :=
  { ordered with proofs := [.node ⟨dataRule.id,[binderValue]⟩ [],.premise (2^70+9)] }
def nullary : Node.Input :=
  ⟨⟨dataRule.id,[binderValue]⟩,judgmentP binderValue,[],site,[.finish (judgmentP binderValue)],[5,5],[9]⟩

theorem ordered_source : Node.sourceResult twoChildCalculus ordered =
    some (Node.positivePacket ordered [judgmentP binderValue,judgmentP secondValue]) := by
  have accepted : instantiateRule? twoChildCalculus ordered.ruleInstance =
      some ([judgmentP binderValue,judgmentP secondValue],ordered.goal) := by decide +kernel
  simp only [Node.sourceResult, accepted]
  rw [if_pos (by decide)]
theorem repeated_source : Node.sourceResult twoChildCalculus repeated =
    some (Node.positivePacket repeated [judgmentP binderValue,judgmentP binderValue]) := by
  have accepted : instantiateRule? twoChildCalculus repeated.ruleInstance =
      some ([judgmentP binderValue,judgmentP binderValue],repeated.goal) := by decide +kernel
  simp only [Node.sourceResult, accepted]
  rw [if_pos (by decide)]
theorem nested_source : Node.sourceResult twoChildCalculus nested =
    some (Node.positivePacket nested [judgmentP binderValue,judgmentP secondValue]) := by
  have accepted : instantiateRule? twoChildCalculus nested.ruleInstance =
      some ([judgmentP binderValue,judgmentP secondValue],nested.goal) := by decide +kernel
  simp only [Node.sourceResult, accepted]
  rw [if_pos (by decide)]
theorem nullary_source : Node.sourceResult twoChildCalculus nullary = some (Node.positivePacket nullary []) := by
  have accepted : instantiateRule? twoChildCalculus nullary.ruleInstance = some ([],nullary.goal) := by decide +kernel
  simp only [Node.sourceResult, accepted]
  rw [if_pos (by decide)]
theorem changed_goal_refused : Node.sourceResult twoChildCalculus {ordered with goal := judgmentP binderValue} = none := by decide +kernel
theorem missing_child_refused : Node.sourceResult twoChildCalculus {ordered with proofs := [.premise 7]} = none := by decide +kernel
theorem excess_child_refused : Node.sourceResult twoChildCalculus {nullary with proofs := [.premise 7]} = none := by decide +kernel
theorem absent_row_refused : Node.sourceResult twoChildCalculus {nullary with ruleInstance := ⟨⟨"absent"⟩,[]⟩} = none := by decide +kernel
def escaping : Node.Input :=
  ⟨⟨dataRule.id,[.lambda none (.bvar 1)]⟩,judgmentP (.lambda none (.bvar 1)),[],site,
    nullary.tail,nullary.saved,nullary.returned⟩
theorem escaping_argument_refused : Node.sourceResult twoChildCalculus escaping = none := by decide +kernel

noncomputable def ordered_execution :
    TM2OutputsInTime (Node.packetMachine twoChildCalculus.1)
      (Indexed.argumentWire (PacketPop.originalFields (.visit ordered.goal (.node ordered.ruleInstance ordered.proofs) ordered.site)
        ordered.tail ordered.saved ordered.returned))
      (some ((1 : Alphabet) :: encodePacket (Node.positivePacket ordered [judgmentP binderValue,judgmentP secondValue])))
      (Node.packetClock twoChildCalculus ordered) := by
  have run := Node.packetOutputs twoChildCalculus twoChild_firstOrder ordered
  simp only [Node.sourceWord, ordered_source, Option.elim_some] at run
  exact run

noncomputable def missing_child_execution :
    TM2OutputsInTime (Node.packetMachine twoChildCalculus.1)
      (Indexed.argumentWire (PacketPop.originalFields (.visit ordered.goal (.node ordered.ruleInstance [.premise 7]) ordered.site)
        ordered.tail ordered.saved ordered.returned)) (some [(0 : Alphabet)])
      (Node.packetClock twoChildCalculus {ordered with proofs := [.premise 7]}) := by
  have run := Node.packetOutputs twoChildCalculus twoChild_firstOrder {ordered with proofs := [.premise 7]}
  simp only [Node.sourceWord, missing_child_refused, Option.elim_none] at run
  exact run

def premise : Premise.TaskInput :=
  ⟨0,SharedPremiseExecution.Controls.goal,site,[.finish SharedPremiseExecution.Controls.goal],[1,0],[17,4],
    #[1,0],#[SharedPremiseExecution.Controls.conditional,SharedPremiseExecution.Controls.original]⟩

theorem premise_physical_root : Premise.resultRoot premise = some 1 := SharedPremiseExecution.Controls.original_physical_root
theorem premise_future_refused : Premise.resultRoot {premise with query := 2} = none := by decide +kernel
theorem premise_scope_refused : Premise.resultRoot {premise with goal := .bvar 0} = none := by
  exact SharedPremiseExecution.invalid_scope_refused _ _ _ _ (by rfl)

noncomputable def premise_execution :
    TM2OutputsInTime Premise.packetMachine (Indexed.argumentWire (Premise.contextFields premise))
      (some ((1 : Alphabet) :: encodePacket (Premise.positivePacket premise 1))) (Premise.packetClock premise) := by
  have run := Premise.packetOutputs premise
  simp only [Premise.resultWord, Premise.resultPacket, premise_physical_root, Option.map_some, Option.elim_some] at run
  exact run

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Controls

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise
open Turing Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec.Binary Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open ChronologicalDriver ChronologicalTaskEncoding
variable (definition : ValidatedCalculusLanguageDef)

/-- The input has the actual controller's complete pending packet and physical
root/value tables. Query, goal, site and tail are obtained by the machine. -/
def stateContextFields (state : State definition) : Fin 3 → List Alphabet :=
  ![encodePacket (statePacket state),table (indexed (savedGoalRoots definition state)),
    table (EncodedTable.rows theoremCodec state.checkedPrefix.val.cache)]

theorem stateContextFields_eq (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (work : state.todo = .visit goal (.premise query) site :: tail) :
    stateContextFields definition state = contextFields (stateTaskInput definition state query goal site tail) := by
  simp only [stateContextFields, contextFields, stateTaskInput, pendingTask, statePacket, work]

noncomputable def controller_state_packet_outputs (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (work : state.todo = .visit goal (.premise query) site :: tail)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal)
    (scope : argumentValidAt 0 goal = true) :
    TM2OutputsInTime packetMachine (Indexed.argumentWire (stateContextFields definition state))
      (some ((1 : Alphabet) :: encodePacket (statePacket (remember definition state site claim tail))))
      (packetClock (stateTaskInput definition state query goal site tail)) := by
  rw [stateContextFields_eq definition state query goal site tail work]
  exact controllerPacketOutputs definition state query goal site tail claim selected same scope

theorem controller_state_packet_readout (state : State definition) (query : Nat) (goal : Pattern)
    (site : Site) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (work : state.todo = .visit goal (.premise query) site :: tail)
    (selected : state.saved[query]? = some claim) (same : claim.goal = goal)
    (scope : argumentValidAt 0 goal = true) (word : List Alphabet)
    (finished : TM2Outputs packetMachine (Indexed.argumentWire (stateContextFields definition state)) (some word)) :
    readPacket word = some (statePacket (remember definition state site claim tail)) := by
  rw [Mettapedia.Computability.StackMachineComposition.outputs_unique finished
    (controller_state_packet_outputs definition state query goal site tail claim work selected same scope).toEvalsTo]
  exact readPacket_positive _
end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver
variable (definition : ValidatedCalculusLanguageDef)

/-- Pending closes have earned their goal from an admitted node. Stored claims
have earned it from such a close or from a previously goalScope saved claim. -/
structure Invariant (state : State definition) : Prop where
  values : ∀ claim ∈ state.values,argumentValidAt 0 claim.goal=true
  saved : ∀ claim ∈ state.saved,argumentValidAt 0 claim.goal=true
  pendingClose : ∀ goal ruleInstance premises site,
    Task.close goal ruleInstance premises site ∈ state.todo → argumentValidAt 0 goal=true

def statusInvariant : Status definition → Prop
  | .running state | .done state _ | .refused _ state => Invariant definition state

theorem rule_conclusion_scope {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
    (accepted : instantiateRule? definition ruleInstance = some (premises,goal)) :
    argumentValidAt 0 goal=true := by
  have safety := (instantiateRule?_eq_some_iff_application.mp accepted).conclusion_safety
  simpa only [argumentValidAt, Pattern.isGround, Bool.and_eq_true] using safety

theorem claimAt_goal {checkedPrefix : Prefix definition} {goal : Pattern} {root : Nat}
    {claim : Claim definition checkedPrefix} (earned : claimAt? definition checkedPrefix goal root=some claim) :
    claim.goal=goal := by
  unfold claimAt? at earned
  split at earned
  · cases earned
  · split at earned
    · cases Option.some.inj earned
      rfl
    · cases earned

theorem close_not_mem_children (goal : Pattern) (ruleInstance : RuleInstance) (premises : List Pattern)
    (site parent : Site) (index : Nat) (jobs : List (Pattern × RawOpenProof)) :
    Task.close goal ruleInstance premises site ∉ children parent index jobs := by
  induction jobs generalizing index with
  | nil => simp [children]
  | cons head tail ih =>
      cases head
      simp only [children,List.mem_cons,reduceCtorEq,false_or]
      exact ih (index+1)

theorem tail_scoped (state : State definition) (valid : Invariant definition state)
    (head : Task) (tail : List Task) (work : state.todo=head::tail)
    (goal : Pattern) (ruleInstance : RuleInstance) (premises : List Pattern) (site : Site)
    (member : Task.close goal ruleInstance premises site ∈ tail) : argumentValidAt 0 goal=true :=
  valid.pendingClose goal ruleInstance premises site (work ▸ List.mem_cons_of_mem head member)

theorem remember_scoped (state : State definition) (valid : Invariant definition state)
    (site : Site) (claim : Claim definition state.checkedPrefix) (tail : List Task)
    (goalScope : argumentValidAt 0 claim.goal=true)
    (tailScoped : ∀ goal ruleInstance premises site,
      Task.close goal ruleInstance premises site ∈ tail → argumentValidAt 0 goal=true) :
    Invariant definition (remember definition state site claim tail) := by
  refine ⟨?_,valid.saved,tailScoped⟩
  intro value member
  rcases List.mem_cons.mp member with same | member
  · subst value
    exact goalScope
  · exact valid.values value member

theorem node_scoped (state : State definition) (valid : Invariant definition state)
    (goal : Pattern) (ruleInstance : RuleInstance) (proofs : List RawOpenProof) (site : Site) (tail : List Task)
    (premises : List Pattern) (work : state.todo=Task.visit goal (.node ruleInstance proofs) site::tail)
    (accepted : instantiateRule? definition ruleInstance=some (premises,goal)) :
    Invariant definition {state with todo:=children site 0 (premises.zip proofs)++Task.close goal ruleInstance premises site::tail} := by
  refine ⟨valid.values,valid.saved,?_⟩
  intro target selectedRule children targetSite member
  rcases List.mem_append.mp member with member | member
  · exact False.elim (close_not_mem_children target selectedRule children targetSite site 0 _ member)
  · rcases List.mem_cons.mp member with same | member
    · cases same
      exact rule_conclusion_scope definition accepted
    · exact tail_scoped definition state valid _ tail work target selectedRule children targetSite member

theorem kept_scoped {before after : Prefix definition} (kept : InferenceCompiler.KeepsOld before.val after.val)
    (claims : List (Claim definition before))
    (valid : ∀ claim ∈ claims,argumentValidAt 0 claim.goal=true) :
    ∀ claim ∈ claims.map (Claim.keep definition kept),argumentValidAt 0 claim.goal=true := by
  intro claim member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact valid original originalMember

theorem close_scoped (state : State definition) (valid : Invariant definition state)
    (goal : Pattern) (ruleInstance : RuleInstance) (premises : List Pattern) (site : Site) (tail : List Task)
    (work : state.todo=Task.close goal ruleInstance premises site::tail)
    (extension : Extension definition state.checkedPrefix)
    (claim : Claim definition extension.after)
    (earned : claimAt? definition extension.after goal extension.root=some claim) :
    Invariant definition (remember definition
      {checkedPrefix:=extension.after,todo:=tail,
       values:=(state.values.drop premises.length).map (Claim.keep definition extension.kept),
       saved:=state.saved.map (Claim.keep definition extension.kept),
       occurrences:=state.occurrences.map fun occurrence => (occurrence.1,Claim.keep definition extension.kept occurrence.2)}
      site claim tail) := by
  have goalScoped := valid.pendingClose goal ruleInstance premises site (work ▸ List.mem_cons_self)
  have claimScoped : argumentValidAt 0 claim.goal=true := by rw [claimAt_goal definition earned];exact goalScoped
  apply remember_scoped definition
  · refine ⟨?_,kept_scoped definition extension.kept state.saved valid.saved,?_⟩
    · apply kept_scoped
      intro value member
      exact valid.values value (List.mem_of_mem_drop member)
    · intro target selectedRule children targetSite member
      exact tail_scoped definition state valid _ tail work target selectedRule children targetSite member
  · exact claimScoped
  · intro target selectedRule children targetSite member
    exact tail_scoped definition state valid _ tail work target selectedRule children targetSite member

theorem save_scoped (state : State definition) (valid : Invariant definition state)
    (goal : Pattern) (index : Nat) (tail : List Task) (claim : Claim definition state.checkedPrefix)
    (work : state.todo=Task.save goal index::tail) (values : state.values=[claim]) :
    Invariant definition {state with todo:=tail,values:=[],saved:=state.saved++[claim]} := by
  refine ⟨?_,?_,?_⟩
  · intro value member;cases member
  · intro value member
    rcases List.mem_append.mp member with member | member
    · exact valid.saved value member
    · have same : value=claim := List.mem_singleton.mp member
      subst value
      exact valid.values claim (values ▸ List.mem_cons_self)
  · intro target selectedRule children targetSite member
    exact tail_scoped definition state valid _ tail work target selectedRule children targetSite member

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver
variable (definition : ValidatedCalculusLanguageDef)

/-- Scope follows the actual source controller, including refused and completed
states. No source-check callback supplies this invariant to the machine. -/
theorem step_invariant (status : Status definition) (valid : statusInvariant definition status) :
    statusInvariant definition (step definition status) := by
  cases status with
  | done state claim => exact valid
  | refused error state => exact valid
  | running state =>
      change Invariant definition state at valid
      cases work : state.todo with
      | nil => simpa only [step,work,statusInvariant] using valid
      | cons head tail =>
          cases head with
          | visit goal proof site =>
              cases proof with
              | premise index =>
                  cases selected : state.saved[index]? with
                  | none => simpa only [step,work,selected,statusInvariant] using valid
                  | some claim =>
                      by_cases same : claim.goal=goal
                      · simp only [step,work,selected,same,↓reduceIte,statusInvariant]
                        apply remember_scoped definition state valid
                        · exact valid.saved claim (List.mem_of_getElem? selected)
                        · intro target selectedRule premises targetSite member
                          exact tail_scoped definition state valid _ tail work target selectedRule premises targetSite member
                      · simpa only [step,work,selected,same,↓reduceIte,statusInvariant] using valid
              | node ruleInstance proofs =>
                  cases accepted : instantiateRule? definition ruleInstance with
                  | none => simpa only [step,work,accepted,statusInvariant] using valid
                  | some pair =>
                      rcases pair with ⟨premises,conclusion⟩
                      by_cases same : conclusion=goal
                      · subst conclusion
                        by_cases count : premises.length=proofs.length
                        · simpa only [step,work,accepted,count,↓reduceIte,statusInvariant] using
                            node_scoped definition state valid goal ruleInstance proofs site tail premises work accepted
                        · simpa only [step,work,accepted,count,↓reduceIte,statusInvariant] using valid
                      · simpa only [step,work,accepted,same,↓reduceIte,statusInvariant] using valid
          | close goal ruleInstance premises site =>
              simp only [step,work]
              split
              · split
                · cases emitted : InferenceRuleExpansion.emitRule? definition ruleInstance
                      (((state.values.take premises.length).reverse).map fun claim => claim.out) site.origin with
                  | none => simpa only [emitted,statusInvariant] using valid
                  | some block =>
                      cases expanded : extend? definition state.checkedPrefix
                          (((state.values.take premises.length).reverse).map fun claim => claim.root) block with
                      | none => simpa only [emitted,expanded,statusInvariant] using valid
                      | some extension =>
                          cases earned : claimAt? definition extension.after goal extension.root with
                          | none => simpa only [emitted,expanded,earned,statusInvariant] using valid
                          | some claim =>
                              simpa only [emitted,expanded,earned,statusInvariant] using
                                close_scoped definition state valid goal ruleInstance premises site tail work extension claim earned
                · exact valid
              · exact valid
          | save goal index =>
              cases values : state.values with
              | nil => simpa only [step,work,values,statusInvariant] using valid
              | cons claim claims =>
                  cases claims with
                  | nil =>
                      by_cases correct : claim.goal=goal ∧ state.saved.length=index
                      · simpa only [step,work,values,correct,and_self,↓reduceIte,statusInvariant] using
                          save_scoped definition state valid goal index tail claim work values
                      · simpa only [step,work,values,correct,and_self,↓reduceIte,statusInvariant] using valid
                  | cons second rest => simpa only [step,work,values,statusInvariant] using valid
          | finish goal =>
              cases tail with
              | cons task rest => simpa only [step,work,statusInvariant] using valid
              | nil =>
                  cases values : state.values with
                  | nil => simpa only [step,work,values,statusInvariant] using valid
                  | cons claim claims =>
                      cases claims with
                      | cons second rest => simpa only [step,work,values,statusInvariant] using valid
                      | nil =>
                          by_cases same : claim.goal=goal <;>
                            simpa only [step,work,values,same,↓reduceIte,statusInvariant] using valid

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver
variable (definition : ValidatedCalculusLanguageDef)

theorem close_not_mem_lemmaTasks (goal : Pattern) (ruleInstance : RuleInstance) (premises : List Pattern)
    (site : Site) (index : Nat) (lemmas : List (Pattern × RawOpenProof)) :
    Task.close goal ruleInstance premises site ∉ lemmaTasks index lemmas := by
  induction lemmas generalizing index with
  | nil => simp [lemmaTasks]
  | cons head tail ih =>
      cases head
      simpa only [lemmaTasks,List.mem_cons,reduceCtorEq,false_or] using ih (index+1)

theorem initial_invariant (goal : Pattern) (source : Mettapedia.Languages.MM0.Translation.CalculusSimulation.LemmaCertificate) :
    Invariant definition
      {checkedPrefix:=seed definition,
       todo:=lemmaTasks 0 source.1++[.visit goal source.2 ⟨("root",0),[]⟩,.finish goal],
       values:=[],saved:=[],occurrences:=[]} := by
  refine ⟨?_,?_,?_⟩
  · intro claim member;cases member
  · intro claim member;cases member
  · intro target ruleInstance premises site member
    rcases List.mem_append.mp member with member | member
    · exact False.elim (close_not_mem_lemmaTasks target ruleInstance premises site 0 source.1 member)
    · simp only [List.mem_cons,reduceCtorEq,List.not_mem_nil,false_or] at member

theorem start_invariant (goal : Pattern) (source : Mettapedia.Languages.MM0.Translation.CalculusSimulation.LemmaCertificate) :
    statusInvariant definition (start definition goal source) := by
  unfold start
  split <;> exact initial_invariant definition goal source

theorem run_invariant (budget : Nat) (status : Status definition)
    (valid : statusInvariant definition status) :
    statusInvariant definition (run definition budget status) := by
  induction budget generalizing status with
  | zero => exact valid
  | succ budget ih => exact ih (step definition status) (step_invariant definition status valid)

theorem reached_invariant (goal : Pattern) (source : Mettapedia.Languages.MM0.Translation.CalculusSimulation.LemmaCertificate) (budget : Nat)
    (state : State definition) (reached : run definition budget (start definition goal source)=.running state) :
    Invariant definition state := by
  have valid := run_invariant definition budget (start definition goal source) (start_invariant definition goal source)
  rw [reached] at valid
  exact valid

theorem reached_saved_goal_scope (goal : Pattern) (source : Mettapedia.Languages.MM0.Translation.CalculusSimulation.LemmaCertificate) (budget : Nat)
    (state : State definition) (reached : run definition budget (start definition goal source)=.running state)
    (query : Nat) (claim : Claim definition state.checkedPrefix) (selected : state.saved[query]?=some claim) :
    argumentValidAt 0 claim.goal=true :=
  (reached_invariant definition goal source budget state reached).saved claim (List.mem_of_getElem? selected)

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.SourceScope

namespace Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise
open Turing Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open ChronologicalDriver ChronologicalTaskEncoding
variable (definition : ValidatedCalculusLanguageDef)

/-- For an actual reached controller state, the original execution earns the
saved goal's scope. This interface requires no enclosing scope assertion. -/
noncomputable def reached_controller_packet_outputs (initialGoal : Pattern)
    (source : Mettapedia.Languages.MM0.Translation.CalculusSimulation.LemmaCertificate) (budget : Nat) (state : State definition)
    (reached : run definition budget (start definition initialGoal source)=.running state)
    (query : Nat) (goal : Pattern) (site : Site) (tail : List Task)
    (claim : Claim definition state.checkedPrefix)
    (work : state.todo=.visit goal (.premise query) site::tail)
    (selected : state.saved[query]?=some claim) (same : claim.goal=goal) :
    TM2OutputsInTime packetMachine (Indexed.argumentWire (stateContextFields definition state))
      (some ((1 : Alphabet)::encodePacket (statePacket (remember definition state site claim tail))))
      (packetClock (stateTaskInput definition state query goal site tail)) := by
  apply controller_state_packet_outputs definition state query goal site tail claim work selected same
  rw [← same]
  exact SourceScope.reached_saved_goal_scope definition initialGoal source budget state reached query claim selected

end Mettapedia.Languages.HOLLight.ChronologicalTaskExecution.Premise

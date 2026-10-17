import Mettapedia.GSLT.LanguageDef.CertificateChronologicalTraversal
import Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission

/-!
# Traversal of original open-proof constructors and children

A finite machine checks the original pair, constructor-tag and child-list
boundaries while retaining every encoded reference and rule-instance payload.
Ordered enter, reference and leave events expose the tree structure to a
separate rule and reference validator. Shape traversal supplies no semantic
rule authority and does not replace the original open-proof checker.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.CertificateProofTraversal
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open CertificateGSLT InferenceChecker
open _root_.Computability Turing StateTransition Polynomial
open ProofSystems Mettapedia.Computability
open Turing.TM2.Stmt CertificateDataTraversal

/-- Each reference event retains the complete original reference field. -/
def referenceWord (index : Nat) : List Alphabet := CertificateDataEncoding.encodeProof (.premise index)

/-- An enter event retains the complete original encoded rule instance. -/
def enterWord (ruleInstance : RuleInstance) : List Alphabet :=
  encodeData (.pair (.atom 1) (CertificateDataEncoding.instanceCodec.put ruleInstance))

/-- Leave is a separate structural event; it is not an authored inference rule. -/
def leaveWord : List Alphabet := encodeData (.atom 2)

mutual
  def proofWords : RawOpenProof → List (List Alphabet)
    | .premise index => [referenceWord index]
    | .node ruleInstance children => enterWord ruleInstance :: childrenWords children ++ [leaveWord]
  def childrenWords : List RawOpenProof → List (List Alphabet)
    | [] => []
    | child :: children => proofWords child ++ childrenWords children
end

def events (proof : RawOpenProof) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (proofWords proof)

def childEvents (children : List RawOpenProof) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (childrenWords children)

def output (proof : RawOpenProof) : List (Option Alphabet) :=
  CertificateArgumentFraming.statusWire (some (events proof))

theorem frame_append (first second : List (List Alphabet)) :
    WordTemplateMachine.Indexed.frame (first ++ second) =
      WordTemplateMachine.Indexed.frame first ++ WordTemplateMachine.Indexed.frame second := by
  simp [WordTemplateMachine.Indexed.frame]

theorem referenceWord_eq (index : Nat) :
    referenceWord index = [4, 3, 2] ++ encodeData (.atom index) := by
  rw [referenceWord, CertificateChronologicalTraversal.premise_wire]
  rfl

theorem enterWord_eq (ruleInstance : RuleInstance) :
    enterWord ruleInstance = [4, 3, 1, 2] ++ encodeWith CertificateDataEncoding.instanceCodec ruleInstance := by
  rw [enterWord, encodeData_pair]
  rfl

theorem leaveWord_eq : leaveWord = [3, 0, 1, 2] := rfl

theorem events_reference (index : Nat) :
    events (.premise index) = (referenceWord index).map some ++ [none] := by
  simp [events, proofWords, WordTemplateMachine.Indexed.frame]

theorem events_node (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    events (.node ruleInstance children) = (enterWord ruleInstance).map some ++
      none :: childEvents children ++ leaveWord.map some ++ [none] := by
  simp only [events, proofWords, WordTemplateMachine.Indexed.frame,
    List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil,
    childEvents, List.append_assoc, List.singleton_append]

theorem childEvents_cons (child : RawOpenProof) (children : List RawOpenProof) :
    childEvents (child :: children) = events child ++ childEvents children := by
  simp only [childEvents, childrenWords, frame_append, events]

theorem referenceWord_decode (index : Nat) :
    decodeWith (Codec.prod Codec.nat Codec.nat) (referenceWord index) = some (0, index) := by
  exact decodeWith_encodeWith (Codec.prod Codec.nat Codec.nat) (0, index)

theorem enterWord_decode (ruleInstance : RuleInstance) :
    decodeWith (Codec.prod Codec.nat CertificateDataEncoding.instanceCodec) (enterWord ruleInstance) =
      some (1, ruleInstance) := by
  exact decodeWith_encodeWith (Codec.prod Codec.nat CertificateDataEncoding.instanceCodec) (1, ruleInstance)

namespace Execution
open CertificateArgumentFraming.Execution

inductive Phase where
  | start | proof | tagAtom | tag | tagEnd | nodePair | fieldStart (node : Bool)
  | field (node : Bool) (phase : CertificateDataTraversal.Phase)
  | clearPost (node : Bool) | restorePrefix (node : Bool) | copyWord (node : Bool)
  | children | childrenEnd | returnProof | checkEnd | restoreVector
  | rejectInput | rejectFrames | rejectPost | rejectPrefix | rejectVector | rejectResult
  deriving DecidableEq, Fintype

local instance : Fintype PrefixField.machine.K := PrefixField.machine.kFin

def parserBody (node : Bool) (phase : CertificateDataTraversal.Phase) : TM2.Stmt Cells Phase State :=
  StackMachineRegisters.withStack id (StackMachineRegisters.withStack id
    (StackMachineRegisters.extend (Phase.field node) (PrefixField.machine.m phase)))

def eventPrefix (node : Bool) : List Alphabet := if node then [4,3,1,2] else [4,3,2]

def pushPrefix (node : Bool) (next : TM2.Stmt Cells Phase State) : TM2.Stmt Cells Phase State :=
  push vectorKey (fun _ => some 4) (push vectorKey (fun _ => some 3)
    (push vectorKey (fun _ => if node then some 1 else some 2)
      (if node then push vectorKey (fun _ => some 2) next else next)))

def machine : FinTM2 where
  K := Key
  k₀ := inputKey
  k₁ := resultKey
  Γ := Cells
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase
  main := .start
  σ := State
  initialState := (none, none)
  m phase := match phase with
    | .start => push framesKey (fun _ => (0 : Alphabet)) (goto fun _ => .proof)
    | .proof => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4) (goto fun _ => .tagAtom) (goto fun _ => .rejectInput))
    | .tagAtom => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 3) (goto fun _ => .tag) (goto fun _ => .rejectInput))
    | .tag => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2) (goto fun _ => .fieldStart false)
          (branch (fun state => state.1 == some 1) (goto fun _ => .tagEnd) (goto fun _ => .rejectInput)))
    | .tagEnd => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2) (goto fun _ => .nodePair) (goto fun _ => .rejectInput))
    | .nodePair => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4) (goto fun _ => .fieldStart true) (goto fun _ => .rejectInput))
    | .fieldStart node => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some (if node then 4 else 3))
          (push inputKey (fun _ => if node then (4 : Alphabet) else (3 : Alphabet))
            (push framesKey (fun _ => (2 : Alphabet)) (goto fun _ => .field node .header)))
          (goto fun _ => .rejectInput))
    | .field node .complete => pop framesKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2) (goto fun _ => .clearPost node)
          (branch (fun state => state.1.isSome)
            (push framesKey (fun state => state.1.getD 2) (parserBody node .complete))
            (goto fun _ => .rejectInput)))
    | .field _ .rejectInput => goto fun _ => .rejectInput
    | .field node phase => parserBody node phase
    | .clearPost node => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .clearPost node)
          (goto fun _ => .restorePrefix node))
    | .restorePrefix node => pop prefixKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push postKey (fun state => state.1.getD 2) (goto fun _ => .restorePrefix node))
          (pushPrefix node (goto fun _ => .copyWord node)))
    | .copyWord node => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push vectorKey (fun state => some (state.1.getD 2)) (goto fun _ => .copyWord node))
          (push vectorKey (fun _ => none) (goto fun _ => if node then .children else .returnProof)))
    | .children => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4)
          (push framesKey (fun _ => (1 : Alphabet)) (goto fun _ => .proof))
          (branch (fun state => state.1 == some 3) (goto fun _ => .childrenEnd) (goto fun _ => .rejectInput)))
    | .childrenEnd => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2)
          (push vectorKey (fun _ => some 3) (push vectorKey (fun _ => some 0)
            (push vectorKey (fun _ => some 1) (push vectorKey (fun _ => some 2)
              (push vectorKey (fun _ => none) (goto fun _ => .returnProof))))))
          (goto fun _ => .rejectInput))
    | .returnProof => pop framesKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 1) (goto fun _ => .children)
          (branch (fun state => state.1 == some 0) (goto fun _ => .checkEnd) (goto fun _ => .rejectInput)))
    | .checkEnd => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isNone) (goto fun _ => .restoreVector) (goto fun _ => .rejectInput))
    | .restoreVector => pop vectorKey (fun state value => (state.1, value))
        (branch (fun state => state.2.isSome)
          (push resultKey (fun state => state.2.getD none) (goto fun _ => .restoreVector))
          (push resultKey (fun _ => some 1) (load (fun _ => (none, none)) halt)))
    | .rejectInput => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectFrames))
    | .rejectFrames => pop framesKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .rejectFrames) (goto fun _ => .rejectPost))
    | .rejectPost => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .rejectPost) (goto fun _ => .rejectPrefix))
    | .rejectPrefix => pop prefixKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .rejectPrefix) (goto fun _ => .rejectVector))
    | .rejectVector => pop vectorKey (fun state value => (state.1, value))
        (branch (fun state => state.2.isSome) (goto fun _ => .rejectVector) (goto fun _ => .rejectResult))
    | .rejectResult => pop resultKey (fun state value => (state.1, value))
        (branch (fun state => state.2.isSome) (goto fun _ => .rejectResult)
          (push resultKey (fun _ => some 0) (load (fun _ => (none, none)) halt)))

def config (phase : Option Phase) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) : machine.Cfg where
  l := phase
  var := state
  stk := (CertificateArgumentFraming.Execution.config 0 none state input frames post memo vector result).stk

local macro "proof_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    inputKey, framesKey, postKey, prefixKey, vectorKey, resultKey, pushPrefix,
    Turing.TM2.step, Turing.TM2.stepAux,
    (show ((1 : Alphabet) == 2) = false from rfl),
    (show ((0 : Alphabet) == 1) = false from rfl),
    (show ((3 : Alphabet) == 4) = false from rfl)] <;>
  (funext key
   cases key with
   | none => simp [Function.update]
   | some key => cases key with
     | none => simp [Function.update]
     | some key => cases key with
       | none => simp [Function.update]
       | some key => cases key <;> simp [Function.update] <;> (first | (intro impossible; cases impossible) | (repeat' split <;> first | rfl | (rename_i impossible; cases impossible))))))

theorem start (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .start) state input frames [] [] vector result) = some (config (some .proof) state input (0 :: frames) [] [] vector result) := by proof_step

theorem proof_pair (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .proof) state (4 :: input) frames [] [] vector result) = some (config (some .tagAtom) (some 4, state.2) input frames [] [] vector result) := by proof_step

theorem tag_atom (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .tagAtom) state (3 :: input) frames [] [] vector result) = some (config (some .tag) (some 3, state.2) input frames [] [] vector result) := by proof_step

theorem tag_reference (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .tag) state (2 :: input) frames [] [] vector result) = some (config (some (.fieldStart false)) (some 2, state.2) input frames [] [] vector result) := by proof_step

theorem tag_node (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .tag) state (1 :: input) frames [] [] vector result) = some (config (some .tagEnd) (some 1, state.2) input frames [] [] vector result) := by proof_step

theorem tag_end (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .tagEnd) state (2 :: input) frames [] [] vector result) = some (config (some .nodePair) (some 2, state.2) input frames [] [] vector result) := by proof_step

theorem node_pair (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .nodePair) state (4 :: input) frames [] [] vector result) = some (config (some (.fieldStart true)) (some 4, state.2) input frames [] [] vector result) := by proof_step

theorem children_cons (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .children) state (4 :: input) frames [] [] vector result) = some (config (some .proof) (some 4, state.2) input (1 :: frames) [] [] vector result) := by proof_step

theorem children_nil (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .children) state (3 :: input) frames [] [] vector result) = some (config (some .childrenEnd) (some 3, state.2) input frames [] [] vector result) := by proof_step

theorem children_end (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .childrenEnd) state (2 :: input) frames [] [] vector result) = some (config (some .returnProof) (some 2, state.2) input frames [] [] (none :: some 2 :: some 1 :: some 0 :: some 3 :: vector) result) := by proof_step

theorem return_child (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .returnProof) state input (1 :: frames) [] [] vector result) = some (config (some .children) (some 1, state.2) input frames [] [] vector result) := by proof_step

theorem return_root (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .returnProof) state input [0] [] [] vector result) = some (config (some .checkEnd) (some 0, state.2) input [] [] [] vector result) := by proof_step

theorem check_end (state : State) (vector result : List (Option Alphabet)) :
    machine.step (config (some .checkEnd) state [] [] [] [] vector result) = some (config (some .restoreVector) (none, state.2) [] [] [] [] vector result) := by proof_step

theorem field_start (node : Bool) (state : State) (input frames : List Alphabet)
    (vector result : List (Option Alphabet)) :
    machine.step (config (some (.fieldStart node)) state
      ((if node then 4 else 3) :: input) frames [] [] vector result) =
      some (config (some (.field node .header)) (some (if node then 4 else 3), state.2)
        ((if node then 4 else 3) :: input) (2 :: frames) [] [] vector result) := by
  cases node <;> proof_step

theorem field_return (node : Bool) (state : State) (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.field node .complete)) state input (2 :: frames) post memo vector result) = some (config (some (.clearPost node)) (some 2, state.2) input frames post memo vector result) := by proof_step

theorem clear_post_cons (node : Bool) (state : State) (head : Alphabet) (input frames tail memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.clearPost node)) state input frames (head :: tail) memo vector result) = some (config (some (.clearPost node)) (some head, state.2) input frames tail memo vector result) := by proof_step

theorem clear_post_nil (node : Bool) (state : State) (input frames memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.clearPost node)) state input frames [] memo vector result) = some (config (some (.restorePrefix node)) (none, state.2) input frames [] memo vector result) := by proof_step

theorem restore_prefix_cons (node : Bool) (state : State) (head : Alphabet) (input frames post tail : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.restorePrefix node)) state input frames post (head :: tail) vector result) = some (config (some (.restorePrefix node)) (some head, state.2) input frames (head :: post) tail vector result) := by proof_step

theorem copy_word_cons (node : Bool) (state : State) (head : Alphabet) (input frames tail : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.copyWord node)) state input frames (head :: tail) [] vector result) = some (config (some (.copyWord node)) (some head, state.2) input frames tail [] (some head :: vector) result) := by proof_step

theorem copy_word_nil (node : Bool) (state : State) (input frames : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.copyWord node)) state input frames [] [] vector result) = some (config (some (if node then .children else .returnProof)) (none, state.2) input frames [] [] (none :: vector) result) := by proof_step

theorem restore_vector_cons (state : State) (head : Option Alphabet) (tail result : List (Option Alphabet)) :
    machine.step (config (some .restoreVector) state [] [] [] [] (head :: tail) result) = some (config (some .restoreVector) (state.1, some head) [] [] [] [] tail (head :: result)) := by proof_step

theorem restore_vector_nil (state : State) (result : List (Option Alphabet)) :
    machine.step (config (some .restoreVector) state [] [] [] [] [] result) = some (config none (none, none) [] [] [] [] [] (some 1 :: result)) := by proof_step

theorem restore_prefix_nil (node : Bool) (state : State)
    (input frames post : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.restorePrefix node)) state input frames post [] vector result) =
      some (config (some (.copyWord node)) (none, state.2) input frames post []
        ((eventPrefix node).reverse.map some ++ vector) result) := by
  cases node <;> simp only [eventPrefix] <;> proof_step

def embed (node : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg) : machine.Cfg :=
  StackMachineRegisters.withStackConfig id result
    (StackMachineRegisters.withStackConfig id vector
      (StackMachineRegisters.config (Phase.field node) extra source))

theorem embed_config (node : Bool) (extra : Option (Option Alphabet))
    (phase : Option CertificateDataTraversal.Phase) (state : Option Alphabet)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    embed node extra vector result (PrefixField.config phase state input frames post memo) =
      config (phase.map (Phase.field node)) (state, extra) input frames post memo vector result := by
  simp only [embed, StackMachineRegisters.withStackConfig, StackMachineRegisters.config,
    PrefixField.config, config, CertificateArgumentFraming.Execution.config, Option.map_id]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

theorem parser_body (node : Bool) (phase : CertificateDataTraversal.Phase)
    (notComplete : phase ≠ .complete) (notReject : phase ≠ .rejectInput) :
    machine.m (.field node phase) = parserBody node phase := by
  cases phase <;> first | rfl | exact (notComplete rfl).elim | exact (notReject rfl).elim

theorem parser_step (node : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (phase : CertificateDataTraversal.Phase) (atPhase : source.l = some phase)
    (notComplete : phase ≠ .complete) (notReject : phase ≠ .rejectInput) :
    machine.step (embed node extra vector result source) =
      (PrefixField.machine.step source).map (embed node extra vector result) := by
  have originalStep : PrefixField.machine.step source =
      some (TM2.stepAux (PrefixField.machine.m phase) source.var source.stk) := by
    cases source with
    | mk label register contents => simp_all [FinTM2.step, TM2.step]
  rw [originalStep]
  have first := StackMachineRegisters.stepAux_extend (Phase.field node) extra
    (PrefixField.machine.m phase) source.var source.stk
  have second := StackMachineRegisters.stepAux_withStack id vector
    (StackMachineRegisters.extend (Phase.field node) (PrefixField.machine.m phase))
    (source.var, extra) source.stk
  have third := StackMachineRegisters.stepAux_withStack id result
    (StackMachineRegisters.withStack id
      (StackMachineRegisters.extend (Phase.field node) (PrefixField.machine.m phase)))
    (source.var, extra) (StackMachineRegisters.withStackContents source.stk vector)
  simp only [FinTM2.step, embed, StackMachineRegisters.withStackConfig,
    StackMachineRegisters.config, atPhase, Option.map_some, id_eq, Turing.TM2.step]
  rw [parser_body node phase notComplete notReject]
  change some (Turing.TM2.stepAux (parserBody node phase) (source.var, extra)
    (StackMachineRegisters.withStackContents (StackMachineRegisters.withStackContents source.stk vector) result)) = _
  rw [parserBody, third]
  rw [second, first]
  simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.config, Option.map_id]

theorem field_complete_first (node : Bool) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.field node .complete)) state input (0 :: frames) post memo vector result) =
      some (config (some (.field node .header)) (some 0, state.2) input (1 :: frames) post memo vector result) := by
  simp [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    inputKey, framesKey, postKey, prefixKey, vectorKey, resultKey, parserBody,
    StackMachineRegisters.withStack, StackMachineRegisters.extend,
    PrefixField.machine_complete, CertificateDataTraversal.machine,
    Turing.TM2.step, Turing.TM2.stepAux,
    (show ((0 : Alphabet) == 2) = false from rfl)]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | none => simp [Function.update]
    | some key => cases key with
      | none => simp [Function.update]
      | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible)

theorem field_complete_second (node : Bool) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.field node .complete)) state input (1 :: frames) post memo vector result) =
      some (config (some (.field node .complete)) (some 1, state.2) input frames (4 :: post) memo vector result) := by
  simp [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    inputKey, framesKey, postKey, prefixKey, vectorKey, resultKey, parserBody,
    StackMachineRegisters.withStack, StackMachineRegisters.extend,
    PrefixField.machine_complete, CertificateDataTraversal.machine,
    Turing.TM2.step, Turing.TM2.stepAux,
    (show ((1 : Alphabet) == 2) = false from rfl),
    (show ((1 : Alphabet) == 0) = false from rfl)]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | none => simp [Function.update]
    | some key => cases key with
      | none => simp [Function.update]
      | some key => cases key <;> simp [Function.update] <;>
        first | (intro impossible; cases impossible) |
          (repeat' split <;> first | rfl | (rename_i impossible; cases impossible))

theorem parser_complete (node : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (state : Option Alphabet)
    (input frames post memo : List Alphabet) (head : Alphabet)
    (allowed : head = 0 ∨ head = 1) :
    machine.step (embed node extra vector result
      (PrefixField.config (some .complete) state input (head :: frames) post memo)) =
      (PrefixField.machine.step (PrefixField.config (some .complete) state input
        (head :: frames) post memo)).map (embed node extra vector result) := by
  rcases allowed with rfl | rfl
  · rw [PrefixField.complete_first, Option.map_some, embed_config, embed_config]
    simp only [Option.map_some]
    exact field_complete_first node (state, extra) input frames post memo vector result
  · rw [PrefixField.complete_second, Option.map_some, embed_config, embed_config]
    simp only [Option.map_some]
    exact field_complete_second node (state, extra) input frames post memo vector result

theorem parser_scanning (node : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (allowed : PrefixField.scanning source) :
    machine.step (embed node extra vector result source) =
      (PrefixField.machine.step source).map (embed node extra vector result) := by
  rcases allowed with atHeader | atNumber | ⟨atComplete, frames⟩
  · exact parser_step node extra vector result source .header atHeader (by decide) (by decide)
  · exact parser_step node extra vector result source .number atNumber (by decide) (by decide)
  · cases frameEq : source.stk (some CertificateDataTraversal.Stack.frames) with
    | nil => simp [frameEq] at frames
    | cons head tail =>
      have headValues : (show Alphabet from head) = (0 : Alphabet) ∨ (show Alphabet from head) = (1 : Alphabet) := by simpa [frameEq] using frames
      have mapped := parser_complete node extra vector result source.var
        (source.stk (some .input)) tail (source.stk (some .output)) (source.stk none) head headValues
      rw [← atComplete, ← frameEq, ← PrefixField.config_eta] at mapped
      exact mapped

noncomputable def fieldWalk (node : Bool) (extra : Option (Option Alphabet))
    (value : Data) (input frames : List Alphabet) (vector result : List (Option Alphabet))
    (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some (.field node .header)) (state, extra) (writeData value input)
        (2 :: frames) [] [] vector result)
      (some (config (some (.field node .complete)) (finalState value, extra) input (2 :: frames)
        (postorderWire value).reverse (encodeData value).reverse vector result)) (scanCost value) := by
  have walked := PrefixField.walkInto machine.step (embed node extra vector result)
    (parser_scanning node extra vector result) value input (2 :: frames) [] [] state
  simpa only [embed_config, Option.map_some, List.append_nil] using walked

noncomputable def clearPostRun (node : Bool) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.clearPost node)) state input frames post memo vector result)
      (some (config (some (.restorePrefix node)) (none, state.2) input frames [] memo vector result))
      (post.length + 1) := by
  induction post generalizing state with
  | nil => exact StackMachineComposition.oneStep (clear_post_nil node state input frames memo vector result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (clear_post_cons node state head input frames tail memo vector result)
    have rest := ih (some head, state.2)
    simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def restorePrefixRun (node : Bool) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.restorePrefix node)) state input frames post memo vector result)
      (some (config (some (.copyWord node)) (none, state.2) input frames (memo.reverse ++ post) []
        ((eventPrefix node).reverse.map some ++ vector) result)) (memo.length + 1) := by
  induction memo generalizing state post with
  | nil => simpa using StackMachineComposition.oneStep (restore_prefix_nil node state input frames post vector result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (restore_prefix_cons node state head input frames post tail vector result)
    have rest := ih (some head, state.2) (head :: post)
    simpa [List.reverse_cons, List.append_assoc] using
      EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def copyWordRun (node : Bool) (state : State)
    (input frames post : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.copyWord node)) state input frames post [] vector result)
      (some (config (some (if node then .children else .returnProof)) (none, state.2) input frames [] []
        (none :: post.reverse.map some ++ vector) result)) (post.length + 1) := by
  induction post generalizing state vector with
  | nil => simpa using StackMachineComposition.oneStep (copy_word_nil node state input frames vector result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (copy_word_cons node state head input frames tail vector result)
    have rest := ih (some head, state.2) (some head :: vector)
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def restoreVectorRun (state : State) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some .restoreVector) state [] [] [] [] vector result)
      (some (config none (none, none) [] [] [] [] [] (some 1 :: vector.reverse ++ result)))
      (vector.length + 1) := by
  induction vector generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (restore_vector_nil state result)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (restore_vector_cons state head tail result)
    have rest := ih (state.1, some head) (head :: result)
    simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

def payloadCost (value : Data) : Nat := scanCost value + 3 * dataWeight value + 4

noncomputable def fieldRun (node : Bool) (extra : Option (Option Alphabet))
    (value : Data) (input frames : List Alphabet) (vector result : List (Option Alphabet))
    (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some (.field node .header)) (state, extra) (writeData value input) (2 :: frames) [] [] vector result)
      (some (config (some (if node then .children else .returnProof)) (none, extra) input frames [] []
        (((eventPrefix node ++ encodeData value).map some ++ [none]).reverse ++ vector) result))
      (payloadCost value) := by
  have walked := fieldWalk node extra value input frames vector result state
  have returned := StackMachineComposition.oneStep (field_return node (finalState value, extra)
    input frames (postorderWire value).reverse (encodeData value).reverse vector result)
  have cleared := clearPostRun node (some 2, extra) input frames
    (postorderWire value).reverse (encodeData value).reverse vector result
  have restored := restorePrefixRun node (none, extra) input frames [] (encodeData value).reverse vector result
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have copied := copyWordRun node (none, extra) input frames (encodeData value)
    ((eventPrefix node).reverse.map some ++ vector) result
  have a := EvalsToInTime.trans _ (scanCost value) 1 _ _ _ walked returned
  have b := EvalsToInTime.trans _ (1 + scanCost value)
    ((postorderWire value).reverse.length + 1) _ _ _ a cleared
  have c := EvalsToInTime.trans _ ((postorderWire value).reverse.length + 1 + (1 + scanCost value))
    ((encodeData value).length + 1) _ _ _ b restored
  have d := EvalsToInTime.trans _ ((encodeData value).length + 1 +
    ((postorderWire value).reverse.length + 1 + (1 + scanCost value)))
    ((encodeData value).length + 1) _ _ _ c copied
  convert d using 1
  · simp [List.reverse_append, List.map_append, List.append_assoc, List.map_reverse]
  · simp only [payloadCost, List.length_reverse, postorderWire_length,
      encodeData, writeData_length, List.length_nil, Nat.add_zero]
    omega

def proofState : RawOpenProof → Option Alphabet
  | .premise _ => none
  | .node _ _ => some 2

mutual
  def proofCost : RawOpenProof → Nat
    | .premise index => 4 + payloadCost (.atom index)
    | .node ruleInstance children => 6 + payloadCost (CertificateDataEncoding.instanceCodec.put ruleInstance) +
        childrenCost children
  def childrenCost : List RawOpenProof → Nat
    | [] => 2
    | child :: children => 2 + proofCost child + childrenCost children
end

theorem premise_input (index : Nat) (input : List Alphabet) :
    writeData (CertificateDataEncoding.putProof (.premise index)) input =
      4 :: 3 :: 2 :: writeData (.atom index) input := rfl

theorem node_input (ruleInstance : RuleInstance) (children : List RawOpenProof) (input : List Alphabet) :
    writeData (CertificateDataEncoding.putProof (.node ruleInstance children)) input =
      4 :: 3 :: 1 :: 2 :: 4 ::
        writeData (CertificateDataEncoding.instanceCodec.put ruleInstance)
          (writeData (CertificateDataEncoding.putProofs children) input) := rfl

theorem field_start_reference (state : State) (index : Nat) (input frames : List Alphabet)
    (vector result : List (Option Alphabet)) :
    machine.step (config (some (.fieldStart false)) state
      (writeData (.atom index) input) frames [] [] vector result) =
      some (config (some (.field false .header)) (some 3, state.2)
        (writeData (.atom index) input) (2 :: frames) [] [] vector result) :=
  field_start false state (natural index ++ input) frames vector result

theorem field_start_instance (state : State) (ruleInstance : RuleInstance) (input frames : List Alphabet)
    (vector result : List (Option Alphabet)) :
    machine.step (config (some (.fieldStart true)) state
      (writeData (CertificateDataEncoding.instanceCodec.put ruleInstance) input) frames [] [] vector result) =
      some (config (some (.field true .header)) (some 4, state.2)
        (writeData (CertificateDataEncoding.instanceCodec.put ruleInstance) input) (2 :: frames) [] [] vector result) := by
  exact field_start true state
    (writeData (Codec.string.put ruleInstance.ruleId.value)
      (writeData ((Codec.list CertificateDataEncoding.patternCodec).put ruleInstance.arguments) input))
    frames vector result

mutual
  /-- The complete source tree is visited using only its original byte fields.
  Caller continuations, input suffix and existing output are retained. -/
  noncomputable def proofRun (proof : RawOpenProof) (input frames : List Alphabet)
      (vector result : List (Option Alphabet)) (state : State) :
      EvalsToInTime machine.step
        (config (some .proof) state (writeData (CertificateDataEncoding.putProof proof) input)
          frames [] [] vector result)
        (some (config (some .returnProof) (proofState proof, state.2) input frames [] []
          ((events proof).reverse ++ vector) result)) (proofCost proof) := by
    cases proof with
    | premise index =>
      rw [premise_input]
      have a := StackMachineComposition.oneStep (proof_pair state
        (3 :: 2 :: writeData (.atom index) input) frames vector result)
      have b := StackMachineComposition.oneStep (tag_atom (some 4, state.2)
        (2 :: writeData (.atom index) input) frames vector result)
      have c := StackMachineComposition.oneStep (tag_reference (some 3, state.2)
        (writeData (.atom index) input) frames vector result)
      have d := StackMachineComposition.oneStep (field_start_reference (some 2, state.2) index
        input frames vector result)
      have e := fieldRun false state.2 (.atom index) input frames vector result (some 3)
      have ab := EvalsToInTime.trans _ 1 1 _ _ _ a b
      have abc := EvalsToInTime.trans _ 2 1 _ _ _ ab c
      have abcd := EvalsToInTime.trans _ 3 1 _ _ _ abc d
      have joined := EvalsToInTime.trans _ 4 (payloadCost (.atom index)) _ _ _ abcd e
      convert joined using 1
      · simp only [proofState, events_reference, referenceWord_eq, eventPrefix,
          Bool.false_eq_true, ↓reduceIte]
      · simp only [proofCost]; omega
    | node ruleInstance children =>
      rw [node_input]
      let remaining := writeData (CertificateDataEncoding.instanceCodec.put ruleInstance)
        (writeData (CertificateDataEncoding.putProofs children) input)
      have a := StackMachineComposition.oneStep (proof_pair state (3 :: 1 :: 2 :: 4 :: remaining) frames vector result)
      have b := StackMachineComposition.oneStep (tag_atom (some 4, state.2) (1 :: 2 :: 4 :: remaining) frames vector result)
      have c := StackMachineComposition.oneStep (tag_node (some 3, state.2) (2 :: 4 :: remaining) frames vector result)
      have d := StackMachineComposition.oneStep (tag_end (some 1, state.2) (4 :: remaining) frames vector result)
      have e := StackMachineComposition.oneStep (node_pair (some 2, state.2) remaining frames vector result)
      have f := StackMachineComposition.oneStep (field_start_instance (some 4, state.2) ruleInstance
        (writeData (CertificateDataEncoding.putProofs children) input) frames vector result)
      have g := fieldRun true state.2 (CertificateDataEncoding.instanceCodec.put ruleInstance)
        (writeData (CertificateDataEncoding.putProofs children) input) frames vector result (some 4)
      have h := childrenRun children input frames
        (((eventPrefix true ++ encodeData (CertificateDataEncoding.instanceCodec.put ruleInstance)).map some ++ [none]).reverse ++ vector)
        result (none, state.2)
      have ab := EvalsToInTime.trans _ 1 1 _ _ _ a b
      have abc := EvalsToInTime.trans _ 2 1 _ _ _ ab c
      have abcd := EvalsToInTime.trans _ 3 1 _ _ _ abc d
      have abcde := EvalsToInTime.trans _ 4 1 _ _ _ abcd e
      have abcdef := EvalsToInTime.trans _ 5 1 _ _ _ abcde f
      have first := EvalsToInTime.trans _ 6 (payloadCost (CertificateDataEncoding.instanceCodec.put ruleInstance)) _ _ _ abcdef g
      have joined := EvalsToInTime.trans _
        (payloadCost (CertificateDataEncoding.instanceCodec.put ruleInstance) + 6) (childrenCost children)
        _ _ _ first h
      convert joined using 1
      · simp [proofState, events_node, enterWord_eq, encodeWith, eventPrefix,
          List.reverse_append, List.append_assoc]
      · simp only [proofCost]; omega
  termination_by sizeOf proof

  /-- Each child occurrence is visited in authored order, then an explicit leave
  event closes the node. Repeated physical children remain repeated events. -/
  noncomputable def childrenRun (children : List RawOpenProof) (input frames : List Alphabet)
      (vector result : List (Option Alphabet)) (state : State) :
      EvalsToInTime machine.step
        (config (some .children) state (writeData (CertificateDataEncoding.putProofs children) input)
          frames [] [] vector result)
        (some (config (some .returnProof) (some 2, state.2) input frames [] []
          ((childEvents children ++ leaveWord.map some ++ [none]).reverse ++ vector) result))
        (childrenCost children) := by
    cases children with
    | nil =>
      have first := StackMachineComposition.oneStep (children_nil state (2 :: input) frames vector result)
      have last := StackMachineComposition.oneStep (children_end (some 3, state.2) input frames vector result)
      simpa only [CertificateDataEncoding.putProofs, writeData, natural, Nat.digits_zero,
        List.map_nil, List.nil_append, List.cons_append, List.reverse_append, childEvents, childrenWords, WordTemplateMachine.Indexed.frame,
        List.flatMap_nil, leaveWord_eq, List.reverse_cons, List.reverse_nil,
        List.append_nil, List.map_cons, List.append_assoc, List.nil_append, List.singleton_append,
        childrenCost] using EvalsToInTime.trans _ 1 1 _ _ _ first last
    | cons child children =>
      have first := StackMachineComposition.oneStep (children_cons state
        (writeData (CertificateDataEncoding.putProof child)
          (writeData (CertificateDataEncoding.putProofs children) input)) frames vector result)
      have walked := proofRun child (writeData (CertificateDataEncoding.putProofs children) input)
        (1 :: frames) vector result (some 4, state.2)
      have returned := StackMachineComposition.oneStep (return_child (proofState child, state.2)
        (writeData (CertificateDataEncoding.putProofs children) input) frames
        ((events child).reverse ++ vector) result)
      have tail := childrenRun children input frames ((events child).reverse ++ vector) result (some 1, state.2)
      have a := EvalsToInTime.trans _ 1 (proofCost child) _ _ _ first walked
      have b := EvalsToInTime.trans _ (proofCost child + 1) 1 _ _ _ a returned
      have c := EvalsToInTime.trans _ (1 + (proofCost child + 1)) (childrenCost children) _ _ _ b tail
      convert c using 1
      · rfl
      · simp [childEvents_cons, List.reverse_append, List.append_assoc]
      · simp only [childrenCost]; omega
  termination_by sizeOf children
end

mutual
  theorem proofCost_le (proof : RawOpenProof) :
      proofCost proof ≤ 8 * dataWeight (CertificateDataEncoding.putProof proof) := by
    cases proof with
    | premise index =>
      have scanned := scanCost_le (.atom index)
      simp only [proofCost, payloadCost, CertificateDataEncoding.putProof, dataWeight] at *
      have nilDigits : (Nat.digits 2 0).length = 0 := rfl
      rw [nilDigits]
      omega
    | node ruleInstance children =>
      have scanned := scanCost_le (CertificateDataEncoding.instanceCodec.put ruleInstance)
      have childBound := childrenCost_le children
      simp only [proofCost, payloadCost, CertificateDataEncoding.putProof, dataWeight] at *
      have oneDigit : (Nat.digits 2 1).length = 1 := rfl
      rw [oneDigit]
      omega
  termination_by sizeOf proof
  theorem childrenCost_le (children : List RawOpenProof) :
      childrenCost children ≤ 8 * dataWeight (CertificateDataEncoding.putProofs children) := by
    cases children with
    | nil => simp only [childrenCost, CertificateDataEncoding.putProofs, dataWeight]; decide
    | cons child children =>
      have head := proofCost_le child
      have tail := childrenCost_le children
      simp only [childrenCost, CertificateDataEncoding.putProofs, dataWeight]
      omega
  termination_by sizeOf children
end

mutual
  theorem events_length_le (proof : RawOpenProof) :
      (events proof).length ≤ 2 * dataWeight (CertificateDataEncoding.putProof proof) := by
    cases proof with
    | premise index =>
      rw [events_reference, referenceWord_eq]
      simp only [List.length_append, List.length_map, encodeData, writeData_length,
        List.length_nil, Nat.add_zero, List.length_cons, CertificateDataEncoding.putProof, dataWeight]
      have nilDigits : (Nat.digits 2 0).length = 0 := rfl
      rw [nilDigits]
      omega
    | node ruleInstance children =>
      have childrenBound := childEvents_length_le children
      rw [events_node, enterWord_eq, leaveWord_eq]
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
        encodeWith, encodeData, writeData_length, CertificateDataEncoding.putProof, dataWeight]
      have oneDigit : (Nat.digits 2 1).length = 1 := rfl
      rw [oneDigit]
      omega
  termination_by sizeOf proof
  theorem childEvents_length_le (children : List RawOpenProof) :
      (childEvents children).length ≤ 2 * dataWeight (CertificateDataEncoding.putProofs children) := by
    cases children with
    | nil => simp only [childEvents, childrenWords, WordTemplateMachine.Indexed.frame,
        List.flatMap_nil, List.length_nil, CertificateDataEncoding.putProofs, dataWeight]; omega
    | cons child children =>
      have head := events_length_le child
      have tail := childEvents_length_le children
      rw [childEvents_cons, List.length_append]
      simp only [CertificateDataEncoding.putProofs, dataWeight]
      omega
  termination_by sizeOf children
end

theorem init_eq (input : List Alphabet) : initList machine input =
    config (some .start) (none, none) input [] [] [] [] [] := by
  simp only [initList, machine, config, CertificateArgumentFraming.Execution.config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

theorem halt_eq (result : List (Option Alphabet)) : haltList machine result =
    config none (none, none) [] [] [] [] [] result := by
  simp only [haltList, machine, config, CertificateArgumentFraming.Execution.config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

/-- The six cleanup labels reuse the existing framing cleanup subroutine.
Other framing labels are excluded by the invariant below. -/
def rejectPhase : CertificateArgumentFraming.Execution.Phase 0 → Phase
  | .rejectInput => .rejectInput
  | .rejectFrames => .rejectFrames
  | .rejectPost => .rejectPost
  | .rejectPrefix => .rejectPrefix
  | .rejectVector => .rejectVector
  | .rejectResult => .rejectResult
  | _ => .rejectInput

def rejectEmbed (source : (CertificateArgumentFraming.Execution.machine 0).Cfg) : machine.Cfg where
  l := source.l.map rejectPhase
  var := source.var
  stk := source.stk

def rejecting (source : (CertificateArgumentFraming.Execution.machine 0).Cfg) : Prop :=
  match source.l with
  | none => True
  | some .rejectInput | some .rejectFrames | some .rejectPost
  | some .rejectPrefix | some .rejectVector | some .rejectResult => True
  | _ => False

theorem rejecting_preserved (before after : (CertificateArgumentFraming.Execution.machine 0).Cfg)
    (valid : rejecting before)
    (computed : (CertificateArgumentFraming.Execution.machine 0).step before = some after) :
    rejecting after := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some phase =>
      cases phase <;> simp only [rejecting] at valid <;> try contradiction
      all_goals
        simp only [FinTM2.step, CertificateArgumentFraming.Execution.machine, TM2.step,
          TM2.stepAux, Bool.cond_eq_ite] at computed
        split at computed <;> cases computed <;> trivial

theorem reject_step (source : (CertificateArgumentFraming.Execution.machine 0).Cfg)
    (valid : rejecting source) : machine.step (rejectEmbed source) =
      ((CertificateArgumentFraming.Execution.machine 0).step source).map rejectEmbed := by
  cases source with
  | mk label state contents =>
    cases label with
    | none => rfl
    | some phase =>
      cases phase <;> simp only [rejecting] at valid <;> try contradiction
      all_goals
        simp only [FinTM2.step, machine, CertificateArgumentFraming.Execution.machine,
          TM2.step, TM2.stepAux, rejectEmbed, rejectPhase, Option.map_some, Bool.cond_eq_ite]
        split <;> rfl

/-- Refusal drains every input and scratch stack and resets the finite register.
Its transition bound is inherited from the original cleanup implementation. -/
noncomputable def rejectRun (state : State) (input frames post memo : List Alphabet)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step (config (some .rejectInput) state input frames post memo vector result)
      (some (config none (none, none) [] [] [] [] [] [some 0]))
      (input.length + frames.length + post.length + memo.length + vector.length + result.length + 6) := by
  have original := CertificateArgumentFraming.Execution.rejectInputRun 0 state input frames post memo vector result
  have lifted := StackMachineRegisters.evalsInto
    (CertificateArgumentFraming.Execution.machine 0).step machine.step rejectEmbed rejecting
    rejecting_preserved reject_step (by trivial) original
  simpa only [rejectEmbed, CertificateArgumentFraming.Execution.config, config,
    Option.map_some, Option.map_none, rejectPhase] using lifted

theorem proof_missing (state : State) (frames : List Alphabet)
    (vector result : List (Option Alphabet)) :
    machine.step (config (some .proof) state [] frames [] [] vector result) =
      some (config (some .rejectInput) (none, state.2) [] frames [] [] vector result) := by proof_step

theorem proof_bad_header (state : State) (head : Alphabet) (tail frames : List Alphabet)
    (vector result : List (Option Alphabet)) (invalid : head ≠ 4) :
    machine.step (config (some .proof) state (head :: tail) frames [] [] vector result) =
      some (config (some .rejectInput) (some head, state.2) tail frames [] [] vector result) := by
  have failed : (some head == some (4 : Alphabet)) = false := by simp [invalid]
  simp only [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    TM2.step, TM2.stepAux, inputKey, List.head?_cons, List.tail_cons, failed, Bool.cond_false]
  congr 2
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> simp [Function.update] <;> intro impossible <;> cases impossible

theorem tag_bad (state : State) (head : Alphabet) (tail frames : List Alphabet)
    (vector result : List (Option Alphabet)) (notReference : head ≠ 2) (notNode : head ≠ 1) :
    machine.step (config (some .tag) state (head :: tail) frames [] [] vector result) =
      some (config (some .rejectInput) (some head, state.2) tail frames [] [] vector result) := by
  have failedReference : (some head == some (2 : Alphabet)) = false := by simp [notReference]
  have failedNode : (some head == some (1 : Alphabet)) = false := by simp [notNode]
  simp only [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    TM2.step, TM2.stepAux, inputKey, List.head?_cons, List.tail_cons,
    failedReference, failedNode, Bool.cond_false]
  congr 2
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> simp [Function.update] <;> intro impossible <;> cases impossible

theorem check_trailing (state : State) (head : Alphabet) (tail : List Alphabet)
    (vector result : List (Option Alphabet)) :
    machine.step (config (some .checkEnd) state (head :: tail) [] [] [] vector result) =
      some (config (some .rejectInput) (some head, state.2) tail [] [] [] vector result) := by proof_step

noncomputable def emptyOutputs : TM2OutputsInTime machine [] (some [some 0]) 9 := by
  have first := StackMachineComposition.oneStep (start (none, none) [] [] [] [])
  have second := StackMachineComposition.oneStep (proof_missing (none, none) [0] [] [])
  have cleanup := rejectRun (none, none) [] [0] [] [] [] []
  have joined := EvalsToInTime.trans _ 1 1 _ _ _ first second
  have finished := EvalsToInTime.trans _ 2 7 _ _ _ joined cleanup
  change EvalsToInTime _ (initList machine []) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  exact finished

noncomputable def badHeaderOutputs (head : Alphabet) (tail : List Alphabet) (invalid : head ≠ 4) :
    TM2OutputsInTime machine (head :: tail) (some [some 0]) (tail.length + 9) := by
  have first := StackMachineComposition.oneStep (start (none, none) (head :: tail) [] [] [])
  have second := StackMachineComposition.oneStep (proof_bad_header (none, none) head tail [0] [] [] invalid)
  have cleanup := rejectRun (some head, none) tail [0] [] [] [] []
  have joined := EvalsToInTime.trans _ 1 1 _ _ _ first second
  have finished := EvalsToInTime.trans _ 2 (tail.length + 7) _ _ _ joined cleanup
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  convert finished using 1

noncomputable def badTagOutputs (head : Alphabet) (tail : List Alphabet)
    (notReference : head ≠ 2) (notNode : head ≠ 1) :
    TM2OutputsInTime machine ([4,3,head] ++ tail) (some [some 0]) (tail.length + 11) := by
  have first := StackMachineComposition.oneStep (start (none, none) ([4,3,head] ++ tail) [] [] [])
  have second := StackMachineComposition.oneStep (proof_pair (none, none) ([3,head] ++ tail) [0] [] [])
  have third := StackMachineComposition.oneStep (tag_atom (some 4, none) (head :: tail) [0] [] [])
  have fourth := StackMachineComposition.oneStep (tag_bad (some 3, none) head tail [0] [] [] notReference notNode)
  have cleanup := rejectRun (some head, none) tail [0] [] [] [] []
  have joined := EvalsToInTime.trans _ 1 1 _ _ _ first second
  have joined := EvalsToInTime.trans _ 2 1 _ _ _ joined third
  have joined := EvalsToInTime.trans _ 3 1 _ _ _ joined fourth
  have finished := EvalsToInTime.trans _ 4 (tail.length + 7) _ _ _ joined cleanup
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  convert finished using 1

def executionCost (proof : RawOpenProof) : Nat := proofCost proof + (events proof).length + 4

/-- The original proof tree runs through the actual finite-control visitor.
No rule lookup, semantic premise discharge or reference permission is inferred
from this syntactic traversal. -/
noncomputable def outputs (proof : RawOpenProof) :
    TM2OutputsInTime machine (CertificateDataEncoding.encodeProof proof) (some (output proof))
      (executionCost proof) := by
  have begin := StackMachineComposition.oneStep (start (none, none)
    (CertificateDataEncoding.encodeProof proof) [] [] [])
  have walked := proofRun proof [] [0] [] [] (none, none)
  have returned := StackMachineComposition.oneStep (return_root (proofState proof, none) []
    ((events proof).reverse ++ []) [])
  have checked := StackMachineComposition.oneStep (check_end (some 0, none) ((events proof).reverse ++ []) [])
  have restored := restoreVectorRun (none, none) ((events proof).reverse ++ []) []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at walked returned checked restored
  have first := EvalsToInTime.trans _ 1 (proofCost proof) _ _ _ begin walked
  have second := EvalsToInTime.trans _ (proofCost proof + 1) 1 _ _ _ first returned
  have third := EvalsToInTime.trans _ (1 + (proofCost proof + 1)) 1 _ _ _ second checked
  have joined := EvalsToInTime.trans _ (1 + (1 + (proofCost proof + 1))) ((events proof).length + 1)
    _ _ _ third restored
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  convert joined using 1
  · rfl
  · simp only [executionCost]; omega

/-- A complete original proof followed by any extra symbol is refused.
The already produced events are drained along with the remaining input. -/
noncomputable def trailingOutputs (proof : RawOpenProof) (head : Alphabet) (tail : List Alphabet) :
    TM2OutputsInTime machine (CertificateDataEncoding.encodeProof proof ++ head :: tail)
      (some [some 0]) (proofCost proof + (events proof).length + tail.length + 9) := by
  have begin := StackMachineComposition.oneStep (start (none, none)
    (CertificateDataEncoding.encodeProof proof ++ head :: tail) [] [] [])
  have walked := proofRun proof (head :: tail) [0] [] [] (none, none)
  rw [writeData_append] at walked
  have returned := StackMachineComposition.oneStep (return_root (proofState proof, none) (head :: tail)
    ((events proof).reverse ++ []) [])
  have checked := StackMachineComposition.oneStep (check_trailing (some 0, none) head tail
    ((events proof).reverse ++ []) [])
  have cleanup := rejectRun (some head, none) tail [] [] [] ((events proof).reverse ++ []) []
  simp only [List.append_nil, List.length_reverse, List.length_nil, Nat.add_zero] at walked returned checked cleanup
  have first := EvalsToInTime.trans _ 1 (proofCost proof) _ _ _ begin walked
  have second := EvalsToInTime.trans _ (proofCost proof + 1) 1 _ _ _ first returned
  have third := EvalsToInTime.trans _ (1 + (proofCost proof + 1)) 1 _ _ _ second checked
  have finished := EvalsToInTime.trans _ (1 + (1 + (proofCost proof + 1)))
    (tail.length + (events proof).length + 6) _ _ _ third cleanup
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  convert finished using 1
  omega

theorem executionCost_le (proof : RawOpenProof) :
    executionCost proof ≤ 10 * (CertificateDataEncoding.encodeProof proof).length + 4 := by
  have structural := proofCost_le proof
  have eventsBound := events_length_le proof
  simp only [executionCost, CertificateDataEncoding.encodeProof, encodeWith, encodeData,
    writeData_length, List.length_nil, Nat.add_zero, CertificateDataEncoding.proofCodec]
  omega

noncomputable def realization : TM2ComputableInPolyTime CertificateDataEncoding.encodeProof
    output (fun proof : RawOpenProof => proof) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 10 * X + C 4
  outputsFun proof := by
    change TM2OutputsInTime machine ((CertificateDataEncoding.encodeProof proof).map id)
      (some ((output proof).map id)) _
    simp only [List.map_id_fun, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    apply BinaryReferenceMachine.within (outputs proof)
    exact executionCost_le proof

end Execution

namespace Admission

variable (definition : CalculusLanguageDef)

/-- Extract the already executed admission tag, retaining no unneeded
working output. The enclosing field caller owns the original event bytes. -/
def project {definition : CalculusLanguageDef} : ((Alphabet ⊕ Bool) ⊕ Option (Fin definition.rules.length)) → List (Option Bool)
  | .inl (.inr result) => [some result]
  | _ => []

local instance : Fintype ((CertificateRuleAdmission.ScopedApplication.machine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.machine definition).k₁) := by
  change Fintype ((Alphabet ⊕ Bool) ⊕ Option (Fin definition.rules.length)); infer_instance
local instance : Inhabited ((CertificateRuleAdmission.ScopedApplication.machine definition).Γ
    (CertificateRuleAdmission.ScopedApplication.machine definition).k₁) := by
  change Inhabited ((Alphabet ⊕ Bool) ⊕ Option (Fin definition.rules.length)); infer_instance
local instance : Fintype ((WordHomomorphismMachine.machine (project (definition := definition))).Γ
    (WordHomomorphismMachine.machine (project (definition := definition))).k₁) := by
  change Fintype (Option Bool); infer_instance

def applicationMachine : FinTM2 :=
  StackMachineComposition.machine (CertificateRuleAdmission.ScopedApplication.machine definition)
    (WordHomomorphismMachine.machine (project (definition := definition))) (Equiv.refl _)

attribute [local implicit_reducible] applicationMachine

theorem project_output (ruleInstance : RuleInstance) :
    (CertificateRuleAdmission.ScopedApplication.output definition ruleInstance).flatMap
      (project (definition := definition)) =
      [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)] := by
  simp only [CertificateRuleAdmission.ScopedApplication.output, List.flatMap_cons,
    project, List.nil_append, List.singleton_append, List.flatMap_map]
  have erased : ∀ symbols : List Alphabet,
      symbols.flatMap (fun _ => ([] : List (Option Bool))) = [] := by
    intro symbols
    induction symbols with
    | nil => rfl
    | cons _ _ ih => simp only [List.flatMap_cons, ih, List.nil_append]
  rw [erased]

noncomputable def applicationOutputs (ruleInstance : RuleInstance) :
    TM2OutputsInTime (applicationMachine definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
      (some [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)])
      (20300 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2) := by
  have projected := WordHomomorphismMachine.outputs (project (definition := definition))
    (CertificateRuleAdmission.ScopedApplication.output definition ruleInstance)
  rw [project_output] at projected
  have joined := StackMachineComposition.outputs
    (CertificateRuleAdmission.ScopedApplication.machine definition)
    (WordHomomorphismMachine.machine (project (definition := definition))) (Equiv.refl _)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)
    (CertificateRuleAdmission.ScopedApplication.output definition ruleInstance)
    [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)]
    (20200 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2)
    (2 * (CertificateRuleAdmission.ScopedApplication.output definition ruleInstance).length + 4)
    (CertificateRuleAdmission.ScopedApplication.outputs definition ruleInstance) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine (project (definition := definition)))
        ((CertificateRuleAdmission.ScopedApplication.output definition ruleInstance).map id) _ _
      simpa only [List.map_id_fun, id_eq, List.length_cons, List.length_nil, Nat.add_zero] using projected)
  apply WordEqualityMachine.within joined
  simp only [CertificateRuleAdmission.ScopedApplication.output, List.length_cons,
    List.length_map] at *
  nlinarith

namespace Event

abbrev Program := applicationMachine definition
local instance : Fintype (Program definition).K := (Program definition).kFin
local instance : Fintype (Program definition).Λ := (Program definition).ΛFin
local instance : Fintype (Program definition).σ := (Program definition).σFin
abbrev State := (Program definition).σ × (Option Alphabet × Bool)

inductive Phase (Label : Type) where
  | start | pairAtom | pairTag | nodeEnd | run (label : Label) | done
  | drain | finish
  deriving DecidableEq, Fintype

/-- Only existing event prefixes select a branch. Enter executes the original
instance admission; reference and leave retain structural meaning only. -/
def statement (phase : Phase (Program definition).Λ) :
    TM2.Stmt (Program definition).Γ (Phase (Program definition).Λ) (State definition) :=
  match phase with
  | .start => pop (Program definition).k₀ (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1 = some 4) (goto fun _ => .pairAtom)
        (load (fun state => (state.1, state.2.1, state.2.1 = some 3)) (goto fun _ => .drain)))
  | .pairAtom => pop (Program definition).k₀ (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1 = some 3) (goto fun _ => .pairTag)
        (load (fun state => (state.1, state.2.1, false)) (goto fun _ => .drain)))
  | .pairTag => pop (Program definition).k₀ (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1 = some 1) (goto fun _ => .nodeEnd)
        (load (fun state => (state.1, state.2.1, state.2.1 = some 2)) (goto fun _ => .drain)))
  | .nodeEnd => pop (Program definition).k₀ (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1 = some 2)
        (load (fun _ => ((Program definition).initialState, none, false))
          (goto fun _ => .run (Program definition).main))
        (load (fun state => (state.1, state.2.1, false)) (goto fun _ => .drain)))
  | .run label => StackMachineRegisters.returning (Extra := Option Alphabet × Bool)
      Phase.run (fun _ => Phase.done) ((Program definition).m label)
  | .done => load (fun _ => ((Program definition).initialState, none, false)) halt
  | .drain => pop (Program definition).k₀ (fun state cell => (state.1, cell, state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .drain) (goto fun _ => .finish))
  | .finish => push (Program definition).k₁ (fun state => some state.2.2)
      (load (fun _ => ((Program definition).initialState, none, false)) halt)

def machine : FinTM2 where
  K := (Program definition).K
  k₀ := (Program definition).k₀
  k₁ := (Program definition).k₁
  Γ := (Program definition).Γ
  Γk₀Fin := (Program definition).Γk₀Fin
  Λ := Phase (Program definition).Λ
  main := .start
  σ := State definition
  initialState := ((Program definition).initialState, none, false)
  m := statement definition

attribute [local implicit_reducible] machine FinTM2.Cfg

def config (phase : Option (Phase (Program definition).Λ)) (state : State definition)
    (contents : ∀ key, List ((Program definition).Γ key)) : (machine definition).Cfg :=
  ⟨phase, state, contents⟩

abbrev inputContents (input : List Alphabet) :=
  RetainedWordExecution.wordContents (Program definition) (Program definition).k₀ input

local macro "event_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, TM2.step, TM2.stepAux, inputContents,
    RetainedWordExecution.wordContents]
  all_goals try rfl
  all_goals (funext key; by_cases same : key = (Program definition).k₀ <;>
    simp [Function.update, same])))

theorem prefix_start (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .start) state (inputContents definition (4 :: tail))) =
      some (config definition (some .pairAtom) (state.1, some 4, state.2.2)
        (inputContents definition tail)) := by event_step

theorem prefix_atom (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .pairAtom) state (inputContents definition (3 :: tail))) =
      some (config definition (some .pairTag) (state.1, some 3, state.2.2)
        (inputContents definition tail)) := by event_step

theorem prefix_node (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .pairTag) state (inputContents definition (1 :: tail))) =
      some (config definition (some .nodeEnd) (state.1, some 1, state.2.2)
        (inputContents definition tail)) := by event_step

theorem prefix_end (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .nodeEnd) state (inputContents definition (2 :: tail))) =
      some (config definition (some (.run (Program definition).main))
        ((Program definition).initialState, none, false) (inputContents definition tail)) := by event_step

theorem reference_start (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .pairTag) state (inputContents definition (2 :: tail))) =
      some (config definition (some .drain) (state.1, some 2, true)
        (inputContents definition tail)) := by event_step

theorem leave_start (state : State definition) (tail : List Alphabet) :
    (machine definition).step (config definition (some .start) state (inputContents definition (3 :: tail))) =
      some (config definition (some .drain) (state.1, some 3, true)
        (inputContents definition tail)) := by event_step

theorem drain_cons (state : State definition) (head : Alphabet) (tail : List Alphabet) :
    (machine definition).step (config definition (some .drain) state (inputContents definition (head :: tail))) =
      some (config definition (some .drain) (state.1, some head, state.2.2)
        (inputContents definition tail)) := by event_step

theorem drain_nil (state : State definition) :
    (machine definition).step (config definition (some .drain) state (inputContents definition [])) =
      some (config definition (some .finish) (state.1, none, state.2.2)
        (inputContents definition [])) := by event_step

theorem finish (state : State definition) :
    (machine definition).step (config definition (some .finish) state (inputContents definition [])) =
      some (config definition none ((Program definition).initialState, none, false)
        (RetainedWordExecution.wordContents (Program definition) (Program definition).k₁ [some state.2.2])) := by
  simp [FinTM2.step, machine, statement, config, TM2.step, TM2.stepAux,
    inputContents, RetainedWordExecution.wordContents]

noncomputable def drainRun (state : State definition) (input : List Alphabet) :
    EvalsToInTime (machine definition).step
      (config definition (some .drain) state (inputContents definition input))
      (some (config definition none ((Program definition).initialState, none, false)
        (RetainedWordExecution.wordContents (Program definition) (Program definition).k₁ [some state.2.2])))
      (input.length + 2) := by
  induction input generalizing state with
  | nil =>
    have first := StackMachineComposition.oneStep (drain_nil definition state)
    have last := StackMachineComposition.oneStep (finish definition (state.1, none, state.2.2))
    simpa only [List.length_nil, Nat.zero_add] using EvalsToInTime.trans _ _ _ _ _ _ first last
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (drain_cons definition state head tail)
    have last := ih (state.1, some head, state.2.2)
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ _ _ _ _ _ first last

def embed (source : (Program definition).Cfg) : (machine definition).Cfg :=
  config definition (some (source.l.elim .done .run)) (source.var, none, false) source.stk

theorem run_step (before after : (Program definition).Cfg)
    (computed : (Program definition).step before = some after) :
    (machine definition).step (embed definition before) = some (embed definition after) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, embed, config, TM2.step, Option.elim_some]
      rw [StackMachineRegisters.stepAux_returning]
      simp only [StackMachineRegisters.returningConfig]

theorem init_eq (input : List Alphabet) : initList (machine definition) input =
    config definition (some .start) ((Program definition).initialState, none, false)
      (inputContents definition input) := by
  simp only [initList, machine, config, inputContents, RetainedWordExecution.wordContents]
  congr 1
  funext key
  by_cases same : key = (Program definition).k₀
  · subst key; simp
  · simp [Function.update, same]

theorem halt_eq (output : List (Option Bool)) : haltList (machine definition) output =
    config definition none ((Program definition).initialState, none, false)
      (RetainedWordExecution.wordContents (Program definition) (Program definition).k₁ output) := by
  simp only [haltList, machine, config, RetainedWordExecution.wordContents]
  congr 1
  funext key
  by_cases same : key = (Program definition).k₁
  · subst key; simp
  · simp [Function.update, same]

set_option maxRecDepth 4096 in
noncomputable def enterOutputs (ruleInstance : RuleInstance) :
    TM2OutputsInTime (machine definition) (enterWord ruleInstance)
      (some [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)])
      (20300 * ((encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1)^2 + 5) := by
  have first := StackMachineComposition.oneStep (prefix_start definition
    ((Program definition).initialState, none, false)
    (3 :: 1 :: 2 :: encodeWith CertificateDataEncoding.instanceCodec ruleInstance))
  have second := StackMachineComposition.oneStep (prefix_atom definition
    ((Program definition).initialState, some 4, false)
    (1 :: 2 :: encodeWith CertificateDataEncoding.instanceCodec ruleInstance))
  have third := StackMachineComposition.oneStep (prefix_node definition
    ((Program definition).initialState, some 3, false)
    (2 :: encodeWith CertificateDataEncoding.instanceCodec ruleInstance))
  have fourth := StackMachineComposition.oneStep (prefix_end definition
    ((Program definition).initialState, some 1, false)
    (encodeWith CertificateDataEncoding.instanceCodec ruleInstance))
  have original := applicationOutputs definition ruleInstance
  have walked := StackMachineComposition.lift_execution (Program definition).step
    (machine definition).step (embed definition) (run_step definition) original
  have last := StackMachineComposition.oneStep (show (machine definition).step
      (embed definition (haltList (Program definition)
        [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)])) =
      some (haltList (machine definition)
        [some (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance)]) by
    simp [FinTM2.step, machine, statement, embed, config, haltList, TM2.step, TM2.stepAux])
  have a := EvalsToInTime.trans _ _ _ _ _ _ first second
  have b := EvalsToInTime.trans _ _ _ _ _ _ a third
  have c := EvalsToInTime.trans _ _ _ _ _ _ b fourth
  have startEq : embed definition (initList (Program definition)
      (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)) =
      config definition (some (.run (Program definition).main))
        ((Program definition).initialState, none, false)
        (inputContents definition (encodeWith CertificateDataEncoding.instanceCodec ruleInstance)) := by
    rw [RetainedWordExecution.source_init]; rfl
  rw [startEq] at walked
  have d := EvalsToInTime.trans _ _ _ _ _ _ c walked
  have e := EvalsToInTime.trans _ _ _ _ _ _ d last
  change EvalsToInTime _ (initList (machine definition) _) (some (haltList (machine definition) _)) _
  rw [init_eq, enterWord_eq]
  convert e using 1
  all_goals first | omega | rfl


noncomputable def referenceOutputs (index : Nat) :
    TM2OutputsInTime (machine definition) (referenceWord index) (some [some true])
      ((referenceWord index).length + 2) := by
  have first := StackMachineComposition.oneStep (prefix_start definition
    ((Program definition).initialState, none, false) (3 :: 2 :: encodeData (.atom index)))
  have second := StackMachineComposition.oneStep (prefix_atom definition
    ((Program definition).initialState, some 4, false) (2 :: encodeData (.atom index)))
  have third := StackMachineComposition.oneStep (reference_start definition
    ((Program definition).initialState, some 3, false) (encodeData (.atom index)))
  have drained := drainRun definition ((Program definition).initialState, some 2, true) (encodeData (.atom index))
  have a := EvalsToInTime.trans _ _ _ _ _ _ first second
  have b := EvalsToInTime.trans _ _ _ _ _ _ a third
  have c := EvalsToInTime.trans _ _ _ _ _ _ b drained
  change EvalsToInTime _ (initList (machine definition) _) (some (haltList (machine definition) _)) _
  rw [init_eq, halt_eq, referenceWord_eq]
  convert c using 1
  · rfl
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega

noncomputable def leaveOutputs :
    TM2OutputsInTime (machine definition) leaveWord (some [some true]) (leaveWord.length + 2) := by
  have first := StackMachineComposition.oneStep (leave_start definition
    ((Program definition).initialState, none, false) [0, 1, 2])
  have drained := drainRun definition ((Program definition).initialState, some 3, true) [0, 1, 2]
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first drained
  change EvalsToInTime _ (initList (machine definition) _) (some (haltList (machine definition) _)) _
  rw [init_eq, halt_eq, leaveWord_eq]
  convert joined using 1
  decide

end Event

/-- The established structural visitor, rather than this local operation,
authorizes which complete words reach its event admission callee. -/
def Generated (word : List Alphabet) : Prop :=
  (∃ index, word = referenceWord index) ∨
    (∃ ruleInstance, word = enterWord ruleInstance) ∨ word = leaveWord

/-- A source-visible admission observation on the existing event words.
Reference currentness and child judgments are supplied by the outer driver. -/
def wordResult (word : List Alphabet) : Bool :=
  if word.take 4 = [4, 3, 1, 2] then
    ((decodeWith CertificateDataEncoding.instanceCodec (word.drop 4)).map
      (CertificateRuleAdmission.ScopedApplication.scopeResult definition)).getD false
  else true

theorem wordResult_enter (ruleInstance : RuleInstance) :
    wordResult definition (enterWord ruleInstance) =
      CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance := by
  rw [enterWord_eq]
  simp [wordResult, decodeWith_encodeWith]

theorem wordResult_reference (index : Nat) : wordResult definition (referenceWord index) = true := by
  rw [referenceWord_eq]
  simp [wordResult, encodeData_atom, natural]

theorem wordResult_leave : wordResult definition leaveWord = true := by
  simp [wordResult, leaveWord_eq]

mutual
  theorem proofWords_generated (proof : RawOpenProof) (word : List Alphabet)
      (member : word ∈ proofWords proof) : Generated word := by
    cases proof with
    | premise index =>
      simp only [proofWords, List.mem_singleton] at member
      exact Or.inl ⟨index, member⟩
    | node ruleInstance children =>
      simp only [proofWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with (same | child) | same
      · exact Or.inr (Or.inl ⟨ruleInstance, same⟩)
      · exact childrenWords_generated children word child
      · exact Or.inr (Or.inr same)
  termination_by sizeOf proof
  theorem childrenWords_generated (children : List RawOpenProof) (word : List Alphabet)
      (member : word ∈ childrenWords children) : Generated word := by
    cases children with
    | nil => simp [childrenWords] at member
    | cons child children =>
      simp only [childrenWords, List.mem_append] at member
      rcases member with member | member
      · exact proofWords_generated child word member
      · exact childrenWords_generated children word member
  termination_by sizeOf children
end

local instance : Fintype ((Event.machine definition).Γ (Event.machine definition).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance : Inhabited ((Event.machine definition).Γ (Event.machine definition).k₀) := by
  change Inhabited Alphabet; infer_instance

theorem generatedRun (word : List Alphabet) (generated : Generated word) :
    Nonempty (TM2OutputsInTime (Event.machine definition) word (some [some (wordResult definition word)])
      (20310 * (word.length + 1)^2)) := by
  rcases generated with ⟨index, same⟩ | ⟨ruleInstance, same⟩ | same
  · subst word
    rw [wordResult_reference]
    refine ⟨WordEqualityMachine.within (Event.referenceOutputs definition index) ?_⟩
    nlinarith
  · subst word
    rw [wordResult_enter]
    refine ⟨WordEqualityMachine.within (Event.enterOutputs definition ruleInstance) ?_⟩
    have lengths : (encodeWith CertificateDataEncoding.instanceCodec ruleInstance).length + 1 ≤
        (enterWord ruleInstance).length + 1 := by
      rw [enterWord_eq]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have squared := Nat.pow_le_pow_left lengths 2
    have positive := Nat.one_le_pow' 2 (enterWord ruleInstance).length
    omega
  · subst word
    rw [wordResult_leave]
    refine ⟨WordEqualityMachine.within (Event.leaveOutputs definition) ?_⟩
    simp [leaveWord_eq]

/-- This chooses only a mathematical execution witness; the finite transition
body above is the executable operation and contains no proof extraction. -/
noncomputable def generatedOutputs (word : List Alphabet) (generated : Generated word) :
    TM2OutputsInTime (Event.machine definition) word (some [some (wordResult definition word)])
      (20310 * (word.length + 1)^2) := Classical.choice (generatedRun definition word generated)

/-- Original event values are retained; this subtype merely records the
structural visitor's proved image invariant for each supplied field. -/
def values (proof : RawOpenProof) : List {word : List Alphabet // Generated word} :=
  (proofWords proof).attach.map (fun word => ⟨word.1, proofWords_generated proof word.1 word.2⟩)

theorem values_words (proof : RawOpenProof) : (values proof).map Subtype.val = proofWords proof := by
  simp [values, List.map_map]

/-- Local application admission, folded over the established ordered events.
It is deliberately distinct from the original semantic proof checker. -/
def proofResult (proof : RawOpenProof) : Bool := (proofWords proof).all (wordResult definition)

theorem proofResult_reference (index : Nat) : proofResult definition (.premise index) = true := by
  simp [proofResult, proofWords, wordResult_reference]

theorem proofResult_node (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    proofResult definition (.node ruleInstance children) =
      (CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance &&
        children.all (proofResult definition)) := by
  have childFold : (childrenWords children).all (wordResult definition) =
      children.all (proofResult definition) := by
    induction children with
    | nil => rfl
    | cons child children ih => simp [childrenWords, List.all_append, proofResult, ih]
  simp only [proofResult, proofWords, List.all_append, List.all_cons, List.all_nil,
    wordResult_enter, wordResult_leave, Bool.and_true, childFold]

/-- Every supplied node is included, including unused or duplicated branches. -/
theorem proofResult_node_iff (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    proofResult definition (.node ruleInstance children) = true ↔
      CertificateRuleAdmission.ScopedApplication.scopeResult definition ruleInstance = true ∧
        ∀ child ∈ children, proofResult definition child = true := by
  rw [proofResult_node, Bool.and_eq_true, List.all_eq_true]

mutual
  /-- Accepted original open proofs pass the local admission phase. This is a
  consequence of the original checker, not an alternative proof authority. -/
  theorem proofResult_of_checked {definition : ValidatedCalculusLanguageDef}
      (zeroDepth : ∀ index : Fin definition.1.rules.length,
        ∀ formal ∈ (CertificateRuleAdmission.row definition.1 index).metavariables, formal.2 = 0)
      (context : List Pattern) (goal : Pattern) (proof : RawOpenProof)
      (accepted : checkOpenRaw definition context goal proof = true) :
      proofResult definition.1 proof = true := by
    cases proof with
    | premise index => exact proofResult_reference definition.1 index
    | node ruleInstance children =>
      cases instanceResult : instantiateRule? definition ruleInstance with
      | none => simp only [checkOpenRaw, instanceResult, Bool.false_eq_true] at accepted
      | some instantiation =>
        rcases instantiation with ⟨premises, conclusion⟩
        have source := accepted
        simp only [checkOpenRaw, instanceResult, Bool.and_eq_true] at source
        rw [proofResult_node, Bool.and_eq_true]
        exact ⟨CertificateRuleAdmission.ScopedApplication.scopeResult_of_application zeroDepth instanceResult,
          childrenResult_of_checked zeroDepth context premises children source.2⟩
  termination_by sizeOf proof
  theorem childrenResult_of_checked {definition : ValidatedCalculusLanguageDef}
      (zeroDepth : ∀ index : Fin definition.1.rules.length,
        ∀ formal ∈ (CertificateRuleAdmission.row definition.1 index).metavariables, formal.2 = 0)
      (context premises : List Pattern) (children : List RawOpenProof)
      (accepted : checkOpenRawChildren definition context premises children = true) :
      children.all (proofResult definition.1) = true := by
    cases premises with
    | nil =>
      cases children with
      | nil => rfl
      | cons child rest => simp only [checkOpenRawChildren, Bool.false_eq_true] at accepted
    | cons premise premises =>
      cases children with
      | nil => simp only [checkOpenRawChildren, Bool.false_eq_true] at accepted
      | cons child rest =>
        simp only [checkOpenRawChildren, Bool.and_eq_true] at accepted
        simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨proofResult_of_checked zeroDepth context premise child accepted.1,
          childrenResult_of_checked zeroDepth context premises rest accepted.2⟩
  termination_by sizeOf children
end

local instance : Fintype ((FramedWordValidation.retainedMachine
    (Event.machine definition) FramedWordValidation.readBoolean).Γ
    (FramedWordValidation.retainedMachine
      (Event.machine definition) FramedWordValidation.readBoolean).k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance

local instance : Inhabited ((FramedWordValidation.retainedMachine
    (Event.machine definition) FramedWordValidation.readBoolean).Γ
    (FramedWordValidation.retainedMachine
      (Event.machine definition) FramedWordValidation.readBoolean).k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def vectorMachine : FinTM2 := FramedWordValidation.retainedMachine
  (Event.machine definition) FramedWordValidation.readBoolean

attribute [local implicit_reducible] vectorMachine

def vectorOutput (proof : RawOpenProof) : List (Option Alphabet ⊕ Bool) :=
  .inr (proofResult definition proof) :: (events proof).map Sum.inl

theorem values_frame (proof : RawOpenProof) :
    FramedWordValidation.frameWords (Event.machine definition) Subtype.val (values proof) = events proof := by
  rw [FramedWordValidation.frameWords, values_words]
  rfl

theorem responses_eq (inputs : List {word : List Alphabet // Generated word}) :
    FramedWordValidation.responses (Event.machine definition) FramedWordValidation.readBoolean
      (fun word => some (wordResult definition word.1)) inputs =
      (inputs.map Subtype.val).all (wordResult definition) := by
  induction inputs with
  | nil => rfl
  | cons value rest ih =>
    simp only [FramedWordValidation.responses, FramedWordValidation.readBoolean,
      Option.getD_some, List.map_cons, List.all_cons, ih]

noncomputable def vectorOutputs (proof : RawOpenProof) :
    TM2OutputsInTime (vectorMachine definition) (events proof) (some (vectorOutput definition proof))
      (20322 * ((events proof).length + 1)^2) := by
  have run := FramedWordValidation.retainedOutputs (Event.machine definition)
    FramedWordValidation.readBoolean Subtype.val
    (fun word : {word : List Alphabet // Generated word} => some (wordResult definition word.1))
    (fun word => 20310 * (word.1.length + 1)^2)
    (fun word => generatedOutputs definition word.1 word.2) (values proof)
  rw [values_frame, responses_eq, values_words] at run
  apply WordEqualityMachine.within (by
    simpa only [vectorMachine, vectorOutput, proofResult, TM2OutputsInTime] using run)
  have bound := FramedWordValidation.retainedClock_quadratic (Event.machine definition)
    Subtype.val (fun word : {word : List Alphabet // Generated word} => 20310 * (word.1.length + 1)^2)
    20310 (fun _ => Nat.le_refl _) (values proof)
  rw [values_frame] at bound
  exact bound

def acceptStatus (status : Option Alphabet) : Bool := status == some 1

def dispatcher : FinTM2 := StackMachineComposition.Dispatch.machine
  (vectorMachine definition) acceptStatus [.inr false]

attribute [local implicit_reducible] dispatcher

noncomputable def dispatcherOutputs (proof : RawOpenProof) :
    TM2OutputsInTime (dispatcher definition) (output proof)
      (some (vectorOutput definition proof)) (20322 * ((events proof).length + 1)^2 + 1) := by
  have run := StackMachineComposition.Dispatch.outputs_success (vectorMachine definition)
    acceptStatus [.inr false] (some (1 : Alphabet)) (events proof) (vectorOutput definition proof)
    (20322 * ((events proof).length + 1)^2) (by rfl) (vectorOutputs definition proof)
  simpa only [dispatcher, output, CertificateArgumentFraming.statusWire] using run

local instance : Fintype (Execution.machine.Γ Execution.machine.k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance : Inhabited (Execution.machine.Γ Execution.machine.k₁) := by
  change Inhabited (Option Alphabet); infer_instance

def machine : FinTM2 := StackMachineComposition.machine Execution.machine
  (dispatcher definition) (Equiv.refl _)

attribute [local implicit_reducible] machine

/-- The original proof visitor checks the complete outer word before its
ordered event vector reaches the admission loop. All supplied events execute,
and the exact original event bytes are retained in the result. -/
noncomputable def outputs (proof : RawOpenProof) :
    TM2OutputsInTime (machine definition) (CertificateDataEncoding.encodeProof proof)
      (some (vectorOutput definition proof))
      (82000 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2) := by
  have first := Execution.outputs proof
  have second := dispatcherOutputs definition proof
  have joined := StackMachineComposition.outputs Execution.machine (dispatcher definition) (Equiv.refl _)
    (CertificateDataEncoding.encodeProof proof) (output proof) (vectorOutput definition proof)
    (Execution.executionCost proof) (20322 * ((events proof).length + 1)^2 + 1) first (by
      change TM2OutputsInTime (dispatcher definition) ((output proof).map id) _ _
      simpa only [List.map_id_fun, id_eq] using second)
  apply WordEqualityMachine.within joined
  have firstBound := Execution.executionCost_le proof
  have vectorBound := Execution.events_length_le proof
  have extent : (CertificateDataEncoding.encodeProof proof).length =
      dataWeight (CertificateDataEncoding.putProof proof) := writeData_length _ []
  have transferred : (output proof).length = (events proof).length + 1 := by
    simp [output, CertificateArgumentFraming.statusWire]
  rw [← extent] at vectorBound
  rw [transferred]
  nlinarith

noncomputable def realization : TM2ComputableInPolyTime CertificateDataEncoding.encodeProof
    (vectorOutput definition) (fun proof : RawOpenProof => proof) where
  tm := machine definition
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 82000 * (X + C 1)^2
  outputsFun proof := by
    change TM2OutputsInTime (machine definition) ((CertificateDataEncoding.encodeProof proof).map id)
      (some ((vectorOutput definition proof).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using outputs definition proof

namespace Packet

namespace Field
attribute [local implicit_reducible] CertificateDataTraversal.ProductField.machine
abbrev Program := CertificateDataTraversal.ProductField.machine true
abbrev State := Program.σ × Option Alphabet
local instance : Fintype Program.K := Program.kFin
local instance : Fintype Program.Λ := Program.ΛFin
local instance : Fintype Program.σ := Program.σFin
local instance (n : Nat) : OfNat (Program.Γ Program.k₀) n := by
  change OfNat Alphabet n
  infer_instance

inductive Phase where
  | start | second | run (label : CertificateDataTraversal.ProductField.Phase) | done
  | copy | restore | reject
  deriving DecidableEq, Fintype

/-- Original row fields are parsed by the existing product selector. Root
proof fields are physically copied unchanged to the same success protocol. -/
def statement (phase : Phase) : TM2.Stmt Program.Γ Phase State :=
  match phase with
  | .start => pop Program.k₀ (fun state cell => (state.1, cell))
      (branch (fun state => state.2 == some 4) (goto fun _ => .second) (goto fun _ => .reject))
  | .second => pop Program.k₀ (fun state cell => (state.1, cell))
      (branch (fun state => state.2 == some 4)
        (push Program.k₀ (fun _ => (4 : Alphabet)) (push Program.k₀ (fun _ => (4 : Alphabet))
          (load (fun _ => (Program.initialState, none)) (goto fun _ => .run Program.main))))
        (branch (fun state => state.2 == some 3)
          (push Program.k₀ (fun _ => (3 : Alphabet)) (push Program.k₀ (fun _ => (4 : Alphabet))
            (load (fun _ => (Program.initialState, none)) (goto fun _ => .copy))))
          (goto fun _ => .reject)))
  | .run label => StackMachineRegisters.returning (Extra := Option Alphabet)
      Phase.run (fun _ => .done) (Program.m label)
  | .done => load (fun _ => (Program.initialState, none)) halt
  | .copy => pop Program.k₀ (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (push (none : Program.K) (fun state => state.2.getD 2) (goto fun _ => .copy))
        (goto fun _ => .restore))
  | .restore => pop (none : Program.K) (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome)
        (push Program.k₁ (fun state => state.2.getD 2) (goto fun _ => .restore))
        (push Program.k₁ (fun _ => (1 : Alphabet)) (load (fun _ => (Program.initialState, none)) halt)))
  | .reject => pop Program.k₀ (fun state cell => (state.1, cell))
      (branch (fun state => state.2.isSome) (goto fun _ => .reject)
        (push Program.k₁ (fun _ => (0 : Alphabet)) (load (fun _ => (Program.initialState, none)) halt)))

def machine : FinTM2 where
  K := Program.K
  k₀ := Program.k₀
  k₁ := Program.k₁
  Γ := Program.Γ
  Γk₀Fin := Program.Γk₀Fin
  Λ := Phase
  main := .start
  σ := State
  initialState := (Program.initialState, none)
  m := statement

attribute [local implicit_reducible] machine FinTM2.Cfg

def config (phase : Option Phase) (state : State) (input memo : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk key := match (show Option CertificateDataTraversal.Stack from key) with
    | none => memo
    | some .input => input
    | some .frames | some .output => []

local macro "packet_step" : tactic => `(tactic| (
  simp_all [FinTM2.step, machine, statement, config, Program, TM2.step, TM2.stepAux,
    CertificateDataTraversal.ProductField.machine, Function.update,
    (show ((some (3 : Alphabet)) == some (4 : Alphabet)) = false from rfl)]
  all_goals first | rfl | (funext key; cases key with
    | none => rfl
    | some key => cases key <;> rfl)))

theorem start (state : State) (input memo : List Alphabet) :
    machine.step (config (some .start) state (4 :: input) memo) =
      some (config (some .second) (state.1, some 4) input memo) := by packet_step

theorem row (state : State) (input memo : List Alphabet) :
    machine.step (config (some .second) state (4 :: input) memo) =
      some (config (some (.run Program.main)) (Program.initialState, none) (4 :: 4 :: input) memo) := by
  packet_step

theorem root (state : State) (input memo : List Alphabet) :
    machine.step (config (some .second) state (3 :: input) memo) =
      some (config (some .copy) (Program.initialState, none) (4 :: 3 :: input) memo) := by packet_step

theorem copy_cons (state : State) (head : Alphabet) (tail memo : List Alphabet) :
    machine.step (config (some .copy) state (head :: tail) memo) =
      some (config (some .copy) (state.1, some head) tail (head :: memo)) := by packet_step

theorem copy_nil (state : State) (memo : List Alphabet) :
    machine.step (config (some .copy) state [] memo) =
      some (config (some .restore) (state.1, none) [] memo) := by packet_step

theorem restore_cons (state : State) (head : Alphabet) (input memo : List Alphabet) :
    machine.step (config (some .restore) state input (head :: memo)) =
      some (config (some .restore) (state.1, some head) (head :: input) memo) := by packet_step

theorem restore_nil (state : State) (input : List Alphabet) :
    machine.step (config (some .restore) state input []) =
      some (config none (Program.initialState, none) (1 :: input) []) := by packet_step

noncomputable def copyRun (state : State) (input memo : List Alphabet) :
    EvalsToInTime machine.step (config (some .copy) state input memo)
      (some (config (some .restore) (state.1, none) [] (input.reverse ++ memo))) (input.length + 1) := by
  induction input generalizing state memo with
  | nil => simpa using StackMachineComposition.oneStep (copy_nil state memo)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (copy_cons state head tail memo)
    have last := ih (state.1, some head) (head :: memo)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ _ _ _ _ _ first last

noncomputable def restoreRun (state : State) (input memo : List Alphabet) :
    EvalsToInTime machine.step (config (some .restore) state input memo)
      (some (config none (Program.initialState, none) (1 :: memo.reverse ++ input) [])) (memo.length + 1) := by
  induction memo generalizing state input with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil state input)
  | cons head tail ih =>
    have first := StackMachineComposition.oneStep (restore_cons state head input tail)
    have last := ih (state.1, some head) (head :: input)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      EvalsToInTime.trans _ _ _ _ _ _ first last

def embed (source : Program.Cfg) : machine.Cfg :=
  ⟨some (source.l.elim .done .run), (source.var, none), source.stk⟩

theorem run_step (before after : Program.Cfg) (computed : Program.step before = some after) :
    machine.step (embed before) = some (embed after) := by
  cases before with
  | mk label state contents =>
    cases label with
    | none => cases computed
    | some label =>
      simp only [FinTM2.step, TM2.step] at computed
      cases computed
      simp only [FinTM2.step, machine, statement, embed, TM2.step, Option.elim_some]
      rw [StackMachineRegisters.stepAux_returning]
      simp only [StackMachineRegisters.returningConfig]

theorem init_eq (input : List Alphabet) : initList machine input = config (some .start) (Program.initialState, none) input [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

theorem halt_eq (output : List Alphabet) : haltList machine output = config none (Program.initialState, none) output [] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

theorem proof_prefix (proof : RawOpenProof) :
    ∃ tail, CertificateDataEncoding.encodeProof proof = 4 :: 3 :: tail := by
  cases proof with
  | premise index => exact ⟨2 :: encodeData (.atom index), CertificateChronologicalTraversal.premise_wire index⟩
  | node ruleInstance children =>
    refine ⟨1 :: 2 :: (4 :: encodeWith CertificateDataEncoding.instanceCodec ruleInstance ++
      encodeWith (Codec.list CertificateDataEncoding.proofCodec) children), ?_⟩
    rw [CertificateChronologicalTraversal.node_wire]
    rfl

theorem row_prefix (goal : Pattern) (proof : RawOpenProof) :
    ∃ tail, encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof) = 4 :: 4 :: tail := by
  have tokens : Mettapedia.OSLF.MeTTaIL.PatternTokens.encode goal ≠ [] := by
    cases goal <;> simp [Mettapedia.OSLF.MeTTaIL.PatternTokens.encode, Mettapedia.OSLF.MeTTaIL.PatternTokens.write]
  cases encoded : Mettapedia.OSLF.MeTTaIL.PatternTokens.encode goal with
  | nil => exact False.elim (tokens encoded)
  | cons head tail =>
    refine ⟨encodeWith Codec.string head ++ encodeWith (Codec.list Codec.string) tail ++
      CertificateDataEncoding.encodeProof proof, ?_⟩
    simp only [CertificateChronologicalTraversal.Execution.rowCodec, encodeWith, Codec.prod,
      CertificateDataEncoding.patternCodec, Codec.mapped, Codec.list, encoded, Codec.putList,
      encodeData_pair, CertificateDataEncoding.encodeProof]
    rfl

noncomputable def rootOutputs (proof : RawOpenProof) :
    TM2OutputsInTime machine (CertificateDataEncoding.encodeProof proof)
      (some ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof))
      (2 * (CertificateDataEncoding.encodeProof proof).length + 4) := by
  let tail := (CertificateDataEncoding.encodeProof proof).drop 2
  have shape : CertificateDataEncoding.encodeProof proof = 4 :: 3 :: tail := by
    obtain ⟨suffix, shape⟩ := proof_prefix proof
    dsimp [tail]
    rw [shape]; rfl
  have first := StackMachineComposition.oneStep (start (Program.initialState, none) (3 :: tail) [])
  have second := StackMachineComposition.oneStep (root (Program.initialState, some 4) tail [])
  have copied := copyRun (Program.initialState, none) (4 :: 3 :: tail) []
  have restored := restoreRun (Program.initialState, none) [] (4 :: 3 :: tail).reverse
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at copied restored
  have a := EvalsToInTime.trans _ _ _ _ _ _ first second
  have b := EvalsToInTime.trans _ _ _ _ _ _ a copied
  have c := EvalsToInTime.trans _ _ _ _ _ _ b restored
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq, shape]
  convert c using 1
  omega

noncomputable def rowOutputs (goal : Pattern) (proof : RawOpenProof) :
    TM2OutputsInTime machine (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))
      (some ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof))
      (4 * (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).length + 6) := by
  let tail := (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).drop 2
  have shape : encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof) = 4 :: 4 :: tail := by
    obtain ⟨suffix, shape⟩ := row_prefix goal proof
    dsimp [tail]
    rw [shape]; rfl
  have first := StackMachineComposition.oneStep (start (Program.initialState, none) (4 :: tail) [])
  have second := StackMachineComposition.oneStep (row (Program.initialState, some 4) tail [])
  have original : TM2OutputsInTime Program
      (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))
      (some ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof))
      (4 * (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).length + 3) := by
    have run := CertificateDataTraversal.ProductField.outputs true
      (CertificateDataEncoding.patternCodec.put goal) (CertificateDataEncoding.proofCodec.put proof)
    apply WordEqualityMachine.within (by
      simpa only [Program, CertificateChronologicalTraversal.Execution.rowCodec,
        CertificateDataEncoding.encodeProof, encodeWith, Codec.prod,
        CertificateDataTraversal.ProductField.selected, if_true, TM2OutputsInTime] using run)
    have first := CertificateDataTraversal.scanCost_add_one_le (CertificateDataEncoding.patternCodec.put goal)
    have second := CertificateDataTraversal.scanCost_add_one_le (CertificateDataEncoding.proofCodec.put proof)
    simp only [CertificateChronologicalTraversal.Execution.rowCodec, encodeWith, Codec.prod,
      encodeData, writeData_length, List.length_nil, dataWeight]
    omega
  have walked := StackMachineComposition.lift_execution Program.step machine.step embed run_step original
  have startEq : embed (initList Program (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))) =
      config (some (.run Program.main)) (Program.initialState, none)
        (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)) [] := by
    simp only [embed, initList, config, Program, CertificateDataTraversal.ProductField.machine]
    congr 1
    funext key
    cases key with
    | none => rfl
    | some key => cases key <;> rfl
  have last := StackMachineComposition.oneStep (show machine.step
      (embed (haltList Program ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof))) =
      some (haltList machine ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof)) by
    simp [FinTM2.step, machine, statement, embed, haltList, Program,
      CertificateDataTraversal.ProductField.machine, TM2.step, TM2.stepAux])
  rw [startEq] at walked
  have a := EvalsToInTime.trans _ _ _ _ _ _ first second
  have b := EvalsToInTime.trans _ _ _ _ _ _ a (by rw [shape] at walked; exact walked)
  have c := EvalsToInTime.trans _ _ _ _ _ _ b last
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, shape]
  convert c using 1
  omega


end Field

/-- The proof machine's physical admission tag is projected once; its retained
working events are cleared by the same executed word homomorphism. -/
def project : Option Alphabet ⊕ Bool → List (Option Bool)
  | .inr result => [some result]
  | .inl _ => []

local instance : Fintype ((Admission.machine definition).Γ (Admission.machine definition).k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance : Inhabited ((Admission.machine definition).Γ (Admission.machine definition).k₁) := by
  change Inhabited (Option Alphabet ⊕ Bool); infer_instance
local instance : Fintype ((WordHomomorphismMachine.machine project).Γ
    (WordHomomorphismMachine.machine project).k₁) := by
  change Fintype (Option Bool); infer_instance

def proofMachine : FinTM2 := StackMachineComposition.machine
  (Admission.machine definition) (WordHomomorphismMachine.machine project) (Equiv.refl _)

attribute [local implicit_reducible] proofMachine

theorem project_output (proof : RawOpenProof) :
    (Admission.vectorOutput definition proof).flatMap project = [some (Admission.proofResult definition proof)] := by
  simp [Admission.vectorOutput, project, List.flatMap_map]

noncomputable def proofOutputs (proof : RawOpenProof) :
    TM2OutputsInTime (proofMachine definition) (CertificateDataEncoding.encodeProof proof)
      (some [some (Admission.proofResult definition proof)])
      (82500 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2) := by
  have projected := WordHomomorphismMachine.outputs project (Admission.vectorOutput definition proof)
  rw [project_output] at projected
  have joined := StackMachineComposition.outputs (Admission.machine definition)
    (WordHomomorphismMachine.machine project) (Equiv.refl _)
    (CertificateDataEncoding.encodeProof proof) (Admission.vectorOutput definition proof)
    [some (Admission.proofResult definition proof)]
    (82000 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2)
    (2 * (Admission.vectorOutput definition proof).length + 4)
    (Admission.outputs definition proof) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project)
        ((Admission.vectorOutput definition proof).map id) _ _
      simpa only [List.map_id_fun, id_eq, List.length_cons, List.length_nil, Nat.add_zero] using projected)
  apply WordEqualityMachine.within joined
  have bound := Execution.events_length_le proof
  have extent : (CertificateDataEncoding.encodeProof proof).length =
      dataWeight (CertificateDataEncoding.putProof proof) := writeData_length _ []
  rw [← extent] at bound
  simp only [Admission.vectorOutput, List.length_cons, List.length_map] at *
  nlinarith

local instance : Fintype ((proofMachine definition).Γ (proofMachine definition).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance : Inhabited ((proofMachine definition).Γ (proofMachine definition).k₀) := by
  change Inhabited Alphabet; infer_instance

def proofDispatcher : FinTM2 := StackMachineComposition.Dispatch.machine
  (proofMachine definition) (fun tag : Alphabet => tag == 1) [some false]

attribute [local implicit_reducible] proofDispatcher

noncomputable def proofDispatcherOutputs (proof : RawOpenProof) :
    TM2OutputsInTime (proofDispatcher definition) ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof)
      (some [some (Admission.proofResult definition proof)])
      (82500 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2 + 1) := by
  exact StackMachineComposition.Dispatch.outputs_success (proofMachine definition)
    (fun tag : Alphabet => tag == 1) [some false] (1 : Alphabet)
    (CertificateDataEncoding.encodeProof proof) [some (Admission.proofResult definition proof)]
    (82500 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2) (by rfl)
    (proofOutputs definition proof)

local instance : Fintype (Field.machine.Γ Field.machine.k₁) := by
  change Fintype Alphabet; infer_instance
local instance : Inhabited (Field.machine.Γ Field.machine.k₁) := by
  change Inhabited Alphabet; infer_instance

def fieldMachine : FinTM2 := StackMachineComposition.machine Field.machine
  (proofDispatcher definition) (Equiv.refl _)

attribute [local implicit_reducible] fieldMachine

noncomputable def rootOutputs (proof : RawOpenProof) :
    TM2OutputsInTime (fieldMachine definition) (CertificateDataEncoding.encodeProof proof)
      (some [some (Admission.proofResult definition proof)])
      (85000 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2) := by
  have joined := StackMachineComposition.outputs Field.machine (proofDispatcher definition) (Equiv.refl _)
    (CertificateDataEncoding.encodeProof proof) ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof)
    [some (Admission.proofResult definition proof)]
    (2 * (CertificateDataEncoding.encodeProof proof).length + 4)
    (82500 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2 + 1)
    (Field.rootOutputs proof) (by
      change TM2OutputsInTime (proofDispatcher definition)
        (((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof).map id) _ _
      simpa only [List.map_id_fun, id_eq] using proofDispatcherOutputs definition proof)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons]
  nlinarith

noncomputable def rowOutputs (goal : Pattern) (proof : RawOpenProof) :
    TM2OutputsInTime (fieldMachine definition)
      (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))
      (some [some (Admission.proofResult definition proof)])
      (85000 * ((encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).length + 1)^2) := by
  have joined := StackMachineComposition.outputs Field.machine (proofDispatcher definition) (Equiv.refl _)
    (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))
    ((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof) [some (Admission.proofResult definition proof)]
    (4 * (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).length + 6)
    (82500 * ((CertificateDataEncoding.encodeProof proof).length + 1)^2 + 1)
    (Field.rowOutputs goal proof) (by
      change TM2OutputsInTime (proofDispatcher definition)
        (((1 : Alphabet) :: CertificateDataEncoding.encodeProof proof).map id) _ _
      simpa only [List.map_id_fun, id_eq] using proofDispatcherOutputs definition proof)
  apply WordEqualityMachine.within joined
  have smaller : (CertificateDataEncoding.encodeProof proof).length ≤
      (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).length := by
    simp only [CertificateDataEncoding.encodeProof, CertificateChronologicalTraversal.Execution.rowCodec,
      encodeWith, Codec.prod, encodeData_pair, List.length_cons, List.length_append]
    omega
  have squared := Nat.pow_le_pow_left (Nat.add_le_add_right smaller 1) 2
  simp only [List.length_cons]
  nlinarith

/-- These are precisely original chronological row and root field images. -/
def Generated (word : List Alphabet) : Prop :=
  (∃ proof, word = CertificateDataEncoding.encodeProof proof) ∨
    (∃ goal proof, word = encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof))

def fieldResult (word : List Alphabet) : Bool :=
  if word.take 2 = [4, 3] then
    ((decodeWith CertificateDataEncoding.proofCodec word).map (Admission.proofResult definition)).getD false
  else ((decodeWith CertificateChronologicalTraversal.Execution.rowCodec word).map
    (fun row => Admission.proofResult definition row.2)).getD false

theorem fieldResult_root (proof : RawOpenProof) :
    fieldResult definition (CertificateDataEncoding.encodeProof proof) = Admission.proofResult definition proof := by
  have headShape : (CertificateDataEncoding.encodeProof proof).take 2 = [4, 3] := by
    obtain ⟨tail, shape⟩ := Field.proof_prefix proof
    rw [shape]; rfl
  unfold fieldResult
  rw [headShape, if_pos rfl]
  simp only [CertificateDataEncoding.encodeProof, decodeWith_encodeWith,
    Option.map_some, Option.getD_some]

theorem fieldResult_row (goal : Pattern) (proof : RawOpenProof) :
    fieldResult definition (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)) =
      Admission.proofResult definition proof := by
  have headShape : (encodeWith CertificateChronologicalTraversal.Execution.rowCodec (goal, proof)).take 2 = [4, 4] := by
    obtain ⟨tail, shape⟩ := Field.row_prefix goal proof
    rw [shape]; rfl
  simp [fieldResult, headShape, decodeWith_encodeWith]

theorem words_generated (source : CertificateChronologicalTraversal.Source) (word : List Alphabet)
    (member : word ∈ CertificateChronologicalTraversal.words source) : Generated word := by
  simp only [CertificateChronologicalTraversal.words, List.mem_append, List.mem_map, List.mem_singleton] at member
  rcases member with ⟨row, member, same⟩ | same
  · exact Or.inr ⟨row.1, row.2, same.symm⟩
  · exact Or.inl ⟨source.2, same⟩

local instance : Fintype ((fieldMachine definition).Γ (fieldMachine definition).k₁) := by
  change Fintype (Option Bool); infer_instance
local instance : Inhabited ((fieldMachine definition).Γ (fieldMachine definition).k₀) := by
  change Inhabited Alphabet; infer_instance

theorem generatedRun (word : List Alphabet) (generated : Generated word) :
    Nonempty (TM2OutputsInTime (fieldMachine definition) word (some [some (fieldResult definition word)])
      (85000 * (word.length + 1)^2)) := by
  rcases generated with ⟨proof, same⟩ | ⟨goal, proof, same⟩
  · subst word
    rw [fieldResult_root]
    exact ⟨rootOutputs definition proof⟩
  · subst word
    rw [fieldResult_row]
    exact ⟨rowOutputs definition goal proof⟩

noncomputable def generatedOutputs (word : List Alphabet) (generated : Generated word) :
    TM2OutputsInTime (fieldMachine definition) word (some [some (fieldResult definition word)])
      (85000 * (word.length + 1)^2) := Classical.choice (generatedRun definition word generated)

def values (source : CertificateChronologicalTraversal.Source) : List {word : List Alphabet // Generated word} :=
  (CertificateChronologicalTraversal.words source).attach.map
    (fun word => ⟨word.1, words_generated source word.1 word.2⟩)

theorem values_words (source : CertificateChronologicalTraversal.Source) :
    (values source).map Subtype.val = CertificateChronologicalTraversal.words source := by
  simp [values, List.map_map]

/-- All supplied lemma proofs, including unused rows, followed by the root.
Claim/root equality and chronological reference meanings remain driver gates. -/
def result (source : CertificateChronologicalTraversal.Source) : Bool :=
  source.1.all (fun row => Admission.proofResult definition row.2) && Admission.proofResult definition source.2

theorem result_words (source : CertificateChronologicalTraversal.Source) :
    (CertificateChronologicalTraversal.words source).all (fieldResult definition) = result definition source := by
  have rowLaw : ∀ row : Pattern × RawOpenProof,
      fieldResult definition (encodeWith CertificateChronologicalTraversal.Execution.rowCodec row) =
        Admission.proofResult definition row.2 := by
    rintro ⟨goal, proof⟩
    exact fieldResult_row definition goal proof
  simp only [CertificateChronologicalTraversal.words, List.all_append, List.all_map,
    List.all_cons, List.all_nil, fieldResult_root, Bool.and_true, result, Function.comp_def]
  simp only [rowLaw]

def vectorMachine : FinTM2 := FramedWordValidation.retainedMachine
  (fieldMachine definition) FramedWordValidation.readBoolean

attribute [local implicit_reducible] vectorMachine

def vectorOutput (source : CertificateChronologicalTraversal.Source) : List (Option Alphabet ⊕ Bool) :=
  .inr (result definition source) :: (CertificateChronologicalTraversal.events source).map Sum.inl

theorem values_frame (source : CertificateChronologicalTraversal.Source) :
    FramedWordValidation.frameWords (fieldMachine definition) Subtype.val (values source) =
      CertificateChronologicalTraversal.events source := by
  rw [FramedWordValidation.frameWords, values_words]
  rfl

theorem responses_eq (inputs : List {word : List Alphabet // Generated word}) :
    FramedWordValidation.responses (fieldMachine definition) FramedWordValidation.readBoolean
      (fun word => some (fieldResult definition word.1)) inputs =
      (inputs.map Subtype.val).all (fieldResult definition) := by
  induction inputs with
  | nil => rfl
  | cons value rest ih =>
    simp only [FramedWordValidation.responses, FramedWordValidation.readBoolean,
      Option.getD_some, List.map_cons, List.all_cons, ih]

noncomputable def vectorOutputs (source : CertificateChronologicalTraversal.Source) :
    TM2OutputsInTime (vectorMachine definition) (CertificateChronologicalTraversal.events source)
      (some (vectorOutput definition source))
      (85012 * ((CertificateChronologicalTraversal.events source).length + 1)^2) := by
  have run := FramedWordValidation.retainedOutputs (fieldMachine definition)
    FramedWordValidation.readBoolean Subtype.val
    (fun word : {word : List Alphabet // Generated word} => some (fieldResult definition word.1))
    (fun word => 85000 * (word.1.length + 1)^2)
    (fun word => generatedOutputs definition word.1 word.2) (values source)
  rw [values_frame, responses_eq, values_words, result_words] at run
  apply WordEqualityMachine.within (by simpa only [vectorMachine, vectorOutput, TM2OutputsInTime] using run)
  have bound := FramedWordValidation.retainedClock_quadratic (fieldMachine definition)
    Subtype.val (fun word : {word : List Alphabet // Generated word} => 85000 * (word.1.length + 1)^2)
    85000 (fun _ => Nat.le_refl _) (values source)
  rw [values_frame] at bound
  exact bound

local instance : Fintype ((vectorMachine definition).Γ (vectorMachine definition).k₁) := by
  change Fintype (Option Alphabet ⊕ Bool); infer_instance
local instance : Inhabited ((vectorMachine definition).Γ (vectorMachine definition).k₀) := by
  change Inhabited (Option Alphabet); infer_instance

def dispatcher : FinTM2 := StackMachineComposition.Dispatch.machine
  (vectorMachine definition) Admission.acceptStatus [.inr false]

attribute [local implicit_reducible] dispatcher

noncomputable def dispatcherOutputs (source : CertificateChronologicalTraversal.Source) :
    TM2OutputsInTime (dispatcher definition) (CertificateChronologicalTraversal.output source)
      (some (vectorOutput definition source))
      (85012 * ((CertificateChronologicalTraversal.events source).length + 1)^2 + 1) := by
  have run := StackMachineComposition.Dispatch.outputs_success (vectorMachine definition)
    Admission.acceptStatus [.inr false] (some (1 : Alphabet))
    (CertificateChronologicalTraversal.events source) (vectorOutput definition source)
    (85012 * ((CertificateChronologicalTraversal.events source).length + 1)^2) (by rfl)
    (vectorOutputs definition source)
  simpa only [dispatcher, CertificateChronologicalTraversal.output,
    CertificateArgumentFraming.statusWire] using run

local instance : Fintype (CertificateChronologicalTraversal.Execution.machine.Γ
    CertificateChronologicalTraversal.Execution.machine.k₁) := by
  change Fintype (Option Alphabet); infer_instance
local instance : Inhabited (CertificateChronologicalTraversal.Execution.machine.Γ
    CertificateChronologicalTraversal.Execution.machine.k₁) := by
  change Inhabited (Option Alphabet); infer_instance

def machine : FinTM2 := StackMachineComposition.machine CertificateChronologicalTraversal.Execution.machine
  (dispatcher definition) (Equiv.refl _)

attribute [local implicit_reducible] machine

/-- Whole original chronological packets physically visit every supplied row
and root proof. Local admission, unchanged field retention and the complete
visitor boundary all participate in this counted run. -/
noncomputable def outputs (source : CertificateChronologicalTraversal.Source) :
    TM2OutputsInTime (machine definition) (CertificateDataEncoding.encodeShared source)
      (some (vectorOutput definition source))
      (90000 * ((CertificateDataEncoding.encodeShared source).length + 1)^2) := by
  have joined := StackMachineComposition.outputs CertificateChronologicalTraversal.Execution.machine
    (dispatcher definition) (Equiv.refl _)
    (CertificateDataEncoding.encodeShared source) (CertificateChronologicalTraversal.output source)
    (vectorOutput definition source) (CertificateChronologicalTraversal.Execution.executionCost source)
    (85012 * ((CertificateChronologicalTraversal.events source).length + 1)^2 + 1)
    (CertificateChronologicalTraversal.Execution.outputs source) (by
      change TM2OutputsInTime (dispatcher definition)
        ((CertificateChronologicalTraversal.output source).map id) _ _
      simpa only [List.map_id_fun, id_eq] using dispatcherOutputs definition source)
  apply WordEqualityMachine.within joined
  have firstBound := CertificateChronologicalTraversal.Execution.executionCost_le source
  have extent := CertificateChronologicalTraversal.Execution.events_length source
  have transfer : (CertificateChronologicalTraversal.output source).length =
      (CertificateChronologicalTraversal.events source).length + 1 := by
    simp [CertificateChronologicalTraversal.output, CertificateArgumentFraming.statusWire]
  rw [transfer]
  have squared := Nat.pow_le_pow_left
    (show (CertificateChronologicalTraversal.events source).length + 1 ≤
      (CertificateDataEncoding.encodeShared source).length + 1 by omega) 2
  nlinarith

noncomputable def realization : TM2ComputableInPolyTime CertificateDataEncoding.encodeShared
    (vectorOutput definition) (fun source : CertificateChronologicalTraversal.Source => source) where
  tm := machine definition
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 90000 * (X + C 1)^2
  outputsFun source := by
    change TM2OutputsInTime (machine definition) ((CertificateDataEncoding.encodeShared source).map id)
      (some ((vectorOutput definition source).map id)) _
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using outputs definition source



/-- The complete ordered submission contributes to this phase, even when a
later source proof never refers to a particular lemma row. -/
theorem result_iff (source : CertificateChronologicalTraversal.Source) :
    result definition source = true ↔
      (∀ row ∈ source.1, Admission.proofResult definition row.2 = true) ∧
        Admission.proofResult definition source.2 = true := by
  simp only [result, Bool.and_eq_true, List.all_eq_true]

theorem unused_refused (source : CertificateChronologicalTraversal.Source)
    (row : Pattern × RawOpenProof) (member : row ∈ source.1)
    (refused : Admission.proofResult definition row.2 = false) : result definition source = false := by
  cases outcome : result definition source with
  | false => rfl
  | true =>
    have accepted := ((result_iff definition source).mp outcome).1 row member
    rw [refused] at accepted
    cases accepted

namespace Controls

def empty : CalculusLanguageDef :=
  {name := "empty", rules := [], types := [], terms := [], equations := [], rewrites := []}

def missing : RawOpenProof := .node {ruleId := ⟨"absent"⟩, arguments := []} []

def unused : CertificateChronologicalTraversal.Source :=
  ([(.apply "claim" [], missing)], .premise 0)

theorem unused_missing_refused : result empty unused = false := by decide

theorem duplicate_missing_fields :
    result empty (unused.1 ++ unused.1, unused.2) = false := by decide

/-- Local admission leaves reference availability to the original cache gate. -/
theorem reference_requires_outer_gate (index : Nat) :
    result empty ([], .premise index) = true := by
  simp [result, Admission.proofResult_reference]

end Controls

namespace Boundary
abbrev Chrono := CertificateChronologicalTraversal.Execution.machine

def rejectPhase : CertificateArgumentFraming.Execution.Phase 0 → CertificateChronologicalTraversal.Execution.Phase
  | .rejectInput => .rejectInput
  | .rejectFrames => .rejectFrames
  | .rejectPost => .rejectPost
  | .rejectPrefix => .rejectPrefix
  | .rejectVector => .rejectVector
  | .rejectResult => .rejectResult
  | _ => .rejectInput

def rejectEmbed (source : (CertificateArgumentFraming.Execution.machine 0).Cfg) : Chrono.Cfg :=
  ⟨source.l.map rejectPhase, source.var, source.stk⟩

theorem reject_step (source : (CertificateArgumentFraming.Execution.machine 0).Cfg)
    (valid : Execution.rejecting source) :
    Chrono.step (rejectEmbed source) =
      ((CertificateArgumentFraming.Execution.machine 0).step source).map rejectEmbed := by
  cases source with
  | mk label state contents =>
    cases label with
    | none => rfl
    | some phase =>
      cases phase <;> simp only [Execution.rejecting] at valid <;> try contradiction
      all_goals
        simp only [FinTM2.step, Chrono, CertificateChronologicalTraversal.Execution.machine,
          CertificateArgumentFraming.Execution.machine, TM2.step, TM2.stepAux,
          rejectEmbed, rejectPhase, Option.map_some, Bool.cond_eq_ite]
        split <;> rfl

noncomputable def rejectRun (state : CertificateArgumentFraming.Execution.State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime Chrono.step
      (CertificateChronologicalTraversal.Execution.config (some .rejectInput) state input frames post memo vector result)
      (some (CertificateChronologicalTraversal.Execution.config none (none, none) [] [] [] [] [] [some 0]))
      (input.length + frames.length + post.length + memo.length + vector.length + result.length + 6) := by
  have original := CertificateArgumentFraming.Execution.rejectInputRun 0 state input frames post memo vector result
  have lifted := StackMachineRegisters.evalsInto (CertificateArgumentFraming.Execution.machine 0).step
    Chrono.step rejectEmbed Execution.rejecting Execution.rejecting_preserved reject_step (by trivial) original
  simpa only [rejectEmbed, CertificateArgumentFraming.Execution.config,
    CertificateChronologicalTraversal.Execution.config, Option.map_some, Option.map_none, rejectPhase] using lifted

theorem check_trailing (state : CertificateArgumentFraming.Execution.State)
    (head : Alphabet) (tail : List Alphabet) (vector result : List (Option Alphabet)) :
    Chrono.step (CertificateChronologicalTraversal.Execution.config (some .checkEnd) state
      (head :: tail) [] [] [] vector result) =
      some (CertificateChronologicalTraversal.Execution.config (some .rejectInput) (some head, state.2)
        tail [] [] [] vector result) := by
  simp only [FinTM2.step, Chrono, CertificateChronologicalTraversal.Execution.machine,
    CertificateChronologicalTraversal.Execution.config, CertificateArgumentFraming.Execution.config,
    TM2.step, TM2.stepAux, CertificateArgumentFraming.Execution.inputKey, List.head?_cons, List.tail_cons,
    Option.isNone_some, Bool.cond_false]
  congr 2
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

/-- The original chronological visitor rejects every nonempty submission
suffix before exposing its event vector to the admission loop. -/
noncomputable def trailingOutputs (source : CertificateChronologicalTraversal.Source)
    (head : Alphabet) (tail : List Alphabet) :
    TM2OutputsInTime Chrono (CertificateDataEncoding.encodeShared source ++ head :: tail) (some [some 0])
      (CertificateChronologicalTraversal.Execution.executionCost source + tail.length + 5) := by
  let rest := head :: tail
  have begin := StackMachineComposition.oneStep (CertificateChronologicalTraversal.Execution.start_pair
    (none, none) (writeData ((Codec.list CertificateChronologicalTraversal.Execution.rowCodec).put source.1)
      (writeData (CertificateDataEncoding.proofCodec.put source.2) rest)) [] [])
  have rows := CertificateChronologicalTraversal.Execution.rowsRun
    CertificateChronologicalTraversal.Execution.rowCodec source.1
    (writeData (CertificateDataEncoding.proofCodec.put source.2) rest) (some 4, none) [] []
  have root := CertificateChronologicalTraversal.Execution.fieldRun true none
    (CertificateDataEncoding.proofCodec.put source.2) rest
    ((CertificateArgumentFraming.framedArguments CertificateChronologicalTraversal.Execution.rowCodec source.1).reverse ++ []) [] (some 2)
  simp only [if_true, List.append_nil] at root rows
  have framing :
      none :: (CertificateDataEncoding.encodeProof source.2).reverse.map some ++
          (CertificateArgumentFraming.framedArguments CertificateChronologicalTraversal.Execution.rowCodec source.1).reverse =
        (CertificateChronologicalTraversal.events source).reverse := by
    simp only [CertificateChronologicalTraversal.events, CertificateChronologicalTraversal.words,
      WordTemplateMachine.Indexed.frame, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.reverse_append, List.reverse_cons,
      List.map_reverse,
      CertificateArgumentFraming.framedArguments, CertificateArgumentFraming.argumentWords,
      List.flatMap_map, CertificateDataEncoding.encodeProof]
    rfl
  have checked := StackMachineComposition.oneStep (check_trailing (none, none) head tail
    (CertificateChronologicalTraversal.events source).reverse [])
  have cleanup := rejectRun (some head, none) tail [] [] []
    (CertificateChronologicalTraversal.events source).reverse []
  rw [← framing] at checked cleanup
  have a := EvalsToInTime.trans _ _ _ _ _ _ begin rows
  have b := EvalsToInTime.trans _ _ _ _ _ _ a root
  have c := EvalsToInTime.trans _ _ _ _ _ _ b checked
  have d := EvalsToInTime.trans _ _ _ _ _ _ c cleanup
  change EvalsToInTime _ (initList Chrono _) (some (haltList Chrono _)) _
  rw [CertificateChronologicalTraversal.Execution.init_eq, CertificateChronologicalTraversal.Execution.halt_eq]
  convert d using 1
  · apply congrArg (fun input => CertificateChronologicalTraversal.Execution.config
      (some .start) (none, none) input [] [] [] [] [])
    change CertificateDataEncoding.encodeShared source ++ rest =
      writeData (CertificateDataEncoding.sharedCodec.put source) rest
    exact (writeData_append (CertificateDataEncoding.sharedCodec.put source) rest).symm
  · simp only [CertificateChronologicalTraversal.Execution.executionCost, List.length_reverse,
      List.length_nil, Nat.add_zero, framing]
    omega

end Boundary

/-- A trailing submission is explicitly refused by the existing boundary;
no unvalidated event vector is forwarded to local admission. -/
noncomputable def trailingOutputs (source : CertificateChronologicalTraversal.Source)
    (head : Alphabet) (tail : List Alphabet) :
    TM2OutputsInTime (machine definition)
      (CertificateDataEncoding.encodeShared source ++ head :: tail) (some [.inr false])
      (CertificateChronologicalTraversal.Execution.executionCost source + tail.length + 12) := by
  have refused := StackMachineComposition.Dispatch.outputs_refused (vectorMachine definition)
    Admission.acceptStatus [.inr false] (some (0 : Alphabet)) [] (by rfl)
  have joined := StackMachineComposition.outputs Boundary.Chrono (dispatcher definition) (Equiv.refl _)
    (CertificateDataEncoding.encodeShared source ++ head :: tail) [some 0] [.inr false]
    (CertificateChronologicalTraversal.Execution.executionCost source + tail.length + 5) 2
    (Boundary.trailingOutputs source head tail) (by
      change TM2OutputsInTime (dispatcher definition) (([some (0 : Alphabet)]).map id) _ _
      simpa only [dispatcher, List.map_id_fun, id_eq, List.length_nil, Nat.zero_add] using refused)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons, List.length_nil]
  omega

end Packet

end Admission

end Mettapedia.GSLT.LanguageDef.CertificateProofTraversal

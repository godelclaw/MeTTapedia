import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

/-!
# Chronological traversal of the original shared certificate

This finite-control iterator emits each original encoded lemma field, followed
by the final open proof. It retains all submitted rows, including unused rows,
and preserves their physical order and repeated payloads. A separate source
checker still decides rule, goal, argument and reference admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.CertificateChronologicalTraversal

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open CertificateGSLT InferenceChecker
open _root_.Computability Turing StateTransition Polynomial
open ProofSystems
open Mettapedia.Computability
open Turing.TM2.Stmt
open CertificateDataTraversal

abbrev Source := List (Pattern × RawOpenProof) × RawOpenProof

def words (source : Source) : List (List Alphabet) :=
  source.1.map (encodeWith (Codec.prod CertificateDataEncoding.patternCodec
    CertificateDataEncoding.proofCodec)) ++ [CertificateDataEncoding.encodeProof source.2]

def events (source : Source) : List (Option Alphabet) :=
  WordTemplateMachine.Indexed.frame (words source)

def output (source : Source) : List (Option Alphabet) :=
  CertificateArgumentFraming.statusWire (some (events source))

theorem words_length (source : Source) : (words source).length = source.1.length + 1 := by
  simp [words]

theorem words_row (source : Source) (index : Nat) (earlier : index < source.1.length) :
    (words source)[index]? = (source.1[index]?).map
      (encodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec)) := by
  simp [words, List.getElem?_append, earlier]

theorem words_root (source : Source) :
    (words source)[source.1.length]? = some (CertificateDataEncoding.encodeProof source.2) := by
  simp [words]

/-- Each emitted lemma is still interpreted by the original pair codec. -/
theorem decode_row (row : Pattern × RawOpenProof) :
    decodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec)
      (encodeWith (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec) row) =
      some row := decodeWith_encodeWith _ _

theorem decode_root (root : RawOpenProof) :
    CertificateDataEncoding.decodeProof (CertificateDataEncoding.encodeProof root) = some root :=
  CertificateDataEncoding.decodeProof_encodeProof _

/-- The original proof-child field is the existing list codec. It can feed the
same authored-arity admission operation as any other original list field. -/
theorem proof_children_put (children : List RawOpenProof) :
    CertificateDataEncoding.putProofs children =
      (Codec.list CertificateDataEncoding.proofCodec).put children := by
  induction children with
  | nil => rfl
  | cons child children ih => simp only [CertificateDataEncoding.putProofs,
      Codec.list, Codec.putList, CertificateDataEncoding.proofCodec] at *; rw [ih]

theorem proof_children_wire (children : List RawOpenProof) :
    encodeData (CertificateDataEncoding.putProofs children) =
      encodeWith (Codec.list CertificateDataEncoding.proofCodec) children := by
  rw [proof_children_put]; rfl

theorem premise_wire (index : Nat) :
    CertificateDataEncoding.encodeProof (.premise index) =
      4 :: encodeData (.atom 0) ++ encodeData (.atom index) := by
  change encodeData (.pair (.atom 0) (.atom index)) = _
  simp only [encodeData_pair, List.cons_append]

theorem node_wire (ruleInstance : RuleInstance) (children : List RawOpenProof) :
    CertificateDataEncoding.encodeProof (.node ruleInstance children) =
      4 :: encodeData (.atom 1) ++ 4 :: encodeWith CertificateDataEncoding.instanceCodec ruleInstance ++
        encodeWith (Codec.list CertificateDataEncoding.proofCodec) children := by
  simp only [CertificateDataEncoding.encodeProof, encodeWith, CertificateDataEncoding.proofCodec,
    CertificateDataEncoding.putProof, encodeData_pair, proof_children_put,
    List.cons_append, List.append_assoc]

namespace Execution

open CertificateArgumentFraming.Execution

inductive Phase where
  | start | spine | nilEnd
  | field (last : Bool) (phase : CertificateDataTraversal.Phase)
  | clearPost (last : Bool) | restorePrefix (last : Bool) | copyWord (last : Bool)
  | checkEnd | restoreVector
  | rejectInput | rejectFrames | rejectPost | rejectPrefix | rejectVector | rejectResult
  deriving DecidableEq, Fintype

local instance : Fintype PrefixField.machine.K := PrefixField.machine.kFin

/-- The original field parser retains both caller-owned output stacks. -/
def parserBody (last : Bool) (phase : CertificateDataTraversal.Phase) : TM2.Stmt Cells Phase State :=
  StackMachineRegisters.withStack id (StackMachineRegisters.withStack id
    (StackMachineRegisters.extend (Phase.field last) (PrefixField.machine.m phase)))

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
    | .start => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4) (goto fun _ => .spine) (goto fun _ => .rejectInput))
    | .spine => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4) (goto fun _ => .field false .header)
          (branch (fun state => state.1 == some 3) (goto fun _ => .nilEnd) (goto fun _ => .rejectInput)))
    | .nilEnd => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2) (goto fun _ => .field true .header) (goto fun _ => .rejectInput))
    | .field last .checkTail => goto fun _ => .clearPost last
    | .field _ .rejectInput => goto fun _ => .rejectInput
    | .field last phase => parserBody last phase
    | .clearPost last => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .clearPost last)
          (goto fun _ => .restorePrefix last))
    | .restorePrefix last => pop prefixKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push postKey (fun state => state.1.getD 2) (goto fun _ => .restorePrefix last))
          (goto fun _ => .copyWord last))
    | .copyWord last => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push vectorKey (fun state => some (state.1.getD 2)) (goto fun _ => .copyWord last))
          (push vectorKey (fun _ => none) (goto fun _ => if last then .checkEnd else .spine)))
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

local macro "iteration_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, CertificateArgumentFraming.Execution.config,
    inputKey, framesKey, postKey, prefixKey, vectorKey, resultKey, Turing.TM2.step, Turing.TM2.stepAux, (show ((3 : Alphabet) == 4) = false from rfl)] <;>
  (funext key
   cases key with
   | none => simp [Function.update]
   | some key => cases key with
     | none => simp [Function.update]
     | some key => cases key with
       | none => simp [Function.update]
       | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible))))

theorem start_pair (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .start) state (4 :: input) [] [] [] vector result) =
      some (config (some .spine) (some 4, state.2) input [] [] [] vector result) := by iteration_step

theorem spine_cons (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .spine) state (4 :: input) [] [] [] vector result) =
      some (config (some (.field false .header)) (some 4, state.2) input [] [] [] vector result) := by iteration_step

theorem spine_nil (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .spine) state (3 :: input) [] [] [] vector result) =
      some (config (some .nilEnd) (some 3, state.2) input [] [] [] vector result) := by iteration_step

theorem nil_end (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some .nilEnd) state (2 :: input) [] [] [] vector result) =
      some (config (some (.field true .header)) (some 2, state.2) input [] [] [] vector result) := by iteration_step

theorem field_return (last : Bool) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.field last .checkTail)) state input [] post memo vector result) =
      some (config (some (.clearPost last)) state input [] post memo vector result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem clear_post_cons (last : Bool) (state : State)
    (head : Alphabet) (input tail memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.clearPost last)) state input [] (head :: tail) memo vector result) =
      some (config (some (.clearPost last)) (some head, state.2) input [] tail memo vector result) := by iteration_step

theorem clear_post_nil (last : Bool) (state : State)
    (input memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.clearPost last)) state input [] [] memo vector result) =
      some (config (some (.restorePrefix last)) (none, state.2) input [] [] memo vector result) := by iteration_step

theorem restore_prefix_cons (last : Bool) (state : State)
    (head : Alphabet) (input post tail : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.restorePrefix last)) state input [] post (head :: tail) vector result) =
      some (config (some (.restorePrefix last)) (some head, state.2) input [] (head :: post) tail vector result) := by iteration_step

theorem restore_prefix_nil (last : Bool) (state : State)
    (input post : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.restorePrefix last)) state input [] post [] vector result) =
      some (config (some (.copyWord last)) (none, state.2) input [] post [] vector result) := by iteration_step

theorem copy_word_cons (last : Bool) (state : State)
    (head : Alphabet) (input tail : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.copyWord last)) state input [] (head :: tail) [] vector result) =
      some (config (some (.copyWord last)) (some head, state.2) input [] tail [] (some head :: vector) result) := by iteration_step

theorem copy_word_nil (last : Bool) (state : State)
    (input : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.copyWord last)) state input [] [] [] vector result) =
      some (config (some (if last then .checkEnd else .spine)) (none, state.2) input [] [] [] (none :: vector) result) := by iteration_step

theorem restore_vector_cons  (state : State)
    (head : Option Alphabet) (tail result : List (Option Alphabet)) :
    machine.step (config (some .restoreVector) state [] [] [] [] (head :: tail) result) =
      some (config (some .restoreVector) (state.1, some head) [] [] [] [] tail (head :: result)) := by iteration_step

theorem restore_vector_nil  (state : State) (result : List (Option Alphabet)) :
    machine.step (config (some .restoreVector) state [] [] [] [] [] result) =
      some (config none (none, none) [] [] [] [] [] (some 1 :: result)) := by iteration_step

/-- Embed one original prefix-parser configuration, retaining two arbitrary
caller-owned words and a separate finite output-symbol register. -/
def embed (last : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg) : machine.Cfg :=
  StackMachineRegisters.withStackConfig id result
    (StackMachineRegisters.withStackConfig id vector
      (StackMachineRegisters.config (Phase.field last) extra source))

theorem embed_config (last : Bool) (extra : Option (Option Alphabet))
    (phase : Option CertificateDataTraversal.Phase) (state : Option Alphabet)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    embed last extra vector result (PrefixField.config phase state input frames post memo) =
      config (phase.map (Phase.field last)) (state, extra) input frames post memo vector result := by
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

theorem parser_body (last : Bool) (phase : CertificateDataTraversal.Phase)
    (notTail : phase ≠ .checkTail) (notReject : phase ≠ .rejectInput) :
    machine.m (.field last phase) = parserBody last phase := by
  cases phase <;> first | rfl | exact (notTail rfl).elim | exact (notReject rfl).elim

theorem parser_step (last : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (phase : CertificateDataTraversal.Phase) (atPhase : source.l = some phase)
    (notTail : phase ≠ .checkTail) (notReject : phase ≠ .rejectInput) :
    machine.step (embed last extra vector result source) =
      (PrefixField.machine.step source).map (embed last extra vector result) := by
  have originalStep : PrefixField.machine.step source =
      some (TM2.stepAux (PrefixField.machine.m phase) source.var source.stk) := by
    cases source with
    | mk label register contents => simp_all [FinTM2.step, TM2.step]
  rw [originalStep]
  have first := StackMachineRegisters.stepAux_extend (Phase.field last) extra
    (PrefixField.machine.m phase) source.var source.stk
  have second := StackMachineRegisters.stepAux_withStack id vector
    (StackMachineRegisters.extend (Phase.field last) (PrefixField.machine.m phase))
    (source.var, extra) source.stk
  have third := StackMachineRegisters.stepAux_withStack id result
    (StackMachineRegisters.withStack id
      (StackMachineRegisters.extend (Phase.field last) (PrefixField.machine.m phase)))
    (source.var, extra) (StackMachineRegisters.withStackContents source.stk vector)
  simp only [FinTM2.step, embed, StackMachineRegisters.withStackConfig,
    StackMachineRegisters.config, atPhase, Option.map_some, id_eq, Turing.TM2.step]
  rw [parser_body last phase notTail notReject]
  change some (Turing.TM2.stepAux (parserBody last phase) (source.var, extra)
    (StackMachineRegisters.withStackContents (StackMachineRegisters.withStackContents source.stk vector) result)) = _
  rw [parserBody, third]
  rw [second, first]
  simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.config, Option.map_id]

theorem field_complete_empty (last : Bool) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    machine.step (config (some (.field last .complete)) state input [] post memo vector result) =
      some (config (some (.field last .checkTail)) (none, state.2) input [] post memo vector result) := by
  have original : PrefixField.machine.step (PrefixField.config (some .complete) state.1 input [] post memo) =
      some (PrefixField.config (some .checkTail) none input [] post memo) := by
    simp only [FinTM2.step, PrefixField.machine, PrefixField.config, Turing.TM2.step]
    apply congrArg some
    change TM2.stepAux (StackMachineRegisters.withStack id (CertificateDataTraversal.machine.m .complete))
      state.1 (PrefixField.config (some .complete) state.1 input [] post memo).stk = _
    simp [CertificateDataTraversal.machine, StackMachineRegisters.withStack, PrefixField.config,
      TM2.stepAux, Function.update]
    funext key
    cases key with
    | none => rfl
    | some key => cases key <;> simp
  have lifted := parser_step last state.2 vector result
    (PrefixField.config (some .complete) state.1 input [] post memo) .complete rfl (by decide) (by decide)
  rw [original] at lifted
  simpa only [Option.map_some, embed_config] using lifted

theorem parser_scanning (last : Bool) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (allowed : PrefixField.scanning source) :
    machine.step (embed last extra vector result source) =
      (PrefixField.machine.step source).map (embed last extra vector result) := by
  rcases allowed with atHeader | atNumber | ⟨atComplete, _⟩
  · exact parser_step last extra vector result source .header atHeader (by decide) (by decide)
  · exact parser_step last extra vector result source .number atNumber (by decide) (by decide)
  · exact parser_step last extra vector result source .complete atComplete (by decide) (by decide)

noncomputable def fieldWalk (last : Bool) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some (.field last .header)) (state, extra) (writeData value input) [] [] [] vector result)
      (some (config (some (.field last .complete)) (finalState value, extra) input []
        (postorderWire value).reverse (encodeData value).reverse vector result)) (scanCost value) := by
  have walked := PrefixField.walkInto machine.step (embed last extra vector result)
    (steps := parser_scanning last extra vector result) value input [] [] [] state
  simpa only [embed_config, Option.map_some, List.append_nil] using walked

noncomputable def clearPostRun (last : Bool) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.clearPost last)) state input [] post memo vector result)
      (some (config (some (.restorePrefix last)) (none, state.2) input [] [] memo vector result))
      (post.length + 1) := by
  induction post generalizing state with
  | nil => exact Mettapedia.Computability.StackMachineComposition.oneStep (clear_post_nil last state input memo vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (clear_post_cons last state head input tail memo vector result)
      have rest := ih (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def restorePrefixRun (last : Bool) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.restorePrefix last)) state input [] post memo vector result)
      (some (config (some (.copyWord last)) (none, state.2) input [] (memo.reverse ++ post) [] vector result))
      (memo.length + 1) := by
  induction memo generalizing state post with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (restore_prefix_nil last state input post vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (restore_prefix_cons last state head input post tail vector result)
      have rest := ih (some head, state.2) (head :: post)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def copyWordRun (last : Bool) (state : State)
    (input post : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some (.copyWord last)) state input [] post [] vector result)
      (some (config (some (if last then .checkEnd else .spine)) (none, state.2) input [] [] [] (none :: post.reverse.map some ++ vector) result))
      (post.length + 1) := by
  induction post generalizing state vector with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (copy_word_nil last state input vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (copy_word_cons last state head input tail vector result)
      have rest := ih (some head, state.2) (some head :: vector)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def restoreVectorRun  (state : State)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some .restoreVector) state [] [] [] [] vector result)
      (some (config none (none, none) [] [] [] [] [] (some 1 :: vector.reverse ++ result)))
      (vector.length + 1) := by
  induction vector generalizing state result with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (restore_vector_nil state result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (restore_vector_cons state head tail result)
      have rest := ih (state.1, some head) (head :: result)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def fieldRun (last : Bool) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some (.field last .header)) (state, extra) (writeData value input) [] [] [] vector result)
      (some (config (some (if last then .checkEnd else .spine)) (none, extra) input [] [] []
        (none :: (encodeData value).reverse.map some ++ vector) result))
      (scanCost value + 3 * dataWeight value + 5) := by
  have walked := fieldWalk last extra value input vector result state
  have boundary := StackMachineComposition.oneStep (field_complete_empty last
    (finalState value, extra) input (postorderWire value).reverse (encodeData value).reverse vector result)
  have returned := StackMachineComposition.oneStep (field_return last (none, extra)
    input (postorderWire value).reverse (encodeData value).reverse vector result)
  have cleared := clearPostRun last (none, extra) input
    (postorderWire value).reverse (encodeData value).reverse vector result
  have restored := restorePrefixRun last (none, extra) input [] (encodeData value).reverse vector result
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have copied := copyWordRun last (none, extra) input (encodeData value) vector result
  have a := EvalsToInTime.trans _ (scanCost value) 1 _ _ _ walked boundary
  have b := EvalsToInTime.trans _ (1 + scanCost value) 1 _ _ _ a returned
  have c := EvalsToInTime.trans _ (1 + (1 + scanCost value))
    ((postorderWire value).reverse.length + 1) _ _ _ b cleared
  have d := EvalsToInTime.trans _ ((postorderWire value).reverse.length + 1 + (1 + (1 + scanCost value)))
    ((encodeData value).length + 1) _ _ _ c restored
  have e := EvalsToInTime.trans _ ((encodeData value).length + 1 + ((postorderWire value).reverse.length + 1 + (1 + (1 + scanCost value))))
    ((encodeData value).length + 1) _ _ _ d copied
  convert e using 1
  simp only [List.length_reverse, postorderWire_length, encodeData, writeData_length, List.length_nil, Nat.add_zero]
  omega


theorem check_end (state : State) (vector result : List (Option Alphabet)) :
    machine.step (config (some .checkEnd) state [] [] [] [] vector result) =
      some (config (some .restoreVector) (none, state.2) [] [] [] [] vector result) := by iteration_step

variable {α : Type}

def rowsCost (codec : Codec α) : List α → Nat
  | [] => 2
  | value :: rest => scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 6 + rowsCost codec rest

/-- Every row is traversed, even if no later proof refers to it. The remaining
root bytes are retained without consuming or re-encoding them. -/
noncomputable def rowsRun (codec : Codec α) (values : List α) (input : List Alphabet)
    (state : State) (vector result : List (Option Alphabet)) :
    EvalsToInTime machine.step
      (config (some .spine) state (writeData ((Codec.list codec).put values) input) [] [] [] vector result)
      (some (config (some (.field true .header)) (some 2, state.2) input [] [] []
        ((CertificateArgumentFraming.framedArguments codec values).reverse ++ vector) result))
      (rowsCost codec values) := by
  induction values generalizing state vector with
  | nil =>
      have first := StackMachineComposition.oneStep (spine_nil state (2 :: input) vector result)
      have second := StackMachineComposition.oneStep (nil_end (some 3, state.2) input vector result)
      have nilWord : writeData ((Codec.list codec).put ([] : List α)) input = (3 :: 2 :: input : List Alphabet) := rfl
      rw [nilWord]
      simpa only [rowsCost, CertificateArgumentFraming.framedArguments,
        CertificateArgumentFraming.argumentWords, List.map_nil,
        WordTemplateMachine.Indexed.frame, List.flatMap_nil, List.reverse_nil,
        List.nil_append] using EvalsToInTime.trans _ 1 1 _ _ _ first second
  | cons value rest ih =>
      have first := StackMachineComposition.oneStep (spine_cons state
        (writeData (codec.put value) (writeData ((Codec.list codec).put rest) input)) vector result)
      have field := fieldRun false state.2 (codec.put value)
        (writeData ((Codec.list codec).put rest) input) vector result (some 4)
      have tail := ih (none, state.2)
        (none :: (encodeWith codec value).reverse.map some ++ vector)
      have joined := EvalsToInTime.trans _ 1 (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5)
        _ _ _ first field
      have finished := EvalsToInTime.trans _
        (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5 + 1)
        (rowsCost codec rest) _ _ _ joined tail
      convert finished using 1
      · rfl
      · simp only [CertificateArgumentFraming.framedArguments_cons, List.reverse_append,
          List.reverse_cons, List.map_reverse, List.append_assoc, List.singleton_append]
      · simp only [rowsCost]; omega

theorem rowsCost_le (codec : Codec α) (values : List α) :
    rowsCost codec values ≤ 6 * (encodeWith (Codec.list codec) values).length := by
  have below : rowsCost codec values ≤ CertificateArgumentFraming.Execution.spineCost codec values := by
    induction values with
    | nil => simp only [rowsCost, CertificateArgumentFraming.Execution.spineCost]; omega
    | cons value rest ih => simp only [rowsCost, CertificateArgumentFraming.Execution.spineCost]; omega
  exact below.trans (CertificateArgumentFraming.Execution.spineCost_le codec values)

theorem init_eq (input : List Alphabet) :
    initList machine input = config (some .start) (none, none) input [] [] [] [] [] := by
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

theorem halt_eq (output : List (Option Alphabet)) :
    haltList machine output = config none (none, none) [] [] [] [] [] output := by
  simp only [haltList, machine, config, CertificateArgumentFraming.Execution.config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key with
      | none => simp [resultKey]
      | some key => cases key <;> simp [resultKey]

abbrev rowCodec := Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec

def executionCost (source : Source) : Nat :=
  1 + rowsCost rowCodec source.1 + scanCost (CertificateDataEncoding.proofCodec.put source.2) +
    3 * dataWeight (CertificateDataEncoding.proofCodec.put source.2) + 5 + 1 + (events source).length + 1

noncomputable def outputs (source : Source) :
    TM2OutputsInTime machine (CertificateDataEncoding.encodeShared source) (some (output source))
      (executionCost source) := by
  rw [TM2OutputsInTime, init_eq, Option.map_some, halt_eq]
  have begin := StackMachineComposition.oneStep (start_pair (none, none)
    (writeData ((Codec.list rowCodec).put source.1)
      (encodeWith CertificateDataEncoding.proofCodec source.2)) [] [])
  have rows := rowsRun rowCodec source.1 (encodeWith CertificateDataEncoding.proofCodec source.2)
    (some 4, none) [] []
  have root := fieldRun true none (CertificateDataEncoding.proofCodec.put source.2) []
    ((CertificateArgumentFraming.framedArguments rowCodec source.1).reverse ++ []) [] (some 2)
  simp only [if_true, List.append_nil] at root
  have checked := StackMachineComposition.oneStep (check_end (none, none)
    (none :: (CertificateDataEncoding.encodeProof source.2).reverse.map some ++
      (CertificateArgumentFraming.framedArguments rowCodec source.1).reverse ++ []) [])
  have restored := restoreVectorRun (none, none)
    (none :: (CertificateDataEncoding.encodeProof source.2).reverse.map some ++
      (CertificateArgumentFraming.framedArguments rowCodec source.1).reverse ++ []) []
  simp only [List.append_nil] at rows checked restored
  have a := EvalsToInTime.trans _ 1 (rowsCost rowCodec source.1) _ _ _ begin rows
  have b := EvalsToInTime.trans _ (rowsCost rowCodec source.1 + 1)
    (scanCost (CertificateDataEncoding.proofCodec.put source.2) + 3 * dataWeight (CertificateDataEncoding.proofCodec.put source.2) + 5)
    _ _ _ a root
  have c := EvalsToInTime.trans _
    (scanCost (CertificateDataEncoding.proofCodec.put source.2) + 3 * dataWeight (CertificateDataEncoding.proofCodec.put source.2) + 5 +
      (rowsCost rowCodec source.1 + 1)) 1 _ _ _ b checked
  have d := EvalsToInTime.trans _
    (1 + (scanCost (CertificateDataEncoding.proofCodec.put source.2) + 3 * dataWeight (CertificateDataEncoding.proofCodec.put source.2) + 5 +
      (rowsCost rowCodec source.1 + 1)))
    ((none :: (CertificateDataEncoding.encodeProof source.2).reverse.map some ++
      (CertificateArgumentFraming.framedArguments rowCodec source.1).reverse).length + 1)
    _ _ _ c restored
  convert d using 1
  · rfl
  · simp only [output, CertificateArgumentFraming.statusWire, events, words,
      WordTemplateMachine.Indexed.frame, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.reverse_append, List.reverse_cons,
      List.reverse_reverse, List.map_reverse,
      CertificateArgumentFraming.framedArguments, CertificateArgumentFraming.argumentWords,
      List.flatMap_map, CertificateDataEncoding.encodeProof]
  · simp only [executionCost, events, words, rowCodec, WordTemplateMachine.Indexed.frame,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.length_cons, List.length_nil, List.length_map, List.length_reverse, List.append_nil,
      CertificateArgumentFraming.framedArguments, CertificateArgumentFraming.argumentWords,
      List.flatMap_map]
    omega

theorem events_length (source : Source) :
    (events source).length + 2 = (CertificateDataEncoding.encodeShared source).length := by
  have rowLength := CertificateArgumentFraming.framedArguments_length rowCodec source.1
  have packet : (CertificateDataEncoding.encodeShared source).length =
      1 + (encodeWith (Codec.list rowCodec) source.1).length +
      (CertificateDataEncoding.encodeProof source.2).length := by
    simp only [CertificateDataEncoding.encodeShared, CertificateDataEncoding.sharedCodec,
      encodeWith, Codec.prod, encodeData_pair, List.length_cons, List.length_append,
      CertificateDataEncoding.encodeProof]
    omega
  rw [packet]
  simp only [events, words, WordTemplateMachine.Indexed.frame, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  change (CertificateArgumentFraming.framedArguments rowCodec source.1).length +
    ((CertificateDataEncoding.encodeProof source.2).length + 1) + 2 = _
  omega

theorem executionCost_le (source : Source) :
    executionCost source ≤ 7 * (CertificateDataEncoding.encodeShared source).length + 8 := by
  have rows := rowsCost_le rowCodec source.1
  have root := scanCost_le (CertificateDataEncoding.proofCodec.put source.2)
  have extent := events_length source
  have packet : (CertificateDataEncoding.encodeShared source).length =
      1 + (encodeWith (Codec.list rowCodec) source.1).length +
      (CertificateDataEncoding.encodeProof source.2).length := by
    simp only [CertificateDataEncoding.encodeShared, CertificateDataEncoding.sharedCodec,
      encodeWith, Codec.prod, encodeData_pair, List.length_cons, List.length_append,
      CertificateDataEncoding.encodeProof]
    omega
  have rootLength : (CertificateDataEncoding.encodeProof source.2).length =
      dataWeight (CertificateDataEncoding.proofCodec.put source.2) := by
    exact writeData_length _ []
  simp only [executionCost]
  omega

noncomputable def realization : TM2ComputableInPolyTime
    CertificateDataEncoding.encodeShared output id where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 7 * X + C 8
  outputsFun source := by
    change TM2OutputsInTime machine ((CertificateDataEncoding.encodeShared source).map id)
      (some ((output source).map id)) _
    simp only [List.map_id]
    have run := outputs source
    refine ⟨run.toEvalsTo, ?_⟩
    simpa only [eval_add, eval_mul, eval_C, eval_X] using
      run.steps_le_m.trans (executionCost_le source)

end Execution

namespace Controls

def repeated (goal : Pattern) (proof : RawOpenProof) : Source :=
  ([(goal, proof), (goal, proof)], .premise 0)

theorem repeated_fields_retained (goal : Pattern) (proof : RawOpenProof) :
    words (repeated goal proof) =
      [encodeWith Execution.rowCodec (goal, proof), encodeWith Execution.rowCodec (goal, proof),
        CertificateDataEncoding.encodeProof (.premise 0)] := rfl

def unusedInvalid : Source :=
  ([(.fvar "unused", CertificateDataEncoding.Controls.hugeReference)], .premise 0)

theorem unused_invalid_is_visited :
    (words unusedInvalid)[0]? = some (encodeWith Execution.rowCodec
      (.fvar "unused", CertificateDataEncoding.Controls.hugeReference)) := rfl

theorem visited_does_not_imply_accepted (definition : ValidatedCalculusLanguageDef) :
    checkOpenRaw definition [] (.fvar "unused") CertificateDataEncoding.Controls.hugeReference = false :=
  CertificateDataEncoding.Controls.huge_refused definition _

end Controls
end Mettapedia.GSLT.LanguageDef.CertificateChronologicalTraversal

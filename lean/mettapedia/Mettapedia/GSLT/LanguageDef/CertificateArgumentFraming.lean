import Mettapedia.GSLT.LanguageDef.CertificateDataTraversal
import Mettapedia.Computability.WordTemplateMachine
import Mettapedia.GSLT.LanguageDef.ProofSystemExecution

/-!
# Executed framing and assembly of original certificate fields

The source is the existing binary encoding of `Codec.list`. Argument fields
retain their complete original prefix words, and the target uses separators
outside the five-symbol argument alphabet. A separate leading status cell
distinguishes success from refusal before any template copier is called.

Framing validates the finite list spine and authored arity. Assembly restores
the original list encoding from framed output fields, preserving order and
duplicates. The source codec and source checker remain responsible for the
meaning of individual fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

open _root_.Computability Turing StateTransition Polynomial
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open Turing.TM2.Stmt

variable {α : Type}

/-- The original writer is retained for every argument, including binary
indices, UTF-8 strings and any nested constructor payload. -/
def argumentWords (codec : Codec α) (values : List α) : List (List Alphabet) :=
  values.map (encodeWith codec)

def framedArguments (codec : Codec α) (values : List α) : List (Option Alphabet) :=
  Indexed.frame (argumentWords codec values)

/-- The status cell is read separately. Success bodies are exactly the
indexed copier's argument framing; refusal has no argument body. -/
def statusWire : Option (List (Option Alphabet)) → List (Option Alphabet)
  | none => [some 0]
  | some body => some 1 :: body

def readStatus : List (Option Alphabet) → Option (Option (List (Option Alphabet)))
  | [some 0] => some none
  | some 1 :: body => some (some body)
  | _ => none

theorem readStatus_statusWire (result : Option (List (Option Alphabet))) :
    readStatus (statusWire result) = some result := by cases result <;> rfl

theorem statusWire_injective : Function.Injective statusWire := by
  intro first second same
  have read := congrArg readStatus same
  simpa only [readStatus_statusWire, Option.some.injEq] using read

theorem frame_append (first second : List (List Alphabet)) :
    Indexed.frame (first ++ second) = Indexed.frame first ++ Indexed.frame second := by
  simp only [Indexed.frame, List.flatMap_append]

theorem encoded_list_length (codec : Codec α) (values : List α) :
    (encodeWith (Codec.list codec) values).length =
      2 + values.length + ((argumentWords codec values).map List.length).sum := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change (encodeData (.pair (codec.put value) ((Codec.list codec).put rest))).length = _
      rw [encodeData_pair]
      change (4 :: (encodeWith codec value ++ encodeWith (Codec.list codec) rest)).length = _
      simp only [List.length_cons, List.length_append, ih, argumentWords,
        List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem framedArguments_length (codec : Codec α) (values : List α) :
    (framedArguments codec values).length + 2 =
      (encodeWith (Codec.list codec) values).length := by
  rw [framedArguments, Indexed.frame_length, encoded_list_length]
  simp only [argumentWords, List.length_map]
  omega

theorem status_length_le (codec : Codec α) (values : List α) :
    (statusWire (some (framedArguments codec values))).length ≤
      (encodeWith (Codec.list codec) values).length := by
  have size := framedArguments_length codec values
  simp only [statusWire, List.length_cons]
  omega

theorem framedArguments_cons (codec : Codec α) (value : α) (rest : List α) :
    framedArguments codec (value :: rest) =
      (encodeWith codec value).map some ++ none :: framedArguments codec rest := by
  simp only [framedArguments, argumentWords, List.map_cons, Indexed.frame,
    List.flatMap_cons, List.append_assoc, List.singleton_append]

theorem framedArguments_duplicates (codec : Codec α) (value : α) :
    framedArguments codec [value, value] =
      ((encodeWith codec value).map some ++ [none]) ++
      ((encodeWith codec value).map some ++ [none]) := by
  simp only [framedArguments, argumentWords, List.map_cons, List.map_nil, Indexed.frame,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

namespace Execution

open CertificateDataTraversal
open Mettapedia.Computability

/-- Two caller-owned stacks hold the reversed vector and its final ordered
result. The parser's own input, frames, postorder and prefix stacks are reused. -/
local instance : Fintype PrefixField.machine.K := PrefixField.machine.kFin

abbrev Key := Option (Option PrefixField.machine.K)
abbrev Cells := StackMachineRegisters.withStackAlphabet
  (StackMachineRegisters.withStackAlphabet PrefixField.machine.Γ (Option Alphabet)) (Option Alphabet)
abbrev State := Option Alphabet × Option (Option Alphabet)

abbrev inputKey : Key := some (some (some .input))
abbrev framesKey : Key := some (some (some .frames))
abbrev postKey : Key := some (some (some .output))
abbrev prefixKey : Key := some (some none)
abbrev vectorKey : Key := some none
abbrev resultKey : Key := none

inductive Phase (arity : Nat) where
  | spine (index : Fin (arity + 1))
  | field (index : Fin (arity + 1)) (phase : CertificateDataTraversal.Phase)
  | clearPost (index : Fin (arity + 1))
  | restorePrefix (index : Fin (arity + 1))
  | copyWord (index : Fin (arity + 1))
  | nilEnd | checkEnd | restoreVector
  | rejectInput | rejectFrames | rejectPost | rejectPrefix | rejectVector | rejectResult
  deriving DecidableEq, Fintype

instance (key : Key) : Fintype (Cells key) := by
  cases key with
  | none => change Fintype (Option Alphabet); infer_instance
  | some key =>
      cases key with
      | none => change Fintype (Option Alphabet); infer_instance
      | some key => cases key <;> change Fintype Alphabet <;> infer_instance

instance (key : Key) : Inhabited (Cells key) := by
  cases key with
  | none => change Inhabited (Option Alphabet); infer_instance
  | some key =>
      cases key with
      | none => change Inhabited (Option Alphabet); infer_instance
      | some key => cases key <;> change Inhabited Alphabet <;> infer_instance

/-- Label, register and stack embeddings retain the original parser body.
Returning from a complete head field is the only successful interception. -/
def parserBody (arity : Nat) (index : Fin (arity + 1))
    (phase : CertificateDataTraversal.Phase) : TM2.Stmt Cells (Phase arity) State :=
  StackMachineRegisters.withStack id (StackMachineRegisters.withStack id
    (StackMachineRegisters.extend (Phase.field index) (PrefixField.machine.m phase)))

/-- Every variable-sized argument and scratch word lives on a stack. The
authored arity appears only in finite labels, never in an unbounded register. -/
def machine (arity : Nat) : FinTM2 where
  K := Key
  k₀ := inputKey
  k₁ := resultKey
  Γ := Cells
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase arity
  main := .spine ⟨0, by omega⟩
  σ := State
  initialState := (none, none)
  m phase := match phase with
    | .spine index => pop inputKey (fun state value => (value, state.2))
        (branch (fun _ => decide (index.val < arity))
          (branch (fun state => state.1 == some 4)
            (goto fun _ => .field index .header) (goto fun _ => .rejectInput))
          (branch (fun state => state.1 == some 3)
            (goto fun _ => .nilEnd) (goto fun _ => .rejectInput)))
    | .field index .checkTail => goto fun _ => .clearPost index
    | .field _ .rejectInput => goto fun _ => .rejectInput
    | .field index phase => parserBody arity index phase
    | .clearPost index => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .clearPost index)
          (goto fun _ => .restorePrefix index))
    | .restorePrefix index => pop prefixKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push postKey (fun state => state.1.getD 2) (goto fun _ => .restorePrefix index))
          (goto fun _ => .copyWord index))
    | .copyWord index => pop postKey (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push vectorKey (fun state => some (state.1.getD 2)) (goto fun _ => .copyWord index))
          (push vectorKey (fun _ => none) (goto fun _ => .spine (advance index))))
    | .nilEnd => pop inputKey (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 2) (goto fun _ => .checkEnd) (goto fun _ => .rejectInput))
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

def config (arity : Nat) (phase : Option (Phase arity)) (state : State)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => result
    | some none => vector
    | some (some none) => memo
    | some (some (some .input)) => input
    | some (some (some .frames)) => frames
    | some (some (some .output)) => post


local macro "framing_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, inputKey, framesKey, postKey,
    prefixKey, vectorKey, resultKey, Turing.TM2.step, Turing.TM2.stepAux] <;>
  (funext key
   cases key with
   | none => simp [Function.update]
   | some key => cases key with
     | none => simp [Function.update]
     | some key => cases key with
       | none => simp [Function.update]
       | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible))))

theorem spine_cons (arity : Nat) (index : Fin (arity + 1)) (room : index.val < arity)
    (state : State) (input : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.spine index)) state (4 :: input) [] [] [] vector result) =
      some (config arity (some (.field index .header)) (some 4, state.2) input [] [] [] vector result) := by
  simp [FinTM2.step, machine, config, inputKey, Turing.TM2.step, Turing.TM2.stepAux, room]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | none => simp [Function.update]
    | some key => cases key with
      | none => simp [Function.update]
      | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible)

theorem spine_nil (arity : Nat) (index : Fin (arity + 1)) (done : index.val = arity)
    (state : State) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.spine index)) state [3,2] [] [] [] vector result) =
      some (config arity (some .nilEnd) (some 3, state.2) [2] [] [] [] vector result) := by
  have noRoom : ¬index.val < arity := by omega
  simp [FinTM2.step, machine, config, inputKey, Turing.TM2.step, Turing.TM2.stepAux, noRoom]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | none => simp [Function.update]
    | some key => cases key with
      | none => simp [Function.update]
      | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible)

theorem nil_end (arity : Nat) (state : State) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .nilEnd) state [2] [] [] [] vector result) =
      some (config arity (some .checkEnd) (some 2, state.2) [] [] [] [] vector result) := by framing_step

theorem check_end (arity : Nat) (state : State) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .checkEnd) state [] [] [] [] vector result) =
      some (config arity (some .restoreVector) (none, state.2) [] [] [] [] vector result) := by framing_step

theorem field_return (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.field index .checkTail)) state input [] post memo vector result) =
      some (config arity (some (.clearPost index)) state input [] post memo vector result) := by
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux]

theorem clear_post_cons (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (head : Alphabet) (input tail memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.clearPost index)) state input [] (head :: tail) memo vector result) =
      some (config arity (some (.clearPost index)) (some head, state.2) input [] tail memo vector result) := by framing_step

theorem clear_post_nil (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.clearPost index)) state input [] [] memo vector result) =
      some (config arity (some (.restorePrefix index)) (none, state.2) input [] [] memo vector result) := by framing_step

theorem restore_prefix_cons (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (head : Alphabet) (input post tail : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.restorePrefix index)) state input [] post (head :: tail) vector result) =
      some (config arity (some (.restorePrefix index)) (some head, state.2) input [] (head :: post) tail vector result) := by framing_step

theorem restore_prefix_nil (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.restorePrefix index)) state input [] post [] vector result) =
      some (config arity (some (.copyWord index)) (none, state.2) input [] post [] vector result) := by framing_step

theorem copy_word_cons (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (head : Alphabet) (input tail : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.copyWord index)) state input [] (head :: tail) [] vector result) =
      some (config arity (some (.copyWord index)) (some head, state.2) input [] tail [] (some head :: vector) result) := by framing_step

theorem copy_word_nil (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.copyWord index)) state input [] [] [] vector result) =
      some (config arity (some (.spine (advance index))) (none, state.2) input [] [] [] (none :: vector) result) := by framing_step

theorem restore_vector_cons (arity : Nat) (state : State)
    (head : Option Alphabet) (tail result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .restoreVector) state [] [] [] [] (head :: tail) result) =
      some (config arity (some .restoreVector) (state.1, some head) [] [] [] [] tail (head :: result)) := by framing_step

theorem restore_vector_nil (arity : Nat) (state : State) (result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .restoreVector) state [] [] [] [] [] result) =
      some (config arity none (none, none) [] [] [] [] [] (some 1 :: result)) := by framing_step

/-- Embed one original prefix-parser configuration, retaining two arbitrary
caller-owned words and a separate finite output-symbol register. -/
def embed (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg) : (machine arity).Cfg :=
  StackMachineRegisters.withStackConfig id result
    (StackMachineRegisters.withStackConfig id vector
      (StackMachineRegisters.config (Phase.field index) extra source))

theorem embed_config (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (phase : Option CertificateDataTraversal.Phase) (state : Option Alphabet)
    (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    embed arity index extra vector result (PrefixField.config phase state input frames post memo) =
      config arity (phase.map (Phase.field index)) (state, extra) input frames post memo vector result := by
  simp only [embed, StackMachineRegisters.withStackConfig, StackMachineRegisters.config,
    PrefixField.config, config, Option.map_id]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

theorem parser_body (arity : Nat) (index : Fin (arity + 1)) (phase : CertificateDataTraversal.Phase)
    (notTail : phase ≠ .checkTail) (notReject : phase ≠ .rejectInput) :
    (machine arity).m (.field index phase) = parserBody arity index phase := by
  cases phase <;> first | rfl | exact (notTail rfl).elim | exact (notReject rfl).elim

theorem parser_step (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (phase : CertificateDataTraversal.Phase) (atPhase : source.l = some phase)
    (notTail : phase ≠ .checkTail) (notReject : phase ≠ .rejectInput) :
    (machine arity).step (embed arity index extra vector result source) =
      (PrefixField.machine.step source).map (embed arity index extra vector result) := by
  have originalStep : PrefixField.machine.step source =
      some (TM2.stepAux (PrefixField.machine.m phase) source.var source.stk) := by
    cases source with
    | mk label register contents => simp_all [FinTM2.step, TM2.step]
  rw [originalStep]
  have first := StackMachineRegisters.stepAux_extend (Phase.field index) extra
    (PrefixField.machine.m phase) source.var source.stk
  have second := StackMachineRegisters.stepAux_withStack id vector
    (StackMachineRegisters.extend (Phase.field index) (PrefixField.machine.m phase))
    (source.var, extra) source.stk
  have third := StackMachineRegisters.stepAux_withStack id result
    (StackMachineRegisters.withStack id
      (StackMachineRegisters.extend (Phase.field index) (PrefixField.machine.m phase)))
    (source.var, extra) (StackMachineRegisters.withStackContents source.stk vector)
  simp only [FinTM2.step, embed, StackMachineRegisters.withStackConfig,
    StackMachineRegisters.config, atPhase, Option.map_some, id_eq, Turing.TM2.step]
  rw [parser_body arity index phase notTail notReject]
  change some (Turing.TM2.stepAux (parserBody arity index phase) (source.var, extra)
    (StackMachineRegisters.withStackContents (StackMachineRegisters.withStackContents source.stk vector) result)) = _
  rw [parserBody, third]
  rw [second, first]
  simp only [StackMachineRegisters.withStackConfig, StackMachineRegisters.config, Option.map_id]

theorem field_complete_empty (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some (.field index .complete)) state input [] post memo vector result) =
      some (config arity (some (.field index .checkTail)) (none, state.2) input [] post memo vector result) := by
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
  have lifted := parser_step arity index state.2 vector result
    (PrefixField.config (some .complete) state.1 input [] post memo) .complete rfl (by decide) (by decide)
  rw [original] at lifted
  simpa only [Option.map_some, embed_config] using lifted

theorem parser_scanning (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (vector result : List (Option Alphabet)) (source : PrefixField.machine.Cfg)
    (allowed : PrefixField.scanning source) :
    (machine arity).step (embed arity index extra vector result source) =
      (PrefixField.machine.step source).map (embed arity index extra vector result) := by
  rcases allowed with atHeader | atNumber | ⟨atComplete, _⟩
  · exact parser_step arity index extra vector result source .header atHeader (by decide) (by decide)
  · exact parser_step arity index extra vector result source .number atNumber (by decide) (by decide)
  · exact parser_step arity index extra vector result source .complete atComplete (by decide) (by decide)

noncomputable def fieldWalk (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime (machine arity).step
      (config arity (some (.field index .header)) (state, extra) (writeData value input) [] [] [] vector result)
      (some (config arity (some (.field index .complete)) (finalState value, extra) input []
        (postorderWire value).reverse (encodeData value).reverse vector result)) (scanCost value) := by
  have walked := PrefixField.walkInto (machine arity).step (embed arity index extra vector result)
    (steps := parser_scanning arity index extra vector result) value input [] [] [] state
  simpa only [embed_config, Option.map_some, List.append_nil] using walked

noncomputable def clearPostRun (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some (.clearPost index)) state input [] post memo vector result)
      (some (config arity (some (.restorePrefix index)) (none, state.2) input [] [] memo vector result))
      (post.length + 1) := by
  induction post generalizing state with
  | nil => exact Mettapedia.Computability.StackMachineComposition.oneStep (clear_post_nil arity index state input memo vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (clear_post_cons arity index state head input tail memo vector result)
      have rest := ih (some head, state.2)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def restorePrefixRun (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some (.restorePrefix index)) state input [] post memo vector result)
      (some (config arity (some (.copyWord index)) (none, state.2) input [] (memo.reverse ++ post) [] vector result))
      (memo.length + 1) := by
  induction memo generalizing state post with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (restore_prefix_nil arity index state input post vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (restore_prefix_cons arity index state head input post tail vector result)
      have rest := ih (some head, state.2) (head :: post)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def copyWordRun (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (input post : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some (.copyWord index)) state input [] post [] vector result)
      (some (config arity (some (.spine (advance index))) (none, state.2) input [] [] [] (none :: post.reverse.map some ++ vector) result))
      (post.length + 1) := by
  induction post generalizing state vector with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (copy_word_nil arity index state input vector result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (copy_word_cons arity index state head input tail vector result)
      have rest := ih (some head, state.2) (some head :: vector)
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def restoreVectorRun (arity : Nat) (state : State)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .restoreVector) state [] [] [] [] vector result)
      (some (config arity none (none, none) [] [] [] [] [] (some 1 :: vector.reverse ++ result)))
      (vector.length + 1) := by
  induction vector generalizing state result with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (restore_vector_nil arity state result)
  | cons head tail ih =>
      have begin := Mettapedia.Computability.StackMachineComposition.oneStep (restore_vector_cons arity state head tail result)
      have rest := ih (state.1, some head) (head :: result)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ begin rest

noncomputable def fieldRun (arity : Nat) (index : Fin (arity + 1)) (extra : Option (Option Alphabet))
    (value : Data) (input : List Alphabet) (vector result : List (Option Alphabet)) (state : Option Alphabet) :
    EvalsToInTime (machine arity).step
      (config arity (some (.field index .header)) (state, extra) (writeData value input) [] [] [] vector result)
      (some (config arity (some (.spine (advance index))) (none, extra) input [] [] []
        (none :: (encodeData value).reverse.map some ++ vector) result))
      (scanCost value + 3 * dataWeight value + 5) := by
  have walked := fieldWalk arity index extra value input vector result state
  have boundary := StackMachineComposition.oneStep (field_complete_empty arity index
    (finalState value, extra) input (postorderWire value).reverse (encodeData value).reverse vector result)
  have returned := StackMachineComposition.oneStep (field_return arity index (none, extra)
    input (postorderWire value).reverse (encodeData value).reverse vector result)
  have cleared := clearPostRun arity index (none, extra) input
    (postorderWire value).reverse (encodeData value).reverse vector result
  have restored := restorePrefixRun arity index (none, extra) input [] (encodeData value).reverse vector result
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have copied := copyWordRun arity index (none, extra) input (encodeData value) vector result
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

def spineCost (codec : Codec α) : List α → Nat
  | [] => 3
  | value :: rest => scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 6 + spineCost codec rest

noncomputable def spineRun (codec : Codec α) (values : List α) (arity : Nat) (index : Fin (arity + 1))
    (remaining : index.val + values.length = arity) (state : State)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some (.spine index)) state (encodeWith (Codec.list codec) values) [] [] [] vector result)
      (some (config arity (some .restoreVector) (none, state.2) [] [] [] []
        ((framedArguments codec values).reverse ++ vector) result)) (spineCost codec values) := by
  induction values generalizing index state vector with
  | nil =>
      have done : index.val = arity := by simpa using remaining
      have first := StackMachineComposition.oneStep (spine_nil arity index done state vector result)
      have second := StackMachineComposition.oneStep (nil_end arity (some 3, state.2) vector result)
      have third := StackMachineComposition.oneStep (check_end arity (some 2, state.2) vector result)
      have a := EvalsToInTime.trans _ 1 1 _ _ _ first second
      have nilWord : encodeWith (Codec.list codec) ([] : List α) = ([3,2] : List Alphabet) := rfl
      rw [nilWord]
      simpa [spineCost, framedArguments, argumentWords, Indexed.frame] using
        EvalsToInTime.trans _ (1 + 1) 1 _ _ _ a third
  | cons value rest ih =>
      have room : index.val < arity := by simp only [List.length_cons] at remaining; omega
      have next : (advance index).val + rest.length = arity := by
        rw [advance_value index room]
        simp only [List.length_cons] at remaining
        omega
      have first := StackMachineComposition.oneStep (spine_cons arity index room state
        (writeData (codec.put value) (encodeWith (Codec.list codec) rest)) vector result)
      have field := fieldRun arity index state.2 (codec.put value) (encodeWith (Codec.list codec) rest) vector result (some 4)
      have tail := ih (advance index) next (none, state.2)
        (none :: (encodeWith codec value).reverse.map some ++ vector)
      have a := EvalsToInTime.trans _ 1 (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5) _ _ _ first field
      have b := EvalsToInTime.trans _ (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5 + 1)
        (spineCost codec rest) _ _ _ a tail
      convert b using 1
      · rfl
      · simp only [framedArguments_cons, List.reverse_append, List.reverse_cons,
          List.map_reverse, List.append_assoc, List.singleton_append]
      · simp only [spineCost]
        omega

theorem init_eq (arity : Nat) (input : List Alphabet) :
    initList (machine arity) input = config arity (some (.spine ⟨0, by omega⟩)) (none, none) input [] [] [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key with
    | none => rfl
    | some key => cases key with
      | none => rfl
      | some key => cases key <;> rfl

theorem halt_eq (arity : Nat) (output : List (Option Alphabet)) :
    haltList (machine arity) output = config arity none (none, none) [] [] [] [] [] output := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp [resultKey]
  | some key => cases key with
    | none => simp [resultKey]
    | some key => cases key with
      | none => simp [resultKey]
      | some key => cases key <;> simp [resultKey]

noncomputable def outputs (codec : Codec α) (values : List α) (arity : Nat) (admitted : values.length = arity) :
    TM2OutputsInTime (machine arity) (encodeWith (Codec.list codec) values)
      (some (statusWire (some (framedArguments codec values))))
      (spineCost codec values + (framedArguments codec values).length + 1) := by
  have walked := spineRun codec values arity ⟨0, by omega⟩ (by simpa using admitted) (none, none) [] []
  simp only [List.append_nil] at walked
  have finished := restoreVectorRun arity (none, none) (framedArguments codec values).reverse []
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at finished
  have joined := EvalsToInTime.trans _ (spineCost codec values) ((framedArguments codec values).length + 1) _ _ _ walked finished
  change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
  rw [init_eq, halt_eq]
  simpa only [statusWire, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem spineCost_le (codec : Codec α) (values : List α) :
    spineCost codec values ≤ 6 * (encodeWith (Codec.list codec) values).length := by
  induction values with
  | nil => change (3 : Nat) ≤ 6 * 2; omega
  | cons value rest ih =>
      have scan := scanCost_le (codec.put value)
      have fieldSize : (encodeWith codec value).length = dataWeight (codec.put value) := by
        simp only [encodeWith, encodeData, writeData_length, List.length_nil, Nat.add_zero]
      have consSize : (encodeWith (Codec.list codec) (value :: rest)).length =
          1 + (encodeWith codec value).length + (encodeWith (Codec.list codec) rest).length := by
        change (encodeData (.pair (codec.put value) ((Codec.list codec).put rest))).length = _
        rw [encodeData_pair]
        simp only [List.length_cons, List.length_append]
        change (encodeWith codec value).length + (encodeWith (Codec.list codec) rest).length + 1 = _
        omega
      rw [consSize, fieldSize]
      simp only [spineCost]
      omega

/-- The bound counts parser transitions, all physical copies, delimiter
stores, status emission and complete scratch cleanup. -/
noncomputable def outputsPolynomial (codec : Codec α) (values : List α) (arity : Nat)
    (admitted : values.length = arity) :
    TM2OutputsInTime (machine arity) (encodeWith (Codec.list codec) values)
      (some (statusWire (some (framedArguments codec values))))
      (7 * (encodeWith (Codec.list codec) values).length + 1) := by
  have result := outputs codec values arity admitted
  have walkBound := spineCost_le codec values
  have frameSize := framedArguments_length codec values
  exact ⟨result.toEvalsTo, result.steps_le_m.trans (by omega)⟩

theorem reject_input_cons (arity : Nat) (state : State) (head : Alphabet) (tail : List Alphabet) (frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectInput) state (head :: tail) frames post memo vector result) =
      some (config arity (some .rejectInput) (some head, state.2) tail frames post memo vector result) := by framing_step

theorem reject_input_nil (arity : Nat) (state : State) (frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectInput) state [] frames post memo vector result) =
      some (config arity (some .rejectFrames) (none, state.2) [] frames post memo vector result) := by framing_step

theorem reject_frames_cons (arity : Nat) (state : State) (head : Alphabet) (tail : List Alphabet) (post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectFrames) state [] (head :: tail) post memo vector result) =
      some (config arity (some .rejectFrames) (some head, state.2) [] tail post memo vector result) := by framing_step

theorem reject_frames_nil (arity : Nat) (state : State) (post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectFrames) state [] [] post memo vector result) =
      some (config arity (some .rejectPost) (none, state.2) [] [] post memo vector result) := by framing_step

theorem reject_post_cons (arity : Nat) (state : State) (head : Alphabet) (tail : List Alphabet) (memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectPost) state [] [] (head :: tail) memo vector result) =
      some (config arity (some .rejectPost) (some head, state.2) [] [] tail memo vector result) := by framing_step

theorem reject_post_nil (arity : Nat) (state : State) (memo : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectPost) state [] [] [] memo vector result) =
      some (config arity (some .rejectPrefix) (none, state.2) [] [] [] memo vector result) := by framing_step

theorem reject_prefix_cons (arity : Nat) (state : State) (head : Alphabet) (tail : List Alphabet) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectPrefix) state [] [] [] (head :: tail) vector result) =
      some (config arity (some .rejectPrefix) (some head, state.2) [] [] [] tail vector result) := by framing_step

theorem reject_prefix_nil (arity : Nat) (state : State) (vector result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectPrefix) state [] [] [] [] vector result) =
      some (config arity (some .rejectVector) (none, state.2) [] [] [] [] vector result) := by framing_step

theorem reject_vector_cons (arity : Nat) (state : State) (head : Option Alphabet) (tail : List (Option Alphabet)) (result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectVector) state [] [] [] [] (head :: tail) result) =
      some (config arity (some .rejectVector) (state.1, some head) [] [] [] [] tail result) := by framing_step

theorem reject_vector_nil (arity : Nat) (state : State) (result : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectVector) state [] [] [] [] [] result) =
      some (config arity (some .rejectResult) (state.1, none) [] [] [] [] [] result) := by framing_step

theorem reject_result_cons (arity : Nat) (state : State) (head : Option Alphabet) (tail : List (Option Alphabet)) :
    (machine arity).step (config arity (some .rejectResult) state [] [] [] [] [] (head :: tail)) =
      some (config arity (some .rejectResult) (state.1, some head) [] [] [] [] [] tail) := by framing_step

theorem reject_result_nil (arity : Nat) (state : State) :
    (machine arity).step (config arity (some .rejectResult) state [] [] [] [] [] []) =
      some (config arity none (none, none) [] [] [] [] [] [some 0]) := by framing_step

noncomputable def rejectResultRun (arity : Nat) (state : State) (result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectResult) state [] [] [] [] [] result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (result.length + 1) := by
  induction result generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (reject_result_nil arity state )
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_result_cons arity state head tail )
      have rest := ih (state.1, some head)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def rejectVectorRun (arity : Nat) (state : State) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectVector) state [] [] [] [] vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (vector.length + result.length + 2) := by
  induction vector generalizing state with
  | nil =>
      have first := StackMachineComposition.oneStep (reject_vector_nil arity state result)
      have rest := rejectResultRun arity (state.1, none) result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (result.length + 1) _ _ _ first rest
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_vector_cons arity state head tail result)
      have rest := ih (state.1, some head)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + result.length + 2) _ _ _ first rest

noncomputable def rejectPrefixRun (arity : Nat) (state : State) (memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectPrefix) state [] [] [] memo vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (memo.length + vector.length + result.length + 3) := by
  induction memo generalizing state with
  | nil =>
      have first := StackMachineComposition.oneStep (reject_prefix_nil arity state vector result)
      have rest := rejectVectorRun arity (none, state.2) vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (vector.length + result.length + 2) _ _ _ first rest
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_prefix_cons arity state head tail vector result)
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + vector.length + result.length + 3) _ _ _ first rest

noncomputable def rejectPostRun (arity : Nat) (state : State) (post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectPost) state [] [] post memo vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (post.length + memo.length + vector.length + result.length + 4) := by
  induction post generalizing state with
  | nil =>
      have first := StackMachineComposition.oneStep (reject_post_nil arity state memo vector result)
      have rest := rejectPrefixRun arity (none, state.2) memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (memo.length + vector.length + result.length + 3) _ _ _ first rest
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_post_cons arity state head tail memo vector result)
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + memo.length + vector.length + result.length + 4) _ _ _ first rest

noncomputable def rejectFramesRun (arity : Nat) (state : State) (frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectFrames) state [] frames post memo vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (frames.length + post.length + memo.length + vector.length + result.length + 5) := by
  induction frames generalizing state with
  | nil =>
      have first := StackMachineComposition.oneStep (reject_frames_nil arity state post memo vector result)
      have rest := rejectPostRun arity (none, state.2) post memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (post.length + memo.length + vector.length + result.length + 4) _ _ _ first rest
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_frames_cons arity state head tail post memo vector result)
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + post.length + memo.length + vector.length + result.length + 5) _ _ _ first rest

noncomputable def rejectInputRun (arity : Nat) (state : State) (input frames post memo : List Alphabet) (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some .rejectInput) state input frames post memo vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0])) (input.length + frames.length + post.length + memo.length + vector.length + result.length + 6) := by
  induction input generalizing state with
  | nil =>
      have first := StackMachineComposition.oneStep (reject_input_nil arity state frames post memo vector result)
      have rest := rejectFramesRun arity (none, state.2) frames post memo vector result
      simpa only [List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (frames.length + post.length + memo.length + vector.length + result.length + 5) _ _ _ first rest
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (reject_input_cons arity state head tail frames post memo vector result)
      have rest := ih (some head, state.2)
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + frames.length + post.length + memo.length + vector.length + result.length + 6) _ _ _ first rest

theorem spine_refuses (arity : Nat) (index : Fin (arity + 1)) (state : State)
    (head : Alphabet) (input : List Alphabet) (vector result : List (Option Alphabet))
    (invalid : if index.val < arity then head ≠ 4 else head ≠ 3) :
    (machine arity).step (config arity (some (.spine index)) state (head :: input) [] [] [] vector result) =
      some (config arity (some .rejectInput) (some head, state.2) input [] [] [] vector result) := by
  by_cases room : index.val < arity
  all_goals simp only [room, if_true, if_false] at invalid
  all_goals
    have comparison : (head == (if index.val < arity then (4 : Alphabet) else 3)) = false := by
      simp only [room, if_true, if_false]
      exact beq_false_of_ne invalid
    simp only [room, if_true, if_false] at comparison
    simp [FinTM2.step, machine, config, inputKey, TM2.step, TM2.stepAux, room, comparison]
  all_goals
    funext key
    cases key with
    | none => simp [Function.update]
    | some key => cases key with
      | none => simp [Function.update]
      | some key => cases key with
        | none => simp [Function.update]
        | some key => cases key <;> simp [Function.update] <;> (intro impossible; cases impossible)

theorem encoded_cons_size (codec : Codec α) (value : α) (rest : List α) :
    (encodeWith (Codec.list codec) (value :: rest)).length =
      1 + dataWeight (codec.put value) + (encodeWith (Codec.list codec) rest).length := by
  change (encodeData (.pair (codec.put value) ((Codec.list codec).put rest))).length = _
  rw [encodeData_pair]
  simp only [List.length_cons, List.length_append, encodeData, writeData_length, List.length_nil, Nat.add_zero]
  rw [show (encodeWith (Codec.list codec) rest).length = dataWeight ((Codec.list codec).put rest) from by
    simp only [encodeWith, encodeData, writeData_length, List.length_nil, Nat.add_zero]]
  omega

noncomputable def mismatchRun (codec : Codec α) (values : List α) (arity : Nat)
    (index : Fin (arity + 1)) (wrong : index.val + values.length ≠ arity) (state : State)
    (vector result : List (Option Alphabet)) :
    EvalsToInTime (machine arity).step
      (config arity (some (.spine index)) state (encodeWith (Codec.list codec) values) [] [] [] vector result)
      (some (config arity none (none, none) [] [] [] [] [] [some 0]))
      (spineCost codec values + (encodeWith (Codec.list codec) values).length + vector.length + result.length + 8) := by
  induction values generalizing index state vector with
  | nil =>
      have room : index.val < arity := by simp only [List.length_nil, Nat.add_zero] at wrong; have := index.isLt; omega
      have first := StackMachineComposition.oneStep (spine_refuses arity index state 3 [2] vector result (by simp [room]))
      have rest := rejectInputRun arity (some 3, state.2) [2] [] [] [] vector result
      have joined := EvalsToInTime.trans _ 1 (1 + 0 + 0 + 0 + vector.length + result.length + 6) _ _ _ first rest
      change EvalsToInTime _ (config arity (some (.spine index)) state [3,2] [] [] [] vector result) _ _
      exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by change _ ≤ 3 + 2 + vector.length + result.length + 8; omega)⟩
  | cons value rest ih =>
      by_cases room : index.val < arity
      · have nextWrong : (advance index).val + rest.length ≠ arity := by
          rw [advance_value index room]
          simp only [List.length_cons] at wrong
          omega
        have first := StackMachineComposition.oneStep (spine_cons arity index room state
          (writeData (codec.put value) (encodeWith (Codec.list codec) rest)) vector result)
        have field := fieldRun arity index state.2 (codec.put value) (encodeWith (Codec.list codec) rest) vector result (some 4)
        have tail := ih (advance index) nextWrong (none, state.2)
          (none :: (encodeWith codec value).reverse.map some ++ vector)
        have a := EvalsToInTime.trans _ 1 (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5) _ _ _ first field
        have b := EvalsToInTime.trans _ (scanCost (codec.put value) + 3 * dataWeight (codec.put value) + 5 + 1)
          (spineCost codec rest + (encodeWith (Codec.list codec) rest).length +
            (none :: (encodeWith codec value).reverse.map some ++ vector).length + result.length + 8) _ _ _ a tail
        convert b using 1
        · rfl
        · rw [encoded_cons_size]
          simp only [spineCost, List.length_append, List.length_cons, List.length_map, List.length_reverse,
            encodeWith, encodeData, writeData_length, List.length_nil, Nat.add_zero]
          omega
      · have first := StackMachineComposition.oneStep (spine_refuses arity index state 4
          (writeData (codec.put value) (encodeWith (Codec.list codec) rest)) vector result (by simp [room]))
        have tail := rejectInputRun arity (some 4, state.2)
          (writeData (codec.put value) (encodeWith (Codec.list codec) rest)) [] [] [] vector result
        have joined := EvalsToInTime.trans _ 1
          ((writeData (codec.put value) (encodeWith (Codec.list codec) rest)).length + 0 + 0 + 0 + vector.length + result.length + 6)
          _ _ _ first tail
        change EvalsToInTime _ (config arity (some (.spine index)) state
          (4 :: writeData (codec.put value) (encodeWith (Codec.list codec) rest)) [] [] [] vector result) _ _
        exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by
          simp only [spineCost, encodeWith, Codec.list, Codec.putList, encodeData, writeData,
            List.length_cons, writeData_length]
          omega)⟩

/-- Total arity admission on the original source list, without introducing a
second element decoder or changing the source field authority. -/
def frameAtArity (codec : Codec α) (arity : Nat) (values : List α) : Option (List (Option Alphabet)) :=
  if values.length = arity then some (framedArguments codec values) else none

noncomputable def outputsAtArity (codec : Codec α) (arity : Nat) (values : List α) :
    TM2OutputsInTime (machine arity) (encodeWith (Codec.list codec) values)
      (some (statusWire (frameAtArity codec arity values)))
      (7 * (encodeWith (Codec.list codec) values).length + 8) := by
  by_cases admitted : values.length = arity
  · rw [frameAtArity, if_pos admitted]
    have result := outputsPolynomial codec values arity admitted
    exact ⟨result.toEvalsTo, result.steps_le_m.trans (by omega)⟩
  · rw [frameAtArity, if_neg admitted]
    have wrong : (0 : Nat) + values.length ≠ arity := by simpa using admitted
    have result := mismatchRun codec values arity ⟨0, by omega⟩ wrong (none, none) [] []
    change EvalsToInTime _ (initList _ _) (some (haltList _ _)) _
    rw [init_eq, halt_eq]
    change EvalsToInTime _ _ (some (config arity none (none, none) [] [] [] [] [] [some 0])) _
    have cost := spineCost_le codec values
    exact ⟨result.toEvalsTo, result.steps_le_m.trans (by simp only [List.length_nil] at *; omega)⟩

/-- The actual finite machine returns success or refusal for every original
encoded source list. Its time polynomial is in the complete physical packet. -/
noncomputable def totalRealization (codec : Codec α) (arity : Nat) :
    TM2ComputableInPolyTime (encodeWith (Codec.list codec)) statusWire (frameAtArity codec arity) where
  tm := machine arity
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C 7 * X + C 8
  outputsFun values := by
    change TM2OutputsInTime (machine arity) ((encodeWith (Codec.list codec) values).map id)
      (some ((statusWire (frameAtArity codec arity values)).map id)) _
    simpa only [List.map_id, eval_add, eval_mul, eval_C, eval_X] using outputsAtArity codec arity values

theorem result_length_le (codec : Codec α) (arity : Nat) (values : List α) :
    (statusWire (frameAtArity codec arity values)).length ≤ (encodeWith (Codec.list codec) values).length := by
  by_cases admitted : values.length = arity
  · rw [frameAtArity, if_pos admitted]
    exact status_length_le codec values
  · rw [frameAtArity, if_neg admitted]
    have size := encoded_list_length codec values
    change 1 ≤ (encodeWith (Codec.list codec) values).length
    omega


/-- The output tag preserves the difference between refusal and an empty
successful word. It describes word transport, not a new term checker. -/
def resultWire : Option (List Alphabet) → List Alphabet
  | none => [0]
  | some word => 1 :: word

/-- A fixed indexed template operates on every supplied framed word. The
framing machine separately earns the source list's authored arity. -/
noncomputable def templateRealization {arity : Nat} (template : Indexed.Template Alphabet arity) :
    TM2ComputableInPolyTime (fun word : List (Option Alphabet) => word) resultWire
      (fun word => some (Indexed.instantiateWire template word)) where
  tm := Indexed.machine (.inl 1 :: template)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := C (4 * ((.inl 1 :: template).length + 1)) * (X + C 1)
  outputsFun word := by
    change TM2OutputsInTime (Indexed.machine (.inl 1 :: template)) (word.map id)
      (some ((resultWire (some (Indexed.instantiateWire template word))).map id)) _
    simp only [List.map_id_fun]
    simpa only [resultWire, Indexed.instantiateWire_literal, id_eq,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using
      Indexed.outputsWire (.inl 1 :: template) word

/-- The original list is framed, its status consumed, and the indexed copier
executes only on admitted input. Both programs and the physical handoff occur
in the same finite-stack machine. Missing or excess arguments return refusal. -/
noncomputable def framedRealization (codec : Codec α) (arity : Nat)
    (template : Indexed.Template Alphabet arity) :
    TM2ComputableInPolyTime (encodeWith (Codec.list codec)) resultWire
      (fun values => (frameAtArity codec arity values).map (Indexed.instantiateWire template)) := by
  let dispatched := ProofSystems.ExecutedDispatch.realization
    (templateRealization template) (some 1) (some 0) (by decide) none
  have sameEncoding : ProofSystems.ExecutedDispatch.inputEncoding
      (fun word : List (Option Alphabet) => word) (some 1) (some 0) = statusWire := by
    funext result
    cases result <;> rfl
  rw [sameEncoding] at dispatched
  have composed := ProofSystems.ExecutedComposition.realization
    (totalRealization codec arity) dispatched X
    (by intro values; simpa only [Polynomial.eval_X] using result_length_le codec arity values)
  have sameOperation :
      (fun values => (frameAtArity codec arity values).elim none
        (fun word => some (Indexed.instantiateWire template word))) =
      (fun values => (frameAtArity codec arity values).map (Indexed.instantiateWire template)) := by
    funext values
    cases frameAtArity codec arity values <;> rfl
  change TM2ComputableInPolyTime (encodeWith (Codec.list codec)) resultWire
    (fun values => (frameAtArity codec arity values).elim none
      (fun word => some (Indexed.instantiateWire template word))) at composed
  rw [sameOperation] at composed
  exact composed

attribute [local implicit_reducible] Indexed.machine Indexed.Alphabet machine

/-- The executable composition uses only the original framing and indexed
copier programs. Intermediate status and payload symbols remain on stacks. -/
def framedMachine (arity : Nat) (template : Indexed.Template Alphabet arity) : FinTM2 := by
  letI : Fintype ((machine arity).Γ (machine arity).k₁) := by
    change Fintype (Option Alphabet)
    infer_instance
  letI : Inhabited ((machine arity).Γ (machine arity).k₁) := by
    change Inhabited (Option Alphabet)
    infer_instance
  exact Mettapedia.Computability.StackMachineComposition.machine (machine arity)
    (Mettapedia.Computability.StackMachineComposition.Dispatch.machine
      (Indexed.machine (.inl 1 :: template)) (fun tag : Option Alphabet => decide (tag = some (1 : Alphabet))) [(0 : Alphabet)])
    (Equiv.refl (Option Alphabet))

/-- The execution witness describes the concrete executable composition,
including refusal paths on the entire original source domain. -/
noncomputable def framedOutputs (codec : Codec α) (arity : Nat)
    (template : Indexed.Template Alphabet arity) (values : List α) :
    TM2OutputsInTime (framedMachine arity template) (encodeWith (Codec.list codec) values)
      (some (resultWire ((frameAtArity codec arity values).map (Indexed.instantiateWire template))))
      ((4 * (template.length + 2) + 10) * (encodeWith (Codec.list codec) values).length +
        4 * (template.length + 2) + 12) := by
  let inner := Indexed.machine (.inl 1 :: template)
  let accept : inner.Γ inner.k₀ → Bool :=
    fun tag => decide ((show Option Alphabet from tag) = some 1)
  let framed := frameAtArity codec arity values
  let middle := statusWire framed
  have later : TM2OutputsInTime
      (Mettapedia.Computability.StackMachineComposition.Dispatch.machine inner accept [(0 : Alphabet)])
      middle (some (resultWire (framed.map (Indexed.instantiateWire template))))
      (4 * (template.length + 2) * (middle.length + 1) + middle.length + 2) := by
    dsimp only [middle]
    cases result : framed with
    | none =>
        simp only [statusWire, Option.map_none, resultWire]
        have failed := Mettapedia.Computability.StackMachineComposition.Dispatch.outputs_refused
          inner accept [(0 : Alphabet)] (some 0) [] (by decide)
        change EvalsToInTime _ _ _ _
        refine ⟨failed.toEvalsTo, failed.steps_le_m.trans ?_⟩
        simp only [List.length_cons, List.length_nil]
        omega
    | some word =>
        simp only [statusWire, Option.map_some, resultWire]
        have copied := Indexed.outputsWire (.inl 1 :: template) word
        have successful := Mettapedia.Computability.StackMachineComposition.Dispatch.outputs_success
          inner accept [(0 : Alphabet)] (some 1) word
          ((1 : Alphabet) :: Indexed.instantiateWire template word)
          (4 * (template.length + 2) * (word.length + 1)) (by decide)
          (by simpa only [Indexed.instantiateWire_literal, List.length_cons] using copied)
        change EvalsToInTime _ _ _ _
        refine ⟨successful.toEvalsTo, successful.steps_le_m.trans ?_⟩
        simp only [List.length_cons]
        nlinarith
  have first := outputsAtArity codec arity values
  letI : Fintype ((machine arity).Γ (machine arity).k₁) := by
    change Fintype (Option Alphabet)
    infer_instance
  letI : Inhabited ((machine arity).Γ (machine arity).k₁) := by
    change Inhabited (Option Alphabet)
    infer_instance
  let dispatched := Mettapedia.Computability.StackMachineComposition.Dispatch.machine
    inner accept [(0 : Alphabet)]
  let bridge : (machine arity).Γ (machine arity).k₁ ≃ dispatched.Γ dispatched.k₀ :=
    Equiv.refl (Option Alphabet)
  have transported : TM2OutputsInTime dispatched (middle.map bridge)
      (some (resultWire (framed.map (Indexed.instantiateWire template))))
      (4 * (template.length + 2) * (middle.length + 1) + middle.length + 2) := by
    have unchanged : middle.map bridge = middle := List.map_id middle
    rw [unchanged]
    exact later
  have joined := Mettapedia.Computability.StackMachineComposition.outputs
    (machine arity) dispatched bridge (encodeWith (Codec.list codec) values) middle
    (resultWire (framed.map (Indexed.instantiateWire template)))
    (7 * (encodeWith (Codec.list codec) values).length + 8)
    (4 * (template.length + 2) * (middle.length + 1) + middle.length + 2) first transported
  change EvalsToInTime _ _ _ _
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  have bounded : middle.length ≤ (encodeWith (Codec.list codec) values).length :=
    result_length_le codec arity values
  nlinarith

/-- Source order and all duplicate argument fields are retained when a valid
list feeds the indexed template. The target is the independent template
interpretation on the complete original codec words. -/
theorem instantiate_framed (codec : Codec α) (arity : Nat)
    (template : Indexed.Template Alphabet arity) (values : List α)
    (admitted : values.length = arity) :
    Indexed.instantiateWire template (framedArguments codec values) =
      Indexed.instantiate template (fun index =>
        encodeWith codec (values[index.val]'(by omega))) := by
  unfold Indexed.instantiateWire
  congr 1
  funext index
  have field := Indexed.select_frame index ⟨0, by omega⟩ (argumentWords codec values)
    (by simp only [argumentWords, List.length_map]; omega)
  have bound : index.val < values.length := by omega
  simpa only [framedArguments, Nat.zero_le, if_pos, Nat.sub_zero, argumentWords,
    List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some, Option.getD_some] using field

/-- The total executed word operation agrees with original source arity
admission; admission never follows from a caller-supplied success tag. -/
theorem framed_correct (codec : Codec α) (arity : Nat)
    (template : Indexed.Template Alphabet arity) (values : List α)
    (admitted : values.length = arity) :
    (frameAtArity codec arity values).map (Indexed.instantiateWire template) =
      some (Indexed.instantiate template (fun index =>
        encodeWith codec (values[index.val]'(by omega)))) := by
  rw [frameAtArity, if_pos admitted, Option.map_some,
    instantiate_framed codec arity template values admitted]

theorem framed_refuses (codec : Codec α) (arity : Nat)
    (template : Indexed.Template Alphabet arity) (values : List α)
    (wrongArity : values.length ≠ arity) :
    (frameAtArity codec arity values).map (Indexed.instantiateWire template) = none := by
  simp only [frameAtArity, if_neg wrongArity, Option.map_none]

end Execution

namespace Controls

theorem empty_success_has_status :
    statusWire (some (framedArguments Codec.nat [])) = [some 1] := rfl

theorem empty_refusal_distinct :
    statusWire (some (framedArguments Codec.nat [])) ≠ statusWire none := by decide

theorem missing_status_refused : readStatus [] = none := rfl

theorem refusal_with_body_refused : readStatus [some 0, none] = none := rfl

end Controls

namespace ListAssembly

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability
open Mettapedia.Computability.WordTemplateMachine
open _root_.Computability Turing StateTransition Polynomial
open Turing.TM2.Stmt

/-- Original list pair markers and nil, with every field retained verbatim. -/
def wire (words : List (List Alphabet)) : List Alphabet :=
  words.flatMap (fun word => 4 :: word) ++ [3, 2]

theorem wire_nil : wire [] = [3, 2] := rfl

theorem wire_cons (word : List Alphabet) (rest : List (List Alphabet)) :
    wire (word :: rest) = 4 :: word ++ wire rest := by
  simp only [wire, List.flatMap_cons, List.cons_append, List.append_assoc]

theorem wire_length (words : List (List Alphabet)) :
    (wire words).length = (Indexed.frame words).length + 2 := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    rw [wire_cons]
    change (4 :: word ++ wire rest).length =
      ((word.map some ++ [none]) ++ Indexed.frame rest).length + 2
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] at *
    omega

/-- This assembler changes list framing, not the codec or meaning of fields. -/
theorem wire_codec {α : Type} (codec : Codec α) (values : List α) :
    wire (values.map (encodeWith codec)) = encodeWith (Codec.list codec) values := by
  rw [encodeWith_list]
  simp only [wire, List.flatMap_map]
  rfl

inductive Stack where
  | input | temporary | result
  deriving DecidableEq, Fintype
inductive Phase where
  | start | copy | reverse | rejectTemporary
  deriving DecidableEq, Fintype
abbrev Cells : Stack → Type
  | .input => Option Alphabet
  | .temporary | .result => Alphabet
abbrev State := Option (Option Alphabet)

def program : Phase → TM2.Stmt Cells Phase State
  | .start => peek .input (fun _ value => value)
      (branch Option.isSome
        (push .temporary (fun _ => 4) (goto fun _ => .copy))
        (push .temporary (fun _ => 3)
          (push .temporary (fun _ => 2) (goto fun _ => .reverse))))
  | .copy => pop .input (fun _ value => value)
      (branch Option.isSome
        (branch (fun state => (state.getD none).isSome)
          (push .temporary (fun state => (state.getD none).getD 0) (goto fun _ => .copy))
          (goto fun _ => .start))
        (goto fun _ => .rejectTemporary))
  | .reverse => pop .temporary (fun _ value => value.map some)
      (branch Option.isSome
        (push .result (fun state => (state.getD none).getD 0) (goto fun _ => .reverse))
        (push .result (fun _ => 1) (load (fun _ => none) halt)))
  | .rejectTemporary => pop .temporary (fun _ value => value.map some)
      (branch Option.isSome (goto fun _ => .rejectTemporary)
        (push .result (fun _ => 0) (load (fun _ => none) halt)))

@[implicit_reducible] def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Λ := Phase
  main := .start
  σ := State
  initialState := none
  m := program

def config (phase : Option Phase) (state : State) (input : List (Option Alphabet))
    (temporary result : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk key := match key with
    | .input => input | .temporary => temporary | .result => result

local macro "assembly_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, TM2.step, TM2.stepAux, Function.update]
  all_goals first | rfl | (congr 2; funext key; cases key <;> simp [Function.update])))

theorem start_cons (head : Option Alphabet) (rest : List (Option Alphabet))
    (temporary result : List Alphabet) (state : State) :
    machine.step (config (some .start) state (head :: rest) temporary result) =
      some (config (some .copy) (some head) (head :: rest) (4 :: temporary) result) := by assembly_step

theorem start_nil (temporary result : List Alphabet) (state : State) :
    machine.step (config (some .start) state [] temporary result) =
      some (config (some .reverse) none [] (2 :: 3 :: temporary) result) := by assembly_step

theorem copy_cons (head : Alphabet) (rest : List (Option Alphabet))
    (temporary result : List Alphabet) (state : State) :
    machine.step (config (some .copy) state (some head :: rest) temporary result) =
      some (config (some .copy) (some (some head)) rest (head :: temporary) result) := by assembly_step

theorem copy_delimiter (rest : List (Option Alphabet)) (temporary result : List Alphabet) (state : State) :
    machine.step (config (some .copy) state (none :: rest) temporary result) =
      some (config (some .start) (some none) rest temporary result) := by assembly_step

theorem copy_nil (temporary result : List Alphabet) (state : State) :
    machine.step (config (some .copy) state [] temporary result) =
      some (config (some .rejectTemporary) none [] temporary result) := by assembly_step

theorem reverse_cons (head : Alphabet) (rest result : List Alphabet) (state : State) :
    machine.step (config (some .reverse) state [] (head :: rest) result) =
      some (config (some .reverse) (some (some head)) [] rest (head :: result)) := by assembly_step

theorem reverse_nil (result : List Alphabet) (state : State) :
    machine.step (config (some .reverse) state [] [] result) =
      some (config none none [] [] (1 :: result)) := by assembly_step

theorem reject_cons (head : Alphabet) (rest result : List Alphabet) (state : State) :
    machine.step (config (some .rejectTemporary) state [] (head :: rest) result) =
      some (config (some .rejectTemporary) (some (some head)) [] rest result) := by assembly_step

theorem reject_nil (result : List Alphabet) (state : State) :
    machine.step (config (some .rejectTemporary) state [] [] result) =
      some (config none none [] [] (0 :: result)) := by assembly_step

def reverse_run (temporary result : List Alphabet) (state : State) :
    EvalsToInTime machine.step (config (some .reverse) state [] temporary result)
      (some (config none none [] [] (1 :: temporary.reverse ++ result))) (temporary.length + 1) := by
  induction temporary generalizing result state with
  | nil => simpa using StackMachineComposition.oneStep (reverse_nil result state)
  | cons head rest ih =>
    have first := StackMachineComposition.oneStep (reverse_cons head rest result state)
    have later := ih (head :: result) (some (some head))
    simpa [List.append_assoc] using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def copy_run (word : List Alphabet) (rest : List (Option Alphabet))
    (temporary result : List Alphabet) (state : State) :
    EvalsToInTime machine.step
      (config (some .copy) state (word.map some ++ none :: rest) temporary result)
      (some (config (some .start) (some none) rest (word.reverse ++ temporary) result))
      (word.length + 1) := by
  induction word generalizing temporary state with
  | nil => simpa using StackMachineComposition.oneStep (copy_delimiter rest temporary result state)
  | cons head word ih =>
    have first := StackMachineComposition.oneStep
      (copy_cons head (word.map some ++ none :: rest) temporary result state)
    have later := ih (head :: temporary) (some (some head))
    simpa [List.append_assoc] using EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first later

/-- Every delimiter and payload cell is consumed, and every original output
cell is charged again when restoring physical order. -/
def start_run (words : List (List Alphabet)) (temporary result : List Alphabet) (state : State) :
    EvalsToInTime machine.step
      (config (some .start) state (Indexed.frame words) temporary result)
      (some (config none none [] [] (1 :: temporary.reverse ++ wire words ++ result)))
      (2 * (Indexed.frame words).length + words.length + temporary.length + 4) := by
  induction words generalizing temporary state with
  | nil =>
    have first := StackMachineComposition.oneStep (start_nil temporary result state)
    have later := reverse_run (2 :: 3 :: temporary) result none
    simpa [wire, Indexed.frame, List.append_assoc] using
      EvalsToInTime.trans _ 1 ((2 :: 3 :: temporary).length + 1) _ _ _ first later
  | cons word rest ih =>
    let head := (word.map some ++ [none]).head?.getD none
    let tail := (word.map some ++ [none]).tail
    have framed : word.map some ++ [none] = head :: tail := by
      cases word <;> rfl
    have first := StackMachineComposition.oneStep
      (start_cons head (tail ++ Indexed.frame rest) temporary result state)
    have copied := copy_run word (Indexed.frame rest) (4 :: temporary) result (some head)
    have continued := ih (word.reverse ++ 4 :: temporary) (some none)
    have packetEq : head :: (tail ++ Indexed.frame rest) =
        word.map some ++ none :: Indexed.frame rest := by
      rw [← List.cons_append, ← framed, List.append_assoc]
      rfl
    rw [packetEq] at first
    have initial := EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first copied
    have joined := EvalsToInTime.trans _ ((word.length + 1) + 1)
      (2 * (Indexed.frame rest).length + rest.length + (word.reverse ++ 4 :: temporary).length + 4)
      _ _ _ initial continued
    have arithmetic :
        (2 * (Indexed.frame rest).length + rest.length + (word.reverse ++ 4 :: temporary).length + 4) +
          ((word.length + 1) + 1) =
        2 * (Indexed.frame (word :: rest)).length + (word :: rest).length + temporary.length + 4 := by
      simp only [List.length_append, List.length_reverse, List.length_cons,
        Indexed.frame_length, List.map_cons, List.sum_cons]
      omega
    rw [arithmetic] at joined
    simpa [Indexed.frame, wire_cons, List.append_assoc] using joined

def reject_run (temporary result : List Alphabet) (state : State) :
    EvalsToInTime machine.step (config (some .rejectTemporary) state [] temporary result)
      (some (config none none [] [] (0 :: result))) (temporary.length + 1) := by
  induction temporary generalizing state with
  | nil => simpa using StackMachineComposition.oneStep (reject_nil result state)
  | cons head rest ih =>
    have first := StackMachineComposition.oneStep (reject_cons head rest result state)
    have later := ih (some (some head))
    simpa using EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def copy_unterminated (word : List Alphabet) (temporary result : List Alphabet) (state : State) :
    EvalsToInTime machine.step
      (config (some .copy) state (word.map some) temporary result)
      (some (config (some .rejectTemporary) none [] (word.reverse ++ temporary) result))
      (word.length + 1) := by
  induction word generalizing temporary state with
  | nil => simpa using StackMachineComposition.oneStep (copy_nil temporary result state)
  | cons head word ih =>
    have first := StackMachineComposition.oneStep (copy_cons head (word.map some) temporary result state)
    have later := ih (head :: temporary) (some (some head))
    simpa [List.append_assoc] using EvalsToInTime.trans _ 1 (word.length + 1) _ _ _ first later

/-- A field without its final framing separator is refused, with all copied
cells discarded. Refusal cannot masquerade as successful empty output. -/
def start_unterminated (word : List Alphabet) (nonempty : word ≠ []) :
    EvalsToInTime machine.step (config (some .start) none (word.map some) [] [])
      (some (config none none [] [] [0])) (2 * word.length + 4) := by
  cases word with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    have first := StackMachineComposition.oneStep (start_cons (some head) (tail.map some) [] [] none)
    have copied := copy_unterminated (head :: tail) [4] [] (some (some head))
    have front := EvalsToInTime.trans _ 1 ((head :: tail).length + 1) _ _ _ first copied
    have cleaned := reject_run ((head :: tail).reverse ++ [4]) [] none
    have joined := EvalsToInTime.trans _ (((head :: tail).length + 1) + 1)
      (((head :: tail).reverse ++ [4]).length + 1) _ _ _ front cleaned
    have budgetEq : (((head :: tail).reverse ++ [4]).length + 1) +
        (((head :: tail).length + 1) + 1) = 2 * (head :: tail).length + 4 := by
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
      omega
    rw [budgetEq] at joined
    simpa using joined

private theorem init_eq (input : List (Option Alphabet)) :
    initList machine input = config (some .start) none input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key <;> simp

private theorem halt_eq (result : List Alphabet) :
    haltList machine result = config none none [] [] result := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key <;> simp

/-- The concrete assembler realizes the original binary list writer on every
framed vector, in linear time including final ordering and the status marker. -/
def outputs (words : List (List Alphabet)) :
    TM2OutputsInTime machine (Indexed.frame words) (some ((1 : Alphabet) :: wire words))
      (3 * (Indexed.frame words).length + 4) := by
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  have ran := start_run words [] [] none
  have count : words.length ≤ (Indexed.frame words).length := by
    rw [Indexed.frame_length]
    omega
  have bounded : 2 * (Indexed.frame words).length + words.length + ([] : List Alphabet).length + 4 ≤
      3 * (Indexed.frame words).length + 4 := by
    simp only [List.length_nil]
    omega
  have completed : EvalsToInTime machine.step
      (config (some .start) none (Indexed.frame words) [] [])
      (some (config none none [] [] (1 :: [].reverse ++ wire words ++ [])))
      (3 * (Indexed.frame words).length + 4) :=
    ⟨ran.toEvalsTo, ran.steps_le_m.trans bounded⟩
  simpa using completed

def unterminatedOutputs (word : List Alphabet) (nonempty : word ≠ []) :
    TM2OutputsInTime machine (word.map some) (some [(0 : Alphabet)]) (2 * word.length + 4) := by
  change EvalsToInTime _ (initList machine _) (some (haltList machine _)) _
  rw [init_eq, halt_eq]
  exact start_unterminated word nonempty

/-- A realization for any original codec charges its complete encoded fields.
Codec validation remains the responsibility of that same original codec. -/
noncomputable def realization {α : Type} (codec : Codec α) :
    TM2ComputableInPolyTime (framedArguments codec)
      (fun values : List α => 1 :: encodeWith (Codec.list codec) values) id where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C 3 * X + C 4
  outputsFun values := by
    change TM2OutputsInTime machine ((framedArguments codec values).map id)
      (some ((1 :: encodeWith (Codec.list codec) values).map id)) _
    simp only [List.map_id_fun]
    rw [← wire_codec]
    simpa only [framedArguments, argumentWords, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, id] using outputs (values.map (encodeWith codec))

end ListAssembly

end Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming

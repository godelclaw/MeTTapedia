import Mettapedia.Computability.StackMachineRegisters
import Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding

/-!
# Finite traversal of certificate data frames

The machine reads the original prefix certificate encoding and emits postorder
frame events. Atom payloads retain their original binary fields; pairs close
after their first and second children, preserving authored order. Existing
codecs interpret the same original `Data` and proof carriers. Prefix capture
and product selection preserve the original field bytes for later compiler
stages; both fields are scanned before a selection is returned.
-/
set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.CertificateDataTraversal
open _root_.Computability Turing StateTransition Polynomial
open ProofSystems
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.Binding.WireCodec
open Turing.TM2.Stmt

/-- Postorder wire traversal of the original generic data carrier. -/
def postorderWire : Data → List Alphabet
  | .atom value => 3 :: natural value
  | .pair first second => postorderWire first ++ postorderWire second ++ [4]

def nodeCount : Data → Nat
  | .atom _ => 1
  | .pair first second => nodeCount first + nodeCount second + 1

/-- Header, binary-field and pair-continuation transitions. -/
def scanCost : Data → Nat
  | .atom value => (Nat.digits 2 value).length + 2
  | .pair first second => scanCost first + scanCost second + 3

def finalState : Data → Option Alphabet
  | .atom _ => some 2
  | .pair _ _ => some 1

set_option backward.isDefEq.respectTransparency false in
inductive Stack where
  | input | frames | output
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Phase where
  | header | number | complete | checkTail | restore
  | rejectInput | rejectFrames | rejectOutput
  deriving DecidableEq, Fintype

/-- Frame zero requests the second child; frame one closes its enclosing pair.
All registers and labels are finite; pending depth is stored on a stack. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .input
  Γ _ := Alphabet
  Λ := Phase
  main := .header
  σ := Option Alphabet
  initialState := none
  m phase := match phase with
  | .header => pop .input (fun _ value => value)
      (branch (fun state => state == some 3)
        (push .output (fun _ => 3) (goto fun _ => .number))
        (branch (fun state => state == some 4)
          (push .frames (fun _ => 0) (goto fun _ => .header))
          (goto fun _ => .rejectInput)))
  | .number => pop .input (fun _ value => value)
      (branch (fun state => state == some 2)
        (push .output (fun _ => 2) (goto fun _ => .complete))
        (branch SharedReferenceExecution.isBit
          (push .output (fun state => state.getD 2) (goto fun _ => .number))
          (goto fun _ => .rejectInput)))
  | .complete => pop .frames (fun _ value => value)
      (branch (fun state => state == some 0)
        (push .frames (fun _ => 1) (goto fun _ => .header))
        (branch (fun state => state == some 1)
          (push .output (fun _ => 4) (goto fun _ => .complete))
          (branch (fun state => state.isNone) (goto fun _ => .checkTail)
            (goto fun _ => .rejectInput))))
  | .checkTail => pop .input (fun _ value => value)
      (branch (fun state => state.isNone) (goto fun _ => .restore)
        (goto fun _ => .rejectInput))
  | .restore => pop .output (fun _ value => value)
      (branch (fun state => state.isSome)
        (push .input (fun state => state.getD 2) (goto fun _ => .restore))
        (push .input (fun _ => 1) (load (fun _ => none) halt)))
  | .rejectInput => pop .input (fun _ value => value)
      (branch (fun state => state.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectFrames))
  | .rejectFrames => pop .frames (fun _ value => value)
      (branch (fun state => state.isSome) (goto fun _ => .rejectFrames) (goto fun _ => .rejectOutput))
  | .rejectOutput => pop .output (fun _ value => value)
      (branch (fun state => state.isSome) (goto fun _ => .rejectOutput)
        (push .input (fun _ => 0) (load (fun _ => none) halt)))

def config (phase : Option Phase) (state : Option Alphabet)
    (input frames output : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk stack := match (show Stack from stack) with
    | .input => input | .frames => frames | .output => output

local macro "check_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, config, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]))

theorem header_atom (state : Option Alphabet) (input frames output : List Alphabet) :
    machine.step (config (some .header) state (3 :: input) frames output) =
      some (config (some .number) (some 3) input frames (3 :: output)) := by check_step

theorem header_pair (state : Option Alphabet) (input frames output : List Alphabet) :
    machine.step (config (some .header) state (4 :: input) frames output) =
      some (config (some .header) (some 4) input (0 :: frames) output) := by check_step

theorem number_bit (state : Option Alphabet) (head : Bool) (input frames output : List Alphabet) :
    machine.step (config (some .number) state (SharedReferenceExecution.bit head :: input) frames output) =
      some (config (some .number) (some (SharedReferenceExecution.bit head)) input frames
        (SharedReferenceExecution.bit head :: output)) := by
  cases head <;>
    simp [SharedReferenceExecution.bit, SharedReferenceExecution.isBit, FinTM2.step, machine, config,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update] <;>
    congr 2 <;> funext stack <;> cases stack <;> simp [Function.update]

theorem number_end (state : Option Alphabet) (input frames output : List Alphabet) :
    machine.step (config (some .number) state (2 :: input) frames output) =
      some (config (some .complete) (some 2) input frames (2 :: output)) := by check_step

theorem complete_first (state : Option Alphabet) (input frames output : List Alphabet) :
    machine.step (config (some .complete) state input (0 :: frames) output) =
      some (config (some .header) (some 0) input (1 :: frames) output) := by check_step

theorem complete_second (state : Option Alphabet) (input frames output : List Alphabet) :
    machine.step (config (some .complete) state input (1 :: frames) output) =
      some (config (some .complete) (some 1) input frames (4 :: output)) := by check_step

def number_run (key : List Bool) (input frames output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some .number) state (SharedReferenceExecution.field key ++ 2 :: input) frames output)
      (some (config (some .complete) (some 2) input frames
        (2 :: (SharedReferenceExecution.field key).reverse ++ output))) (key.length + 1) := by
  induction key generalizing state output with
  | nil => simpa [SharedReferenceExecution.field] using SymbolMapMachine.oneStep (number_end state input frames output)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (number_bit state head
        (SharedReferenceExecution.field tail ++ 2 :: input) frames output)
      have rest := ih (SharedReferenceExecution.bit head :: output) (some (SharedReferenceExecution.bit head))
      simpa [SharedReferenceExecution.field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- A frame walk emits both children before their pair-closing event, retaining
all atom fields and the surrounding continuation stack. -/
noncomputable def traversal (value : Data) (input frames output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some .header) state (writeData value input) frames output)
      (some (config (some .complete) (finalState value) input frames
        ((postorderWire value).reverse ++ output))) (scanCost value) := by
  induction value generalizing input frames output state with
  | atom value =>
      have first := SymbolMapMachine.oneStep (header_atom state (natural value ++ input) frames output)
      have rest := number_run (SharedReferenceExecution.naturalKey value) input frames (3 :: output) (some 3)
      have sameInput : SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value) ++ 2 :: input =
          natural value ++ input := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.append_assoc]
      rw [sameInput] at rest
      have joined := EvalsToInTime.trans _ 1
        ((SharedReferenceExecution.naturalKey value).length + 1) _ _ _ first rest
      have sameOutput : 2 :: (SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value)).reverse ++ 3 :: output =
          (3 :: natural value).reverse ++ output := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.reverse_append, List.append_assoc]
      rw [sameOutput] at joined
      simpa [writeData, postorderWire, finalState, scanCost, SharedReferenceExecution.naturalKey] using joined
  | pair first second ihFirst ihSecond =>
      have begin := SymbolMapMachine.oneStep (header_pair state (writeData first (writeData second input)) frames output)
      have firstRun := ihFirst (writeData second input) (0 :: frames) output (some 4)
      have separator := SymbolMapMachine.oneStep (complete_first (finalState first) (writeData second input)
        frames ((postorderWire first).reverse ++ output))
      have secondRun := ihSecond input (1 :: frames) ((postorderWire first).reverse ++ output) (some 0)
      have finish := SymbolMapMachine.oneStep (complete_second (finalState second) input frames
        ((postorderWire second).reverse ++ (postorderWire first).reverse ++ output))
      have a := EvalsToInTime.trans _ 1 (scanCost first) _ _ _ begin firstRun
      have b := EvalsToInTime.trans _ (scanCost first + 1) 1 _ _ _ a separator
      have c := EvalsToInTime.trans _ (1 + (scanCost first + 1)) (scanCost second) _ _ _ b secondRun
      have d := EvalsToInTime.trans _ (scanCost second + (1 + (scanCost first + 1))) 1 _ _ _ c (by simpa [List.append_assoc] using finish)
      convert d using 1
      all_goals simp [writeData, postorderWire, finalState, scanCost, List.reverse_append, List.append_assoc]
      all_goals omega


theorem complete_empty (state : Option Alphabet) (input output : List Alphabet) :
    machine.step (config (some .complete) state input [] output) =
      some (config (some .checkTail) none input [] output) := by check_step

theorem tail_empty (output : List Alphabet) :
    machine.step (config (some .checkTail) none [] [] output) =
      some (config (some .restore) none [] [] output) := by check_step

theorem restore_cons (state : Option Alphabet) (head : Alphabet) (input tail : List Alphabet) :
    machine.step (config (some .restore) state input [] (head :: tail)) =
      some (config (some .restore) (some head) (head :: input) [] tail) := by check_step

theorem restore_nil (state : Option Alphabet) (input : List Alphabet) :
    machine.step (config (some .restore) state input [] []) =
      some (config none none (1 :: input) [] []) := by check_step

def restore_run (output input : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (config (some .restore) state input [] output)
      (some (config none none (1 :: output.reverse ++ input) [] [])) (output.length + 1) := by
  induction output generalizing input state with
  | nil => simpa using SymbolMapMachine.oneStep (restore_nil state input)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_cons state head input tail)
      have rest := ih (head :: input) (some head)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem init_eq (input : List Alphabet) :
    initList machine input = config (some .header) none input [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

theorem halt_eq (output : List Alphabet) :
    haltList machine output = config none none output [] [] := by
  simp only [haltList, machine, config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

theorem postorderWire_length (value : Data) : (postorderWire value).length = dataWeight value := by
  induction value with
  | atom value => simp [postorderWire, natural, dataWeight]; omega
  | pair first second ihFirst ihSecond => simp [postorderWire, dataWeight, ihFirst, ihSecond]; omega

theorem scanCost_le (value : Data) : scanCost value ≤ 3 * dataWeight value := by
  induction value with
  | atom value => simp [scanCost, dataWeight]; omega
  | pair first second ihFirst ihSecond => simp [scanCost, dataWeight]; omega

/-- Full finite-machine traversal, including pair closure, output restoration
and the reset of all scratch stacks and finite control. -/
noncomputable def outputs (value : Data) : TM2OutputsInTime machine (encodeData value)
    (some ((1 :: postorderWire value) : List Alphabet)) (scanCost value + dataWeight value + 3) := by
  have walk := traversal value [] [] [] none
  simp only [List.append_nil] at walk
  have endFrame := SymbolMapMachine.oneStep (complete_empty (finalState value) [] (postorderWire value).reverse)
  have check := SymbolMapMachine.oneStep (tail_empty (postorderWire value).reverse)
  have restore := restore_run (postorderWire value).reverse [] none
  simp only [List.reverse_reverse, List.append_nil] at restore
  have first := EvalsToInTime.trans _ (scanCost value) 1 _ _ _ walk endFrame
  have second := EvalsToInTime.trans _ (1 + scanCost value) 1 _ _ _ first check
  have third := EvalsToInTime.trans _ (1 + (1 + scanCost value))
    ((postorderWire value).reverse.length + 1) _ _ _ second restore
  change EvalsToInTime _ (initList machine (encodeData value))
    (some (haltList machine ((1 :: postorderWire value) : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert third using 1
  · rfl
  · simp [postorderWire_length]; omega

set_option backward.isDefEq.respectTransparency false in
/-- The physical traversal is linear in the complete encoded input length;
no natural payload is decoded into an unbounded machine register. -/
noncomputable def computable : TM2ComputableInPolyTime encodeData
    (fun word : List Alphabet => word) (fun value => 1 :: postorderWire value) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 4 * X + C 3
  outputsFun value := by
    change TM2OutputsInTime machine ((encodeData value).map id)
      (some ((1 :: postorderWire value).map id)) _
    simp only [List.map_id_fun]
    apply BinaryReferenceMachine.within (outputs value)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      encodeData, writeData_length, List.length_nil]
    have bound := scanCost_le value
    omega

/-- Reading the emitted events reconstructs the same original `Data`, so
existing source codecs retain all their interpretation and authority. -/
def foldFrames : Nat → List Alphabet → List Data → Option (List Data)
  | _, [], stack => some stack
  | 0, _, _ => none
  | fuel + 1, 3 :: word, stack => do
      let (value, rest) ← readNatural word
      foldFrames fuel rest (.atom value :: stack)
  | fuel + 1, 4 :: word, second :: first :: stack =>
      foldFrames fuel word (.pair first second :: stack)
  | _, _, _ => none

theorem foldFrames_postorderWire (value : Data) (tail : List Alphabet) (stack : List Data) (fuel : Nat) :
    foldFrames (nodeCount value + fuel) (postorderWire value ++ tail) stack =
      foldFrames fuel tail (value :: stack) := by
  induction value generalizing tail stack fuel with
  | atom value => simp [nodeCount, postorderWire, Nat.add_comm, foldFrames, readNatural_natural]
  | pair first second ihFirst ihSecond =>
      have count : nodeCount (.pair first second) + fuel =
          nodeCount first + (nodeCount second + (1 + fuel)) := by simp [nodeCount]; omega
      rw [count]
      simp only [postorderWire, List.append_assoc]
      rw [ihFirst]
      rw [ihSecond]
      simp [foldFrames, Nat.add_comm]

def decodeFrames (word : List Alphabet) : Option Data := do
  let stack ← foldFrames word.length word []
  match stack with
  | [value] => some value
  | _ => none

theorem nodeCount_le (value : Data) : nodeCount value ≤ dataWeight value := by
  induction value with
  | atom value => simp [nodeCount, dataWeight]; omega
  | pair first second ihFirst ihSecond => simp [nodeCount, dataWeight]; omega

theorem decodeFrames_postorderWire (value : Data) : decodeFrames (postorderWire value) = some value := by
  have enough := nodeCount_le value
  have fuel : dataWeight value = nodeCount value + (dataWeight value - nodeCount value) := by omega
  have run := foldFrames_postorderWire value [] [] (dataWeight value - nodeCount value)
  simp only [List.append_nil, ← fuel, foldFrames] at run
  simp only [decodeFrames, postorderWire_length, run]
  rfl

def decodeWithFrames {α : Type} (codec : Codec α) : List Alphabet → Option α
  | 1 :: word => (decodeFrames word).bind codec.get
  | _ => none

theorem decodeWithFrames_output {α : Type} (codec : Codec α) (value : α) :
    decodeWithFrames codec (1 :: postorderWire (codec.put value)) = some value := by
  simp [decodeWithFrames, decodeFrames_postorderWire, codec.get_put]


/-- The target storage remains a codec of the same authored object; only its
finite wire traversal and explicit frame closures change. -/
def frameEncoding {α : Type} (codec : Codec α) : _root_.Computability.Encoding α Alphabet where
  encode value := 1 :: postorderWire (codec.put value)
  decode := decodeWithFrames codec
  decode_encode := decodeWithFrames_output codec

set_option backward.isDefEq.respectTransparency false in
/-- Actual operational reencoding for any original source codec. This is a
nonidentity wire traversal, not a replacement proof checker. -/
noncomputable def reencode {α : Type} (codec : Codec α) : TM2ComputableInPolyTime
    (encodeWith codec) (frameEncoding codec).encode (fun value : α => value) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 4 * X + C 3
  outputsFun value := by
    change TM2OutputsInTime machine ((encodeWith codec value).map id)
      (some ((1 :: postorderWire (codec.put value)).map id)) _
    simp only [List.map_id_fun, encodeWith]
    apply BinaryReferenceMachine.within (outputs (codec.put value))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      encodeData, writeData_length, List.length_nil]
    have bound := scanCost_le (codec.put value)
    omega

/-- The complete original goal, chronological lemma list and final open proof
are retained by the finite traversal, including unused lemma occurrences. -/
noncomputable def inputReencoding : TM2ComputableInPolyTime CertificateDataEncoding.inputEncoding.encode
    (frameEncoding CertificateDataEncoding.inputCodec).encode (fun value => value) := reencode CertificateDataEncoding.inputCodec

noncomputable def sharedReencoding : TM2ComputableInPolyTime CertificateDataEncoding.sharedEncoding.encode
    (frameEncoding CertificateDataEncoding.sharedCodec).encode (fun value => value) := reencode CertificateDataEncoding.sharedCodec

theorem frameEncoding_length {α : Type} (codec : Codec α) (value : α) :
    ((frameEncoding codec).encode value).length = (encodeWith codec value).length + 1 := by
  simp [frameEncoding, postorderWire_length, encodeWith, encodeData, writeData_length]

theorem decodeInput_frames (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (source : List (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern × CertificateGSLT.RawOpenProof) × CertificateGSLT.RawOpenProof) :
    decodeWithFrames CertificateDataEncoding.inputCodec ((frameEncoding CertificateDataEncoding.inputCodec).encode (goal, source)) = some (goal, source) :=
  decodeWithFrames_output CertificateDataEncoding.inputCodec (goal, source)

theorem reject_output_cons (state : Option Alphabet) (head : Alphabet) (tail : List Alphabet) :
    machine.step (config (some .rejectOutput) state [] [] (head :: tail)) =
      some (config (some .rejectOutput) (some head) [] [] tail) := by check_step

theorem reject_output_nil (state : Option Alphabet) :
    machine.step (config (some .rejectOutput) state [] [] []) =
      some (config none none [0] [] []) := by check_step

def reject_output_run (output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (config (some .rejectOutput) state [] [] output)
      (some (config none none [0] [] [])) (output.length + 1) := by
  induction output generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (reject_output_nil state)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_output_cons state head tail)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem reject_frames_cons (state : Option Alphabet) (head : Alphabet) (tail output : List Alphabet) :
    machine.step (config (some .rejectFrames) state [] (head :: tail) output) =
      some (config (some .rejectFrames) (some head) [] tail output) := by check_step

theorem reject_frames_nil (state : Option Alphabet) (output : List Alphabet) :
    machine.step (config (some .rejectFrames) state [] [] output) =
      some (config (some .rejectOutput) none [] [] output) := by check_step

def reject_frames_run (frames output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (config (some .rejectFrames) state [] frames output)
      (some (config none none [0] [] [])) (frames.length + output.length + 2) := by
  induction frames generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (reject_frames_nil state output)
      have rest := reject_output_run output none
      convert EvalsToInTime.trans _ 1 (output.length + 1) _ _ _ first rest using 1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_frames_cons state head tail output)
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (tail.length + output.length + 2) _ _ _ first rest

theorem reject_input_cons (state : Option Alphabet) (head : Alphabet) (tail frames output : List Alphabet) :
    machine.step (config (some .rejectInput) state (head :: tail) frames output) =
      some (config (some .rejectInput) (some head) tail frames output) := by check_step

theorem reject_input_nil (state : Option Alphabet) (frames output : List Alphabet) :
    machine.step (config (some .rejectInput) state [] frames output) =
      some (config (some .rejectFrames) none [] frames output) := by check_step

def reject_run (input frames output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (config (some .rejectInput) state input frames output)
      (some (config none none [0] [] [])) (input.length + frames.length + output.length + 3) := by
  induction input generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (reject_input_nil state frames output)
      have rest := reject_frames_run frames output none
      convert EvalsToInTime.trans _ 1 (frames.length + output.length + 2) _ _ _ first rest using 1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_input_cons state head tail frames output)
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ 1 (tail.length + frames.length + output.length + 3) _ _ _ first rest

theorem tail_nonempty (head : Alphabet) (tail output : List Alphabet) :
    machine.step (config (some .checkTail) none (head :: tail) [] output) =
      some (config (some .rejectInput) (some head) tail [] output) := by check_step

theorem header_missing (state : Option Alphabet) (frames output : List Alphabet) :
    machine.step (config (some .header) state [] frames output) =
      some (config (some .rejectInput) none [] frames output) := by check_step

/-- Trailing data is refused after the whole scratch state has been cleared;
the unread suffix is charged even when an earlier complete frame was valid. -/
noncomputable def trailingOutputs (value : Data) (head : Alphabet) (tail : List Alphabet) :
    TM2OutputsInTime machine (writeData value (head :: tail)) (some ([0] : List Alphabet))
      (scanCost value + dataWeight value + tail.length + 5) := by
  have walk := traversal value (head :: tail) [] [] none
  simp only [List.append_nil] at walk
  have endFrame := SymbolMapMachine.oneStep (complete_empty (finalState value) (head :: tail) (postorderWire value).reverse)
  have check := SymbolMapMachine.oneStep (tail_nonempty head tail (postorderWire value).reverse)
  have reject := reject_run tail [] (postorderWire value).reverse (some head)
  have first := EvalsToInTime.trans _ (scanCost value) 1 _ _ _ walk endFrame
  have second := EvalsToInTime.trans _ (1 + scanCost value) 1 _ _ _ first check
  have third := EvalsToInTime.trans _ (1 + (1 + scanCost value))
    (tail.length + 0 + (postorderWire value).reverse.length + 3) _ _ _ second reject
  change EvalsToInTime _ (initList machine (writeData value (head :: tail)))
    (some (haltList machine ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert third using 1
  simp [postorderWire_length]
  omega

/-- An incomplete pair retains its outstanding second-child frame and is
refused by the same actual parser, without losing its executed work. -/
noncomputable def missingSecondOutputs (first : Data) :
    TM2OutputsInTime machine ((4 :: encodeData first) : List Alphabet) (some ([0] : List Alphabet))
      (scanCost first + dataWeight first + 7) := by
  have begin := SymbolMapMachine.oneStep (header_pair none (encodeData first) [] [])
  have walk := traversal first [] [0] [] (some 4)
  simp only [List.append_nil] at walk
  have separator := SymbolMapMachine.oneStep (complete_first (finalState first) [] [] (postorderWire first).reverse)
  have missing := SymbolMapMachine.oneStep (header_missing (some 0) [1] (postorderWire first).reverse)
  have reject := reject_run [] [1] (postorderWire first).reverse none
  have a := EvalsToInTime.trans _ 1 (scanCost first) _ _ _ begin walk
  have b := EvalsToInTime.trans _ (scanCost first + 1) 1 _ _ _ a separator
  have c := EvalsToInTime.trans _ (1 + (scanCost first + 1)) 1 _ _ _ b missing
  have d := EvalsToInTime.trans _ (1 + (1 + (scanCost first + 1)))
    (0 + 1 + (postorderWire first).reverse.length + 3) _ _ _ c reject
  change EvalsToInTime _ (initList machine ((4 :: encodeData first) : List Alphabet))
    (some (haltList machine ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert d using 1
  simp [postorderWire_length]
  omega


theorem number_missing (state : Option Alphabet) (frames output : List Alphabet) :
    machine.step (config (some .number) state [] frames output) =
      some (config (some .rejectInput) none [] frames output) := by
  simp [SharedReferenceExecution.isBit, FinTM2.step, machine, config,
    Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

def number_missing_run (key : List Bool) (frames output : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some .number) state (SharedReferenceExecution.field key) frames output)
      (some (config (some .rejectInput) none [] frames
        ((SharedReferenceExecution.field key).reverse ++ output))) (key.length + 1) := by
  induction key generalizing state output with
  | nil => simpa [SharedReferenceExecution.field] using SymbolMapMachine.oneStep (number_missing state frames output)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (number_bit state head (SharedReferenceExecution.field tail) frames output)
      have rest := ih (SharedReferenceExecution.bit head :: output) (some (SharedReferenceExecution.bit head))
      simpa [SharedReferenceExecution.field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- Unterminated binary payloads are refused with their complete scanning and
scratch-clearing costs, for arbitrarily long submitted fields. -/
def missingNaturalOutputs (key : List Bool) :
    TM2OutputsInTime machine ((3 :: SharedReferenceExecution.field key) : List Alphabet)
      (some ([0] : List Alphabet)) (2 * key.length + 6) := by
  have begin := SymbolMapMachine.oneStep (header_atom none (SharedReferenceExecution.field key) [] [])
  have walk := number_missing_run key [] [3] (some 3)
  have reject := reject_run [] [] ((SharedReferenceExecution.field key).reverse ++ [3]) none
  have first := EvalsToInTime.trans _ 1 (key.length + 1) _ _ _ begin walk
  have joined := EvalsToInTime.trans _ (key.length + 1 + 1)
    (0 + 0 + ((SharedReferenceExecution.field key).reverse ++ [3]).length + 3) _ _ _ first reject
  change EvalsToInTime _ (initList machine ((3 :: SharedReferenceExecution.field key) : List Alphabet))
    (some (haltList machine ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert joined using 1
  simp [SharedReferenceExecution.field]
  omega

def emptyOutputs : TM2OutputsInTime machine ([] : List Alphabet) (some ([0] : List Alphabet)) 4 := by
  have begin := SymbolMapMachine.oneStep (header_missing none [] [])
  have reject := reject_run [] [] [] none
  change EvalsToInTime _ (initList machine ([] : List Alphabet))
    (some (haltList machine ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  simpa using EvalsToInTime.trans _ 1 (0 + 0 + 0 + 3) _ _ _ begin reject

namespace SecondField

private abbrev original := CertificateDataTraversal.machine

/-- The original data walker keeps the caller's first/second-field mode in a
separate Boolean register. Both fields are fully scanned; only the second is
returned. The discarded first field remains charged to execution. -/
def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .input
  Γ _ := Alphabet
  Λ := Bool ⊕ Phase
  main := .inl false
  σ := Option Alphabet × Bool
  initialState := (none, true)
  m
  | .inl false => pop .input (fun _ value => (value, false))
      (branch (fun state => state.1 == some 4)
        (goto fun _ => .inr .header)
        (goto fun _ => .inr .rejectInput))
  | .inl true => pop .output (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .inl true)
        (load (fun _ => (none, true)) (goto fun _ => .inr .header)))
  | .inr .checkTail => branch (fun state => state.2)
      (Mettapedia.Computability.StackMachineRegisters.extend Sum.inr (original.m .checkTail))
      (goto fun _ => .inl true)
  | .inr .rejectOutput => pop .output (fun state value => (value, state.2))
      (branch (fun state => state.1.isSome) (goto fun _ => .inr .rejectOutput)
        (push .input (fun _ => 0) (load (fun _ => (none, true)) halt)))
  | .inr phase => Mettapedia.Computability.StackMachineRegisters.extend Sum.inr (original.m phase)

def embedded (phase : Option Phase) (state : Option Alphabet) (second : Bool)
    (input frames output : List Alphabet) : machine.Cfg :=
  Mettapedia.Computability.StackMachineRegisters.config Sum.inr second
    (CertificateDataTraversal.config phase state input frames output)

def extra (phase : Bool) (state : Option Alphabet) (second : Bool)
    (input output : List Alphabet) : machine.Cfg where
  l := some (.inl phase)
  var := (state, second)
  stk stack := match (show Stack from stack) with
    | .input => input | .frames => [] | .output => output

/-- Embedded ordinary walker transitions retain their exact physical cost. -/
theorem liftStep (phase : Phase) (notTail : phase ≠ .checkTail)
    (notReject : phase ≠ .rejectOutput) (next : Option Phase)
    (state nextState : Option Alphabet) (second : Bool)
    (input frames output nextInput nextFrames nextOutput : List Alphabet)
    (sourceStep : original.step (CertificateDataTraversal.config (some phase) state input frames output) =
      some (CertificateDataTraversal.config next nextState nextInput nextFrames nextOutput)) :
    machine.step (embedded (some phase) state second input frames output) =
      some (embedded next nextState second nextInput nextFrames nextOutput) := by
  have body : ∀ label, (CertificateDataTraversal.config (some phase) state input frames output).l = some label →
      machine.m (Sum.inr label) =
        Mettapedia.Computability.StackMachineRegisters.extend Sum.inr (original.m label) := by
    intro label same
    have labelEq : label = phase := Option.some.inj same.symm
    subst label
    cases phase <;> first | exact (notTail rfl).elim | exact (notReject rfl).elim | rfl
  have result := Mettapedia.Computability.StackMachineRegisters.step_extend Sum.inr second
    original.m machine.m (CertificateDataTraversal.config (some phase) state input frames output) body
  change Turing.TM2.step original.m _ = _ at sourceStep
  rw [sourceStep] at result
  exact result

local macro "walk_step" mode:term:max term:term : term => `(liftStep _ (by decide) (by decide) _ _ _ $mode _ _ _ _ _ _ $term)

noncomputable def numberRun (key : List Bool) (input frames output : List Alphabet)
    (state : Option Alphabet) (second : Bool) :
    EvalsToInTime machine.step
      (embedded (some .number) state second (SharedReferenceExecution.field key ++ 2 :: input) frames output)
      (some (embedded (some .complete) (some 2) second input frames
        (2 :: (SharedReferenceExecution.field key).reverse ++ output))) (key.length + 1) := by
  induction key generalizing state output with
  | nil => simpa [SharedReferenceExecution.field] using
      SymbolMapMachine.oneStep (walk_step second (number_end state input frames output))
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (walk_step second (number_bit state head
        (SharedReferenceExecution.field tail ++ 2 :: input) frames output))
      have rest := ih (SharedReferenceExecution.bit head :: output) (some (SharedReferenceExecution.bit head))
      simpa [SharedReferenceExecution.field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def walk (value : Data) (input frames output : List Alphabet)
    (state : Option Alphabet) (second : Bool) :
    EvalsToInTime machine.step
      (embedded (some .header) state second (writeData value input) frames output)
      (some (embedded (some .complete) (finalState value) second input frames
        ((postorderWire value).reverse ++ output))) (scanCost value) := by
  induction value generalizing input frames output state with
  | atom value =>
      have first := SymbolMapMachine.oneStep (walk_step second (header_atom state (natural value ++ input) frames output))
      have rest := numberRun (SharedReferenceExecution.naturalKey value) input frames (3 :: output) (some 3) second
      have sameInput : SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value) ++ 2 :: input =
          natural value ++ input := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.append_assoc]
      rw [sameInput] at rest
      have joined := EvalsToInTime.trans _ 1
        ((SharedReferenceExecution.naturalKey value).length + 1) _ _ _ first rest
      have sameOutput : 2 :: (SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value)).reverse ++ 3 :: output =
          (3 :: natural value).reverse ++ output := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.reverse_append, List.append_assoc]
      rw [sameOutput] at joined
      simpa [writeData, postorderWire, finalState, scanCost, SharedReferenceExecution.naturalKey] using joined
  | pair first secondValue ihFirst ihSecond =>
      have begin := SymbolMapMachine.oneStep (walk_step second (header_pair state (writeData first (writeData secondValue input)) frames output))
      have firstRun := ihFirst (writeData secondValue input) (0 :: frames) output (some 4)
      have separator := SymbolMapMachine.oneStep (walk_step second (complete_first (finalState first) (writeData secondValue input)
        frames ((postorderWire first).reverse ++ output)))
      have secondRun := ihSecond input (1 :: frames) ((postorderWire first).reverse ++ output) (some 0)
      have finish := SymbolMapMachine.oneStep (walk_step second (complete_second (finalState secondValue) input frames
        ((postorderWire secondValue).reverse ++ (postorderWire first).reverse ++ output)))
      have a := EvalsToInTime.trans _ 1 (scanCost first) _ _ _ begin firstRun
      have b := EvalsToInTime.trans _ (scanCost first + 1) 1 _ _ _ a separator
      have c := EvalsToInTime.trans _ (1 + (scanCost first + 1)) (scanCost secondValue) _ _ _ b secondRun
      have d := EvalsToInTime.trans _ (scanCost secondValue + (1 + (scanCost first + 1))) 1 _ _ _ c (by simpa [List.append_assoc] using finish)
      convert d using 1
      all_goals simp [writeData, postorderWire, finalState, scanCost, List.reverse_append, List.append_assoc]
      all_goals omega

local macro "projection_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, original, embedded, extra,
    Mettapedia.Computability.StackMachineRegisters.config,
    Mettapedia.Computability.StackMachineRegisters.extend,
    CertificateDataTraversal.machine, CertificateDataTraversal.config,
    Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  all_goals (congr 2
             funext stack
             cases stack <;> simp [Function.update])))

theorem start_pair (input : List Alphabet) :
    machine.step (extra false none true (4 :: input) []) =
      some (embedded (some .header) (some 4) false input [] []) := by projection_step

theorem first_done (input output : List Alphabet) :
    machine.step (embedded (some .checkTail) none false input [] output) =
      some (extra true none false input output) := by rfl

theorem clear_cons (state : Option Alphabet) (head : Alphabet) (input output : List Alphabet) :
    machine.step (extra true state false input (head :: output)) =
      some (extra true (some head) false input output) := by projection_step

theorem clear_nil (state : Option Alphabet) (input : List Alphabet) :
    machine.step (extra true state false input []) =
      some (embedded (some .header) none true input [] []) := by projection_step

def clearRun (output input : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (extra true state false input output)
      (some (embedded (some .header) none true input [] [])) (output.length + 1) := by
  induction output generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (clear_nil state input)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (clear_cons state head input tail)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem second_tail (output : List Alphabet) :
    machine.step (embedded (some .checkTail) none true [] [] output) =
      some (embedded (some .restore) none true [] [] output) := by projection_step

noncomputable def restoreRun (output input : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime machine.step (embedded (some .restore) state true input [] output)
      (some (embedded none none true (1 :: output.reverse ++ input) [] [])) (output.length + 1) := by
  induction output generalizing input state with
  | nil => simpa using SymbolMapMachine.oneStep (walk_step true (restore_nil state input))
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (walk_step true (restore_cons state head input tail))
      have rest := ih (head :: input) (some head)
      simpa [List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem init_eq (input : List Alphabet) :
    initList machine input = extra false none true input [] := by
  simp only [initList, machine, extra]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

theorem halt_eq (output : List Alphabet) :
    haltList machine output = embedded none none true output [] [] := by
  simp only [haltList, machine, embedded,
    Mettapedia.Computability.StackMachineRegisters.config, CertificateDataTraversal.config]
  congr 1
  funext stack
  cases stack
  · simp; rfl
  · simp
  · simp

/-- The selected second field is exactly the original child, and scanning and
clearing the first field contribute their physical costs. -/
noncomputable def outputs (first second : Data) :
    TM2OutputsInTime machine (encodeData (.pair first second))
      (some ((1 :: postorderWire second) : List Alphabet))
      (scanCost first + scanCost second + dataWeight first + dataWeight second + 7) := by
  have start := SymbolMapMachine.oneStep (start_pair (writeData first (writeData second [])))
  have left := walk first (writeData second []) [] [] (some 4) false
  simp only [List.append_nil] at left
  have leftDone := SymbolMapMachine.oneStep (walk_step false (complete_empty (finalState first)
    (writeData second []) (postorderWire first).reverse))
  have separator := SymbolMapMachine.oneStep (first_done (writeData second []) (postorderWire first).reverse)
  have clear := clearRun (postorderWire first).reverse (writeData second []) none
  have right := walk second [] [] [] none true
  simp only [List.append_nil] at right
  have rightDone := SymbolMapMachine.oneStep (walk_step true (complete_empty (finalState second) [] (postorderWire second).reverse))
  have tail := SymbolMapMachine.oneStep (second_tail (postorderWire second).reverse)
  have restore := restoreRun (postorderWire second).reverse [] none
  simp only [List.reverse_reverse, List.append_nil] at restore
  have a := EvalsToInTime.trans _ 1 (scanCost first) _ _ _ start left
  have b := EvalsToInTime.trans _ (scanCost first + 1) 1 _ _ _ a leftDone
  have c := EvalsToInTime.trans _ (1 + (scanCost first + 1)) 1 _ _ _ b separator
  have d := EvalsToInTime.trans _ (1 + (1 + (scanCost first + 1)))
    ((postorderWire first).reverse.length + 1) _ _ _ c clear
  have e := EvalsToInTime.trans _ ((postorderWire first).reverse.length + 1 + (1 + (1 + (scanCost first + 1))))
    (scanCost second) _ _ _ d right
  have f := EvalsToInTime.trans _ (scanCost second + ((postorderWire first).reverse.length + 1 + (1 + (1 + (scanCost first + 1))))) 1 _ _ _ e rightDone
  have g := EvalsToInTime.trans _ (1 + (scanCost second + ((postorderWire first).reverse.length + 1 + (1 + (1 + (scanCost first + 1)))))) 1 _ _ _ f tail
  have h := EvalsToInTime.trans _ (1 + (1 + (scanCost second + ((postorderWire first).reverse.length + 1 + (1 + (1 + (scanCost first + 1)))))))
    ((postorderWire second).reverse.length + 1) _ _ _ g restore
  change EvalsToInTime _ (initList machine (encodeData (.pair first second)))
    (some (haltList machine ((1 :: postorderWire second) : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert h using 1
  · rfl
  · simp only [List.length_reverse, postorderWire_length]
    omega

/-- Source product components are selected by the finite machine, rather than
by an uncharged call to the codec's decoder. -/
noncomputable def computable : TM2ComputableInPolyTime
    (fun pair : Data × Data => encodeData (.pair pair.1 pair.2))
    (fun word : List Alphabet => word) (fun pair => 1 :: postorderWire pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 4 * X + C 3
  outputsFun pair := by
    change TM2OutputsInTime machine ((encodeData (.pair pair.1 pair.2)).map id)
      (some ((1 :: postorderWire pair.2).map id)) _
    simp only [List.map_id_fun]
    apply BinaryReferenceMachine.within (outputs pair.1 pair.2)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      encodeData, writeData_length, List.length_nil]
    have first := scanCost_le pair.1
    have second := scanCost_le pair.2
    simp only [dataWeight]
    omega

/-- Intermediate storage remains bounded by the complete original packet. -/
theorem selected_length_le {A B : Type} (first : Codec A) (second : Codec B) (pair : A × B) :
    ((frameEncoding second).encode pair.2).length ≤ (encodeWith (Codec.prod first second) pair).length := by
  rw [frameEncoding_length]
  simp only [encodeWith, Codec.prod, encodeData, writeData_length, List.length_nil, dataWeight]
  omega

noncomputable def selectCodec {A B : Type} (first : Codec A) (second : Codec B) :
    TM2ComputableInPolyTime (encodeWith (Codec.prod first second))
      (frameEncoding second).encode (fun pair : A × B => pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := computable.time
  outputsFun pair := computable.outputsFun (first.put pair.1, second.put pair.2)

/-- Select the original chronological source from its goal/source packet. -/
noncomputable def sourceSelection := selectCodec CertificateDataEncoding.patternCodec CertificateDataEncoding.sharedCodec

/-- Select the original final open proof after scanning every authored lemma. -/
noncomputable def finalSelection := selectCodec
  (Codec.list (Codec.prod CertificateDataEncoding.patternCodec CertificateDataEncoding.proofCodec))
  CertificateDataEncoding.proofCodec

theorem reject_output_cons (state : Option Alphabet) (second : Bool)
    (head : Alphabet) (output : List Alphabet) :
    machine.step (embedded (some .rejectOutput) state second [] [] (head :: output)) =
      some (embedded (some .rejectOutput) (some head) second [] [] output) := by projection_step

theorem reject_output_nil (state : Option Alphabet) (second : Bool) :
    machine.step (embedded (some .rejectOutput) state second [] [] []) =
      some (embedded none none true [0] [] []) := by projection_step

def rejectOutputRun (output : List Alphabet) (state : Option Alphabet) (second : Bool) :
    EvalsToInTime machine.step (embedded (some .rejectOutput) state second [] [] output)
      (some (embedded none none true [0] [] [])) (output.length + 1) := by
  induction output generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (reject_output_nil state second)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_output_cons state second head tail)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

noncomputable def rejectFramesRun (frames output : List Alphabet) (state : Option Alphabet) (second : Bool) :
    EvalsToInTime machine.step (embedded (some .rejectFrames) state second [] frames output)
      (some (embedded none none true [0] [] [])) (frames.length + output.length + 2) := by
  induction frames generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (walk_step second (reject_frames_nil state output))
      have rest := rejectOutputRun output none second
      convert EvalsToInTime.trans _ 1 (output.length + 1) _ _ _ first rest using 1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (walk_step second (reject_frames_cons state head tail output))
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + output.length + 2) _ _ _ first rest

noncomputable def rejectRun (input frames output : List Alphabet) (state : Option Alphabet) (second : Bool) :
    EvalsToInTime machine.step (embedded (some .rejectInput) state second input frames output)
      (some (embedded none none true [0] [] [])) (input.length + frames.length + output.length + 3) := by
  induction input generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (walk_step second (reject_input_nil state frames output))
      have rest := rejectFramesRun frames output none second
      convert EvalsToInTime.trans _ 1 (frames.length + output.length + 2) _ _ _ first rest using 1
      simp only [List.length_nil]
      omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (walk_step second (reject_input_cons state head tail frames output))
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + frames.length + output.length + 3) _ _ _ first rest

theorem start_not_pair (head : Alphabet) (notPair : head ≠ 4) (input : List Alphabet) :
    machine.step (extra false none true (head :: input) []) =
      some (embedded (some .rejectInput) (some head) false input [] []) := by
  have notEq : ((some head : Option Alphabet) == some 4) = false := by simp [notPair]
  simp [FinTM2.step, machine, extra, embedded,
    Mettapedia.Computability.StackMachineRegisters.config, CertificateDataTraversal.config,
    Turing.TM2.step, Turing.TM2.stepAux, notEq]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

/-- A malformed outer product is refused after clearing all remaining input
and scratch storage, including arbitrarily long supplied suffixes. -/
noncomputable def notPairOutputs (head : Alphabet) (notPair : head ≠ 4) (tail : List Alphabet) :
    TM2OutputsInTime machine ((head :: tail) : List Alphabet) (some ([0] : List Alphabet)) (tail.length + 4) := by
  have first := SymbolMapMachine.oneStep (start_not_pair head notPair tail)
  have rest := rejectRun tail [] [] (some head) false
  change EvalsToInTime _ (initList machine ((head :: tail) : List Alphabet))
    (some (haltList machine ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  simpa using EvalsToInTime.trans _ 1 (tail.length + 0 + 0 + 3) _ _ _ first rest

end SecondField


namespace PrefixField

set_option backward.isDefEq.respectTransparency false

private abbrev original := CertificateDataTraversal.machine
open Mettapedia.Computability.StackMachineRegisters

private def afterRead : original.Stmt → original.Stmt
  | .pop _ _ rest => rest
  | statement => statement

/-- Capture a physically read symbol on the caller's extra stack, retaining
exactly the original parser's remaining statement and state update. -/
private def capture (rest : original.Stmt) :
    Turing.TM2.Stmt (withStackAlphabet original.Γ Alphabet) Phase (Option Alphabet) :=
  pop (some Stack.input) (fun _ value => value)
    (branch (fun state => state.isSome)
      (push none (fun state => state.getD 2) (withStack id rest))
      (withStack id rest))

/-- Prefix capture is an actual subroutine of the original data walker. The
extra stack stores read symbols, rather than decoded numbers or data trees. -/
def machine : FinTM2 where
  K := Option Stack
  k₀ := some .input
  k₁ := some .input
  Γ := withStackAlphabet original.Γ Alphabet
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase
  main := .header
  σ := Option Alphabet
  initialState := none
  m phase := match phase with
    | .header => capture (afterRead (original.m .header))
    | .number => capture (afterRead (original.m .number))
    | phase => withStack id (original.m phase)

/-- Pair continuations use the original walker body. A caller may intercept a
separate sentinel return while retaining the original zero/one frame steps. -/
theorem machine_complete : machine.m .complete =
    withStack (Cell := Alphabet) id (CertificateDataTraversal.machine.m .complete) := rfl

/-- Public statement equation for embedding the original captured header read
without exposing the walker's private construction helpers. -/
theorem machine_header : machine.m .header =
    (show TM2.Stmt (withStackAlphabet (fun _ : Stack => Alphabet) Alphabet) Phase (Option Alphabet) from
    let rest : TM2.Stmt (withStackAlphabet (fun _ : Stack => Alphabet) Alphabet) Phase (Option Alphabet) := branch (fun state => state == some 3)
      (push (some .output) (fun _ => 3) (goto fun _ => .number))
      (branch (fun state => state == some 4)
        (push (some .frames) (fun _ => 0) (goto fun _ => .header))
        (goto fun _ => .rejectInput))
    pop (some .input) (fun _ value => value)
      (branch (fun state => state.isSome)
        (push none (fun state => state.getD 2) rest) rest)) := rfl

/-- Public statement equation for the original binary-field read. Capturing a
byte remains part of this same physical transition. -/
theorem machine_number : machine.m .number =
    (show TM2.Stmt (withStackAlphabet (fun _ : Stack => Alphabet) Alphabet) Phase (Option Alphabet) from
    let rest : TM2.Stmt (withStackAlphabet (fun _ : Stack => Alphabet) Alphabet) Phase (Option Alphabet) := branch (fun state => state == some 2)
      (push (some .output) (fun _ => 2) (goto fun _ => .complete))
      (branch SharedReferenceExecution.isBit
        (push (some .output) (fun state => state.getD 2) (goto fun _ => .number))
        (goto fun _ => .rejectInput))
    pop (some .input) (fun _ value => value)
      (branch (fun state => state.isSome)
        (push none (fun state => state.getD 2) rest) rest)) := rfl

def config (phase : Option Phase) (state : Option Alphabet)
    (input frames output memo : List Alphabet) : machine.Cfg where
  l := phase
  var := state
  stk key := match key with
    | none => memo
    | some .input => input
    | some .frames => frames
    | some .output => output

local macro "prefix_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, original, config,
    withStack, capture, afterRead, CertificateDataTraversal.machine,
    Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  congr 2
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key <;> simp [Function.update]))

theorem header_atom (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (config (some .header) state (3 :: input) frames output memo) =
      some (config (some .number) (some 3) input frames (3 :: output) (3 :: memo)) := by prefix_step

theorem header_pair (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (config (some .header) state (4 :: input) frames output memo) =
      some (config (some .header) (some 4) input (0 :: frames) output (4 :: memo)) := by prefix_step

theorem number_bit (state : Option Alphabet) (head : Bool) (input frames output memo : List Alphabet) :
    machine.step (config (some .number) state (SharedReferenceExecution.bit head :: input) frames output memo) =
      some (config (some .number) (some (SharedReferenceExecution.bit head)) input frames
        (SharedReferenceExecution.bit head :: output) (SharedReferenceExecution.bit head :: memo)) := by
  cases head <;>
    simp [SharedReferenceExecution.bit, SharedReferenceExecution.isBit,
      FinTM2.step, machine, original, config,
      withStack, capture, afterRead, CertificateDataTraversal.machine,
      Turing.TM2.step, Turing.TM2.stepAux, Function.update] <;>
    funext key <;> cases key with
    | none => simp [Function.update]
    | some key => cases key <;> simp [Function.update]

theorem number_end (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (config (some .number) state (2 :: input) frames output memo) =
      some (config (some .complete) (some 2) input frames (2 :: output) (2 :: memo)) := by prefix_step

theorem complete_first (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (config (some .complete) state input (0 :: frames) output memo) =
      some (config (some .header) (some 0) input (1 :: frames) output memo) := by prefix_step

theorem complete_second (state : Option Alphabet) (input frames output memo : List Alphabet) :
    machine.step (config (some .complete) state input (1 :: frames) output memo) =
      some (config (some .complete) (some 1) input frames (4 :: output) memo) := by prefix_step

/-- Positive field walking calls only header/number reads and internal pair
continuations. An enclosing driver may override the empty-frame return and
all rejection phases. -/
def scanning (state : machine.Cfg) : Prop :=
  state.l = some .header ∨ state.l = some .number ∨
    (state.l = some .complete ∧
      ((state.stk (some Stack.frames)).head? = some (0 : Alphabet) ∨
       (state.stk (some Stack.frames)).head? = some (1 : Alphabet)))

section Mapping

variable {Target : Type} (targetStep : Target → Option Target) (embed : machine.Cfg → Target)
  (steps : ∀ state, scanning state → targetStep (embed state) = (machine.step state).map embed)

include steps

theorem stepInto (before after : machine.Cfg) (sourceStep : machine.step before = some after)
    (allowed : scanning before) : targetStep (embed before) = some (embed after) := by
  rw [steps before allowed, sourceStep]
  rfl

local macro "prefix_mapped" term:term : term => `(stepInto targetStep embed (steps := steps) _ _ $term (by simp [scanning, config]))

noncomputable def numberInto (key : List Bool) (input frames output memo : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime targetStep
      (embed (config (some .number) state (SharedReferenceExecution.field key ++ 2 :: input) frames output memo))
      (some (embed (config (some .complete) (some 2) input frames
        (2 :: (SharedReferenceExecution.field key).reverse ++ output)
        ((SharedReferenceExecution.field key ++ [2]).reverse ++ memo)))) (key.length + 1) := by
  induction key generalizing state output memo with
  | nil => simpa [SharedReferenceExecution.field] using SymbolMapMachine.oneStep (prefix_mapped (number_end state input frames output memo))
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (prefix_mapped (number_bit state head
        (SharedReferenceExecution.field tail ++ 2 :: input) frames output memo))
      have rest := ih (SharedReferenceExecution.bit head :: output)
        (SharedReferenceExecution.bit head :: memo) (some (SharedReferenceExecution.bit head))
      simpa [SharedReferenceExecution.field, List.reverse_cons, List.append_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- A caller reuses the same exact finite field traversal through its proved
one-step configuration embedding; empty-frame returns remain the caller's
responsibility. -/
noncomputable def walkInto (value : Data) (input frames output memo : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime targetStep
      (embed (config (some .header) state (writeData value input) frames output memo))
      (some (embed (config (some .complete) (finalState value) input frames
        ((postorderWire value).reverse ++ output)
        ((encodeData value).reverse ++ memo)))) (scanCost value) := by
  induction value generalizing input frames output memo state with
  | atom value =>
      have first := SymbolMapMachine.oneStep (prefix_mapped (header_atom state (natural value ++ input) frames output memo))
      have rest := numberInto targetStep embed (steps := steps) (SharedReferenceExecution.naturalKey value) input frames (3 :: output) (3 :: memo) (some 3)
      have sameInput : SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value) ++ 2 :: input =
          natural value ++ input := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.append_assoc]
      rw [sameInput] at rest
      have joined := EvalsToInTime.trans _ 1
        ((SharedReferenceExecution.naturalKey value).length + 1) _ _ _ first rest
      have sameField : SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value) ++ [2] =
          natural value := SharedReferenceExecution.field_naturalKey value
      rw [sameField] at joined
      have sameOutput : 2 :: (SharedReferenceExecution.field (SharedReferenceExecution.naturalKey value)).reverse ++ 3 :: output =
          (3 :: natural value).reverse ++ output := by
        rw [← SharedReferenceExecution.field_naturalKey]
        simp [List.reverse_append, List.append_assoc]
      have sameMemo : (natural value).reverse ++ 3 :: memo =
          (3 :: natural value).reverse ++ memo := by
        simp [List.reverse_cons, List.append_assoc]
      rw [sameOutput, sameMemo] at joined
      simpa [writeData, postorderWire, encodeData_atom, finalState,
        scanCost, SharedReferenceExecution.naturalKey] using joined
  | pair first second ihFirst ihSecond =>
      have begin := SymbolMapMachine.oneStep (prefix_mapped (header_pair state (writeData first (writeData second input)) frames output memo))
      have firstRun := ihFirst (writeData second input) (0 :: frames) output (4 :: memo) (some 4)
      have separator := SymbolMapMachine.oneStep (prefix_mapped (complete_first (finalState first) (writeData second input)
        frames ((postorderWire first).reverse ++ output) ((encodeData first).reverse ++ 4 :: memo)))
      have secondRun := ihSecond input (1 :: frames) ((postorderWire first).reverse ++ output)
        ((encodeData first).reverse ++ 4 :: memo) (some 0)
      have finish := SymbolMapMachine.oneStep (prefix_mapped (complete_second (finalState second) input frames
        ((postorderWire second).reverse ++ (postorderWire first).reverse ++ output)
        ((encodeData second).reverse ++ (encodeData first).reverse ++ 4 :: memo)))
      have a := EvalsToInTime.trans _ 1 (scanCost first) _ _ _ begin firstRun
      have b := EvalsToInTime.trans _ (scanCost first + 1) 1 _ _ _ a separator
      have c := EvalsToInTime.trans _ (1 + (scanCost first + 1)) (scanCost second) _ _ _ b secondRun
      have d := EvalsToInTime.trans _ (scanCost second + (1 + (scanCost first + 1))) 1 _ _ _ c
        (by simpa [List.append_assoc] using finish)
      convert d using 1
      all_goals simp [writeData, postorderWire, finalState, scanCost, encodeData_pair,
        List.reverse_cons, List.reverse_append, List.append_assoc]
      all_goals omega

end Mapping

noncomputable def numberRun (key : List Bool) (input frames output memo : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some .number) state (SharedReferenceExecution.field key ++ 2 :: input) frames output memo)
      (some (config (some .complete) (some 2) input frames
        (2 :: (SharedReferenceExecution.field key).reverse ++ output)
        ((SharedReferenceExecution.field key ++ [2]).reverse ++ memo))) (key.length + 1) := by
  exact numberInto machine.step id (steps := by intro state _; simp) key input frames output memo state

/-- The original prefix bytes are captured in their physical read order. The
same walk also retains its original postorder scratch, caller continuation
frames and unread tail, with no reserialization call or new data authority. -/
noncomputable def traversal (value : Data) (input frames output memo : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime machine.step
      (config (some .header) state (writeData value input) frames output memo)
      (some (config (some .complete) (finalState value) input frames
        ((postorderWire value).reverse ++ output)
        ((encodeData value).reverse ++ memo))) (scanCost value) := by
  exact walkInto machine.step id (steps := by intro state _; simp) value input frames output memo state


/-- Discard the capture-only stack while retaining the original parser state. -/
def forgetMemo (state : machine.Cfg) : CertificateDataTraversal.machine.Cfg where
  l := state.l
  var := state.var
  stk key := state.stk (some key)

theorem forgetMemo_config (phase : Option Phase) (state : Option Alphabet)
    (input frames output memo : List Alphabet) :
    forgetMemo (config phase state input frames output memo) =
      CertificateDataTraversal.config phase state input frames output := by
  simp only [forgetMemo, config, CertificateDataTraversal.config]
  congr 1
  funext key
  cases key <;> rfl

/-- Capture writes are private to the extra stack; erasing that stack recovers
exactly one original parser transition, including malformed-input branches. -/
theorem step_forgetMemo (phase : Option Phase) (state : Option Alphabet)
    (input frames output memo : List Alphabet) :
    CertificateDataTraversal.machine.step (CertificateDataTraversal.config phase state input frames output) =
      (machine.step (config phase state input frames output memo)).map forgetMemo := by
  cases phase with
  | none => rfl
  | some phase =>
    cases phase <;>
      simp [FinTM2.step, machine, original, config, forgetMemo,
        withStack, capture, afterRead, CertificateDataTraversal.machine, CertificateDataTraversal.config,
        Turing.TM2.step, Turing.TM2.stepAux, Function.update]
    all_goals simp only [Bool.cond_eq_ite]
    all_goals repeat' split
    all_goals simp_all!
    all_goals first
      | rfl
      | (funext key; cases key <;> simp_all [Function.update])


theorem config_eta (source : machine.Cfg) :
    source = config source.l source.var (source.stk (some .input))
      (source.stk (some .frames)) (source.stk (some .output)) (source.stk none) := by
  cases source with
  | mk phase state contents =>
    simp only [config]
    congr 1
    funext key
    cases key with
    | none => rfl
    | some key => cases key <;> rfl

theorem step_forgetMemo_general (source : machine.Cfg) :
    CertificateDataTraversal.machine.step (forgetMemo source) =
      (machine.step source).map forgetMemo := by
  have result := step_forgetMemo source.l source.var (source.stk (some .input))
    (source.stk (some .frames)) (source.stk (some .output)) (source.stk none)
  rw [← forgetMemo_config source.l source.var (source.stk (some .input))
    (source.stk (some .frames)) (source.stk (some .output)) (source.stk none)] at result
  rw [← config_eta source] at result
  exact result

end PrefixField


theorem scanCost_add_one_le (value : Data) : scanCost value + 1 ≤ 2 * dataWeight value := by
  induction value with
  | atom value => simp only [scanCost, dataWeight]; omega
  | pair first second firstIH secondIH => simp only [scanCost, dataWeight]; omega

namespace ProductField
set_option backward.isDefEq.respectTransparency false
open Mettapedia.Computability.StackMachineRegisters
local instance : Fintype PrefixField.machine.K := PrefixField.machine.kFin

inductive Phase where
  | start | field (phase : CertificateDataTraversal.Phase)
  | clearOutput | restoreMemo | rejectMemo
  deriving DecidableEq, Fintype

abbrev Control := Option Alphabet × Bool

/-- The selected field captures its physically read prefix; the other field
runs the original walker while retaining the selected memo. -/
def parserBody (takeSecond : Bool) (phase : CertificateDataTraversal.Phase) :
    TM2.Stmt PrefixField.machine.Γ Phase Control :=
  branch (fun state => state.2 == takeSecond)
    (extend Phase.field (PrefixField.machine.m phase))
    (extend Phase.field (withStack id (CertificateDataTraversal.machine.m phase)))

def machine (takeSecond : Bool) : FinTM2 where
  K := PrefixField.machine.K
  k₀ := some .input
  k₁ := some .input
  Γ := PrefixField.machine.Γ
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase
  main := .start
  σ := Control
  initialState := (none, false)
  m phase := match phase with
    | .start => pop (some Stack.input) (fun state value => (value, state.2))
        (branch (fun state => state.1 == some 4)
          (goto fun _ => .field .header) (goto fun _ => .field .rejectInput))
    | .field .checkTail => branch (fun state => state.2)
        (pop (some Stack.input) (fun state value => (value, state.2))
          (branch (fun state => state.1.isNone)
            (goto fun _ => .clearOutput) (goto fun _ => .field .rejectInput)))
        (load (fun state => (state.1, true)) (goto fun _ => .field .header))
    | .field .rejectOutput => pop (some Stack.output) (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (goto fun _ => .field .rejectOutput) (goto fun _ => .rejectMemo))
    | .field phase => parserBody takeSecond phase
    | .clearOutput => pop (some Stack.output) (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .clearOutput) (goto fun _ => .restoreMemo))
    | .restoreMemo => pop none (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome)
          (push (some Stack.input) (fun state => state.1.getD 2) (goto fun _ => .restoreMemo))
          (push (some Stack.input) (fun _ => (1 : Alphabet)) (load (fun _ => (none, false)) halt)))
    | .rejectMemo => pop none (fun state value => (value, state.2))
        (branch (fun state => state.1.isSome) (goto fun _ => .rejectMemo)
          (push (some Stack.input) (fun _ => (0 : Alphabet)) (load (fun _ => (none, false)) halt)))

def config (takeSecond : Bool) (phase : Option Phase) (state : Option Alphabet) (second : Bool)
    (input frames output memo : List Alphabet) : (machine takeSecond).Cfg where
  l := phase
  var := (state, second)
  stk key := match (show Option Stack from key) with
    | none => memo | some .input => input | some .frames => frames | some .output => output

/-- Configuration embedding for a captured field. -/
def embedCaptured (takeSecond second : Bool) (source : PrefixField.machine.Cfg) : (machine takeSecond).Cfg :=
  Mettapedia.Computability.StackMachineRegisters.config Phase.field second source

/-- Configuration embedding for an unselected field retains the captured
selected word, while the original walker continues on the other stacks. -/
def embedIgnored (takeSecond second : Bool) (memo : List Alphabet) (source : PrefixField.machine.Cfg) :
    (machine takeSecond).Cfg :=
  Mettapedia.Computability.StackMachineRegisters.config Phase.field second
    (withStackConfig id memo (PrefixField.forgetMemo source))

theorem embedCaptured_config (takeSecond second : Bool) (phase : Option CertificateDataTraversal.Phase)
    (state : Option Alphabet) (input frames output memo : List Alphabet) :
    embedCaptured takeSecond second (PrefixField.config phase state input frames output memo) =
      config takeSecond (phase.map Phase.field) state second input frames output memo := by
  rfl

theorem embedIgnored_config (takeSecond second : Bool) (phase : Option CertificateDataTraversal.Phase)
    (state : Option Alphabet) (input frames output captured memo : List Alphabet) :
    embedIgnored takeSecond second memo (PrefixField.config phase state input frames output captured) =
      config takeSecond (phase.map Phase.field) state second input frames output memo := by
  simp only [embedIgnored, PrefixField.forgetMemo_config, withStackConfig,
    Mettapedia.Computability.StackMachineRegisters.config,
    CertificateDataTraversal.config, config, Option.map_id]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

/-- The selected-field branch executes the original capturing statement with
one finite caller register, rather than invoking a semantic oracle. -/
theorem captured_step (takeSecond second : Bool) (selected : second = takeSecond)
    (phase : CertificateDataTraversal.Phase) (notTail : phase ≠ .checkTail)
    (notReject : phase ≠ .rejectOutput) (source : PrefixField.machine.Cfg)
    (atPhase : source.l = some phase) :
    (machine takeSecond).step (embedCaptured takeSecond second source) =
      (PrefixField.machine.step source).map (embedCaptured takeSecond second) := by
  rcases source with ⟨label, state, contents⟩
  cases label with
  | none => cases atPhase
  | some label =>
      have same : label = phase := Option.some.inj atPhase
      subst label
      change some (TM2.stepAux ((machine takeSecond).m (.field phase))
        (state, second) contents) = some (Mettapedia.Computability.StackMachineRegisters.config
          Phase.field second (TM2.stepAux (PrefixField.machine.m phase) state contents))
      have body : (machine takeSecond).m (.field phase) = parserBody takeSecond phase := by
        cases phase <;> simp_all [machine]
      rw [body]
      simp only [parserBody, TM2.stepAux, selected, beq_self_eq_true, Bool.cond_true]
      exact congrArg some (stepAux_extend Phase.field takeSecond (PrefixField.machine.m phase) state contents)

/-- The unselected field still executes the original parser. Its capture stack
is retained, and erasing temporary capture writes preserves every transition. -/
theorem ignored_step (takeSecond second : Bool) (unselected : second ≠ takeSecond)
    (memo : List Alphabet) (phase : CertificateDataTraversal.Phase)
    (notTail : phase ≠ .checkTail) (notReject : phase ≠ .rejectOutput)
    (source : PrefixField.machine.Cfg) (atPhase : source.l = some phase) :
    (machine takeSecond).step (embedIgnored takeSecond second memo source) =
      (PrefixField.machine.step source).map (embedIgnored takeSecond second memo) := by
  let assembly := fun original : CertificateDataTraversal.machine.Cfg =>
    Mettapedia.Computability.StackMachineRegisters.config Phase.field second
      (withStackConfig id memo original)
  have erased := congrArg (Option.map assembly) (PrefixField.step_forgetMemo_general source)
  simp only [Option.map_map] at erased
  change (machine takeSecond).step (assembly (PrefixField.forgetMemo source)) =
    (PrefixField.machine.step source).map (assembly ∘ PrefixField.forgetMemo)
  rw [← erased]
  rcases source with ⟨label, state, contents⟩
  cases label with
  | none => cases atPhase
  | some label =>
      have same : label = phase := Option.some.inj atPhase
      subst label
      change some (TM2.stepAux ((machine takeSecond).m (.field phase)) (state, second)
        (withStackContents (fun key => contents (some key)) memo)) =
        some (Mettapedia.Computability.StackMachineRegisters.config Phase.field second
          (withStackConfig id memo (TM2.stepAux (CertificateDataTraversal.machine.m phase)
            state (fun key => contents (some key)))))
      have body : (machine takeSecond).m (.field phase) = parserBody takeSecond phase := by
        cases phase <;> simp_all [machine]
      rw [body]
      simp only [parserBody, TM2.stepAux]
      rw [beq_eq_false_iff_ne.mpr unselected]
      simp only [Bool.cond_false]
      apply congrArg some
      exact (stepAux_extend Phase.field second
        (withStack id (CertificateDataTraversal.machine.m phase)) state
        (withStackContents (fun key => contents (some key)) memo)).trans
        (congrArg (Mettapedia.Computability.StackMachineRegisters.config Phase.field second)
          (stepAux_withStack id memo (CertificateDataTraversal.machine.m phase)
            state (fun key => contents (some key))))

noncomputable def captured_walk (takeSecond second : Bool) (selected : second = takeSecond)
    (value : Data) (input frames output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step
      (config takeSecond (some (.field .header)) state second (writeData value input) frames output memo)
      (some (config takeSecond (some (.field .complete)) (finalState value) second input frames
        ((postorderWire value).reverse ++ output) ((encodeData value).reverse ++ memo)))
      (scanCost value) := by
  have run := PrefixField.walkInto (machine takeSecond).step (embedCaptured takeSecond second)
    (steps := by
      intro source allowed
      rcases allowed with header | number | ⟨complete, _⟩
      · exact captured_step takeSecond second selected .header (by decide) (by decide) source header
      · exact captured_step takeSecond second selected .number (by decide) (by decide) source number
      · exact captured_step takeSecond second selected .complete (by decide) (by decide) source complete)
    value input frames output memo state
  simpa only [embedCaptured_config, Option.map_some] using run

noncomputable def ignored_walk (takeSecond second : Bool) (unselected : second ≠ takeSecond)
    (value : Data) (input frames output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step
      (config takeSecond (some (.field .header)) state second (writeData value input) frames output memo)
      (some (config takeSecond (some (.field .complete)) (finalState value) second input frames
        ((postorderWire value).reverse ++ output) memo)) (scanCost value) := by
  have run := PrefixField.walkInto (machine takeSecond).step (embedIgnored takeSecond second memo)
    (steps := by
      intro source allowed
      rcases allowed with header | number | ⟨complete, _⟩
      · exact ignored_step takeSecond second unselected memo .header (by decide) (by decide) source header
      · exact ignored_step takeSecond second unselected memo .number (by decide) (by decide) source number
      · exact ignored_step takeSecond second unselected memo .complete (by decide) (by decide) source complete)
    value input frames output [] state
  simpa only [embedIgnored_config, Option.map_some] using run

def retained (takeSecond second : Bool) (value : Data) (memo : List Alphabet) : List Alphabet :=
  if second = takeSecond then (encodeData value).reverse ++ memo else memo

noncomputable def walk (takeSecond second : Bool) (value : Data)
    (input frames output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step
      (config takeSecond (some (.field .header)) state second (writeData value input) frames output memo)
      (some (config takeSecond (some (.field .complete)) (finalState value) second input frames
        ((postorderWire value).reverse ++ output) (retained takeSecond second value memo)))
      (scanCost value) := by
  by_cases selected : second = takeSecond
  · simpa only [retained, if_pos selected] using captured_walk takeSecond second selected value input frames output memo state
  · simpa only [retained, if_neg selected] using ignored_walk takeSecond second selected value input frames output memo state

local macro "product_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, parserBody, config,
    Mettapedia.Computability.StackMachineRegisters.extend,
    Mettapedia.Computability.StackMachineRegisters.withStack,
    PrefixField.machine, PrefixField.original, PrefixField.capture, PrefixField.afterRead,
    CertificateDataTraversal.machine, Turing.TM2.step, Turing.TM2.stepAux, Function.update]
  all_goals first
    | rfl
    | (congr 2; funext key; cases key with
       | none => simp [Function.update]
       | some key => cases key <;> simp [Function.update])))

theorem start_pair (takeSecond : Bool) (input : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .start) none false (4 :: input) [] [] []) =
      some (config takeSecond (some (.field .header)) (some 4) false input [] [] []) := by product_step

theorem complete_empty (takeSecond second : Bool) (state : Option Alphabet)
    (input output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .complete)) state second input [] output memo) =
      some (config takeSecond (some (.field .checkTail)) none second input [] output memo) := by
  cases takeSecond <;> cases second <;> product_step

theorem first_done (takeSecond : Bool) (input output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .checkTail)) none false input [] output memo) =
      some (config takeSecond (some (.field .header)) none true input [] output memo) := by product_step

theorem second_tail (takeSecond : Bool) (output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .checkTail)) none true [] [] output memo) =
      some (config takeSecond (some .clearOutput) none true [] [] output memo) := by product_step

theorem clear_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (input frames output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .clearOutput) state second input frames (head :: output) memo) =
      some (config takeSecond (some .clearOutput) (some head) second input frames output memo) := by product_step

theorem clear_nil (takeSecond second : Bool) (state : Option Alphabet)
    (input frames memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .clearOutput) state second input frames [] memo) =
      some (config takeSecond (some .restoreMemo) none second input frames [] memo) := by product_step

noncomputable def clearRun (takeSecond second : Bool) (output input frames memo : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some .clearOutput) state second input frames output memo)
      (some (config takeSecond (some .restoreMemo) none second input frames [] memo)) (output.length + 1) := by
  induction output generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (clear_nil takeSecond second state input frames memo)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (clear_cons takeSecond second state head input frames tail memo)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem restore_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (input frames tail : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .restoreMemo) state second input frames [] (head :: tail)) =
      some (config takeSecond (some .restoreMemo) (some head) second (head :: input) frames [] tail) := by product_step

theorem restore_nil (takeSecond second : Bool) (state : Option Alphabet) (input frames : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .restoreMemo) state second input frames [] []) =
      some (config takeSecond none none false (1 :: input) frames [] []) := by product_step

noncomputable def restoreRun (takeSecond second : Bool) (memo input frames : List Alphabet)
    (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some .restoreMemo) state second input frames [] memo)
      (some (config takeSecond none none false (1 :: memo.reverse ++ input) frames [] [])) (memo.length + 1) := by
  induction memo generalizing input state with
  | nil => simpa using SymbolMapMachine.oneStep (restore_nil takeSecond second state input frames)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (restore_cons takeSecond second state head input frames tail)
      have rest := ih (head :: input) (some head)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem init_eq (takeSecond : Bool) (input : List Alphabet) :
    initList (machine takeSecond) input = config takeSecond (some .start) none false input [] [] [] := by
  simp only [initList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp
  | some key =>
      cases key <;> simp
      all_goals intro impossible; cases impossible

theorem halt_eq (takeSecond : Bool) (output : List Alphabet) :
    haltList (machine takeSecond) output = config takeSecond none none false output [] [] [] := by
  simp only [haltList, machine, config]
  congr 1
  funext key
  cases key with
  | none => simp
  | some key =>
      cases key <;> simp
      all_goals intro impossible; cases impossible

def selected (takeSecond : Bool) (first second : Data) : Data :=
  if takeSecond then second else first

theorem retained_selected (takeSecond : Bool) (first second : Data) :
    retained takeSecond true second (retained takeSecond false first []) =
      (encodeData (selected takeSecond first second)).reverse := by
  cases takeSecond <;> simp [retained, selected]

/-- The enclosing caller gets the original suffix back at the boundary after
both fields. The only memo is the selected original byte prefix. -/
noncomputable def fields (takeSecond : Bool) (first second : Data) (suffix : List Alphabet) :
    EvalsToInTime (machine takeSecond).step
      (config takeSecond (some .start) none false (writeData (.pair first second) suffix) [] [] [])
      (some (config takeSecond (some (.field .checkTail)) none true suffix []
        ((postorderWire second).reverse ++ (postorderWire first).reverse)
        (encodeData (selected takeSecond first second)).reverse))
      (scanCost first + scanCost second + 4) := by
  have start := SymbolMapMachine.oneStep (start_pair takeSecond (writeData first (writeData second suffix)))
  have left := walk takeSecond false first (writeData second suffix) [] [] [] (some 4)
  simp only [List.append_nil] at left
  have leftDone := SymbolMapMachine.oneStep (complete_empty takeSecond false (finalState first)
    (writeData second suffix) (postorderWire first).reverse (retained takeSecond false first []))
  have separator := SymbolMapMachine.oneStep (first_done takeSecond (writeData second suffix)
    (postorderWire first).reverse (retained takeSecond false first []))
  have right := walk takeSecond true second suffix [] (postorderWire first).reverse
    (retained takeSecond false first []) none
  rw [retained_selected] at right
  have rightDone := SymbolMapMachine.oneStep (complete_empty takeSecond true (finalState second) suffix
    ((postorderWire second).reverse ++ (postorderWire first).reverse)
    (encodeData (selected takeSecond first second)).reverse)
  have a := EvalsToInTime.trans _ _ _ _ _ _ start left
  have b := EvalsToInTime.trans _ _ _ _ _ _ a leftDone
  have c := EvalsToInTime.trans _ _ _ _ _ _ b separator
  have d := EvalsToInTime.trans _ _ _ _ _ _ c right
  have e := EvalsToInTime.trans _ _ _ _ _ _ d rightDone
  convert e using 1
  · rfl
  · omega

/-- Both original fields are parsed before the selected physical prefix is
returned. All parser frames and temporary output are cleared. -/
noncomputable def outputs (takeSecond : Bool) (first second : Data) :
    TM2OutputsInTime (machine takeSecond) (encodeData (.pair first second))
      (some ((1 :: encodeData (selected takeSecond first second)) : List Alphabet))
      (scanCost first + scanCost second + dataWeight first + dataWeight second +
        dataWeight (selected takeSecond first second) + 7) := by
  have parsed :=  fields takeSecond first second []
  have tail := SymbolMapMachine.oneStep (second_tail takeSecond
    ((postorderWire second).reverse ++ (postorderWire first).reverse)
    (encodeData (selected takeSecond first second)).reverse)
  have clear := clearRun takeSecond true ((postorderWire second).reverse ++ (postorderWire first).reverse)
    [] [] (encodeData (selected takeSecond first second)).reverse none
  have restore := restoreRun takeSecond true (encodeData (selected takeSecond first second)).reverse [] [] none
  simp only [List.reverse_reverse, List.append_nil] at restore
  have a := EvalsToInTime.trans _ _ _ _ _ _ parsed tail
  have b := EvalsToInTime.trans _ _ _ _ _ _ a clear
  have c := EvalsToInTime.trans _ _ _ _ _ _ b restore
  change EvalsToInTime _ (initList (machine takeSecond) (encodeData (.pair first second)))
    (some (haltList (machine takeSecond) ((1 :: encodeData (selected takeSecond first second)) : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert c using 1
  · rfl
  · simp only [List.length_append, List.length_reverse, postorderWire_length,
      encodeData, writeData_length, List.length_nil]
    omega

noncomputable def computable (takeSecond : Bool) : TM2ComputableInPolyTime
    (fun pair : Data × Data => encodeData (.pair pair.1 pair.2))
    (fun word : List Alphabet => word) (fun pair => 1 :: encodeData (selected takeSecond pair.1 pair.2)) where
  tm := machine takeSecond
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C 4 * X + C 3
  outputsFun pair := by
    change TM2OutputsInTime (machine takeSecond) ((encodeData (.pair pair.1 pair.2)).map id)
      (some ((1 :: encodeData (selected takeSecond pair.1 pair.2)).map id)) _
    simp only [List.map_id_fun]
    apply BinaryReferenceMachine.within (outputs takeSecond pair.1 pair.2)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      encodeData, writeData_length, List.length_nil, dataWeight]
    have first := scanCost_add_one_le pair.1
    have second := scanCost_add_one_le pair.2
    have retainedBound : dataWeight (selected takeSecond pair.1 pair.2) ≤ dataWeight pair.1 + dataWeight pair.2 := by
      cases takeSecond <;> simp [selected]
    omega

/-- A success tag followed by the original encoding, without a second codec. -/
def successEncoding {A : Type} (codec : Codec A) : A → List Alphabet :=
  fun value => 1 :: encodeWith codec value

noncomputable def selectFirstCodec {A B : Type} (first : Codec A) (second : Codec B) :
    TM2ComputableInPolyTime (encodeWith (Codec.prod first second))
      (successEncoding first) (fun pair : A × B => pair.1) where
  tm := machine false
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := (computable false).time
  outputsFun pair := (computable false).outputsFun (first.put pair.1, second.put pair.2)

noncomputable def selectSecondCodec {A B : Type} (first : Codec A) (second : Codec B) :
    TM2ComputableInPolyTime (encodeWith (Codec.prod first second))
      (successEncoding second) (fun pair : A × B => pair.2) where
  tm := machine true
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := (computable true).time
  outputsFun pair := (computable true).outputsFun (first.put pair.1, second.put pair.2)

theorem selected_length_le (takeSecond : Bool) (first second : Data) :
    (encodeData (selected takeSecond first second)).length ≤ (encodeData (.pair first second)).length := by
  simp only [encodeData, writeData_length, List.length_nil, dataWeight]
  cases takeSecond <;> simp [selected]
  all_goals omega

theorem reject_input_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (input frames output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectInput)) state second (head :: input) frames output memo) =
      some (config takeSecond (some (.field .rejectInput)) (some head) second input frames output memo) := by
  cases takeSecond <;> cases second <;> product_step

theorem reject_input_nil (takeSecond second : Bool) (state : Option Alphabet)
    (frames output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectInput)) state second [] frames output memo) =
      some (config takeSecond (some (.field .rejectFrames)) none second [] frames output memo) := by
  cases takeSecond <;> cases second <;> product_step

theorem reject_frames_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (frames output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectFrames)) state second [] (head :: frames) output memo) =
      some (config takeSecond (some (.field .rejectFrames)) (some head) second [] frames output memo) := by
  cases takeSecond <;> cases second <;> product_step

theorem reject_frames_nil (takeSecond second : Bool) (state : Option Alphabet) (output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectFrames)) state second [] [] output memo) =
      some (config takeSecond (some (.field .rejectOutput)) none second [] [] output memo) := by
  cases takeSecond <;> cases second <;> product_step

theorem reject_output_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectOutput)) state second [] [] (head :: output) memo) =
      some (config takeSecond (some (.field .rejectOutput)) (some head) second [] [] output memo) := by product_step

theorem reject_output_nil (takeSecond second : Bool) (state : Option Alphabet) (memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .rejectOutput)) state second [] [] [] memo) =
      some (config takeSecond (some .rejectMemo) none second [] [] [] memo) := by product_step

theorem reject_memo_cons (takeSecond second : Bool) (state : Option Alphabet) (head : Alphabet)
    (memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .rejectMemo) state second [] [] [] (head :: memo)) =
      some (config takeSecond (some .rejectMemo) (some head) second [] [] [] memo) := by product_step

theorem reject_memo_nil (takeSecond second : Bool) (state : Option Alphabet) :
    (machine takeSecond).step (config takeSecond (some .rejectMemo) state second [] [] [] []) =
      some (config takeSecond none none false [0] [] [] []) := by product_step

noncomputable def rejectMemoRun (takeSecond second : Bool) (memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some .rejectMemo) state second [] [] [] memo)
      (some (config takeSecond none none false [0] [] [] [])) (memo.length + 1) := by
  induction memo generalizing state with
  | nil => simpa using SymbolMapMachine.oneStep (reject_memo_nil takeSecond second state)
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_memo_cons takeSecond second state head tail)
      have rest := ih (some head)
      simpa using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def rejectOutputRun (takeSecond second : Bool) (output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some (.field .rejectOutput)) state second [] [] output memo)
      (some (config takeSecond none none false [0] [] [] [])) (output.length + memo.length + 2) := by
  induction output generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (reject_output_nil takeSecond second state memo)
      have rest := rejectMemoRun takeSecond second memo none
      convert EvalsToInTime.trans _ _ _ _ _ _ first rest using 1
      simp only [List.length_nil]; omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_output_cons takeSecond second state head tail memo)
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def rejectFramesRun (takeSecond second : Bool) (frames output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some (.field .rejectFrames)) state second [] frames output memo)
      (some (config takeSecond none none false [0] [] [] [])) (frames.length + output.length + memo.length + 3) := by
  induction frames generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (reject_frames_nil takeSecond second state output memo)
      have rest := rejectOutputRun takeSecond second output memo none
      convert EvalsToInTime.trans _ _ _ _ _ _ first rest using 1
      simp only [List.length_nil]; omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_frames_cons takeSecond second state head tail output memo)
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def rejectRun (takeSecond second : Bool) (input frames output memo : List Alphabet) (state : Option Alphabet) :
    EvalsToInTime (machine takeSecond).step (config takeSecond (some (.field .rejectInput)) state second input frames output memo)
      (some (config takeSecond none none false [0] [] [] []))
      (input.length + frames.length + output.length + memo.length + 4) := by
  induction input generalizing state with
  | nil =>
      have first := SymbolMapMachine.oneStep (reject_input_nil takeSecond second state frames output memo)
      have rest := rejectFramesRun takeSecond second frames output memo none
      convert EvalsToInTime.trans _ _ _ _ _ _ first rest using 1
      simp only [List.length_nil]; omega
  | cons head tail ih =>
      have first := SymbolMapMachine.oneStep (reject_input_cons takeSecond second state head tail frames output memo)
      have rest := ih (some head)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem start_not_pair (takeSecond : Bool) (head : Alphabet) (notPair : head ≠ 4) (input : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some .start) none false (head :: input) [] [] []) =
      some (config takeSecond (some (.field .rejectInput)) (some head) false input [] [] []) := by
  have notEq : ((some head : Option Alphabet) == some 4) = false := by simp [notPair]
  simp [FinTM2.step, machine, config, TM2.step, TM2.stepAux, notEq]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key =>
      cases key <;> simp [Function.update]
      all_goals intro impossible; cases impossible

noncomputable def notPairOutputs (takeSecond : Bool) (head : Alphabet) (notPair : head ≠ 4) (tail : List Alphabet) :
    TM2OutputsInTime (machine takeSecond) ((head :: tail) : List Alphabet) (some ([0] : List Alphabet)) (tail.length + 5) := by
  have first := SymbolMapMachine.oneStep (start_not_pair takeSecond head notPair tail)
  have rest := rejectRun takeSecond false tail [] [] [] (some head)
  change EvalsToInTime _ (initList (machine takeSecond) ((head :: tail) : List Alphabet))
    (some (haltList (machine takeSecond) ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  simpa using EvalsToInTime.trans _ _ _ _ _ _ first rest

theorem second_trailing (takeSecond : Bool) (head : Alphabet) (tail output memo : List Alphabet) :
    (machine takeSecond).step (config takeSecond (some (.field .checkTail)) none true (head :: tail) [] output memo) =
      some (config takeSecond (some (.field .rejectInput)) (some head) true tail [] output memo) := by product_step

/-- Trailing symbols refuse the whole packet, even after both fields parsed
successfully. The previously captured selection is cleared before refusal. -/
noncomputable def trailingOutputs (takeSecond : Bool) (first second : Data) (head : Alphabet) (suffix : List Alphabet) :
    TM2OutputsInTime (machine takeSecond) (writeData (.pair first second) (head :: suffix))
      (some ([0] : List Alphabet))
      (scanCost first + scanCost second + dataWeight first + dataWeight second +
        dataWeight (selected takeSecond first second) + suffix.length + 9) := by
  have parsed := fields takeSecond first second (head :: suffix)
  have tail := SymbolMapMachine.oneStep (second_trailing takeSecond head suffix
    ((postorderWire second).reverse ++ (postorderWire first).reverse)
    (encodeData (selected takeSecond first second)).reverse)
  have refused := rejectRun takeSecond true suffix []
    ((postorderWire second).reverse ++ (postorderWire first).reverse)
    (encodeData (selected takeSecond first second)).reverse (some head)
  have a := EvalsToInTime.trans _ _ _ _ _ _ parsed tail
  have b := EvalsToInTime.trans _ _ _ _ _ _ a refused
  change EvalsToInTime _ (initList (machine takeSecond) (writeData (.pair first second) (head :: suffix)))
    (some (haltList (machine takeSecond) ([0] : List Alphabet))) _
  rw [init_eq, halt_eq]
  convert b using 1
  simp only [List.length_append, List.length_reverse, postorderWire_length,
    encodeData, writeData_length, List.length_nil]
  omega

end ProductField

namespace PatternTokenField

/-- Structural token spelling from the existing flat Pattern codec. The same
lexical tag may serve different grammar positions; grammar and scope admission
remain separate from this complete-token classification. -/
def tags : Fin 14 → String :=
  !["a", "h", "z", "l", "m", "s", "c", "b", "v", "n", "o", "0", "1", "e"]

abbrev words := Dictionary.words Codec.string tags
@[reducible, macro_inline] def machine := Mettapedia.Computability.FiniteWordClassifier.machine words
abbrev result := Dictionary.result Codec.string tags
abbrev output := Dictionary.output Codec.string tags

/-- Classification retains the exact original UTF-8 token field. -/
noncomputable def outputs (token : String) := Dictionary.outputs Codec.string tags token
noncomputable def computable := Dictionary.computable Codec.string tags

end PatternTokenField

namespace Controls

theorem pair_wire_changes :
    1 :: postorderWire (.pair (.atom 0) (.atom 1)) =
      [1, 3, 2, 3, 1, 2, 4] := rfl

theorem pair_wire_not_prefix :
    postorderWire (.pair (.atom 0) (.atom 1)) ≠ encodeData (.pair (.atom 0) (.atom 1)) := by decide

theorem reversed_children_refused :
    decodeFrames (postorderWire (.atom 1) ++ postorderWire (.atom 0) ++ [4]) ≠
      some (.pair (.atom 0) (.atom 1)) := by decide

theorem extra_frame_refused : decodeFrames [3, 2, 4] = none := by decide

theorem missing_frame_refused : decodeFrames [3, 2, 3, 1, 2] = none := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.CertificateDataTraversal

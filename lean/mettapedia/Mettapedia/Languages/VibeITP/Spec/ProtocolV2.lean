import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mettapedia.Languages.VibeITP.Spec.ProtocolSuccess
import Mettapedia.Languages.VibeITP.Spec.Encode
import Mettapedia.Languages.VibeITP.Spec.SimultaneousInstantiation

/-!
# Versioned simultaneous-instantiation protocol

The previous instruction type and its decoder remain pinned to opcodes 0--25.
This extension admits opcode 26, whose operand layout groups all symbol slots
before all value slots. It uses the existing state, phase guards and placement
operations. The new theorem operation is the simultaneous reference, not a
sequence of single substitutions. Native guest refinement and a corresponding
presentation rule remain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Spec.ProtocolV2

inductive Instruction where
  | legacy (instruction : Instr)
  | instantiateMany (source : Nat) (assignments : List (Nat × Nat)) (destination : Nat)
deriving Repr, DecidableEq

def Instruction.opcode : Instruction → Nat
  | .legacy instruction => instruction.opcode
  | .instantiateMany .. => 26

def Instruction.payload : Instruction → List UInt8
  | .legacy instruction => instruction.payload
  | .instantiateMany source assignments destination =>
      encodeWord assignments.length ++ encodeWord source ++
      encodeWords (assignments.map Prod.fst) ++ encodeWords (assignments.map Prod.snd) ++
      encodeWord destination

def Instruction.Bounded : Instruction → Prop
  | .legacy instruction => instruction.Bounded
  | .instantiateMany source assignments destination =>
      assignments.length < wordBound ∧ source < wordBound ∧ destination < wordBound ∧
        ∀ assignment ∈ assignments, assignment.1 < wordBound ∧ assignment.2 < wordBound

instance (instruction : Instruction) : Decidable instruction.Bounded := by
  cases instruction with
  | legacy instruction =>
      change Decidable (∀ word ∈ instruction.words, word < wordBound)
      infer_instance
  | instantiateMany source assignments destination =>
      change Decidable (assignments.length < wordBound ∧ source < wordBound ∧
        destination < wordBound ∧ ∀ entry ∈ assignments, entry.1 < wordBound ∧ entry.2 < wordBound)
      infer_instance

def encode (instruction : Instruction) : List UInt8 :=
  UInt8.ofNat instruction.opcode :: instruction.payload

open _root_.Mettapedia.Languages.VibeITP.Spec.Parser in
def decodeMany : Parser Instruction :=
  bind word fun count => bind word fun source =>
    bind (words count) fun symbols => bind (words count) fun values =>
      bind word fun destination => pure (.instantiateMany source (symbols.zip values) destination)

open _root_.Mettapedia.Languages.VibeITP.Spec.Parser in
def decodeOperands (opcode : Nat) : Parser Instruction :=
  if opcode = 26 then decodeMany
  else bind (Spec.decodeOperands opcode) fun instruction => pure (.legacy instruction)

def decodeOne : Parser Instruction
  | [] => .error .truncatedInteger
  | opcode :: rest => decodeOperands opcode.toNat rest

private theorem zip_projections (pairs : List (Nat × Nat)) :
    (pairs.map Prod.fst).zip (pairs.map Prod.snd) = pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => cases pair; simp [ih]

theorem decodeMany_payload (source destination : Nat) (assignments : List (Nat × Nat))
    (rest : List UInt8)
    (bounded : (Instruction.instantiateMany source assignments destination).Bounded) :
    decodeMany ((Instruction.instantiateMany source assignments destination).payload ++ rest) =
      .ok (.instantiateMany source assignments destination, rest) := by
  obtain ⟨countBound, sourceBound, destinationBound, operandsBound⟩ := bounded
  have symbolsBound : ∀ n ∈ assignments.map Prod.fst, n < wordBound := by
    intro n member
    obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp member
    exact (operandsBound pair inPairs).1
  have valuesBound : ∀ n ∈ assignments.map Prod.snd, n < wordBound := by
    intro n member
    obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp member
    exact (operandsBound pair inPairs).2
  simp only [Instruction.payload, List.append_assoc, decodeMany]
  rw [bind_ok (word_encodeWord _ _ countBound), bind_ok (word_encodeWord _ _ sourceBound)]
  have symbolsRead := words_encodeWords (assignments.map Prod.fst)
    (encodeWords (assignments.map Prod.snd) ++ encodeWord destination ++ rest) symbolsBound
  simp only [List.length_map, List.append_assoc] at symbolsRead
  rw [bind_ok symbolsRead]
  have valuesRead := words_encodeWords (assignments.map Prod.snd)
    (encodeWord destination ++ rest) valuesBound
  simp only [List.length_map] at valuesRead
  rw [bind_ok valuesRead, bind_ok (word_encodeWord _ _ destinationBound), zip_projections]
  rfl

theorem decodeOne_encode (instruction : Instruction) (rest : List UInt8)
    (bounded : instruction.Bounded) :
    decodeOne (encode instruction ++ rest) = .ok (instruction, rest) := by
  cases instruction with
  | legacy instruction =>
      have opcode : (UInt8.ofNat instruction.opcode).toNat = instruction.opcode := by
        cases instruction <;> rfl
      have different : instruction.opcode ≠ 26 := by cases instruction <;> simp [Instr.opcode]
      simp only [encode, Instruction.opcode, Instruction.payload, List.cons_append,
        decodeOne, opcode, decodeOperands, different, if_false]
      exact bind_ok (decodeOperands_payload instruction rest bounded)
  | instantiateMany source assignments destination =>
      change decodeMany ((Instruction.instantiateMany source assignments destination).payload ++ rest) = _
      exact decodeMany_payload source destination assignments rest bounded

open _root_.Mettapedia.Languages.VibeITP.Spec.Parser in
theorem decodeOperands_consumes (opcode : Nat) : (decodeOperands opcode).Consumes := by
  unfold decodeOperands
  split
  · unfold decodeMany
    repeat' (first
      | exact pure_consumes _
      | exact word_consumes
      | exact words_consumes _
      | refine bind_consumes ?_ fun _ => ?_)
  · exact bind_consumes (Spec.decodeOperands_consumes opcode) fun _ => pure_consumes _

def decodeStream : Nat → List UInt8 → Except DecodeError (List Instruction)
  | _, [] => .ok []
  | 0, _ :: _ => .ok []
  | fuel + 1, opcode :: rest =>
      match decodeOperands opcode.toNat rest with
      | .error error => .error error
      | .ok (instruction, suffix) =>
          match decodeStream fuel suffix with
          | .error error => .error error
          | .ok instructions => .ok (instruction :: instructions)

def decodeFile (bytes : List UInt8) : Except DecodeError (List Instruction) :=
  decodeStream bytes.length bytes

theorem decodeStream_fuel : ∀ (fuel fuel' : Nat) (bytes : List UInt8),
    bytes.length ≤ fuel → bytes.length ≤ fuel' →
      decodeStream fuel bytes = decodeStream fuel' bytes
  | _, _, [], _, _ => by simp [decodeStream]
  | 0, _, _ :: _, bound, _ => by simp at bound
  | _, 0, _ :: _, _, bound => by simp at bound
  | fuel + 1, fuel' + 1, opcode :: rest, bound, bound' => by
      simp only [decodeStream]
      split
      · rfl
      · rename_i instruction suffix decoded
        have consumes := decodeOperands_consumes opcode.toNat rest instruction suffix decoded
        simp only [List.length_cons] at bound bound'
        rw [decodeStream_fuel fuel fuel' suffix (by omega) (by omega)]

def encodeFile (instructions : List Instruction) : List UInt8 := instructions.flatMap encode

theorem decodeStream_encodeFile : ∀ (instructions : List Instruction) (fuel : Nat),
    (∀ instruction ∈ instructions, instruction.Bounded) →
    (encodeFile instructions).length ≤ fuel →
      decodeStream fuel (encodeFile instructions) = .ok instructions
  | [], fuel, _, _ => by cases fuel <;> rfl
  | instruction :: rest, fuel, bounded, room => by
      cases fuel with
      | zero => simp [encodeFile, encode] at room
      | succ fuel =>
          have decoded := decodeOne_encode instruction (encodeFile rest) (bounded instruction (by simp))
          simp only [decodeOne, encode, List.cons_append, encodeFile] at decoded
          simp only [encodeFile, List.flatMap_cons, encode, List.cons_append, decodeStream]
          rw [decoded]
          have following := decodeStream_encodeFile rest fuel
            (fun child member => bounded child (by simp [member]))
            (by simp [encodeFile, encode] at room ⊢; omega)
          simp only [encodeFile] at following
          simp only [following]

theorem decodeFile_encodeFile (instructions : List Instruction)
    (bounded : ∀ instruction ∈ instructions, instruction.Bounded) :
    decodeFile (encodeFile instructions) = .ok instructions :=
  decodeStream_encodeFile instructions _ bounded (Nat.le_refl _)

theorem decodeOperands_legacy {opcode : Nat} {bytes suffix : List UInt8} {instruction : Instr}
    (accepted : Spec.decodeOperands opcode bytes = .ok (instruction, suffix)) :
    decodeOperands opcode bytes = .ok (.legacy instruction, suffix) := by
  by_cases newOpcode : opcode = 26
  · subst opcode
    simp [Spec.decodeOperands, Parser.fail] at accepted
  · simp only [decodeOperands, newOpcode, if_false]
    exact bind_ok accepted

/-- Every previously decoded stream keeps its original instructions, including
noncanonical word encodings accepted by the previous decoder. -/
theorem decodeStream_legacy : ∀ (fuel : Nat) (bytes : List UInt8) (instructions : List Instr),
    Spec.decodeStream fuel bytes = .ok instructions →
      decodeStream fuel bytes = .ok (instructions.map Instruction.legacy)
  | fuel, [], instructions, accepted => by
      cases fuel <;> simp [Spec.decodeStream] at accepted <;> subst instructions <;> rfl
  | 0, _ :: _, instructions, accepted => by
      simp [Spec.decodeStream] at accepted
      subst instructions
      rfl
  | fuel + 1, opcode :: rest, instructions, accepted => by
      simp only [Spec.decodeStream] at accepted
      cases first : Spec.decodeOperands opcode.toNat rest with
      | error error => simp [first] at accepted
      | ok result =>
          rcases result with ⟨instruction, suffix⟩
          simp only [first] at accepted
          cases following : Spec.decodeStream fuel suffix with
          | error error => simp [following] at accepted
          | ok tail =>
              simp only [following, Except.ok.injEq] at accepted
              subst instructions
              simp only [decodeStream, decodeOperands_legacy first]
              rw [decodeStream_legacy fuel suffix tail following]
              rfl

theorem decodeFile_legacy {bytes : List UInt8} {instructions : List Instr}
    (accepted : Spec.decodeFile bytes = .ok instructions) :
    decodeFile bytes = .ok (instructions.map Instruction.legacy) :=
  decodeStream_legacy bytes.length bytes instructions accepted

/-- Source operands are read in native order: theorem, all symbols, all terms.
Validation of symbol kinds and replacement depths follows those reads. -/
def executeMany (before : State) (source : Nat) (assignments : List (Nat × Nat))
    (destination : Nat) : StepM State := do
  before.inProofs .instantiate
  let statement ← need .theorem (before.theorems source)
  let symbols ← assignments.mapM fun pair => need .symbol (before.symbols pair.1)
  let values ← assignments.mapM fun pair => need .term (before.terms pair.2)
  match slotIds symbols with
  | none => .error .theoremFailed
  | some heads =>
      match SimultaneousInstantiation.statement before.sig (heads.zip values) statement with
      | none => .error .theoremFailed
      | some result => before.placeTheorem destination result

def execute (before : State) : Instruction → Option (StepM State)
  | .legacy instruction => Spec.execute before instruction
  | .instantiateMany source assignments destination =>
      some (executeMany before source assignments destination)

/-- Legacy runs retain their exact errors and unsupported-execution outcome. -/
theorem execute_legacy (before : State) (instruction : Instr) :
    execute before (.legacy instruction) = Spec.execute before instruction := rfl

theorem execute_singleton (before : State) (source symbol value destination : Nat) :
    execute before (.instantiateMany source [(symbol, value)] destination) =
      Spec.execute before (.thmInstantiate source symbol value destination) := by
  simp only [execute, executeMany, Spec.execute]
  cases phase : before.inProofs .instantiate with
  | error error => simp [ bind, Except.bind]
  | ok phaseDone =>
      cases phaseDone
      cases proof : need .theorem (before.theorems source) with
      | error error => simp [ bind, Except.bind]
      | ok statement =>
          cases head : need .symbol (before.symbols symbol) with
          | error error => simp [ head, bind, Except.bind, List.mapM_cons]
          | ok entry =>
              cases term : need .term (before.terms value) with
              | error error => simp [ head, term, bind, Except.bind, pure, Except.pure, List.mapM_cons, List.mapM_nil]
              | ok replacement =>
                  cases entry with
                  | bvarMarker =>
                      simp [ head, term, bind, Except.bind, pure, Except.pure,
                        List.mapM_cons, List.mapM_nil, slotIds]
                  | literalMarker =>
                      simp [ head, term, bind, Except.bind, pure, Except.pure,
                        List.mapM_cons, List.mapM_nil, slotIds]
                  | sym F =>
                      simp [ head, term, bind, Except.bind, pure, Except.pure,
                        List.mapM_cons, List.mapM_nil, slotIds,
                        SimultaneousInstantiation.statement_singleton]
                      cases instantiateStatement before.sig F replacement statement <;> rfl

/-- Successful publication retains the exact source theorem, every slot read,
the resolved simultaneous result and the original placement operation. -/
theorem executeMany_success {before after : State} (source destination : Nat)
    (assignments : List (Nat × Nat))
    (accepted : executeMany before source assignments destination = .ok after) :
    ∃ statement symbols values heads result,
      before.phase = .proofs ∧ before.theorems source = some statement ∧
      assignments.mapM (fun pair => need .symbol (before.symbols pair.1)) = .ok symbols ∧
      assignments.mapM (fun pair => need .term (before.terms pair.2)) = .ok values ∧
      slotIds symbols = some heads ∧
      SimultaneousInstantiation.statement before.sig (heads.zip values) statement = some result ∧
      before.placeTheorem destination result = .ok after := by
  unfold executeMany at accepted
  obtain ⟨phaseDone, phase, following⟩ := (ProtocolSuccess.bind_ok_iff _ _ _).mp accepted
  cases phaseDone
  obtain ⟨statement, theoremRead, following⟩ := (ProtocolSuccess.bind_ok_iff _ _ _).mp following
  obtain ⟨symbols, symbolsRead, following⟩ := (ProtocolSuccess.bind_ok_iff _ _ _).mp following
  obtain ⟨values, valuesRead, following⟩ := (ProtocolSuccess.bind_ok_iff _ _ _).mp following
  cases identities : slotIds symbols with
  | none => simp [identities] at following
  | some heads =>
      simp only [identities] at following
      cases computed : SimultaneousInstantiation.statement before.sig (heads.zip values) statement with
      | none => simp [computed] at following
      | some result =>
          simp only [computed] at following
          exact ⟨statement, symbols, values, heads, result,
            (ProtocolSuccess.inProofs_ok_iff _ _).mp phase,
            (ProtocolSuccess.need_ok_iff _ _ _).mp theoremRead,
            symbolsRead, valuesRead, identities, computed, following⟩

theorem executeMany_updates_only_theorem {before after : State} (source destination : Nat)
    (assignments : List (Nat × Nat))
    (accepted : executeMany before source assignments destination = .ok after) :
    ∃ result, before.theorems destination = none ∧
      after = { before with theorems := setSlot before.theorems destination (some result) } := by
  obtain ⟨_, _, _, _, result, _, _, _, _, _, _, placed⟩ :=
    executeMany_success source destination assignments accepted
  cases occupied : before.theorems destination with
  | some old => simp [State.placeTheorem, occupied] at placed
  | none =>
      simp only [State.placeTheorem, occupied, Option.isSome_none, Bool.false_eq_true,
        if_false, Except.ok.injEq] at placed
      exact ⟨result, rfl, placed.symm⟩

def runInstrs : State → Nat → List Instruction → RunResult
  | state, _, [] => .ok state
  | state, index, instruction :: rest =>
      match execute state instruction with
      | none => .unsupported index
      | some (.error error) => .error index error
      | some (.ok next) => runInstrs next (index + 1) rest

theorem runInstrs_legacy (instructions : List Instr) (state : State) (index : Nat) :
    runInstrs state index (instructions.map Instruction.legacy) =
      Spec.runInstrs state index instructions := by
  induction instructions generalizing state index with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.map_cons, runInstrs, Spec.runInstrs, execute]
      cases Spec.execute state instruction with
      | none => rfl
      | some next =>
          cases next with
          | error error => rfl
          | ok state => exact ih state (index + 1)

def runFiles : State → Nat → List (List Instruction) → FilesResult
  | state, _, [] => .ok state
  | state, file, instructions :: rest =>
      match runInstrs state 0 instructions with
      | .ok next => runFiles next (file + 1) rest
      | .error index error => .stop (.rejected file index error)
      | .unsupported index => .stop (.unsupported file index)

def decodeFiles : Nat → List (List UInt8) →
    Except (Nat × DecodeError) (List (List Instruction))
  | _, [] => .ok []
  | file, bytes :: rest =>
      match decodeFile bytes with
      | .error error => .error (file, error)
      | .ok instructions =>
          match decodeFiles (file + 1) rest with
          | .error error => .error error
          | .ok decoded => .ok (instructions :: decoded)

/-- All files are decoded before execution, preserving malformed-input priority.
The old verdict type continues to distinguish completion from full success. -/
def checkRun (setup proofs : List (List UInt8)) : Verdict :=
  match decodeFiles 0 (setup ++ proofs) with
  | .error (file, error) => .malformed file error
  | .ok decoded =>
      match runFiles initialState 0 (decoded.take setup.length) with
      | .stop verdict => verdict
      | .ok state =>
          if proofs.isEmpty then .setupOnly state.openChallenges
          else
            match runFiles (enterProofs state) setup.length (decoded.drop setup.length) with
            | .stop verdict => verdict
            | .ok final => .proofs final.setupChallenges final.proofChallenges final.openChallenges

#print axioms decodeMany_payload
#print axioms decodeOne_encode
#print axioms decodeFile_encodeFile
#print axioms decodeFile_legacy
#print axioms execute_singleton
#print axioms executeMany_updates_only_theorem
#print axioms runInstrs_legacy

end Mettapedia.Languages.VibeITP.Spec.ProtocolV2

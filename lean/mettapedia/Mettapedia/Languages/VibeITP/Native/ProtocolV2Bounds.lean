import Mettapedia.Languages.VibeITP.Spec.ProtocolV2
import Mettapedia.Languages.VibeITP.Native.DecodedBounds

/-!
# Word-domain evidence for versioned byte inputs

Opcode 26 uses the unchanged word codec, so the existing word and vector bounds
apply to both operand groups. This proves the input-domain premise needed by
the reference logical invariant; it does not update the native guest decoder.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Native.ProtocolV2Bounds

open Spec Spec.ProtocolV2

theorem many_establishes : decodeMany.Establishes Instruction.Bounded := by
  unfold decodeMany
  refine Spec.Parser.bind_establishes _ _ _ _ DecodedBounds.word_establishes ?_
  intro count countBound
  refine Spec.Parser.bind_establishes _ _ _ _ DecodedBounds.word_establishes ?_
  intro source sourceBound
  refine Spec.Parser.bind_establishes _ _ _ _ (DecodedBounds.words_establishes count) ?_
  intro symbols symbolsValid
  refine Spec.Parser.bind_establishes _ _ _ _ (DecodedBounds.words_establishes count) ?_
  intro values valuesValid
  refine Spec.Parser.bind_establishes _ _ _ _ DecodedBounds.word_establishes ?_
  intro destination destinationBound
  apply Spec.Parser.pure_establishes
  refine ⟨?_, sourceBound, destinationBound, ?_⟩
  · simpa only [List.length_zip, symbolsValid.1, valuesValid.1, Nat.min_self] using countBound
  · intro pair member
    have both := List.of_mem_zip member
    exact ⟨symbolsValid.2 pair.1 both.1, valuesValid.2 pair.2 both.2⟩

theorem operands_establishes (opcode : Nat) :
    (ProtocolV2.decodeOperands opcode).Establishes Instruction.Bounded := by
  unfold ProtocolV2.decodeOperands
  split
  · exact many_establishes
  · refine Spec.Parser.bind_establishes _ _ _ _ (DecodedBounds.operands_establishes opcode) ?_
    intro instruction bounded
    exact Spec.Parser.pure_establishes _ _ ((instruction.bounded_iff_machineBounded).mpr bounded)

theorem stream_establishes : ∀ (fuel : Nat) (bytes : List UInt8) (instructions : List Instruction),
    ProtocolV2.decodeStream fuel bytes = .ok instructions →
      ∀ instruction ∈ instructions, instruction.Bounded
  | fuel, [], instructions, accepted => by
      cases fuel <;> simp [ProtocolV2.decodeStream] at accepted <;> subst instructions <;> simp
  | 0, _ :: _, instructions, accepted => by
      simp [ProtocolV2.decodeStream] at accepted
      subst instructions
      simp
  | fuel + 1, opcode :: rest, instructions, accepted => by
      simp only [ProtocolV2.decodeStream] at accepted
      cases decoded : ProtocolV2.decodeOperands opcode.toNat rest with
      | error error => simp [decoded] at accepted
      | ok result =>
          rcases result with ⟨head, suffix⟩
          simp only [decoded] at accepted
          cases tail : ProtocolV2.decodeStream fuel suffix with
          | error error => simp [tail] at accepted
          | ok remaining =>
              simp only [tail, Except.ok.injEq] at accepted
              subst instructions
              intro instruction member
              rcases List.mem_cons.mp member with newest | previous
              · subst instruction
                exact operands_establishes opcode.toNat rest head suffix decoded
              · exact stream_establishes fuel suffix remaining tail instruction previous

theorem file_establishes (bytes : List UInt8) (instructions : List Instruction)
    (accepted : ProtocolV2.decodeFile bytes = .ok instructions) :
    ∀ instruction ∈ instructions, instruction.Bounded :=
  stream_establishes bytes.length bytes instructions accepted

theorem files_establishes (files : List (List UInt8)) (index : Nat)
    (decoded : List (List Instruction))
    (accepted : ProtocolV2.decodeFiles index files = .ok decoded) :
    ∀ instructions ∈ decoded, ∀ instruction ∈ instructions, instruction.Bounded := by
  induction files generalizing index decoded with
  | nil =>
      have same : [] = decoded := Except.ok.inj accepted
      subst decoded
      simp
  | cons bytes files ih =>
      simp only [ProtocolV2.decodeFiles] at accepted
      cases first : ProtocolV2.decodeFile bytes with
      | error error => simp [first] at accepted
      | ok instructions =>
          simp only [first] at accepted
          cases rest : ProtocolV2.decodeFiles (index + 1) files with
          | error error => simp [rest] at accepted
          | ok remaining =>
              simp only [rest, Except.ok.injEq] at accepted
              subst decoded
              intro batch member
              rcases List.mem_cons.mp member with newest | previous
              · subst batch
                exact file_establishes bytes instructions first
              · exact ih (index + 1) remaining rest batch previous

#print axioms file_establishes
#print axioms files_establishes

end Mettapedia.Languages.VibeITP.Native.ProtocolV2Bounds

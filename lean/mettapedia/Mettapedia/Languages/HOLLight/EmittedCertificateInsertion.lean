import Mettapedia.Languages.HOLLight.ChronologicalInsertion
import Mettapedia.GSLT.LanguageDef.CertificateDataTraversal

/-!
# Insert the original emitted certificate without supplied decoded fields

The packet retains an earlier receipt list and the original certificate word
emitted by relocation. Two original product-field parsers earn the new list
and selected root. Physical retention keeps the packet while these fields are
extracted; field routing then calls chronological insertion. The caller does
not supply the unpacked receipts or root as additional physical inputs.

The contract concerns the codec images accepted by the surrounding admission
boundary. It does not give an arbitrary-malformed-byte refusal theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.EmittedCertificateInsertion

open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open ProofExecution ProofDataEncoding

abbrev Alphabet := Binary.Alphabet

theorem field_length_le {arity : Nat} (packet : Fin arity → List Alphabet)
    (index : Fin arity) : (packet index).length ≤ (Indexed.argumentWire packet).length := by
  have member : (packet index).length ∈
      (List.finRange arity).map (fun index => (packet index).length) :=
    List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  have bound := List.le_sum_of_mem member
  rw [Indexed.argumentWire_length]
  omega

def fields (earlier : List Receipt) (block : ProofSystem.Certificate) : Fin 2 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) earlier, encodeCertificate block]

def inputWire (earlier : List Receipt) (block : ProofSystem.Certificate) : List (Option Alphabet) :=
  Indexed.argumentWire (fields earlier block)

def componentPlan {arity : Nat} (index : Fin arity) : Indexed.Template Alphabet arity := [.inr index]

local instance {arity : Nat} (index : Fin arity) :
    Fintype ((Indexed.machine (componentPlan index)).Γ
      (Indexed.machine (componentPlan index)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((Indexed.machine (componentPlan index)).Γ
      (Indexed.machine (componentPlan index)).k₁) := inferInstanceAs (Inhabited Alphabet)

def parsedMachine {arity : Nat} (index : Fin arity) (second : Bool) :=
  StackMachineComposition.machine (Indexed.machine (componentPlan index))
    (CertificateDataTraversal.ProductField.machine second) (Equiv.refl Alphabet)

local instance {arity : Nat} (index : Fin arity) (second : Bool) :
    Fintype ((parsedMachine index second).Γ (parsedMachine index second).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) :
    Inhabited ((parsedMachine index second).Γ (parsedMachine index second).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def componentMachine {arity : Nat} (index : Fin arity) (second : Bool) :=
  StackMachineComposition.machine (parsedMachine index second)
    BinaryListAppend.stripMachine (Equiv.refl Alphabet)

local instance {arity : Nat} (index : Fin arity) (second : Bool) :
    Fintype ((componentMachine index second).Γ (componentMachine index second).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) (second : Bool) :
    Inhabited ((componentMachine index second).Γ (componentMachine index second).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) (second : Bool) :
    Inhabited ((componentMachine index second).Γ (componentMachine index second).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def componentWord (second : Bool) (block : ProofSystem.Certificate) : List Alphabet :=
  if second then encodeWith Codec.nat block.2 else encodeWith (Codec.list receiptCodec) block.1

theorem component_length (second : Bool) (block : ProofSystem.Certificate) :
    (componentWord second block).length ≤ (encodeCertificate block).length := by
  simp only [componentWord, encodeCertificate, certificateCodec, encodeWith,
    Codec.prod, encodeData_pair, List.length_cons, List.length_append]
  split <;> omega

noncomputable def parsedOutputs {arity : Nat} (index : Fin arity) (second : Bool)
    (packet : Fin arity → List Alphabet) (block : ProofSystem.Certificate)
    (stored : packet index = encodeCertificate block) :
    TM2OutputsInTime (parsedMachine index second) (Indexed.argumentWire packet)
      (some ((1 : Alphabet) :: componentWord second block))
      (14 * ((Indexed.argumentWire packet).length + 1)) := by
  have copied := Indexed.outputs (componentPlan index) packet
  have image : Indexed.instantiate (componentPlan index) packet = encodeCertificate block := by
    simpa only [componentPlan, Indexed.instantiate_hole, Indexed.instantiate_nil,
      List.append_nil] using stored
  rw [image] at copied
  have parsed := (CertificateDataTraversal.ProductField.computable second).outputsFun
    ((Codec.list receiptCodec).put block.1, Codec.nat.put block.2)
  dsimp only [CertificateDataTraversal.ProductField.computable] at parsed
  have alphabetIdentity : (Equiv.refl Alphabet).invFun = id := rfl
  rw [alphabetIdentity] at parsed
  simp only [List.map_id, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at parsed
  have result : CertificateDataTraversal.ProductField.selected second
      ((Codec.list receiptCodec).put block.1) (Codec.nat.put block.2) =
      if second then Codec.nat.put block.2 else (Codec.list receiptCodec).put block.1 := by
    cases second <;> rfl
  rw [result] at parsed
  have resultWord : encodeData (if second then Codec.nat.put block.2
      else (Codec.list receiptCodec).put block.1) = componentWord second block := by
    cases second <;> rfl
  rw [resultWord] at parsed
  change TM2OutputsInTime (CertificateDataTraversal.ProductField.machine second)
    (encodeCertificate block) (some ((1 : Alphabet) :: componentWord second block))
    (4 * (encodeCertificate block).length + 3) at parsed
  have joined := StackMachineComposition.outputs (Indexed.machine (componentPlan index))
    (CertificateDataTraversal.ProductField.machine second) (Equiv.refl Alphabet)
    (Indexed.argumentWire packet) (encodeCertificate block)
    ((1 : Alphabet) :: componentWord second block) _ _ copied (by
      change TM2OutputsInTime (CertificateDataTraversal.ProductField.machine second)
        ((encodeCertificate block).map id) _ _
      simpa only [List.map_id] using parsed)
  apply WordEqualityMachine.within joined
  have within := field_length_le packet index
  rw [stored] at within
  simp only [componentPlan, List.length_cons, List.length_nil]
  omega

noncomputable def componentOutputs {arity : Nat} (index : Fin arity) (second : Bool)
    (packet : Fin arity → List Alphabet) (block : ProofSystem.Certificate)
    (stored : packet index = encodeCertificate block) :
    TM2OutputsInTime (componentMachine index second) (Indexed.argumentWire packet)
      (some (componentWord second block))
      (24 * ((Indexed.argumentWire packet).length + 1)) := by
  let word := componentWord second block
  have identity := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) word
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success
    BinaryListAppend.identityMachine BinaryListAppend.acceptStatus [] (1 : Alphabet)
    word word _ (by decide) identity
  have joined := StackMachineComposition.outputs (parsedMachine index second)
    BinaryListAppend.stripMachine (Equiv.refl Alphabet) (Indexed.argumentWire packet)
    ((1 : Alphabet) :: word) word _ _ (parsedOutputs index second packet block stored) (by
      change TM2OutputsInTime BinaryListAppend.stripMachine (((1 : Alphabet) :: word).map id) _ _
      simpa only [List.map_id, BinaryListAppend.stripMachine] using stripped)
  apply WordEqualityMachine.within joined
  have within := field_length_le packet index
  rw [stored] at within
  have length := (component_length second block).trans within
  simp only [List.length_cons]
  dsimp only [word]
  omega

def firstMachine := RetainedWordExecution.WithOutput.Framed.machine
  (componentMachine (1 : Fin 2) false) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

local instance : Fintype (firstMachine.Γ firstMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (firstMachine.Γ firstMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def firstFields (earlier : List Receipt) (block : ProofSystem.Certificate) : Fin 3 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) earlier, encodeCertificate block,
    encodeWith (Codec.list receiptCodec) block.1]

theorem first_wire (earlier : List Receipt) (block : ProofSystem.Certificate) :
    RetainedWordExecution.WithOutput.Framed.outputWord (componentMachine (1 : Fin 2) false)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (inputWire earlier block) (componentWord false block) =
    Indexed.argumentWire (firstFields earlier block) := by
  simp [RetainedWordExecution.WithOutput.Framed.outputWord, inputWire, fields,
    firstFields, componentWord, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc, Function.comp_def]
  rfl

noncomputable def firstOutputs (earlier : List Receipt) (block : ProofSystem.Certificate) :
    TM2OutputsInTime firstMachine (inputWire earlier block)
      (some (Indexed.argumentWire (firstFields earlier block)))
      (70 * ((inputWire earlier block).length + 1)) := by
  have ran := RetainedWordExecution.WithOutput.Framed.outputs
    (componentMachine (1 : Fin 2) false) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (inputWire earlier block) (componentWord false block) _
    (componentOutputs (1 : Fin 2) false (fields earlier block) block rfl)
  rw [first_wire] at ran
  apply WordEqualityMachine.within ran
  have within := field_length_le (fields earlier block) (1 : Fin 2)
  change (encodeCertificate block).length ≤ (inputWire earlier block).length at within
  have length := (component_length false block).trans within
  dsimp only [inputWire] at length ⊢
  omega

def secondMachine := RetainedWordExecution.WithOutput.Framed.machine
  (componentMachine (1 : Fin 3) true) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

local instance : Fintype (secondMachine.Γ secondMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (secondMachine.Γ secondMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def secondFields (earlier : List Receipt) (block : ProofSystem.Certificate) : Fin 4 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) earlier, encodeCertificate block,
    encodeWith (Codec.list receiptCodec) block.1, encodeWith Codec.nat block.2]

theorem second_wire (earlier : List Receipt) (block : ProofSystem.Certificate) :
    RetainedWordExecution.WithOutput.Framed.outputWord (componentMachine (1 : Fin 3) true)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (Indexed.argumentWire (firstFields earlier block)) (componentWord true block) =
    Indexed.argumentWire (secondFields earlier block) := by
  simp [RetainedWordExecution.WithOutput.Framed.outputWord, firstFields, secondFields,
    componentWord, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc, Function.comp_def]
  rfl

noncomputable def secondOutputs (earlier : List Receipt) (block : ProofSystem.Certificate) :
    TM2OutputsInTime secondMachine (Indexed.argumentWire (firstFields earlier block))
      (some (Indexed.argumentWire (secondFields earlier block)))
      (70 * ((Indexed.argumentWire (firstFields earlier block)).length + 1)) := by
  have ran := RetainedWordExecution.WithOutput.Framed.outputs
    (componentMachine (1 : Fin 3) true) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (Indexed.argumentWire (firstFields earlier block)) (componentWord true block) _
    (componentOutputs (1 : Fin 3) true (firstFields earlier block) block rfl)
  rw [second_wire] at ran
  apply WordEqualityMachine.within ran
  have within := field_length_le (firstFields earlier block) (1 : Fin 3)
  change (encodeCertificate block).length ≤
    (Indexed.argumentWire (firstFields earlier block)).length at within
  have length := (component_length true block).trans within
  omega

def parsedPacketMachine := StackMachineComposition.machine firstMachine secondMachine
  (Equiv.refl (Option Alphabet))

local instance : Fintype (parsedPacketMachine.Γ parsedPacketMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (parsedPacketMachine.Γ parsedPacketMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def route : List (Fin 4) := [0, 2, 3]
def routedMachine := StackMachineComposition.machine parsedPacketMachine
  (FramedFieldSelection.machine (Γ := Alphabet) route) (Equiv.refl (Option Alphabet))

local instance : Fintype (routedMachine.Γ routedMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (routedMachine.Γ routedMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def machine := StackMachineComposition.machine routedMachine ChronologicalInsertion.machine
  (Equiv.refl (Option Alphabet))

theorem first_length (earlier : List Receipt) (block : ProofSystem.Certificate) :
    (Indexed.argumentWire (firstFields earlier block)).length =
      (inputWire earlier block).length + (componentWord false block).length + 1 := by
  rw [← first_wire]
  simp [RetainedWordExecution.WithOutput.Framed.outputWord, Nat.add_assoc]

theorem second_length (earlier : List Receipt) (block : ProofSystem.Certificate) :
    (Indexed.argumentWire (secondFields earlier block)).length =
      (Indexed.argumentWire (firstFields earlier block)).length +
        (componentWord true block).length + 1 := by
  rw [← second_wire]
  simp [RetainedWordExecution.WithOutput.Framed.outputWord, Nat.add_assoc]

theorem routed_wire (earlier : List Receipt) (block : ProofSystem.Certificate) :
    Indexed.frame (route.map (secondFields earlier block)) =
      ChronologicalInsertion.inputWire earlier block.1 block.2 := by
  simp [route, secondFields, ChronologicalInsertion.inputWire,
    ChronologicalInsertion.fields, Indexed.argumentWire, List.finRange_succ]

theorem routed_length (earlier : List Receipt) (block : ProofSystem.Certificate) :
    (ChronologicalInsertion.inputWire earlier block.1 block.2).length =
      (inputWire earlier block).length := by
  have certificateWord : encodeCertificate block =
      (4 : Alphabet) :: (encodeWith (Codec.list receiptCodec) block.1 ++
        encodeWith Codec.nat block.2) := by
    simp [encodeCertificate, certificateCodec, encodeWith, Codec.prod, encodeData_pair]
  simp [ChronologicalInsertion.inputWire, ChronologicalInsertion.fields,
    inputWire, fields, Indexed.argumentWire, Indexed.frame, List.finRange_succ,
    certificateWord, Nat.add_assoc]

theorem component_input_length (second : Bool) (earlier : List Receipt)
    (block : ProofSystem.Certificate) :
    (componentWord second block).length ≤ (inputWire earlier block).length := by
  have within := field_length_le (fields earlier block) (1 : Fin 2)
  change (encodeCertificate block).length ≤ (inputWire earlier block).length at within
  exact (component_length second block).trans within

noncomputable def parsedPacketOutputs (earlier : List Receipt) (block : ProofSystem.Certificate) :
    TM2OutputsInTime parsedPacketMachine (inputWire earlier block)
      (some (Indexed.argumentWire (secondFields earlier block)))
      (220 * ((inputWire earlier block).length + 1)) := by
  have joined := StackMachineComposition.outputs firstMachine secondMachine
    (Equiv.refl (Option Alphabet)) (inputWire earlier block)
    (Indexed.argumentWire (firstFields earlier block))
    (Indexed.argumentWire (secondFields earlier block)) _ _ (firstOutputs earlier block) (by
      change TM2OutputsInTime secondMachine
        ((Indexed.argumentWire (firstFields earlier block)).map id) _ _
      simpa only [List.map_id] using secondOutputs earlier block)
  apply WordEqualityMachine.within joined
  rw [first_length]
  have length := component_input_length false earlier block
  omega

noncomputable def routedOutputs (earlier : List Receipt) (block : ProofSystem.Certificate) :
    TM2OutputsInTime routedMachine (inputWire earlier block)
      (some (ChronologicalInsertion.inputWire earlier block.1 block.2))
      (340 * ((inputWire earlier block).length + 1)) := by
  have routed := FramedFieldSelection.outputs (Γ := Alphabet) route (secondFields earlier block)
  rw [routed_wire] at routed
  have joined := StackMachineComposition.outputs parsedPacketMachine
    (FramedFieldSelection.machine (Γ := Alphabet) route) (Equiv.refl (Option Alphabet))
    (inputWire earlier block) (Indexed.argumentWire (secondFields earlier block))
    (ChronologicalInsertion.inputWire earlier block.1 block.2) _ _
    (parsedPacketOutputs earlier block) (by
      change TM2OutputsInTime (FramedFieldSelection.machine (Γ := Alphabet) route)
        ((Indexed.argumentWire (secondFields earlier block)).map id) _ _
      simpa only [List.map_id] using routed)
  apply WordEqualityMachine.within joined
  rw [second_length, first_length]
  have first := component_input_length false earlier block
  have second := component_input_length true earlier block
  simp only [route, List.length_cons, List.length_nil]
  omega

/-- The fixed writer computes both fields from the actual emitted certificate,
then appends and packs the earlier graph. Every intermediate transfer is paid. -/
noncomputable def outputs (earlier : List Receipt) (block : ProofSystem.Certificate) :
    TM2OutputsInTime machine (inputWire earlier block)
      (some (encodeCertificate (earlier ++ block.1, block.2)))
      (850 * ((inputWire earlier block).length + 1)) := by
  have joined := StackMachineComposition.outputs routedMachine ChronologicalInsertion.machine
    (Equiv.refl (Option Alphabet)) (inputWire earlier block)
    (ChronologicalInsertion.inputWire earlier block.1 block.2)
    (encodeCertificate (earlier ++ block.1, block.2)) _ _ (routedOutputs earlier block) (by
      change TM2OutputsInTime ChronologicalInsertion.machine
        ((ChronologicalInsertion.inputWire earlier block.1 block.2).map id) _ _
      simpa only [List.map_id] using ChronologicalInsertion.outputs earlier block.1 block.2)
  apply WordEqualityMachine.within joined
  rw [routed_length]
  omega

theorem run_decodes (earlier : List Receipt) (block : ProofSystem.Certificate)
    {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire earlier block) (some word)) :
    decodeCertificate word = some (earlier ++ block.1, block.2) := by
  have same := StackMachineComposition.outputs_unique finished (outputs earlier block).toEvalsTo
  rw [same, decodeCertificate_encodeCertificate]

noncomputable def realization : TM2ComputableInPolyTime
    (fun packet : List Receipt × ProofSystem.Certificate => inputWire packet.1 packet.2)
    encodeCertificate (fun packet => (packet.1 ++ packet.2.1, packet.2.2)) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 850 * (Polynomial.X + Polynomial.C 1)
  outputsFun packet := by
    change TM2OutputsInTime machine ((inputWire packet.1 packet.2).map id)
      (some ((encodeCertificate (packet.1 ++ packet.2.1, packet.2.2)).map id)) _
    simp only [List.map_id, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    exact outputs packet.1 packet.2

theorem run_emitted_authorized {policy : AxiomPolicy} [DecidablePred policy]
    {roots : List Nat} {block : ProofSystem.Certificate}
    {before after : ProofExecution.State} {root : Nat} {word : List Alphabet}
    (earlier : GraphExpansion.BuildChecked policy [] before)
    (emitted : GraphExpansion.emitBlock policy roots block before = some (after, root))
    (finished : TM2Outputs machine
      (inputWire before.receipts.toList
        (GraphExpansion.expandBlock roots before.cache.size block)) (some word)) :
    ∃ conclusion,
      decodeCertificate word = some (GraphExpansion.finish after root) ∧
      (ProofSystem.checker policy).check conclusion
        (GraphExpansion.finish after root) = true ∧
      after.cache[root]? = some conclusion := by
  obtain ⟨checked, ⟨conclusion, found⟩, _⟩ :=
    GraphExpansion.emitBlock_preserves_checked earlier emitted
  have decoded := run_decodes before.receipts.toList
    (GraphExpansion.expandBlock roots before.cache.size block) finished
  obtain ⟨receipts, selected⟩ := GraphExpansion.emitBlock_expanded emitted
  refine ⟨conclusion, ?_, ?_, found⟩
  · simpa only [GraphExpansion.finish, receipts, selected] using decoded
  · exact (ProofSystem.checker_check_iff policy _ _).mpr ⟨after.cache, checked, found⟩

end Mettapedia.Languages.HOLLight.EmittedCertificateInsertion

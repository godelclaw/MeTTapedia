import Mettapedia.Computability.BinaryListAppend
import Mettapedia.Languages.HOLLight.GraphExpansion
import Mettapedia.Languages.HOLLight.ProofDataEncoding

/-!
# Physical chronological receipt insertion

The input contains the earlier receipt list, the relocated new receipt list
and its selected physical root. Selection, original binary append, status
removal, input retention and certificate packing are actual machine stages.
The root remains a separate retained field; it is never inferred from the
last receipt. Logical authorization is earned by the original graph replay.

The execution contract concerns original codec images. Arbitrary malformed
packet admission and the driver that computes relocation remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ChronologicalInsertion

open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory Mettapedia.Logic.DerivationGraph
open ProofExecution ProofDataEncoding

abbrev Alphabet := Binary.Alphabet

def fields (earlier later : List Receipt) (root : Nat) : Fin 3 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) earlier,
    encodeWith (Codec.list receiptCodec) later, encodeWith Codec.nat root]

def inputWire (earlier later : List Receipt) (root : Nat) : List (Option Alphabet) :=
  Indexed.argumentWire (fields earlier later root)

def selector : List (Fin 3) := [0, 1]

theorem selected_wire (earlier later : List Receipt) (root : Nat) :
    Indexed.frame (selector.map (fields earlier later root)) =
      BinaryListAppend.inputWire receiptCodec earlier later := by
  simp [selector, fields, BinaryListAppend.inputWire, BinaryListAppend.fields,
    Indexed.argumentWire, List.finRange_succ]

theorem selected_length (earlier later : List Receipt) (root : Nat) :
    (BinaryListAppend.inputWire receiptCodec earlier later).length ≤
      (inputWire earlier later root).length := by
  simp [inputWire, fields, BinaryListAppend.inputWire, BinaryListAppend.fields,
    Indexed.argumentWire, Indexed.frame, List.finRange_succ]

theorem joined_length (earlier later : List Receipt) (root : Nat) :
    (encodeWith (Codec.list receiptCodec) (earlier ++ later)).length + 1 ≤
      (inputWire earlier later root).length := by
  rw [← BinaryListAppend.original_append]
  have input := BinaryListAppend.input_length receiptCodec earlier later
  have selected := selected_length earlier later root
  simp only [List.length_append] at *
  omega

local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) selector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) selector).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) selector).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) selector).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def appendedMachine := StackMachineComposition.machine
  (FramedFieldSelection.machine (Γ := Alphabet) selector)
  BinaryListAppend.machine (Equiv.refl (Option Alphabet))

local instance : Fintype (appendedMachine.Γ appendedMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (appendedMachine.Γ appendedMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)

noncomputable def appendedOutputs (earlier later : List Receipt) (root : Nat) :
    TM2OutputsInTime appendedMachine (inputWire earlier later root)
      (some (BinaryListAppend.resultWire receiptCodec (earlier ++ later)))
      (320 * ((inputWire earlier later root).length + 1)) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet) selector
    (fields earlier later root)
  rw [selected_wire] at selected
  have appended := BinaryListAppend.outputs receiptCodec earlier later
  have joined := StackMachineComposition.outputs
    (FramedFieldSelection.machine (Γ := Alphabet) selector) BinaryListAppend.machine
    (Equiv.refl (Option Alphabet)) (inputWire earlier later root)
    (BinaryListAppend.inputWire receiptCodec earlier later)
    (BinaryListAppend.resultWire receiptCodec (earlier ++ later)) _ _ selected (by
      change TM2OutputsInTime BinaryListAppend.machine
        ((BinaryListAppend.inputWire receiptCodec earlier later).map id) _ _
      simpa only [List.map_id] using appended)
  apply WordEqualityMachine.within joined
  have bound := selected_length earlier later root
  simp only [selector, List.length_cons, List.length_nil]
  change (8 * 2 + 12) * ((inputWire earlier later root).length + 1) +
    2 * (BinaryListAppend.inputWire receiptCodec earlier later).length + 2 +
    288 * ((BinaryListAppend.inputWire receiptCodec earlier later).length + 1) ≤ _
  omega

def rawMachine := StackMachineComposition.machine appendedMachine
  BinaryListAppend.stripMachine (Equiv.refl Alphabet)

local instance : Fintype (rawMachine.Γ rawMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (rawMachine.Γ rawMachine.k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (rawMachine.Γ rawMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

noncomputable def rawOutputs (earlier later : List Receipt) (root : Nat) :
    TM2OutputsInTime rawMachine (inputWire earlier later root)
      (some (encodeWith (Codec.list receiptCodec) (earlier ++ later)))
      (330 * ((inputWire earlier later root).length + 1)) := by
  let word := encodeWith (Codec.list receiptCodec) (earlier ++ later)
  have identity := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol]) word
  simp only [List.flatMap_singleton'] at identity
  have stripped := StackMachineComposition.Dispatch.outputs_success
    BinaryListAppend.identityMachine BinaryListAppend.acceptStatus [] (1 : Alphabet)
    word word _ (by decide) identity
  have joined := StackMachineComposition.outputs appendedMachine BinaryListAppend.stripMachine
    (Equiv.refl Alphabet) (inputWire earlier later root)
    ((1 : Alphabet) :: word) word _ _ (appendedOutputs earlier later root) (by
      change TM2OutputsInTime BinaryListAppend.stripMachine ((1 :: word).map id) _ _
      simpa only [List.map_id, BinaryListAppend.stripMachine] using stripped)
  apply WordEqualityMachine.within joined
  have length := joined_length earlier later root
  simp only [List.length_cons]
  change 330 * ((inputWire earlier later root).length + 1) ≥
    320 * ((inputWire earlier later root).length + 1) + 2 * (word.length + 1) + 2 +
      (2 * word.length + 2 * word.length + 2 + 1)
  dsimp only [word]
  omega

def retainedMachine := RetainedWordExecution.WithOutput.Framed.machine rawMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

local instance : Fintype (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (retainedMachine.Γ retainedMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def retainedFields (earlier later : List Receipt) (root : Nat) : Fin 4 → List Alphabet :=
  ![encodeWith (Codec.list receiptCodec) earlier,
    encodeWith (Codec.list receiptCodec) later, encodeWith Codec.nat root,
    encodeWith (Codec.list receiptCodec) (earlier ++ later)]

theorem retained_wire (earlier later : List Receipt) (root : Nat) :
    RetainedWordExecution.WithOutput.Framed.outputWord rawMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (inputWire earlier later root)
      (encodeWith (Codec.list receiptCodec) (earlier ++ later)) =
    Indexed.argumentWire (retainedFields earlier later root) := by
  simp [RetainedWordExecution.WithOutput.Framed.outputWord, inputWire, fields,
    retainedFields, Indexed.argumentWire, Indexed.frame, List.finRange_succ,
    List.append_assoc, Function.comp_def]
  rfl

def pack : Indexed.Template Alphabet 4 := [.inl 4, .inr 3, .inr 2]

theorem pack_exact (earlier later : List Receipt) (root : Nat) :
    Indexed.instantiate pack (retainedFields earlier later root) =
      encodeCertificate (earlier ++ later, root) := by
  simp [pack, retainedFields, Indexed.instantiate, encodeCertificate, certificateCodec,
    encodeWith, Codec.prod, encodeData_pair]

def machine := StackMachineComposition.machine retainedMachine (Indexed.machine pack)
  (Equiv.refl (Option Alphabet))

noncomputable def outputs (earlier later : List Receipt) (root : Nat) :
    TM2OutputsInTime machine (inputWire earlier later root)
      (some (encodeCertificate (earlier ++ later, root)))
      (500 * ((inputWire earlier later root).length + 1)) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs rawMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (inputWire earlier later root) (encodeWith (Codec.list receiptCodec) (earlier ++ later))
    _ (rawOutputs earlier later root)
  rw [retained_wire] at retained
  have packed := Indexed.outputs pack (retainedFields earlier later root)
  rw [pack_exact] at packed
  have joined := StackMachineComposition.outputs retainedMachine (Indexed.machine pack)
    (Equiv.refl (Option Alphabet)) (inputWire earlier later root)
    (Indexed.argumentWire (retainedFields earlier later root))
    (encodeCertificate (earlier ++ later, root)) _ _ retained (by
      change TM2OutputsInTime (Indexed.machine pack)
        ((Indexed.argumentWire (retainedFields earlier later root)).map id) _ _
      simpa only [List.map_id] using packed)
  apply WordEqualityMachine.within joined
  have joinedLength := joined_length earlier later root
  have retainedLength : (Indexed.argumentWire (retainedFields earlier later root)).length =
      (inputWire earlier later root).length +
        (encodeWith (Codec.list receiptCodec) (earlier ++ later)).length + 1 := by
    rw [← retained_wire]
    simp [RetainedWordExecution.WithOutput.Framed.outputWord, Nat.add_assoc]
  simp only [pack, List.length_cons, List.length_nil]
  rw [retainedLength]
  omega

theorem run_decodes (earlier later : List Receipt) (root : Nat) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire earlier later root) (some word)) :
    decodeCertificate word = some (earlier ++ later, root) := by
  have same := StackMachineComposition.outputs_unique finished (outputs earlier later root).toEvalsTo
  rw [same, decodeCertificate_encodeCertificate]

/-- One fixed machine packs the complete original certificate. The polynomial
counts the physical input, including the full binary root field. -/
noncomputable def realization : TM2ComputableInPolyTime
    (fun packet : (List Receipt × List Receipt) × Nat =>
      inputWire packet.1.1 packet.1.2 packet.2)
    encodeCertificate
    (fun packet => (packet.1.1 ++ packet.1.2, packet.2)) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 500 * (Polynomial.X + Polynomial.C 1)
  outputsFun packet := by
    change TM2OutputsInTime machine
      ((inputWire packet.1.1 packet.1.2 packet.2).map id)
      (some ((encodeCertificate (packet.1.1 ++ packet.1.2, packet.2)).map id)) _
    simp only [List.map_id, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    exact outputs packet.1.1 packet.1.2 packet.2

/-- The actual writer's readout is exactly the original checked builder's
certificate, including the relocated selected root. -/
theorem run_emitted_decodes {policy : AxiomPolicy} [DecidablePred policy]
    {roots : List Nat} {block : ProofSystem.Certificate}
    {before after : ProofExecution.State} {root : Nat} {word : List Alphabet}
    (emitted : GraphExpansion.emitBlock policy roots block before = some (after, root))
    (finished : TM2Outputs machine
      (inputWire before.receipts.toList
        (GraphExpansion.expandBlock roots before.cache.size block).1
        (GraphExpansion.expandBlock roots before.cache.size block).2) (some word)) :
    decodeCertificate word = some (GraphExpansion.finish after root) := by
  have decoded := run_decodes before.receipts.toList
    (GraphExpansion.expandBlock roots before.cache.size block).1
    (GraphExpansion.expandBlock roots before.cache.size block).2 finished
  obtain ⟨receipts, selected⟩ := GraphExpansion.emitBlock_expanded emitted
  simpa only [GraphExpansion.finish, receipts, selected] using decoded

/-- Authorization comes from original chronological replay, with no local
emitter-correctness assumption. The emitted bytes and the independently
checked original certificate have the same readout. -/
theorem run_emitted_authorized {policy : AxiomPolicy} [DecidablePred policy]
    {roots : List Nat} {block : ProofSystem.Certificate}
    {before after : ProofExecution.State} {root : Nat} {word : List Alphabet}
    (earlier : GraphExpansion.BuildChecked policy [] before)
    (emitted : GraphExpansion.emitBlock policy roots block before = some (after, root))
    (finished : TM2Outputs machine
      (inputWire before.receipts.toList
        (GraphExpansion.expandBlock roots before.cache.size block).1
        (GraphExpansion.expandBlock roots before.cache.size block).2) (some word)) :
    ∃ certificate conclusion,
      decodeCertificate word = some certificate ∧
      certificate = GraphExpansion.finish after root ∧
      (ProofSystem.checker policy).check conclusion certificate = true ∧
      after.cache[root]? = some conclusion := by
  obtain ⟨checked, ⟨conclusion, found⟩, _⟩ :=
    GraphExpansion.emitBlock_preserves_checked earlier emitted
  refine ⟨GraphExpansion.finish after root, conclusion,
    run_emitted_decodes emitted finished, rfl, ?_, found⟩
  apply (ProofSystem.checker_check_iff policy _ _).mpr
  exact ⟨after.cache, checked, found⟩

/-- A saved root is authorized again in the exact new graph. Appending receipts
does not replace the theorem at any earlier physical address. -/
theorem saved_root_retained {policy : AxiomPolicy} [DecidablePred policy]
    {roots : List Nat} {block : ProofSystem.Certificate}
    {before after : ProofExecution.State} {root saved : Nat} {conclusion : Theorem}
    (earlier : GraphExpansion.BuildChecked policy [] before)
    (emitted : GraphExpansion.emitBlock policy roots block before = some (after, root))
    (found : before.cache[saved]? = some conclusion) :
    after.cache[saved]? = some conclusion ∧
      (ProofSystem.checker policy).check conclusion
        (GraphExpansion.finish after saved) = true := by
  obtain ⟨checked, _, kept⟩ := GraphExpansion.emitBlock_preserves_checked earlier emitted
  have retained := kept saved conclusion found
  exact ⟨retained, (ProofSystem.checker_check_iff policy _ _).mpr
    ⟨after.cache, checked, retained⟩⟩

/-- Witness and origin occurrences survive physical packing in their original
order. Equal-valued receipts stay separate list positions. -/
theorem run_occurrences (earlier later : List Receipt) (root : Nat)
    {word : List Alphabet} {certificate : ProofSystem.Certificate}
    (finished : TM2Outputs machine (inputWire earlier later root) (some word))
    (decoded : decodeCertificate word = some certificate) :
    certificate.1.map (fun receipt => (receipt.witness, receipt.origin)) =
      earlier.map (fun receipt => (receipt.witness, receipt.origin)) ++
        later.map (fun receipt => (receipt.witness, receipt.origin)) ∧
      certificate.1.length = earlier.length + later.length ∧
      certificate.2 = root := by
  have same := Option.some.inj (decoded.symm.trans (run_decodes earlier later root finished))
  subst certificate
  simp only [List.map_append, List.length_append, and_self]

end Mettapedia.Languages.HOLLight.ChronologicalInsertion

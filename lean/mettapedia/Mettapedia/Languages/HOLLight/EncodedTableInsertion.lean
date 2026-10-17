import Mettapedia.Languages.HOLLight.SavedRootInsertion

/-!
# Original codec values physically inserted into the resolver table

The packet carries the existing table, next index in the original natural
codec, and the complete new value in its original codec. Executed projection
earns the binary index; physical triple encoding earns every stored value bit.
The original table append then installs exactly one occurrence. Lookup uses
the existing resolver, not a separate map. A HOL specialization relates the
installed row to successful original node replay. Arbitrary byte admission and
the complete chronological driver remain separate contracts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.EncodedTableInsertion

open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution
abbrev Alphabet := Binary.Alphabet
variable {A : Type}

def valueImage (symbol : Alphabet) : List Alphabet := (Triples.symbol symbol).map bit

theorem value_image (word : List Alphabet) :
    word.flatMap valueImage = field (Triples.encode word) := by
  simp only [field, Triples.encode, List.map_flatMap]
  rfl

attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  WordHomomorphismMachine.machine SavedRootInsertion.retainedProjection

local instance {arity : Nat} (index : Fin arity) :
    Fintype ((Indexed.machine (SavedRootInsertion.selectTemplate index)).Γ
      (Indexed.machine (SavedRootInsertion.selectTemplate index)).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((Indexed.machine (SavedRootInsertion.selectTemplate index)).Γ
      (Indexed.machine (SavedRootInsertion.selectTemplate index)).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def valueProjection {arity : Nat} (index : Fin arity) :=
  StackMachineComposition.machine (Indexed.machine (SavedRootInsertion.selectTemplate index))
    (WordHomomorphismMachine.machine valueImage) (Equiv.refl Alphabet)

attribute [local implicit_reducible] valueProjection
local instance {arity : Nat} (index : Fin arity) :
    Fintype ((valueProjection index).Γ (valueProjection index).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((valueProjection index).Γ (valueProjection index).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((valueProjection index).Γ (valueProjection index).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

noncomputable def valueProjectionOutputs {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) :
    TM2OutputsInTime (valueProjection index) (Indexed.argumentWire packet)
      (some (field (Triples.encode (packet index))))
      (20 * ((Indexed.argumentWire packet).length + 1)) := by
  have selected := Indexed.outputs (SavedRootInsertion.selectTemplate index) packet
  have selectedWord : Indexed.instantiate (SavedRootInsertion.selectTemplate index) packet =
      packet index := by simp [SavedRootInsertion.selectTemplate]
  rw [selectedWord] at selected
  have encoded := WordHomomorphismMachine.outputs valueImage (packet index)
  rw [value_image] at encoded
  have joined := StackMachineComposition.outputs
    (Indexed.machine (SavedRootInsertion.selectTemplate index))
    (WordHomomorphismMachine.machine valueImage) (Equiv.refl Alphabet)
    (Indexed.argumentWire packet) (packet index)
    (field (Triples.encode (packet index))) _ _ selected (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine valueImage)
        ((packet index).map id) _ _
      simpa only [List.map_id] using encoded)
  apply WordEqualityMachine.within joined
  have bound := EmittedCertificateInsertion.field_length_le packet index
  simp only [SavedRootInsertion.selectTemplate, List.length_cons, List.length_nil,
    field, List.length_map, Triples.encode_length]
  omega

def retainedValue {arity : Nat} (index : Fin arity) :=
  RetainedWordExecution.WithOutput.Framed.machine (valueProjection index)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

attribute [local implicit_reducible] retainedValue
local instance {arity : Nat} (index : Fin arity) :
    Fintype ((retainedValue index).Γ (retainedValue index).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((retainedValue index).Γ (retainedValue index).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def valueFields {arity : Nat} (packet : Fin arity → List Alphabet) (index : Fin arity) :
    Fin (arity + 1) → List Alphabet :=
  Fin.addCases packet (fun _ => field (Triples.encode (packet index)))

theorem retained_word {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) :
    RetainedWordExecution.WithOutput.Framed.outputWord (valueProjection index)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (Indexed.argumentWire packet) (field (Triples.encode (packet index))) =
      Indexed.argumentWire (valueFields packet index) := by
  change (Indexed.argumentWire packet).map id ++
    (field (Triples.encode (packet index))).map some ++ [none] = _
  rw [List.map_id]
  exact (RelocatedCertificateInsertion.argumentWire_add_one packet _).symm

noncomputable def retainedValueOutputs {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) :
    TM2OutputsInTime (retainedValue index) (Indexed.argumentWire packet)
      (some (Indexed.argumentWire (valueFields packet index)))
      (128 * ((Indexed.argumentWire packet).length + 1)) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (valueProjection index)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (Indexed.argumentWire packet) (field (Triples.encode (packet index))) _
    (valueProjectionOutputs index packet)
  rw [retained_word] at retained
  apply WordEqualityMachine.within retained
  have bound := EmittedCertificateInsertion.field_length_le packet index
  simp only [field, List.length_map, Triples.encode_length]
  omega

def fields (codec : Codec A) (values : Array A) (next : A) : Fin 3 → List Alphabet :=
  ![table (EncodedTable.rows codec values), GraphAddressAddition.natWord values.size,
    encodeWith codec next]
def inputWire (codec : Codec A) (values : Array A) (next : A) :=
  Indexed.argumentWire (fields codec values next)
def middleFields (codec : Codec A) (values : Array A) (next : A) :=
  SavedRootInsertion.projectedFields (fields codec values next) values.size
def finalFields (codec : Codec A) (values : Array A) (next : A) :=
  valueFields (middleFields codec values next) (2 : Fin 4)

local instance : Fintype ((SavedRootInsertion.retainedProjection (1 : Fin 3)).Γ
    (SavedRootInsertion.retainedProjection (1 : Fin 3)).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((SavedRootInsertion.retainedProjection (1 : Fin 3)).Γ
    (SavedRootInsertion.retainedProjection (1 : Fin 3)).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def projections := StackMachineComposition.machine
  (SavedRootInsertion.retainedProjection (1 : Fin 3)) (retainedValue (2 : Fin 4))
  (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] projections
local instance : Fintype (projections.Γ projections.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (projections.Γ projections.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

theorem field_bounds (codec : Codec A) (values : Array A) (next : A) :
    (field (naturalKey values.size)).length ≤ (inputWire codec values next).length ∧
      (encodeWith codec next).length ≤ (inputWire codec values next).length := by
  exact ⟨(SavedRootInsertion.digits_length values.size).trans
    (EmittedCertificateInsertion.field_length_le (fields codec values next) 1),
    EmittedCertificateInsertion.field_length_le (fields codec values next) 2⟩

theorem middle_length (codec : Codec A) (values : Array A) (next : A) :
    (Indexed.argumentWire (middleFields codec values next)).length =
      (inputWire codec values next).length + (field (naturalKey values.size)).length + 1 :=
  SavedRootInsertion.projected_length _ _

theorem final_length (codec : Codec A) (values : Array A) (next : A) :
    (Indexed.argumentWire (finalFields codec values next)).length =
      (inputWire codec values next).length + (field (naturalKey values.size)).length +
        3 * (encodeWith codec next).length + 2 := by
  unfold finalFields valueFields
  rw [RelocatedCertificateInsertion.argumentWire_add_one]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
    field, Triples.encode_length]
  change (Indexed.argumentWire (middleFields codec values next)).length +
    3 * (encodeWith codec next).length + 1 = _
  rw [middle_length]
  simp only [field, List.length_map]
  omega

noncomputable def projectionsOutputs (codec : Codec A) (values : Array A) (next : A) :
    TM2OutputsInTime projections (inputWire codec values next)
      (some (Indexed.argumentWire (finalFields codec values next)))
      (350 * ((inputWire codec values next).length + 1)) := by
  have first := SavedRootInsertion.retainedProjectionOutputs (1 : Fin 3)
    (fields codec values next) values.size rfl
  have second := retainedValueOutputs (2 : Fin 4) (middleFields codec values next)
  have joined := StackMachineComposition.outputs
    (SavedRootInsertion.retainedProjection (1 : Fin 3)) (retainedValue (2 : Fin 4))
    (Equiv.refl (Option Alphabet)) (inputWire codec values next)
    (Indexed.argumentWire (middleFields codec values next))
    (Indexed.argumentWire (finalFields codec values next)) _ _ first (by
      change TM2OutputsInTime (retainedValue (2 : Fin 4))
        ((Indexed.argumentWire (middleFields codec values next)).map id) _ _
      simpa only [List.map_id, finalFields] using second)
  apply WordEqualityMachine.within joined
  have bounded := (field_bounds codec values next).1
  rw [middle_length]
  change 70 * ((inputWire codec values next).length + 1) +
    2 * ((inputWire codec values next).length + (field (naturalKey values.size)).length + 1) + 2 +
    128 * ((inputWire codec values next).length + (field (naturalKey values.size)).length + 2) ≤ _
  omega

theorem routed_word (codec : Codec A) (values : Array A) (next : A) :
    Indexed.frame (SavedRootInsertion.route.map (finalFields codec values next)) =
      TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
        (EncodedTable.value codec next) := by rfl

local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def routed := StackMachineComposition.machine projections
  (FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route)
  (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] routed
local instance : Fintype (routed.Γ routed.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (routed.Γ routed.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

noncomputable def routedOutputs (codec : Codec A) (values : Array A) (next : A) :
    TM2OutputsInTime routed (inputWire codec values next)
      (some (TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
        (EncodedTable.value codec next)))
      (550 * ((inputWire codec values next).length + 1)) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet)
    SavedRootInsertion.route (finalFields codec values next)
  rw [routed_word] at selected
  have joined := StackMachineComposition.outputs projections
    (FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route)
    (Equiv.refl (Option Alphabet)) (inputWire codec values next)
    (Indexed.argumentWire (finalFields codec values next))
    (TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
      (EncodedTable.value codec next)) _ _ (projectionsOutputs codec values next) (by
      change TM2OutputsInTime (FramedFieldSelection.machine (Γ := Alphabet) SavedRootInsertion.route)
        ((Indexed.argumentWire (finalFields codec values next)).map id) _ _
      simpa only [List.map_id] using selected)
  apply WordEqualityMachine.within joined
  obtain ⟨firstBound, secondBound⟩ := field_bounds codec values next
  simp only [SavedRootInsertion.route, List.length_cons, List.length_nil]
  rw [final_length]
  omega

def machine := StackMachineComposition.machine routed TableAppend.machine
  (Equiv.refl (Option Alphabet))

theorem packet_bound (codec : Codec A) (values : Array A) (next : A) :
    (TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
      (EncodedTable.value codec next)).length ≤ 3 * (inputWire codec values next).length := by
  have bounds := field_bounds codec values next
  have natLength : (GraphAddressAddition.natWord values.size).length =
      (field (naturalKey values.size)).length + 2 := by
    simp [GraphAddressAddition.natWord, Binary.encodeWith, Codec.nat,
      encodeData_atom, natural, field, naturalKey]
  simp only [TableAppend.packet, TableAppend.fields, inputWire, fields,
    Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.length_append,
    List.length_map, List.length_cons, List.length_nil, List.append_nil,
    EncodedTable.value, field, Triples.encode_length]
  have digitsLength : (naturalKey values.size).length =
      (field (naturalKey values.size)).length := by simp [field]
  rw [digitsLength, natLength]
  omega

noncomputable def outputs (codec : Codec A) (values : Array A) (next : A) :
    TM2OutputsInTime machine (inputWire codec values next)
      (some (table (EncodedTable.rows codec (values.push next))))
      (768 * ((inputWire codec values next).length + 1)) := by
  have appended := EncodedTable.appendOutputs codec values next
  have joined := StackMachineComposition.outputs routed TableAppend.machine
    (Equiv.refl (Option Alphabet)) (inputWire codec values next)
    (TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
      (EncodedTable.value codec next)) (table (EncodedTable.rows codec (values.push next)))
    _ _ (routedOutputs codec values next) (by
      change TM2OutputsInTime TableAppend.machine
        ((TableAppend.packet (EncodedTable.rows codec values) (naturalKey values.size)
          (EncodedTable.value codec next)).map id) _ _
      simpa only [List.map_id] using appended)
  apply WordEqualityMachine.within joined
  have bounded := packet_bound codec values next
  omega

theorem run_exact (codec : Codec A) (values : Array A) (next : A) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire codec values next) (some word)) :
    word = table (EncodedTable.rows codec (values.push next)) :=
  StackMachineComposition.outputs_unique finished (outputs codec values next).toEvalsTo

noncomputable def realization (codec : Codec A) : TM2ComputableInPolyTime
    (fun pair : Array A × A => inputWire codec pair.1 pair.2)
    (fun values => table (EncodedTable.rows codec values)) (fun pair => pair.1.push pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 768 * (Polynomial.X + Polynomial.C 1)
  outputsFun pair := by
    change TM2OutputsInTime machine ((inputWire codec pair.1 pair.2).map id)
      (some ((table (EncodedTable.rows codec (pair.1.push pair.2))).map id)) _
    simp only [List.map_id, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    exact outputs codec pair.1 pair.2

/-- Successful original HOL replay, independently of byte insertion, earns
the new theorem row and its exact chronological address. -/
theorem replayed_node {policy : Mettapedia.Languages.OpenTheory.AxiomPolicy}
    [DecidablePred policy] {before after : Array Mettapedia.Languages.OpenTheory.Theorem}
    {node : Mettapedia.Languages.HOLLight.ProofExecution.Receipt}
    (checked : node.replay (Mettapedia.Languages.HOLLight.ruleWitness policy) before = some after)
    {word : List Alphabet}
    (finished : TM2Outputs machine
      (inputWire Mettapedia.Languages.OpenTheory.SyntaxEncoding.theoremCodec before node.conclusion)
      (some word)) :
    word = table (EncodedTable.rows Mettapedia.Languages.OpenTheory.SyntaxEncoding.theoremCodec after) ∧
      after[before.size]? = some node.conclusion := by
  have next := Mettapedia.Logic.DerivationGraph.Node.replay_eq_push
    (Mettapedia.Languages.HOLLight.ruleWitness policy) checked
  rw [next]
  exact ⟨run_exact _ before node.conclusion finished, by simp⟩

theorem new_index_lookup (codec : Codec A) (values : Array A) (next : A) :
    lookup (naturalKey values.size) (EncodedTable.rows codec (values.push next)) =
      some (EncodedTable.value codec next) := by
  rw [EncodedTable.lookup_rows]
  simp

theorem old_index_lookup (codec : Codec A) (values : Array A) (next : A) (query : Nat)
    (earlier : query < values.size) :
    lookup (naturalKey query) (EncodedTable.rows codec (values.push next)) =
      lookup (naturalKey query) (EncodedTable.rows codec values) := by
  rw [EncodedTable.lookup_rows, EncodedTable.lookup_rows]
  simp [Array.getElem?_push, earlier, Nat.ne_of_lt earlier]

theorem future_index_lookup (codec : Codec A) (values : Array A) (next : A) (query : Nat)
    (future : values.size + 1 ≤ query) :
    lookup (naturalKey query) (EncodedTable.rows codec (values.push next)) = none := by
  rw [EncodedTable.lookup_rows, Array.getElem?_eq_none (by simpa using future)]
  rfl

theorem changed_value_observable (codec : Codec A) (values : Array A) (next changed : A)
    (different : next ≠ changed) :
    lookup (naturalKey values.size) (EncodedTable.rows codec (values.push next)) ≠
      some (EncodedTable.value codec changed) := by
  rw [new_index_lookup]
  intro equal
  exact different (EncodedTable.value_injective codec (Option.some.inj equal))

namespace Controls

theorem duplicate_values_preserve_indices :
    lookup (naturalKey 0) (EncodedTable.rows Codec.nat (#[7].push 7)) =
        some (EncodedTable.value Codec.nat 7) ∧
      lookup (naturalKey 1) (EncodedTable.rows Codec.nat (#[7].push 7)) =
        some (EncodedTable.value Codec.nat 7) ∧
      (EncodedTable.rows Codec.nat (#[7].push 7)).length = 2 := by decide +kernel

theorem changed_value_is_visible :
    lookup (naturalKey 1) (EncodedTable.rows Codec.nat (#[7].push 13)) ≠
      some (EncodedTable.value Codec.nat 14) := by decide +kernel

theorem future_is_missing :
    lookup (naturalKey 2) (EncodedTable.rows Codec.nat (#[7].push 7)) = none := by decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.EncodedTableInsertion

import Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion
import Mettapedia.Languages.HOLLight.GraphAddressAddition
import Mettapedia.Languages.HOLLight.ChronologicalDriver
import Mettapedia.GSLT.LanguageDef.SharedReferenceExecution

/-!
# Physical insertion into the original saved-root table

The packet contains the existing binary root table, the next source index and
the selected physical root in the original natural codec. Two executed field
projections recover their binary keys. Retention preserves the original table;
the existing table-append machine installs the new occurrence. This stage
concerns admitted codec images. Index admission and theorem authority belong
to the controller and chronological replay respectively.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SavedRootInsertion

open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.SharedReferenceExecution

abbrev Alphabet := Binary.Alphabet

theorem digits_exact (value : Nat) :
    GraphAddressAddition.digitWord value = field (naturalKey value) := by
  simp only [GraphAddressAddition.digitWord, BinaryStackArithmetic.naturalBits,
    field, naturalKey, List.map_map, Function.comp_def, bit]
  apply List.map_congr_left
  intro digit member
  have bounded := Nat.digits_lt_base (by decide : 1 < 2) member
  have cases : digit = 0 ∨ digit = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

theorem digits_length (value : Nat) :
    (field (naturalKey value)).length ≤ (GraphAddressAddition.natWord value).length := by
  rw [← digits_exact]
  simpa only [GraphAddressAddition.digitWord, GraphAddressAddition.bits,
    List.length_map] using GraphAddressAddition.bits_length value

attribute [local implicit_reducible] Indexed.machine StackMachineComposition.machine
  GraphAddressAddition.bitMachine GraphAddressAddition.digitMachine

def selectTemplate {arity : Nat} (index : Fin arity) : Indexed.Template Alphabet arity :=
  [.inr index]

local instance {arity : Nat} (index : Fin arity) :
    Fintype ((Indexed.machine (selectTemplate index)).Γ
      (Indexed.machine (selectTemplate index)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((Indexed.machine (selectTemplate index)).Γ
      (Indexed.machine (selectTemplate index)).k₁) := inferInstanceAs (Inhabited Alphabet)

def bitProjection {arity : Nat} (index : Fin arity) :=
  StackMachineComposition.machine (Indexed.machine (selectTemplate index))
    GraphAddressAddition.bitMachine (Equiv.refl Alphabet)

attribute [local implicit_reducible] bitProjection
local instance {arity : Nat} (index : Fin arity) :
    Fintype ((bitProjection index).Γ (bitProjection index).k₁) :=
  inferInstanceAs (Fintype (Option Bool))
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((bitProjection index).Γ (bitProjection index).k₁) :=
  inferInstanceAs (Inhabited (Option Bool))

def projection {arity : Nat} (index : Fin arity) :=
  StackMachineComposition.machine (bitProjection index)
    GraphAddressAddition.digitMachine (Equiv.refl (Option Bool))

attribute [local implicit_reducible] projection
local instance {arity : Nat} (index : Fin arity) :
    Fintype ((projection index).Γ (projection index).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((projection index).Γ (projection index).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((projection index).Γ (projection index).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

/-- This machine reads the submitted natural field rather than a decoded
numeric control register. The input index is a fixed finite selector. -/
noncomputable def projectionOutputs {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) (value : Nat)
    (encoded : packet index = GraphAddressAddition.natWord value) :
    TM2OutputsInTime (projection index) (Indexed.argumentWire packet)
      (some (field (naturalKey value)))
      (24 * ((Indexed.argumentWire packet).length + 1)) := by
  have selected := Indexed.outputs (selectTemplate index) packet
  have selectedWord : Indexed.instantiate (selectTemplate index) packet =
      GraphAddressAddition.natWord value := by simp [selectTemplate, encoded]
  rw [selectedWord] at selected
  have projected := StackMachineComposition.outputs
    (Indexed.machine (selectTemplate index)) GraphAddressAddition.bitMachine
    (Equiv.refl Alphabet) (Indexed.argumentWire packet)
    (GraphAddressAddition.natWord value) (GraphAddressAddition.bits value)
    _ _ selected (by
      change TM2OutputsInTime GraphAddressAddition.bitMachine
        ((GraphAddressAddition.natWord value).map id) _ _
      simpa only [List.map_id] using GraphAddressAddition.bitOutputs value)
  have joined := StackMachineComposition.outputs (bitProjection index)
    GraphAddressAddition.digitMachine (Equiv.refl (Option Bool))
    (Indexed.argumentWire packet) (GraphAddressAddition.bits value)
    (GraphAddressAddition.digitWord value) _ _ projected (by
      change TM2OutputsInTime GraphAddressAddition.digitMachine
        ((GraphAddressAddition.bits value).map id) _ _
      simpa only [List.map_id] using GraphAddressAddition.digitOutputs value)
  rw [digits_exact] at joined
  apply WordEqualityMachine.within joined
  have selectedLength := EmittedCertificateInsertion.field_length_le packet index
  rw [encoded] at selectedLength
  have bitLength := GraphAddressAddition.bits_length value
  have digitLength := digits_length value
  simp only [selectTemplate, List.length_cons, List.length_nil]
  omega

def retainedProjection {arity : Nat} (index : Fin arity) :=
  RetainedWordExecution.WithOutput.Framed.machine (projection index)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

attribute [local implicit_reducible] retainedProjection
local instance {arity : Nat} (index : Fin arity) :
    Fintype ((retainedProjection index).Γ (retainedProjection index).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) :
    Inhabited ((retainedProjection index).Γ (retainedProjection index).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def projectedFields {arity : Nat} (packet : Fin arity → List Alphabet)
    (value : Nat) : Fin (arity + 1) → List Alphabet :=
  Fin.addCases packet (fun _ => field (naturalKey value))

theorem retained_word {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) (value : Nat) :
    RetainedWordExecution.WithOutput.Framed.outputWord (projection index)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (Indexed.argumentWire packet) (field (naturalKey value)) =
      Indexed.argumentWire (projectedFields packet value) := by
  change (Indexed.argumentWire packet).map id ++ (field (naturalKey value)).map some ++ [none] =
    Indexed.argumentWire (projectedFields packet value)
  rw [List.map_id]
  exact (RelocatedCertificateInsertion.argumentWire_add_one packet
    (field (naturalKey value))).symm

theorem projected_length {arity : Nat} (packet : Fin arity → List Alphabet)
    (value : Nat) :
    (Indexed.argumentWire (projectedFields packet value)).length =
      (Indexed.argumentWire packet).length + (field (naturalKey value)).length + 1 := by
  unfold projectedFields
  rw [RelocatedCertificateInsertion.argumentWire_add_one]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]

noncomputable def retainedProjectionOutputs {arity : Nat} (index : Fin arity)
    (packet : Fin arity → List Alphabet) (value : Nat)
    (encoded : packet index = GraphAddressAddition.natWord value) :
    TM2OutputsInTime (retainedProjection index) (Indexed.argumentWire packet)
      (some (Indexed.argumentWire (projectedFields packet value)))
      (70 * ((Indexed.argumentWire packet).length + 1)) := by
  have retained := RetainedWordExecution.WithOutput.Framed.outputs (projection index)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (Indexed.argumentWire packet) (field (naturalKey value)) _
    (projectionOutputs index packet value encoded)
  rw [retained_word] at retained
  apply WordEqualityMachine.within retained
  have bound := (digits_length value).trans
    (by simpa only [← encoded] using EmittedCertificateInsertion.field_length_le packet index)
  omega

def fields (roots : Array Nat) (root : Nat) : Fin 3 → List Alphabet :=
  ![table (indexed roots), GraphAddressAddition.natWord roots.size,
    GraphAddressAddition.natWord root]

def inputWire (roots : Array Nat) (root : Nat) := Indexed.argumentWire (fields roots root)
def middleFields (roots : Array Nat) (root : Nat) := projectedFields (fields roots root) roots.size
def finalFields (roots : Array Nat) (root : Nat) := projectedFields (middleFields roots root) root

def projections := StackMachineComposition.machine
  (retainedProjection (1 : Fin 3)) (retainedProjection (2 : Fin 4))
  (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] projections
local instance : Fintype (projections.Γ projections.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (projections.Γ projections.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

theorem field_bounds (roots : Array Nat) (root : Nat) :
    (field (naturalKey roots.size)).length ≤ (inputWire roots root).length ∧
      (field (naturalKey root)).length ≤ (inputWire roots root).length := by
  exact ⟨(digits_length roots.size).trans
    (EmittedCertificateInsertion.field_length_le (fields roots root) 1),
    (digits_length root).trans
    (EmittedCertificateInsertion.field_length_le (fields roots root) 2)⟩

theorem middle_length (roots : Array Nat) (root : Nat) :
    (Indexed.argumentWire (middleFields roots root)).length =
      (inputWire roots root).length + (field (naturalKey roots.size)).length + 1 :=
  projected_length _ _

theorem final_length (roots : Array Nat) (root : Nat) :
    (Indexed.argumentWire (finalFields roots root)).length =
      (inputWire roots root).length + (field (naturalKey roots.size)).length +
        (field (naturalKey root)).length + 2 := by
  rw [finalFields, projected_length, middle_length]
  omega

noncomputable def projectionsOutputs (roots : Array Nat) (root : Nat) :
    TM2OutputsInTime projections (inputWire roots root)
      (some (Indexed.argumentWire (finalFields roots root)))
      (224 * ((inputWire roots root).length + 1)) := by
  have first := retainedProjectionOutputs (1 : Fin 3) (fields roots root) roots.size rfl
  have second := retainedProjectionOutputs (2 : Fin 4) (middleFields roots root) root rfl
  have joined := StackMachineComposition.outputs (retainedProjection (1 : Fin 3))
    (retainedProjection (2 : Fin 4)) (Equiv.refl (Option Alphabet))
    (inputWire roots root) (Indexed.argumentWire (middleFields roots root))
    (Indexed.argumentWire (finalFields roots root)) _ _ first (by
      change TM2OutputsInTime (retainedProjection (2 : Fin 4))
        ((Indexed.argumentWire (middleFields roots root)).map id) _ _
      simpa only [List.map_id, finalFields] using second)
  apply WordEqualityMachine.within joined
  have bounded := (field_bounds roots root).1
  rw [middle_length]
  change 70 * ((inputWire roots root).length + 1) +
    2 * ((inputWire roots root).length + (field (naturalKey roots.size)).length + 1) + 2 +
    70 * ((inputWire roots root).length + (field (naturalKey roots.size)).length + 1 + 1) ≤ _
  omega

def route : List (Fin 5) := [0, 3, 4]

theorem routed_word (roots : Array Nat) (root : Nat) :
    Indexed.frame (route.map (finalFields roots root)) =
      TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root) := by
  rfl

local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) route).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) route).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) route).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) route).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def routed := StackMachineComposition.machine projections
  (FramedFieldSelection.machine (Γ := Alphabet) route) (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] routed
local instance : Fintype (routed.Γ routed.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (routed.Γ routed.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

noncomputable def routedOutputs (roots : Array Nat) (root : Nat) :
    TM2OutputsInTime routed (inputWire roots root)
      (some (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root)))
      (350 * ((inputWire roots root).length + 1)) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet) route (finalFields roots root)
  rw [routed_word] at selected
  have joined := StackMachineComposition.outputs projections
    (FramedFieldSelection.machine (Γ := Alphabet) route) (Equiv.refl (Option Alphabet))
    (inputWire roots root) (Indexed.argumentWire (finalFields roots root))
    (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root)) _ _
    (projectionsOutputs roots root) (by
      change TM2OutputsInTime (FramedFieldSelection.machine (Γ := Alphabet) route)
        ((Indexed.argumentWire (finalFields roots root)).map id) _ _
      simpa only [List.map_id] using selected)
  apply WordEqualityMachine.within joined
  obtain ⟨firstBound, secondBound⟩ := field_bounds roots root
  simp only [route, List.length_cons, List.length_nil]
  rw [final_length]
  omega

def machine := StackMachineComposition.machine routed TableAppend.machine
  (Equiv.refl (Option Alphabet))

theorem packet_length (roots : Array Nat) (root : Nat) :
    (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root)).length + 4 =
      (inputWire roots root).length := by
  simp only [TableAppend.packet, TableAppend.fields, inputWire, fields,
    Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ, List.length_append,
    List.length_map, List.length_cons, List.length_nil, List.append_nil]
  have natLength (value : Nat) : (GraphAddressAddition.natWord value).length =
      (field (naturalKey value)).length + 2 := by
    simp [GraphAddressAddition.natWord, Binary.encodeWith, Codec.nat,
      encodeData_atom, natural, field, naturalKey]
  rw [natLength, natLength]
  omega

/-- Complete physical insertion. The natural fields are supplied once, in
their original codec, and both binary row fields are earned by execution. -/
noncomputable def outputs (roots : Array Nat) (root : Nat) :
    TM2OutputsInTime machine (inputWire roots root)
      (some (table (indexed (roots.push root))))
      (512 * ((inputWire roots root).length + 1)) := by
  have appended := TableAppend.indexedOutputs roots root
  have joined := StackMachineComposition.outputs routed TableAppend.machine
    (Equiv.refl (Option Alphabet)) (inputWire roots root)
    (TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root))
    (table (indexed (roots.push root))) _ _ (routedOutputs roots root) (by
      change TM2OutputsInTime TableAppend.machine
        ((TableAppend.packet (indexed roots) (naturalKey roots.size) (naturalKey root)).map id) _ _
      simpa only [List.map_id] using appended)
  apply WordEqualityMachine.within joined
  have size := packet_length roots root
  omega

theorem run_exact (roots : Array Nat) (root : Nat) {word : List Alphabet}
    (finished : TM2Outputs machine (inputWire roots root) (some word)) :
    word = table (indexed (roots.push root)) :=
  StackMachineComposition.outputs_unique finished (outputs roots root).toEvalsTo

noncomputable def realization : TM2ComputableInPolyTime
    (fun pair : Array Nat × Nat => inputWire pair.1 pair.2)
    (fun roots => table (indexed roots)) (fun pair => pair.1.push pair.2) where
  tm := machine
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C 512 * (Polynomial.X + Polynomial.C 1)
  outputsFun pair := by
    change TM2OutputsInTime machine ((inputWire pair.1 pair.2).map id)
      (some ((table (indexed (pair.1.push pair.2))).map id)) _
    simp only [List.map_id, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    exact outputs pair.1 pair.2

/-- The original resolver sees the newly installed source index, including
when its physical root has appeared at another index already. -/
theorem new_index_lookup (roots : Array Nat) (root : Nat) :
    lookup (naturalKey roots.size) (indexed (roots.push root)) = some (naturalKey root) := by
  rw [lookup_indexed]
  simp

theorem old_index_lookup (roots : Array Nat) (root query : Nat)
    (earlier : query < roots.size) :
    lookup (naturalKey query) (indexed (roots.push root)) =
      lookup (naturalKey query) (indexed roots) := by
  rw [lookup_indexed, lookup_indexed]
  simp [Array.getElem?_push, earlier, Nat.ne_of_lt earlier]

theorem future_index_lookup (roots : Array Nat) (root query : Nat)
    (future : roots.size + 1 ≤ query) :
    lookup (naturalKey query) (indexed (roots.push root)) = none := by
  rw [lookup_indexed, Array.getElem?_eq_none (by simpa using future)]
  rfl

/-- The same successful save task as the proved controller installs the
actual new table. Its claim already carries original replay-earned lookup
and source-goal checks; the writer adds no theorem authority. -/
theorem controller_save (definition : Mettapedia.GSLT.LanguageDef.ValidatedCalculusLanguageDef)
    (state : ChronologicalDriver.State definition)
    (claim : ChronologicalDriver.Claim definition state.checkedPrefix)
    (goal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (index : Nat)
    (rest : List ChronologicalDriver.Task)
    (work : state.todo = .save goal index :: rest)
    (returned : state.values = [claim]) (correctGoal : claim.goal = goal)
    (correctIndex : state.saved.length = index) :
    ∃ after : ChronologicalDriver.State definition,
      ChronologicalDriver.step definition (.running state) = .running after ∧
      after.checkedPrefix = state.checkedPrefix ∧
      HEq after.saved (state.saved ++ [claim]) ∧
      Nonempty (TM2OutputsInTime machine
        (inputWire (state.saved.map (fun saved => saved.root)).toArray claim.root)
        (some (table (indexed (after.saved.map (fun saved => saved.root)).toArray)))
        (512 * ((inputWire (state.saved.map (fun saved => saved.root)).toArray claim.root).length + 1))) := by
  let after : ChronologicalDriver.State definition :=
    { state with todo := rest, values := [], saved := state.saved ++ [claim] }
  refine ⟨after, ?_, rfl, (by rfl), ?_⟩
  · simp only [ChronologicalDriver.step, work, returned, correctGoal, correctIndex,
      and_self, ↓reduceIte]
    rfl
  · have appended := outputs (state.saved.map (fun saved => saved.root)).toArray claim.root
    have rows : (after.saved.map (fun saved => saved.root)).toArray =
        (state.saved.map (fun saved => saved.root)).toArray.push claim.root := by
      simp [after, List.map_append]
    rw [rows]
    exact ⟨appended⟩

namespace Controls

theorem repeated_root_keeps_distinct_indices :
    lookup (naturalKey 0) (indexed (#[7].push 7)) = some (naturalKey 7) ∧
      lookup (naturalKey 1) (indexed (#[7].push 7)) = some (naturalKey 7) ∧
      (indexed (#[7].push 7)).length = 2 := by decide +kernel

theorem changed_root_observable :
    lookup (naturalKey 1) (indexed (#[7].push 13)) ≠
      lookup (naturalKey 1) (indexed (#[7].push 14)) := by decide +kernel

theorem future_is_missing :
    lookup (naturalKey 2) (indexed (#[7].push 7)) = none := by decide +kernel

end Controls

end Mettapedia.Languages.HOLLight.SavedRootInsertion

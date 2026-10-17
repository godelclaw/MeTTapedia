import Mettapedia.Languages.HOLLight.GraphRelocationEmission
import Mettapedia.Languages.HOLLight.EmittedCertificateInsertion

/-!
# One physical relocation and chronological insertion

A packet carries the original relocation fields followed by the earlier
receipt list. Relocation computes its actual addresses and certificate word.
The retained packet routes that word, together with the earlier receipts, to
the original certificate parser and insertion machine. No decoded relocation
result is supplied to the second stage by the caller.

The descriptor is fixed; its finite selectors and original template size are
charged in the coefficient. Constructing descriptors from a runtime calculus
and admitting arbitrary packet bytes belong to the complete driver.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion

open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Logic.DerivationGraph
open ProofExecution ProofDataEncoding

abbrev Alphabet := Binary.Alphabet

def fields {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt) :
    Fin ((arity + premiseCount + 1) + 1) → List Alphabet :=
  Fin.addCases (GraphRelocationEmission.inputFields payload roots base)
    (fun _ => encodeWith (Codec.list receiptCodec) earlier)

def inputWire {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt) :=
  Indexed.argumentWire (fields payload roots base earlier)

def selector (arity premiseCount : Nat) : List (Fin ((arity + premiseCount + 1) + 1)) :=
  List.ofFn (fun index : Fin (arity + premiseCount + 1) => index.castSucc)

theorem selected_wire {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt) :
    Indexed.frame ((selector arity premiseCount).map (fields payload roots base earlier)) =
      Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base) := by
  unfold selector
  simp only [List.map_ofFn, Indexed.argumentWire, ← List.ofFn_eq_map]
  congr 1
  congr 1
  funext index
  change Fin.addCases (GraphRelocationEmission.inputFields payload roots base)
    (fun _ : Fin 1 => encodeWith (Codec.list receiptCodec) earlier) (index.castAdd 1) =
      GraphRelocationEmission.inputFields payload roots base index
  exact Fin.addCases_left index

theorem argumentWire_add_one {arity : Nat} (front : Fin arity → List Alphabet)
    (last : List Alphabet) :
    Indexed.argumentWire (Fin.addCases front (fun _ : Fin 1 => last)) =
      Indexed.argumentWire front ++ last.map some ++ [none] := by
  unfold Indexed.argumentWire
  simp only [← List.ofFn_eq_map]
  rw [List.ofFn_add]
  have left : List.ofFn (fun index : Fin arity =>
      Fin.addCases front (fun _ : Fin 1 => last)
        (index.castLE (by omega : arity ≤ arity + 1))) = List.ofFn front := by
    congr 1
    funext index
    have cast : index.castLE (by omega : arity ≤ arity + 1) = index.castAdd 1 := by
      apply Fin.ext
      rfl
    rw [cast]
    exact Fin.addCases_left index
  rw [left]
  simp only [Fin.addCases_right, List.ofFn_succ, List.ofFn_zero, Indexed.frame,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

theorem input_length {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt) :
    (inputWire payload roots base earlier).length =
      (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length +
        (encodeWith (Codec.list receiptCodec) earlier).length + 1 := by
  unfold inputWire fields
  rw [argumentWire_add_one]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]

local instance (arity premiseCount : Nat) :
    Fintype ((FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount)).Γ
      (FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount)).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity premiseCount : Nat) :
    Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount)).Γ
      (FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount)).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def selectedMachine {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  StackMachineComposition.machine
    (FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount))
    (GraphRelocationEmission.machine premiseCount internalCount block safe)
    (Equiv.refl (Option Alphabet))

attribute [local implicit_reducible] selectedMachine StackMachineComposition.machine

local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Fintype ((selectedMachine premiseCount internalCount block safe).Γ
      (selectedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Inhabited ((selectedMachine premiseCount internalCount block safe).Γ
      (selectedMachine premiseCount internalCount block safe).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Inhabited ((selectedMachine premiseCount internalCount block safe).Γ
      (selectedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def retainedMachine {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  RetainedWordExecution.WithOutput.Framed.machine
    (selectedMachine premiseCount internalCount block safe)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

attribute [local implicit_reducible] retainedMachine

local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Fintype ((retainedMachine premiseCount internalCount block safe).Γ
      (retainedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Inhabited ((retainedMachine premiseCount internalCount block safe).Γ
      (retainedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def route (arity premiseCount : Nat) :
    List (Fin (((arity + premiseCount + 1) + 1) + 1)) :=
  [⟨arity + premiseCount + 1, by omega⟩, ⟨arity + premiseCount + 2, by omega⟩]

def routedMachine {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  StackMachineComposition.machine (retainedMachine premiseCount internalCount block safe)
    (FramedFieldSelection.machine (Γ := Alphabet) (route arity premiseCount))
    (Equiv.refl (Option Alphabet))

local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Fintype ((routedMachine premiseCount internalCount block safe).Γ
      (routedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    Inhabited ((routedMachine premiseCount internalCount block safe).Γ
      (routedMachine premiseCount internalCount block safe).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))

def machine {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  StackMachineComposition.machine (routedMachine premiseCount internalCount block safe)
    EmittedCertificateInsertion.machine (Equiv.refl (Option Alphabet))

def Aligned {arity : Nat} (block : GraphRelocationEmission.Block arity)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet) : Prop :=
  List.Forall₂ (fun node receipt =>
    Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
    Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
    Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
    node.parents = receipt.parents) block.1 receipts

def emissionFactor {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) : Nat :=
  ((GraphRelocationEmission.template premiseCount internalCount block safe).length + 1) *
    ((GraphAddressSequence.plan (GraphRelocationEmission.offsets internalCount)).length + 1)

theorem emission_length {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat)
    (aligned : Aligned block receipts payload) :
    (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2))).length ≤
      emissionFactor premiseCount internalCount block safe *
        ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1) := by
  rw [← GraphRelocationEmission.template_exact internalCount block safe receipts payload roots base aligned]
  have emitted := Indexed.instantiateWire_length
    (GraphRelocationEmission.template premiseCount internalCount block safe)
    (Indexed.argumentWire (GraphRelocationEmission.expandedFields internalCount payload roots base))
  rw [Indexed.instantiateWire_argumentWire] at emitted
  have addressLength := (GraphRelocationEmission.result_length_le
    (GraphRelocationEmission.offsets internalCount) base).trans
    (GraphAddressSequence.prepared_length (GraphRelocationEmission.offsets internalCount) base)
  have baseLength := GraphRelocationEmission.base_length_le payload roots base
  have enlarged :
      (Indexed.argumentWire (GraphRelocationEmission.expandedFields internalCount payload roots base)).length + 1 ≤
      ((GraphAddressSequence.plan (GraphRelocationEmission.offsets internalCount)).length + 1) *
        ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1) := by
    rw [GraphRelocationEmission.expanded_wire, List.length_append]
    have bound := addressLength.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right baseLength 1))
    nlinarith only [bound]
  apply emitted.trans
  calc
    _ ≤ (GraphRelocationEmission.template premiseCount internalCount block safe).length *
        (((GraphAddressSequence.plan (GraphRelocationEmission.offsets internalCount)).length + 1) *
          ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1)) :=
      Nat.mul_le_mul_left _ enlarged
    _ ≤ emissionFactor premiseCount internalCount block safe *
        ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1) := by
      unfold emissionFactor
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))

def selectedCoefficient {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  8 * (arity + premiseCount + 1) + 14 +
    GraphRelocationEmission.coefficient premiseCount internalCount block safe

noncomputable def selectedOutputs {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (aligned : Aligned block receipts payload) :
    TM2OutputsInTime (selectedMachine premiseCount internalCount block safe)
      (inputWire payload roots base earlier)
      (some (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2))))
      (selectedCoefficient premiseCount internalCount block safe *
        ((inputWire payload roots base earlier).length + 1)) := by
  have selected := FramedFieldSelection.outputs (Γ := Alphabet)
    (selector arity premiseCount) (fields payload roots base earlier)
  rw [selected_wire] at selected
  have emitted := GraphRelocationEmission.outputs internalCount block safe receipts payload roots base aligned
  have linear : TM2OutputsInTime (GraphRelocationEmission.machine premiseCount internalCount block safe)
      (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base))
      (some (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2))))
      (GraphRelocationEmission.coefficient premiseCount internalCount block safe *
        ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1)) := by
    apply WordEqualityMachine.within emitted
    exact GraphRelocationEmission.clock_linear internalCount block safe payload roots base
  have joined := StackMachineComposition.outputs
    (FramedFieldSelection.machine (Γ := Alphabet) (selector arity premiseCount))
    (GraphRelocationEmission.machine premiseCount internalCount block safe)
    (Equiv.refl (Option Alphabet)) (inputWire payload roots base earlier)
    (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base))
    (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)))
    _ _ selected (by
      change TM2OutputsInTime (GraphRelocationEmission.machine premiseCount internalCount block safe)
        ((Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).map id) _ _
      simpa only [List.map_id] using linear)
  apply WordEqualityMachine.within joined
  have input := input_length payload roots base earlier
  have relocationBound := Nat.mul_le_mul_left
    (GraphRelocationEmission.coefficient premiseCount internalCount block safe)
    (show (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1 ≤
      (inputWire payload roots base earlier).length + 1 by omega)
  simp only [selector, List.length_ofFn]
  unfold selectedCoefficient
  dsimp only [inputWire] at input relocationBound ⊢
  nlinarith only [input, relocationBound]

def retainedFields {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (expanded : ProofSystem.Certificate) :
    Fin (((arity + premiseCount + 1) + 1) + 1) → List Alphabet :=
  Fin.addCases (fields payload roots base earlier) (fun _ => encodeCertificate expanded)

theorem retained_wire {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat)
    (base : Nat) (earlier : List Receipt) (expanded : ProofSystem.Certificate) :
    RetainedWordExecution.WithOutput.Framed.outputWord
      (selectedMachine premiseCount internalCount block safe)
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
      (inputWire payload roots base earlier) (encodeCertificate expanded) =
    Indexed.argumentWire (retainedFields payload roots base earlier expanded) := by
  unfold retainedFields
  rw [argumentWire_add_one]
  have inputIdentity : (inputWire payload roots base earlier).map
      (Equiv.refl (Option Alphabet)) = inputWire payload roots base earlier := by simp
  have outputIdentity : (encodeCertificate expanded).map
      (fun symbol => some ((Equiv.refl Alphabet) symbol)) =
      (encodeCertificate expanded).map some := by
    congr 1
  unfold RetainedWordExecution.WithOutput.Framed.outputWord
  change (inputWire payload roots base earlier).map (Equiv.refl (Option Alphabet)) ++
      (encodeCertificate expanded).map (fun symbol => some ((Equiv.refl Alphabet) symbol)) ++
        [none] = Indexed.argumentWire (fields payload roots base earlier) ++
          (encodeCertificate expanded).map some ++ [none]
  rw [inputIdentity, outputIdentity]
  simp only [inputWire, List.append_assoc]

theorem routed_wire {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (expanded : ProofSystem.Certificate) :
    Indexed.frame ((route arity premiseCount).map
      (retainedFields payload roots base earlier expanded)) =
      EmittedCertificateInsertion.inputWire earlier expanded := by
  have earlierField : retainedFields payload roots base earlier expanded
      ⟨arity + premiseCount + 1, by omega⟩ = encodeWith (Codec.list receiptCodec) earlier := by
    have cast : (⟨arity + premiseCount + 1, by omega⟩ :
        Fin (((arity + premiseCount + 1) + 1) + 1)) =
        (⟨arity + premiseCount + 1, by omega⟩ : Fin ((arity + premiseCount + 1) + 1)).castAdd 1 := by
      apply Fin.ext
      rfl
    rw [cast, retainedFields, Fin.addCases_left]
    change Fin.addCases (GraphRelocationEmission.inputFields payload roots base)
      (fun _ : Fin 1 => encodeWith (Codec.list receiptCodec) earlier)
      ((0 : Fin 1).natAdd (arity + premiseCount + 1)) =
        encodeWith (Codec.list receiptCodec) earlier
    exact Fin.addCases_right 0
  have emittedField : retainedFields payload roots base earlier expanded
      ⟨arity + premiseCount + 2, by omega⟩ = encodeCertificate expanded := by
    change Fin.addCases (fields payload roots base earlier)
      (fun _ : Fin 1 => encodeCertificate expanded)
      ((0 : Fin 1).natAdd ((arity + premiseCount + 1) + 1)) = encodeCertificate expanded
    exact Fin.addCases_right 0
  simp only [route, List.map_cons, List.map_nil, earlierField, emittedField]
  simp [EmittedCertificateInsertion.inputWire, EmittedCertificateInsertion.fields,
    Indexed.argumentWire, List.finRange_succ]

def retainedCoefficient {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  selectedCoefficient premiseCount internalCount block safe + 23 +
    22 * emissionFactor premiseCount internalCount block safe

noncomputable def retainedOutputs {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (aligned : Aligned block receipts payload) :
    TM2OutputsInTime (retainedMachine premiseCount internalCount block safe)
      (inputWire payload roots base earlier)
      (some (Indexed.argumentWire (retainedFields payload roots base earlier
        (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)))))
      (retainedCoefficient premiseCount internalCount block safe *
        ((inputWire payload roots base earlier).length + 1)) := by
  have ran := RetainedWordExecution.WithOutput.Framed.outputs
    (selectedMachine premiseCount internalCount block safe)
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)
    (inputWire payload roots base earlier)
    (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)))
    _ (selectedOutputs internalCount block safe receipts payload roots base earlier aligned)
  rw [retained_wire] at ran
  apply WordEqualityMachine.within ran
  have input := input_length payload roots base earlier
  have length := (emission_length internalCount block safe receipts payload roots base aligned).trans
    (Nat.mul_le_mul_left _ (show
      (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1 ≤
        (inputWire payload roots base earlier).length + 1 by omega))
  unfold retainedCoefficient
  nlinarith only [length]

def routedCoefficient {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  retainedCoefficient premiseCount internalCount block safe +
    30 * (emissionFactor premiseCount internalCount block safe + 2)

noncomputable def routedOutputs {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (aligned : Aligned block receipts payload) :
    TM2OutputsInTime (routedMachine premiseCount internalCount block safe)
      (inputWire payload roots base earlier)
      (some (EmittedCertificateInsertion.inputWire earlier
        (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2))))
      (routedCoefficient premiseCount internalCount block safe *
        ((inputWire payload roots base earlier).length + 1)) := by
  let expanded := GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)
  have routed := FramedFieldSelection.outputs (Γ := Alphabet) (route arity premiseCount)
    (retainedFields payload roots base earlier expanded)
  rw [routed_wire] at routed
  have joined := StackMachineComposition.outputs
    (retainedMachine premiseCount internalCount block safe)
    (FramedFieldSelection.machine (Γ := Alphabet) (route arity premiseCount))
    (Equiv.refl (Option Alphabet)) (inputWire payload roots base earlier)
    (Indexed.argumentWire (retainedFields payload roots base earlier expanded))
    (EmittedCertificateInsertion.inputWire earlier expanded) _ _
    (retainedOutputs internalCount block safe receipts payload roots base earlier aligned) (by
      change TM2OutputsInTime (FramedFieldSelection.machine (Γ := Alphabet) (route arity premiseCount))
        ((Indexed.argumentWire (retainedFields payload roots base earlier expanded)).map id) _ _
      simpa only [List.map_id] using routed)
  apply WordEqualityMachine.within joined
  have input := input_length payload roots base earlier
  have length := (emission_length internalCount block safe receipts payload roots base aligned).trans
    (Nat.mul_le_mul_left _ (show
      (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1 ≤
        (inputWire payload roots base earlier).length + 1 by omega))
  have retainedLength :
      (Indexed.argumentWire (retainedFields payload roots base earlier expanded)).length =
      (inputWire payload roots base earlier).length + (encodeCertificate expanded).length + 1 := by
    unfold retainedFields
    rw [argumentWire_add_one]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, inputWire]
  rw [retainedLength]
  simp only [route, List.length_cons, List.length_nil]
  unfold routedCoefficient
  dsimp only [expanded] at *
  nlinarith only [length]

def coefficient {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :=
  routedCoefficient premiseCount internalCount block safe +
    852 * (emissionFactor premiseCount internalCount block safe + 3)

/-- The final graph is emitted by one composed machine; its selected root
comes from actual relocation and parsing rather than a supplied second input. -/
noncomputable def outputs {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (aligned : Aligned block receipts payload) :
    TM2OutputsInTime (machine premiseCount internalCount block safe)
      (inputWire payload roots base earlier)
      (some (encodeCertificate
        (earlier ++ (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)).1,
          (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)).2)))
      (coefficient premiseCount internalCount block safe *
        ((inputWire payload roots base earlier).length + 1)) := by
  let expanded := GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)
  have packed := EmittedCertificateInsertion.outputs earlier expanded
  have joined := StackMachineComposition.outputs
    (routedMachine premiseCount internalCount block safe) EmittedCertificateInsertion.machine
    (Equiv.refl (Option Alphabet)) (inputWire payload roots base earlier)
    (EmittedCertificateInsertion.inputWire earlier expanded)
    (encodeCertificate (earlier ++ expanded.1, expanded.2)) _ _
    (routedOutputs internalCount block safe receipts payload roots base earlier aligned) (by
      change TM2OutputsInTime EmittedCertificateInsertion.machine
        ((EmittedCertificateInsertion.inputWire earlier expanded).map id) _ _
      simpa only [List.map_id] using packed)
  apply WordEqualityMachine.within joined
  have input := input_length payload roots base earlier
  have length := (emission_length internalCount block safe receipts payload roots base aligned).trans
    (Nat.mul_le_mul_left _ (show
      (Indexed.argumentWire (GraphRelocationEmission.inputFields payload roots base)).length + 1 ≤
        (inputWire payload roots base earlier).length + 1 by omega))
  have packedLength : (EmittedCertificateInsertion.inputWire earlier expanded).length =
      (encodeWith (Codec.list receiptCodec) earlier).length + (encodeCertificate expanded).length + 2 := by
    simp [EmittedCertificateInsertion.inputWire, EmittedCertificateInsertion.fields,
      Indexed.argumentWire, Indexed.frame, List.finRange_succ, Nat.add_assoc]
  have bound : (EmittedCertificateInsertion.inputWire earlier expanded).length + 1 ≤
      (emissionFactor premiseCount internalCount block safe + 3) *
        ((inputWire payload roots base earlier).length + 1) := by
    rw [packedLength]
    dsimp only [expanded] at *
    nlinarith only [input, length]
  have charged := Nat.mul_le_mul_left 852 bound
  unfold coefficient
  nlinarith only [charged]

theorem run_decodes {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) (earlier : List Receipt)
    (aligned : Aligned block receipts payload) {word : List Alphabet}
    (finished : TM2Outputs (machine premiseCount internalCount block safe)
      (inputWire payload roots base earlier) (some word)) :
    decodeCertificate word = some
      (earlier ++ (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)).1,
        (GraphExpansion.expandBlock (List.ofFn roots) base (receipts, block.2)).2) := by
  have same := StackMachineComposition.outputs_unique finished
    (outputs internalCount block safe receipts payload roots base earlier aligned).toEvalsTo
  rw [same, decodeCertificate_encodeCertificate]

/-- The descriptor's payload image, rather than arbitrary unchecked bytes,
determines the original receipts whose machine execution is represented. -/
structure Packet {arity : Nat} (premiseCount : Nat)
    (block : GraphRelocationEmission.Block arity) where
  receipts : List Receipt
  payload : Fin arity → List Alphabet
  roots : Fin premiseCount → Nat
  base : Nat
  earlier : List Receipt
  aligned : Aligned block receipts payload

noncomputable def realization {arity : Nat} (premiseCount internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block) :
    TM2ComputableInPolyTime
      (fun packet : Packet premiseCount block =>
        inputWire packet.payload packet.roots packet.base packet.earlier)
      encodeCertificate (fun packet =>
        (packet.earlier ++ (GraphExpansion.expandBlock (List.ofFn packet.roots) packet.base
            (packet.receipts, block.2)).1,
          (GraphExpansion.expandBlock (List.ofFn packet.roots) packet.base (packet.receipts, block.2)).2)) where
  tm := machine premiseCount internalCount block safe
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C (coefficient premiseCount internalCount block safe) *
    (Polynomial.X + Polynomial.C 1)
  outputsFun packet := by
    change TM2OutputsInTime (machine premiseCount internalCount block safe)
      ((inputWire packet.payload packet.roots packet.base packet.earlier).map id)
      (some ((encodeCertificate
        (packet.earlier ++ (GraphExpansion.expandBlock (List.ofFn packet.roots) packet.base
            (packet.receipts, block.2)).1,
          (GraphExpansion.expandBlock (List.ofFn packet.roots) packet.base
            (packet.receipts, block.2)).2)).map id)) _
    simp only [List.map_id, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_X]
    exact outputs internalCount block safe packet.receipts packet.payload packet.roots
      packet.base packet.earlier packet.aligned

/-- The original prefix, selected roots and local block replay earn the
result's authority. The actual emitted bytes decode to that same graph. -/
theorem run_authorized {arity premiseCount : Nat} (internalCount : Nat)
    (block : GraphRelocationEmission.Block arity)
    (safe : GraphRelocationEmission.SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (aligned : Aligned block receipts payload)
    {policy : AxiomPolicy} [DecidablePred policy]
    {earlier : List Receipt} {cache : Array Theorem} {premises : List Theorem}
    {conclusion : Theorem}
    (prefixChecked : replay (ruleWitness policy) earlier = some cache)
    (selected : lookupPremises cache (List.ofFn roots) = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion (receipts, block.2))
    {word : List Alphabet}
    (finished : TM2Outputs (machine premiseCount internalCount block safe)
      (inputWire payload roots cache.size earlier) (some word)) :
    ∃ certificate, decodeCertificate word = some certificate ∧
      (ProofSystem.checker policy).check conclusion certificate = true := by
  refine ⟨(earlier ++ (GraphExpansion.expandBlock (List.ofFn roots) cache.size
      (receipts, block.2)).1,
    (GraphExpansion.expandBlock (List.ofFn roots) cache.size (receipts, block.2)).2),
    run_decodes internalCount block safe receipts payload roots cache.size earlier aligned finished, ?_⟩
  exact GraphExpansion.appendBlock_accepted prefixChecked selected checked

end Mettapedia.Languages.HOLLight.RelocatedCertificateInsertion

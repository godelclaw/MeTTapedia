import Mettapedia.Languages.HOLLight.GraphAddressSequence
import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Computability.RetainedWordExecution

/-!
# Original HOL block emission with earned physical addresses

A compiled original block retains its theorem, request and origin templates.
Runtime input carries their complete fields, the earlier physical roots and
current graph base. The existing sequence machine earns the new internal
addresses. Physical retention appends those address fields, and an indexed
copier emits the original certificate codec with only parent/root numbers
relocated. Address-field images are assumed at this stage; earlier-root
lookup authorization and malformed packet admission belong to the driver.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.GraphRelocationEmission
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Logic.DerivationGraph
open ProofExecution (Receipt)
open ProofDataEncoding EqualityExpansion.Emission
abbrev Alphabet := Binary.Alphabet
abbrev Plan (arity : Nat) := Indexed.Template Alphabet arity
abbrev Block (arity : Nat) := List (Node (Plan arity) (Plan arity) (Plan arity)) × Nat

def SafeBlock {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity) : Prop :=
  block.2 < premiseCount+internalCount ∧
    ∀ node ∈ block.1, ∀ index ∈ node.parents, index < premiseCount+internalCount

def inputFields {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) : Fin (arity+premiseCount+1) → List Alphabet :=
  Fin.addCases (Fin.addCases payload (fun index => GraphAddressAddition.natWord (roots index)))
    (fun _ => GraphAddressAddition.natWord base)

def internalFields (internalCount base : Nat) : Fin internalCount → List Alphabet :=
  fun index => GraphAddressAddition.natWord (base+index.val)

def expandedFields {arity premiseCount : Nat} (internalCount : Nat)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    Fin ((arity+premiseCount+1)+internalCount) → List Alphabet :=
  Fin.addCases (inputFields payload roots base) (internalFields internalCount base)

def liftPlan {arity : Nat} (premiseCount internalCount : Nat) (plan : Plan arity) :
    Plan ((arity+premiseCount+1)+internalCount) :=
  Templates.substitute plan (fun index => [.inr ⟨index.val,by omega⟩])

theorem liftPlan_exact {arity premiseCount : Nat} (internalCount : Nat) (plan : Plan arity)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    Indexed.instantiate (liftPlan premiseCount internalCount plan) (expandedFields internalCount payload roots base) =
      Indexed.instantiate plan payload := by
  rw [liftPlan,Templates.substitute_exact]
  congr 1
  funext index
  simp only [Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil]
  change Fin.addCases (inputFields payload roots base) (internalFields internalCount base)
    ((index.castAdd premiseCount).castAdd 1 |>.castAdd internalCount) = payload index
  simp [inputFields,Fin.addCases_left]

def addressPlan {arity : Nat} (premiseCount internalCount : Nat) (index : Fin (premiseCount+internalCount)) :
    Plan ((arity+premiseCount+1)+internalCount) :=
  if external : index.val < premiseCount then [.inr ⟨arity+index.val,by omega⟩]
  else [.inr ⟨arity+premiseCount+1+(index.val-premiseCount),by have bound:=index.isLt; omega⟩]

theorem addressPlan_exact {arity premiseCount : Nat} (internalCount : Nat)
    (index : Fin (premiseCount+internalCount)) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    Indexed.instantiate (addressPlan premiseCount internalCount index) (expandedFields internalCount payload roots base) =
      GraphAddressAddition.natWord (GraphExpansion.address (List.ofFn roots) base index.val) := by
  unfold addressPlan
  split
  · rename_i external
    simp only [Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil]
    have field : (⟨arity+index.val,by omega⟩ : Fin ((arity+premiseCount+1)+internalCount)) =
        (((⟨index.val,external⟩ : Fin premiseCount).natAdd arity).castAdd 1).castAdd internalCount := by apply Fin.ext; rfl
    rw [field]
    rw [expandedFields,Fin.addCases_left,inputFields,Fin.addCases_left,Fin.addCases_right]
    simp [GraphExpansion.address,external,List.length_ofFn]
  · rename_i internal
    simp only [Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil]
    have within : index.val-premiseCount < internalCount := by have bound:=index.isLt; omega
    have field : (⟨arity+premiseCount+1+(index.val-premiseCount),by omega⟩ : Fin ((arity+premiseCount+1)+internalCount)) =
        (⟨index.val-premiseCount,within⟩ : Fin internalCount).natAdd (arity+premiseCount+1) := by apply Fin.ext; rfl
    rw [field]
    rw [expandedFields,Fin.addCases_right]
    simp [internalFields,GraphExpansion.address,internal,List.length_ofFn]

def parentPlan {arity : Nat} (premiseCount internalCount : Nat) (parents : List Nat)
    (bounded : ∀ index ∈ parents, index < premiseCount+internalCount) :
    Plan ((arity+premiseCount+1)+internalCount) :=
  listTemplate (parents.attach.map (fun index => addressPlan premiseCount internalCount ⟨index.val,bounded index.val index.property⟩))

theorem parentPlan_exact {arity premiseCount : Nat} (internalCount : Nat) (parents : List Nat)
    (bounded : ∀ index ∈ parents, index < premiseCount+internalCount)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    Indexed.instantiate (parentPlan premiseCount internalCount parents bounded)
      (expandedFields internalCount payload roots base) =
      encodeWith (Codec.list Codec.nat) (parents.map (GraphExpansion.address (List.ofFn roots) base)) := by
  induction parents with
  | nil => rfl
  | cons first rest ih =>
    simp only [parentPlan,List.attach_cons,List.map_cons,listTemplate,Templates.pair_exact]
    rw [addressPlan_exact]
    have restBound : ∀ index ∈ rest, index < premiseCount+internalCount := fun index member => bounded index (by simp [member])
    simp only [List.map_map,Function.comp_def]
    change 4 :: GraphAddressAddition.natWord (GraphExpansion.address (List.ofFn roots) base first) ++
      Indexed.instantiate (parentPlan premiseCount internalCount rest restBound) _ = _
    rw [ih restBound]
    simp [encodeWith,Codec.list,Codec.putList,Codec.nat,encodeData_pair,GraphAddressAddition.natWord]

def relocatedNodePlan {arity : Nat} (premiseCount internalCount : Nat)
    (node : Node (Plan arity) (Plan arity) (Plan arity))
    (bounded : ∀ index ∈ node.parents, index < premiseCount+internalCount) :
    Plan ((arity+premiseCount+1)+internalCount) :=
  Templates.pair (liftPlan premiseCount internalCount node.conclusion)
    (Templates.pair (liftPlan premiseCount internalCount node.witness)
      (Templates.pair (parentPlan premiseCount internalCount node.parents bounded)
        (liftPlan premiseCount internalCount node.origin)))

theorem relocatedNodePlan_exact {arity premiseCount : Nat} (internalCount : Nat)
    (node : Node (Plan arity) (Plan arity) (Plan arity)) (receipt : Receipt)
    (bounded : ∀ index ∈ node.parents, index < premiseCount+internalCount)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (conclusion : Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion)
    (witness : Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness)
    (origin : Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin)
    (parents : node.parents = receipt.parents) :
    Indexed.instantiate (relocatedNodePlan premiseCount internalCount node bounded)
      (expandedFields internalCount payload roots base) =
      encodeWith receiptCodec (receipt.relocate (GraphExpansion.address (List.ofFn roots) base)) := by
  simp only [relocatedNodePlan,Templates.pair_exact,liftPlan_exact,parentPlan_exact,conclusion,witness,origin,parents]
  simp [encodeWith,receiptCodec,Codec.prod,Codec.mapped,Node.relocate,encodeData_pair]

def template {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) : Plan ((arity+premiseCount+1)+internalCount) :=
  Templates.pair
    (listTemplate (block.1.attach.map (fun node => relocatedNodePlan premiseCount internalCount node.val
      (safe.2 node.val node.property))))
    (addressPlan premiseCount internalCount ⟨block.2,safe.1⟩)


theorem template_exact {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (receipts : List Receipt)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
      Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
      Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
      node.parents = receipt.parents) block.1 receipts) :
    Indexed.instantiate (template premiseCount internalCount block safe)
      (expandedFields internalCount payload roots base) =
      encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)) := by
  have lower (sourceNodes : List (Node (Plan arity) (Plan arity) (Plan arity))) (resultNodes : List Receipt)
      (bounded : ∀ node ∈ sourceNodes, ∀ index ∈ node.parents, index < premiseCount+internalCount)
      (correspond : List.Forall₂ (fun node receipt =>
        Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
        Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
        Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
        node.parents = receipt.parents) sourceNodes resultNodes) :
      List.Forall₂ (fun plan receipt => Indexed.instantiate plan (expandedFields internalCount payload roots base) =
        encodeWith receiptCodec receipt)
        (sourceNodes.attach.map (fun node => relocatedNodePlan premiseCount internalCount node.val (bounded node.val node.property)))
        (resultNodes.map (Node.relocate (GraphExpansion.address (List.ofFn roots) base))) := by
    revert bounded
    induction correspond with
    | nil => intro bounded; exact .nil
    | @cons node receipt nodes receipts first rest ih =>
      intro bounded
      simp only [List.attach_cons,List.map_cons,List.map_map,Function.comp_def]
      apply List.Forall₂.cons
      · exact relocatedNodePlan_exact internalCount node receipt (bounded node (by simp)) payload roots base
          first.1 first.2.1 first.2.2.1 first.2.2.2
      · apply ih
        intro memberNode member index parent
        exact bounded memberNode (by simp [member]) index parent
  have nodes := lower block.1 receipts safe.2 aligned
  have packed := listTemplate_exact (expandedFields internalCount payload roots base) nodes
  simp only [template,Templates.pair_exact,packed,addressPlan_exact,GraphExpansion.expandBlock]
  simp [encodeCertificate,certificateCodec,encodeWith,Codec.prod,Codec.nat,encodeData_pair,GraphAddressAddition.natWord]


def offsets (internalCount : Nat) : List Nat := (List.finRange internalCount).map Fin.val

theorem internal_wire (internalCount base : Nat) :
    GraphAddressSequence.resultWire (offsets internalCount) base = Indexed.argumentWire (internalFields internalCount base) := by
  simp only [GraphAddressSequence.resultWire,offsets,Indexed.argumentWire,List.map_map,Function.comp_def]
  rfl

theorem expanded_wire {arity premiseCount : Nat} (internalCount : Nat)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    Indexed.argumentWire (expandedFields internalCount payload roots base) =
      Indexed.argumentWire (inputFields payload roots base) ++ GraphAddressSequence.resultWire (offsets internalCount) base := by
  rw [internal_wire]
  unfold expandedFields
  simp only [Indexed.argumentWire,← List.ofFn_eq_map]
  rw [List.ofFn_add]
  have left : List.ofFn (fun index : Fin (arity+premiseCount+1) =>
      Fin.addCases (inputFields payload roots base) (internalFields internalCount base) (index.castLE (by omega : arity+premiseCount+1 ≤ (arity+premiseCount+1)+internalCount))) =
      List.ofFn (inputFields payload roots base) := by
    congr 1
    funext index
    have cast : index.castLE (by omega : arity+premiseCount+1 ≤ (arity+premiseCount+1)+internalCount) = index.castAdd internalCount := by apply Fin.ext; rfl
    rw [cast]
    exact Fin.addCases_left index
  have right : List.ofFn (fun index : Fin internalCount =>
      Fin.addCases (inputFields payload roots base) (internalFields internalCount base) (index.natAdd (arity+premiseCount+1))) =
      List.ofFn (internalFields internalCount base) := by
    congr 1
    funext index
    exact Fin.addCases_right index
  rw [left,right]
  exact List.flatMap_append

def basePlan (arity premiseCount : Nat) : Plan (arity+premiseCount+1) := [.inr ⟨arity+premiseCount,by omega⟩]

theorem basePlan_exact {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    Indexed.instantiate (basePlan arity premiseCount) (inputFields payload roots base) = GraphAddressAddition.natWord base := by
  simp only [basePlan,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil]
  change inputFields payload roots base ((0 : Fin 1).natAdd (arity+premiseCount)) = _
  rw [inputFields,Fin.addCases_right]

attribute [local implicit_reducible] StackMachineComposition.machine WordHomomorphismMachine.machine
  RetainedWordExecution.WithOutput.machine GraphAddressSequence.machine
local instance (arity premiseCount : Nat) : Fintype ((Indexed.machine (basePlan arity premiseCount)).Γ
    (Indexed.machine (basePlan arity premiseCount)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (arity premiseCount : Nat) : Inhabited ((Indexed.machine (basePlan arity premiseCount)).Γ
    (Indexed.machine (basePlan arity premiseCount)).k₁) := inferInstanceAs (Inhabited Alphabet)

def selectedAddressMachine (arity premiseCount internalCount : Nat) := StackMachineComposition.machine
  (Indexed.machine (basePlan arity premiseCount)) (GraphAddressSequence.machine (offsets internalCount)) (Equiv.refl Alphabet)
local instance (arity premiseCount internalCount : Nat) : Fintype ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((selectedAddressMachine arity premiseCount internalCount).Γ
    (selectedAddressMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def selectedClock {arity premiseCount : Nat} (internalCount : Nat) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :=
  8*((Indexed.argumentWire (inputFields payload roots base)).length+1) +
  2*(GraphAddressAddition.natWord base).length+2 + GraphAddressSequence.clock (offsets internalCount) base

noncomputable def selectedOutputs {arity premiseCount : Nat} (internalCount : Nat)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    TM2OutputsInTime (selectedAddressMachine arity premiseCount internalCount)
      (Indexed.argumentWire (inputFields payload roots base))
      (some (GraphAddressSequence.resultWire (offsets internalCount) base))
      (selectedClock internalCount payload roots base) := by
  have selected := Indexed.outputs (basePlan arity premiseCount) (inputFields payload roots base)
  rw [basePlan_exact] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine (basePlan arity premiseCount))
    (GraphAddressSequence.machine (offsets internalCount)) (Equiv.refl Alphabet)
    (Indexed.argumentWire (inputFields payload roots base)) (GraphAddressAddition.natWord base)
    (GraphAddressSequence.resultWire (offsets internalCount) base) _ _ selected (by
      change TM2OutputsInTime (GraphAddressSequence.machine (offsets internalCount))
        ((GraphAddressAddition.natWord base).map id) _ _
      simpa only [List.map_id] using GraphAddressSequence.outputs (offsets internalCount) base)
  exact joined

abbrev TaggedCell := Sum (Option Alphabet) (Option Alphabet)
def untag : TaggedCell → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr symbol => [symbol]

def retainedMachine (arity premiseCount internalCount : Nat) :=
  RetainedWordExecution.WithOutput.machine (selectedAddressMachine arity premiseCount internalCount)
local instance (arity premiseCount internalCount : Nat) : Fintype ((retainedMachine arity premiseCount internalCount).Γ
    (retainedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype TaggedCell)
local instance (arity premiseCount internalCount : Nat) : Inhabited ((retainedMachine arity premiseCount internalCount).Γ
    (retainedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited TaggedCell)

def preparedMachine (arity premiseCount internalCount : Nat) := StackMachineComposition.machine
  (retainedMachine arity premiseCount internalCount) (WordHomomorphismMachine.machine untag) (Equiv.refl TaggedCell)
local instance (arity premiseCount internalCount : Nat) : Fintype ((preparedMachine arity premiseCount internalCount).Γ
    (preparedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity premiseCount internalCount : Nat) : Inhabited ((preparedMachine arity premiseCount internalCount).Γ
    (preparedMachine arity premiseCount internalCount).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

theorem untag_exact (input output : List (Option Alphabet)) :
    (input.map Sum.inl ++ output.map Sum.inr).flatMap untag = input++output := by
  simp only [List.flatMap_append,List.flatMap_map]
  have left : input.flatMap (fun symbol => untag (.inl symbol)) = input := by induction input <;> simp_all [untag]
  have right : output.flatMap (fun symbol => untag (.inr symbol)) = output := by induction output <;> simp_all [untag]
  rw [left,right]

def preparedClock {arity premiseCount : Nat} (internalCount : Nat) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :=
  selectedClock internalCount payload roots base + 9*(Indexed.argumentWire (inputFields payload roots base)).length +
    8*(GraphAddressSequence.resultWire (offsets internalCount) base).length+9

noncomputable def preparedOutputs {arity premiseCount : Nat} (internalCount : Nat)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat) :
    TM2OutputsInTime (preparedMachine arity premiseCount internalCount)
      (Indexed.argumentWire (inputFields payload roots base))
      (some (Indexed.argumentWire (expandedFields internalCount payload roots base)))
      (preparedClock internalCount payload roots base) := by
  have retained := RetainedWordExecution.WithOutput.outputs (selectedAddressMachine arity premiseCount internalCount)
    (Indexed.argumentWire (inputFields payload roots base)) (GraphAddressSequence.resultWire (offsets internalCount) base)
    _ (selectedOutputs internalCount payload roots base)
  have mapped := WordHomomorphismMachine.outputs untag
    ((Indexed.argumentWire (inputFields payload roots base)).map (Sum.inl : Option Alphabet → TaggedCell) ++
      (GraphAddressSequence.resultWire (offsets internalCount) base).map (Sum.inr : Option Alphabet → TaggedCell))
  rw [untag_exact,← expanded_wire] at mapped
  have joined := StackMachineComposition.outputs (retainedMachine arity premiseCount internalCount)
    (WordHomomorphismMachine.machine untag) (Equiv.refl TaggedCell)
    (Indexed.argumentWire (inputFields payload roots base))
    ((Indexed.argumentWire (inputFields payload roots base)).map (Sum.inl : Option Alphabet → TaggedCell) ++
      (GraphAddressSequence.resultWire (offsets internalCount) base).map (Sum.inr : Option Alphabet → TaggedCell))
    (Indexed.argumentWire (expandedFields internalCount payload roots base)) _ _ retained (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine untag)
        (((Indexed.argumentWire (inputFields payload roots base)).map (Sum.inl : Option Alphabet → TaggedCell) ++
          (GraphAddressSequence.resultWire (offsets internalCount) base).map (Sum.inr : Option Alphabet → TaggedCell)).map id) _ _
      simpa only [List.map_id] using mapped)
  convert joined using 1
  · rfl
  · simp only [preparedClock,List.length_append,List.length_map,expanded_wire]
    omega


def machine {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) := StackMachineComposition.machine
  (preparedMachine arity premiseCount internalCount) (Indexed.machine (template premiseCount internalCount block safe))
  (Equiv.refl (Option Alphabet))

def clock {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :=
  preparedClock internalCount payload roots base + 2*(Indexed.argumentWire (expandedFields internalCount payload roots base)).length+2 +
  4*((template premiseCount internalCount block safe).length+1)*((Indexed.argumentWire (expandedFields internalCount payload roots base)).length+1)

noncomputable def emittedOutputs {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    TM2OutputsInTime (machine premiseCount internalCount block safe)
      (Indexed.argumentWire (inputFields payload roots base))
      (some (Indexed.instantiate (template premiseCount internalCount block safe) (expandedFields internalCount payload roots base)))
      (clock internalCount block safe payload roots base) := by
  exact StackMachineComposition.outputs (preparedMachine arity premiseCount internalCount)
    (Indexed.machine (template premiseCount internalCount block safe)) (Equiv.refl (Option Alphabet))
    (Indexed.argumentWire (inputFields payload roots base)) (Indexed.argumentWire (expandedFields internalCount payload roots base))
    (Indexed.instantiate (template premiseCount internalCount block safe) (expandedFields internalCount payload roots base))
    _ _ (preparedOutputs internalCount payload roots base) (by
      change TM2OutputsInTime (Indexed.machine (template premiseCount internalCount block safe))
        ((Indexed.argumentWire (expandedFields internalCount payload roots base)).map id) _ _
      simpa only [List.map_id] using Indexed.outputs (template premiseCount internalCount block safe)
        (expandedFields internalCount payload roots base))

theorem base_length_le {arity premiseCount : Nat} (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    (GraphAddressAddition.natWord base).length ≤ (Indexed.argumentWire (inputFields payload roots base)).length := by
  have field := basePlan_exact payload roots base
  simp only [basePlan,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil] at field
  have selected := Indexed.select_length (⟨arity+premiseCount,by omega⟩ : Fin (arity+premiseCount+1))
    ⟨0,by omega⟩ (Indexed.argumentWire (inputFields payload roots base))
  rw [Indexed.select_argument,field] at selected
  exact selected

theorem result_length_le (addressOffsets : List Nat) (base : Nat) :
    (GraphAddressSequence.resultWire addressOffsets base).length ≤ (GraphAddressSequence.preparedWire addressOffsets base).length := by
  induction addressOffsets with
  | nil => rfl
  | cons offset rest ih =>
    have length := GraphAddressSequence.sum_word_length base offset
    simp only [GraphAddressSequence.resultWire,GraphAddressSequence.preparedWire,List.map_cons,Indexed.frame,
      List.flatMap_cons,List.length_append,List.length_map,List.length_cons,List.length_nil] at ih ⊢
    omega

def coefficient {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) :=
  128*((GraphAddressSequence.plan (offsets internalCount)).length+1)*((template premiseCount internalCount block safe).length+1)

theorem clock_linear {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    clock internalCount block safe payload roots base ≤
      coefficient premiseCount internalCount block safe*((Indexed.argumentWire (inputFields payload roots base)).length+1) := by
  let inputLength := (Indexed.argumentWire (inputFields payload roots base)).length
  let descriptor := (GraphAddressSequence.plan (offsets internalCount)).length
  let addressLength := (GraphAddressSequence.resultWire (offsets internalCount) base).length
  let emissionLength := (template premiseCount internalCount block safe).length
  have baseBound := base_length_le payload roots base
  have addressBound := (result_length_le (offsets internalCount) base).trans (GraphAddressSequence.prepared_length (offsets internalCount) base)
  have size : addressLength ≤ descriptor*(inputLength+1) := by
    dsimp only [addressLength,descriptor,inputLength]
    exact addressBound.trans (Nat.mul_le_mul_left _ (by omega))
  have sequenceBound := GraphAddressSequence.clock_linear (offsets internalCount) base
  have sequence : GraphAddressSequence.clock (offsets internalCount) base ≤ 80*(descriptor+1)*(inputLength+1) := by
    exact sequenceBound.trans (Nat.mul_le_mul_left _ (by dsimp only [inputLength]; omega))
  have expanded : inputLength+addressLength+1 ≤ (descriptor+1)*(inputLength+1) := by nlinarith only [size]
  have copied := Nat.mul_le_mul_left (4*(emissionLength+1)) expanded
  have prep : preparedClock internalCount payload roots base ≤ (99+88*descriptor)*(inputLength+1) := by
    dsimp only [preparedClock,selectedClock]
    change 8*(inputLength+1)+2*(GraphAddressAddition.natWord base).length+2+
      GraphAddressSequence.clock (offsets internalCount) base+9*inputLength+8*addressLength+9 ≤ _
    nlinarith only [baseBound,sequence,size]
  unfold clock coefficient
  rw [expanded_wire]
  simp only [List.length_append]
  change preparedClock internalCount payload roots base+2*(inputLength+addressLength)+2+
    4*(emissionLength+1)*(inputLength+addressLength+1) ≤ 128*(descriptor+1)*(emissionLength+1)*(inputLength+1)
  nlinarith only [prep,expanded,copied,Nat.zero_le emissionLength,Nat.zero_le descriptor,Nat.zero_le inputLength]

noncomputable def linearOutputs {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (payload : Fin arity → List Alphabet)
    (roots : Fin premiseCount → Nat) (base : Nat) :
    TM2OutputsInTime (machine premiseCount internalCount block safe)
      (Indexed.argumentWire (inputFields payload roots base))
      (some (Indexed.instantiate (template premiseCount internalCount block safe) (expandedFields internalCount payload roots base)))
      (coefficient premiseCount internalCount block safe*((Indexed.argumentWire (inputFields payload roots base)).length+1)) :=
  WordEqualityMachine.within (emittedOutputs internalCount block safe payload roots base)
    (clock_linear internalCount block safe payload roots base)

noncomputable def realization {arity : Nat} (premiseCount internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) :
    TM2ComputableInPolyTime
      (fun input : (Fin arity → List Alphabet) × (Fin premiseCount → Nat) × Nat => Indexed.argumentWire (inputFields input.1 input.2.1 input.2.2))
      id (fun input => Indexed.instantiate (template premiseCount internalCount block safe)
        (expandedFields internalCount input.1 input.2.1 input.2.2)) where
  tm := machine premiseCount internalCount block safe
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := Polynomial.C (coefficient premiseCount internalCount block safe)*(Polynomial.X+Polynomial.C 1)
  outputsFun input := by
    change TM2OutputsInTime (machine premiseCount internalCount block safe)
      ((Indexed.argumentWire (inputFields input.1 input.2.1 input.2.2)).map id)
      (some ((Indexed.instantiate (template premiseCount internalCount block safe)
        (expandedFields internalCount input.1 input.2.1 input.2.2)).map id)) _
    simp only [List.map_id,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X]
    exact linearOutputs internalCount block safe input.1 input.2.1 input.2.2


theorem safeBlock_of_checked {arity premiseCount : Nat} {policy : AxiomPolicy} [DecidablePred policy]
    (block : Block arity) (receipts : List Receipt) (payload : Fin arity → List Alphabet)
    (premises : List Theorem) (conclusion : Theorem) (premiseLength : premises.length = premiseCount)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
      Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
      Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
      node.parents = receipt.parents) block.1 receipts)
    (checked : GraphExpansion.BlockChecked policy premises conclusion (receipts,block.2)) :
    SafeBlock premiseCount block.1.length block := by
  obtain ⟨result,replayed,found⟩ := checked
  have length := replayFrom_size (ruleWitness policy) replayed
  have rootBound := (Array.getElem?_eq_some_iff.mp found).1
  have parentBound := replayFrom_parents_lt_result (ruleWitness policy) replayed
  have sameLength := aligned.length_eq
  have count : result.size = premiseCount+block.1.length := by
    simpa only [List.size_toArray,premiseLength,← sameLength] using length
  rw [count] at rootBound parentBound
  refine ⟨rootBound,?_⟩
  have pull (sourceNodes : List (Node (Plan arity) (Plan arity) (Plan arity))) (resultNodes : List Receipt)
      (correspond : List.Forall₂ (fun node receipt =>
        Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
        Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
        Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
        node.parents = receipt.parents) sourceNodes resultNodes)
      (bounded : ∀ node ∈ resultNodes, ∀ index ∈ node.parents, index < premiseCount+block.1.length) :
      ∀ node ∈ sourceNodes, ∀ index ∈ node.parents, index < premiseCount+block.1.length := by
    revert bounded
    induction correspond with
    | nil => simp
    | @cons node receipt nodes receipts first rest ih =>
      intro bounded memberNode member index parent
      rcases List.mem_cons.mp member with same | remaining
      · subst memberNode
        rw [first.2.2.2] at parent
        exact bounded receipt (by simp) index parent
      · exact ih (fun receipt member => bounded receipt (by simp [member])) memberNode remaining index parent
  exact pull block.1 receipts aligned parentBound

noncomputable def outputs {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (receipts : List Receipt)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
      Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
      Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
      node.parents = receipt.parents) block.1 receipts) :
    TM2OutputsInTime (machine premiseCount internalCount block safe)
      (Indexed.argumentWire (inputFields payload roots base))
      (some (encodeCertificate (GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2))))
      (clock internalCount block safe payload roots base) := by
  rw [← template_exact internalCount block safe receipts payload roots base aligned]
  exact emittedOutputs internalCount block safe payload roots base

theorem run_decodes {arity premiseCount : Nat} (internalCount : Nat) (block : Block arity)
    (safe : SafeBlock premiseCount internalCount block) (receipts : List Receipt)
    (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat) (base : Nat)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
      Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
      Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
      node.parents = receipt.parents) block.1 receipts) {word : List Alphabet}
    (finished : TM2Outputs (machine premiseCount internalCount block safe)
      (Indexed.argumentWire (inputFields payload roots base)) (some word)) :
    decodeCertificate word = some (GraphExpansion.expandBlock (List.ofFn roots) base (receipts,block.2)) := by
  have same := StackMachineComposition.outputs_unique finished (outputs internalCount block safe receipts payload roots base aligned).toEvalsTo
  rw [same,decodeCertificate_encodeCertificate]

theorem run_accepted {arity premiseCount : Nat} {policy : AxiomPolicy} [DecidablePred policy]
    (internalCount : Nat) (block : Block arity) (safe : SafeBlock premiseCount internalCount block)
    (receipts : List Receipt) (payload : Fin arity → List Alphabet) (roots : Fin premiseCount → Nat)
    (earlierNodes : List Receipt) (cache : Array Theorem) (premises : List Theorem) (conclusion : Theorem)
    (aligned : List.Forall₂ (fun node receipt =>
      Indexed.instantiate node.conclusion payload = encodeWith theoremCodec receipt.conclusion ∧
      Indexed.instantiate node.witness payload = encodeWith requestCodec receipt.witness ∧
      Indexed.instantiate node.origin payload = encodeWith originCodec receipt.origin ∧
      node.parents = receipt.parents) block.1 receipts)
    (prefixChecked : replay (ruleWitness policy) earlierNodes = some cache)
    (selected : lookupPremises cache (List.ofFn roots) = some premises)
    (checked : GraphExpansion.BlockChecked policy premises conclusion (receipts,block.2))
    {word : List Alphabet} (finished : TM2Outputs (machine premiseCount internalCount block safe)
      (Indexed.argumentWire (inputFields payload roots cache.size)) (some word)) :
    ∃ decoded, decodeCertificate word = some decoded ∧
      (ProofSystem.checker policy).check conclusion (earlierNodes++decoded.1,decoded.2) = true := by
  refine ⟨GraphExpansion.expandBlock (List.ofFn roots) cache.size (receipts,block.2),
    run_decodes internalCount block safe receipts payload roots cache.size aligned finished,?_⟩
  exact GraphExpansion.appendBlock_accepted prefixChecked selected checked

namespace Controls

theorem external_repeated_parents :
    Indexed.instantiate (parentPlan (arity:=0) 2 1 [1,0,1] (by intro i h; simp at h; omega))
      (expandedFields 1 (fun i : Fin 0 => nomatch i) (![37,11] : Fin 2 → Nat) 100) =
      encodeWith (Codec.list Codec.nat) [11,37,11] := by
  rw [parentPlan_exact]
  rfl

theorem internal_and_external_parents :
    Indexed.instantiate (parentPlan (arity:=0) 2 3 [2,0,4,2] (by intro i h; simp at h; omega))
      (expandedFields 3 (fun i : Fin 0 => nomatch i) (![37,11] : Fin 2 → Nat) 100) =
      encodeWith (Codec.list Codec.nat) [100,37,102,100] := by
  rw [parentPlan_exact]
  rfl

theorem wrong_root_not_selected :
    Indexed.instantiate (addressPlan (arity:=0) 2 1 0)
      (expandedFields 1 (fun i : Fin 0 => nomatch i) (![37,11] : Fin 2 → Nat) 100) ≠
      GraphAddressAddition.natWord 11 := by
  rw [addressPlan_exact]
  decide +kernel

theorem future_parent_not_compilable :
    ¬SafeBlock 2 1 (([⟨[],[],[3],[]⟩],2) : Block 0) := by
  intro admitted
  have future := admitted.2 ⟨[],[],[3],[]⟩ (by simp) 3 (by simp)
  omega

end Controls
end Mettapedia.Languages.HOLLight.GraphRelocationEmission

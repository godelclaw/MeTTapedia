import Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel
import Mettapedia.Logic.HOL.MappedFamilyPredicate

/-!
# Exact reading of the generated Vector-container guards

The actual typed guard programs are compared with the mapped source guards.
The comparison uses the registered code's shapes and slot decoder, rather than
assigning ideal guard meanings to fresh primitive symbols.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPositiveContainer IndexedPolynomial.RecursiveSpaceRepresentation
open IndexedConstructorGuards FiniteConstructorEncoding

theorem shape_readback (shape : presentation.polynomial.Shape VectorControl.environment ()) :
    VectorControl.shapeAt shape.1 = shape := by
  exact eq_of_heq (Sigma.mk.inj (point_readback ⟨(), shape⟩)).2


namespace CarrierReading
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
  {model : HenkinModel.{u,v,w} Base Const} (reading : CarrierReading model)

theorem denotes_eq {type : Ty Base} (term : ClosedTerm Const type) :
    RecursiveSpacePredicate.Signature.denotes model term = model.denote term reading.values :=
  (RecursiveSpacePredicate.Signature.denote_closed model term reading.values).symm

theorem payload_agrees_iff (payload : reading.Payload) (length : Nat) :
    payloadEquivalence model reading.constructors.fields payload =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) reading.constructors.fields
        (reading.data length) ↔ payload = reading.packed length := by
  constructor
  · intro agrees
    apply (payloadEquivalence model reading.constructors.fields).injective
    exact agrees.trans ((payloadEquivalence model reading.constructors.fields).apply_symm_apply _).symm
  · rintro rfl
    exact (payloadEquivalence model reading.constructors.fields).apply_symm_apply _

theorem native_shape_iff (full : model.FullDomains) (tag : Nat) (payload : reading.Payload) :
    (model.denote reading.constructors.shapeProgram reading.values (reading.numbers tag) payload).down ↔
      tag = 0 ∧ ∃ length, payload = reading.packed length := by
  rw [reading.constructors.shapeProgram_denote model full]
  constructor
  · rintro ⟨other, ⟨_, tagSame⟩, agrees⟩
    obtain ⟨length, rfl⟩ := reading.data_unique other
    have zero : model.denote (reading.numeral 0) reading.values = reading.numbers 0 :=
      (reading.denotes_eq _).symm.trans reading.zero
    exact ⟨reading.numbers.injective (tagSame.trans zero), length,
      (reading.payload_agrees_iff payload length).mp agrees⟩
  · rintro ⟨rfl, length, rfl⟩
    refine ⟨reading.data length, ⟨reading.allowed length, ?_⟩,
      (reading.payload_agrees_iff _ _).mpr rfl⟩
    exact reading.zero.symm.trans (reading.denotes_eq _)

theorem mapped_shape_iff (tag : Nat) (payload : reading.Payload) :
    Mapped.ShapeGuard presentation VectorControl.environment reading.payloadMap tag payload ↔
      tag = 0 ∧ ∃ length, payload = reading.packed length := by
  constructor
  · rintro ⟨point, tagSame, agrees⟩
    exact ⟨tagSame, pointLength point, agrees⟩
  · rintro ⟨same, length, agrees⟩
    exact ⟨point length, same, agrees⟩

theorem native_active_iff (full : model.FullDomains) (payload : reading.Payload) (slot : Nat) :
    (model.denote reading.positions.activeProgram reading.values payload (reading.numbers slot)).down ↔
      ∃ length, payload = reading.packed length ∧ slot < length := by
  rw [reading.positions.activeProgram_denote model full]
  constructor
  · rintro ⟨other, ⟨_, index, relation⟩, agrees⟩
    obtain ⟨length, rfl⟩ := reading.data_unique other
    exact ⟨length, (reading.payload_agrees_iff payload length).mp agrees,
      ((reading.relation_iff full length slot index).mp relation).1⟩
  · rintro ⟨length, agrees, inside⟩
    exact ⟨reading.data length,
      ⟨reading.allowed length, ULift.up True, (reading.relation_iff full length slot _).mpr ⟨inside, rfl⟩⟩,
      (reading.payload_agrees_iff payload length).mpr agrees⟩

theorem mapped_active_iff (payload : reading.Payload) (slot : Nat) :
    Mapped.ActiveGuard presentation VectorControl.environment reading.payloadMap payload slot ↔
      ∃ length, payload = reading.packed length ∧ slot < length := by
  constructor
  · rintro ⟨point, position, agrees, decoded⟩
    obtain ⟨length, same⟩ : ∃ length, point = IndexedVectorContainerFamilyModel.point length :=
      ⟨pointLength point, (point_readback point).symm⟩
    cases same
    exact ⟨length, agrees,
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mp ⟨position, decoded⟩⟩
  · rintro ⟨length, agrees, inside⟩
    obtain ⟨position, decoded⟩ :=
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mpr inside
    exact ⟨point length, position, agrees, decoded⟩

theorem native_root_iff (tree : reading.Tree) (index : Ty.denote model.Carrier Ty.prop) :
    reading.constructors.rootMeaning reading.construct model reading.values (reading.trees tree) index ↔
      index = ULift.up True ∧
        Mapped.HasRootIndex presentation VectorControl.environment reading.payloadMap tree () := by
  constructor
  · rintro ⟨other, _, result, children, same⟩
    obtain ⟨length, rfl⟩ := reading.data_unique other
    rw [reading.result_index] at result
    let decoded := fun slot => reading.trees.symm (children (reading.numbers slot))
    refine ⟨result.symm, VectorControl.shapeAt length, decoded, ?_⟩
    apply reading.trees.injective
    have constructor := reading.construct_eq 0 (reading.packed length) decoded
    simp only [decoded, Equiv.apply_symm_apply] at constructor
    change reading.trees tree = model.denote reading.construct reading.values
      (model.denote (reading.numeral 0) reading.values) (reading.packed length) children at same
    rw [← reading.denotes_eq (reading.numeral 0), reading.zero, ← reading.denotes_eq reading.construct] at same
    exact same.trans constructor.symm
  · rintro ⟨rfl, shape, children, same⟩
    have shapeEq := shape_readback shape
    let length := shape.1
    have shapeEq' : VectorControl.shapeAt length = shape := shapeEq
    rw [← shapeEq'] at same
    refine ⟨reading.data length, reading.allowed length, reading.result_index length,
      (fun slot => reading.trees (children (reading.numbers.symm slot))), ?_⟩
    change reading.trees tree = model.denote reading.construct reading.values
      (model.denote (reading.numeral 0) reading.values) (reading.packed length) _
    rw [← reading.denotes_eq (reading.numeral 0), reading.zero, ← reading.denotes_eq reading.construct]
    exact (congrArg reading.trees same).trans (reading.construct_eq 0 (reading.packed length) children)

theorem native_edge_iff (full : model.FullDomains) (payload : reading.Payload) (slot : Nat) (child : reading.Tree) :
    (model.denote (reading.positions.edgeProgram reading.construct) reading.values payload
      (reading.numbers slot) (reading.trees child)).down ↔
      ∃ length, payload = reading.packed length ∧ slot < length ∧
        Mapped.HasRootIndex presentation VectorControl.environment reading.payloadMap child () := by
  rw [reading.positions.edgeProgram_denote reading.construct model full]
  constructor
  · rintro ⟨other, _, agrees, index, relation, root⟩
    obtain ⟨length, rfl⟩ := reading.data_unique other
    exact ⟨length, (reading.payload_agrees_iff payload length).mp agrees,
      ((reading.relation_iff full length slot index).mp relation).1,
      ((reading.native_root_iff child index).mp root).2⟩
  · rintro ⟨length, agrees, inside, root⟩
    exact ⟨reading.data length, reading.allowed length, (reading.payload_agrees_iff payload length).mpr agrees,
      ULift.up True, (reading.relation_iff full length slot _).mpr ⟨inside, rfl⟩,
      (reading.native_root_iff child _).mpr ⟨rfl, root⟩⟩

theorem mapped_edge_iff (payload : reading.Payload) (slot : Nat) (child : reading.Tree) :
    Mapped.EdgeGuard presentation VectorControl.environment reading.payloadMap payload slot child ↔
      ∃ length, payload = reading.packed length ∧ slot < length ∧
        Mapped.HasRootIndex presentation VectorControl.environment reading.payloadMap child () := by
  constructor
  · rintro ⟨point, position, agrees, decoded, root⟩
    obtain ⟨length, same⟩ : ∃ length, point = IndexedVectorContainerFamilyModel.point length :=
      ⟨pointLength point, (point_readback point).symm⟩
    cases same
    refine ⟨length, agrees,
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mp ⟨position, decoded⟩, ?_⟩
    convert root
  · rintro ⟨length, agrees, inside, root⟩
    obtain ⟨position, decoded⟩ :=
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mpr inside
    refine ⟨point length, position, agrees, decoded, ?_⟩
    convert root
    exact @Subsingleton.elim Unit inferInstance _ _

def familyReading (full : model.FullDomains) :
    MappedFamilyPredicate.Reading presentation VectorControl.environment reading.signature model reading.payloadMap where
  numbers := reading.numbers
  trees := reading.trees
  bottom := reading.bottom_eq
  construct := reading.construct_eq
  shape_iff := by
    intro tag payload
    rw [reading.denotes_eq]
    exact (reading.native_shape_iff full tag payload).trans (reading.mapped_shape_iff tag payload).symm
  active_iff := by
    intro payload slot
    rw [reading.denotes_eq]
    exact (reading.native_active_iff full payload slot).trans (reading.mapped_active_iff payload slot).symm
  edge_iff := by
    intro payload slot child
    rw [reading.denotes_eq]
    exact (reading.native_edge_iff full payload slot child).trans (reading.mapped_edge_iff payload slot child).symm

theorem member_iff (full : model.FullDomains) (tree : reading.Tree) :
    (RecursiveSpacePredicate.Signature.denotes model
      (reading.positions.member reading.bottom reading.construct) (reading.trees tree)).down ↔
      Mapped.FamilyValid presentation VectorControl.environment reading.payloadMap tree :=
  MappedFamilyPredicate.Reading.member_iff presentation VectorControl.environment
    reading.signature model reading.payloadMap (reading.familyReading full) full reading.payloadMap_injective tree

#print axioms familyReading
#print axioms member_iff
end CarrierReading

private theorem reference_values : (fun {type} => referenceCarrier.values (τ := type)) =
    (fun {type} => values (τ := type)) := by
  funext type index
  exact nomatch index

private theorem reference_constructors : referenceCarrier.constructors = constructors := rfl
private theorem reference_positions : referenceCarrier.positions = positions := rfl
private theorem reference_number (n : Nat) : referenceCarrier.numbers n = ULift.up n := rfl
private theorem reference_tree (tree : Tree) : referenceCarrier.trees tree = tree := rfl
private theorem reference_packed (n : Nat) : referenceCarrier.packed n = packed n := rfl
private theorem reference_payload : referenceCarrier.payloadMap = payloadMap := rfl
private theorem reference_construct : referenceCarrier.construct = construct := rfl

theorem denotes_eq {type : Ty SortCode} (term : ClosedTerm Symbol type) :
    RecursiveSpacePredicate.Signature.denotes model term = model.denote term values := by
  simpa only [reference_values] using referenceCarrier.denotes_eq term

theorem payload_agrees_iff (payload : PayloadValue) (length : Nat) :
    payloadEquivalence model constructors.fields payload =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) constructors.fields (data length) ↔
      payload = packed length :=
  referenceCarrier.payload_agrees_iff payload length

theorem native_shape_iff (tag : Nat) (payload : PayloadValue) :
    (model.denote constructors.shapeProgram values (ULift.up tag) payload).down ↔
      tag = 0 ∧ ∃ length, payload = packed length := by
  simpa only [reference_values, reference_constructors, reference_number, reference_packed] using referenceCarrier.native_shape_iff full tag payload

theorem mapped_shape_iff (tag : Nat) (payload : PayloadValue) :
    Mapped.ShapeGuard presentation VectorControl.environment payloadMap tag payload ↔
      tag = 0 ∧ ∃ length, payload = packed length :=
  referenceCarrier.mapped_shape_iff tag payload

theorem native_active_iff (payload : PayloadValue) (slot : Nat) :
    (model.denote positions.activeProgram values payload (ULift.up slot)).down ↔
      ∃ length, payload = packed length ∧ slot < length := by
  simpa only [reference_values, reference_positions, reference_number, reference_packed] using referenceCarrier.native_active_iff full payload slot

theorem mapped_active_iff (payload : PayloadValue) (slot : Nat) :
    Mapped.ActiveGuard presentation VectorControl.environment payloadMap payload slot ↔
      ∃ length, payload = packed length ∧ slot < length :=
  referenceCarrier.mapped_active_iff payload slot

theorem native_root_iff (tree : Tree) (index : Ty.denote.{0,0} model.Carrier Ty.prop) :
    constructors.rootMeaning construct model values tree index ↔
      index = ULift.up True ∧ Mapped.HasRootIndex presentation VectorControl.environment payloadMap tree () := by
  simpa only [reference_values, reference_constructors, reference_construct, reference_tree, reference_payload] using referenceCarrier.native_root_iff tree index

theorem native_edge_iff (payload : PayloadValue) (slot : Nat) (child : Tree) :
    (model.denote (positions.edgeProgram construct) values payload (ULift.up slot) child).down ↔
      ∃ length, payload = packed length ∧ slot < length ∧
        Mapped.HasRootIndex presentation VectorControl.environment payloadMap child () := by
  simpa only [reference_values, reference_positions, reference_construct, reference_number, reference_tree, reference_packed, reference_payload] using referenceCarrier.native_edge_iff full payload slot child

theorem mapped_edge_iff (payload : PayloadValue) (slot : Nat) (child : Tree) :
    Mapped.EdgeGuard presentation VectorControl.environment payloadMap payload slot child ↔
      ∃ length, payload = packed length ∧ slot < length ∧
        Mapped.HasRootIndex presentation VectorControl.environment payloadMap child () :=
  referenceCarrier.mapped_edge_iff payload slot child

def reading : MappedFamilyPredicate.Reading presentation VectorControl.environment signature model payloadMap :=
  referenceCarrier.familyReading full

#print axioms native_root_iff
#print axioms native_edge_iff
#print axioms reading
end Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel

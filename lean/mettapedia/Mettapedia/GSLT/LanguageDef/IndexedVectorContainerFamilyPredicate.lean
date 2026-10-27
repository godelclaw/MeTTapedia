import Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyReading

/-!
# Whole-family membership for the generated Vector-container predicate

The generated HOL least predicate recognizes exactly the encoded original
registered family. The semantic representation has both inverse laws. Concrete
controls separate a valid zero-child node from missing required children,
hidden inactive-slot data and a payload outside the constructor image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPositiveContainer IndexedPolynomial IndexedPolynomial.RecursiveSpaceRepresentation

def member (tree : Tree) : Prop := (model.denote (positions.member bottom construct) values tree).down

theorem member_iff (tree : Tree) :
    member tree ↔ Mapped.FamilyValid presentation VectorControl.environment payloadMap tree := by
  have complete := referenceCarrier.member_iff full tree
  change (RecursiveSpacePredicate.Signature.denotes model
    (positions.member bottom construct) tree).down ↔
      Mapped.FamilyValid presentation VectorControl.environment payloadMap tree at complete
  simpa only [denotes_eq, member] using complete

abbrev Source := Fix presentation.polynomial VectorControl.environment ()

noncomputable def encode (source : Source) : Tree :=
  RecursiveSpace.mapPayload payloadMap
    (recursiveSpaceRepresentation presentation VectorControl.environment () source).val

theorem encode_member (source : Source) : member (encode source) := by
  apply (member_iff _).mpr
  exact ⟨(), _, (recursiveSpaceRepresentation presentation VectorControl.environment () source).property, rfl⟩

theorem encode_injective : Function.Injective encode := by
  intro first second same
  apply (recursiveSpaceRepresentation presentation VectorControl.environment ()).injective
  apply Subtype.ext
  exact RecursiveSpace.mapPayload_injective payloadMap payloadMap_injective same

noncomputable def representation : Source ≃ {tree : Tree // member tree} :=
  Equiv.ofBijective (fun source => ⟨encode source, encode_member source⟩)
    ⟨fun first second same => encode_injective (congrArg Subtype.val same), by
      intro target
      obtain ⟨index, original, valid, same⟩ := (member_iff target.val).mp target.property
      cases index
      let source := (recursiveSpaceRepresentation presentation VectorControl.environment ()).symm ⟨original, valid⟩
      refine ⟨source, Subtype.ext ?_⟩
      have restored := congrArg Subtype.val
        ((recursiveSpaceRepresentation presentation VectorControl.environment ()).apply_symm_apply ⟨original, valid⟩)
      exact (congrArg (RecursiveSpace.mapPayload payloadMap) restored).trans same⟩

theorem representation_left (source : Source) : representation.symm (representation source) = source :=
  representation.symm_apply_apply source
theorem representation_right (target : {tree : Tree // member tree}) : representation (representation.symm target) = target :=
  representation.apply_symm_apply target

def leaf : Tree := RecursiveSpace.construct 0 (packed 0) (fun _ => RecursiveSpace.bottom)
def missingChildren : Tree := RecursiveSpace.construct 0 (packed 2) (fun _ => RecursiveSpace.bottom)
def hiddenPadding : Tree := RecursiveSpace.construct 0 (packed 0)
  (fun slot => if slot = 0 then leaf else RecursiveSpace.bottom)
def foreignPayload : Tree := RecursiveSpace.construct 0 unused (fun _ => RecursiveSpace.bottom)

theorem zero_slots_absent (slot : Nat) :
    (presentation.coding (VectorControl.shapeAt 0)).decode slot = none := by
  apply (IndexedPositiveContainer.RecursiveSpaceRepresentation.code_padding_iff
    VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt 0) slot).mpr
  rw [IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_ordered_length]
  exact Nat.zero_le slot

theorem leaf_valid : Mapped.Valid presentation VectorControl.environment payloadMap () leaf := by
  apply (Mapped.valid_iff_constructorStep presentation VectorControl.environment payloadMap () leaf).mpr
  let children : presentation.polynomial.Position (VectorControl.shapeAt 0) → Tree :=
    fun position => Fin.elim0 (VectorControl.positionEquiv 0 position)
  refine ⟨VectorControl.shapeAt 0, children, ?_, ?_⟩
  · change RecursiveSpace.construct 0 (packed 0) (fun _ => RecursiveSpace.bottom) =
      RecursiveSpace.construct 0 (packed 0) ((presentation.coding (VectorControl.shapeAt 0)).extend RecursiveSpace.bottom children)
    apply congrArg (RecursiveSpace.construct 0 (packed 0))
    funext slot
    simp only [SlotEncoding.extend, zero_slots_absent]
  · intro position
    exact Fin.elim0 (VectorControl.positionEquiv 0 position)

theorem leaf_member : member leaf := (member_iff leaf).mpr ⟨(), leaf_valid⟩

theorem bottom_refused : ¬ member RecursiveSpace.bottom := by
  intro valid
  obtain ⟨index, valid⟩ := (member_iff _).mp valid
  exact Mapped.valid_bottom_refused presentation VectorControl.environment payloadMap index valid

theorem missing_children_refused : ¬ member missingChildren := by
  intro valid
  obtain ⟨index, valid⟩ := (member_iff _).mp valid
  have children := ((Mapped.valid_construct_iff presentation VectorControl.environment payloadMap
    payloadMap_injective index (point 2) (fun _ => RecursiveSpace.bottom)).mp valid).2.2
  let position := (VectorControl.positionEquiv 2).symm ⟨0, by decide⟩
  exact Mapped.valid_bottom_refused presentation VectorControl.environment payloadMap _ (children position)

theorem hidden_padding_refused : ¬ member hiddenPadding := by
  intro valid
  obtain ⟨index, valid⟩ := (member_iff _).mp valid
  have padding := ((Mapped.valid_construct_iff presentation VectorControl.environment payloadMap
    payloadMap_injective index (point 0)
      (fun slot => if slot = 0 then leaf else RecursiveSpace.bottom)).mp valid).2.1
  have same : leaf = RecursiveSpace.bottom := padding 0 (zero_slots_absent 0)
  exact RecursiveSpace.construct_ne_bottom _ _ _ same

theorem hidden_padding_root_accepted :
    (model.denote (constructors.rootProgram construct) values hiddenPadding (ULift.up True)).down := by
  apply (constructors.rootProgram_denote construct model full values _ _).mpr
  apply (native_root_iff _ _).mpr
  exact ⟨rfl, VectorControl.shapeAt 0, _, rfl⟩

theorem foreign_payload_refused : ¬ member foreignPayload := by
  intro valid
  obtain ⟨index, valid⟩ := (member_iff _).mp valid
  obtain ⟨shape, children, same, _⟩ :=
    (Mapped.valid_iff_constructorStep presentation VectorControl.environment payloadMap index _).mp valid
  have payloads := ((RecursiveSpace.construct_injective _ _ _ _ _ _).mp same).2.1
  exact packed_ne_unused _ payloads.symm

#print axioms member_iff
#print axioms representation
#print axioms encode_injective
#print axioms leaf_member
#print axioms missing_children_refused
#print axioms hidden_padding_refused
#print axioms foreign_payload_refused
end Mettapedia.GSLT.LanguageDef.IndexedVectorContainerFamilyModel

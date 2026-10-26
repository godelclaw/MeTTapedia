import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpaceRepresentation
import Mettapedia.TypeTheory.IndexedPositiveContainerInduction

/-!
# Ordered registered containers in recursive spaces

The existing ordered-position equivalence supplies natural slots for every
indexed registered code. Complete admitted registered blocks retain their
constructor ordinals and transport their whole fixed family through the shared
recursive-space representation. Ordered finitarity is explicit; positivity alone
supplies no slot encoder or finite traversal. These semantic adapters add no
object-language formation or native proof authority.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPositiveContainer.RecursiveSpaceRepresentation
open IndexedPolynomial
open IndexedPolynomial.Description
open IndexedPolynomial.RecursiveSpaceRepresentation
universe u v
variable {I : Interface.{u}} {registry : Registry I} {parameters : Nat} {context : List I.SortCode}

noncomputable def codePresentation (ordered : registry.OrderedFinitary)
    (code : Code I registry parameters context) :
    IndexedPolynomial.RecursiveSpaceRepresentation.Presentation (Base := Env I.Value context) (Index := fun _ => I.Index) where
  polynomial := Code.polynomial code
  coding := fun shape => SlotEncoding.finite (Code.orderedPositionEquiv ordered code shape).symm
  tag := fun _ => 0

theorem code_padding_iff (ordered : registry.OrderedFinitary)
    (code : Code I registry parameters context) {environment : Env I.Value context} {index : I.Index}
    (shape : Code.Shape code environment index) (slot : Nat) :
    ((codePresentation ordered code).coding shape).decode slot = none ↔
      (Code.orderedPositions ordered code shape).length ≤ slot :=
  SlotEncoding.finite_decoded_iff (Code.orderedPositionEquiv ordered code shape).symm slot

theorem code_position_order (ordered : registry.OrderedFinitary)
    (code : Code I registry parameters context) {environment : Env I.Value context} {index : I.Index}
    (shape : Code.Shape code environment index) (slot : Fin (Code.orderedPositions ordered code shape).length) :
    ((codePresentation ordered code).coding shape).encode (Code.orderedPositionEquiv ordered code shape slot) = slot.val := by
  change ((Code.orderedPositionEquiv ordered code shape).symm (Code.orderedPositionEquiv ordered code shape slot)).val = slot.val
  rw [Equiv.symm_apply_apply]

variable {source : PositiveInductiveBlock.Registry}

noncomputable def blockPresentation
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    IndexedPolynomial.RecursiveSpaceRepresentation.Presentation (Base := Env I.Value context) (Index := fun _ => I.Index) where
  polynomial := Unindexed.blockPolynomial block registered
  coding := fun shape => SlotEncoding.finite
    (Code.orderedPositionEquiv (Unindexed.liftOrdered sourceOrder) (Unindexed.blockCode block registered shape.1) shape.2).symm
  tag := fun shape => shape.1.val

theorem block_position_order
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (Unindexed.blockPolynomial block registered).Shape environment index)
    (slot : Fin (Code.orderedPositions (Unindexed.liftOrdered sourceOrder) (Unindexed.blockCode block registered shape.1) shape.2).length) :
    ((blockPresentation sourceOrder block registered).coding shape).encode
      (Code.orderedPositionEquiv (Unindexed.liftOrdered sourceOrder) (Unindexed.blockCode block registered shape.1) shape.2 slot) = slot.val := by
  change ((Code.orderedPositionEquiv (Unindexed.liftOrdered sourceOrder) (Unindexed.blockCode block registered shape.1) shape.2).symm
    (Code.orderedPositionEquiv (Unindexed.liftOrdered sourceOrder) (Unindexed.blockCode block registered shape.1) shape.2 slot)).val = slot.val
  rw [Equiv.symm_apply_apply]

noncomputable def blockRepresentation
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    (environment : Env I.Value context) (index : I.Index) :
    block.Family environment index ≃ RecursiveFamily (blockPresentation sourceOrder block registered) environment index :=
  (Unindexed.blockFamilyEquiv block registered environment index).trans
    (recursiveSpaceRepresentation (blockPresentation sourceOrder block registered) environment index)

noncomputable def interpretedBlockRepresentation
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    (environment : Env I.Value context) {R : Type v}
    (M : Mettapedia.TypeTheory.RecursiveSpace.Model
      (RecursivePayload (blockPresentation sourceOrder block registered) environment) R) (index : I.Index) :
    block.Family environment index ≃
      {value : R // RecursiveValid (blockPresentation sourceOrder block registered) ((Mettapedia.TypeTheory.RecursiveSpace.equivalence M).symm value) index} :=
  (Unindexed.blockFamilyEquiv block registered environment index).trans
    (interpretedRepresentation (blockPresentation sourceOrder block registered) environment M index)

#print axioms code_position_order
#print axioms blockRepresentation
#print axioms interpretedBlockRepresentation
end Mettapedia.TypeTheory.IndexedPositiveContainer.RecursiveSpaceRepresentation

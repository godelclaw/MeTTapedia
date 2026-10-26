import Mettapedia.Languages.HOLLight.IndexedFamilyModels
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace

/-!
# Admitted ordered container families in a received source model

An admitted registered block obtains its natural slots from the existing
ordered-position equivalence. The generic family interpretation then uses the
algebra constructed from source replay and exact root readings. Every result
index retains its guard, including empty fibers.
Ordered finitarity is required separately from positivity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedRegisteredFamilyModels

open Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer
open Mettapedia.Languages.OpenTheory.TypeFamilySemantics

universe u

variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry}
  {parameters : Nat} {context : List I.SortCode}
  (roots : IndexedFamilyModels.ReceivedRoots)
  (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
  (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
  (environment : Env I.Value context) (other : OperatorFamilies.{u+1}) (prior : Assignment.{u+1})

abbrev Family (index : I.Index) :=
  IndexedFamilyModels.Family roots (RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    environment other prior index

noncomputable def representation (index : I.Index) :
    block.Family environment index ≃ Family roots sourceOrder block registered environment other prior index :=
  (Unindexed.blockFamilyEquiv block registered environment index).trans
    (IndexedFamilyModels.representation roots
      (RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered) environment other prior index)

theorem roundtrip (index : I.Index) (value : block.Family environment index) :
    (representation roots sourceOrder block registered environment other prior index).symm
      (representation roots sourceOrder block registered environment other prior index value) = value :=
  (representation roots sourceOrder block registered environment other prior index).symm_apply_apply value

theorem guarded_roundtrip (index : I.Index)
    (value : Family roots sourceOrder block registered environment other prior index) :
    representation roots sourceOrder block registered environment other prior index
      ((representation roots sourceOrder block registered environment other prior index).symm value) = value :=
  (representation roots sourceOrder block registered environment other prior index).apply_symm_apply value

theorem empty_fiber_preserved (index : I.Index) (empty : IsEmpty (block.Family environment index)) :
    IsEmpty (Family roots sourceOrder block registered environment other prior index) :=
  ⟨fun value => empty.false ((representation roots sourceOrder block registered environment other prior index).symm value)⟩

#print axioms representation
#print axioms empty_fiber_preserved

end Mettapedia.Languages.HOLLight.IndexedRegisteredFamilyModels

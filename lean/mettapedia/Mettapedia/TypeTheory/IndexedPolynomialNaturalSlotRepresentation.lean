import Mettapedia.TypeTheory.IndexedPolynomialDescription
import Mettapedia.TypeTheory.IndexedPolynomialGuardedRepresentation

/-!
# Natural-slot representations of first-order constructor inventories

The source-order finite position equivalence supplies the partial natural-slot
codec for every constructor occurrence. The generic guarded representation
retains the original family, every child index and canonical unused slots.
Semantic decoding and native recursive-space interpretation remain distinct.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u
variable {I : Interface.{u}} {context : List I.SortCode}

def naturalSlots (constructors : List (NamedConstructor I context)) :
    GuardedRaw.Positions (inventoryPolynomial constructors) where
  Slot := fun _ => Nat
  coding := fun shape => SlotEncoding.finite (positionEquivFin (constructors.get shape.1).body shape.2)

noncomputable def naturalSlotRepresentation (constructors : List (NamedConstructor I context)) :=
  GuardedRaw.algebraRepresentation (inventoryPolynomial constructors) (naturalSlots constructors)

end Mettapedia.TypeTheory.IndexedPolynomial.Description

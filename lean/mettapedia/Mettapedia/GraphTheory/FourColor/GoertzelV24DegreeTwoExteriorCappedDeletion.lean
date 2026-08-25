import Mettapedia.GraphTheory.FourColor.GoertzelV24CappedCardSubtraction
import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoExteriorBoundary

/-!
# Exact capped deletion at a degree-two exterior boundary

Suppose a finite maximum-degree-two graph is represented through a bounded
interface.  A connected component of the strict exterior exposes at most two
distinct labels at that interface.  Consequently, if advancing the interface
removes only exposed labels, then the cap at five of the remaining component
is determined exactly by the predecessor cap at seven and the exact number of
removed labels.

This is the graph-generic capped-cardinality step.  A concrete rolling
interface still has to prove that its newly promoted labels are among the
component's exposed boundary labels.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DegreeTwoExteriorCappedDeletion

open Finset
open GoertzelV24CappedCardSubtraction
open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

variable {N Interface Label : Type*} [Fintype N] [DecidableEq N]
  [Fintype Interface] [DecidableEq Label]

/-- Cap seven is sufficient and exact for a cap-five successor after deleting
any set of labels exposed at the boundary of one strict-exterior component. -/
theorem min_exteriorComponentLabelSupport_sdiff_five_eq
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N) (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface interfaceVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (removed : Finset Label)
    (hremoved : removed ⊆
      exteriorComponentBoundaryLabels graph interfaceVertex label component) :
    min ((exteriorComponentLabelSupport graph interfaceVertex label component) \
        removed).card 5 =
      min (min (exteriorComponentLabelSupport graph interfaceVertex label
        component).card 7 - removed.card) 5 := by
  have hremovedSupport : removed ⊆
      exteriorComponentLabelSupport graph interfaceVertex label component :=
    hremoved.trans
      (exteriorComponentBoundaryLabels_subset_labelSupport graph
        interfaceVertex label component)
  have hremovedCard : removed.card ≤ 2 :=
    (Finset.card_le_card hremoved).trans
      (card_exteriorComponentBoundaryLabels_le_two graph interfaceVertex label
        component hroot hrootOutside hdegree)
  exact min_card_sdiff_five_eq_min_min_card_seven_sub
    (exteriorComponentLabelSupport graph interfaceVertex label component)
    removed hremovedSupport hremovedCard

end GoertzelV24DegreeTwoExteriorCappedDeletion

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24DegreeTwoExteriorCappedDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactor

/-!
# Capped deletion for one represented exterior incidence

The weighted interface code describes an exterior component through a live
incidence rather than through a connected-component quotient.  This file
identifies those two presentations and transfers the generic degree-two
capped-deletion theorem to the incidence vocabulary used by the finite code.

The only remaining obligation for a concrete rolling interface is geometric:
the labels it promotes must be labels on the entered component's exposed
boundary vertices.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ExteriorIncidenceCappedDeletion

open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24DegreeTwoExteriorCappedDeletion
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open SimpleGraph

variable {N Interface Incidence Label : Type*}
  [Fintype N] [DecidableEq N] [Fintype Interface]
  [Fintype Label] [DecidableEq Label]

/-- The strict-exterior connected component entered by an incidence. -/
noncomputable def exteriorIncidenceComponent
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceVertex : Incidence → N) (incidence : Incidence) :
    (exteriorGraph graph interfaceVertex).ConnectedComponent :=
  (exteriorGraph graph interfaceVertex).connectedComponentMk
    (incidenceVertex incidence)

omit [Fintype Interface] in
/-- For a live incidence, the support stored by the weighted interface code is
exactly the label support of its strict-exterior connected component. -/
theorem exteriorIncidenceLabelSupport_eq_componentLabelSupport
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence)
    (hpresent : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex incidence) :
    exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label incidence =
      exteriorComponentLabelSupport graph interfaceVertex label
        (exteriorIncidenceComponent graph interfaceVertex incidenceVertex
          incidence) := by
  classical
  ext value
  rw [mem_exteriorIncidenceLabelSupport_iff,
    mem_exteriorComponentLabelSupport_iff]
  constructor
  · rintro ⟨_hpresent, vertex, hreachable, hlabel⟩
    refine ⟨⟨vertex, ?_⟩, hlabel⟩
    change
      (exteriorGraph graph interfaceVertex).connectedComponentMk vertex =
        (exteriorGraph graph interfaceVertex).connectedComponentMk
          (incidenceVertex incidence)
    exact ConnectedComponent.sound hreachable.symm
  · rintro ⟨vertex, hlabel⟩
    refine ⟨hpresent, vertex.1, ?_, hlabel⟩
    rw [← ConnectedComponent.eq]
    exact vertex.2.symm

omit [Fintype Label] in
/-- A live incidence into a maximum-degree-two graph exposes at most two
distinct boundary labels. -/
theorem card_exteriorIncidenceBoundaryLabels_le_two
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence)
    (hpresent : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex incidence)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2) :
    (exteriorComponentBoundaryLabels graph interfaceVertex label
      (exteriorIncidenceComponent graph interfaceVertex incidenceVertex
        incidence)).card ≤ 2 := by
  exact card_exteriorComponentBoundaryLabels_le_two graph interfaceVertex label
    (exteriorIncidenceComponent graph interfaceVertex incidenceVertex incidence)
    ConnectedComponent.connectedComponentMk_mem hpresent.1 hdegree

/-- The cap at seven stored for a live incidence determines exactly the cap at
five after deleting any exposed boundary labels. -/
theorem min_exteriorIncidenceLabelSupport_sdiff_five_eq
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N)
    (incidenceSlot : Incidence → Interface)
    (incidenceVertex : Incidence → N) (label : N → Label)
    (incidence : Incidence)
    (hpresent : ExteriorIncidencePresent graph interfaceVertex incidenceSlot
      incidenceVertex incidence)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (removed : Finset Label)
    (hremoved : removed ⊆
      exteriorComponentBoundaryLabels graph interfaceVertex label
        (exteriorIncidenceComponent graph interfaceVertex incidenceVertex
          incidence)) :
    min ((exteriorIncidenceLabelSupport graph interfaceVertex incidenceSlot
        incidenceVertex label incidence) \ removed).card 5 =
      min (min (exteriorIncidenceLabelSupport graph interfaceVertex
        incidenceSlot incidenceVertex label incidence).card 7 - removed.card)
        5 := by
  rw [exteriorIncidenceLabelSupport_eq_componentLabelSupport graph
    interfaceVertex incidenceSlot incidenceVertex label incidence hpresent]
  exact min_exteriorComponentLabelSupport_sdiff_five_eq graph interfaceVertex
    label (exteriorIncidenceComponent graph interfaceVertex incidenceVertex
      incidence) ConnectedComponent.connectedComponentMk_mem hpresent.1 hdegree
    removed hremoved

end GoertzelV24ExteriorIncidenceCappedDeletion

end Mettapedia.GraphTheory.FourColor

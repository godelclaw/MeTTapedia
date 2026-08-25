import Mettapedia.GraphTheory.FourColor.GoertzelV24ExteriorIncidenceCappedDeletion
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceExteriorBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceInterfaceExteriorLabelCap

/-!
# Exact cap update for a regional face incidence

This file specializes degree-two exterior capped deletion to the regional face
graph.  A live face incidence stores the cap at seven of its exterior primal
edge support.  If a rolling interface promotes only labels exposed at that
component's boundary, the stored value and the exact number promoted determine
the successor cap at five.

The theorem deliberately keeps boundary-label provenance as a hypothesis.
Identifying the concrete promoted labels of a Cell rebase is the remaining
source-geometric step.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceExteriorCappedDeletion

open GoertzelV24DegreeTwoExteriorBoundary
open GoertzelV24ExteriorIncidenceCappedDeletion
open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceExteriorBoundary
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraph
open SimpleGraphDartRotation

variable {V E Interface : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype Interface]

noncomputable section

/-- A live regional-face incidence exposes at most two distinct primal-edge
labels at the represented interface. -/
theorem card_faceExteriorIncidenceBoundaryLabels_le_two
    (RS : RotationSystem V E) (region : Finset E)
    (interfaceVertex : Interface → RS.D)
    (incidence : FaceInterfaceIncidence Interface)
    (hpresent :
      (exactFaceInterfaceExteriorLabelCapCode RS region interfaceVertex 7
        ).incidencePresent incidence = true) :
    (exteriorComponentBoundaryLabels (faceRegionalDartGraph RS region)
      interfaceVertex RS.edgeOf
      (exteriorIncidenceComponent (faceRegionalDartGraph RS region)
        interfaceVertex (faceInterfaceIncidenceVertex RS interfaceVertex)
        incidence)).card ≤ 2 := by
  classical
  have hpresent' : ExteriorIncidencePresent (faceRegionalDartGraph RS region)
      interfaceVertex Prod.fst
      (faceInterfaceIncidenceVertex RS interfaceVertex) incidence :=
    (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff RS region
      interfaceVertex incidence 7).1 hpresent
  exact card_exteriorIncidenceBoundaryLabels_le_two
    (faceRegionalDartGraph RS region) interfaceVertex Prod.fst
    (faceInterfaceIncidenceVertex RS interfaceVertex) RS.edgeOf incidence
    hpresent' (faceRegionalDartGraph_neighborSet_ncard_le_two RS region)

/-- The literal cap-seven field of a live regional-face incidence computes the
cap at five after deleting any subset of its exposed boundary labels. -/
theorem min_faceExteriorIncidenceSupport_sdiff_five_eq_storedCap_sub
    (RS : RotationSystem V E) (region : Finset E)
    (interfaceVertex : Interface → RS.D)
    (incidence : FaceInterfaceIncidence Interface)
    (hpresent :
      (exactFaceInterfaceExteriorLabelCapCode RS region interfaceVertex 7
        ).incidencePresent incidence = true)
    (removed : Finset E)
    (hremoved : removed ⊆
      exteriorComponentBoundaryLabels (faceRegionalDartGraph RS region)
        interfaceVertex RS.edgeOf
        (exteriorIncidenceComponent (faceRegionalDartGraph RS region)
          interfaceVertex (faceInterfaceIncidenceVertex RS interfaceVertex)
          incidence)) :
    min ((exteriorIncidenceLabelSupport (faceRegionalDartGraph RS region)
        interfaceVertex Prod.fst
        (faceInterfaceIncidenceVertex RS interfaceVertex) RS.edgeOf incidence) \
      removed).card 5 =
      min (((exactFaceInterfaceExteriorLabelCapCode RS region interfaceVertex 7
        ).incidenceCap incidence).val - removed.card) 5 := by
  classical
  have hpresent' : ExteriorIncidencePresent (faceRegionalDartGraph RS region)
      interfaceVertex Prod.fst
      (faceInterfaceIncidenceVertex RS interfaceVertex) incidence :=
    (exactFaceInterfaceExteriorLabelCapCode_incidencePresent_iff RS region
      interfaceVertex incidence 7).1 hpresent
  rw [exactFaceInterfaceExteriorLabelCapCode_incidenceCap_val RS region
    interfaceVertex incidence 7]
  exact min_exteriorIncidenceLabelSupport_sdiff_five_eq
    (faceRegionalDartGraph RS region) interfaceVertex Prod.fst
    (faceInterfaceIncidenceVertex RS interfaceVertex) RS.edgeOf incidence
    hpresent' (faceRegionalDartGraph_neighborSet_ncard_le_two RS region)
    removed hremoved

end

end GoertzelV24RotationFaceExteriorCappedDeletion

end Mettapedia.GraphTheory.FourColor

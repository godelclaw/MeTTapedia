import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitOpenRegionComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningComparison

/-!
# The two-cap opening reaches the existing open-region graph tower

The two-cap toolchain opening keeps the ten cap vertices as degree-one stubs.
The manuscript deletes them and adds fresh ports.  The preceding comparison
identifies those two simple graphs.  The generic slit comparison identifies the
manuscript graph with the primal graph of the existing literal open-region
rotation.  Their composite is the one reusable entry point for the two-cap
laboratory; it does not construct an annular embedding or transport cyclic
face order.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpening

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation

attribute [-instance] GoertzelV24OpenRegionRotation.retainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCapPair

/-- The two-cap toolchain opening is isomorphic, as a simple graph, to the
primal graph of the existing literal open-region rotation for the same deleted
cap support.  This is a presentation bridge only: the outer dart remains a
parameter and no annular rotation or face-order claim is made here. -/
def openingGraphIsoOpenPrimalGraph (data : Data G) (caps : PentagonCapPair G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    caps.openGraph.Iso
      (PrimalGraph data.toRotationSystem (keep caps.deletedVertexSupport) outer) :=
  caps.openingGraphIso.symm.trans
    (slitGraphIsoOpenPrimalGraph data caps.deletedVertexSupport outer)

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor

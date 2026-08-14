import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitOpenRegionComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularBoundaryIsoTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationIsoTransport

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
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24AnnularBoundaryIsoTransport
open GoertzelV24SimpleGraphRotationIsoTransport

attribute [-instance] GoertzelV24OpenRegionRotation.retainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCapPair

local instance comparisonOpenGraphDecidableRel (caps : PentagonCapPair G) :
    DecidableRel caps.openGraph.Adj :=
  Classical.decRel _

local instance comparisonOpenPrimalGraphDecidableRel
    (data : Data G) (caps : PentagonCapPair G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (keep caps.deletedVertexSupport) outer).Adj :=
  Classical.decRel _

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

/-- The literal two-cap toolchain graph now carries the graph-backed rotation
computed by the open-region construction.  This transports only the dart
rotation and its root through the proved graph isomorphism.  In particular it
does not claim that the two cap interfaces already determine the intended
annular hole faces or their cyclic order. -/
def openingGraphData (data : Data G) (caps : PentagonCapPair G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    Data caps.openGraph :=
  transportData (caps.openingGraphIsoOpenPrimalGraph data outer).symm
    (graphData data (keep caps.deletedVertexSupport) outer)

/-- The comparison also carries the two ordered five-stub interfaces to the
literal open-region primal graph.  This is a boundary-data transport, not an
annular-embedding construction: it preserves the actual graph interfaces
while leaving named hole faces and their cyclic orders as source geometry. -/
def openingBoundaryData (data : Data G) (caps : PentagonCapPair G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport)) :
    AnnularBoundaryData
      (PrimalGraph data.toRotationSystem (keep caps.deletedVertexSupport) outer) 5 :=
  GoertzelV24AnnularBoundaryIsoTransport.transport
    (caps.openingGraphIsoOpenPrimalGraph data outer) caps.boundaryData

/-- Graph-level well-formedness of the two-cap frontier is retained on the
same literal open-region carrier used by the face-transport layer. -/
theorem openingBoundaryData_wellFormed
    (data : Data G) (caps : PentagonCapPair G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep caps.deletedVertexSupport))
    (hboundary : caps.boundaryData.WellFormed) :
    (openingBoundaryData data caps outer).WellFormed :=
  GoertzelV24AnnularBoundaryIsoTransport.wellFormed_transport
    (caps.openingGraphIsoOpenPrimalGraph data outer) caps.boundaryData
    hboundary

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor

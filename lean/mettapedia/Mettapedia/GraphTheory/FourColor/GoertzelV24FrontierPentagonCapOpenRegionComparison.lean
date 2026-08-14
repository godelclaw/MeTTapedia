import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularBoundaryIsoTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitOpenRegionComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpening
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationIsoTransport

/-!
# Addendum V frontier opening reaches the literal open-region tower

Addendum V removes one interior pentagon cap from a frontier tangle which
already carries an ordered outer interface.  The graph-level opening and its
preserved interface were constructed in
`GoertzelV24FrontierPentagonCapOpening`.  This module identifies that same
opening with the existing literal open-region primal graph and transports the
computed rotation and the complete ordered boundary datum through the proved
graph isomorphism.

This is the representation bridge needed before the two hole faces can be
computed.  It does not assume that either interface is a face orbit, package
an annular cellulation, select the frontier tangle from a minimal
counterexample, or construct the L1 crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapOpenRegionComparison

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24AnnularBoundaryIsoTransport
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningComparison
open GoertzelV24SimpleGraphRotationIsoTransport

attribute [-instance] GoertzelV24OpenRegionRotation.retainedVertexDecidableEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance comparisonOpenGraphDecidableRel (cap : PentagonCap G) :
    DecidableRel cap.openGraph.Adj :=
  Classical.decRel _

local instance comparisonOpenPrimalGraphDecidableRel
    (data : Data G) (cap : PentagonCap G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (keep cap.vertexSupport) outer).Adj :=
  Classical.decRel _

namespace PentagonCap

/-- The one-cap toolchain opening is the same simple graph as the primal
graph computed by the literal open-region rotation. -/
def openingGraphIsoOpenPrimalGraph (data : Data G) (cap : PentagonCap G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    cap.openGraph.Iso
      (PrimalGraph data.toRotationSystem (keep cap.vertexSupport) outer) :=
  (GoertzelV24PentagonCapOpeningComparison.PentagonCap.openingGraphIso cap).symm.trans
    (slitGraphIsoOpenPrimalGraph data cap.vertexSupport outer)

/-- The toolchain one-cap graph carries the literal open-region rotation,
transported rather than postulated.  Named hole faces are deliberately not
part of this carrier theorem. -/
def openingGraphData (data : Data G) (cap : PentagonCap G)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    Data cap.openGraph :=
  transportData (openingGraphIsoOpenPrimalGraph data cap outer).symm
    (graphData data (keep cap.vertexSupport) outer)

end PentagonCap

namespace FrontierBoundaryData

variable {outerCount : Nat}

/-- Move Addendum V's complete ordered inner/outer boundary carrier to the
same literal open-region primal graph on which the face-transport tower is
stated. -/
def openingPrimalBoundaryData
    (data : Data G) (frontier : FrontierBoundaryData G outerCount)
    (cap : PentagonCap G) (hinterior : frontier.InteriorPentagonCap cap)
    (hfrontier : frontier.WellFormed)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    AnnularBoundaryData
      (PrimalGraph data.toRotationSystem (keep cap.vertexSupport) outer)
      outerCount :=
  transport (PentagonCap.openingGraphIsoOpenPrimalGraph data cap outer)
    (frontier.openingBoundaryData cap hinterior hfrontier)

/-- The graph-level validity of both ordered interfaces survives the exact
presentation change from the toolchain opening to the literal open-region
primal graph. -/
theorem openingPrimalBoundaryData_wellFormed
    (data : Data G) (frontier : FrontierBoundaryData G outerCount)
    (cap : PentagonCap G) (hinterior : frontier.InteriorPentagonCap cap)
    (hfrontier : frontier.WellFormed)
    (outer : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (keep cap.vertexSupport)) :
    (openingPrimalBoundaryData data frontier cap hinterior hfrontier outer).WellFormed :=
  wellFormed_transport (PentagonCap.openingGraphIsoOpenPrimalGraph data cap outer)
    (frontier.openingBoundaryData cap hinterior hfrontier)
    (frontier.openingBoundaryData_wellFormed cap hinterior hfrontier)

end FrontierBoundaryData

end

end GoertzelV24FrontierPentagonCapOpenRegionComparison

end Mettapedia.GraphTheory.FourColor

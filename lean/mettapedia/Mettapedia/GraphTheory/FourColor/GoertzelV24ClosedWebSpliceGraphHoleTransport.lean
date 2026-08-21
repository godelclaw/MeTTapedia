import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebOpenTangle
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalFaceTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphRotationEndpointInjective

/-!
# Named hole faces on the graph-backed splice output

Addendum XXVII requires the two named holes to remain outside the pumped
region.  The closed-web splice calculus already transports each fully retained
hole to a literal face of the shortened rotation system.  This module carries
those faces through the canonical graph backing and proves that the two output
faces remain distinct there.

The result consumes the finite `OrderedCutEndpointSimple` test.  It does not
construct that test, output boundary data, or the full output annular
cellulation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RotationSystemPrimalFaceTransport.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalGraphBacking
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24SpliceUnification

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance rotationPrimalGraphAdjDecidable
    {W F : Type*} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (RS : RotationSystem W F) :
    DecidableRel (rotationPrimalGraph RS).Adj :=
  Classical.decRel _

attribute [-instance]
  GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace Instance

variable {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : Instance data coloring}

private abbrev ambientEndpointsInjective :
    Function.Injective web.annular.RS.endpoints :=
  endpoints_injective web.annular.cellulation.rotation

/-- A protected source hole becomes a literal facial orbit on the actual
simple graph underlying the shortened splice. -/
def outputGraphFaceOfHoleFaceKept
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (face : OrbitFace web.annular.RS)
    (hkept : HoleFaceKept splice face)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    OrbitFace
      (OrderedCutSpliceData.outputGraphData splice
        ambientEndpointsInjective hsimple).toRotationSystem :=
  outputGraphFaceEquiv splice ambientEndpointsInjective hsimple
    (outputFaceOrbit_of_holeFaceKept splice face hkept).1

/-- The graph-backed shortened output retains two different named hole faces.
This transports the already-proved rotation-level distinction; it does not
infer a cellulation merely from two quotient elements. -/
theorem outputGraphInnerHole_ne_outputGraphOuterHole
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    outputGraphFaceOfHoleFaceKept splice web.annular.cellulation.innerHole
        hinner hsimple ≠
      outputGraphFaceOfHoleFaceKept splice web.annular.cellulation.outerHole
        houter hsimple := by
  intro hfaces
  apply outputInnerHole_ne_outputOuterHole splice hinner houter
  exact (outputGraphFaceEquiv splice ambientEndpointsInjective hsimple).injective
    hfaces

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor

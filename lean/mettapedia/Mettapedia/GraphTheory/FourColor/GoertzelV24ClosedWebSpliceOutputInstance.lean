import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebReductiveAssembly
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphGoodWordTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceSeamArcClosureCriterion

/-!
# L1: assemble the graph-backed splice output instance

The carrier-changing reductive spine consumes a complete smaller
`ClosedWebAtGoodWord.Instance`, not a collection of unrelated splice lemmas.
This module assembles that object on the computed primal graph and then packs
it as the strict-reduction certificate used by the public reductive system.

Every still-open physical receipt remains an explicit argument: protected
holes, endpoint simplicity, retained connectivity, Euler balance, the seam
face count, local two-sidedness, literal internal-dual connectedness, and
total closure of the output web.  Thus this is an end-to-end assembly theorem,
not a construction of those receipts and not closure of Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord.Instance

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24ClosedWebReductiveAssembly
open GoertzelV24ClosedWebSpliceBoundarySimplicity
open GoertzelV24ClosedWebSpliceGraphAnnularCellulation
open GoertzelV24ClosedWebSpliceGraphAnnularCellulation.Instance
open GoertzelV24ClosedWebSpliceGraphAnnularEmbedding
open GoertzelV24ClosedWebSpliceGraphGeometry
open GoertzelV24ClosedWebSpliceGraphGeometry.Instance
open GoertzelV24ClosedWebSpliceSeamArcClosureCriterion
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OpenRegionOutputRestriction
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationSystemPrimalColorTransport
open GoertzelV24RotationSystemPrimalColorTransport.OrderedCutSpliceData
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24SpliceUnification

universe u

variable {W : Type u} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance outputInstanceSourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance outputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

/-- The actual graph-backed splice output, with every source invariant
assembled into one `ClosedWebAtGoodWord.Instance`.  The arguments are exactly
the still-visible physical receipts; no output field is postulated inside the
constructor. -/
def outputInstance
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (profile : splice.EqualProfile)
    (hprofileColoring : profile.coloring =
      rotationColoringOfGraph web.annular coloring)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected)
    (hbalance : splice.LocalEulerBalance)
    (hprofile : splice.SeamFacesMeetFive)
    (htwoSided : splice.SeamFacesTwoSided)
    (hdualConnected :
      (interiorDualGraph (orbitFaceBoundary splice.output)
        (GoertzelV24ClosedWebSpliceGraphGeometry.Instance.outputRotationInteriorFaces
          splice hinner houter)).Connected)
    (htotallyClosed : TotallyClosedWeb
      (outputBoundaryData splice hinner houter hsimple)
      (outputGraphColoring splice profile
        (endpoints_injective web.annular.cellulation.rotation) hsimple)) :
    GoertzelV24ClosedWebAtGoodWord.Instance
      (outputBoundaryData splice hinner houter hsimple)
      (outputGraphColoring splice profile
        (endpoints_injective web.annular.cellulation.rotation) hsimple) := by
  have hpairwise : splice.SeamArcsPairwiseEdgeDisjoint :=
    (seamArcsPairwiseEdgeDisjoint_iff_seamFacesTwoSided
      splice hinner houter).2 htwoSided
  have hseamBoundarySimple : splice.SeamFacesBoundarySimple := by
    apply splice.seamFacesBoundarySimple_of_arcNoncollision
    exact ⟨GoertzelV24ClosedWebSpliceSeamArcAmbientSimplicity.seamArcsInternallySimple
      splice hinner houter, hpairwise⟩
  exact {
    boundary_wellFormed := outputBoundaryData_wellFormed
      splice hinner houter hsimple
    connected := outputGraph_connected_of_retained splice hretained
    annular := outputAnnularEmbedding splice hinner houter hsimple
      hretained hbalance
    geometry := outputGeometryOfSeamBoundarySimple splice hinner houter
      hsimple hretained hbalance hprofile hseamBoundarySimple hdualConnected
    tait := outputGraphColoring_isTait splice profile
      (endpoints_injective web.annular.cellulation.rotation) hsimple
    totallyClosed := htotallyClosed
    goodWord := outputInnerBoundaryWord_good splice profile hprofileColoring
      hinner houter hsimple
  }

/-- Package an existing closed-web instance into the carrier-changing object
used by the public reductive spine. -/
def toPackedInstance : PackedInstance.{u} where
  Vertex := W
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  graph := G
  adjDecidable := inferInstance
  boundary := data
  coloring := coloring
  web := web

/-- **C→D→E assembly joint.**  Once the physical splice receipts construct
the graph-backed output instance above, strict decrease packages it directly
as the public reductive system's certificate.  This theorem does not supply
any of its geometric or total-closure premises. -/
def strictReductionCertificateOfSplice
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (profile : splice.EqualProfile)
    (hprofileColoring : profile.coloring =
      rotationColoringOfGraph web.annular coloring)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected)
    (hbalance : splice.LocalEulerBalance)
    (hprofile : splice.SeamFacesMeetFive)
    (htwoSided : splice.SeamFacesTwoSided)
    (hdualConnected :
      (interiorDualGraph (orbitFaceBoundary splice.output)
        (GoertzelV24ClosedWebSpliceGraphGeometry.Instance.outputRotationInteriorFaces
          splice hinner houter)).Connected)
    (htotallyClosed : TotallyClosedWeb
      (outputBoundaryData splice hinner houter hsimple)
      (outputGraphColoring splice profile
        (endpoints_injective web.annular.cellulation.rotation) hsimple)) :
    PackedInstance.StrictReductionCertificate (toPackedInstance (web := web)) :=
  {
    output := {
      Vertex := RetainedVertex splice.keep
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      graph := rotationPrimalGraph splice.output
      adjDecidable := inferInstance
      boundary := outputBoundaryData splice hinner houter hsimple
      coloring := outputGraphColoring splice profile
        (endpoints_injective web.annular.cellulation.rotation) hsimple
      web := outputInstance splice profile hprofileColoring hinner houter
        hsimple hretained hbalance hprofile htwoSided hdualConnected
        htotallyClosed
    }
    smaller := by
      exact splice.outputSize_lt
  }

end

end GoertzelV24ClosedWebAtGoodWord.Instance

end Mettapedia.GraphTheory.FourColor

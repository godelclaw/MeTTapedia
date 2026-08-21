import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphBoundaryWellFormed
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSystemPrimalColorTransport

/-!
# Good-word transport to the graph-backed splice output

Addendum XXVII's L1 splice checklist keeps the inner hole outside the pumped
region so that its five-edge word is unchanged.  The rotation-level splice
already proves that old internal edges retain their colors.  This module
transports that equality through the computed primal-graph presentation and
the reconstructed ordered boundary data.

The result constructs the graph-backed output's `(3,1,1)` good-word field from
the source field.  It assumes the literal profile coloring is the source graph
coloring transported to the source rotation system; an arbitrary equal-profile
coloring need not preserve the distinguished source word.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord.Instance

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationSystemPrimalColorTransport
open GoertzelV24RotationSystemPrimalColorTransport.OrderedCutSpliceData
open GoertzelV24RotationSystemPrimalEdgePresentation
open GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData
open GoertzelV24SimpleGraphRotationEndpointInjective
open GoertzelV24SpliceUnification

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : Instance data coloring}

noncomputable section

attribute [-instance] GoertzelV24SeamFaceArcPartition.hitPointFintype

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance goodWordSourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance goodWordOutputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

/-- The graph-backed coloring of a retained old boundary edge is its literal
source-profile color. -/
theorem outputGraphColoring_outputBoundaryEdge
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (profile : splice.EqualProfile)
    (hambient : Function.Injective web.annular.RS.endpoints)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (edge : G.edgeSet)
    (hkept : ∀ dart ∈ web.annular.RS.dartsOn edge,
      splice.keep (web.annular.RS.vertOf dart)) :
    outputGraphColoring splice profile hambient hsimple
        (outputBoundaryEdge splice hsimple edge hkept) =
      profile.coloring edge := by
  change graphEdgeColoring splice.output
      (output_endpoints_injective splice hambient hsimple)
      (splice.splicedColoring profile)
      (outputEdgeEquiv splice hambient hsimple
        (retainedInternalSpliceEdge web.annular.RS splice.keep
          splice.left.crossingEdge splice.right.crossingEdge
          splice.leftCrosses splice.rightCrosses splice.leftInjective
          splice.rightInjective splice.cover splice.disjoint splice.outer_kept
          splice.seamEndpoints
          (internalDartOfEdgeKept web.annular.RS splice.keep edge hkept))) = _
  unfold GoertzelV24RotationSystemPrimalEdgePresentation.OrderedCutSpliceData.outputEdgeEquiv
  rw [graphEdgeColoring_apply]
  change splice.splicedColoring profile
      (splice.output.edgeOf
        (Sum.inl (internalDartOfEdgeKept web.annular.RS splice.keep
          edge hkept))) = _
  rw [splice.splicedColoring_internal_edgeOf]
  rw [internalDartOfEdgeKept_edgeOf]

/-- The five ordered inner colors on the graph-backed shortened carrier are
exactly the source inner word. -/
theorem outputInnerBoundaryWord_eq_source
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (profile : splice.EqualProfile)
    (hprofileColoring : profile.coloring =
      rotationColoringOfGraph web.annular coloring)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    (outputBoundaryData splice hinner houter hsimple).innerBoundaryWord
        (outputGraphColoring splice profile
          (endpoints_injective web.annular.cellulation.rotation) hsimple) =
      data.innerBoundaryWord coloring := by
  let hinnerKept : ProtectedInnerInterface.InnerBoundaryKept splice :=
    innerBoundaryKept_of_innerHoleFaceKept splice hinner
  funext port
  change outputGraphColoring splice profile
      (endpoints_injective web.annular.cellulation.rotation) hsimple
      (outputBoundaryEdge splice hsimple (data.innerBoundaryEdge port)
        (hinnerKept port)) =
    coloring (data.innerBoundaryEdge port)
  rw [outputGraphColoring_outputBoundaryEdge]
  rw [hprofileColoring]
  rfl

/-- The source good word survives on the actual graph-backed output boundary.
This is the good-word clause of Addendum XXVII's splice checklist, not a
postulated output-instance field. -/
theorem outputInnerBoundaryWord_good
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (profile : splice.EqualProfile)
    (hprofileColoring : profile.coloring =
      rotationColoringOfGraph web.annular coloring)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses) :
    CAP5BoundaryWordHasColoredBlock311
      ((outputBoundaryData splice hinner houter hsimple).innerBoundaryWord
        (outputGraphColoring splice profile
          (endpoints_injective web.annular.cellulation.rotation) hsimple)) := by
  rw [outputInnerBoundaryWord_eq_source splice profile hprofileColoring]
  exact web.goodWord

end

end GoertzelV24ClosedWebAtGoodWord.Instance

end Mettapedia.GraphTheory.FourColor

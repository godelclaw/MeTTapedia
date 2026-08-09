import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebComputedDepthProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification

/-!
# From repeated closed-web profiles to a concrete splice

The L7 finite-state layer stores a boundary state in a dependent carrier: its
actual crossing width and its actual number of face fragments are part of the
state.  The concrete retained-vertex surgery, on the other hand, works with
fixed finite coordinates.  This module supplies the exact bridge between the
two descriptions.

It deliberately does not manufacture a transversal from a chord, nor does it
claim that an arbitrary pair of cuts bounds a removable corridor.  A caller
must first provide the two genuine boundary sides, their geometric port
correspondence, and the seam condition in `OrderedCutSidesData`.  Once that
has been done, equality in the L7 carrier fills the profile premise of the
concrete splice without re-encoding the finite state by hand.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebProfileSpliceBridge

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSidesData

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Put fixed-coordinate graph-derived cut data into the varying-width L7
carrier.  The two numerical bounds are the only information erased by the
carrier; the full `CorridorCutProfile` remains its payload. -/
def graphCutDepthProfile
    {RS : RotationSystem V E} {crossingEdgeCount faceFragmentCount : Nat}
    (widthBound : Nat)
    (data : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (hwidth : crossingEdgeCount ≤ widthBound)
    (hfragments : faceFragmentCount ≤ 2 * crossingEdgeCount) :
    ClosedWebDepthProfile widthBound where
  crossingEdgeCount := ⟨crossingEdgeCount, Nat.lt_succ_of_le hwidth⟩
  profile := {
    faceFragmentCount := ⟨faceFragmentCount, Nat.lt_succ_of_le hfragments⟩
    profile := data.profile coloring hcoloring
  }

/-- With the width and fragment coordinates fixed, equality in the L7 carrier
is precisely equality of the concrete profile payload.  This is the dependent
bookkeeping needed to pass a profile repeat to the retained-vertex splice. -/
theorem graphCutProfile_eq_of_depthProfile_eq
    {RS : RotationSystem V E} {crossingEdgeCount faceFragmentCount : Nat}
    {widthBound : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount 0 faceFragmentCount)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (hwidth : crossingEdgeCount ≤ widthBound)
    (hfragments : faceFragmentCount ≤ 2 * crossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound left coloring hcoloring hwidth hfragments =
        graphCutDepthProfile widthBound right coloring hcoloring hwidth hfragments) :
    left.profile coloring hcoloring = right.profile coloring hcoloring := by
  simpa [graphCutDepthProfile] using hprofiles

/-- Equality of two bounded L7 states forces equality of their concrete
crossing widths. -/
theorem crossingEdgeCount_eq_of_graphCutDepthProfile_eq
    {RS : RotationSystem V E}
    {leftCrossingEdgeCount leftFaceFragmentCount : Nat}
    {rightCrossingEdgeCount rightFaceFragmentCount : Nat}
    {widthBound : Nat}
    (left : GraphCorridorCutData RS leftCrossingEdgeCount 0 leftFaceFragmentCount)
    (right : GraphCorridorCutData RS rightCrossingEdgeCount 0 rightFaceFragmentCount)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (leftWidth : leftCrossingEdgeCount ≤ widthBound)
    (rightWidth : rightCrossingEdgeCount ≤ widthBound)
    (leftFragments : leftFaceFragmentCount ≤ 2 * leftCrossingEdgeCount)
    (rightFragments : rightFaceFragmentCount ≤ 2 * rightCrossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound left coloring hcoloring leftWidth leftFragments =
        graphCutDepthProfile widthBound right coloring hcoloring rightWidth rightFragments) :
    leftCrossingEdgeCount = rightCrossingEdgeCount := by
  simpa [graphCutDepthProfile] using
    congrArg (fun profile : ClosedWebDepthProfile widthBound =>
      profile.crossingEdgeCount.val) hprofiles

/-- Equality of two bounded L7 states also forces equality of their concrete
face-fragment counts. -/
theorem faceFragmentCount_eq_of_graphCutDepthProfile_eq
    {RS : RotationSystem V E}
    {leftCrossingEdgeCount leftFaceFragmentCount : Nat}
    {rightCrossingEdgeCount rightFaceFragmentCount : Nat}
    {widthBound : Nat}
    (left : GraphCorridorCutData RS leftCrossingEdgeCount 0 leftFaceFragmentCount)
    (right : GraphCorridorCutData RS rightCrossingEdgeCount 0 rightFaceFragmentCount)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (leftWidth : leftCrossingEdgeCount ≤ widthBound)
    (rightWidth : rightCrossingEdgeCount ≤ widthBound)
    (leftFragments : leftFaceFragmentCount ≤ 2 * leftCrossingEdgeCount)
    (rightFragments : rightFaceFragmentCount ≤ 2 * rightCrossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound left coloring hcoloring leftWidth leftFragments =
        graphCutDepthProfile widthBound right coloring hcoloring rightWidth rightFragments) :
    leftFaceFragmentCount = rightFaceFragmentCount := by
  simpa [graphCutDepthProfile] using
    congrArg (fun profile : ClosedWebDepthProfile widthBound =>
      profile.profile.faceFragmentCount.val) hprofiles

/-- Retype raw cut data after a repeated profile has identified its two
dependent numerical coordinates.  This is only transport across equal natural
numbers; it does not alter the cut, its region, or its port order. -/
def castGraphCutDataAlongProfileRepeat
    {RS : RotationSystem V E}
    {leftCrossingEdgeCount leftFaceFragmentCount : Nat}
    {rightCrossingEdgeCount rightFaceFragmentCount : Nat}
    (hcrossing : leftCrossingEdgeCount = rightCrossingEdgeCount)
    (hfragments : leftFaceFragmentCount = rightFaceFragmentCount)
    (right : GraphCorridorCutData RS rightCrossingEdgeCount 0 rightFaceFragmentCount) :
    GraphCorridorCutData RS leftCrossingEdgeCount 0 leftFaceFragmentCount := by
  cases hcrossing
  cases hfragments
  exact right

/-- After the forced coordinate transport, an equal bounded L7 profile is the
same concrete corridor profile.  This closes the dependent-type part of the
unification; a separate geometric theorem still has to supply the actual
simple transversals and their seam. -/
theorem graphCutProfile_eq_of_dependentDepthProfile_eq
    {RS : RotationSystem V E}
    {leftCrossingEdgeCount leftFaceFragmentCount : Nat}
    {rightCrossingEdgeCount rightFaceFragmentCount : Nat}
    {widthBound : Nat}
    (left : GraphCorridorCutData RS leftCrossingEdgeCount 0 leftFaceFragmentCount)
    (right : GraphCorridorCutData RS rightCrossingEdgeCount 0 rightFaceFragmentCount)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (leftWidth : leftCrossingEdgeCount ≤ widthBound)
    (rightWidth : rightCrossingEdgeCount ≤ widthBound)
    (leftFragments : leftFaceFragmentCount ≤ 2 * leftCrossingEdgeCount)
    (rightFragments : rightFaceFragmentCount ≤ 2 * rightCrossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound left coloring hcoloring leftWidth leftFragments =
        graphCutDepthProfile widthBound right coloring hcoloring rightWidth rightFragments) :
    left.profile coloring hcoloring =
      (castGraphCutDataAlongProfileRepeat
        (crossingEdgeCount_eq_of_graphCutDepthProfile_eq left right coloring hcoloring
          leftWidth rightWidth leftFragments rightFragments hprofiles)
        (faceFragmentCount_eq_of_graphCutDepthProfile_eq left right coloring hcoloring
          leftWidth rightWidth leftFragments rightFragments hprofiles)
        right).profile coloring hcoloring := by
  let hcrossing := crossingEdgeCount_eq_of_graphCutDepthProfile_eq left right
    coloring hcoloring leftWidth rightWidth leftFragments rightFragments hprofiles
  let hfragments := faceFragmentCount_eq_of_graphCutDepthProfile_eq left right
    coloring hcoloring leftWidth rightWidth leftFragments rightFragments hprofiles
  cases hcrossing
  cases hfragments
  simpa [castGraphCutDataAlongProfileRepeat] using
    graphCutProfile_eq_of_depthProfile_eq left right coloring hcoloring
      leftWidth leftFragments (by simpa using hprofiles)

/-! ## Compatibility with the computed depth-profile route -/

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComputedDepthProfile
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph

local instance subtypeEdgeSetDecidableEq
    {Vertex : Type*} [DecidableEq Vertex]
    {G : SimpleGraph Vertex} [DecidableRel G.Adj] : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The L7 state already computed from a closed-web transversal is exactly the
fixed-coordinate graph-cut state used above.  This definition exposes that
identity at the source-facing boundary, rather than asking a later splice to
recreate its profile from an unrelated representation. -/
def chordSideDepthProfile
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {G : SimpleGraph Vertex} [DecidableRel G.Adj] {outerCount : Nat}
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed} {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound)
    (hC : IsTaitEdgeColoring G C)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side)
    (indexing : VertexSetCrossingIndexing embedded.RS
      (assignment.inside cut side chord)) :
    ClosedWebDepthProfile widthBound :=
  graphCutDepthProfile widthBound
    (vertexSetBoundaryGraphCutDataWithIndexing embedded.RS
      (assignment.inside cut side chord) indexing)
    (rotationColoringOfGraph embedded C)
    (rotationColoringOfGraph_isTait embedded C hC)
    (assignment.crossingWidth cut side chord)
    (vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
      embedded.RS (assignment.inside cut side chord))

/-- No semantic translation remains between the computed closed-web L7 state
and the state consumed by the splice bridge. -/
theorem chordSideDepthProfile_eq_profileWithIndexing
    {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]
    {G : SimpleGraph Vertex} [DecidableRel G.Adj] {outerCount : Nat}
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {pair : RadialPathPair data C first second}
    {embedded : ClosedWebAnnularEmbedding data}
    {hdata : data.WellFormed} {htriple : IsTaitColorTriple majority first second}
    {widthBound : Nat}
    (assignment : ChordSideAssignment pair embedded hdata htriple widthBound)
    (hC : IsTaitEdgeColoring G C)
    (cut : Fin pair.firstPath.path.length) (side : Bool)
    (chord : SectorChord pair embedded hdata htriple cut side)
    (indexing : VertexSetCrossingIndexing embedded.RS
      (assignment.inside cut side chord)) :
    chordSideDepthProfile assignment hC cut side chord indexing =
      assignment.profileWithIndexing hC cut side chord indexing := by
  rfl

/-- Turn an equality of bounded L7 states, expressed in the actual geometric
port correspondence, into the fixed-coordinate splice interface.  The
`OrderedCutSidesData` argument is intentionally separate: it is where the
simple-transversal and complementary-piece geometry must be proved. -/
def profileAlignedSpliceOfEqualDepthProfile
    {RS : RotationSystem V E} {crossingEdgeCount faceFragmentCount : Nat}
    {widthBound : Nat}
    (data : OrderedCutSidesData RS crossingEdgeCount 0 faceFragmentCount)
    (indexing : CorridorProfileIndexing crossingEdgeCount 0 faceFragmentCount)
    (seamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS
            (data.reindexRight indexing).keep
            (data.reindexRight indexing).left.crossingEdge
            (data.reindexRight indexing).leftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS
            (data.reindexRight indexing).keep
            (data.reindexRight indexing).right.crossingEdge
            (data.reindexRight indexing).rightCrosses step).1.1.1)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (hwidth : crossingEdgeCount ≤ widthBound)
    (hfragments : faceFragmentCount ≤ 2 * crossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound data.left coloring hcoloring hwidth hfragments =
        graphCutDepthProfile widthBound
          (reindexGraphCorridorCutData data.right indexing)
          coloring hcoloring hwidth hfragments) :
    ProfileAlignedSplice data where
  indexing := indexing
  seamEndpoints := seamEndpoints
  coloring := coloring
  coloring_isTait := hcoloring
  profile_eq := by
    simpa [OrderedCutSidesData.reindexRight] using
      graphCutProfile_eq_of_depthProfile_eq data.left
        (reindexGraphCorridorCutData data.right indexing)
        coloring hcoloring hwidth hfragments hprofiles

/-- The source's forward coloring part of the splice checklist now follows
directly from an equal L7 profile and the separately certified seam geometry. -/
theorem output_taitColorable_of_equalDepthProfile
    {RS : RotationSystem V E} {crossingEdgeCount faceFragmentCount : Nat}
    {widthBound : Nat}
    (data : OrderedCutSidesData RS crossingEdgeCount 0 faceFragmentCount)
    (indexing : CorridorProfileIndexing crossingEdgeCount 0 faceFragmentCount)
    (seamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS
            (data.reindexRight indexing).keep
            (data.reindexRight indexing).left.crossingEdge
            (data.reindexRight indexing).leftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS
            (data.reindexRight indexing).keep
            (data.reindexRight indexing).right.crossingEdge
            (data.reindexRight indexing).rightCrosses step).1.1.1)
    (coloring : RS.EdgeColoring Color) (hcoloring : RS.IsTaitEdgeColoring coloring)
    (hwidth : crossingEdgeCount ≤ widthBound)
    (hfragments : faceFragmentCount ≤ 2 * crossingEdgeCount)
    (hprofiles :
      graphCutDepthProfile widthBound data.left coloring hcoloring hwidth hfragments =
        graphCutDepthProfile widthBound
          (reindexGraphCorridorCutData data.right indexing)
          coloring hcoloring hwidth hfragments) :
    TaitColorable
      (profileAlignedSpliceOfEqualDepthProfile data indexing seamEndpoints
        coloring hcoloring hwidth hfragments hprofiles).spliceData.output :=
  (profileAlignedSpliceOfEqualDepthProfile data indexing seamEndpoints
    coloring hcoloring hwidth hfragments hprofiles).output_taitColorable

end

end GoertzelV24ClosedWebProfileSpliceBridge

end Mettapedia.GraphTheory.FourColor

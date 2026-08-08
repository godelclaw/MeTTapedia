import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInterleavingChordHoleDrainage
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnermostChordHoleFree

/-!
# Uniform drainage from an innermost actual chord

Minimum endpoint span excludes a strictly nested actual chord.  Properness
of the Tait coloring excludes shared endpoints.  Hence every distinct chord
touching the open interval of the chosen innermost chord strictly
interleaves it, and the same retained exact cut drains all such chords to the
common hole side.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebInnermostChordDrainage

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordHoleSideCutWitness
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebInterleavingChordHoleDrainage
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24WalkCycleParity
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance innermostDrainageGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- One fixed exact cut and one fixed hole-free side of an innermost chord
drain every distinct actual chord which touches its open path interval. -/
theorem all_touching_chords_drain_from_holeFreeSide_of_innermost
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (position : OrderedPathChord (pair.firstPath.path.length + 1))
    (hpositionData : IsMajorityChordAt
      C majority first second pair.firstPath position)
    (hposition : position ∈ majorityChordDiagram
      C majority first second pair.firstPath)
    (hinnermost : InnermostIn position
      (majorityChordDiagram C majority first second pair.firstPath))
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈
          (majorityChordOfPosition position hpositionData).cycleWalk.edges)
    (hholes : labels embedded.cellulation.innerHole =
      labels embedded.cellulation.outerHole)
    (side : Bool)
    (hsideHole : labels (chordSideFace embedded.cellulation
        ((majorityChordOfPosition position hpositionData).boundary
          htriple) side) ≠
      labels embedded.cellulation.innerHole) :
    ∀ (otherPosition :
        OrderedPathChord (pair.firstPath.path.length + 1))
      (hotherData : IsMajorityChordAt
        C majority first second pair.firstPath otherPosition),
      otherPosition ∈ majorityChordDiagram
          C majority first second pair.firstPath →
      otherPosition ≠ position →
      otherPosition.HasEndpointInside position →
      (otherPosition.left.val < position.left.val ∧
          position.left.val < otherPosition.right.val ∧
          otherPosition.right.val < position.right.val ∧
          labels (dartOrbitFace embedded.RS
              (embedded.RS.alpha
                (majorityChordOfPosition otherPosition
                  hotherData).chordDart)) ≠
            labels (chordSideFace embedded.cellulation
              ((majorityChordOfPosition position hpositionData).boundary
                htriple) side)) ∨
        (position.left.val < otherPosition.left.val ∧
          otherPosition.left.val < position.right.val ∧
          position.right.val < otherPosition.right.val ∧
          labels (dartOrbitFace embedded.RS
              (majorityChordOfPosition otherPosition
                hotherData).chordDart) ≠
            labels (chordSideFace embedded.cellulation
              ((majorityChordOfPosition position hpositionData).boundary
                htriple) side)) := by
  intro otherPosition hotherData hother hne htouches
  have hcross : otherPosition.Crosses position :=
    other_chord_crosses_of_hasEndpointInside_innermost
      hinnermost hposition hother hne htouches
  have hinterleave :
      ((majorityChordOfPosition otherPosition hotherData).left.val <
          (majorityChordOfPosition position hpositionData).left.val ∧
        (majorityChordOfPosition position hpositionData).left.val <
          (majorityChordOfPosition otherPosition hotherData).right.val ∧
        (majorityChordOfPosition otherPosition hotherData).right.val <
          (majorityChordOfPosition position hpositionData).right.val) ∨
      ((majorityChordOfPosition position hpositionData).left.val <
          (majorityChordOfPosition otherPosition hotherData).left.val ∧
        (majorityChordOfPosition otherPosition hotherData).left.val <
          (majorityChordOfPosition position hpositionData).right.val ∧
        (majorityChordOfPosition position hpositionData).right.val <
          (majorityChordOfPosition otherPosition hotherData).right.val) := by
    simpa [OrderedPathChord.Crosses, majorityChordOfPosition] using hcross
  exact interleaving_chord_innerFace_label_ne_holeFreeSide
    embedded hdata
      (majorityChordOfPosition position hpositionData)
      (majorityChordOfPosition otherPosition hotherData)
      htriple labels hexact hholes side hsideHole hinterleave

/-- Every nonempty actual chord diagram has one minimum-span chord, one
retained exact cut, and one fixed genuinely hole-free side which uniformly
drains every distinct actual chord touching its open interval. -/
theorem exists_innermost_exact_holeFreeSide_with_uniform_drainage
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (hnonempty :
      (majorityChordDiagram C majority first second
        pair.firstPath).Nonempty) :
    ∃ (position : OrderedPathChord (pair.firstPath.path.length + 1))
      (hpositionData : IsMajorityChordAt
        C majority first second pair.firstPath position)
      (labels : OrbitFace embedded.RS → F2) (side : Bool),
      position ∈ majorityChordDiagram
          C majority first second pair.firstPath ∧
        InnermostIn position
          (majorityChordDiagram C majority first second pair.firstPath) ∧
        orbitFaceParityBoundaryLinearMap embedded.RS labels =
          walkEdgeParity
            (majorityChordOfPosition position hpositionData).cycleWalk ∧
        (∀ dart : embedded.RS.D,
          labels (dartOrbitFace embedded.RS dart) ≠
              labels (dartOrbitFace embedded.RS
                (embedded.RS.alpha dart)) ↔
            (embedded.RS.edgeOf dart).1 ∈
              (majorityChordOfPosition position
                hpositionData).cycleWalk.edges) ∧
        labels embedded.cellulation.innerHole =
          labels embedded.cellulation.outerHole ∧
        labels (chordSideFace embedded.cellulation
            ((majorityChordOfPosition position hpositionData).boundary
              htriple) side) ≠
          labels embedded.cellulation.innerHole ∧
        HoleFreeChordSide embedded.cellulation
          ((majorityChordOfPosition position hpositionData).boundary
            htriple) side ∧
        ∀ (otherPosition :
            OrderedPathChord (pair.firstPath.path.length + 1))
          (hotherData : IsMajorityChordAt
            C majority first second pair.firstPath otherPosition),
          otherPosition ∈ majorityChordDiagram
              C majority first second pair.firstPath →
          otherPosition ≠ position →
          otherPosition.HasEndpointInside position →
          (otherPosition.left.val < position.left.val ∧
              position.left.val < otherPosition.right.val ∧
              otherPosition.right.val < position.right.val ∧
              labels (dartOrbitFace embedded.RS
                  (embedded.RS.alpha
                    (majorityChordOfPosition otherPosition
                      hotherData).chordDart)) ≠
                labels (chordSideFace embedded.cellulation
                  ((majorityChordOfPosition position
                    hpositionData).boundary htriple) side)) ∨
            (position.left.val < otherPosition.left.val ∧
              otherPosition.left.val < position.right.val ∧
              position.right.val < otherPosition.right.val ∧
              labels (dartOrbitFace embedded.RS
                  (majorityChordOfPosition otherPosition
                    hotherData).chordDart) ≠
                labels (chordSideFace embedded.cellulation
                  ((majorityChordOfPosition position
                    hpositionData).boundary htriple) side)) := by
  obtain ⟨position, hposition, hinnermost⟩ :=
    exists_innermost_majorityChord hnonempty
  have hpositionData : IsMajorityChordAt
      C majority first second pair.firstPath position :=
    (mem_majorityChordDiagram_iff).1 hposition
  let selected := majorityChordOfPosition position hpositionData
  rcases exists_exact_chordCycle_faceCut_with_holeFreeSide
      embedded hdata pair selected htriple with
    ⟨labels, side, hboundary, hexact, hholes, hsideHole, hholeFree⟩
  have hdrainage :=
    all_touching_chords_drain_from_holeFreeSide_of_innermost
      embedded hdata pair htriple position hpositionData hposition
        hinnermost labels hexact hholes side hsideHole
  exact ⟨position, hpositionData, labels, side, hposition, hinnermost,
    hboundary, hexact, hholes, hsideHole, hholeFree, hdrainage⟩

end

end GoertzelV24ClosedWebInnermostChordDrainage

end Mettapedia.GraphTheory.FourColor

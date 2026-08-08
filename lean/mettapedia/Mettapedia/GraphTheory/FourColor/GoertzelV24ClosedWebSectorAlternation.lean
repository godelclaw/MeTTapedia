import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInnermostChordDrainage

/-!
# The closed-web Sector-Alternation certificate

The playbook's L8 obligation is the embedded, rotation-system part of
Sector Alternation: a same-path chord and its radial subarc must cut off a
face region containing neither annular hole.  The retained exact face cut
proves more.  For a minimum-span actual chord, every other actual chord
touching its open interval has its interior endpoint on the opposite side
of that cut.

This module packages that result for either radial path.  It also retains
the empty-diagram alternative, so the source-facing statement does not
silently assume that a majority chord exists.  No geometric sector name or
unrelated proof architecture is introduced.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebSectorAlternation

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordHoleSideCutWitness
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebInnermostChordDrainage
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24WalkCycleParity
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Exchange the two disjoint radial components and their path witnesses. -/
def swapRadialPathPair
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    (pair : RadialPathPair data C first second) :
    RadialPathPair data C first second where
  firstComponent := pair.secondComponent
  secondComponent := pair.firstComponent
  components_ne := pair.components_ne.symm
  firstPath := pair.secondPath
  secondPath := pair.firstPath
  cover_support := by
    rw [Set.union_comm]
    exact pair.cover_support

local instance sectorAlternationGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The complete embedded L8 witness on the first path of a radial pair.

The selected actual chord has minimum endpoint span.  Its exact face cut
selects a side separated from both holes, and every distinct actual chord
touching the selected open interval drains away from that side. -/
structure InnermostChordDrainageCertificate
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    {C : G.EdgeColoring Color} {first second : Color}
    (pair : RadialPathPair data C first second)
    (majority : Color)
    (htriple : IsTaitColorTriple majority first second) where
  position : OrderedPathChord (pair.firstPath.path.length + 1)
  hpositionData : IsMajorityChordAt
    C majority first second pair.firstPath position
  labels : OrbitFace embedded.RS → F2
  side : Bool
  position_mem : position ∈ majorityChordDiagram
    C majority first second pair.firstPath
  innermost : InnermostIn position
    (majorityChordDiagram C majority first second pair.firstPath)
  boundary_eq :
    orbitFaceParityBoundaryLinearMap embedded.RS labels =
      walkEdgeParity
        (majorityChordOfPosition position hpositionData).cycleWalk
  exact_cut : ∀ dart : embedded.RS.D,
    labels (dartOrbitFace embedded.RS dart) ≠
        labels (dartOrbitFace embedded.RS (embedded.RS.alpha dart)) ↔
      (embedded.RS.edgeOf dart).1 ∈
        (majorityChordOfPosition position hpositionData).cycleWalk.edges
  holes_same_side :
    labels embedded.cellulation.innerHole =
      labels embedded.cellulation.outerHole
  selected_side_away_from_holes :
    labels (chordSideFace embedded.cellulation
        ((majorityChordOfPosition position hpositionData).boundary
          htriple) side) ≠
      labels embedded.cellulation.innerHole
  selected_side_hole_free :
    HoleFreeChordSide embedded.cellulation
      ((majorityChordOfPosition position hpositionData).boundary
        htriple) side
  touching_chords_drain :
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
                htriple) side))

/-- A nonempty chord diagram on the first radial path has the full embedded
Sector-Alternation certificate. -/
theorem exists_firstPath_sectorAlternationCertificate_of_nonempty
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (hnonempty :
      (majorityChordDiagram C majority first second
        pair.firstPath).Nonempty) :
    Nonempty (InnermostChordDrainageCertificate
      embedded pair majority htriple) := by
  rcases exists_innermost_exact_holeFreeSide_with_uniform_drainage
      embedded hdata pair htriple hnonempty with
    ⟨position, hpositionData, labels, side, hposition, hinnermost,
      hboundary, hexact, hholes, hside, hholeFree, hdrainage⟩
  exact ⟨{
    position := position
    hpositionData := hpositionData
    labels := labels
    side := side
    position_mem := hposition
    innermost := hinnermost
    boundary_eq := hboundary
    exact_cut := hexact
    holes_same_side := hholes
    selected_side_away_from_holes := hside
    selected_side_hole_free := hholeFree
    touching_chords_drain := hdrainage }⟩

/-- On the first radial path, either there are no majority chords or L8 has
an explicit embedded certificate. -/
theorem firstPath_chordDiagram_empty_or_sectorAlternationCertificate
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second) :
    majorityChordDiagram C majority first second pair.firstPath = ∅ ∨
      Nonempty (InnermostChordDrainageCertificate
        embedded pair majority htriple) := by
  classical
  by_cases hnonempty :
      (majorityChordDiagram C majority first second
        pair.firstPath).Nonempty
  · exact Or.inr <|
      exists_firstPath_sectorAlternationCertificate_of_nonempty
        embedded hdata pair htriple hnonempty
  · apply Or.inl
    exact Finset.not_nonempty_iff_eq_empty.mp hnonempty

/-- The same empty-or-certified alternative holds on the second radial path
after exchanging the two path witnesses.  The color-pair order stays fixed,
as it indexes the common support graph rather than an oriented path. -/
theorem secondPath_chordDiagram_empty_or_sectorAlternationCertificate
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second) :
    majorityChordDiagram C majority first second
        (swapRadialPathPair pair).firstPath = ∅ ∨
      Nonempty (InnermostChordDrainageCertificate
        embedded (swapRadialPathPair pair) majority htriple) := by
  exact firstPath_chordDiagram_empty_or_sectorAlternationCertificate
    embedded hdata (swapRadialPathPair pair) htriple

/-- L8 on both disjoint radial paths: each actual same-path chord diagram is
either empty or carries a minimum-span hole-free drainage certificate. -/
theorem both_radialPaths_sectorAlternation
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second) :
    (majorityChordDiagram C majority first second pair.firstPath = ∅ ∨
        Nonempty (InnermostChordDrainageCertificate
          embedded pair majority htriple)) ∧
      (majorityChordDiagram C majority first second
          (swapRadialPathPair pair).firstPath = ∅ ∨
        Nonempty (InnermostChordDrainageCertificate
          embedded (swapRadialPathPair pair) majority htriple)) := by
  exact ⟨
    firstPath_chordDiagram_empty_or_sectorAlternationCertificate
      embedded hdata pair htriple,
    secondPath_chordDiagram_empty_or_sectorAlternationCertificate
      embedded hdata pair htriple⟩

/-- Source-facing L8 theorem at the sharp five-stub boundary.  Total closure
at a good word produces the two disjoint radial paths, four distinct facial
anchors, and the embedded empty-or-draining alternative on both paths. -/
theorem exists_two_radialPaths_with_sectorAlternation_at_five
    {data : AnnularBoundaryData G 5}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C)) :
    ∃ majority singletonFirst singletonSecond : Color,
      ∃ htriple : IsTaitColorTriple majority singletonFirst singletonSecond,
      ∃ pair : RadialPathPair data C singletonFirst singletonSecond,
        Disjoint pair.firstPath.path.toSubgraph.verts
            pair.secondPath.path.toSubgraph.verts ∧
        innerBoundaryPosition embedded hdata pair.firstPath.inner ≠
            innerBoundaryPosition embedded hdata pair.secondPath.inner ∧
        outerBoundaryPosition embedded hdata pair.firstPath.outer ≠
            outerBoundaryPosition embedded hdata pair.secondPath.outer ∧
        (majorityChordDiagram C majority singletonFirst singletonSecond
              pair.firstPath = ∅ ∨
            Nonempty (InnermostChordDrainageCertificate
              embedded pair majority htriple)) ∧
        (majorityChordDiagram C majority singletonFirst singletonSecond
              (swapRadialPathPair pair).firstPath = ∅ ∨
            Nonempty (InnermostChordDrainageCertificate
              embedded (swapRadialPathPair pair) majority htriple)) := by
  rcases exists_radialPathPair_with_distinct_hole_positions_at_five
      embedded hdata hconnected C hC hclosed hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple, pair,
      hdisjoint, hinner, houter⟩
  have hsector := both_radialPaths_sectorAlternation
    embedded hdata pair htriple
  exact ⟨majority, singletonFirst, singletonSecond, htriple, pair,
    hdisjoint, hinner, houter, hsector.1, hsector.2⟩

end

end GoertzelV24ClosedWebSectorAlternation

end Mettapedia.GraphTheory.FourColor

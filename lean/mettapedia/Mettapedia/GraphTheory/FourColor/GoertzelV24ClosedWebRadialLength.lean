import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSectorAlternation

/-!
# Large closed webs have a long radial coordinate

At a good closed web, the selected singleton color-pair support is the union
of two simple radial paths.  Every interior vertex belongs to that support.
Consequently the interior vertex count is at most the sum of the two path
lengths plus their two initial vertices.  This is the first quantitative
bridge required by L6: a sufficiently large web forces one long radial
coordinate before the later shallow-corridor/deep-nest split is applied.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebRadialLength

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24ClosedWebSectorAlternation
open GoertzelV24ClosedWebTotalClosure
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Regard an interior vertex as a vertex of any valid Tait color-pair
support. -/
def interiorSupportVertex
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second) :
    {vertex // vertex ∈ data.interiorVertices} →
      ColorPairSupportVertex C first second :=
  fun vertex => ⟨vertex.1,
    interior_mem_colorPairGraph_support data hdata C hC hpair vertex.2⟩

theorem interiorSupportVertex_injective
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second) :
    Function.Injective (interiorSupportVertex data hdata C hC hpair) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg
    (fun vertex : ColorPairSupportVertex C first second => vertex.1) heq

/-- Two path witnesses covering the selected support bound its cardinality
by their two edge lengths plus their two initial vertices. -/
theorem card_colorPairSupportVertex_le_radialPath_lengths
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {first second : Color}
    (pair : RadialPathPair data C first second) :
    Fintype.card (ColorPairSupportVertex C first second) ≤
      pair.firstPath.path.length + pair.secondPath.path.length + 2 := by
  classical
  let firstVertices := pair.firstPath.path.support.toFinset
  let secondVertices := pair.secondPath.path.support.toFinset
  have hcover : firstVertices ∪ secondVertices = Finset.univ := by
    ext vertex
    have hmembership := Set.ext_iff.mp pair.cover_support vertex
    simpa [firstVertices, secondVertices,
      SimpleGraph.Walk.mem_verts_toSubgraph] using hmembership
  calc
    Fintype.card (ColorPairSupportVertex C first second) =
        (Finset.univ : Finset
          (ColorPairSupportVertex C first second)).card := by simp
    _ = (firstVertices ∪ secondVertices).card := by rw [hcover]
    _ ≤ firstVertices.card + secondVertices.card :=
      Finset.card_union_le firstVertices secondVertices
    _ = pair.firstPath.path.length + pair.secondPath.path.length + 2 := by
      rw [List.toFinset_card_of_nodup
          pair.firstPath.path_isPath.support_nodup,
        List.toFinset_card_of_nodup
          pair.secondPath.path_isPath.support_nodup,
        pair.firstPath.path.length_support,
        pair.secondPath.path.length_support]
      omega

/-- The interior vertex count is bounded by the combined lengths of the two
radial paths. -/
theorem card_interiorVertices_le_radialPath_lengths
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (pair : RadialPathPair data C first second) :
    data.interiorVertices.card ≤
      pair.firstPath.path.length + pair.secondPath.path.length + 2 := by
  calc
    data.interiorVertices.card =
        Fintype.card {vertex // vertex ∈ data.interiorVertices} := by simp
    _ ≤ Fintype.card (ColorPairSupportVertex C first second) :=
      Fintype.card_le_of_injective
        (interiorSupportVertex data hdata C hC hpair)
        (interiorSupportVertex_injective data hdata C hC hpair)
    _ ≤ pair.firstPath.path.length + pair.secondPath.path.length + 2 :=
      card_colorPairSupportVertex_le_radialPath_lengths pair

/-- Quantitative radial-length alternative: more than twice `bound + 1`
interior vertices force one of the two radial paths to have length greater
than `bound`. -/
theorem one_radialPath_long_of_many_interiorVertices
    {data : AnnularBoundaryData G outerCount}
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {first second : Color} (hpair : ValidColorPair first second)
    (pair : RadialPathPair data C first second) (bound : Nat)
    (hlarge : 2 * (bound + 1) < data.interiorVertices.card) :
    bound < pair.firstPath.path.length ∨
      bound < pair.secondPath.path.length := by
  have hcard := card_interiorVertices_le_radialPath_lengths
    hdata C hC hpair pair
  by_contra hnotLong
  push Not at hnotLong
  omega

/-- The source-facing package handed from L8 to L6: two disjoint radial
paths with distinct facial anchors, embedded chord drainage on both paths,
and a proof that one path is quantitatively long. -/
structure LongRadialSectorWitness
    {data : AnnularBoundaryData G 5}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (majority first second : Color)
    (htriple : IsTaitColorTriple majority first second)
    (bound : Nat) where
  pair : RadialPathPair data C first second
  paths_disjoint :
    Disjoint pair.firstPath.path.toSubgraph.verts
      pair.secondPath.path.toSubgraph.verts
  inner_anchors_ne :
    innerBoundaryPosition embedded hdata pair.firstPath.inner ≠
      innerBoundaryPosition embedded hdata pair.secondPath.inner
  outer_anchors_ne :
    outerBoundaryPosition embedded hdata pair.firstPath.outer ≠
      outerBoundaryPosition embedded hdata pair.secondPath.outer
  first_sector_alternation :
    majorityChordDiagram C majority first second pair.firstPath = ∅ ∨
      Nonempty (InnermostChordDrainageCertificate
        embedded pair majority htriple)
  second_sector_alternation :
    majorityChordDiagram C majority first second
        (swapRadialPathPair pair).firstPath = ∅ ∨
      Nonempty (InnermostChordDrainageCertificate
        embedded (swapRadialPathPair pair) majority htriple)
  one_path_long :
    bound < pair.firstPath.path.length ∨
      bound < pair.secondPath.path.length

/-- At a good five-stub totally closed web, a sufficiently large interior
produces the complete long-radial L8-to-L6 witness. -/
theorem exists_longRadialSectorWitness_at_five
    {data : AnnularBoundaryData G 5}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    (hconnected : G.Connected)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hclosed : TotallyClosedWeb data C)
    (hgood : CAP5BoundaryWordHasColoredBlock311
      (data.innerBoundaryWord C))
    (bound : Nat)
    (hlarge : 2 * (bound + 1) < data.interiorVertices.card) :
    ∃ majority first second : Color,
      ∃ htriple : IsTaitColorTriple majority first second,
        Nonempty (LongRadialSectorWitness
          embedded hdata C majority first second htriple bound) := by
  rcases exists_two_radialPaths_with_sectorAlternation_at_five
      embedded hdata hconnected C hC hclosed hgood with
    ⟨majority, first, second, htriple, pair,
      hdisjoint, hinner, houter, hfirstSector, hsecondSector⟩
  have hpair : ValidColorPair first second :=
    ⟨htriple.2.1, htriple.2.2.1, htriple.2.2.2.2.2⟩
  have hlong := one_radialPath_long_of_many_interiorVertices
    hdata C hC hpair pair bound hlarge
  exact ⟨majority, first, second, htriple, ⟨{
    pair := pair
    paths_disjoint := hdisjoint
    inner_anchors_ne := hinner
    outer_anchors_ne := houter
    first_sector_alternation := hfirstSector
    second_sector_alternation := hsecondSector
    one_path_long := hlong }⟩⟩

end

end GoertzelV24ClosedWebRadialLength

end Mettapedia.GraphTheory.FourColor

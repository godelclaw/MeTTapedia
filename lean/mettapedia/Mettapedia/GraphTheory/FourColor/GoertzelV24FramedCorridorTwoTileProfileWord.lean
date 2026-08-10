import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSourceProfileWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorRailPair
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorTwoTileLayerProfile

/-!
# A source-indexed two-tile depth-profile word

Addendum XXVII assigns finite depth profiles to actual layer boundaries, then
uses a repeated profile in a sufficiently long corridor.  The preceding
two-tile construction supplies a literal six-step source layer boundary with
an oriented deletion side and six ordered ports.  This file indexes those
boundaries along the source corridor and applies the finite L7 pigeonhole to
their computed profiles.

The result records only the finite-repeat input.  It does not claim that two
repeated local boundaries have already been assembled into the complementary
pieces of a global splice; that is a separate formation-and-gluing step.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance twoTileProfileWordGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The first interior tile of an indexed pair of adjacent source tiles.
The four-position margin leaves both tiles with the successor data required
by the concrete two-tile boundary construction. -/
def sourceTwoTileLeftInterior {blockLength : Nat}
    (offset : Fin (blockLength - 4)) : CorridorInterior blockLength :=
  corridorInteriorOfOffset ⟨offset.val, by
    have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
    omega⟩

/-- The first source tile in an indexed two-tile layer has its required
successor. -/
theorem sourceTwoTileLeftInterior_hasNext {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    (sourceTwoTileLeftInterior offset).center.val + 2 < blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 1 + 2 < blockLength
  omega

/-- The second source tile in an indexed two-tile layer also has its required
successor. -/
theorem sourceTwoTileLeftInterior_hasNextNext {blockLength : Nat}
    (offset : Fin (blockLength - 4)) :
    (nextCorridorInterior (sourceTwoTileLeftInterior offset)
      (sourceTwoTileLeftInterior_hasNext offset)).center.val + 2 <
      blockLength := by
  have hoffset := (Nat.lt_sub_iff_add_lt).mp offset.isLt
  change offset.val + 1 + 1 + 2 < blockLength
  omega

/-- The first corner-aligned interface of the literal two-tile source layer
at an indexed corridor position. -/
noncomputable def sourceTwoTileFirstInterfaceAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      (sourceTwoTileLeftInterior offset)
      (sourceTwoTileLeftInterior_hasNext offset) :=
  realization.sourceCornerAlignedSlabInterface hcubic hrotation htwoSided hunique
    (sourceTwoTileLeftInterior offset) (sourceTwoTileLeftInterior_hasNext offset)

/-- The second corner-aligned interface of the same literal two-tile source
layer. -/
noncomputable def sourceTwoTileSecondInterfaceAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedSlabInterface realization htwoSided hunique
      (nextCorridorInterior (sourceTwoTileLeftInterior offset)
        (sourceTwoTileLeftInterior_hasNext offset))
      (sourceTwoTileLeftInterior_hasNextNext offset) :=
  realization.sourceCornerAlignedSlabInterface hcubic hrotation htwoSided hunique
    (nextCorridorInterior (sourceTwoTileLeftInterior offset)
      (sourceTwoTileLeftInterior_hasNext offset))
    (sourceTwoTileLeftInterior_hasNextNext offset)

/-- The literal six-step layer boundary around the two adjacent source tiles
at one corridor offset. -/
noncomputable def sourceTwoTileLayerBoundaryAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedTwoTileLayerBoundary
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset) :=
  sourceCornerAlignedTwoTileLayerBoundary hcubic hrotation
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset)

/-- The L7 depth profile computed from the actual oriented six-port boundary
at a source corridor position. -/
noncomputable def sourceTwoTileLayerDepthProfile
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4))
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 6 :=
  (sourceTwoTileLayerBoundaryAt realization hcubic hrotation htwoSided
    hunique offset).orderedDepthProfile coloring hcoloring

/-- One more actual two-tile source layer than the six-port L7 state count
forces two distinct corridor positions to have exactly the same computed
depth profile. -/
theorem exists_equal_sourceTwoTileLayerDepthProfiles
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : closedWebCutProfileCount 6 + 1 ≤ blockLength - 4)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (closedWebCutProfileCount 6 + 1), first ≠ second ∧
      sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge first) coloring hcoloring =
      sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (closedWebCutProfileCount 6 + 1) →
      ClosedWebDepthProfile 6 := fun offset =>
    sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  rcases exists_depthProfile_repeat 6 profiles with ⟨first, second, hne, heq⟩
  exact ⟨first, second, hne, heq⟩

/-- A sufficiently long source corridor has two equal, literal two-tile
six-port depth profiles whose starts are separated by at least three whole
corridor positions.  This is the finite-state spacing refinement required by
the already-proved remote rail-separation lemmas: pair a profile with its
source offset modulo four, so a repeated pair cannot occur too near itself.

This theorem supplies an explicit geometric separation budget; it does not
yet replace the two boundaries by an abstract splice premise. -/
theorem exists_equal_sourceTwoTileLayerDepthProfiles_separated
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (hlarge : 4 * closedWebCutProfileCount 6 + 1 ≤ blockLength - 4)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (4 * closedWebCutProfileCount 6 + 1),
      first.val + 3 < second.val ∧
      sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge first) coloring hcoloring =
      sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
        hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (4 * closedWebCutProfileCount 6 + 1) →
      ClosedWebDepthProfile 6 := fun offset =>
    sourceTwoTileLayerDepthProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  by_contra hrepeat
  have hseparated : ∀ first second,
      first.val + 3 < second.val → profiles first ≠ profiles second := by
    intro first second hfar heq
    exact hrepeat ⟨first, second, hfar, heq⟩
  let encode : Fin (4 * closedWebCutProfileCount 6 + 1) →
      ClosedWebDepthProfile 6 × Fin 4 := fun offset =>
    (profiles offset, ⟨offset.val % 4, Nat.mod_lt _ (by omega)⟩)
  have hinjective : Function.Injective encode := by
    intro first second heq
    have hprofile : profiles first = profiles second := by
      exact congrArg Prod.fst heq
    have hmod : first.val % 4 = second.val % 4 := by
      have hresidue := congrArg (fun pair => pair.2.val) heq
      simpa [encode] using hresidue
    apply Fin.ext
    by_cases hval : first.val = second.val
    · exact hval
    · rcases lt_or_gt_of_ne hval with hfirst | hsecond
      · have hfar : first.val + 3 < second.val := by omega
        exact False.elim (hseparated first second hfar hprofile)
      · have hfar : second.val + 3 < first.val := by omega
        exact False.elim (hseparated second first hfar hprofile.symm)
  have hcard := Fintype.card_le_of_injective encode hinjective
  simp [card_closedWebDepthProfile] at hcard
  omega

/-- The finite two-tile profile coordinate also retains the actual paired
facial-dual rails between its two consecutive source interfaces.  This is
chosen from the source's three checked rung cases, so a later layer assembly
can use concrete paths rather than reconstructing rails from a profile word. -/
noncomputable def sourceTwoTileRailPairAt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 4)) :
    SourceCornerAlignedRailPair
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique offset)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique offset) :=
  Classical.choice (exists_sourceCornerAlignedRailPair hcubic hrotation
    (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
      hunique offset)
    (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
      hunique offset))

/-- Two two-tile source layers whose starts differ by at least three corridor
positions have no remote rail collision, on either source track or across the
two tracks.  This turns the spacing built into the L7 repeat into concrete
noncrossing geometry for the source's layer-boundary construction. -/
theorem sourceTwoTileRailPairSupports_disjoint_of_add_three_lt
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (first second : Fin (blockLength - 4))
    (hseparated : first.val + 3 < second.val) :
    (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
      first).firstRail.support.Disjoint
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second).firstRail.support ∧
    (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
      first).secondRail.support.Disjoint
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second).secondRail.support ∧
    (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
      first).firstRail.support.Disjoint
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second).secondRail.support ∧
    (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
      first).secondRail.support.Disjoint
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second).firstRail.support := by
  have hcenter : (sourceTwoTileLeftInterior first).center.val + 3 <
      (sourceTwoTileLeftInterior second).center.val := by
    change first.val + 1 + 3 < second.val + 1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sourceCornerAlignedRailPair_firstRail_support_disjoint_of_add_three_lt
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        first)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second)
      hcenter
  · exact sourceCornerAlignedRailPair_secondRail_support_disjoint_of_add_three_lt
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        first)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second)
      hcenter
  · exact sourceCornerAlignedRailPair_first_second_support_disjoint_of_add_three_lt
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        first)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second)
      hcenter
  · exact sourceCornerAlignedRailPair_second_first_support_disjoint_of_add_three_lt
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique first)
      (sourceTwoTileFirstInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileSecondInterfaceAt realization hcubic hrotation htwoSided
        hunique second)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        first)
      (sourceTwoTileRailPairAt realization hcubic hrotation htwoSided hunique
        second)
      hcenter

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCompression

/-!
# Source-prefix repetition over the port-incidence carrier

The literal cumulative source-prefix profile is an indexed regional boundary.
Besides its earlier semantic laws, each of its two displayed cut edges occurs
in at most two occurrence-sensitive face fragments, because a rotation-system
edge has exactly two darts.

At four face fragments the gap-at-least-four repeat demand is exactly
`6164737`.  Equality of the complete raw splice profile remains the
conclusion.  This is an L7 theorem, not a reachable-closure certificate or a
completed numerical `V₀`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPortIncidencePrefixEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- A literal cumulative source-prefix profile satisfies the
occurrence-sensitive port-incidence laws. -/
theorem localLayerLeftPrefixBoundedProfile_isPortIncidenceSemantic
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.localLayerPrefixCrossing step) ≠ 0) :
    BoundedIsPortIncidenceSemantic
      (interface.localLayerLeftPrefixBoundedProfile color hcolor) := by
  unfold localLayerLeftPrefixBoundedProfile
  unfold regionalBoundaryBoundedProfile
  exact regionalBoundaryProfile_isPortIncidenceSemantic
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))
    interface.localLayerPrefixCrossing
    interface.localLayerPrefixCrossing_mem_prefixEdgeRegion color hcolor

end SourceConsecutiveSlabInterface

/-- L7: the literal source-prefix word repeats at gap at least four over the
port-incidence carrier. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_portIncidence_separated
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
    (hlarge : 4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1 ≤
      blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin
        (4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hsemantic : ∀ offset,
      BoundedIsPortIncidenceSemantic (profiles offset) := by
    intro offset
    exact SourceConsecutiveSlabInterface.localLayerLeftPrefixBoundedProfile_isPortIncidenceSemantic
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge offset)) coloring (fun step => hcoloring _)
  exact exists_separated_profile_eq_of_portIncidenceSemantic profiles hsemantic

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

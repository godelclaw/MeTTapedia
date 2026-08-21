import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCompression

/-!
# Lossless compression of the literal serial-prefix profile word

The route-correct cumulative state before one source Cell is
`sourceCorridorSerialInputBoundedProfileAt`.  It is computed on the union of
the preceding literal complementary Cells and the displayed two-edge input
cut; it is not the older complete-hex geometric prefix.

Every such graph-derived state satisfies two uniform semantic restrictions:
face continuation is an equivalence relation, and either displayed edge can
occur in at most two occurrence-sensitive boundary fragments.  The generic
width-two port-incidence codec is lossless on exactly those states.  This
file specializes that codec to the heterogeneous literal source word and
reduces its separated repeat demand from the raw bounded-profile count to
`6164737` positions.

This is a finite carrier theorem, not yet a reachable-closure computation,
a one-Cell factorization theorem, or a numerical vertex threshold `V0`.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixProfileCompressionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every literal serial-prefix input state satisfies the graph-semantic laws
used by the lossless width-two port-incidence codec. -/
theorem sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
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
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    BoundedIsPortIncidenceSemantic
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hcolor) := by
  unfold sourceCorridorSerialInputBoundedProfileAt
  unfold regionalBoundaryBoundedProfile
  exact regionalBoundaryProfile_isPortIncidenceSemantic
    (sourceCorridorSerialCutRegionAt realization hcubic hrotation htwoSided
      hunique offset)
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).localLayerPrefixCrossing)
    (sourceCorridorSerialCutRegionAt_inputCrossing realization hcubic
      hrotation htwoSided hunique offset)
    color hcolor

/-- The compact, route-correct state observed immediately before one indexed
literal source Cell. -/
noncomputable def sourceCorridorSerialInputCompressedProfileAt
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
    (offset : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    BoundedWidthTwoPortIncidenceProfile 4 :=
  compressPortIncidenceBounded
    (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique offset color hcolor)
    (sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique offset color hcolor)

/-- Equality of compact literal serial states recovers equality of all five
fields of the corresponding manuscript profiles. -/
theorem sourceCorridorSerialInputCompressedProfileAt_eq_reflects
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
    (left right : Fin (blockLength - 3))
    (color : G.edgeSet → Color)
    (hleft : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique left).localLayerPrefixCrossing step) ≠ 0)
    (hright : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique right).localLayerPrefixCrossing step) ≠ 0)
    (heq : sourceCorridorSerialInputCompressedProfileAt realization hcubic
      hrotation htwoSided hunique left color hleft =
        sourceCorridorSerialInputCompressedProfileAt realization hcubic
          hrotation htwoSided hunique right color hright) :
    sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique left color hleft =
      sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique right color hright := by
  exact compressPortIncidenceBounded_injective
    (sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique left color hleft)
    (sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique right color hright)
    heq

/-- The lossless literal serial carrier has exactly `1541184` states. -/
theorem card_sourceCorridorSerialInputCompressedProfile :
    Fintype.card (BoundedWidthTwoPortIncidenceProfile 4) = 1541184 := by
  rw [card_boundedWidthTwoPortIncidenceProfile,
    boundedWidthTwoPortIncidenceProfileCount_four]

/-- A corridor with `6164737` literal serial positions has two equal complete
five-field states separated by three intervening source positions. -/
theorem exists_equal_sourceCorridorSerialInputProfiles_portIncidenceCompressed
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ (offset : Fin (blockLength - 3)) (step : Fin 2),
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).localLayerPrefixCrossing step) ≠ 0) :
    ∃ first second :
        Fin (4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
          htwoSided hunique (Fin.castLE hlarge first) color
            (hcolor (Fin.castLE hlarge first)) =
        sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
          htwoSided hunique (Fin.castLE hlarge second) color
            (hcolor (Fin.castLE hlarge second)) := by
  let profiles :
      Fin (4 * boundedWidthTwoPortIncidenceProfileCount 4 + 1) →
        BoundedCorridorCutProfile 2 0 4 :=
    fun offset =>
      sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (Fin.castLE hlarge offset) color
          (hcolor (Fin.castLE hlarge offset))
  have hsemantic : ∀ offset,
      BoundedIsPortIncidenceSemantic (profiles offset) := by
    intro offset
    exact sourceCorridorSerialInputBoundedProfileAt_isPortIncidenceSemantic
      realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset) color (hcolor (Fin.castLE hlarge offset))
  have hrepeat :=
    exists_separated_profile_eq_of_portIncidenceSemantic profiles hsemantic
  simpa only [profiles] using hrepeat

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

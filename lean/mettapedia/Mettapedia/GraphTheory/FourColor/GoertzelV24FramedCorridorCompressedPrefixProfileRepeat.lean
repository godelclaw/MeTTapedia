import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoProfileCompression

/-!
# Source-prefix repetition over the semantic width-two carrier

The cumulative source-prefix profile is graph-derived.  Its tracked
connectivity and face continuation therefore obey the diagonal and symmetry
laws used by `GoertzelV24WidthTwoProfileCompression`.  This file applies the
lossless compressed pigeonhole theorem to the literal source-indexed profile
word.

At the four-fragment source bound, the separated-repeat demand falls from
`4 * 801805237456896 + 1` to `6147484705`.  This is an L7 carrier theorem,
not the full reachable-state closure and not a practical `V₀` claim.  The
twenty-state Lemma-8.18 laboratory is not used here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WidthTwoProfileCompression
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorCompressedPrefixProfileEdgeSetDecidableEq :
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

/-- A literal cumulative source-prefix profile lies in the lossless semantic
carrier. -/
theorem localLayerLeftPrefixBoundedProfile_isGraphSemantic
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.localLayerPrefixCrossing step) ≠ 0) :
    BoundedIsGraphSemantic
      (interface.localLayerLeftPrefixBoundedProfile color hcolor) := by
  unfold localLayerLeftPrefixBoundedProfile
  unfold regionalBoundaryBoundedProfile
  exact regionalProfile_isGraphSemantic
    interface.localLayerLeftPrefixGraphCutData
    interface.localLayerLeftPrefixGraphCutData_portsInRegion color hcolor

end SourceConsecutiveSlabInterface

/-- L7: one more source-prefix cross-section than the compressed semantic
carrier forces equality of the complete raw profiles consumed by the splice. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_compressed
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
    (hlarge : boundedWidthTwoCompressedProfileCount 4 + 1 ≤ blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin (boundedWidthTwoCompressedProfileCount 4 + 1),
      first ≠ second ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin (boundedWidthTwoCompressedProfileCount 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hsemantic : ∀ offset, BoundedIsGraphSemantic (profiles offset) := by
    intro offset
    exact (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset)).localLayerLeftPrefixBoundedProfile_isGraphSemantic
        coloring (fun step => hcoloring _)
  exact exists_ne_profile_eq_of_semantic profiles hsemantic (by omega)

/-- L7: the modulo-four tag yields a gap of at least four while using the
compressed semantic carrier. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_compressed_separated
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
    (hlarge : 4 * boundedWidthTwoCompressedProfileCount 4 + 1 ≤
      blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin
        (4 * boundedWidthTwoCompressedProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin
        (4 * boundedWidthTwoCompressedProfileCount 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hsemantic : ∀ offset, BoundedIsGraphSemantic (profiles offset) := by
    intro offset
    exact (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      (Fin.castLE hlarge offset)).localLayerLeftPrefixBoundedProfile_isGraphSemantic
        coloring (fun step => hcoloring _)
  exact exists_separated_profile_eq_of_semantic profiles hsemantic

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileRepeat
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoFaceEquivalenceCompression

/-!
# Source-prefix repetition over the face-equivalence carrier

The literal cumulative source-prefix profile is an indexed regional boundary
profile.  Its face-continuation table is therefore literal equality of face
labels, hence an equivalence relation in addition to satisfying the tracked
color, fragment-incidence, and positive-length laws.

At four face fragments the gap-at-least-four repeat demand is exactly
`74564737`.  Equality of the complete raw splice profile remains the
conclusion.  This is an L7 theorem, not the reachable transfer closure or a
practical numerical `V₀`.
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
open GoertzelV24WidthTwoFaceEquivalenceCompression
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorFaceEquivalencePrefixEdgeSetDecidableEq :
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

/-- A literal cumulative source-prefix profile satisfies the face-equivalence
semantic laws. -/
theorem localLayerLeftPrefixBoundedProfile_isFaceEquivalenceSemantic
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.localLayerPrefixCrossing step) ≠ 0) :
    BoundedIsFaceEquivalenceSemantic
      (interface.localLayerLeftPrefixBoundedProfile color hcolor) := by
  unfold localLayerLeftPrefixBoundedProfile
  unfold regionalBoundaryBoundedProfile
  exact regionalBoundaryProfile_isFaceEquivalenceSemantic
    (corridorPrefixEdgeRegion
      realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      (leftInterior.center.val + 1))
    interface.localLayerPrefixCrossing
    interface.localLayerPrefixCrossing_mem_prefixEdgeRegion color hcolor

end SourceConsecutiveSlabInterface

/-- L7: the literal source-prefix word repeats at gap at least four over the
face-equivalence carrier. -/
theorem exists_equal_sourceSlabPrefixBoundedProfiles_faceEquivalence_separated
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
    (hlarge : 4 * boundedWidthTwoFaceEquivalenceProfileCount 4 + 1 ≤
      blockLength - 3)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ∃ first second : Fin
        (4 * boundedWidthTwoFaceEquivalenceProfileCount 4 + 1),
      first.val + 3 < second.val ∧
      sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge first) coloring hcoloring =
        sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
          hunique (Fin.castLE hlarge second) coloring hcoloring := by
  let profiles : Fin
        (4 * boundedWidthTwoFaceEquivalenceProfileCount 4 + 1) →
      BoundedCorridorCutProfile 2 0 4 := fun offset =>
    sourceSlabPrefixBoundedProfile realization hcubic hrotation htwoSided
      hunique (Fin.castLE hlarge offset) coloring hcoloring
  have hsemantic : ∀ offset,
      BoundedIsFaceEquivalenceSemantic (profiles offset) := by
    intro offset
    exact SourceConsecutiveSlabInterface.localLayerLeftPrefixBoundedProfile_isFaceEquivalenceSemantic
      (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        (Fin.castLE hlarge offset)) coloring (fun step => hcoloring _)
  exact exists_separated_profile_eq_of_faceEquivalenceSemantic profiles hsemantic

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

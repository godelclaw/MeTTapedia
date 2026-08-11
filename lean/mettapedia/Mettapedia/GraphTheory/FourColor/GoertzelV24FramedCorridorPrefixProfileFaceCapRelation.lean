import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileCellFactor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFactorSum

/-!
# Relational finite-profile face-cap update for one source Cell

This file joins the two exact halves of the occurrence-sensitive cap update:
the old-prefix factor sum is resolved through incoming finite-profile
coordinates (with the singleton-rung residue kept explicit), while the new
hexagon and its overlap are computed directly from source geometry.

The result is an existential finite relation for every outgoing cap
coordinate.  It does not assert a deterministic successor profile.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFaceCapRelationEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedSlabInterface

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

/-- Every actual outgoing cap coordinate is obtained by the source's finite
relational update: a capped sum of incoming coordinates and explicit rung
residues, plus the computed Cell contribution, minus the computed common-rung
overlap. -/
theorem exists_localLayerRightPrefixProfileFaceCapRelation
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet
        aligned.toInterface.nextLocalLayerPrefixCrossing)
      aligned.toInterface.localLayerRightPrefixRegion))) :
    ∃ assignment : aligned.LocalLayerLeftFactor
          (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) →
        Option aligned.LocalLayerLeftBoundaryIndex,
      (∀ factor, factor ∈ aligned.localLayerLeftFactorFragments
            (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) →
        match assignment factor with
        | some inputIndex =>
            (((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                color hleftColor).profile.faceLengthCap inputIndex).val) =
              aligned.localLayerLeftFactorPositionCap
                (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index)
                factor
        | none =>
            aligned.localLayerLeftFactorPositionCap
                (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                  index)
                factor = 1) ∧
      (((aligned.toInterface.localLayerRightPrefixBoundedProfile
          color hrightColor).profile.faceLengthCap index).val) =
        min
          (min
              (∑ factor ∈ aligned.localLayerLeftFactorFragments
                  (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index),
                match assignment factor with
                | some inputIndex =>
                    ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                        color hleftColor).profile.faceLengthCap inputIndex).val
                | none => 1)
              5 +
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 5 else 1) -
            (if (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt
                    index).1.1 =
                  aligned.toInterface.nextCenterLayerFace.1 then 1 else 0))
          5 := by
  rcases aligned.exists_localLayerLeftFactorCapResolution hcubic hrotation
      color hleftColor
        (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index) with
    ⟨assignment, hresolve, hsum⟩
  refine ⟨assignment, hresolve, ?_⟩
  rw [aligned.localLayerRightPrefixBoundedProfile_faceLengthCap_eq_cellUpdate,
    hsum]
  rfl

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

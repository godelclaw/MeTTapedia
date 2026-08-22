import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSuccessorPortIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceCapUpdate

/-!
# Exact successor face caps for a serial boundary rebase

The successor face coordinates and their port incidence already live on the
stable occurrence carrier of the literal rebase switch.  This file supplies
the remaining manuscript face coordinate at the geometric level: the cap at
five of a successor fragment is the overlap-corrected sum of its old-prefix
and newly displayed two-edge slices.

The formula is occurrence-sensitive and therefore counts a shared seam once
without identifying the two sides of a bridge.  It is an exact successor cap
law, not yet a graph-free decoder: the next finite-state step must recover the
old-prefix slice cap from the predecessor profile and its residual state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceSuccessorCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The cap stored by the successor profile is the exact inclusion-exclusion
of the old-prefix and two-edge rebase slices on the successor face fragment.
All three finite numbers are capped at five or bounded by the two-edge seam. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_faceLengthCap_eq_slices
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
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    let RS := embedded.cellulation.rotation.toRotationSystem
    let oldRegion :=
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
    let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
      hcubic hrotation htwoSided hunique offset hnext
    let boundaryFragment :=
      sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment
    let root := orbitFaceRoot RS boundaryFragment.1.1
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.faceLengthCap fragment).val =
      min
        (min (faceRegionalFragmentPositionSlice RS root
              (oldRegion ∪ newRegion) oldRegion boundaryFragment.2.1).card 5 +
          min (faceRegionalFragmentPositionSlice RS root
              (oldRegion ∪ newRegion) newRegion boundaryFragment.2.1).card 5 -
          (faceRegionalFragmentPositionSlice RS root
                (oldRegion ∪ newRegion) oldRegion boundaryFragment.2.1 ∩
            faceRegionalFragmentPositionSlice RS root
                (oldRegion ∪ newRegion) newRegion boundaryFragment.2.1).card)
        5 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newRegion := sourceCorridorSerialBoundaryRebaseEdgeSetAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let nextRegion := sourceCorridorSerialCutRegionAt realization hcubic
    hrotation htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let boundaryFragment :=
    sourceCorridorSerialBoundaryRebaseSuccessorFaceFragmentAt realization
      hcubic hrotation htwoSided hunique offset hnext fragment
  have hnextRegion : nextRegion = oldRegion ∪ newRegion :=
    sourceCorridorSerialCutRegionAt_next_eq_prefixCut_union_rebase realization
      hcubic hrotation htwoSided hunique offset hnext
  subst nextRegion
  let root := orbitFaceRoot RS boundaryFragment.1.1
  have hfragmentEdges : data.regionalFragmentEdges fragment =
      boundaryRegionalFragmentEdges RS
        (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        (oldRegion ∪ newRegion) boundaryFragment := by
    rw [data.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
      (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS
        (oldRegion ∪ newRegion)
        (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext))]
    rfl
  have hseam : (oldRegion ∩ newRegion).card < 5 := by
    refine lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_right) ?_
    have hcard := sourceCorridorSerialBoundaryRebaseEdgeSetAt_card_le_two
      realization hcubic hrotation htwoSided hunique offset hnext
    simpa [newRegion] using (lt_of_le_of_lt hcard (by omega : 2 < 5))
  have hcap := min_card_faceRegionalFragmentEdges_union_eq_min_slices_sub_inter
    RS htwoSided root oldRegion newRegion
      boundaryFragment.2.1 hseam
  change min (data.regionalFragmentEdges fragment).card 5 = _
  rw [hfragmentEdges]
  change min (faceRegionalFragmentEdges RS root (oldRegion ∪ newRegion)
      boundaryFragment.2.1).card 5 = _
  exact hcap

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

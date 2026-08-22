import Mettapedia.GraphTheory.FourColor.GoertzelV24SimpleGraphThreeFactorSelectedAnchor
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceComponentCapSum

/-!
# Old-factor anchors for a literal facial rebase

Every old-prefix occurrence inside a successor face fragment belongs to an old
component which meets the finite rebase switch.  This is the source-specific
specialization of the generic three-factor selected-anchor theorem: the old
prefix, newly displayed two-edge region, and facial seam are the three factors,
and the proved eight-edge switch contains every genuine change of factor.

The selected anchor is transported through the exact finite closure theorem,
so it is already expressed in the same occurrence coordinates used by the
canonical component-cap decoder.  This is the coverage half of the eventual
factor-fragment/representative equivalence; it does not yet identify their
finite sums.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SimpleGraphThreeFactorContraction
open GoertzelV24SimpleGraphThreeFactorSelectedAnchor
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceOldFactorAnchorEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Every old-prefix occurrence connected to a selected successor occurrence
has an old-component anchor on the finite switch, and the finite rebase closure
connects the output coordinate to that anchor. -/
theorem exists_sourceCorridorSerialBoundaryRebaseOldFactorAnchor
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (output : {position // position ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root})
    (position : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card)
    (hpositionOld : position ∈
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges).support)
    (hreachable :
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        ).Reachable output.1 position) :
    let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
      realization hcubic hrotation htwoSided hunique offset hnext root
    let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root
    ∃ anchor : {position // position ∈ carrier},
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges).Reachable anchor.1 position ∧
      Relation.ReflTransGen
        (boundedSerialBoundaryRebaseFaceComponentStep code)
        (carrierCoordinate carrier output)
        (carrierCoordinate carrier anchor) := by
  let oldGraph := faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let newGraph := faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic hrotation
      htwoSided hunique offset hnext)
  let seamGraph := sourceCorridorSerialBoundaryRebaseFaceSeamAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let code := sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext root
  have hreachableUnion : ((oldGraph ⊔ newGraph) ⊔ seamGraph).Reachable
      output.1 position := by
    rw [← sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
      realization hcubic hrotation htwoSided hunique offset hnext root]
    exact hreachable
  rcases exists_selected_firstFactor_anchor oldGraph newGraph seamGraph
      (fun position => position ∈ carrier) output.1 position output.2
      hpositionOld (by
        intro x middle y hx hy hold hnew
        apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
          realization hcubic hrotation htwoSided hunique offset hnext root
            middle).2
        have hinter := faceRegionalAmbientPositionGraph_switch_mem_inter
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges
          (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
            hrotation htwoSided hunique offset hnext)
          hx hy hold hnew
        exact Finset.mem_union_right _ (Finset.mem_inter.1 hinter).2)
      (by
        intro x middle y _hx hy _hold hseam
        apply (mem_sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_iff
          realization hcubic hrotation htwoSided hunique offset hnext root
            middle).2
        apply
          sourceCorridorSerialBoundaryRebaseFaceSeamAt_support_projects_finiteSwitch
            realization hcubic hrotation htwoSided hunique offset hnext root
        exact SimpleGraph.mem_support_of_reachable hy hseam)
      hreachableUnion with ⟨anchor, hanchor, holdAnchor⟩
  let selectedAnchor : {position // position ∈ carrier} := ⟨anchor, hanchor⟩
  have hanchorNext :
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        ).Reachable anchor position := by
    rw [sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
      realization hcubic hrotation htwoSided hunique offset hnext root]
    exact holdAnchor.mono (le_trans le_sup_left le_sup_left)
  have houtputAnchor :
      (faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        ).Reachable output.1 anchor :=
    hreachable.trans hanchorNext.symm
  refine ⟨selectedAnchor, holdAnchor, ?_⟩
  exact
    (sourceCorridorSerialInputFaceGraph_next_reachable_iff_faceStepCode
      realization hcubic hrotation htwoSided hunique offset hnext root output.1
        anchor output.2 hanchor).1 houtputAnchor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

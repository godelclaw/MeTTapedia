import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSupportedState

/-!
# Support-sensitive finite facial rebase steps

The finite facial rebase code already computes successor connectivity from
the predecessor component matrix and the two literal local factors.  A
component diagonal cannot say whether its coordinate is physically present:
reachability is reflexive at an isolated retained coordinate.  This module
adds the predecessor support bit and computes successor support by the exact
union law.

For a literal source slab, the computed bit is proved equivalent to support
membership in the actual successor regional face graph.  This is one finite
letter field of the reachable-state recurrence.  It does not yet construct
the complete five-coordinate transfer relation or a numerical threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

/-- One finite facial rebase step together with exact predecessor activity on
its at-most-eight occurrence coordinates. -/
structure BoundedSupportedSerialBoundaryRebaseFaceStepCode
    extends BoundedSerialBoundaryRebaseFaceStepCode where
  oldActive : Fin localCode.vertexCount.val → Bool

private def boundedSupportedSerialBoundaryRebaseFaceStepCodeEquiv :
    BoundedSupportedSerialBoundaryRebaseFaceStepCode ≃
      Σ code : BoundedSerialBoundaryRebaseFaceStepCode,
        Fin code.localCode.vertexCount.val → Bool where
  toFun code := ⟨code.toBoundedSerialBoundaryRebaseFaceStepCode, code.oldActive⟩
  invFun data :=
    { toBoundedSerialBoundaryRebaseFaceStepCode := data.1
      oldActive := data.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq BoundedSupportedSerialBoundaryRebaseFaceStepCode :=
  Classical.decEq _

noncomputable instance :
    Fintype BoundedSupportedSerialBoundaryRebaseFaceStepCode := by
  exact Fintype.ofEquiv _
    boundedSupportedSerialBoundaryRebaseFaceStepCodeEquiv.symm

/-- A coordinate is active after the rebase exactly when it was active in the
old prefix or is used by one of the two literal local factors. -/
noncomputable def boundedSupportedSerialBoundaryRebaseFaceOutputActive
    (code : BoundedSupportedSerialBoundaryRebaseFaceStepCode)
    (coordinate : Fin code.localCode.vertexCount.val) : Bool := by
  classical
  exact decide
    (code.oldActive coordinate = true ∨
      coordinate ∈ (code.localCode.graph false).support ∨
      coordinate ∈ (code.localCode.graph true).support)

@[simp]
theorem boundedSupportedSerialBoundaryRebaseFaceOutputActive_eq_true_iff
    (code : BoundedSupportedSerialBoundaryRebaseFaceStepCode)
    (coordinate : Fin code.localCode.vertexCount.val) :
    boundedSupportedSerialBoundaryRebaseFaceOutputActive code coordinate = true ↔
      code.oldActive coordinate = true ∨
        coordinate ∈ (code.localCode.graph false).support ∨
        coordinate ∈ (code.localCode.graph true).support := by
  classical
  simp [boundedSupportedSerialBoundaryRebaseFaceOutputActive]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceSupportedStepEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Cyclic positions and their literal darts agree on whether the regional
face graph uses that occurrence. -/
theorem faceRegionalAmbientPositionGraph_mem_support_iff_dartGraph
    (RS : RotationSystem V G.edgeSet) (root : RS.D)
    (region : Finset G.edgeSet)
    (position : Fin (RS.faceOrbit root).card) :
    position ∈ (faceRegionalAmbientPositionGraph RS root region).support ↔
      faceCycleDart RS root position ∈
        (faceRegionalDartGraph RS region).support := by
  rw [SimpleGraph.mem_support, SimpleGraph.mem_support]
  constructor
  · rintro ⟨neighbor, hadjacent⟩
    refine ⟨faceCycleDart RS root neighbor, ?_⟩
    have hinduced :=
      (faceRegionalAmbientPositionGraphIsoDartOrbit RS root region
        ).map_rel_iff.mpr hadjacent
    exact hinduced
  · rintro ⟨neighbor, hadjacent⟩
    have hcurrentOrbit :
        faceCycleDart RS root position ∈ RS.faceOrbit root :=
      faceCycleDart_mem RS root position
    have hcurrentFace :
        dartOrbitFace RS (faceCycleDart RS root position) =
          dartOrbitFace RS root :=
      (Quotient.sound ((RS.mem_faceOrbit).1 hcurrentOrbit)).symm
    have hneighborFace :
        dartOrbitFace RS neighbor = dartOrbitFace RS root :=
      (faceRegionalDartGraph_adj_dartOrbitFace_eq RS region
        hadjacent).symm.trans hcurrentFace
    have hneighborOrbit : neighbor ∈ RS.faceOrbit root := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root,
        mem_orbitFaceDarts_iff]
      exact hneighborFace
    rcases existsUnique_faceCycleDart_eq RS root neighbor hneighborOrbit with
      ⟨neighborPosition, hneighborPosition, _⟩
    refine ⟨neighborPosition, ?_⟩
    apply (faceRegionalAmbientPositionGraphIsoDartOrbit RS root region
      ).map_rel_iff.mp
    change
      (faceRegionalDartGraph RS region).Adj
        (faceCycleDart RS root position)
        (faceCycleDart RS root neighborPosition)
    simpa [hneighborPosition] using hadjacent

namespace SourceTrail

namespace AnnularEmbedding

/-- The finite local code also preserves support membership exactly. -/
theorem sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_mem_support_iff
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
    (factor : Bool)
    (position : {position // position ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root}) :
    carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root) position ∈
      ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).graph factor).support ↔
    position.1 ∈
      (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext root factor).support := by
  exact boundedCarrierGraphFamilyCode_mem_support_iff
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
      hcubic hrotation htwoSided hunique offset hnext root)
    8 0
    (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext root)
    (fun point => Fin.elim0 point)
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    factor
    (sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt_support_subset_switch
      realization hcubic hrotation htwoSided hunique offset hnext root factor)
    position

/-- Extract the finite support-sensitive rebase step from the literal old
prefix state and the exact local letter. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    BoundedSupportedSerialBoundaryRebaseFaceStepCode where
  toBoundedSerialBoundaryRebaseFaceStepCode :=
    sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root
  oldActive coordinate :=
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfaceActive
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate)

/-- The added predecessor activity bit is exactly support of the old regional
face graph on the corresponding switch position. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt_oldActive_iff
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
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldActive coordinate =
        true ↔
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
          hcubic hrotation htwoSided hunique offset hnext root)).symm
          coordinate).1 ∈
        (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).support := by
  change
    (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfaceActive
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate) =
      true ↔ _
  rw [sourceCorridorSerialBoundaryRebaseFaceStepCoordinate_oldActive_iff]
  rw [faceRegionalAmbientPositionGraph_mem_support_iff_dartGraph]
  rfl

/-- The finite output-activity calculation agrees exactly with support of the
literal successor regional face graph on every switch occurrence. -/
theorem sourceCorridorSerialBoundaryRebaseSupportedFaceOutputActive_iff
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
    (position : {position // position ∈
      sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root}) :
    boundedSupportedSerialBoundaryRebaseFaceOutputActive
        (sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext root)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root) position) =
          true ↔
      position.1 ∈
        (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialCutRegionAt realization hcubic hrotation
            htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
          ).support := by
  rw [boundedSupportedSerialBoundaryRebaseFaceOutputActive_eq_true_iff]
  change
    (sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root).oldActive
          (carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
              hcubic hrotation htwoSided hunique offset hnext root) position) =
        true ∨
      carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root) position ∈
        ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext root).graph false).support ∨
      carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
            hcubic hrotation htwoSided hunique offset hnext root) position ∈
        ((sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext root).graph true).support ↔ _
  rw [sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt_oldActive_iff]
  rw [sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_mem_support_iff
    realization hcubic hrotation htwoSided hunique offset hnext root false]
  rw [sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt_mem_support_iff
    realization hcubic hrotation htwoSided hunique offset hnext root true]
  rw [sourceCorridorSerialInputFaceGraph_next_eq_rebase_three_factor
    realization hcubic hrotation htwoSided hunique offset hnext root]
  simp [sourceCorridorSerialBoundaryRebaseFaceLocalGraphAt,
    SimpleGraph.mem_support]
  aesop

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

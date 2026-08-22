import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSuccessorCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceSupportedStep

/-!
# Capped predecessor face components for a serial boundary rebase

The support-sensitive rebase state records which finite switch occurrences
are present and which belong to one old-prefix component.  Capped face
progress also needs the weight of that component.  This file adds exactly that
finite coordinate: for every switch occurrence, the cardinality at most five
of the supported old-prefix component which contains it.

The cap is zero at an inactive occurrence and is constant on every stored old
component.  Forgetting it recovers the preceding support-sensitive state by
definition.  This is the predecessor weight needed by the successor cap law;
it does not yet deduplicate several old components joined by the local rebase,
construct the full Cell/rebase recurrence, or measure reachable closure.
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
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

/-- A support-sensitive finite facial rebase state together with the capped
weight of the predecessor component at every switch coordinate. -/
structure BoundedCappedSerialBoundaryRebaseFaceStepCode
    extends BoundedSupportedSerialBoundaryRebaseFaceStepCode where
  oldComponentCap : Fin localCode.vertexCount.val → Fin 6

private def boundedCappedSerialBoundaryRebaseFaceStepCodeEquiv :
    BoundedCappedSerialBoundaryRebaseFaceStepCode ≃
      Σ code : BoundedSupportedSerialBoundaryRebaseFaceStepCode,
        Fin code.localCode.vertexCount.val → Fin 6 where
  toFun code :=
    ⟨code.toBoundedSupportedSerialBoundaryRebaseFaceStepCode,
      code.oldComponentCap⟩
  invFun data :=
    { toBoundedSupportedSerialBoundaryRebaseFaceStepCode := data.1
      oldComponentCap := data.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq BoundedCappedSerialBoundaryRebaseFaceStepCode :=
  Classical.decEq _

noncomputable instance :
    Fintype BoundedCappedSerialBoundaryRebaseFaceStepCode := by
  exact Fintype.ofEquiv _
    boundedCappedSerialBoundaryRebaseFaceStepCodeEquiv.symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseFaceCappedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The supported part of the old-prefix facial component meeting one finite
switch coordinate.  Filtering by support makes this empty at an inactive
coordinate despite reflexivity of graph reachability. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt
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
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val) :
    Finset
      (Fin (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) := by
  classical
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let graph := faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let start := ((carrierCoordinate carrier).symm coordinate).1
  exact Finset.univ.filter fun position =>
    position ∈ graph.support ∧ graph.Reachable start position

@[simp]
theorem mem_sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_iff
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
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (position : Fin
      (embedded.cellulation.rotation.toRotationSystem.faceOrbit root).card) :
    position ∈
        sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate ↔
      position ∈
          (faceRegionalAmbientPositionGraph
            embedded.cellulation.rotation.toRotationSystem root
            (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
              htwoSided hunique offset).regionEdges).support ∧
        (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges).Reachable
          (((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
              hcubic hrotation htwoSided hunique offset hnext root)).symm
                coordinate).1)
          position := by
  classical
  simp [sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt]

/-- Extract the predecessor component weights together with the already exact
support-sensitive finite rebase state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
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
    BoundedCappedSerialBoundaryRebaseFaceStepCode where
  toBoundedSupportedSerialBoundaryRebaseFaceStepCode :=
    sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root
  oldComponentCap coordinate :=
    ⟨min
      (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate).card 5,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Forgetting predecessor component weights recovers the existing
support-sensitive rebase step definitionally. -/
theorem sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_toSupported
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
    (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root
        ).toBoundedSupportedSerialBoundaryRebaseFaceStepCode =
      sourceCorridorSerialBoundaryRebaseSupportedFaceStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext root :=
  rfl

/-- The stored predecessor weight is exactly the cap at five of its literal
supported old-prefix component. -/
theorem sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldComponentCap
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
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val) :
    ((sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root).oldComponentCap
        coordinate).val =
      min
        (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate).card 5 :=
  rfl

/-- Equal predecessor-component coordinates carry equal capped weights. -/
theorem sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_oldComponentCap_eq
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
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val)
    (hsame :
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent left right =
          true) :
    (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponentCap left =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponentCap right := by
  let graph := faceRegionalAmbientPositionGraph
    embedded.cellulation.rotation.toRotationSystem root
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  have hreachable : graph.Reachable
      ((carrierCoordinate carrier).symm left).1
      ((carrierCoordinate carrier).symm right).1 :=
    (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_eq_true_iff
      realization hcubic hrotation htwoSided hunique offset hnext root left
        right).1 hsame
  apply Fin.ext
  change min
      (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root left).card 5 =
    min
      (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root right).card 5
  congr 2
  ext position
  simp only [mem_sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_iff]
  constructor
  · rintro ⟨hsupport, hleft⟩
    exact ⟨hsupport, hreachable.symm.trans hleft⟩
  · rintro ⟨hsupport, hright⟩
    exact ⟨hsupport, hreachable.trans hright⟩

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

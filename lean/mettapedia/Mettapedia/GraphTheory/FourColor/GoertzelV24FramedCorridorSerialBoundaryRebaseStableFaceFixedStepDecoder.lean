import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedState

/-!
# A fully fixed finite decoder for one capped facial rebase

The predecessor facial state now has one common carrier: sixteen occurrence
slots and four boundary-fragment slots.  This file feeds that state to the
graph-free capped decoder and proves agreement with the literal graph receipt.

Consequently the accumulated predecessor relation, support activity, literal
presence, and component cap used by one facial rebase are all reconstructed
from fixed finite data.  The heterogeneous local face code remains a separate
letter, as required by the source.

This is not yet the successor-state recurrence or a reachable-closure count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceFixedStepDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Decode the literal per-face rebase receipt from one fully fixed
predecessor state and the literal local two-factor face code. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
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
    BoundedCappedSerialBoundaryRebaseFaceStepCode :=
  boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
    (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    (fun coordinate =>
      sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate))

/-- The fully fixed decoder reconstructs every predecessor-component bit of
the literal per-face receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldComponent_eq_true_iff_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).oldComponent left right = true ↔
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent
          left right = true := by
  let leftOccurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root left
  let rightOccurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root right
  rw [show
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).oldComponent left right = true ↔
      GoertzelV24SimpleGraphSupportedPortResidualFactorContraction.SupportedPortResidualFactoredReachability
        (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext
            ).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Fin 4 => leftPort = rightPort)
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext leftOccurrence)
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext rightOccurrence) by
      exact boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable_oldComponent_eq_true_iff
        _ _ _ _ left right]
  rw [sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt_factored_iff]
  rw [← boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable_oldComponent_eq_true_iff
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    (fun leftPort rightPort => leftPort = rightPort)
    (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    (fun coordinate =>
      sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate))
    left right]
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldComponent
        left right = true ↔ _
  exact
    sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldComponent_eq_true_iff_literal
      realization hcubic hrotation htwoSided hunique offset hnext root left right

/-- The fully fixed decoder reconstructs predecessor activity exactly. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldActive_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).oldActive coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldActive coordinate := by
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldActive coordinate = _
  exact
    sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldActive_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext root coordinate

/-- The fully fixed decoder reconstructs literal predecessor presence exactly. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldPresent_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).oldPresent coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldPresent coordinate := by
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldPresent coordinate = _
  exact
    sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldPresent_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext root coordinate

/-- The fully fixed decoder reconstructs the predecessor cap at five exactly. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldComponentCap_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).oldComponentCap coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponentCap
          coordinate := by
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldComponentCap
        coordinate = _
  exact
    sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldComponentCap_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext root coordinate

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

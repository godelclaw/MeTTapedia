import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedStepDecoder

/-!
# Exactness of the fixed capped facial rebase step

The fixed predecessor state and the literal local face code already decode
each field of the accumulated facial rebase step.  This file packages those
fieldwise results as equality of the complete finite step code.

This equality is the substitution interface for the existing finite successor
face receipt.  It does not compute the successor fixed residual state or a
reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

private theorem boundedSerialBoundaryRebaseFaceStepCode_eq_of_fields
    (left right : BoundedSerialBoundaryRebaseFaceStepCode)
    (hlocal : left.localCode = right.localCode)
    (hold : HEq left.oldComponent right.oldComponent) : left = right := by
  cases left with
  | mk leftLocal leftOld =>
    cases right with
    | mk rightLocal rightOld =>
      dsimp only at hlocal hold
      cases hlocal
      cases hold
      rfl

private theorem boundedSupportedSerialBoundaryRebaseFaceStepCode_eq_of_fields
    (left right : BoundedSupportedSerialBoundaryRebaseFaceStepCode)
    (hbase : left.toBoundedSerialBoundaryRebaseFaceStepCode =
      right.toBoundedSerialBoundaryRebaseFaceStepCode)
    (hactive : HEq left.oldActive right.oldActive) : left = right := by
  cases left with
  | mk leftBase leftActive =>
    cases right with
    | mk rightBase rightActive =>
      dsimp only at hbase hactive
      cases hbase
      cases hactive
      rfl

private theorem boundedCappedSerialBoundaryRebaseFaceStepCode_eq_of_fields
    (left right : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (hbase : left.toBoundedSupportedSerialBoundaryRebaseFaceStepCode =
      right.toBoundedSupportedSerialBoundaryRebaseFaceStepCode)
    (hpresent : HEq left.oldPresent right.oldPresent)
    (hcap : HEq left.oldComponentCap right.oldComponentCap) : left = right := by
  cases left with
  | mk leftBase leftPresent leftCap =>
    cases right with
    | mk rightBase rightPresent rightCap =>
      dsimp only at hbase hpresent hcap
      cases hbase
      cases hpresent
      cases hcap
      rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceFixedStepExactEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The graph-free decoder from the fixed predecessor state is exactly the
literal capped facial step, as a complete finite structure. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_eq_literal
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
    sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext root =
      sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root := by
  let fixed :=
    sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
  let literal := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  have hstep : fixed.toBoundedSerialBoundaryRebaseFaceStepCode =
      literal.toBoundedSerialBoundaryRebaseFaceStepCode := by
    apply boundedSerialBoundaryRebaseFaceStepCode_eq_of_fields
    · rfl
    · apply heq_of_eq
      funext left right
      apply Bool.eq_iff_iff.mpr
      exact
        sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldComponent_eq_true_iff_literal
          realization hcubic hrotation htwoSided hunique offset hnext root
            left right
  have hsupported : fixed.toBoundedSupportedSerialBoundaryRebaseFaceStepCode =
      literal.toBoundedSupportedSerialBoundaryRebaseFaceStepCode := by
    apply boundedSupportedSerialBoundaryRebaseFaceStepCode_eq_of_fields
    · exact hstep
    · apply heq_of_eq
      funext coordinate
      exact
        sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldActive_eq_literal
          realization hcubic hrotation htwoSided hunique offset hnext root
            coordinate
  apply boundedCappedSerialBoundaryRebaseFaceStepCode_eq_of_fields
  · exact hsupported
  · apply heq_of_eq
    funext coordinate
    exact
      sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldPresent_eq_literal
        realization hcubic hrotation htwoSided hunique offset hnext root
          coordinate
  · apply heq_of_eq
    funext coordinate
    exact
      sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_oldComponentCap_eq_literal
        realization hcubic hrotation htwoSided hunique offset hnext root
          coordinate

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

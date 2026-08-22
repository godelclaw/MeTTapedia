import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceFixedStepExact
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteFaceReceipt

/-!
# A finite successor-face receipt from fixed predecessor state

The existing successor-face receipt stored an accumulated-prefix matrix and
cap inside every output row.  The fixed capped state now reconstructs those
fields.  This file substitutes that reconstruction into every row and proves
that the complete continuation, port-incidence, and capped-progress receipt is
unchanged.

The remaining receipt fields are literal local data of the heterogeneous
Cell--rebase letter.  No ambient prefix graph is consulted by the generic row
decoder below.  Updating the fixed residual state for the following letter and
measuring reachable closure remain separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationAllFaceCutProfile
open SimpleGraph
open SimpleGraphDartRotation

/-- Build one successor-face row from a capped predecessor step already
decoded from fixed state and the remaining finite local row data. -/
noncomputable def boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep
    (cappedStep : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (output : Fin cappedStep.localCode.vertexCount.val)
    (portPositions : Fin 2 →
      Option (Fin cappedStep.localCode.vertexCount.val))
    (semantic : cappedStep.IsComponentSemantic) :
    BoundedSerialBoundaryRebaseFiniteFaceRowCode :=
  { step := cappedStep.toBoundedSerialBoundaryRebaseFaceStepCode
    output := output
    portPositions := portPositions
    oldCap :=
      ⟨cappedStep.oldComponentCapSumAt semantic output,
        Nat.lt_succ_of_le
          (cappedStep.oldComponentCapSumAt_le_five semantic output)⟩ }

/-- Equality of capped predecessor steps transports the complete decoded row,
including its dependent output and port-position coordinates. -/
theorem boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep_congr
    (left right : BoundedCappedSerialBoundaryRebaseFaceStepCode)
    (hstep : left = right)
    (leftOutput : Fin left.localCode.vertexCount.val)
    (rightOutput : Fin right.localCode.vertexCount.val)
    (houtput : HEq leftOutput rightOutput)
    (leftPorts : Fin 2 → Option (Fin left.localCode.vertexCount.val))
    (rightPorts : Fin 2 → Option (Fin right.localCode.vertexCount.val))
    (hports : HEq leftPorts rightPorts)
    (leftSemantic : left.IsComponentSemantic)
    (rightSemantic : right.IsComponentSemantic) :
    boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep left leftOutput
        leftPorts leftSemantic =
      boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep right rightOutput
        rightPorts rightSemantic := by
  cases hstep
  cases houtput
  cases hports
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceFixedReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The fixed decoder inherits the literal component-partition laws. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_isComponentSemantic
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
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
        ).IsComponentSemantic := by
  rw [sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_eq_literal]
  exact
    sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root

/-- One literal successor-face row with its predecessor contribution decoded
from the fully fixed state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceRowCodeAt
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
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    BoundedSerialBoundaryRebaseFiniteFaceRowCode := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let cappedStep :=
    sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin cappedStep.localCode.vertexCount.val :=
    carrierCoordinate carrier
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
  exact boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep cappedStep output
    (sourceCorridorSerialBoundaryRebaseFacePortPositionCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_isComponentSemantic
      realization hcubic hrotation htwoSided hunique offset hnext root)

/-- Replacing the accumulated predecessor data by its fixed-state decoder
leaves one complete successor-face row unchanged. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceRowCodeAt_eq_literal
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
    (fragment : SourceCorridorSerialBoundaryRebaseSuccessorFacePortAt
      realization hcubic hrotation htwoSided hunique offset hnext) :
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceRowCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment =
      sourceCorridorSerialBoundaryRebaseFiniteFaceRowCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext fragment := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  let root := orbitFaceRoot RS (data.fragmentFace fragment)
  let fixed :=
    sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext root
  let literal := sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let output : Fin fixed.localCode.vertexCount.val :=
    carrierCoordinate
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt realization
        hcubic hrotation htwoSided hunique offset hnext root)
      (sourceCorridorSerialBoundaryRebaseSuccessorFacePositionAt realization
        hcubic hrotation htwoSided hunique offset hnext fragment)
  let ports : Fin 2 → Option (Fin fixed.localCode.vertexCount.val) :=
    sourceCorridorSerialBoundaryRebaseFacePortPositionCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root
  have hstep : fixed = literal :=
    sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceStepCodeAt_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext root
  change boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep fixed output
      ports _ =
    boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep literal output
      ports _
  exact boundedSerialBoundaryRebaseFiniteFaceRowCodeOfCappedStep_congr
    fixed literal hstep output output (HEq.rfl) ports ports (HEq.rfl) _ _

/-- The complete successor-face receipt with every accumulated predecessor row
decoded from the fixed state. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceReceiptCodeAt
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialBoundaryRebaseFiniteFaceReceiptCode
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).faceFragmentCount.val :=
  let literal := sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext color hcolor
  { continuation := literal.continuation
    row := fun fragment =>
      sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceRowCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext fragment
    localCaps := literal.localCaps }

/-- Fixed-state substitution preserves the complete finite successor-face
receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceReceiptCodeAt_eq_literal
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceReceiptCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcolor =
      sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color hcolor := by
  apply congrArg (fun rows =>
    { continuation :=
        (sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color hcolor
            ).continuation
      row := rows
      localCaps :=
        (sourceCorridorSerialBoundaryRebaseFiniteFaceReceiptCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color hcolor
            ).localCaps } :
      (Fin _ → BoundedSerialBoundaryRebaseFiniteFaceRowCode) →
        BoundedSerialBoundaryRebaseFiniteFaceReceiptCode _)
  funext fragment
  exact
    sourceCorridorSerialBoundaryRebaseStableFixedFiniteFaceRowCodeAt_eq_literal
      realization hcubic hrotation htwoSided hunique offset hnext fragment

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

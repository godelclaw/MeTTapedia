import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteOneCellSupport
import Mettapedia.GraphTheory.FourColor.GoertzelV24WidthTwoPortIncidenceCompression

/-!
# Source-shaped code for literal outgoing Cell profiles

The generic three-fragment width-two carrier still stores arbitrary face
equivalence and port-incidence tables.  A literal source Cell is much sharper.
Its outgoing cut has exactly the three stable roles `first`, `center`, and
`second`; distinct roles are distinct faces, and their port rows are fixed as
left-only, both, and right-only.

Consequently the moving data consists of only:

* one of the `24` color-compatible strand states;
* one of the `3!` orders of the three stable face roles;
* three positive capped face lengths, with `5` choices each.

This file packages that `18000`-element ABI and proves that every Tait-colored
literal source Cell produces one such code from the same joint receipt.  The
companion codec module proves that equality of these codes reconstructs
equality of the complete outgoing profile.  Neither module yet identifies the
cumulative-prefix word with the outgoing word, so no reachable-closure or
numerical `V0` is claimed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedCorridorThreeFacePrefixProfileRepeat
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WidthTwoBoundarySemanticCompression
open GoertzelV24WidthTwoPortIncidenceCompression
open SimpleGraph
open SimpleGraphDartRotation

/-- The finite moving data of a source-shaped outgoing Cell profile.  The
face-equivalence and port-incidence tables are fixed by `roleOrder`; they are
therefore not stored redundantly. -/
structure SourceOutgoingProfileCode where
  strand : WidthTwoStrandCode
  roleOrder : Fin 3 ≃ LocalLayerRightFaceRole
  faceLengthCap : LocalLayerRightFaceRole → PositiveFaceLengthCap
  deriving DecidableEq

private def sourceOutgoingProfileCodeEquiv :
    SourceOutgoingProfileCode ≃
      WidthTwoStrandCode ×
        (Fin 3 ≃ LocalLayerRightFaceRole) ×
        (LocalLayerRightFaceRole → PositiveFaceLengthCap) where
  toFun code := (code.strand, code.roleOrder, code.faceLengthCap)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype SourceOutgoingProfileCode :=
  Fintype.ofEquiv _ sourceOutgoingProfileCodeEquiv.symm

theorem card_finThreeEquivLocalLayerRightFaceRole :
    Fintype.card (Fin 3 ≃ LocalLayerRightFaceRole) = 6 := by
  decide

/-- Exact size of the source-shaped outgoing ABI:
`24` strand states times `3!` role orders times `5^3` cap assignments. -/
theorem card_sourceOutgoingProfileCode :
    Fintype.card SourceOutgoingProfileCode = 18000 := by
  rw [Fintype.card_congr sourceOutgoingProfileCodeEquiv]
  simp only [Fintype.card_prod, Fintype.card_fun]
  rw [card_widthTwoStrandCode,
    card_finThreeEquivLocalLayerRightFaceRole,
    card_localLayerRightFaceRole, card_positiveFaceLengthCap]
  norm_num

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance sourceOutgoingProfileCompressionEdgeSetDecidableEq :
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

/-- Every actual outgoing profile of a literal source Cell satisfies the
semantic laws used by the lossless width-two port-incidence codec. -/
theorem localLayerFiniteOutputProfile_isPortIncidenceSemantic
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedIsPortIncidenceSemantic
      (aligned.localLayerFiniteOutputProfile color hcolor) := by
  unfold localLayerFiniteOutputProfile
  unfold narrowFaceFragmentBound
  unfold SourceConsecutiveSlabInterface.localLayerRightPrefixBoundedProfile
  unfold regionalBoundaryBoundedProfile
  exact regionalBoundaryProfile_isPortIncidenceSemantic
    aligned.toInterface.localLayerRightPrefixRegion
    aligned.toInterface.nextLocalLayerPrefixCrossing
    aligned.toInterface.nextLocalLayerPrefixCrossing_mem_prefixEdgeRegion
    color hcolor

/-- Extract the compact outgoing ABI from an explicit joint one-Cell witness.
Separating the witness from the existential receipt keeps later codec proofs
independent of the proof term chosen for the dependent face count. -/
noncomputable def sourceOutgoingProfileCodeOfWitness
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (semantic : BoundedIsPortIncidenceSemantic output)
    (code : LocalLayerFiniteOneCellCode
      (widenFaceFragmentBoundThreeToFour incoming)
      (widenFaceFragmentBoundThreeToFour output))
    (hcount : output.faceFragmentCount.val = 3) :
    SourceOutgoingProfileCode :=
  {
    strand := (compressPortIncidenceBounded output semantic).profile.strand
    roleOrder := (Equiv.cast (congrArg Fin hcount)).symm.trans
      code.roleIndex.symm
    faceLengthCap := fun role =>
      (compressPortIncidenceBounded output semantic).profile.faceLengthCap
        (code.roleIndex role)
  }

/-- Extract the compact outgoing ABI from a complete joint one-Cell receipt.
The receipt fixes the omitted face relation and port-incidence tables. -/
noncomputable def sourceOutgoingProfileCodeOfReceipt
    (incoming : BoundedCorridorCutProfile 2 1 3)
    (output : BoundedCorridorCutProfile 2 0 3)
    (semantic : BoundedIsPortIncidenceSemantic output)
    (receipt : LocalLayerFiniteOneCellReceiptThree incoming output) :
    SourceOutgoingProfileCode :=
  sourceOutgoingProfileCodeOfWitness incoming output semantic
    (Classical.choose receipt) (Classical.choose_spec receipt).1

/-- Every Tait-colored literal source Cell produces one element of the exact
`18000`-element outgoing ABI, with all data extracted from the same coloring
and the same joint receipt. -/
noncomputable def sourceOutgoingProfileCodeOfTait
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcolor : embedded.cellulation.rotation.toRotationSystem
      |>.IsTaitEdgeColoring color) :
    SourceOutgoingProfileCode :=
  sourceOutgoingProfileCodeOfReceipt
    (aligned.localLayerFiniteInputProfile color
      (fun step => hcolor
        (aligned.toInterface.localLayerPrefixCrossing step)))
    (aligned.localLayerFiniteOutputProfile color
      (fun step => hcolor
        (aligned.toInterface.nextLocalLayerPrefixCrossing step)))
    (aligned.localLayerFiniteOutputProfile_isPortIncidenceSemantic color
      (fun step => hcolor
        (aligned.toInterface.nextLocalLayerPrefixCrossing step)))
    (aligned.exists_localLayerFiniteOneCellReceipt_of_tait
      hcubic hrotation color hcolor)

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

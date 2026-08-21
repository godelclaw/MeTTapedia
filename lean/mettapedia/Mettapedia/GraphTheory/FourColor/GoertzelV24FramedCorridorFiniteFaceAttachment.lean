import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixFactorSubsingleton

/-!
# A finite attachment alphabet for one source Cell

After the old-prefix factor set is proved subsingleton, one outgoing face has
only three possible relationships to the cumulative prefix:

* it is fresh on the Cell side;
* it continues one indexed incoming boundary fragment; or
* it is the fixed shared-rung residue.

`CellFaceAttachmentCode n` is this graph-free finite alphabet for an input
with `n` boundary fragments.  The coverage theorem below encodes every actual
outgoing fragment in it while retaining exact ambient-face and edge-support
data.  It is a per-fragment code; padding all output fragments into the proved
three-coordinate carrier and combining their cap equations remains the next
step toward the complete five-coordinate transition.
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
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorFiniteFaceAttachmentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The graph-free old-prefix attachment of one outgoing face fragment. -/
inductive CellFaceAttachmentCode (inputFaceCount : Nat) where
  | fresh
  | continues (input : Fin inputFaceCount)
  | sharedRung
  deriving DecidableEq, Fintype

/-- Concrete nested-option representation of the three attachment cases. -/
def cellFaceAttachmentCodeEquiv (inputFaceCount : Nat) :
    CellFaceAttachmentCode inputFaceCount ≃ Option (Option (Fin inputFaceCount)) where
  toFun
    | .fresh => none
    | .continues input => some (some input)
    | .sharedRung => some none
  invFun
    | none => .fresh
    | some (some input) => .continues input
    | some none => .sharedRung
  left_inv code := by cases code <;> rfl
  right_inv code := by rcases code with _ | (_ | _) <;> rfl

/-- The per-fragment alphabet has exactly two local cases in addition to one
continuation case for each incoming face coordinate. -/
@[simp]
theorem card_cellFaceAttachmentCode (inputFaceCount : Nat) :
    Fintype.card (CellFaceAttachmentCode inputFaceCount) = inputFaceCount + 2 := by
  rw [Fintype.card_congr (cellFaceAttachmentCodeEquiv inputFaceCount)]
  simp

/-- The old-prefix capped contribution carried by one attachment code.  A
continued fragment reads the corresponding incoming cap; a fresh fragment
contributes nothing; and the shared-rung residue contributes its proved
single occurrence. -/
def CellFaceAttachmentCode.oldCap {inputFaceCount : Nat}
    (inputCap : Fin inputFaceCount → Fin 6) :
    CellFaceAttachmentCode inputFaceCount → Nat
  | .fresh => 0
  | .continues input => (inputCap input).val
  | .sharedRung => 1

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

/-- Exact interpretation of a finite attachment code for one actual outgoing
fragment.  The continued case retains both face identity and edge support;
the residue case retains its literal singleton support. -/
def LocalLayerFaceAttachmentRealizes
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    CellFaceAttachmentCode (Fintype.card aligned.LocalLayerLeftBoundaryFragment) →
      Prop
  | .fresh => aligned.localLayerLeftFactorFragments fragment = ∅
  | .continues input =>
      ∃ factor : aligned.LocalLayerLeftFactor fragment,
        aligned.localLayerLeftFactorFragments fragment = {factor} ∧
          (aligned.localLayerLeftBoundaryFragmentAt input).1.1 = fragment.1.1 ∧
          aligned.localLayerLeftBoundaryFragmentEdgesAt input =
            aligned.localLayerLeftFactorEdges fragment factor
  | .sharedRung =>
      ∃ factor : aligned.LocalLayerLeftFactor fragment,
        aligned.localLayerLeftFactorFragments fragment = {factor} ∧
          aligned.LocalLayerLeftFactorContainsSharedRung fragment factor ∧
          aligned.localLayerLeftFactorEdges fragment factor =
            {aligned.toInterface.localLayerSharedRungEdge}

/-- Every literal outgoing fragment has a graph-free finite attachment code.
This is coverage, not a postulated quotient: all dependent factors are
consumed by the singleton theorem and the existing face/support resolution. -/
theorem exists_localLayerFaceAttachmentCode
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment) :
    ∃ code : CellFaceAttachmentCode
        (Fintype.card aligned.LocalLayerLeftBoundaryFragment),
      aligned.LocalLayerFaceAttachmentRealizes fragment code := by
  classical
  let factors := aligned.localLayerLeftFactorFragments fragment
  by_cases hempty : factors = ∅
  · exact ⟨.fresh, hempty⟩
  · have hnonempty : factors.Nonempty := Finset.nonempty_iff_ne_empty.2 hempty
    rcases hnonempty with ⟨factor, hfactor⟩
    have hcard := aligned.localLayerLeftFactorFragments_card_le_one
      hcubic hrotation fragment
    have huniqueFactor : ∀ other ∈ factors, other = factor := by
      intro other hother
      exact (Finset.card_le_one_iff.1 hcard) hother hfactor
    have hsingleton : factors = {factor} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hfactor, huniqueFactor⟩
    rcases aligned
        |>.localLayerLeftFactorHasProfileFragmentCoordinate_or_containsSharedRung
          hcubic hrotation fragment factor hfactor with
      hcoordinate | hshared
    · rcases hcoordinate with ⟨input, hface, hedges⟩
      refine ⟨.continues input, ?_⟩
      exact ⟨factor, hsingleton, hface, hedges⟩
    · refine ⟨.sharedRung, ?_⟩
      exact ⟨factor, hsingleton, hshared,
        aligned.localLayerLeftFactorEdges_eq_singleton_of_containsSharedRung
          fragment factor hshared⟩

/-- A realized finite attachment code computes the complete old-prefix term
in the exact one-Cell face-cap update.  This removes the last dependent factor
carrier from that term; no face-count estimate or arbitrary assignment is
used. -/
theorem localLayerFactorFragmentCapSum_eq_oldCap_of_faceAttachment
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (fragment : aligned.toInterface.LocalLayerComposedBoundaryFragment)
    (code : CellFaceAttachmentCode
      (Fintype.card aligned.LocalLayerLeftBoundaryFragment))
    (hrealizes : aligned.LocalLayerFaceAttachmentRealizes fragment code) :
    aligned.toInterface.localLayerFactorFragmentCapSum
          aligned.toInterface.localLayerLeftPrefixRegion fragment =
      min (code.oldCap
        ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
          color hleftColor).profile.faceLengthCap)) 5 := by
  classical
  cases code with
  | fresh =>
      change min
        (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
          aligned.localLayerLeftFactorPositionCap fragment factor) 5 = _
      rw [hrealizes]
      simp [CellFaceAttachmentCode.oldCap]
  | continues input =>
      rcases hrealizes with ⟨factor, hsingleton, _hface, hedges⟩
      have hcap :=
        aligned
          |>.localLayerLeftPrefixProfileFaceLengthCap_eq_factorPositionCap_of_support
            color hleftColor fragment factor input hedges
      change min
        (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
          aligned.localLayerLeftFactorPositionCap fragment factor) 5 = _
      rw [hsingleton]
      simp [CellFaceAttachmentCode.oldCap, ← hcap]
  | sharedRung =>
      rcases hrealizes with ⟨factor, hsingleton, hshared, _hedges⟩
      have hcap :=
        aligned.localLayerLeftFactorPositionCap_eq_one_of_containsSharedRung
          fragment factor hshared
      change min
        (∑ factor ∈ aligned.localLayerLeftFactorFragments fragment,
          aligned.localLayerLeftFactorPositionCap fragment factor) 5 = _
      rw [hsingleton]
      simp [CellFaceAttachmentCode.oldCap, hcap]

/-- Every actual outgoing coordinate admits a finite attachment code which
also computes its exact capped face-length update.  This is the face-progress
half of the finite one-Cell semantic letter; coloring, tracked connectivity,
and the remaining outgoing-coordinate padding are separate fields. -/
theorem exists_localLayerFaceAttachmentCode_with_cap
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
    ∃ code : CellFaceAttachmentCode
        (Fintype.card aligned.LocalLayerLeftBoundaryFragment),
      aligned.LocalLayerFaceAttachmentRealizes
          (aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index)
          code ∧
        (((aligned.toInterface.localLayerRightPrefixBoundedProfile
              color hrightColor).profile.faceLengthCap index).val) =
          min
            (min (code.oldCap
                ((aligned.toInterface.localLayerLeftPrefixBoundedProfile
                  color hleftColor).profile.faceLengthCap)) 5 +
              (if (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index).1.1 =
                    aligned.toInterface.nextCenterLayerFace.1 then 5 else 1) -
              (if (aligned.toInterface
                    |>.localLayerRightPrefixBoundaryFragmentAt index).1.1 =
                    aligned.toInterface.nextCenterLayerFace.1 then 1 else 0))
            5 := by
  let fragment :=
    aligned.toInterface.localLayerRightPrefixBoundaryFragmentAt index
  rcases aligned.exists_localLayerFaceAttachmentCode hcubic hrotation fragment with
    ⟨code, hrealizes⟩
  refine ⟨code, hrealizes, ?_⟩
  rw [aligned.localLayerRightPrefixBoundedProfile_faceLengthCap_eq_cellUpdate,
    aligned.localLayerFactorFragmentCapSum_eq_oldCap_of_faceAttachment
      color hleftColor fragment code hrealizes]

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

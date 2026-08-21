import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorFiniteRightFaceUpdate

/-!
# A graph-free face-update receipt for one literal source Cell

The three outgoing faces already have the stable semantic roles `first`,
`center`, and `second`.  This module attaches to each role the previously
proved finite old-prefix receipt: `fresh`, `continues i`, or `sharedRung`.
The resulting table is graph-free and computes the exact capped face-progress
coordinate of the actual one-Cell update.

This is the face half of the source letter.  It does not yet combine the table
with the finite tracked-connectivity update or claim that different literal
Cells have the same semantic relation.
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

local instance framedCorridorFiniteFaceUpdateCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A finite face-update table assigns one old-prefix attachment receipt to
each of the three semantic outgoing roles. -/
abbrev LocalLayerFiniteFaceUpdateCode (inputFaceCount : Nat) :=
  LocalLayerRightFaceRole → CellFaceAttachmentCode inputFaceCount

/-- The finite face-update alphabet has `(n+2)^3` tables for an input with
`n` face coordinates. -/
theorem card_localLayerFiniteFaceUpdateCode (inputFaceCount : Nat) :
    Fintype.card (LocalLayerFiniteFaceUpdateCode inputFaceCount) =
      (inputFaceCount + 2) ^ 3 := by
  rw [Fintype.card_fun, card_localLayerRightFaceRole,
    card_cellFaceAttachmentCode]

/-- At the proved three-face input bound, the complete face-update receipt
alphabet has at most `5^3 = 125` elements. -/
theorem card_localLayerFiniteFaceUpdateCode_le_125
    (inputFaceCount : Nat) (hcount : inputFaceCount ≤ 3) :
    Fintype.card (LocalLayerFiniteFaceUpdateCode inputFaceCount) ≤ 125 := by
  rw [card_localLayerFiniteFaceUpdateCode]
  calc
    (inputFaceCount + 2) ^ 3 ≤ (3 + 2) ^ 3 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hcount 2) 3
    _ = 125 := by norm_num

/-- Literal Cell-side length contributed by an outgoing role before overlap
with the old prefix is removed. -/
def LocalLayerRightFaceRole.cellCap : LocalLayerRightFaceRole → Nat
  | .center => 5
  | .first | .second => 1

/-- The centre role shares one boundary edge with the old prefix; either
outer role is a fresh one-edge contribution on the Cell side. -/
def LocalLayerRightFaceRole.overlapCap : LocalLayerRightFaceRole → Nat
  | .center => 1
  | .first | .second => 0

/-- Exact capped output value computed from one attachment receipt and its
semantic output role. -/
def CellFaceAttachmentCode.updatedCap {inputFaceCount : Nat}
    (code : CellFaceAttachmentCode inputFaceCount)
    (inputCap : Fin inputFaceCount → Fin 6)
    (role : LocalLayerRightFaceRole) : Nat :=
  min (min (code.oldCap inputCap) 5 + role.cellCap - role.overlapCap) 5

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

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

/-- Canonical finite index of one semantic outgoing face role. -/
noncomputable def localLayerRightFaceRoleIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion)) :=
  Fintype.equivFin _ (interface.localLayerRightFaceRoleEquivBoundaryFragment role)

/-- Looking up a role index recovers its semantic boundary fragment. -/
theorem boundaryRegionalFragmentAt_localLayerRightFaceRoleIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    boundaryRegionalFragmentAt
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion
        (interface.localLayerRightFaceRoleIndex role) =
      interface.localLayerRightFaceRoleEquivBoundaryFragment role := by
  exact (Fintype.equivFin _).symm_apply_apply _

/-- The literal prefix-plus-Cell fragment named by a semantic output role. -/
noncomputable def localLayerRightComposedFragmentOfRole
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    interface.LocalLayerComposedBoundaryFragment :=
  interface.localLayerRightPrefixBoundaryFragmentEquiv
    (interface.localLayerRightFaceRoleEquivBoundaryFragment role)

/-- Role lookup through the graph-cut profile agrees with the literal
prefix-plus-Cell fragment of that role. -/
theorem localLayerRightPrefixBoundaryFragmentAt_roleIndex
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    interface.localLayerRightPrefixBoundaryFragmentAt
        (interface.localLayerRightFaceRoleIndex role) =
      interface.localLayerRightComposedFragmentOfRole role := by
  simp only [localLayerRightPrefixBoundaryFragmentAt,
    localLayerRightComposedFragmentOfRole,
    interface.boundaryRegionalFragmentAt_localLayerRightFaceRoleIndex]

/-- Reading the role back from its semantic fragment is exact. -/
theorem localLayerRightBoundaryFragmentRole_roleEquiv
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    interface.localLayerRightBoundaryFragmentRole
        (interface.localLayerRightFaceRoleEquivBoundaryFragment role) = role := by
  simp [localLayerRightBoundaryFragmentRole,
    localLayerRightFaceRoleEquivBoundaryFragment,
    localLayerRightBoundaryFragmentEquivCutIncidentFace]

/-- The composed fragment indexed by a role names exactly that role's literal
ambient face. -/
theorem localLayerRightComposedFragmentOfRole_face
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    (interface.localLayerRightComposedFragmentOfRole role).1.1 =
      interface.localLayerRightFaceOfRole role := by
  let fragment := interface.localLayerRightFaceRoleEquivBoundaryFragment role
  have hcast := congrArg (fun face => face.1)
    (interface.localLayerRightPrefixBoundaryFragmentEquiv_face fragment)
  have hroleFace :=
    interface.localLayerRightFaceOfRole_boundaryFragmentRole fragment
  rw [interface.localLayerRightBoundaryFragmentRole_roleEquiv role] at hroleFace
  exact hcast.trans hroleFace.symm

/-- The centre role is exactly the role whose Cell contribution is the whole
new hexagonal face. -/
theorem localLayerRightComposedFragmentOfRole_face_eq_nextCenter_iff
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) (role : LocalLayerRightFaceRole) :
    (interface.localLayerRightComposedFragmentOfRole role).1.1 =
        interface.nextCenterLayerFace.1 ↔
      role = .center := by
  rw [interface.localLayerRightComposedFragmentOfRole_face role]
  have hfirst : interface.firstLayerFace.1 ≠
      interface.nextCenterLayerFace.1 := by
    intro heq
    exact interface.firstLayerFace_ne_nextCenterLayerFace (Subtype.ext heq)
  have hsecond : interface.secondLayerFace.1 ≠
      interface.nextCenterLayerFace.1 := by
    intro heq
    exact interface.secondLayerFace_ne_nextCenterLayerFace (Subtype.ext heq)
  cases role <;> simp [localLayerRightFaceOfRole, hfirst, hsecond]

end SourceConsecutiveSlabInterface

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

/-- Every literal source Cell produces one finite three-role attachment table,
and that table computes all three outgoing capped face-progress values. -/
theorem exists_localLayerFiniteFaceUpdateCode
    (aligned : SourceCornerAlignedSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (color : G.edgeSet → Color)
    (hleftColor : ∀ step,
      color (aligned.toInterface.localLayerPrefixCrossing step) ≠ 0)
    (hrightColor : ∀ step,
      color (aligned.toInterface.nextLocalLayerPrefixCrossing step) ≠ 0) :
    ∃ update : LocalLayerFiniteFaceUpdateCode
        (Fintype.card aligned.LocalLayerLeftBoundaryFragment),
      ∀ role : LocalLayerRightFaceRole,
        aligned.LocalLayerFaceAttachmentRealizes
            (aligned.toInterface.localLayerRightComposedFragmentOfRole role)
            (update role) ∧
          (((aligned.toInterface.localLayerRightPrefixBoundedProfile
              color hrightColor).profile.faceLengthCap
                (aligned.toInterface.localLayerRightFaceRoleIndex role)).val) =
            (update role).updatedCap
              ((aligned.localLayerLeftPrefixSharedRungBoundedProfile
                color hleftColor).profile.faceLengthCap) role := by
  have hexists : ∀ role : LocalLayerRightFaceRole,
      ∃ code : CellFaceAttachmentCode
          (Fintype.card aligned.LocalLayerLeftBoundaryFragment),
        aligned.LocalLayerFaceAttachmentRealizes
            (aligned.toInterface.localLayerRightComposedFragmentOfRole role)
            code ∧
          (((aligned.toInterface.localLayerRightPrefixBoundedProfile
              color hrightColor).profile.faceLengthCap
                (aligned.toInterface.localLayerRightFaceRoleIndex role)).val) =
            code.updatedCap
              ((aligned.localLayerLeftPrefixSharedRungBoundedProfile
                color hleftColor).profile.faceLengthCap) role := by
    intro role
    rcases aligned.exists_localLayerFaceAttachmentCode_with_cap hcubic hrotation
        color hleftColor hrightColor
        (aligned.toInterface.localLayerRightFaceRoleIndex role) with
      ⟨code, hrealizes, hcap⟩
    refine ⟨code, ?_, ?_⟩
    · simpa only [aligned.toInterface
          |>.localLayerRightPrefixBoundaryFragmentAt_roleIndex role] using
        hrealizes
    · rw [aligned.toInterface
        |>.localLayerRightPrefixBoundaryFragmentAt_roleIndex role] at hcap
      have hinputCaps :
          (aligned.localLayerLeftPrefixSharedRungBoundedProfile
              color hleftColor).profile.faceLengthCap =
            (aligned.toInterface.localLayerLeftPrefixBoundedProfile
              color hleftColor).profile.faceLengthCap := by
        funext fragment
        exact aligned.localLayerLeftPrefixSharedRungBoundedProfile_faceLengthCap
          color hleftColor fragment
      rw [hinputCaps]
      cases role <;>
        simp [CellFaceAttachmentCode.updatedCap,
          LocalLayerRightFaceRole.cellCap,
          LocalLayerRightFaceRole.overlapCap,
          aligned.toInterface
            |>.localLayerRightComposedFragmentOfRole_face_eq_nextCenter_iff]
          at hcap ⊢ <;>
        exact hcap
  choose update hupdate using hexists
  exact ⟨update, hupdate⟩

end SourceCornerAlignedSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseAttachmentCode

/-!
# Stable six-slot coordinates for serial-rebase old attachments

The literal old-attachment role records a proof that an immediately preceding
Cell exists.  That dependent proof is useful for source geometry but is not a
stable finite-state ABI.  This file erases only the proof coordinate, yielding
six named slots: two current inputs, two current outputs, and two predecessor
outputs.

At the first offset the predecessor slots decode to `none`; no fictitious
source edge is introduced.  Every actual dependent role encodes injectively
and decodes back exactly.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

/-- Stable source names for the at-most-six old rebase contacts. -/
abbrev BoundedSerialBoundaryRebaseOldAttachmentSlot :=
  (Fin 2 ⊕ Fin 2) ⊕ Fin 2

/-- The stable old-attachment carrier has exactly six coordinates. -/
@[simp] theorem card_boundedSerialBoundaryRebaseOldAttachmentSlot :
    Fintype.card BoundedSerialBoundaryRebaseOldAttachmentSlot = 6 := by
  simp [BoundedSerialBoundaryRebaseOldAttachmentSlot]

namespace SourceTrail

namespace AnnularEmbedding

/-- Forget the unique predecessor proof while retaining its two literal step
names. -/
def sourceCorridorSerialBoundaryRebaseOldAttachmentSlot
    {blockLength : Nat} {offset : Fin (blockLength - 3)} :
    SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset →
      BoundedSerialBoundaryRebaseOldAttachmentSlot
  | .inl current => .inl current
  | .inr previous => .inr previous.2

/-- Erasing the predecessor proof loses no actual source role because an
offset has at most one immediate predecessor. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentSlot_injective
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :
    Function.Injective
      (@sourceCorridorSerialBoundaryRebaseOldAttachmentSlot blockLength
        offset) := by
  intro left right heq
  rcases left with current | ⟨leftPrevious, leftStep⟩ <;>
    rcases right with current' | ⟨rightPrevious, rightStep⟩
  · exact congrArg Sum.inl (Sum.inl.inj heq)
  · cases heq
  · cases heq
  · have hstep : leftStep = rightStep := Sum.inr.inj heq
    have hprevious : leftPrevious = rightPrevious := by
      apply Subtype.ext
      omega
    subst rightPrevious
    subst rightStep
    rfl

/-- Recover the dependent source role represented by a stable slot when it
exists.  The two predecessor slots are deliberately absent at offset zero. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :
    BoundedSerialBoundaryRebaseOldAttachmentSlot →
      Option (SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset)
  | .inl current => some (.inl current)
  | .inr step =>
      if hpositive : 0 < offset.val then
        let historical : Fin (blockLength - 3) :=
          ⟨offset.val - 1,
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) offset.isLt⟩
        some (.inr (⟨historical, by
          change offset.val - 1 + 1 = offset.val
          omega⟩, step))
      else
        none

/-- Every literal role survives the stable-slot round trip exactly. -/
@[simp] theorem sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?_slot
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset
        (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role) =
      some role := by
  rcases role with current | ⟨historical, step⟩
  · rfl
  · have hpositive : 0 < offset.val := by
      omega
    simp only [sourceCorridorSerialBoundaryRebaseOldAttachmentSlot,
      sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?,
      dif_pos hpositive, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq]
    refine ⟨?_, trivial⟩
    apply Subtype.ext
    apply Fin.ext
    change offset.val - 1 = historical.val
    have hhistorical := historical.property
    omega

/-- A predecessor slot is inactive exactly at the first source offset. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?_previous_eq_none_iff
    {blockLength : Nat} (offset : Fin (blockLength - 3)) (step : Fin 2) :
    sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset
        (.inr step) = none ↔
      offset.val = 0 := by
  simp only [sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot?]
  split
  next hpositive => simp [Nat.ne_of_gt hpositive]
  next hnotPositive =>
    simp only [true_iff]
    omega

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseOldAttachmentSlotsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Interpret a stable slot as its literal edge when that role is active. -/
noncomputable def sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAtSlot?
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
    (slot : BoundedSerialBoundaryRebaseOldAttachmentSlot) : Option G.edgeSet :=
  (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset slot).map
    (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
      hrotation htwoSided hunique offset)

/-- Interpreting an encoded actual role recovers its literal edge. -/
@[simp] theorem sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAtSlot?_slot
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
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAtSlot? realization
        hcubic hrotation htwoSided hunique offset
          (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role) =
      some (sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset role) := by
  simp [sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAtSlot?]

end


end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor

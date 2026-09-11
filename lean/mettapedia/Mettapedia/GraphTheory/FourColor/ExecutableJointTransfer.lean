import Mettapedia.GraphTheory.FourColor.FiniteFaceReturn
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint
import Mettapedia.GraphTheory.FourColor.BoundarySmallCutExecutable

/-!
# Executable joint boundary transfer with exact semantic reflection

Colour supports and small-cut profiles are finite sets. Composition
enumerates the present supports, not all possible supports. First-return
permutations use the executable operator; integer mass retains every
closed face correction. No unproved range bound is imposed on mass.
-/

namespace Mettapedia.GraphTheory.FourColor.ExecutableJointTransfer

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open SerialTangleSmallCutTransfer

@[ext] structure State (L R : Type*) where
  colours : Finset ((L → Color) × (R → Color))
  face : Equiv.Perm (L ⊕ R)
  cuts : Finset (BoundarySmallCutProfile.State (L ⊕ R))
  mass : ℤ

def denote {L R : Type*} (s : State L R) : SerialTangleJointTransfer.Signature L R :=
  ⟨s.colours, s.face, s.cuts, s.mass⟩

variable {L P R L' R' : Type*}
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R] [Fintype L'] [DecidableEq L']
  [Fintype R'] [DecidableEq R']

def reword (e : L' ⊕ R' ≃ L ⊕ R) (xy : (L → Color) × (R → Color)) :
    (L' → Color) × (R' → Color) :=
  ⟨fun p => Sum.elim xy.1 xy.2 (e (.inl p)),
   fun p => Sum.elim xy.1 xy.2 (e (.inr p))⟩

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R'] in
theorem reword_apply (e : L' ⊕ R' ≃ L ⊕ R) (xy : (L → Color) × (R → Color))
    (b : L' ⊕ R') :
    Sum.elim (reword e xy).1 (reword e xy).2 b = Sum.elim xy.1 xy.2 (e b) := by
  cases b <;> rfl

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R'] in
theorem reword_inverse (e : L' ⊕ R' ≃ L ⊕ R) (xy : (L → Color) × (R → Color)) :
    reword e.symm (reword e xy) = xy := by
  apply Prod.ext
  · funext p
    change Sum.elim (reword e xy).1 (reword e xy).2 (e.symm (.inl p)) = _
    rw [reword_apply, Equiv.apply_symm_apply]
    rfl
  · funext p
    change Sum.elim (reword e xy).1 (reword e xy).2 (e.symm (.inr p)) = _
    rw [reword_apply, Equiv.apply_symm_apply]
    rfl

def transport (e : L' ⊕ R' ≃ L ⊕ R) (s : State L R) : State L' R' where
  colours := s.colours.image (reword e)
  face := e.symm.permCongr s.face
  cuts := s.cuts.image (BoundarySmallCutProfile.reindex e)
  mass := s.mass

omit [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [DecidableEq L'] [DecidableEq R'] in
theorem transport_exact (e : L' ⊕ R' ≃ L ⊕ R) (s : State L R) :
    denote (transport e s) = TwoSidedBoundaryJoint.transport e (denote s) := by
  apply SerialTangleJointTransfer.Signature.ext
  · ext xy
    change xy ∈ s.colours.image (reword e) ↔ reword e.symm xy ∈ s.colours
    constructor
    · rintro h
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      simpa only [reword_inverse] using hz
    · intro h
      exact Finset.mem_image.mpr ⟨reword e.symm xy, h, reword_inverse e.symm xy⟩
  · rfl
  · exact Finset.coe_image
  · rfl

def transfer (s : State L P) (t : State P R) : State L R where
  colours := ((s.colours.product t.colours).filter (fun p => p.1.2 = p.2.1)).image
    (fun p => (p.1.1, p.2.2))
  face := FiniteFaceReturn.transfer s.face t.face
  cuts := BoundarySmallCutExecutable.transfer s.cuts t.cuts
  mass := s.mass + t.mass - 2 * Fintype.card P +
    2 * ((Equiv.Perm.partition
      (Equiv.sumCongr s.face t.face * SerialTangleFaceCode.codeSwap)).parts.card : ℤ) -
    2 * ((Equiv.Perm.partition (Equiv.sumCongr s.face t.face)).parts.card : ℤ)

set_option maxHeartbeats 1000000 in
theorem transfer_exact (s : State L P) (t : State P R) :
    denote (transfer s t) = SerialTangleJointTransfer.transfer (denote s) (denote t) := by
  apply SerialTangleJointTransfer.Signature.ext
  · ext xy
    change xy ∈ ((s.colours.product t.colours).filter (fun p => p.1.2 = p.2.1)).image
      (fun p => (p.1.1, p.2.2)) ↔ ∃ z, (xy.1, z) ∈ s.colours ∧ (z, xy.2) ∈ t.colours
    constructor
    · intro h
      obtain ⟨⟨⟨x, z⟩, ⟨z', y⟩⟩, hp, he⟩ := Finset.mem_image.mp h
      obtain ⟨hp, hh⟩ := Finset.mem_filter.mp hp
      obtain ⟨hs, ht⟩ := Finset.mem_product.mp hp
      cases he
      cases hh
      exact ⟨z, hs, ht⟩
    · rintro ⟨z, hs, ht⟩
      exact Finset.mem_image.mpr ⟨((xy.1, z), (z, xy.2)),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, Prod.eta xy⟩
  · exact FiniteFaceReturn.transfer_eq s.face t.face
  · exact BoundarySmallCutExecutable.transfer_correct s.cuts t.cuts
  · rfl

end Mettapedia.GraphTheory.FourColor.ExecutableJointTransfer

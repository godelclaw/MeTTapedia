import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryReindex
import Mettapedia.GraphTheory.FourColor.SerialTangleJointTransfer

/-! # Joint semantics under a change of boundary coordinates -/

namespace Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open TwoSidedBoundaryReindex SerialTangleSmallCutTransfer
open GoertzelV24CompositeSeamMultigraph OpenTangleMarkedFace OpenTangleReplacementEuler
open GoertzelV24RetainedSpliceFaceCount SerialTangleFaceCode SerialTangleFaceTransfer
open GoertzelV24OrderedCutFaceReturnProfile

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I L R L' R' : Type*}
  (T : TwoSidedOpenTangleData V I L R) (e : L' ⊕ R' ≃ L ⊕ R)

theorem side_reindex : sideMultigraph (asOpen (reindex T e)) =
    sideMultigraph (asOpen T) := rfl

theorem boundary_reindex (b : L' ⊕ R') :
    (asOpen (reindex T e)).boundaryVert b = (asOpen T).boundaryVert (e b) := by
  cases b <;> rfl

theorem phi_map (d : I ⊕ (L' ⊕ R')) :
    openPhi (asOpen T) (darts e d) = darts e (openPhi (asOpen (reindex T e)) d) := by
  rcases d with i | b
  · change T.rho (.inl (T.interiorAlpha i)) =
      darts e ((darts e).symm (T.rho (.inl (T.interiorAlpha i))))
    exact ((darts e).apply_symm_apply _).symm
  · change T.rho (.inr (e b)) = darts e ((darts e).symm (T.rho (.inr (e b))))
    exact ((darts e).apply_symm_apply _).symm

theorem phi_reindex : openPhi (asOpen (reindex T e)) =
    (darts e).symm.permCongr (openPhi (asOpen T)) := by
  ext d
  apply (darts e).injective
  simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply] using
    (phi_map T e d).symm

variable [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] [Fintype L'] [DecidableEq L']
  [Fintype R'] [DecidableEq R']

omit [DecidableEq I] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype L'] [DecidableEq L'] [Fintype R'] [DecidableEq R'] in
theorem cuts_reindex :
    BoundarySmallCutProfile.profile (sideMultigraph (asOpen (reindex T e)))
      (asOpen (reindex T e)).boundaryVert =
    BoundarySmallCutProfile.reindex e ''
      BoundarySmallCutProfile.profile (sideMultigraph (asOpen T)) (asOpen T).boundaryVert := by
  rw [side_reindex]
  have hb : (asOpen (reindex T e)).boundaryVert = (asOpen T).boundaryVert ∘ e :=
    funext (boundary_reindex T e)
  rw [hb, BoundarySmallCutProfile.profile_reindex]
  rfl

theorem face_reindex : SerialTangleFaceCode.encode (reindex T e) =
    e.symm.permCongr (SerialTangleFaceCode.encode T) := by
  have hhit (d : I ⊕ (L' ⊕ R')) : Boundary (darts e d) ↔ Boundary d := by
    cases d <;> rfl
  have hh (b : L' ⊕ R') := PermutationFirstReturnRestriction.nextHit_map
    (openPhi (asOpen (reindex T e))) (openPhi (asOpen T)) (darts e)
    (phi_map T e) Boundary Boundary hhit ⟨.inr b, trivial⟩
  have hb (b : L' ⊕ R') :
      (boundaryCoordinate I (L ⊕ R))
        (nextHitPerm (openPhi (asOpen T)) Boundary ⟨.inr (e b), trivial⟩) =
      e ((boundaryCoordinate I (L' ⊕ R'))
        (nextHitPerm (openPhi (asOpen (reindex T e))) Boundary ⟨.inr b, trivial⟩)) := by
    let left := nextHitPerm (openPhi (asOpen T)) Boundary ⟨.inr (e b), trivial⟩
    let right := nextHitPerm (openPhi (asOpen (reindex T e))) Boundary ⟨.inr b, trivial⟩
    have h := hh b
    change left.1 = darts e right.1 at h
    change boundaryCoordinate I _ left = e (boundaryCoordinate I _ right)
    rcases left with ⟨i | x, hl⟩
    · exact False.elim hl
    rcases right with ⟨i | y, hr⟩
    · exact False.elim hr
    exact Sum.inr.inj h
  ext b
  apply e.injective
  simp only [SerialTangleFaceCode.encode, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]
  change e ((boundaryCoordinate I (L' ⊕ R'))
      (nextHitPerm (openPhi (asOpen (reindex T e))) Boundary ⟨.inr b, trivial⟩)) =
    (boundaryCoordinate I (L ⊕ R))
      (nextHitPerm (openPhi (asOpen T)) Boundary ⟨.inr (e b), trivial⟩)
  exact (hb b).symm

variable [Fintype V]

theorem mass_reindex : eulerMass (asOpen (reindex T e)) = eulerMass (asOpen T) := by
  simp only [eulerMass, phi_reindex, card_permCongr_partition_parts]

def transport (s : SerialTangleJointTransfer.Signature L R) :
    SerialTangleJointTransfer.Signature L' R' where
  colours := {xy | ((fun p => Sum.elim xy.1 xy.2 (e.symm (.inl p))),
    (fun p => Sum.elim xy.1 xy.2 (e.symm (.inr p)))) ∈ s.colours}
  face := e.symm.permCongr s.face
  cuts := BoundarySmallCutProfile.reindex e '' s.cuts
  mass := s.mass

theorem joint_reindex : SerialTangleJointTransfer.encode (reindex T e) =
    transport e (SerialTangleJointTransfer.encode T) := by
  apply SerialTangleJointTransfer.Signature.ext
  · ext xy
    let w := Sum.elim xy.1 xy.2 ∘ e.symm
    have hw : w ∘ e = Sum.elim xy.1 xy.2 := by
      funext b
      exact congrArg (Sum.elim xy.1 xy.2) (e.symm_apply_apply b)
    have hh := accepts_reindex T e w
    rw [hw, accepts_iff] at hh
    have hw' : w = Sum.elim (fun p => w (.inl p)) (fun p => w (.inr p)) := by
      funext b; cases b <;> rfl
    rw [hw', accepts_iff] at hh
    exact hh
  · exact face_reindex T e
  · exact cuts_reindex T e
  · exact mass_reindex T e

end
end Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryJoint

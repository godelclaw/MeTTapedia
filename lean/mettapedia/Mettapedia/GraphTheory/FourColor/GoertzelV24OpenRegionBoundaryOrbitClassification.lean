import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbit

/-!
# Classification of open-region stub face orbits

The literal open-region rotation inserts one fresh degree-one stub into every
exposed retained edge.  The forward C-2 lemma shows that a cycle of the
retained first-return permutation lies in one opened face.  Here we prove the
converse: two fresh stubs lie on one opened face only if their retained
boundary darts lie in one first-return cycle.

The proof collapses each fresh stub dart to its old retained boundary dart.
One opened face step then either leaves this projection fixed (the old
boundary-to-stub step) or advances it by one capped retained-face step.  This
is generic rotation-system plumbing, not source annulus geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionBoundaryOrbitClassification

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionBoundaryOrbit
open GoertzelV24OpenRegionRotation
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Forget whether an opened dart is old or a fresh stub, retaining the old
retained dart on the same half-edge. -/
def collapseOpenDart (RS : RotationSystem V E) (keep : V → Prop) :
    Dart RS keep → RetainedDart RS keep
  | Sum.inl dart => dart
  | Sum.inr boundary => boundary.1

/-- One opened face step either pauses the collapsed capped walk at an
inserted stub, or advances it by one capped retained-face step. -/
theorem collapseOpenDart_phi_eq_self_or_capped
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : Dart RS keep) :
    collapseOpenDart RS keep ((rotationSystem RS keep outer).phi dart) =
        collapseOpenDart RS keep dart ∨
      collapseOpenDart RS keep ((rotationSystem RS keep outer).phi dart) =
        retainedCappedFacePerm RS keep (collapseOpenDart RS keep dart) := by
  rcases dart with dart | boundary
  · by_cases hinternal : keep (RS.vertOf (RS.alpha dart.1))
    · right
      rw [rotationSystem_phi_old_eq_retainedCappedFacePerm_of_internal
        RS keep outer dart hinternal]
      rfl
    · left
      let boundary : BoundaryDart RS keep := ⟨dart, hinternal⟩
      have hstep := rotationSystem_phi_old_boundary RS keep outer boundary
      change collapseOpenDart RS keep
          ((rotationSystem RS keep outer).phi (Sum.inl dart)) = dart
      rw [hstep]
      rfl
  · right
    rw [rotationSystem_phi_stub_eq_retainedCappedFacePerm
      RS keep outer boundary]
    rfl

/-- Every finite opened face walk projects to some finite capped retained-face
walk; inserted stub steps may contribute zero projected advances. -/
theorem exists_capped_pow_eq_collapse_phi_pow
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (dart : Dart RS keep) (power : Nat) :
    ∃ cappedPower : Nat,
      collapseOpenDart RS keep
          (((rotationSystem RS keep outer).phi ^ power) dart) =
        (retainedCappedFacePerm RS keep ^ cappedPower)
          (collapseOpenDart RS keep dart) := by
  induction power with
  | zero => exact ⟨0, rfl⟩
  | succ power ih =>
      rcases ih with ⟨cappedPower, hcollapsed⟩
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases collapseOpenDart_phi_eq_self_or_capped RS keep outer
          (((rotationSystem RS keep outer).phi ^ power) dart) with hsame | hstep
      · refine ⟨cappedPower, ?_⟩
        exact hsame.trans hcollapsed
      · refine ⟨cappedPower + 1, ?_⟩
        rw [hstep, hcollapsed, pow_succ', Equiv.Perm.mul_apply]

/-- An opened-face relation between fresh stubs forces the corresponding old
retained darts into one capped retained-face cycle. -/
theorem retainedCappedFacePerm_sameCycle_of_open_stub_sameCycle
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (first second : BoundaryDart RS keep)
    (hsame : (rotationSystem RS keep outer).phi.SameCycle
      (Sum.inr first) (Sum.inr second)) :
    (retainedCappedFacePerm RS keep).SameCycle first.1 second.1 := by
  rcases hsame.exists_nat_pow_eq with ⟨power, hpower⟩
  rcases exists_capped_pow_eq_collapse_phi_pow
      RS keep outer (Sum.inr first) power with ⟨cappedPower, hcollapsed⟩
  rw [hpower] at hcollapsed
  change second.1 =
    (retainedCappedFacePerm RS keep ^ cappedPower) first.1 at hcollapsed
  have hpow : (retainedCappedFacePerm RS keep).SameCycle first.1
      ((retainedCappedFacePerm RS keep ^ cappedPower) first.1) :=
    (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl (retainedCappedFacePerm RS keep) first.1)
  exact hpow.trans (hcollapsed.sameCycle (retainedCappedFacePerm RS keep)).symm

/-- Fresh stubs share an opened face exactly when their boundary coordinates
share a cycle of the retained first-return permutation. -/
theorem dartOrbitFace_stub_eq_iff_boundarySuccessor_sameCycle
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) (first second : BoundaryDart RS keep) :
    dartOrbitFace (rotationSystem RS keep outer) (Sum.inr first) =
        dartOrbitFace (rotationSystem RS keep outer) (Sum.inr second) ↔
      (retainedRegionBoundarySuccessor RS keep).SameCycle first second := by
  constructor
  · intro hface
    have hopen : (rotationSystem RS keep outer).phi.SameCycle
        (Sum.inr first) (Sum.inr second) := by
      change Quotient.mk (Equiv.Perm.SameCycle.setoid
          (rotationSystem RS keep outer).phi) (Sum.inr first) =
        Quotient.mk (Equiv.Perm.SameCycle.setoid
          (rotationSystem RS keep outer).phi) (Sum.inr second) at hface
      rw [Quotient.eq] at hface
      exact hface
    change (nextHitPerm (retainedCappedFacePerm RS keep)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1)))).SameCycle first second
    exact (nextHitPerm_sameCycle_iff
      (retainedCappedFacePerm RS keep)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) first second).2
        (retainedCappedFacePerm_sameCycle_of_open_stub_sameCycle
          RS keep outer first second hopen)
  · exact dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
      RS keep outer first second

end

end GoertzelV24OpenRegionBoundaryOrbitClassification

end Mettapedia.GraphTheory.FourColor

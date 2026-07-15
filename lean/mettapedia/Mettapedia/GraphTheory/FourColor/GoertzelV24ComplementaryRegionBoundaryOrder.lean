import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ComplementaryRegionBoundaryOrder

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Along a capped retained-side face walk, every positive step through the
next exposed half-dart is the corresponding ambient face step starting from
the old opposite half-dart. -/
theorem retainedCappedFacePerm_pow_val_eq_ambient_phi_pow_alpha
    (RS : RotationSystem V E) (keep : V -> Prop)
    (root : BoundaryDart RS keep) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLe : step <= firstPositiveHitTime
      (retainedCappedFacePerm RS keep)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) root.1 root.2) :
    ((retainedCappedFacePerm RS keep ^ step) root.1).1 =
      (RS.phi ^ step) (RS.alpha root.1.1) := by
  classical
  induction step with
  | zero => omega
  | succ previous ih =>
      by_cases hpreviousZero : previous = 0
      · subst previous
        change (retainedRho RS keep
            (retainedCappedAlpha RS keep root.1)).1 =
          RS.rho (RS.alpha (RS.alpha root.1.1))
        rw [retainedRho_val,
          retainedCappedAlpha_apply_boundary RS keep root.1 root.2,
          RS.alpha_involutive]
      · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hpreviousZero
        have hpreviousLt : previous < firstPositiveHitTime
            (retainedCappedFacePerm RS keep)
            (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1)))
            root.1 root.2 := by
          omega
        have hnotBoundary :
            ¬ (¬ keep (RS.vertOf (RS.alpha
              ((retainedCappedFacePerm RS keep ^ previous) root.1).1))) :=
          not_hit_before_firstPositiveHitTime
            (retainedCappedFacePerm RS keep)
            (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1)))
            root.1 root.2 hpreviousPos hpreviousLt
        have hoppositeKeep : keep (RS.vertOf (RS.alpha
            ((retainedCappedFacePerm RS keep ^ previous) root.1).1)) := by
          simpa using hnotBoundary
        rw [pow_succ', Equiv.Perm.mul_apply,
          pow_succ', Equiv.Perm.mul_apply]
        change (retainedRho RS keep
            (retainedCappedAlpha RS keep
              ((retainedCappedFacePerm RS keep ^ previous) root.1))).1 =
          RS.phi ((RS.phi ^ previous) (RS.alpha root.1.1))
        rw [retainedRho_val,
          retainedCappedAlpha_apply_internal RS keep _ hoppositeKeep]
        change RS.rho (RS.alpha
            ((retainedCappedFacePerm RS keep ^ previous) root.1).1) =
          RS.rho (RS.alpha
            ((RS.phi ^ previous) (RS.alpha root.1.1)))
        rw [ih hpreviousPos (Nat.le_of_lt hpreviousLt)]

/-- The retained capped successor ends on the same ambient facial cycle as
the deleted-side half-dart opposite its starting boundary dart. -/
theorem retainedRegionBoundarySuccessor_sameAmbientFace_alpha
    (RS : RotationSystem V E) (keep : V -> Prop)
    (root : BoundaryDart RS keep) :
    RS.phi.SameCycle (RS.alpha root.1.1)
      ((retainedRegionBoundarySuccessor RS keep root).1.1) := by
  classical
  let returnTime := firstPositiveHitTime
    (retainedCappedFacePerm RS keep)
    (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) root.1 root.2
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos (retainedCappedFacePerm RS keep)
      (fun dart => ¬ keep (RS.vertOf (RS.alpha dart.1))) root.1 root.2
  have hreturn :
      (retainedRegionBoundarySuccessor RS keep root).1.1 =
        (RS.phi ^ returnTime) (RS.alpha root.1.1) := by
    exact retainedCappedFacePerm_pow_val_eq_ambient_phi_pow_alpha
      RS keep root hreturnPos (Nat.le_refl returnTime)
  rw [hreturn]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl RS.phi (RS.alpha root.1.1))

/-- Along a capped deleted-side face walk, every positive step through the
next exposed half-dart is the corresponding ambient face step starting from
the retained half-dart on the same crossing edge. -/
theorem deletedFacePerm_pow_val_eq_ambient_phi_pow_alpha
    (RS : RotationSystem V E) (deleted : Finset V)
    (root : DeletedBoundaryHalfDart RS deleted) {step : Nat}
    (hstepPos : 0 < step)
    (hstepLe : step <= firstPositiveHitTime
      (deletedFacePerm RS deleted)
      (IsDeletedBoundaryHalfDart RS deleted) root.1 root.2) :
    ((deletedFacePerm RS deleted ^ step) root.1).1 =
      (RS.phi ^ step) (RS.alpha root.1.1) := by
  classical
  induction step with
  | zero => omega
  | succ previous ih =>
      by_cases hpreviousZero : previous = 0
      · subst previous
        change (deletedRho RS deleted
            (deletedAlpha RS deleted root.1)).1 =
          RS.rho (RS.alpha (RS.alpha root.1.1))
        rw [deletedRho_val,
          deletedAlpha_apply_boundary RS deleted root.1 root.2,
          RS.alpha_involutive]
      · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hpreviousZero
        have hpreviousLt : previous < firstPositiveHitTime
            (deletedFacePerm RS deleted)
            (IsDeletedBoundaryHalfDart RS deleted) root.1 root.2 := by
          omega
        have hnotBoundary : ¬ IsDeletedBoundaryHalfDart RS deleted
            ((deletedFacePerm RS deleted ^ previous) root.1) :=
          not_hit_before_firstPositiveHitTime
            (deletedFacePerm RS deleted)
            (IsDeletedBoundaryHalfDart RS deleted)
            root.1 root.2 hpreviousPos hpreviousLt
        have hoppositeDeleted : RS.vertOf (RS.alpha
            ((deletedFacePerm RS deleted ^ previous) root.1).1) ∈ deleted := by
          simpa [IsDeletedBoundaryHalfDart] using hnotBoundary
        rw [pow_succ', Equiv.Perm.mul_apply,
          pow_succ', Equiv.Perm.mul_apply]
        change (deletedRho RS deleted
            (deletedAlpha RS deleted
              ((deletedFacePerm RS deleted ^ previous) root.1))).1 =
          RS.phi ((RS.phi ^ previous) (RS.alpha root.1.1))
        rw [deletedRho_val,
          deletedAlpha_apply_internal RS deleted _ hoppositeDeleted]
        change RS.rho (RS.alpha
            ((deletedFacePerm RS deleted ^ previous) root.1).1) =
          RS.rho (RS.alpha
            ((RS.phi ^ previous) (RS.alpha root.1.1)))
        rw [ih hpreviousPos (Nat.le_of_lt hpreviousLt)]

/-- The deleted capped successor ends on the same ambient facial cycle as
the retained half-dart opposite its starting deleted boundary half-dart. -/
theorem deletedBoundaryNextHit_sameAmbientFace_alpha
    (RS : RotationSystem V E) (deleted : Finset V)
    (root : DeletedBoundaryHalfDart RS deleted) :
    RS.phi.SameCycle (RS.alpha root.1.1)
      ((nextHitPerm (deletedFacePerm RS deleted)
        (IsDeletedBoundaryHalfDart RS deleted) root).1.1) := by
  classical
  let returnTime := firstPositiveHitTime
    (deletedFacePerm RS deleted)
    (IsDeletedBoundaryHalfDart RS deleted) root.1 root.2
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos (deletedFacePerm RS deleted)
      (IsDeletedBoundaryHalfDart RS deleted) root.1 root.2
  have hreturn :
      (nextHitPerm (deletedFacePerm RS deleted)
        (IsDeletedBoundaryHalfDart RS deleted) root).1.1 =
        (RS.phi ^ returnTime) (RS.alpha root.1.1) := by
    exact deletedFacePerm_pow_val_eq_ambient_phi_pow_alpha
      RS deleted root hreturnPos (Nat.le_refl returnTime)
  rw [hreturn]
  exact (Equiv.Perm.sameCycle_pow_right).2
    (Equiv.Perm.SameCycle.refl RS.phi (RS.alpha root.1.1))

/-- Transported to the retained boundary carrier, the deleted capped
successor reaches a half-dart whose old opposite remains on the starting
ambient facial cycle. -/
theorem deletedRegionBoundarySuccessor_sameAmbientFace_alpha
    (RS : RotationSystem V E) (deleted : Finset V)
    (root : BoundaryDart RS (deletedRegionKeep deleted)) :
    RS.phi.SameCycle root.1.1
      (RS.alpha
        ((deletedRegionBoundarySuccessor RS deleted root).1.1)) := by
  classical
  let boundaryEquiv :=
    deletedBoundaryHalfDartEquivBoundaryDart RS deleted
  let deletedRoot := boundaryEquiv.symm root
  let following := nextHitPerm (deletedFacePerm RS deleted)
    (IsDeletedBoundaryHalfDart RS deleted) deletedRoot
  have hface := deletedBoundaryNextHit_sameAmbientFace_alpha
    RS deleted deletedRoot
  have hroot : RS.alpha deletedRoot.1.1 = root.1.1 := by
    have happly := boundaryEquiv.apply_symm_apply root
    exact congrArg (fun dart : BoundaryDart RS
      (deletedRegionKeep deleted) => dart.1.1) happly
  have hfollowing : following.1.1 =
      RS.alpha (boundaryEquiv following).1.1 := by
    change following.1.1 = RS.alpha (RS.alpha following.1.1)
    rw [RS.alpha_involutive]
  have hsuccessor :
      deletedRegionBoundarySuccessor RS deleted root =
        boundaryEquiv following := by
    rfl
  rw [← hroot, hsuccessor, ← hfollowing]
  exact hface

/-- One deleted-side boundary return followed by one retained-side boundary
return stays on the ambient facial cycle of the original retained boundary
dart. -/
theorem retained_mul_deleted_boundarySuccessor_sameAmbientFace
    (RS : RotationSystem V E) (deleted : Finset V)
    (root : BoundaryDart RS (deletedRegionKeep deleted)) :
    RS.phi.SameCycle root.1.1
      (((retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) *
        deletedRegionBoundarySuccessor RS deleted) root).1.1) := by
  rw [Equiv.Perm.mul_apply]
  exact (deletedRegionBoundarySuccessor_sameAmbientFace_alpha
    RS deleted root).trans
      (retainedRegionBoundarySuccessor_sameAmbientFace_alpha
        RS (deletedRegionKeep deleted)
        (deletedRegionBoundarySuccessor RS deleted root))

/-- Every ambient facial cycle contains at most one retained boundary dart
of the vertex cut. This is the exact local form of the planar bond/dual-cycle
property needed to compare the two computed boundary orientations. -/
def CutFacesHaveUniqueRetainedBoundaryDart
    (RS : RotationSystem V E) (deleted : Finset V) : Prop :=
  forall left right : BoundaryDart RS (deletedRegionKeep deleted),
    RS.phi.SameCycle left.1.1 right.1.1 -> left = right

/-- Darts of one facial cycle currently based on the selected vertex side. -/
noncomputable def faceSideCurrentDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    Finset RS.D := by
  classical
  exact (RS.faceOrbit root).filter (fun dart => side (RS.vertOf dart))

/-- Darts of one facial cycle whose next facial step is based on the selected
vertex side. -/
noncomputable def faceSideNextDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    Finset RS.D := by
  classical
  exact (RS.faceOrbit root).filter
    (fun dart => side (RS.vertOf (RS.phi dart)))

/-- Oriented exits from the selected vertex side along one facial cycle. -/
noncomputable def faceSideExitDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    Finset RS.D :=
  faceSideCurrentDarts RS side root \ faceSideNextDarts RS side root

/-- Oriented entries into the selected vertex side along one facial cycle. -/
noncomputable def faceSideEntryDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    Finset RS.D :=
  faceSideNextDarts RS side root \ faceSideCurrentDarts RS side root

/-- All side-changing darts on one facial cycle. -/
noncomputable def faceSideTransitionDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    Finset RS.D := by
  classical
  exact (RS.faceOrbit root).filter (fun dart =>
    side (RS.vertOf dart) ≠ side (RS.vertOf (RS.phi dart)))

@[simp]
theorem mem_faceSideCurrentDarts_iff
    (RS : RotationSystem V E) (side : V -> Prop) (root dart : RS.D) :
    dart ∈ faceSideCurrentDarts RS side root <->
      dart ∈ RS.faceOrbit root /\ side (RS.vertOf dart) := by
  classical
  simp [faceSideCurrentDarts]

@[simp]
theorem mem_faceSideNextDarts_iff
    (RS : RotationSystem V E) (side : V -> Prop) (root dart : RS.D) :
    dart ∈ faceSideNextDarts RS side root <->
      dart ∈ RS.faceOrbit root /\ side (RS.vertOf (RS.phi dart)) := by
  classical
  simp [faceSideNextDarts]

/-- Reindexing a facial cycle by `phi` shows that it has equally many
currently selected and next-selected darts. -/
theorem card_faceSideCurrentDarts_eq_card_faceSideNextDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    (faceSideCurrentDarts RS side root).card =
      (faceSideNextDarts RS side root).card := by
  classical
  symm
  refine Finset.card_bij (fun dart _ => RS.phi dart) ?_ ?_ ?_
  · intro dart hdart
    rw [mem_faceSideCurrentDarts_iff]
    rw [mem_faceSideNextDarts_iff] at hdart
    exact ⟨RS.phi_mem_faceOrbit hdart.1, hdart.2⟩
  · intro left hleft right hright heq
    exact RS.phi.injective heq
  · intro dart hdart
    refine ⟨RS.phi.symm dart, ?_, by simp⟩
    rw [mem_faceSideNextDarts_iff]
    rw [mem_faceSideCurrentDarts_iff] at hdart
    exact ⟨RS.phi_symm_mem_faceOrbit hdart.1, by simpa using hdart.2⟩

/-- A cyclic binary side word has equally many exits and entries. -/
theorem card_faceSideExitDarts_eq_card_faceSideEntryDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    (faceSideExitDarts RS side root).card =
      (faceSideEntryDarts RS side root).card := by
  unfold faceSideExitDarts faceSideEntryDarts
  exact Finset.card_sdiff_comm
    (card_faceSideCurrentDarts_eq_card_faceSideNextDarts RS side root)

/-- The transition darts are exactly the disjoint union of exits and entries. -/
theorem faceSideTransitionDarts_eq_exit_union_entry
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    faceSideTransitionDarts RS side root =
      faceSideExitDarts RS side root ∪ faceSideEntryDarts RS side root := by
  classical
  ext dart
  simp only [faceSideTransitionDarts, Finset.mem_filter,
    faceSideExitDarts, faceSideEntryDarts, Finset.mem_union,
    Finset.mem_sdiff, mem_faceSideCurrentDarts_iff,
    mem_faceSideNextDarts_iff]
  by_cases horbit : dart ∈ RS.faceOrbit root <;>
    by_cases hcurrent : side (RS.vertOf dart) <;>
    by_cases hnext : side (RS.vertOf (RS.phi dart)) <;>
    simp_all

/-- Consequently a face has twice as many side-changing darts as oriented
exits from either chosen side. -/
theorem card_faceSideTransitionDarts_eq_twice_exitDarts
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    (faceSideTransitionDarts RS side root).card =
      2 * (faceSideExitDarts RS side root).card := by
  rw [faceSideTransitionDarts_eq_exit_union_entry]
  have hdisjoint : Disjoint (faceSideExitDarts RS side root)
      (faceSideEntryDarts RS side root) := by
    rw [Finset.disjoint_left]
    intro dart hexit hentry
    exact (Finset.mem_sdiff.1 hexit).2
      (Finset.mem_sdiff.1 hentry).1
  rw [Finset.card_union_of_disjoint hdisjoint,
    ← card_faceSideExitDarts_eq_card_faceSideEntryDarts]
  omega

/-- Computed planar-bond face condition: every ambient facial occurrence
changes between the retained and deleted vertex sides at most twice. -/
def CutFacesHaveAtMostTwoTransitionDarts
    (RS : RotationSystem V E) (deleted : Finset V) : Prop :=
  forall root : RS.D,
    (faceSideTransitionDarts RS (deletedRegionKeep deleted) root).card <= 2

/-- Every retained boundary dart is an oriented exit in any representative
of its ambient facial cycle. -/
theorem boundaryDart_mem_faceSideExitDarts
    (RS : RotationSystem V E) (deleted : Finset V)
    (representative : RS.D)
    (boundary : BoundaryDart RS (deletedRegionKeep deleted))
    (hface : RS.phi.SameCycle representative boundary.1.1) :
    boundary.1.1 ∈ faceSideExitDarts RS
      (deletedRegionKeep deleted) representative := by
  classical
  rw [faceSideExitDarts, Finset.mem_sdiff]
  constructor
  · rw [mem_faceSideCurrentDarts_iff]
    exact ⟨(RS.mem_faceOrbit).2 hface, boundary.1.2⟩
  · rw [mem_faceSideNextDarts_iff]
    intro hnext
    apply boundary.2
    rw [← RS.vert_phi_eq_vert_alpha]
    exact hnext.2

/-- At most two side changes per face implies unique retained boundary
occurrence on every touched face. -/
theorem cutFacesHaveUniqueRetainedBoundaryDart_of_atMostTwoTransitions
    (RS : RotationSystem V E) (deleted : Finset V)
    (hatMostTwo : CutFacesHaveAtMostTwoTransitionDarts RS deleted) :
    CutFacesHaveUniqueRetainedBoundaryDart RS deleted := by
  intro left right hface
  by_contra hne
  have hleftMem := boundaryDart_mem_faceSideExitDarts
    RS deleted left.1.1 left (Equiv.Perm.SameCycle.refl RS.phi left.1.1)
  have hrightMem := boundaryDart_mem_faceSideExitDarts
    RS deleted left.1.1 right hface
  have hvals : left.1.1 ≠ right.1.1 := by
    intro hval
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  have hexits : 2 <= (faceSideExitDarts RS
      (deletedRegionKeep deleted) left.1.1).card := by
    have hone : 1 < (faceSideExitDarts RS
        (deletedRegionKeep deleted) left.1.1).card :=
      Finset.one_lt_card.2
        ⟨left.1.1, hleftMem, right.1.1, hrightMem, hvals⟩
    omega
  have htransitions := hatMostTwo left.1.1
  have htwice := card_faceSideTransitionDarts_eq_twice_exitDarts
    RS (deletedRegionKeep deleted) left.1.1
  omega

/-- Ambient darts at which a face step changes between the retained and
deleted sides of a concrete vertex cut. -/
def CutSideTransitionDart
    (RS : RotationSystem V E) (deleted : Finset V) :=
  {dart : RS.D //
    deletedRegionKeep deleted (RS.vertOf dart) ≠
      deletedRegionKeep deleted (RS.vertOf (RS.phi dart))}

noncomputable instance cutSideTransitionDartFintype
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype (CutSideTransitionDart RS deleted) :=
  Fintype.ofInjective (fun dart => dart.1) Subtype.val_injective

/-- A side-changing dart is either the retained orientation of its crossing
edge or the alpha-opposite of that orientation. -/
def cutSideTransitionDartEquivBoundarySum
    (RS : RotationSystem V E) (deleted : Finset V) :
    CutSideTransitionDart RS deleted ≃
      BoundaryDart RS (deletedRegionKeep deleted) ⊕
        BoundaryDart RS (deletedRegionKeep deleted) := by
  classical
  refine
    { toFun := fun dart =>
        if hcurrent : deletedRegionKeep deleted (RS.vertOf dart.1) then
          Sum.inl
            ⟨⟨dart.1, hcurrent⟩, by
              intro hopposite
              apply dart.2
              rw [RS.vert_phi_eq_vert_alpha]
              exact propext ⟨fun _ => hopposite, fun _ => hcurrent⟩⟩
        else
          Sum.inr
            ⟨⟨RS.alpha dart.1, by
                rw [← RS.vert_phi_eq_vert_alpha]
                by_contra hnext
                apply dart.2
                exact propext ⟨fun h => (hcurrent h).elim,
                  fun h => (hnext h).elim⟩⟩,
              by simpa [RS.alpha_involutive] using hcurrent⟩
      invFun := fun dart => dart.elim
        (fun boundary =>
          ⟨boundary.1.1, by
            intro heq
            have hnext : deletedRegionKeep deleted
                (RS.vertOf (RS.phi boundary.1.1)) := by
              exact heq.mp boundary.1.2
            exact boundary.2
              (by rwa [RS.vert_phi_eq_vert_alpha] at hnext)⟩)
        (fun boundary =>
          ⟨RS.alpha boundary.1.1, by
            intro heq
            have hcurrent : deletedRegionKeep deleted
                (RS.vertOf (RS.alpha boundary.1.1)) := heq.mpr (by
              rw [RS.vert_phi_eq_vert_alpha, RS.alpha_involutive]
              exact boundary.1.2)
            exact boundary.2 hcurrent⟩)
      left_inv := ?_
      right_inv := ?_ }
  · intro dart
    dsimp
    split
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change RS.alpha (RS.alpha dart.1) = dart.1
      exact RS.alpha_involutive dart.1
  · intro dart
    rcases dart with boundary | boundary
    · dsimp
      split
      · apply congrArg Sum.inl
        apply Subtype.ext
        rfl
      · exact (‹¬ deletedRegionKeep deleted
          (RS.vertOf boundary.1.1)› boundary.1.2).elim
    · dsimp
      split
      · exact (boundary.2 ‹deletedRegionKeep deleted
          (RS.vertOf (RS.alpha boundary.1.1))›).elim
      · apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        exact RS.alpha_involutive boundary.1.1

/-- Side-changing darts are counted by the two orientations of every
endpoint-computed crossing edge. -/
theorem card_cutSideTransitionDart_eq_twice_crossingEdges
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype.card (CutSideTransitionDart RS deleted) =
      2 * (vertexSetCrossingEdges RS deleted).card := by
  rw [Fintype.card_congr
      (cutSideTransitionDartEquivBoundarySum RS deleted),
    Fintype.card_sum,
    card_boundaryDart_deletedRegionKeep]
  omega

/-- Side-changing darts on one quotient face, retaining facial-cycle
multiplicity rather than only edge support. -/
noncomputable def orbitFaceSideTransitionDarts
    (RS : RotationSystem V E) (side : V -> Prop) (face : OrbitFace RS) :
    Finset RS.D := by
  classical
  exact (orbitFaceDarts RS face).filter (fun dart =>
    side (RS.vertOf dart) ≠ side (RS.vertOf (RS.phi dart)))

@[simp]
theorem mem_orbitFaceSideTransitionDarts_iff
    (RS : RotationSystem V E) (side : V -> Prop)
    (face : OrbitFace RS) (dart : RS.D) :
    dart ∈ orbitFaceSideTransitionDarts RS side face <->
      dartOrbitFace RS dart = face /\
        side (RS.vertOf dart) ≠ side (RS.vertOf (RS.phi dart)) := by
  classical
  simp [orbitFaceSideTransitionDarts]

/-- The quotient-face fibers partition every selected collection of darts,
including the side-transition collection. -/
theorem sum_card_orbitFaceSideTransitionDarts_eq_card_cutSideTransitionDart
    (RS : RotationSystem V E) (deleted : Finset V) :
    (∑ face : OrbitFace RS,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card) =
      Fintype.card (CutSideTransitionDart RS deleted) := by
  classical
  change (∑ face : OrbitFace RS,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card) =
      Fintype.card {dart : RS.D //
        deletedRegionKeep deleted (RS.vertOf dart) ≠
          deletedRegionKeep deleted (RS.vertOf (RS.phi dart))}
  rw [Fintype.card_subtype]
  symm
  change ((Finset.univ.filter fun dart : RS.D =>
      deletedRegionKeep deleted (RS.vertOf dart) ≠
        deletedRegionKeep deleted (RS.vertOf (RS.phi dart))).card) =
    ∑ face : OrbitFace RS,
      (orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) face).card
  rw [Finset.card_eq_sum_card_fiberwise
    (f := dartOrbitFace RS)
    (s := Finset.univ.filter fun dart : RS.D =>
      deletedRegionKeep deleted (RS.vertOf dart) ≠
        deletedRegionKeep deleted (RS.vertOf (RS.phi dart)))
    (t := Finset.univ) (by simp)]
  change (∑ face : OrbitFace RS,
      (((Finset.univ.filter fun dart : RS.D =>
        deletedRegionKeep deleted (RS.vertOf dart) ≠
          deletedRegionKeep deleted (RS.vertOf (RS.phi dart))).filter
        fun dart => dartOrbitFace RS dart = face).card) =
    ∑ face : OrbitFace RS,
      (orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) face).card)
  apply Finset.sum_congr rfl
  intro face _
  apply congrArg Finset.card
  ext dart
  simp [orbitFaceSideTransitionDarts, orbitFaceDarts, and_comm]

/-- Summed over quotient faces, transition multiplicity is exactly twice the
computed crossing-edge count. -/
theorem sum_card_orbitFaceSideTransitionDarts_eq_twice_crossingEdges
    (RS : RotationSystem V E) (deleted : Finset V) :
    (∑ face : OrbitFace RS,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card) =
      2 * (vertexSetCrossingEdges RS deleted).card := by
  rw [sum_card_orbitFaceSideTransitionDarts_eq_card_cutSideTransitionDart,
    card_cutSideTransitionDart_eq_twice_crossingEdges]

/-- At the quotient face of a representative, the quotient-fiber definition
of transition darts is the earlier face-orbit definition. -/
theorem orbitFaceSideTransitionDarts_dartOrbitFace
    (RS : RotationSystem V E) (side : V -> Prop) (root : RS.D) :
    orbitFaceSideTransitionDarts RS side (dartOrbitFace RS root) =
      faceSideTransitionDarts RS side root := by
  unfold orbitFaceSideTransitionDarts faceSideTransitionDarts
  rw [orbitFaceDarts_dartOrbitFace_eq_faceOrbit]

/-- Quotient faces touched by the vertex cut, computed by nonempty transition
fibers. -/
noncomputable def cutSideTransitionFaces
    (RS : RotationSystem V E) (deleted : Finset V) :
    Finset (OrbitFace RS) := by
  classical
  exact Finset.univ.filter fun face =>
    (orbitFaceSideTransitionDarts RS
      (deletedRegionKeep deleted) face).Nonempty

@[simp]
theorem mem_cutSideTransitionFaces_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (face : OrbitFace RS) :
    face ∈ cutSideTransitionFaces RS deleted <->
      (orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) face).Nonempty := by
  classical
  simp [cutSideTransitionFaces]

/-- Transition multiplicity on every quotient face is even. -/
theorem even_card_orbitFaceSideTransitionDarts
    (RS : RotationSystem V E) (side : V -> Prop) (face : OrbitFace RS) :
    Even (orbitFaceSideTransitionDarts RS side face).card := by
  rcases exists_dartOrbitFace_eq RS face with ⟨root, rfl⟩
  rw [orbitFaceSideTransitionDarts_dartOrbitFace,
    card_faceSideTransitionDarts_eq_twice_exitDarts]
  exact even_two_mul _

/-- A touched quotient face has at least one exit and one entry, hence at
least two side-transition darts. -/
theorem two_le_card_orbitFaceSideTransitionDarts_of_mem
    (RS : RotationSystem V E) (deleted : Finset V)
    (face : OrbitFace RS) (hface : face ∈ cutSideTransitionFaces RS deleted) :
    2 <= (orbitFaceSideTransitionDarts RS
      (deletedRegionKeep deleted) face).card := by
  have hpositive : 0 < (orbitFaceSideTransitionDarts RS
      (deletedRegionKeep deleted) face).card :=
    Finset.card_pos.2 ((mem_cutSideTransitionFaces_iff
      RS deleted face).1 hface)
  rcases even_card_orbitFaceSideTransitionDarts RS
      (deletedRegionKeep deleted) face with ⟨half, hhalf⟩
  omega

/-- Removing untouched zero fibers does not change the global transition
sum. -/
theorem sum_card_cutSideTransitionFaces_eq_allFaces
    (RS : RotationSystem V E) (deleted : Finset V) :
    (∑ face ∈ cutSideTransitionFaces RS deleted,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card) =
      ∑ face : OrbitFace RS,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card := by
  classical
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro face _ hnotTouched
    have hempty : orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) face = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.1
      simpa using hnotTouched
    simp [hempty]

/-- Since every touched face consumes at least two transition darts and the
cut supplies exactly two darts per crossing edge, there can be no more
touched faces than crossing edges. -/
theorem card_cutSideTransitionFaces_le_crossingEdges
    (RS : RotationSystem V E) (deleted : Finset V) :
    (cutSideTransitionFaces RS deleted).card <=
      (vertexSetCrossingEdges RS deleted).card := by
  have hlower : 2 * (cutSideTransitionFaces RS deleted).card <=
      ∑ face : OrbitFace RS,
        (orbitFaceSideTransitionDarts RS
          (deletedRegionKeep deleted) face).card := by
    calc
      2 * (cutSideTransitionFaces RS deleted).card =
          ∑ _face ∈ cutSideTransitionFaces RS deleted, 2 := by
        simp [Nat.mul_comm]
      _ <= ∑ face ∈ cutSideTransitionFaces RS deleted,
          (orbitFaceSideTransitionDarts RS
            (deletedRegionKeep deleted) face).card := by
        apply Finset.sum_le_sum
        intro face hface
        exact two_le_card_orbitFaceSideTransitionDarts_of_mem
          RS deleted face hface
      _ = ∑ face : OrbitFace RS,
          (orbitFaceSideTransitionDarts RS
            (deletedRegionKeep deleted) face).card :=
        sum_card_cutSideTransitionFaces_eq_allFaces RS deleted
  rw [sum_card_orbitFaceSideTransitionDarts_eq_twice_crossingEdges]
    at hlower
  omega

/-- The reverse face-count inequality is sufficient to turn the global
transition count into the pointwise planar-bond condition. -/
theorem cutFacesHaveAtMostTwoTransitions_of_crossingEdges_le_touchedFaces
    (RS : RotationSystem V E) (deleted : Finset V)
    (hlower : (vertexSetCrossingEdges RS deleted).card <=
      (cutSideTransitionFaces RS deleted).card) :
    CutFacesHaveAtMostTwoTransitionDarts RS deleted := by
  have hcards : (cutSideTransitionFaces RS deleted).card =
      (vertexSetCrossingEdges RS deleted).card :=
    Nat.le_antisymm
      (card_cutSideTransitionFaces_le_crossingEdges RS deleted) hlower
  have hsumTouched :
      (∑ face ∈ cutSideTransitionFaces RS deleted,
          (orbitFaceSideTransitionDarts RS
            (deletedRegionKeep deleted) face).card) =
        2 * (cutSideTransitionFaces RS deleted).card := by
    rw [sum_card_cutSideTransitionFaces_eq_allFaces,
      sum_card_orbitFaceSideTransitionDarts_eq_twice_crossingEdges,
      hcards]
  intro root
  rw [← orbitFaceSideTransitionDarts_dartOrbitFace]
  by_cases htouched : dartOrbitFace RS root ∈
      cutSideTransitionFaces RS deleted
  · by_contra hnot
    have hstrict : 2 < (orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) (dartOrbitFace RS root)).card := by
      omega
    have hsumStrict :
        (∑ _face ∈ cutSideTransitionFaces RS deleted, 2) <
          ∑ face ∈ cutSideTransitionFaces RS deleted,
            (orbitFaceSideTransitionDarts RS
              (deletedRegionKeep deleted) face).card := by
      apply Finset.sum_lt_sum
      · intro face hface
        exact two_le_card_orbitFaceSideTransitionDarts_of_mem
          RS deleted face hface
      · exact ⟨dartOrbitFace RS root, htouched, hstrict⟩
    have hconstant :
        (∑ _face ∈ cutSideTransitionFaces RS deleted, 2) =
          2 * (cutSideTransitionFaces RS deleted).card := by
      simp [Nat.mul_comm]
    rw [hconstant, hsumTouched] at hsumStrict
    exact (Nat.lt_irrefl _ hsumStrict)
  · have hempty : orbitFaceSideTransitionDarts RS
        (deletedRegionKeep deleted) (dartOrbitFace RS root) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.1
      simpa using htouched
    simp [hempty]

/-- Unique retained boundary occurrence on every touched face forces the
two complementary capped boundary orders to compose to the identity. -/
theorem retained_mul_deleted_boundarySuccessor_eq_one_of_cutFacesUnique
    (RS : RotationSystem V E) (deleted : Finset V)
    (hunique : CutFacesHaveUniqueRetainedBoundaryDart RS deleted) :
    retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) *
      deletedRegionBoundarySuccessor RS deleted = 1 := by
  apply Equiv.ext
  intro root
  simpa using (hunique root _
    (retained_mul_deleted_boundarySuccessor_sameAmbientFace
      RS deleted root)).symm

/-- Under the same computed face-occurrence condition, the retained capped
boundary order is exactly the inverse of the deleted capped boundary order. -/
theorem retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
    (RS : RotationSystem V E) (deleted : Finset V)
    (hunique : CutFacesHaveUniqueRetainedBoundaryDart RS deleted) :
    retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) =
      (deletedRegionBoundarySuccessor RS deleted)⁻¹ := by
  have hproduct :=
    retained_mul_deleted_boundarySuccessor_eq_one_of_cutFacesUnique
      RS deleted hunique
  calc
    retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) =
        retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) * 1 := by
      rw [mul_one]
    _ = retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) *
        (deletedRegionBoundarySuccessor RS deleted *
          (deletedRegionBoundarySuccessor RS deleted)⁻¹) := by
      rw [mul_inv_cancel]
    _ = (retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted) *
          deletedRegionBoundarySuccessor RS deleted) *
        (deletedRegionBoundarySuccessor RS deleted)⁻¹ := by
      rw [mul_assoc]
    _ = (deletedRegionBoundarySuccessor RS deleted)⁻¹ := by
      rw [hproduct, one_mul]

end

end GoertzelV24ComplementaryRegionBoundaryOrder

end Mettapedia.GraphTheory.FourColor

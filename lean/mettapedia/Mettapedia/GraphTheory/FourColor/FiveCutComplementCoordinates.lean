import Mettapedia.GraphTheory.FourColor.ExactSizedCyclicEdgeCut
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedRegionBoundaryOrder

/-!
# Complement coordinates of an exact five-edge cut

Boundary `alpha` identifies the outward boundary darts of the two shores of
an exact cyclic five-edge cut.  Transporting the first-return permutations
through this identification exchanges the deleted-side and retained-side
successors of complementary shores: the retained successor of the
complement is the deleted successor of the original cut, conjugated by
boundary `alpha`.  This is the single source of cross-shore orientation
truth used by the five-cut splice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace FiveCutComplementCoordinates

set_option maxRecDepth 100000

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

local instance graphEdgeSetDecidableEq
    {G : SimpleGraph V} [DecidableRel G.Adj] : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Membership in the complement cut's vertex side, phrased on the original
cut. -/
@[simp]
theorem mem_exactCutVertexSide_compl_iff
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) (vertex : V) :
    vertex ∈ exactCutVertexSide cut.compl ↔ ¬ cut.side vertex := by
  rw [mem_exactCutVertexSide_iff]
  exact Iff.rfl

def retainedDartEquivComplementDeleted
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    RetainedDart RS (deletedRegionKeep (exactCutVertexSide cut)) ≃
      DeletedBasedDart RS (exactCutVertexSide cut.compl) where
  toFun dart := ⟨dart.1, (mem_exactCutVertexSide_compl_iff cut _).mpr fun hside =>
    dart.2 ((mem_exactCutVertexSide_iff cut _).mpr hside)⟩
  invFun dart := ⟨dart.1, fun hmem =>
    (mem_exactCutVertexSide_compl_iff cut _).mp dart.2
      ((mem_exactCutVertexSide_iff cut _).mp hmem)⟩
  left_inv dart := rfl
  right_inv dart := rfl

@[simp]
theorem retainedDartEquivComplementDeleted_val
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : RetainedDart RS
      (deletedRegionKeep (exactCutVertexSide cut))) :
    (retainedDartEquivComplementDeleted RS cut dart).1 = dart.1 :=
  rfl

@[simp]
theorem retainedDartEquivComplementDeleted_symm_val
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : DeletedBasedDart RS (exactCutVertexSide cut.compl)) :
    ((retainedDartEquivComplementDeleted RS cut).symm dart).1 = dart.1 :=
  rfl

/-- The exposed-dart predicates agree under the preceding equivalence. -/
theorem retainedDartEquivComplementDeleted_hit_iff
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : RetainedDart RS
      (deletedRegionKeep (exactCutVertexSide cut))) :
    (¬ deletedRegionKeep (exactCutVertexSide cut)
        (RS.vertOf (RS.alpha dart.1))) ↔
      IsDeletedBoundaryHalfDart RS (exactCutVertexSide cut.compl)
        (retainedDartEquivComplementDeleted RS cut dart) := by
  constructor
  · intro hexposed hmem
    exact hexposed fun hmemA =>
      (mem_exactCutVertexSide_compl_iff cut _).mp hmem
        ((mem_exactCutVertexSide_iff cut _).mp hmemA)
  · intro hexposed hnotmem
    exact hexposed ((mem_exactCutVertexSide_compl_iff cut _).mpr
      fun hside => hnotmem ((mem_exactCutVertexSide_iff cut _).mpr hside))

/-- The capped face permutation of the old retained side is literally the
capped deleted-face permutation of the complementary cut after transport. -/
theorem deletedFacePerm_complement_eq_permCongr_retained
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    deletedFacePerm RS (exactCutVertexSide cut.compl) =
      (retainedDartEquivComplementDeleted RS cut).permCongr
        (retainedCappedFacePerm RS
          (deletedRegionKeep (exactCutVertexSide cut))) := by
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  have hrho : deletedRho RS (exactCutVertexSide cut.compl) =
      dartEquiv.permCongr
        (retainedRho RS (deletedRegionKeep (exactCutVertexSide cut))) := by
    apply Equiv.ext
    intro dart
    apply Subtype.ext
    rfl
  have halpha : deletedAlpha RS (exactCutVertexSide cut.compl) =
      dartEquiv.permCongr
        (retainedCappedAlpha RS
          (deletedRegionKeep (exactCutVertexSide cut))) := by
    apply Equiv.ext
    intro dart
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    by_cases hside : cut.side (RS.vertOf (RS.alpha dart.1))
    · have hcompNot : RS.vertOf (RS.alpha dart.1) ∉
          exactCutVertexSide cut.compl := fun hmem =>
        (mem_exactCutVertexSide_compl_iff cut _).mp hmem hside
      have hkeepNot : ¬ deletedRegionKeep (exactCutVertexSide cut)
          (RS.vertOf (RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1)) :=
        fun hnot => hnot ((mem_exactCutVertexSide_iff cut _).mpr hside)
      rw [deletedAlpha_apply_boundary RS _ dart hcompNot,
        retainedCappedAlpha_apply_boundary RS _ _ hkeepNot]
      rfl
    · have hcompMem : RS.vertOf (RS.alpha dart.1) ∈
          exactCutVertexSide cut.compl :=
        (mem_exactCutVertexSide_compl_iff cut _).mpr hside
      have hkeep : deletedRegionKeep (exactCutVertexSide cut)
          (RS.vertOf (RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1)) :=
        fun hmem => hside ((mem_exactCutVertexSide_iff cut _).mp hmem)
      rw [deletedAlpha_apply_internal RS _ dart hcompMem]
      calc
        RS.alpha dart.1 = RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1 := by
          rw [retainedDartEquivComplementDeleted_symm_val]
        _ = (retainedCappedAlpha RS
            (deletedRegionKeep (exactCutVertexSide cut))
              ((retainedDartEquivComplementDeleted RS cut).symm dart)).1 :=
          (retainedCappedAlpha_apply_internal RS _ _ hkeep).symm
        _ = (dartEquiv (retainedCappedAlpha RS
            (deletedRegionKeep (exactCutVertexSide cut))
              (dartEquiv.symm dart))).1 := by
          rfl
  rw [deletedFacePerm, retainedCappedFacePerm, hrho, halpha]
  exact (Equiv.permCongr_mul dartEquiv _ _).symm

/-- Reversing every crossing dart by ambient `alpha` identifies the two
boundary carriers of complementary cut sides. -/
def complementBoundaryAlphaEquiv
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    BoundaryDart RS (deletedRegionKeep (exactCutVertexSide cut)) ≃
      BoundaryDart RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) :=
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  let markedEquiv := dartEquiv.subtypeEquiv
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  markedEquiv.trans
    (deletedBoundaryHalfDartEquivBoundaryDart RS
      (exactCutVertexSide cut.compl))

@[simp]
theorem complementBoundaryAlphaEquiv_val
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : BoundaryDart RS
      (deletedRegionKeep (exactCutVertexSide cut))) :
    (complementBoundaryAlphaEquiv RS cut dart).1.1 =
      RS.alpha dart.1.1 := by
  rfl

/-- The deleted-side boundary successor of the complementary cut is the
old retained-side successor transported through boundary `alpha`. -/
theorem deletedRegionBoundarySuccessor_complement_eq_permCongr_retained
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    deletedRegionBoundarySuccessor RS (exactCutVertexSide cut.compl) =
      (complementBoundaryAlphaEquiv RS cut).permCongr
        (retainedRegionBoundarySuccessor RS
          (deletedRegionKeep (exactCutVertexSide cut))) := by
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  let hitRetained := fun dart : RetainedDart RS
      (deletedRegionKeep (exactCutVertexSide cut)) ↦
    ¬ deletedRegionKeep (exactCutVertexSide cut)
      (RS.vertOf (RS.alpha dart.1))
  let hitDeleted := IsDeletedBoundaryHalfDart RS
    (exactCutVertexSide cut.compl)
  let markedEquiv := dartEquiv.subtypeEquiv
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  let deletedBoundaryEquiv := deletedBoundaryHalfDartEquivBoundaryDart RS
    (exactCutVertexSide cut.compl)
  have hface := deletedFacePerm_complement_eq_permCongr_retained RS cut
  have hnext := nextHitPerm_permCongr dartEquiv
    (retainedCappedFacePerm RS
      (deletedRegionKeep (exactCutVertexSide cut)))
    hitRetained hitDeleted
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  change deletedBoundaryEquiv.permCongr
      (nextHitPerm (deletedFacePerm RS
        (exactCutVertexSide cut.compl)) hitDeleted) =
    (markedEquiv.trans deletedBoundaryEquiv).permCongr
      (nextHitPerm (retainedCappedFacePerm RS
        (deletedRegionKeep (exactCutVertexSide cut))) hitRetained)
  rw [hface, hnext]
  apply Equiv.ext
  intro boundary
  simp only [Equiv.permCongr_apply]
  simp [markedEquiv]

/-- Darts deleted by one cut side are retained by the complementary cut
side, again without changing their ambient representative. -/
def deletedDartEquivComplementRetained
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    DeletedBasedDart RS (exactCutVertexSide cut) ≃
      RetainedDart RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) where
  toFun dart := ⟨dart.1, fun hmem =>
    (mem_exactCutVertexSide_compl_iff cut _).mp hmem
      ((mem_exactCutVertexSide_iff cut _).mp dart.2)⟩
  invFun dart := ⟨dart.1, (mem_exactCutVertexSide_iff cut _).mpr
    (not_not.mp fun hns =>
      dart.2 ((mem_exactCutVertexSide_compl_iff cut _).mpr hns))⟩
  left_inv dart := rfl
  right_inv dart := rfl

@[simp]
theorem deletedDartEquivComplementRetained_val
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : DeletedBasedDart RS (exactCutVertexSide cut)) :
    (deletedDartEquivComplementRetained RS cut dart).1 = dart.1 :=
  rfl

@[simp]
theorem deletedDartEquivComplementRetained_symm_val
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : RetainedDart RS
      (deletedRegionKeep (exactCutVertexSide cut.compl))) :
    ((deletedDartEquivComplementRetained RS cut).symm dart).1 = dart.1 :=
  rfl

/-- The exposed predicates on the old deleted and new retained carriers
agree under the identity-on-darts equivalence. -/
theorem deletedDartEquivComplementRetained_hit_iff
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5)
    (dart : DeletedBasedDart RS (exactCutVertexSide cut)) :
    IsDeletedBoundaryHalfDart RS (exactCutVertexSide cut) dart ↔
      ¬ deletedRegionKeep (exactCutVertexSide cut.compl)
        (RS.vertOf (RS.alpha
          (deletedDartEquivComplementRetained RS cut dart).1)) := by
  constructor
  · intro hexposed hnotmem
    exact hnotmem ((mem_exactCutVertexSide_compl_iff cut _).mpr
      fun hside => hexposed ((mem_exactCutVertexSide_iff cut _).mpr hside))
  · intro hexposed hmem
    exact (mem_exactCutVertexSide_compl_iff cut _).mp (not_not.mp hexposed)
      ((mem_exactCutVertexSide_iff cut _).mp hmem)

/-- The old deleted-face permutation is the new retained-face permutation
after transport to the complementary carrier. -/
theorem retainedFacePerm_complement_eq_permCongr_deleted
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    retainedCappedFacePerm RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      (deletedDartEquivComplementRetained RS cut).permCongr
        (deletedFacePerm RS (exactCutVertexSide cut)) := by
  let dartEquiv := deletedDartEquivComplementRetained RS cut
  have hrho : retainedRho RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      dartEquiv.permCongr
        (deletedRho RS (exactCutVertexSide cut)) := by
    apply Equiv.ext
    intro dart
    apply Subtype.ext
    rfl
  have halpha : retainedCappedAlpha RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      dartEquiv.permCongr
        (deletedAlpha RS (exactCutVertexSide cut)) := by
    apply Equiv.ext
    intro dart
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    by_cases hside : cut.side (RS.vertOf (RS.alpha dart.1))
    · have hdeletedMem : RS.vertOf (RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1) ∈
          exactCutVertexSide cut :=
        (mem_exactCutVertexSide_iff cut _).mpr hside
      have hkeep : deletedRegionKeep (exactCutVertexSide cut.compl)
          (RS.vertOf (RS.alpha dart.1)) := fun hmem =>
        (mem_exactCutVertexSide_compl_iff cut _).mp hmem hside
      rw [retainedCappedAlpha_apply_internal RS _ dart hkeep]
      calc
        RS.alpha dart.1 = RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1 := by
          rw [deletedDartEquivComplementRetained_symm_val]
        _ = (deletedAlpha RS (exactCutVertexSide cut)
            ((deletedDartEquivComplementRetained RS cut).symm dart)).1 :=
          (deletedAlpha_apply_internal RS _ _ hdeletedMem).symm
        _ = (dartEquiv (deletedAlpha RS (exactCutVertexSide cut)
            (dartEquiv.symm dart))).1 := by
          rfl
    · have hdeletedNot : RS.vertOf (RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1) ∉
          exactCutVertexSide cut :=
        fun hmem => hside ((mem_exactCutVertexSide_iff cut _).mp hmem)
      have hkeepNot : ¬ deletedRegionKeep
          (exactCutVertexSide cut.compl)
            (RS.vertOf (RS.alpha dart.1)) :=
        fun hnot => hnot ((mem_exactCutVertexSide_compl_iff cut _).mpr hside)
      rw [retainedCappedAlpha_apply_boundary RS _ dart hkeepNot,
        deletedAlpha_apply_boundary RS _ _ hdeletedNot]
      rfl
  rw [retainedCappedFacePerm, deletedFacePerm, hrho, halpha]
  exact (Equiv.permCongr_mul dartEquiv _ _).symm

/-- The two descriptions of boundary `alpha`, from either side's marked
carrier, coincide. -/
theorem complementBoundaryAlphaEquiv_eq_deleted_trans_retained
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    complementBoundaryAlphaEquiv RS cut =
      (deletedBoundaryHalfDartEquivBoundaryDart RS
        (exactCutVertexSide cut)).symm.trans
        ((deletedDartEquivComplementRetained RS cut).subtypeEquiv
          (deletedDartEquivComplementRetained_hit_iff RS cut)) := by
  apply Equiv.ext
  intro boundary
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Symmetrically, the retained-side successor of the complementary cut is
the old deleted-side successor transported through boundary `alpha`. -/
theorem retainedRegionBoundarySuccessor_complement_eq_permCongr_deleted
    (RS : RotationSystem V E) {G : SimpleGraph V} [DecidableRel G.Adj]
    (cut : ExactSizedCyclicEdgeCut G 5) :
    retainedRegionBoundarySuccessor RS
        (deletedRegionKeep (exactCutVertexSide cut.compl)) =
      (complementBoundaryAlphaEquiv RS cut).permCongr
        (deletedRegionBoundarySuccessor RS
          (exactCutVertexSide cut)) := by
  let dartEquiv := deletedDartEquivComplementRetained RS cut
  let hitDeleted := IsDeletedBoundaryHalfDart RS
    (exactCutVertexSide cut)
  let hitRetained := fun dart : RetainedDart RS
      (deletedRegionKeep (exactCutVertexSide cut.compl)) ↦
    ¬ deletedRegionKeep (exactCutVertexSide cut.compl)
      (RS.vertOf (RS.alpha dart.1))
  let markedEquiv := dartEquiv.subtypeEquiv
    (p := hitDeleted) (q := hitRetained)
    (deletedDartEquivComplementRetained_hit_iff RS cut)
  let deletedBoundaryEquiv := deletedBoundaryHalfDartEquivBoundaryDart RS
    (exactCutVertexSide cut)
  have hface := retainedFacePerm_complement_eq_permCongr_deleted RS cut
  have hnext := nextHitPerm_permCongr dartEquiv
    (deletedFacePerm RS (exactCutVertexSide cut))
    hitDeleted hitRetained
    (deletedDartEquivComplementRetained_hit_iff RS cut)
  rw [complementBoundaryAlphaEquiv_eq_deleted_trans_retained RS cut]
  change nextHitPerm (retainedCappedFacePerm RS
      (deletedRegionKeep (exactCutVertexSide cut.compl))) hitRetained =
    (deletedBoundaryEquiv.symm.trans markedEquiv).permCongr
      (deletedBoundaryEquiv.permCongr
        (nextHitPerm (deletedFacePerm RS
          (exactCutVertexSide cut)) hitDeleted))
  rw [hface, hnext]
  apply Equiv.ext
  intro boundary
  simp only [Equiv.permCongr_apply]
  simp [markedEquiv]

end

end FiveCutComplementCoordinates

end Mettapedia.GraphTheory.FourColor

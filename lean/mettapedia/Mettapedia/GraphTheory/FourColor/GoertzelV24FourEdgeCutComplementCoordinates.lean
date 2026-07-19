import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutKempeEscape

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutComplementCoordinates

set_option maxRecDepth 100000

open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourEdgeCutClosureColor
open GoertzelV24FourEdgeCutKempeEscape
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutRetainedBridge
open GoertzelV24FourEdgeCutStateOverlap
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

/-- Darts retained by one cut side are the deleted-based darts of the
complementary cut side, without changing the underlying ambient dart. -/
def retainedDartEquivComplementDeleted
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    RetainedDart RS (deletedRegionKeep (cyclicCutVertexSide cut)) ≃
      DeletedBasedDart RS (cyclicCutVertexSide cut.compl) where
  toFun dart := ⟨dart.1, by
    simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
      SmallCyclicEdgeCut.compl] using dart.2⟩
  invFun dart := ⟨dart.1, by
    simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
      SmallCyclicEdgeCut.compl] using dart.2⟩
  left_inv dart := rfl
  right_inv dart := rfl

@[simp]
theorem retainedDartEquivComplementDeleted_val
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : RetainedDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (retainedDartEquivComplementDeleted RS cut dart).1 = dart.1 :=
  rfl

@[simp]
theorem retainedDartEquivComplementDeleted_symm_val
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : DeletedBasedDart RS (cyclicCutVertexSide cut.compl)) :
    ((retainedDartEquivComplementDeleted RS cut).symm dart).1 = dart.1 :=
  rfl

/-- The exposed-dart predicates agree under the preceding equivalence. -/
theorem retainedDartEquivComplementDeleted_hit_iff
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : RetainedDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (¬ deletedRegionKeep (cyclicCutVertexSide cut)
        (RS.vertOf (RS.alpha dart.1))) ↔
      IsDeletedBoundaryHalfDart RS (cyclicCutVertexSide cut.compl)
        (retainedDartEquivComplementDeleted RS cut dart) := by
  simp only [IsDeletedBoundaryHalfDart, deletedRegionKeep,
    mem_cyclicCutVertexSide_iff, SmallCyclicEdgeCut.compl, not_not]
  change cut.side (RS.vertOf (RS.alpha dart.1)) ↔
    cut.side (RS.vertOf (RS.alpha
      (retainedDartEquivComplementDeleted RS cut dart).1))
  rw [retainedDartEquivComplementDeleted_val]

/-- The capped face permutation of the old retained side is literally the
capped deleted-face permutation of the complementary cut after transport. -/
theorem deletedFacePerm_complement_eq_permCongr_retained
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    deletedFacePerm RS (cyclicCutVertexSide cut.compl) =
      (retainedDartEquivComplementDeleted RS cut).permCongr
        (retainedCappedFacePerm RS
          (deletedRegionKeep (cyclicCutVertexSide cut))) := by
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  have hrho : deletedRho RS (cyclicCutVertexSide cut.compl) =
      dartEquiv.permCongr
        (retainedRho RS (deletedRegionKeep (cyclicCutVertexSide cut))) := by
    apply Equiv.ext
    intro dart
    apply Subtype.ext
    rfl
  have halpha : deletedAlpha RS (cyclicCutVertexSide cut.compl) =
      dartEquiv.permCongr
        (retainedCappedAlpha RS
          (deletedRegionKeep (cyclicCutVertexSide cut))) := by
    apply Equiv.ext
    intro dart
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    by_cases hside : cut.side (RS.vertOf (RS.alpha dart.1))
    · have hcompNot : RS.vertOf (RS.alpha dart.1) ∉
          cyclicCutVertexSide cut.compl := by
        simpa [mem_cyclicCutVertexSide_iff,
          SmallCyclicEdgeCut.compl] using hside
      have hkeepNot : ¬ deletedRegionKeep (cyclicCutVertexSide cut)
          (RS.vertOf (RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1)) := by
        simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using hside
      rw [deletedAlpha_apply_boundary RS _ dart hcompNot,
        retainedCappedAlpha_apply_boundary RS _ _ hkeepNot]
      rfl
    · have hcompMem : RS.vertOf (RS.alpha dart.1) ∈
          cyclicCutVertexSide cut.compl := by
        simpa [mem_cyclicCutVertexSide_iff,
          SmallCyclicEdgeCut.compl] using hside
      have hkeep : deletedRegionKeep (cyclicCutVertexSide cut)
          (RS.vertOf (RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1)) := by
        simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using hside
      rw [deletedAlpha_apply_internal RS _ dart hcompMem]
      calc
        RS.alpha dart.1 = RS.alpha
            ((retainedDartEquivComplementDeleted RS cut).symm dart).1 := by
          rw [retainedDartEquivComplementDeleted_symm_val]
        _ = (retainedCappedAlpha RS
            (deletedRegionKeep (cyclicCutVertexSide cut))
              ((retainedDartEquivComplementDeleted RS cut).symm dart)).1 :=
          (retainedCappedAlpha_apply_internal RS _ _ hkeep).symm
        _ = (dartEquiv (retainedCappedAlpha RS
            (deletedRegionKeep (cyclicCutVertexSide cut))
              (dartEquiv.symm dart))).1 := by
          rfl
  rw [deletedFacePerm, retainedCappedFacePerm, hrho, halpha]
  exact (Equiv.permCongr_mul dartEquiv _ _).symm

/-- Reversing every crossing dart by ambient `alpha` identifies the two
boundary carriers of complementary cut sides. -/
def complementBoundaryAlphaEquiv
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    BoundaryDart RS (deletedRegionKeep (cyclicCutVertexSide cut)) ≃
      BoundaryDart RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) :=
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  let markedEquiv := dartEquiv.subtypeEquiv
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  markedEquiv.trans
    (deletedBoundaryHalfDartEquivBoundaryDart RS
      (cyclicCutVertexSide cut.compl))

@[simp]
theorem complementBoundaryAlphaEquiv_val
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : BoundaryDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut))) :
    (complementBoundaryAlphaEquiv RS cut dart).1.1 =
      RS.alpha dart.1.1 := by
  rfl

/-- The deleted-side boundary successor of the complementary cut is the
old retained-side successor transported through boundary `alpha`. -/
theorem deletedRegionBoundarySuccessor_complement_eq_permCongr_retained
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    deletedRegionBoundarySuccessor RS (cyclicCutVertexSide cut.compl) =
      (complementBoundaryAlphaEquiv RS cut).permCongr
        (retainedRegionBoundarySuccessor RS
          (deletedRegionKeep (cyclicCutVertexSide cut))) := by
  let dartEquiv := retainedDartEquivComplementDeleted RS cut
  let hitRetained := fun dart : RetainedDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut)) ↦
    ¬ deletedRegionKeep (cyclicCutVertexSide cut)
      (RS.vertOf (RS.alpha dart.1))
  let hitDeleted := IsDeletedBoundaryHalfDart RS
    (cyclicCutVertexSide cut.compl)
  let markedEquiv := dartEquiv.subtypeEquiv
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  let deletedBoundaryEquiv := deletedBoundaryHalfDartEquivBoundaryDart RS
    (cyclicCutVertexSide cut.compl)
  have hface := deletedFacePerm_complement_eq_permCongr_retained RS cut
  have hnext := nextHitPerm_permCongr dartEquiv
    (retainedCappedFacePerm RS
      (deletedRegionKeep (cyclicCutVertexSide cut)))
    hitRetained hitDeleted
    (retainedDartEquivComplementDeleted_hit_iff RS cut)
  change deletedBoundaryEquiv.permCongr
      (nextHitPerm (deletedFacePerm RS
        (cyclicCutVertexSide cut.compl)) hitDeleted) =
    (markedEquiv.trans deletedBoundaryEquiv).permCongr
      (nextHitPerm (retainedCappedFacePerm RS
        (deletedRegionKeep (cyclicCutVertexSide cut))) hitRetained)
  rw [hface, hnext]
  apply Equiv.ext
  intro boundary
  simp only [Equiv.permCongr_apply]
  simp [markedEquiv]

/-- Darts deleted by one cut side are retained by the complementary cut
side, again without changing their ambient representative. -/
def deletedDartEquivComplementRetained
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    DeletedBasedDart RS (cyclicCutVertexSide cut) ≃
      RetainedDart RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) where
  toFun dart := ⟨dart.1, by
    simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
      SmallCyclicEdgeCut.compl] using dart.2⟩
  invFun dart := ⟨dart.1, by
    simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
      SmallCyclicEdgeCut.compl] using dart.2⟩
  left_inv dart := rfl
  right_inv dart := rfl

@[simp]
theorem deletedDartEquivComplementRetained_val
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : DeletedBasedDart RS (cyclicCutVertexSide cut)) :
    (deletedDartEquivComplementRetained RS cut dart).1 = dart.1 :=
  rfl

@[simp]
theorem deletedDartEquivComplementRetained_symm_val
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : RetainedDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut.compl))) :
    ((deletedDartEquivComplementRetained RS cut).symm dart).1 = dart.1 :=
  rfl

/-- The exposed predicates on the old deleted and new retained carriers
agree under the identity-on-darts equivalence. -/
theorem deletedDartEquivComplementRetained_hit_iff
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G)
    (dart : DeletedBasedDart RS (cyclicCutVertexSide cut)) :
    IsDeletedBoundaryHalfDart RS (cyclicCutVertexSide cut) dart ↔
      ¬ deletedRegionKeep (cyclicCutVertexSide cut.compl)
        (RS.vertOf (RS.alpha
          (deletedDartEquivComplementRetained RS cut dart).1)) := by
  simp only [IsDeletedBoundaryHalfDart, deletedRegionKeep,
    mem_cyclicCutVertexSide_iff, SmallCyclicEdgeCut.compl, not_not]
  change (¬ cut.side (RS.vertOf (RS.alpha dart.1))) ↔
    ¬ cut.side (RS.vertOf (RS.alpha
      (deletedDartEquivComplementRetained RS cut dart).1))
  rw [deletedDartEquivComplementRetained_val]

/-- The old deleted-face permutation is the new retained-face permutation
after transport to the complementary carrier. -/
theorem retainedFacePerm_complement_eq_permCongr_deleted
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    retainedCappedFacePerm RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) =
      (deletedDartEquivComplementRetained RS cut).permCongr
        (deletedFacePerm RS (cyclicCutVertexSide cut)) := by
  let dartEquiv := deletedDartEquivComplementRetained RS cut
  have hrho : retainedRho RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) =
      dartEquiv.permCongr
        (deletedRho RS (cyclicCutVertexSide cut)) := by
    apply Equiv.ext
    intro dart
    apply Subtype.ext
    rfl
  have halpha : retainedCappedAlpha RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) =
      dartEquiv.permCongr
        (deletedAlpha RS (cyclicCutVertexSide cut)) := by
    apply Equiv.ext
    intro dart
    rw [Equiv.permCongr_apply]
    apply Subtype.ext
    by_cases hside : cut.side (RS.vertOf (RS.alpha dart.1))
    · have hdeletedMem : RS.vertOf (RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1) ∈
          cyclicCutVertexSide cut := by
        simpa [mem_cyclicCutVertexSide_iff] using hside
      have hkeep : deletedRegionKeep (cyclicCutVertexSide cut.compl)
          (RS.vertOf (RS.alpha dart.1)) := by
        simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
          SmallCyclicEdgeCut.compl] using hside
      rw [retainedCappedAlpha_apply_internal RS _ dart hkeep]
      calc
        RS.alpha dart.1 = RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1 := by
          rw [deletedDartEquivComplementRetained_symm_val]
        _ = (deletedAlpha RS (cyclicCutVertexSide cut)
            ((deletedDartEquivComplementRetained RS cut).symm dart)).1 :=
          (deletedAlpha_apply_internal RS _ _ hdeletedMem).symm
        _ = (dartEquiv (deletedAlpha RS (cyclicCutVertexSide cut)
            (dartEquiv.symm dart))).1 := by
          rfl
    · have hdeletedNot : RS.vertOf (RS.alpha
            ((deletedDartEquivComplementRetained RS cut).symm dart).1) ∉
          cyclicCutVertexSide cut := by
        simpa [mem_cyclicCutVertexSide_iff] using hside
      have hkeepNot : ¬ deletedRegionKeep
          (cyclicCutVertexSide cut.compl)
            (RS.vertOf (RS.alpha dart.1)) := by
        simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff,
          SmallCyclicEdgeCut.compl] using hside
      rw [retainedCappedAlpha_apply_boundary RS _ dart hkeepNot,
        deletedAlpha_apply_boundary RS _ _ hdeletedNot]
      rfl
  rw [retainedCappedFacePerm, deletedFacePerm, hrho, halpha]
  exact (Equiv.permCongr_mul dartEquiv _ _).symm

/-- The two descriptions of boundary `alpha`, from either side's marked
carrier, coincide. -/
theorem complementBoundaryAlphaEquiv_eq_deleted_trans_retained
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    complementBoundaryAlphaEquiv RS cut =
      (deletedBoundaryHalfDartEquivBoundaryDart RS
        (cyclicCutVertexSide cut)).symm.trans
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
    (RS : RotationSystem V E) {G : SimpleGraph V}
    (cut : SmallCyclicEdgeCut G) :
    retainedRegionBoundarySuccessor RS
        (deletedRegionKeep (cyclicCutVertexSide cut.compl)) =
      (complementBoundaryAlphaEquiv RS cut).permCongr
        (deletedRegionBoundarySuccessor RS
          (cyclicCutVertexSide cut)) := by
  let dartEquiv := deletedDartEquivComplementRetained RS cut
  let hitDeleted := IsDeletedBoundaryHalfDart RS
    (cyclicCutVertexSide cut)
  let hitRetained := fun dart : RetainedDart RS
      (deletedRegionKeep (cyclicCutVertexSide cut.compl)) ↦
    ¬ deletedRegionKeep (cyclicCutVertexSide cut.compl)
      (RS.vertOf (RS.alpha dart.1))
  let markedEquiv := dartEquiv.subtypeEquiv
    (p := hitDeleted) (q := hitRetained)
    (deletedDartEquivComplementRetained_hit_iff RS cut)
  let deletedBoundaryEquiv := deletedBoundaryHalfDartEquivBoundaryDart RS
    (cyclicCutVertexSide cut)
  have hface := retainedFacePerm_complement_eq_permCongr_deleted RS cut
  have hnext := nextHitPerm_permCongr dartEquiv
    (deletedFacePerm RS (cyclicCutVertexSide cut))
    hitDeleted hitRetained
    (deletedDartEquivComplementRetained_hit_iff RS cut)
  rw [complementBoundaryAlphaEquiv_eq_deleted_trans_retained RS cut]
  change nextHitPerm (retainedCappedFacePerm RS
      (deletedRegionKeep (cyclicCutVertexSide cut.compl))) hitRetained =
    (deletedBoundaryEquiv.symm.trans markedEquiv).permCongr
      (deletedBoundaryEquiv.permCongr
        (nextHitPerm (deletedFacePerm RS
          (cyclicCutVertexSide cut)) hitDeleted))
  rw [hface, hnext]
  apply Equiv.ext
  intro boundary
  simp only [Equiv.permCongr_apply]
  simp [markedEquiv]

/-- Conjugation along a composite equivalence is successive conjugation. -/
theorem permCongr_trans_equiv
    {A B C : Type*} (first : A ≃ B) (second : B ≃ C)
    (perm : Equiv.Perm A) :
    (first.trans second).permCongr perm =
      second.permCongr (first.permCongr perm) := by
  apply Equiv.ext
  intro point
  rfl

/-- Conjugation preserves inversion. -/
theorem permCongr_inv
    {A B : Type*} (equiv : A ≃ B) (perm : Equiv.Perm A) :
    equiv.permCongr (perm⁻¹) = (equiv.permCongr perm)⁻¹ := by
  exact equiv.permCongrHom.map_inv perm

/-- Negation reflects the positive four-cycle to its inverse. -/
theorem negFinFour_permCongr_finRotate :
    (Equiv.neg (Fin 4)).permCongr (finRotate 4) =
      (finRotate 4)⁻¹ := by
  decide

/-- A common cyclic boundary coordinate system canonically induces the
reflected common coordinate system for the complementary cut. Boundary
`alpha` changes sides, while negation reverses the cyclic orientation. -/
def complementCyclicFourBoundaryData
    {G : SimpleGraph V} {RS : RotationSystem V E}
    {cut : SmallCyclicEdgeCut G}
    (data : CyclicFourBoundaryData RS (cyclicCutVertexSide cut)) :
    CyclicFourBoundaryData RS (cyclicCutVertexSide cut.compl) := by
  let reflection : Fin 4 ≃ Fin 4 := Equiv.neg (Fin 4)
  let boundaryAlpha := complementBoundaryAlphaEquiv RS cut
  let boundaryOrder :=
    (reflection.trans data.boundaryOrder).trans boundaryAlpha
  refine
    { boundaryOrder := boundaryOrder
      deleted_order := ?_
      retained_order := ?_ }
  · rw [deletedRegionBoundarySuccessor_complement_eq_permCongr_retained,
      data.retained_order]
    rw [show boundaryOrder =
        (reflection.trans data.boundaryOrder).trans boundaryAlpha from rfl]
    rw [permCongr_trans_equiv (reflection.trans data.boundaryOrder)
        boundaryAlpha,
      permCongr_trans_equiv reflection data.boundaryOrder,
      show reflection.permCongr (finRotate 4) =
          (finRotate 4)⁻¹ by
        exact negFinFour_permCongr_finRotate,
      permCongr_inv data.boundaryOrder]
  · rw [retainedRegionBoundarySuccessor_complement_eq_permCongr_deleted,
      data.deleted_order]
    rw [show boundaryOrder =
        (reflection.trans data.boundaryOrder).trans boundaryAlpha from rfl]
    rw [permCongr_trans_equiv (reflection.trans data.boundaryOrder)
        boundaryAlpha,
      permCongr_trans_equiv reflection data.boundaryOrder,
      show reflection.permCongr (finRotate 4) =
          (finRotate 4)⁻¹ by
        exact negFinFour_permCongr_finRotate,
      permCongr_inv data.boundaryOrder,
      permCongr_inv boundaryAlpha, inv_inv]

@[simp]
theorem complementCyclicFourBoundaryData_boundaryOrder
    {G : SimpleGraph V} {RS : RotationSystem V E}
    {cut : SmallCyclicEdgeCut G}
    (data : CyclicFourBoundaryData RS (cyclicCutVertexSide cut))
    (port : Fin 4) :
    ((complementCyclicFourBoundaryData data).boundaryOrder port).1.1 =
      RS.alpha (data.boundaryOrder (-port)).1.1 := by
  rfl

/-- Reflect a square boundary word across ports `0` and `2`. -/
def reflectSquareBoundaryWord (word : SquareBoundaryWord) :
    SquareBoundaryWord :=
  fun port ↦ word (-port)

@[simp]
theorem reflectSquareBoundaryWord_apply
    (word : SquareBoundaryWord) (port : Fin 4) :
    reflectSquareBoundaryWord word port = word (-port) :=
  rfl

@[simp]
theorem reflectSquareBoundaryWord_involutive
    (word : SquareBoundaryWord) :
    reflectSquareBoundaryWord (reflectSquareBoundaryWord word) = word := by
  funext port
  simp [reflectSquareBoundaryWord]

theorem reflectSquareBoundaryWord_nonzero :
    ∀ word : SquareBoundaryWord,
      (reflectSquareBoundaryWord word).Nonzero ↔ word.Nonzero := by
  decide

theorem reflectSquareBoundaryWord_allEqual :
    ∀ word : SquareBoundaryWord,
      (reflectSquareBoundaryWord word).AllEqual ↔ word.AllEqual := by
  decide

theorem reflectSquareBoundaryWord_adjacent01_23 :
    ∀ word : SquareBoundaryWord,
      (reflectSquareBoundaryWord word).Adjacent01_23 ↔
        word.Adjacent12_30 := by
  decide

theorem reflectSquareBoundaryWord_adjacent12_30 :
    ∀ word : SquareBoundaryWord,
      (reflectSquareBoundaryWord word).Adjacent12_30 ↔
        word.Adjacent01_23 := by
  decide

theorem reflectSquareBoundaryWord_join01_23 :
    ∀ word : SquareBoundaryWord,
      SquareReductionSide.join01_23.Compatible
          (reflectSquareBoundaryWord word) ↔
        SquareReductionSide.join12_30.Compatible word := by
  decide

theorem reflectSquareBoundaryWord_join12_30 :
    ∀ word : SquareBoundaryWord,
      SquareReductionSide.join12_30.Compatible
          (reflectSquareBoundaryWord word) ↔
        SquareReductionSide.join01_23.Compatible word := by
  decide

/-- Reflection preserves a noncrossing four-pole profile, exchanging its
two adjacent seam classes. -/
def reflectNoncrossingFourPoleStateProfile
    (profile : NoncrossingFourPoleStateProfile) :
    NoncrossingFourPoleStateProfile where
  states := reflectSquareBoundaryWord '' profile.states
  nonzero := by
    rintro _ ⟨word, hword, rfl⟩
    exact (reflectSquareBoundaryWord_nonzero word).2
      (profile.nonzero word hword)
  join01_23 := by
    rcases profile.join12_30 with ⟨word, hword, hcompatible⟩
    exact ⟨reflectSquareBoundaryWord word, ⟨word, hword, rfl⟩,
      (reflectSquareBoundaryWord_join01_23 word).2 hcompatible⟩
  join12_30 := by
    rcases profile.join01_23 with ⟨word, hword, hcompatible⟩
    exact ⟨reflectSquareBoundaryWord word, ⟨word, hword, rfl⟩,
      (reflectSquareBoundaryWord_join12_30 word).2 hcompatible⟩
  allEqualKempeEscape := by
    rintro ⟨_, ⟨word, hword, rfl⟩, hall⟩
    have hsourceAll : word.AllEqual :=
      (reflectSquareBoundaryWord_allEqual word).1 hall
    rcases profile.allEqualKempeEscape
        ⟨word, hword, hsourceAll⟩ with h01 | h12
    · rcases h01 with ⟨next, hnext, hclass⟩
      exact Or.inr ⟨reflectSquareBoundaryWord next,
        ⟨next, hnext, rfl⟩,
        (reflectSquareBoundaryWord_adjacent12_30 next).2 hclass⟩
    · rcases h12 with ⟨next, hnext, hclass⟩
      exact Or.inl ⟨reflectSquareBoundaryWord next,
        ⟨next, hnext, rfl⟩,
        (reflectSquareBoundaryWord_adjacent01_23 next).2 hclass⟩

@[simp]
theorem mem_reflectNoncrossingFourPoleStateProfile_states
    (profile : NoncrossingFourPoleStateProfile)
    (word : SquareBoundaryWord) :
    word ∈ (reflectNoncrossingFourPoleStateProfile profile).states ↔
      ∃ source ∈ profile.states,
        reflectSquareBoundaryWord source = word := by
  rfl

/-- The two genuine sides of an exact cyclic four-edge cut admit Tait
colorings whose missing-color boundary words agree after one global
zero-fixing color permutation. Complementary ports are compared through
the orientation-reversing correspondence `port ↦ -port`. -/
theorem exists_aligned_complementary_retainedCutColorings
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) :
    ∃ (leftColoring : (retainedCutGraph G cut).EdgeColoring Color)
      (rightColoring : (retainedCutGraph G cut.compl).EdgeColoring Color)
      (colorEquiv : Color ≃ Color),
      IsTaitEdgeColoring (retainedCutGraph G cut) leftColoring ∧
      IsTaitEdgeColoring (retainedCutGraph G cut.compl) rightColoring ∧
      colorEquiv 0 = 0 ∧
      ∀ port : Fin 4,
        colorEquiv
            ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
              leftColoring port) =
          (commonRetainedBoundaryData graphData cut.compl
              (complementCyclicFourBoundaryData cyclicData)).colorWord
            rightColoring (-port) := by
  let complementData := complementCyclicFourBoundaryData cyclicData
  let leftProfile :=
    commonRetainedStateProfile graphData minimal cut hcard cyclicData
  let rightSourceProfile :=
    commonRetainedStateProfile graphData minimal cut.compl
      (by simpa using hcard) complementData
  let rightProfile :=
    reflectNoncrossingFourPoleStateProfile rightSourceProfile
  rcases leftProfile.exists_aligned_common_boundary_words rightProfile with
    ⟨_boundaryClass, leftWord, rightWord, colorEquiv, _hclass,
      hleftWord, hrightWord, _hleftClass, _hrightClass, hzero, halign⟩
  change leftWord ∈ commonRetainedStateSet graphData cut cyclicData at hleftWord
  rcases hleftWord with ⟨leftColoring, hleftColoring, hleftWord⟩
  have hrightReflected :
      ∃ sourceWord ∈ rightSourceProfile.states,
        reflectSquareBoundaryWord sourceWord = rightWord :=
    (mem_reflectNoncrossingFourPoleStateProfile_states
      rightSourceProfile rightWord).1 hrightWord
  rcases hrightReflected with
    ⟨sourceWord, hsourceWord, hrightWordEq⟩
  change sourceWord ∈ commonRetainedStateSet graphData cut.compl
    complementData at hsourceWord
  rcases hsourceWord with
    ⟨rightColoring, hrightColoring, hsourceWordEq⟩
  refine ⟨leftColoring, rightColoring, colorEquiv,
    hleftColoring, hrightColoring, hzero, ?_⟩
  intro port
  have hport := halign port
  rw [← hleftWord, ← hrightWordEq, ← hsourceWordEq] at hport
  simpa [complementData, reflectSquareBoundaryWord] using hport

end

end GoertzelV24FourEdgeCutComplementCoordinates

end Mettapedia.GraphTheory.FourColor

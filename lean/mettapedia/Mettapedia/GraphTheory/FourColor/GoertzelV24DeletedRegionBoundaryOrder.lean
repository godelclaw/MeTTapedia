import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionEuler
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DeletedRegionBoundaryOrder

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Ambient darts based at vertices in the finite deleted region. -/
def DeletedBasedDart (RS : RotationSystem V E) (deleted : Finset V) :=
  {dart : RS.D // RS.vertOf dart ∈ deleted}

noncomputable instance deletedBasedDartFintype
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype (DeletedBasedDart RS deleted) :=
  Fintype.ofInjective
    (fun dart : DeletedBasedDart RS deleted => dart.1)
    Subtype.val_injective

instance deletedBasedDartDecidableEq
    (RS : RotationSystem V E) (deleted : Finset V) :
    DecidableEq (DeletedBasedDart RS deleted) :=
  Classical.decEq _

/-- Vertex rotation restricts to darts based in the deleted region. -/
def deletedRho (RS : RotationSystem V E) (deleted : Finset V) :
    Equiv.Perm (DeletedBasedDart RS deleted) :=
  RS.rho.subtypePerm fun dart => by rw [RS.vert_rho]

@[simp]
theorem deletedRho_val
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted) :
    (deletedRho RS deleted dart).1 = RS.rho dart.1 :=
  rfl

/-- The deleted-side edge flip crosses an internal deleted edge and fixes an
exposed half-dart. It is the standard capped involution of the ribbon submap
induced by the deleted vertices. -/
def deletedAlphaFun
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted) :
    DeletedBasedDart RS deleted :=
  if hopposite : RS.vertOf (RS.alpha dart.1) ∈ deleted then
    ⟨RS.alpha dart.1, hopposite⟩
  else dart

/-- The capped deleted-side flip is involutive. -/
theorem deletedAlphaFun_involutive
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted) :
    deletedAlphaFun RS deleted (deletedAlphaFun RS deleted dart) = dart := by
  by_cases hopposite : RS.vertOf (RS.alpha dart.1) ∈ deleted
  · apply Subtype.ext
    simp [deletedAlphaFun, hopposite, dart.2, RS.alpha_involutive]
  · simp [deletedAlphaFun, hopposite]

/-- Capped alpha as a permutation of deleted-based darts. -/
def deletedAlpha (RS : RotationSystem V E) (deleted : Finset V) :
    Equiv.Perm (DeletedBasedDart RS deleted) where
  toFun := deletedAlphaFun RS deleted
  invFun := deletedAlphaFun RS deleted
  left_inv := deletedAlphaFun_involutive RS deleted
  right_inv := deletedAlphaFun_involutive RS deleted

@[simp]
theorem deletedAlpha_apply_internal
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted)
    (hopposite : RS.vertOf (RS.alpha dart.1) ∈ deleted) :
    (deletedAlpha RS deleted dart).1 = RS.alpha dart.1 := by
  simp [deletedAlpha, deletedAlphaFun, hopposite]

@[simp]
theorem deletedAlpha_apply_boundary
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted)
    (hopposite : RS.vertOf (RS.alpha dart.1) ∉ deleted) :
    deletedAlpha RS deleted dart = dart := by
  simp [deletedAlpha, deletedAlphaFun, hopposite]

/-- Face walk of the capped deleted-side ribbon submap. -/
def deletedFacePerm (RS : RotationSystem V E) (deleted : Finset V) :
    Equiv.Perm (DeletedBasedDart RS deleted) :=
  deletedRho RS deleted * deletedAlpha RS deleted

/-- A deleted-based half-dart is exposed when its old opposite endpoint is
retained. -/
def IsDeletedBoundaryHalfDart
    (RS : RotationSystem V E) (deleted : Finset V)
    (dart : DeletedBasedDart RS deleted) : Prop :=
  RS.vertOf (RS.alpha dart.1) ∉ deleted

/-- Exposed half-darts on the deleted side. -/
abbrev DeletedBoundaryHalfDart
    (RS : RotationSystem V E) (deleted : Finset V) :=
  {dart : DeletedBasedDart RS deleted //
    IsDeletedBoundaryHalfDart RS deleted dart}

/-- Alpha reverses a deleted-side exposed half-dart into the uniquely retained
boundary dart used by the shortening splice. -/
def deletedBoundaryHalfDartEquivBoundaryDart
    (RS : RotationSystem V E) (deleted : Finset V) :
    DeletedBoundaryHalfDart RS deleted ≃
      BoundaryDart RS (deletedRegionKeep deleted) where
  toFun dart :=
    ⟨⟨RS.alpha dart.1.1, dart.2⟩, by
      simpa [deletedRegionKeep, RS.alpha_involutive] using dart.1.2⟩
  invFun dart :=
    ⟨⟨RS.alpha dart.1.1, by
      simpa [deletedRegionKeep] using dart.2⟩, by
        simpa [IsDeletedBoundaryHalfDart, deletedRegionKeep,
          RS.alpha_involutive] using dart.1.2⟩
  left_inv dart := by
    apply Subtype.ext
    apply Subtype.ext
    exact RS.alpha_involutive dart.1.1
  right_inv dart := by
    apply Subtype.ext
    apply Subtype.ext
    exact RS.alpha_involutive dart.1.1

/-- The computed cyclic boundary order of a finite deleted region. It follows
the capped deleted-side face walk from one exposed half-dart to the next and
transports the result to the retained boundary-dart carrier used by splice. -/
def deletedRegionBoundarySuccessor
    (RS : RotationSystem V E) (deleted : Finset V) :
    Equiv.Perm (BoundaryDart RS (deletedRegionKeep deleted)) :=
  (deletedBoundaryHalfDartEquivBoundaryDart RS deleted).permCongr
    (nextHitPerm (deletedFacePerm RS deleted)
      (IsDeletedBoundaryHalfDart RS deleted))

/-- The boundary successor has exactly the capped deleted-side first-return
cycle relation. -/
theorem deletedRegionBoundarySuccessor_sameCycle_iff
    (RS : RotationSystem V E) (deleted : Finset V)
    (first second : DeletedBoundaryHalfDart RS deleted) :
    (deletedRegionBoundarySuccessor RS deleted).SameCycle
        (deletedBoundaryHalfDartEquivBoundaryDart RS deleted first)
        (deletedBoundaryHalfDartEquivBoundaryDart RS deleted second) ↔
      (deletedFacePerm RS deleted).SameCycle first.1 second.1 := by
  rw [deletedRegionBoundarySuccessor, permCongr_sameCycle_iff,
    nextHitPerm_sameCycle_iff]

/-- Actual retained boundary darts are canonically indexed by the computed
crossing-edge finset. -/
def boundaryDartEquivVertexSetCrossingEdge
    (RS : RotationSystem V E) (deleted : Finset V) :
    BoundaryDart RS (deletedRegionKeep deleted) ≃
      VertexSetCrossingEdge RS deleted where
  toFun dart :=
    ⟨RS.edgeOf dart.1.1,
      boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted dart⟩
  invFun edge :=
    ⟨⟨Classical.choose
          (exists_outward_dart_of_mem_vertexSetCrossingEdges
            RS deleted edge.2),
        (Classical.choose_spec
          (exists_outward_dart_of_mem_vertexSetCrossingEdges
            RS deleted edge.2)).2.1⟩,
      (Classical.choose_spec
        (exists_outward_dart_of_mem_vertexSetCrossingEdges
          RS deleted edge.2)).2.2⟩
  left_inv dart := by
    apply boundaryDart_eq_of_edgeOf_eq
    exact (Classical.choose_spec
      (exists_outward_dart_of_mem_vertexSetCrossingEdges RS deleted
        (boundaryDart_edge_mem_vertexSetCrossingEdges RS deleted dart))).1
  right_inv edge := by
    apply Subtype.ext
    exact (Classical.choose_spec
      (exists_outward_dart_of_mem_vertexSetCrossingEdges
        RS deleted edge.2)).1

/-- Hence the computed deleted-region boundary-order carrier has exactly one
point for every endpoint-computed crossing edge. -/
theorem card_boundaryDart_deletedRegionKeep
    (RS : RotationSystem V E) (deleted : Finset V) :
    Fintype.card (BoundaryDart RS (deletedRegionKeep deleted)) =
      (vertexSetCrossingEdges RS deleted).card := by
  rw [Fintype.card_congr
    (boundaryDartEquivVertexSetCrossingEdge RS deleted)]
  exact Fintype.card_coe _

/-- Coordinate order `left 0, ..., left (n-1), right (n-1), ..., right 0`
on two ordered cut interfaces. -/
def oppositeBoundaryPositionEquiv (n : Nat) :
    OrderedSeamPosition n ≃ Fin (n + n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) Fin.revPerm).trans
    finSumFinEquiv

/-- One positive cyclic step in the opposite-order boundary coordinates. -/
def oppositeBoundaryCycle (n : Nat) :
    Equiv.Perm (OrderedSeamPosition n) :=
  (oppositeBoundaryPositionEquiv n).symm.permCongr (finRotate (n + n))

/-- The seam matching on ordered positions: equal indices on the two cuts are
paired. -/
def orderedPositionSeamSwap (n : Nat) :
    Equiv.Perm (OrderedSeamPosition n) :=
  MatchedSeam.seamSwap (Equiv.refl (Fin n))

/-- In opposite boundary coordinates, equal-index seam matching is precisely
the reversal involution. Thus its chords are nested rather than crossing. -/
theorem oppositeBoundaryPosition_seamSwap_eq_revPerm (n : Nat) :
    (oppositeBoundaryPositionEquiv n).permCongr
        (orderedPositionSeamSwap n) =
      Fin.revPerm := by
  ext position
  rcases position with ⟨position, hposition⟩
  by_cases hleft : position < n
  · let index : Fin n := ⟨position, hleft⟩
    have hsource :
        (oppositeBoundaryPositionEquiv n).symm
            ⟨position, hposition⟩ = Sum.inl index := by
      apply (oppositeBoundaryPositionEquiv n).symm_apply_eq.mpr
      apply Fin.ext
      rfl
    rw [Equiv.permCongr_apply, hsource]
    simp [orderedPositionSeamSwap, oppositeBoundaryPositionEquiv,
      MatchedSeam.seamSwap, finSumFinEquiv, index, Fin.revPerm, Fin.rev]
    omega
  · have hright : n ≤ position := Nat.le_of_not_gt hleft
    let offset : Fin n := ⟨position - n, by omega⟩
    let index : Fin n := Fin.rev offset
    have hsource :
        (oppositeBoundaryPositionEquiv n).symm
            ⟨position, hposition⟩ = Sum.inr index := by
      apply (oppositeBoundaryPositionEquiv n).symm_apply_eq.mpr
      apply Fin.ext
      simp [oppositeBoundaryPositionEquiv, index, offset,
        finSumFinEquiv, Fin.revPerm, Fin.rev]
      omega
    rw [Equiv.permCongr_apply, hsource]
    simp [orderedPositionSeamSwap, oppositeBoundaryPositionEquiv,
      MatchedSeam.seamSwap, finSumFinEquiv, index, offset,
      Fin.revPerm, Fin.rev]
    omega

/-- A positive cyclic step followed by reversal is negation in cyclic
coordinates. This identifies the face permutation created by capping one
oppositely ordered boundary with the elementary reflection of `Fin m`. -/
theorem finRotate_mul_revPerm_eq_neg (m : Nat) :
    finRotate m * Fin.revPerm =
      (Equiv.neg (Fin m) : Equiv.Perm (Fin m)) := by
  cases m with
  | zero => exact Subsingleton.elim _ _
  | succ k =>
      apply Equiv.ext
      intro position
      simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply, finRotate_apply,
        Equiv.neg_apply]
      rw [← Fin.last_sub]
      have hlast : Fin.last k = -(1 : Fin (k + 1)) := by
        rw [← neg_inj]
        simp
      rw [hlast]
      abel

/-- Negation of a finite cyclic coordinate is an involution. -/
theorem negFin_perm_sq (m : Nat) :
    ((Equiv.neg (Fin m) : Equiv.Perm (Fin m)) ^ 2) = 1 := by
  apply Equiv.ext
  intro position
  change -(-position) = position
  exact neg_neg position

/-- On `Fin (2 * n)` with positive `n`, the reflection fixes exactly the two
antipodal boundary positions `0` and `n`. -/
theorem negFin_fixed_iff {n : Nat} (hn : 0 < n)
    (position : Fin (n + n)) :
    -position = position ↔ position.val = 0 ∨ position.val = n := by
  letI : NeZero (n + n) := ⟨by omega⟩
  constructor
  · intro hfixed
    have hval := congrArg Fin.val hfixed
    simp only [Fin.val_neg] at hval
    split at hval <;> rename_i hzero
    · exact Or.inl (Fin.ext_iff.mp hzero)
    · right
      omega
  · intro hposition
    rcases hposition with hzero | hhalf
    · have hposition : position = 0 := Fin.ext hzero
      simp [hposition]
    · apply Fin.ext
      simp [Fin.val_neg]
      split <;> rename_i hzero
      · have : position.val = 0 := Fin.ext_iff.mp hzero
        omega
      · omega

/-- Capping a positive-width cyclic boundary by the reversal matching creates
exactly `n + 1` face cycles. The proof is uniform in `n`: two antipodal fixed
positions and `n - 1` two-cycles. -/
theorem card_finRotate_mul_revPerm_partition {n : Nat} (hn : 0 < n) :
    (finRotate (n + n) * Fin.revPerm).partition.parts.card = n + 1 := by
  rw [finRotate_mul_revPerm_eq_neg]
  let reflection : Equiv.Perm (Fin (n + n)) := Equiv.neg _
  have hreflection_sq : reflection ^ 2 = 1 := by
    exact negFin_perm_sq (n + n)
  have hcycle : reflection.cycleType =
      Multiset.replicate reflection.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hreflection_sq
  let zeroPoint : Fin (n + n) := ⟨0, by omega⟩
  let halfPoint : Fin (n + n) := ⟨n, by omega⟩
  have hzero_ne_half : zeroPoint ≠ halfPoint := by
    intro h
    have hval := Fin.ext_iff.mp h
    simp [zeroPoint, halfPoint] at hval
    omega
  have hsupport : reflection.support =
      (Finset.univ.erase zeroPoint).erase halfPoint := by
    ext position
    simp only [Equiv.Perm.mem_support, Finset.mem_erase, Finset.mem_univ,
      and_true]
    change (-(position : Fin (n + n)) ≠ position) ↔
      position ≠ halfPoint ∧ position ≠ zeroPoint
    rw [ne_eq, negFin_fixed_iff hn, not_or]
    constructor
    · rintro ⟨hzero, hhalf⟩
      constructor
      · intro h
        exact hhalf (congrArg Fin.val h)
      · intro h
        exact hzero (congrArg Fin.val h)
    · rintro ⟨hhalf, hzero⟩
      constructor
      · intro h
        apply hzero
        exact Fin.ext h
      · intro h
        apply hhalf
        exact Fin.ext h
  have hsupport_card : reflection.support.card = n + n - 2 := by
    rw [hsupport, Finset.card_erase_of_mem, Finset.card_erase_of_mem]
    · simp only [Finset.card_univ, Fintype.card_fin]
      omega
    · exact Finset.mem_univ zeroPoint
    · exact Finset.mem_erase.mpr
        ⟨hzero_ne_half.symm, Finset.mem_univ halfPoint⟩
  have hcycle_card : reflection.cycleType.card = n - 1 := by
    have hsum := reflection.sum_cycleType
    rw [hsupport_card, hcycle] at hsum
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hsum
    omega
  change reflection.partition.parts.card = n + 1
  rw [Equiv.Perm.parts_partition, Multiset.card_add, hcycle,
    Multiset.card_replicate, hsupport_card]
  simp only [Fintype.card_fin, hcycle_card, Multiset.card_replicate]
  omega

/-- In canonical boundary coordinates, the actual ordered cap permutation is
the cyclic-step/reflection permutation counted above. -/
theorem oppositeBoundary_capPerm_congr (n : Nat) :
    (oppositeBoundaryPositionEquiv n).permCongr
        (oppositeBoundaryCycle n * orderedPositionSeamSwap n) =
      finRotate (n + n) * Fin.revPerm := by
  apply Equiv.ext
  intro position
  simp only [Equiv.permCongr_apply, Equiv.Perm.mul_apply]
  simp only [oppositeBoundaryCycle, Equiv.permCongr_apply,
    Equiv.apply_symm_apply]
  change finRotate (n + n)
      ((oppositeBoundaryPositionEquiv n)
        (orderedPositionSeamSwap n
          ((oppositeBoundaryPositionEquiv n).symm position))) =
    finRotate (n + n) (Fin.revPerm position)
  congr 1
  exact DFunLike.congr_fun
    (oppositeBoundaryPosition_seamSwap_eq_revPerm n) position

/-- Therefore the ordered cap itself has exactly `n + 1` face cycles for every
positive interface width. -/
theorem card_oppositeBoundary_capPerm_partition {n : Nat} (hn : 0 < n) :
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n).partition.parts.card =
      n + 1 := by
  rw [← GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts
    (oppositeBoundaryPositionEquiv n)
    (oppositeBoundaryCycle n * orderedPositionSeamSwap n),
    oppositeBoundary_capPerm_congr]
  exact card_finRotate_mul_revPerm_partition hn

/-- Ordered positions enumerate the whole actual boundary whenever the two
cut edge sets are disjoint and cover the computed vertex boundary. -/
def orderedBoundaryPositionEquiv
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    OrderedSeamPosition n ≃
      BoundaryDart RS (deletedRegionKeep deleted) :=
  (Equiv.sumCongr
    (orderedBoundaryDartEquiv RS (deletedRegionKeep deleted)
      leftCrossing
      (leftCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
      hleftInjective)
    (orderedBoundaryDartEquiv RS (deletedRegionKeep deleted)
      rightCrossing
      (rightCrossing_outward RS deleted leftCrossing rightCrossing hboundary)
      hrightInjective)).trans
    (boundaryDartEquivCutSum RS (deletedRegionKeep deleted)
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      (deletedRegionBoundaryCover RS deleted leftCrossing rightCrossing
        hboundary) hdisjoint).symm

@[simp]
theorem orderedBoundaryPositionEquiv_apply_left
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) (step : Fin n) :
    orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
        hboundary hleftInjective hrightInjective hdisjoint (Sum.inl step) =
      (orderedBoundaryDart RS (deletedRegionKeep deleted) leftCrossing
        (leftCrossing_outward RS deleted leftCrossing rightCrossing
          hboundary) step).1 :=
  rfl

@[simp]
theorem orderedBoundaryPositionEquiv_apply_right
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) (step : Fin n) :
    orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
        hboundary hleftInjective hrightInjective hdisjoint (Sum.inr step) =
      (orderedBoundaryDart RS (deletedRegionKeep deleted) rightCrossing
        (rightCrossing_outward RS deleted leftCrossing rightCrossing
          hboundary) step).1 :=
  rfl

/-- Computed statement that the two transversals occur as opposite arcs of
one deleted-region boundary: left in forward order and right in reverse order.
This is the precise rotation-system replacement for the splice note's
topological "homeomorphism" phrase. -/
def CutsFollowOppositeDeletedBoundaryOrder
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) : Prop :=
  deletedRegionBoundarySuccessor RS deleted =
    (orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
      hboundary hleftInjective hrightInjective hdisjoint).permCongr
        (oppositeBoundaryCycle n)

/-- Equal-index seam matching transported to the actual boundary darts of the
deleted region. -/
def deletedRegionOrderedSeamSwap
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    Equiv.Perm (BoundaryDart RS (deletedRegionKeep deleted)) :=
  (orderedBoundaryPositionEquiv RS deleted leftCrossing rightCrossing
    hboundary hleftInjective hrightInjective hdisjoint).permCongr
      (orderedPositionSeamSwap n)

/-- When the computed deleted boundary consists of the two transversals in
opposite order, capping that actual boundary by the splice matching creates
exactly `n + 1` boundary face cycles. -/
theorem card_deletedRegionBoundary_cap_partition
    (RS : RotationSystem V E) (deleted : Finset V)
    (leftCrossing rightCrossing : Fin n → E)
    (hboundary : orderedCut leftCrossing ∪ orderedCut rightCrossing =
      vertexSetCrossingEdges RS deleted)
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (hn : 0 < n)
    (horder : CutsFollowOppositeDeletedBoundaryOrder RS deleted
      leftCrossing rightCrossing hboundary hleftInjective hrightInjective
      hdisjoint) :
    (deletedRegionBoundarySuccessor RS deleted *
        deletedRegionOrderedSeamSwap RS deleted leftCrossing rightCrossing
          hboundary hleftInjective hrightInjective hdisjoint).partition.parts.card =
      n + 1 := by
  let boundaryEquiv := orderedBoundaryPositionEquiv RS deleted
    leftCrossing rightCrossing hboundary hleftInjective hrightInjective
    hdisjoint
  have hperm :
      deletedRegionBoundarySuccessor RS deleted *
          deletedRegionOrderedSeamSwap RS deleted leftCrossing rightCrossing
            hboundary hleftInjective hrightInjective hdisjoint =
        boundaryEquiv.permCongr
          (oppositeBoundaryCycle n * orderedPositionSeamSwap n) := by
    rw [horder]
    apply Equiv.ext
    intro dart
    simp [deletedRegionOrderedSeamSwap, boundaryEquiv,
      Equiv.Perm.mul_apply, Equiv.permCongr_apply]
  rw [hperm,
    GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts]
  exact card_oppositeBoundary_capPerm_partition hn

end

end GoertzelV24DeletedRegionBoundaryOrder

end Mettapedia.GraphTheory.FourColor

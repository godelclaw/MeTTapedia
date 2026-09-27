import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceReturnProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutOldFaceReturn

open GoertzelV24BoundaryFaceReturnProfile
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamArcAmbientFace
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Starting opposite a retained boundary dart, the first deleted-side return
takes at least two old face steps. The first step is based back on the retained
endpoint of the original crossing edge. -/
theorem two_le_boundaryDeletedSideReturnTime
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    2 ≤ boundaryDeletedSideReturnTime RS keep boundary := by
  let root := RS.alpha boundary.1.1
  let returnTime := boundaryDeletedSideReturnTime RS keep boundary
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos RS.phi
      (fun dart => ¬ keep (RS.vertOf dart)) root boundary.2
  have hreturnHit : ¬ keep
      (RS.vertOf ((RS.phi ^ returnTime) root)) :=
    firstPositiveHitTime_hits RS.phi
      (fun dart => ¬ keep (RS.vertOf dart)) root boundary.2
  have hfirstKeep : keep (RS.vertOf ((RS.phi ^ 1) root)) := by
    simp only [pow_one, root]
    rw [RS.vert_phi_eq_vert_alpha, RS.alpha_involutive]
    exact boundary.1.2
  by_contra hnot
  have hreturnEq : returnTime = 1 := by omega
  rw [hreturnEq] at hreturnHit
  exact hreturnHit hfirstKeep

/-- The retained dart immediately before the next deleted-side old-face
return. -/
def boundaryReturnEndpointDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) : RS.D :=
  (RS.phi ^ (boundaryDeletedSideReturnTime RS keep boundary - 1))
    (RS.alpha boundary.1.1)

theorem keep_boundaryReturnEndpointDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    keep (RS.vertOf (boundaryReturnEndpointDart RS keep boundary)) := by
  let returnTime := boundaryDeletedSideReturnTime RS keep boundary
  have htwo : 2 ≤ returnTime :=
    two_le_boundaryDeletedSideReturnTime RS keep boundary
  have hnotDeleted := not_hit_before_firstPositiveHitTime RS.phi
    (fun dart => ¬ keep (RS.vertOf dart))
    (RS.alpha boundary.1.1) boundary.2
    (show 0 < returnTime - 1 by omega)
    (show returnTime - 1 < returnTime by omega)
  by_contra hdeleted
  exact hnotDeleted hdeleted

theorem not_keep_alpha_boundaryReturnEndpointDart
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    ¬ keep (RS.vertOf
      (RS.alpha (boundaryReturnEndpointDart RS keep boundary))) := by
  let returnTime := boundaryDeletedSideReturnTime RS keep boundary
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos RS.phi
      (fun dart => ¬ keep (RS.vertOf dart))
      (RS.alpha boundary.1.1) boundary.2
  have hreturnHit : ¬ keep (RS.vertOf
      ((RS.phi ^ returnTime) (RS.alpha boundary.1.1))) :=
    firstPositiveHitTime_hits RS.phi
      (fun dart => ¬ keep (RS.vertOf dart))
      (RS.alpha boundary.1.1) boundary.2
  rw [← RS.vert_phi_eq_vert_alpha]
  change ¬ keep (RS.vertOf (RS.phi
    ((RS.phi ^ (returnTime - 1)) (RS.alpha boundary.1.1))))
  rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hreturnPos]
  exact hreturnHit

/-- The next old-face boundary endpoint computed without constructing a new
splice. -/
def boundaryReturnEndpoint
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) : BoundaryDart RS keep :=
  ⟨⟨boundaryReturnEndpointDart RS keep boundary,
      keep_boundaryReturnEndpointDart RS keep boundary⟩,
    not_keep_alpha_boundaryReturnEndpointDart RS keep boundary⟩

@[simp]
theorem boundaryReturnEndpoint_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (boundary : BoundaryDart RS keep) :
    (boundaryReturnEndpoint RS keep boundary).1.1 =
      (RS.phi ^ (boundaryDeletedSideReturnTime RS keep boundary - 1))
        (RS.alpha boundary.1.1) :=
  rfl

/-- At a seam root, the next constructed seam hit has exactly the old
boundary endpoint obtained by the preceding definition. -/
theorem nextHit_underlying_eq_boundaryReturnEndpoint
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hroot : IsSeamDart root) :
    let splicePhi := orderedCutSplicePhi RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    let markedRoot := (⟨root, hroot⟩ : { point // IsSeamDart point })
    matchedPartUnderlyingDart RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        (nextHit splicePhi IsSeamDart markedRoot).1 =
      (boundaryReturnEndpoint RS keep
        (orderedCutSpliceMatchedBoundary RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective root hroot)).1.1 := by
  dsimp only
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  let returnTime := firstPositiveHitTime splicePhi IsSeamDart root hroot
  let matched := orderedCutSpliceMatchedBoundary RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective root hroot
  have hreturnPos : 0 < returnTime :=
    firstPositiveHitTime_pos splicePhi IsSeamDart root hroot
  have htransport :=
    orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      root hroot hreturnPos (Nat.le_refl returnTime)
  have hlength := ambientPartialFaceLength_eq_spliceReturnTime RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hroot
  have hrootEq := orderedCutSpliceAmbientFaceRoot_eq_alpha_matchedBoundary
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hroot
  have hreturns : boundaryDeletedSideReturnTime RS keep matched =
      orderedCutSpliceAmbientDeletedSideReturnTime RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root hroot := by
    rcases root with dart | side
    · exact False.elim hroot
    · rcases side with dart | dart <;> rfl
  have hlength' : boundaryDeletedSideReturnTime RS keep matched - 1 =
      returnTime := hreturns ▸ hlength
  change matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      ((splicePhi ^ returnTime) root) = _
  rw [htransport]
  change (RS.phi ^ returnTime)
      (orderedCutSpliceAmbientFaceRoot RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter root) =
    (RS.phi ^ (boundaryDeletedSideReturnTime RS keep matched - 1))
      (RS.alpha matched.1.1)
  rw [hlength', hrootEq]

/-- Ordered seam positions are also an exact enumeration of all old boundary
darts, with the left/right tag determined by the disjoint cut cover. -/
def orderedSeamBoundaryEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing)) :
    OrderedSeamPosition n ≃ BoundaryDart RS keep :=
  (Equiv.sumCongr
    (orderedBoundaryDartEquiv RS keep leftCrossing
      hleftCrosses hleftInjective)
    (orderedBoundaryDartEquiv RS keep rightCrossing
      hrightCrosses hrightInjective)).trans
    (boundaryDartEquivCutSum RS keep (orderedCut leftCrossing)
      (orderedCut rightCrossing) hcover hdisjoint).symm

/-- Decode an old boundary dart to its oriented ordered seam position. -/
def orderedBoundaryPosition
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (boundary : BoundaryDart RS keep) : OrderedSeamPosition n :=
  (orderedSeamBoundaryEquiv RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint).symm boundary

theorem matchedPartUnderlyingDart_seamDartEquiv
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCut rightCut : Finset E)
    (side : BoundaryDartOn RS keep leftCut ⊕
      BoundaryDartOn RS keep rightCut) :
    matchedPartUnderlyingDart RS keep leftCut rightCut
        (seamDartEquiv side).1 =
      (cutSumUnderlyingBoundary RS keep leftCut rightCut side).1.1 := by
  rcases side with left | right <;> rfl

/-- Encoding a decoded boundary position as a seam dart preserves its old
underlying dart. -/
theorem orderedSeamRoot_orderedBoundaryPosition_val
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (boundary : BoundaryDart RS keep) :
    matchedPartUnderlyingDart RS keep
        (orderedCut leftCrossing) (orderedCut rightCrossing)
        (orderedSeamRoot RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          (orderedBoundaryPosition RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint boundary)) =
      boundary.1.1 := by
  simp [orderedSeamRoot, orderedSeamPositionEquiv,
    orderedBoundaryPosition, orderedSeamBoundaryEquiv,
    Equiv.trans_apply, matchedPartUnderlyingDart_seamDartEquiv]
  exact congrArg (fun dart : BoundaryDart RS keep => dart.1.1)
    (cutSumUnderlyingBoundary_toCutSum RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing) hcover boundary)

/-- The next face port computed entirely in the old rotation system: cross
the prescribed matching, follow the old face to its next deleted-side return,
and decode the preceding retained boundary dart. -/
def oldOrderedCutFaceReturnSuccessor
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (position : OrderedSeamPosition n) : OrderedSeamPosition n :=
  let root := orderedSeamRoot RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective position
  let hroot := orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective position
  orderedBoundaryPosition RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective hcover hdisjoint
    (boundaryReturnEndpoint RS keep
      (orderedCutSpliceMatchedBoundary RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective root hroot))

/-- The successor constructed from old face returns is exactly the successor
of the spliced face permutation. -/
theorem actualOrderedCutFaceReturnSuccessor_apply_eq_old
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (position : OrderedSeamPosition n) :
    actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter position =
      oldOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint position := by
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  apply seamEquiv.injective
  change seamEquiv
      (seamEquiv.symm (nextHit splicePhi IsSeamDart
        (seamEquiv position))) =
    seamEquiv (oldOrderedCutFaceReturnSuccessor RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint position)
  rw [seamEquiv.apply_symm_apply]
  apply Subtype.ext
  apply matchedPartUnderlyingDart_injective RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint
  change matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      (nextHit splicePhi IsSeamDart (seamEquiv position)).1 =
    matchedPartUnderlyingDart RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      (orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        (oldOrderedCutFaceReturnSuccessor RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint position))
  unfold oldOrderedCutFaceReturnSuccessor
  rw [orderedSeamRoot_orderedBoundaryPosition_val]
  exact nextHit_underlying_eq_boundaryReturnEndpoint RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    (orderedSeamRoot RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective position)
    (orderedSeamRoot_isSeam RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective position)

theorem oldOrderedCutFaceReturnSuccessor_bijective
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    Function.Bijective
      (oldOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint) := by
  let actual := actualOrderedCutFaceReturnSuccessor RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  constructor
  · intro first second heq
    apply actual.injective
    rw [actualOrderedCutFaceReturnSuccessor_apply_eq_old,
      actualOrderedCutFaceReturnSuccessor_apply_eq_old]
    exact heq
  · intro target
    rcases actual.surjective target with ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    rw [← actualOrderedCutFaceReturnSuccessor_apply_eq_old]
    exact hsource

/-- The old-face return map as a permutation. Its forward map contains no
reference to the constructed splice; the splice theorem supplies
bijectivity. -/
def oldOrderedCutFaceReturnPerm
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    Equiv.Perm (OrderedSeamPosition n) :=
  Equiv.ofBijective
    (oldOrderedCutFaceReturnSuccessor RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint)
    (oldOrderedCutFaceReturnSuccessor_bijective RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter)

@[simp]
theorem oldOrderedCutFaceReturnPerm_apply
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (position : OrderedSeamPosition n) :
    oldOrderedCutFaceReturnPerm RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter position =
      oldOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint position :=
  rfl

/-- The old-rotation return permutation and constructed-face successor are
extensionally identical. -/
theorem oldOrderedCutFaceReturnPerm_eq_actual
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    oldOrderedCutFaceReturnPerm RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter =
      actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter := by
  apply Equiv.ext
  intro position
  exact (actualOrderedCutFaceReturnSuccessor_apply_eq_old RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter position).symm

/-- A fixed-width face-return profile whose stored cap and successor data are
both computed from old rotation-system face returns. -/
def oldRotationOrderedCutFaceReturnProfile
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    OrderedCutFaceReturnProfile n where
  arcCap
    | Sum.inl step => cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1
    | Sum.inr step => cappedBoundaryPartialFaceLength RS keep
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1
  faceSuccessor := oldOrderedCutFaceReturnPerm RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter

/-- Computing the profile before the splice gives exactly the profile read
from the constructed rotation system. -/
theorem oldRotationOrderedCutFaceReturnProfile_eq_actual
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    oldRotationOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter =
      actualOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter := by
  unfold oldRotationOrderedCutFaceReturnProfile
  unfold actualOrderedCutFaceReturnProfile
  congr 1
  exact oldOrderedCutFaceReturnPerm_eq_actual RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter

/-- The profile computed before splicing decides the minimum size of every
seam-touching face in the constructed rotation system. -/
theorem orderedCutRotationSystem_five_le_seam_faceOrbit_iff_oldProfile
    (RS : RotationSystem V E) (keep : V → Prop)
    (leftCrossing rightCrossing : Fin n → E)
    (hleftCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = leftCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hrightCrosses : ∀ step, ∃ dart : RS.D,
      RS.edgeOf dart = rightCrossing step ∧
      keep (RS.vertOf dart) ∧
      ¬ keep (RS.vertOf (RS.alpha dart)))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : ∀ dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing ∨
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : ∀ step,
      RS.vertOf
          (orderedBoundaryDart RS keep leftCrossing
            hleftCrosses step).1.1.1 ≠
        RS.vertOf
          (orderedBoundaryDart RS keep rightCrossing
            hrightCrosses step).1.1.1)
    (rootPosition : OrderedSeamPosition n) :
    let profile := oldRotationOrderedCutFaceReturnProfile RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
    5 ≤ ((orderedCutRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints).faceOrbit
      (orderedSeamRoot RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        rootPosition)).card ↔
      profile.FaceMeetsFive rootPosition := by
  dsimp only
  rw [oldRotationOrderedCutFaceReturnProfile_eq_actual]
  exact orderedCutRotationSystem_five_le_seam_faceOrbit_iff_profile
    RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hseamEndpoints rootPosition

end

end GoertzelV24OrderedCutOldFaceReturn

end Mettapedia.GraphTheory.FourColor

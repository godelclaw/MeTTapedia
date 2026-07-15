import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceEdgeCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceReturnProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitPartitionBridge

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSpliceFaceCount

open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Cycles of a permutation which contain at least one marked point. -/
def HitOrbit (perm : Equiv.Perm A) (hit : A -> Prop) :=
  {orbit : Quotient (Equiv.Perm.SameCycle.setoid perm) //
    exists point : A, hit point /\ Quotient.mk _ point = orbit}

/-- Cycles of a permutation which avoid every marked point. -/
def NonHitOrbit (perm : Equiv.Perm A) (hit : A -> Prop) :=
  {orbit : Quotient (Equiv.Perm.SameCycle.setoid perm) //
    Not (exists point : A, hit point /\ Quotient.mk _ point = orbit)}

noncomputable instance permutationOrbitFintype (perm : Equiv.Perm A) :
    Fintype (Quotient (Equiv.Perm.SameCycle.setoid perm)) :=
  Fintype.ofFinite _

noncomputable instance hitOrbitFintype
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Fintype (HitOrbit perm hit) :=
  Fintype.ofInjective (fun orbit : HitOrbit perm hit => orbit.1)
    Subtype.val_injective

noncomputable instance nonHitOrbitFintype
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Fintype (NonHitOrbit perm hit) :=
  Fintype.ofInjective (fun orbit : NonHitOrbit perm hit => orbit.1)
    Subtype.val_injective

/-- Every representative of an unmarked cycle is itself unmarked. -/
theorem nonHitOrbit_not_hit_of_sameCycle
    (perm : Equiv.Perm A) (hit : A -> Prop)
    (orbit : NonHitOrbit perm hit) (point : A)
    (hpoint : perm.SameCycle orbit.1.out point) :
    Not (hit point) := by
  intro hhit
  apply orbit.2
  refine ⟨point, hhit, ?_⟩
  exact (Quotient.sound hpoint).symm.trans (Quotient.out_eq orbit.1)

/-- Conjugating a permutation transports its cycle quotient. -/
def permOrbitEquivPermCongr
    {B : Type*} [Fintype B] [DecidableEq B]
    (equiv : A ≃ B) (perm : Equiv.Perm A) :
    Quotient (Equiv.Perm.SameCycle.setoid perm) ≃
      Quotient (Equiv.Perm.SameCycle.setoid (equiv.permCongr perm)) :=
  Quotient.congr equiv (fun first second =>
    (permCongr_sameCycle_iff equiv perm first second).symm)

/-- Cycle count is invariant under transport to an equivalent carrier. -/
theorem card_permCongr_partition_parts
    {B : Type*} [Fintype B] [DecidableEq B]
    (equiv : A ≃ B) (perm : Equiv.Perm A) :
    (equiv.permCongr perm).partition.parts.card =
      perm.partition.parts.card := by
  calc
    (equiv.permCongr perm).partition.parts.card =
        Fintype.card
          (Quotient
            (Equiv.Perm.SameCycle.setoid (equiv.permCongr perm))) :=
      (card_permOrbit_eq_card_partition_parts
        (equiv.permCongr perm)).symm
    _ = Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid perm)) :=
      Fintype.card_congr (permOrbitEquivPermCongr equiv perm).symm
    _ = perm.partition.parts.card :=
      card_permOrbit_eq_card_partition_parts perm

/-- Every permutation cycle lies in exactly one of the marked and unmarked
classes. -/
theorem card_permOrbit_eq_hit_add_nonHit
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid perm)) =
      Fintype.card (HitOrbit perm hit) +
        Fintype.card (NonHitOrbit perm hit) := by
  classical
  let meets : Quotient (Equiv.Perm.SameCycle.setoid perm) -> Prop :=
    fun orbit => exists point : A,
      hit point /\ Quotient.mk _ point = orbit
  calc
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid perm)) =
        Fintype.card
          ({orbit // meets orbit} ⊕ {orbit // Not (meets orbit)}) :=
      (Fintype.card_congr (Equiv.sumCompl meets)).symm
    _ = Fintype.card {orbit // meets orbit} +
          Fintype.card {orbit // Not (meets orbit)} :=
      Fintype.card_sum
    _ = Fintype.card (HitOrbit perm hit) +
          Fintype.card (NonHitOrbit perm hit) := by
      rfl

/-- A cycle of the first-return permutation determines its ambient marked
cycle. -/
def markedOrbitToHitOrbit
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Quotient (Equiv.Perm.SameCycle.setoid (nextHitPerm perm hit)) ->
      HitOrbit perm hit :=
  Quotient.lift
    (fun marked : {point // hit point} =>
      ⟨Quotient.mk _ marked.1, ⟨marked.1, marked.2, rfl⟩⟩)
    (by
      intro left right hsame
      apply Subtype.ext
      apply Quotient.sound
      exact (nextHitPerm_sameCycle_iff perm hit left right).1 hsame)

theorem markedOrbitToHitOrbit_injective
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Function.Injective (markedOrbitToHitOrbit perm hit) := by
  intro left right heq
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      apply Quotient.sound
      apply (nextHitPerm_sameCycle_iff perm hit left right).2
      have hambient :
          (Quotient.mk _ left.1 :
              Quotient (Equiv.Perm.SameCycle.setoid perm)) =
            Quotient.mk _ right.1 :=
        congrArg (fun orbit : HitOrbit perm hit => orbit.1) heq
      exact Quotient.exact hambient

theorem markedOrbitToHitOrbit_surjective
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Function.Surjective (markedOrbitToHitOrbit perm hit) := by
  rintro ⟨orbit, point, hpoint, hpointOrbit⟩
  let marked : {point // hit point} := ⟨point, hpoint⟩
  refine ⟨Quotient.mk _ marked, ?_⟩
  apply Subtype.ext
  exact hpointOrbit

/-- Marked ambient cycles are canonically the cycles of the first-return
permutation on marked points. -/
def hitOrbitEquivNextHitOrbit
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Quotient (Equiv.Perm.SameCycle.setoid (nextHitPerm perm hit)) ≃
      HitOrbit perm hit :=
  Equiv.ofBijective (markedOrbitToHitOrbit perm hit)
    ⟨markedOrbitToHitOrbit_injective perm hit,
      markedOrbitToHitOrbit_surjective perm hit⟩

/-- Hence the number of ambient cycles meeting the marked set is the cycle
count of its first-return permutation. -/
theorem card_hitOrbit_eq_nextHit_partition_card
    (perm : Equiv.Perm A) (hit : A -> Prop) :
    Fintype.card (HitOrbit perm hit) =
      (nextHitPerm perm hit).partition.parts.card := by
  calc
    Fintype.card (HitOrbit perm hit) =
        Fintype.card
          (Quotient
            (Equiv.Perm.SameCycle.setoid (nextHitPerm perm hit))) :=
      Fintype.card_congr (hitOrbitEquivNextHitOrbit perm hit).symm
    _ = (nextHitPerm perm hit).partition.parts.card :=
      card_permOrbit_eq_card_partition_parts (nextHitPerm perm hit)

/-- The seam-touching face cycles of an ordered splice are counted exactly by
the cycles of its computed ordered-port return successor. -/
theorem card_orderedCut_seamHitOrbit_eq_actualSuccessor_parts
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer)) :
    Fintype.card
        (HitOrbit
          (orderedCutSplicePhi RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint houter)
          IsSeamDart) =
      (actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card := by
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  rw [card_hitOrbit_eq_nextHit_partition_card]
  symm
  simpa [actualOrderedCutFaceReturnSuccessor, seamEquiv, splicePhi] using
    card_permCongr_partition_parts seamEquiv.symm
      (nextHitPerm splicePhi IsSeamDart)

/-- Exact face-count decomposition of the shortened rotation system. The
first summand is computed from face cycles avoiding the seam; the second is
the finite ordered-port profile used to validate all newly completed faces. -/
theorem card_orderedCutRetainedVertex_faceCycleLengths
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V -> Prop)
    (leftCrossing rightCrossing : Fin n -> E)
    (hleftCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = leftCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hrightCrosses : forall step, exists dart : RS.D,
      RS.edgeOf dart = rightCrossing step /\
      keep (RS.vertOf dart) /\
      Not (keep (RS.vertOf (RS.alpha dart))))
    (hleftInjective : Function.Injective leftCrossing)
    (hrightInjective : Function.Injective rightCrossing)
    (hcover : forall dart : BoundaryDart RS keep,
      RS.edgeOf dart.1.1 ∈ orderedCut leftCrossing \/
        RS.edgeOf dart.1.1 ∈ orderedCut rightCrossing)
    (hdisjoint : Disjoint (orderedCut leftCrossing)
      (orderedCut rightCrossing))
    (houter : keep (RS.vertOf RS.outer))
    (hseamEndpoints : forall step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1) :
    (GoertzelV24CurvatureScope.faceCycleLengths
      (orderedCutRetainedVertexRotationSystem RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints)).card =
      Fintype.card
        (NonHitOrbit
          (orderedCutSplicePhi RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint houter)
          IsSeamDart) +
      (actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card := by
  let splicePhi := orderedCutSplicePhi RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
  have horbits := card_permOrbit_eq_hit_add_nonHit splicePhi IsSeamDart
  rw [card_orderedCut_seamHitOrbit_eq_actualSuccessor_parts RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter] at horbits
  have hpartition : splicePhi.partition.parts.card =
      (actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card +
      Fintype.card (NonHitOrbit splicePhi IsSeamDart) := by
    rw [<- card_permOrbit_eq_card_partition_parts splicePhi]
    exact horbits
  change splicePhi.partition.parts.card = _
  simpa only [splicePhi, Nat.add_comm] using hpartition

end


end GoertzelV24RetainedSpliceFaceCount

end Mettapedia.GraphTheory.FourColor

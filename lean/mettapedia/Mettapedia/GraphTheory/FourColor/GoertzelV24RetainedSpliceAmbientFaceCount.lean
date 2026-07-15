import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamArcAmbientFace

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedSpliceAmbientFaceCount

open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamArcAmbientFace
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

variable (RS : RotationSystem V E) (keep : V -> Prop)
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

local notation "splicePhi" =>
  orderedCutSplicePhi RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter

local notation "forgetDart" =>
  matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
    (orderedCut rightCrossing)

/-- Seam-avoiding cycles of the shortened face permutation. -/
abbrev SpliceNonSeamOrbit := NonHitOrbit splicePhi IsSeamDart

/-- Ambient face cycles whose every dart is based at a retained vertex. -/
abbrev AmbientRetainedFaceOrbit :=
  NonHitOrbit RS.phi (fun dart => Not (keep (RS.vertOf dart)))

/-- Every dart on a seam-avoiding splice cycle is an intact retained dart. -/
theorem nonHitSpliceOrbit_all_interior
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    (point : {point // (splicePhi).SameCycle orbit.1.out point}) :
    exists dart : InternalDart RS keep, point.1 = Sum.inl dart := by
  exact exists_interior_of_not_isSeamDart point.1
    (nonHitOrbit_not_hit_of_sameCycle splicePhi IsSeamDart orbit point.1
      point.2)

/-- Forgetting splice tags commutes with the face permutations along one
seam-avoiding cycle. -/
theorem nonHitSpliceOrbit_forget_commutes
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    (point : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hpoint : (splicePhi).SameCycle orbit.1.out point) :
    forgetDart (splicePhi point) = RS.phi (forgetDart point) := by
  rcases nonHitSpliceOrbit_all_interior RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter orbit ⟨point, hpoint⟩ with ⟨dart, rfl⟩
  exact orderedCutSplicePhi_interior_underlying RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter dart

/-- Forgetting tags maps one seam-avoiding splice cycle into its complete
ambient face cycle. -/
def nonHitSpliceCycleForget
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter) :
    {point // (splicePhi).SameCycle orbit.1.out point} ->
      {dart // RS.phi.SameCycle (forgetDart orbit.1.out) dart} :=
  fun point => ⟨forgetDart point.1, by
    rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
    have htransport := map_pow_of_map_apply_on_cycle splicePhi RS.phi
      forgetDart orbit.1.out
      (nonHitSpliceOrbit_forget_commutes RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter orbit)
      power
    rw [hpower] at htransport
    rw [htransport]
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl RS.phi (forgetDart orbit.1.out))⟩

theorem nonHitSpliceCycleForget_bijective
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter) :
    Function.Bijective
      (nonHitSpliceCycleForget RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter orbit) := by
  let cycleForget := nonHitSpliceCycleForget RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter orbit
  have hinjective : Function.Injective cycleForget := by
    intro first second heq
    apply Subtype.ext
    apply matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint
    exact congrArg Subtype.val heq
  apply (Fintype.bijective_iff_injective_and_card cycleForget).2
  refine ⟨hinjective, ?_⟩
  have hcard := card_sameCycle_eq_of_injective_map_apply
    splicePhi RS.phi forgetDart
    (matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint)
    orbit.1.out
    (nonHitSpliceOrbit_forget_commutes RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter orbit)
  simpa only [cycleForget, Fintype.card_subtype] using hcard

/-- The ambient face containing a seam-avoiding splice cycle avoids the
deleted vertex set. -/
theorem nonHitSpliceOrbit_ambient_avoids_deleted
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter) :
    Not (exists point : RS.D,
      Not (keep (RS.vertOf point)) /\
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) point =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetDart orbit.1.out)) := by
  rintro ⟨point, hdeleted, hpoint⟩
  have hcycle : RS.phi.SameCycle (forgetDart orbit.1.out) point :=
    Quotient.exact hpoint.symm
  let target : {dart //
      RS.phi.SameCycle (forgetDart orbit.1.out) dart} :=
    ⟨point, hcycle⟩
  rcases (nonHitSpliceCycleForget_bijective RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter orbit).2 target
    with ⟨source, hsource⟩
  apply hdeleted
  have hunderlying : forgetDart source.1 = point :=
    congrArg Subtype.val hsource
  rw [<- hunderlying]
  exact keep_matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) source.1

/-- Send a seam-avoiding output face to its unchanged ambient face. -/
def nonHitSpliceOrbitToAmbient
    (orbit : SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter) :
    AmbientRetainedFaceOrbit RS keep :=
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      (forgetDart orbit.1.out),
    nonHitSpliceOrbit_ambient_avoids_deleted RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter orbit⟩

theorem nonHitSpliceOrbitToAmbient_injective :
    Function.Injective
      (nonHitSpliceOrbitToAmbient RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter) := by
  intro left right heq
  apply Subtype.ext
  have hambientQuotient :
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetDart left.1.out) =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetDart right.1.out) :=
    congrArg Subtype.val heq
  have hambientCycle :
      RS.phi.SameCycle (forgetDart left.1.out)
        (forgetDart right.1.out) :=
    Quotient.exact hambientQuotient
  let target : {dart //
      RS.phi.SameCycle (forgetDart left.1.out) dart} :=
    ⟨forgetDart right.1.out, hambientCycle⟩
  rcases (nonHitSpliceCycleForget_bijective RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter left).2 target
    with ⟨source, hsource⟩
  have hunderlying : forgetDart source.1 = forgetDart right.1.out :=
    congrArg Subtype.val hsource
  have hsourceEq : source.1 = right.1.out :=
    matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint hunderlying
  have hspliceCycle : (splicePhi).SameCycle left.1.out right.1.out := by
    simpa only [hsourceEq] using source.2
  exact (Quotient.out_eq left.1).symm.trans
    ((Quotient.sound hspliceCycle).trans (Quotient.out_eq right.1))

/-- The untouched ambient orbit predicate supplies retainedness at every
representative of the face. -/
theorem ambientRetainedFaceOrbit_keep
    (orbit : AmbientRetainedFaceOrbit RS keep) (point : RS.D)
    (hpoint : RS.phi.SameCycle orbit.1.out point) :
    keep (RS.vertOf point) := by
  by_contra hdeleted
  exact nonHitOrbit_not_hit_of_sameCycle RS.phi
    (fun dart => Not (keep (RS.vertOf dart))) orbit point hpoint hdeleted

/-- A chosen ambient dart on an untouched face and its opposite endpoint are
both retained, so it is an intact splice dart. -/
def ambientRetainedFaceOrbitInternalDart
    (orbit : AmbientRetainedFaceOrbit RS keep) : InternalDart RS keep :=
  ⟨⟨orbit.1.out,
      ambientRetainedFaceOrbit_keep RS keep orbit orbit.1.out
        (Equiv.Perm.SameCycle.refl RS.phi orbit.1.out)⟩,
    by
      have hnextCycle : RS.phi.SameCycle orbit.1.out
          (RS.phi orbit.1.out) :=
        Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          RS.phi orbit.1.out
      have hnextKeep := ambientRetainedFaceOrbit_keep RS keep orbit
        (RS.phi orbit.1.out) hnextCycle
      rwa [RS.vert_phi_eq_vert_alpha] at hnextKeep⟩

/-- One splice face step from an intact dart on an untouched ambient face
remains intact and follows that same ambient face. -/
theorem ambientRetainedFaceOrbit_step
    (orbit : AmbientRetainedFaceOrbit RS keep)
    (point : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hpointNonSeam : Not (IsSeamDart point))
    (hpointCycle : RS.phi.SameCycle orbit.1.out (forgetDart point)) :
    Not (IsSeamDart (splicePhi point)) /\
      RS.phi.SameCycle orbit.1.out (forgetDart (splicePhi point)) := by
  rcases exists_interior_of_not_isSeamDart point hpointNonSeam with
    ⟨dart, rfl⟩
  have hunderlying :
      forgetDart (splicePhi (Sum.inl dart)) = RS.phi dart.1.1 :=
    orderedCutSplicePhi_interior_underlying RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter dart
  have hnextCycle : RS.phi.SameCycle orbit.1.out
      (forgetDart (splicePhi (Sum.inl dart))) := by
    rw [hunderlying]
    exact hpointCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
        RS.phi dart.1.1)
  refine ⟨?_, hnextCycle⟩
  intro hnextSeam
  have hfollowingCycle : RS.phi.SameCycle orbit.1.out
      (RS.phi (forgetDart (splicePhi (Sum.inl dart)))) :=
    hnextCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi _)
  have hfollowingKeep := ambientRetainedFaceOrbit_keep RS keep orbit
    (RS.phi (forgetDart (splicePhi (Sum.inl dart)))) hfollowingCycle
  exact (not_keep_phi_matchedPartUnderlyingDart_of_isSeam RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
    (splicePhi (Sum.inl dart)) hnextSeam) hfollowingKeep

/-- Every iterate from the chosen untouched ambient-face dart remains off the
new seam and continues around the original ambient face. -/
theorem ambientRetainedFaceOrbit_pow
    (orbit : AmbientRetainedFaceOrbit RS keep) (power : Nat) :
    let root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) :=
        Sum.inl (ambientRetainedFaceOrbitInternalDart RS keep orbit)
    Not (IsSeamDart ((splicePhi ^ power) root)) /\
      RS.phi.SameCycle orbit.1.out
        (forgetDart ((splicePhi ^ power) root)) := by
  let root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) :=
    Sum.inl (ambientRetainedFaceOrbitInternalDart RS keep orbit)
  change Not (IsSeamDart ((splicePhi ^ power) root)) /\
    RS.phi.SameCycle orbit.1.out
      (forgetDart ((splicePhi ^ power) root))
  induction power with
  | zero =>
      refine ⟨by simp [root, IsSeamDart], ?_⟩
      change RS.phi.SameCycle orbit.1.out orbit.1.out
      exact Equiv.Perm.SameCycle.refl RS.phi orbit.1.out
  | succ power ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ambientRetainedFaceOrbit_step RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter orbit
        ((splicePhi ^ power) root) ih.1 ih.2

/-- Construct the unique seam-avoiding output face represented by an
untouched ambient face. -/
def ambientRetainedFaceOrbitToSplice
    (orbit : AmbientRetainedFaceOrbit RS keep) :
    SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter :=
  let root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) :=
    Sum.inl (ambientRetainedFaceOrbitInternalDart RS keep orbit)
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid splicePhi) root, by
    rintro ⟨point, hseam, hpoint⟩
    have hcycle : (splicePhi).SameCycle root point :=
      (Quotient.exact hpoint).symm
    rcases hcycle.exists_nat_pow_eq with ⟨power, hpower⟩
    have hnonseam := (ambientRetainedFaceOrbit_pow RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter orbit power).1
    exact hnonseam (hpower.symm ▸ hseam)⟩

theorem nonHitSpliceOrbitToAmbient_surjective :
    Function.Surjective
      (nonHitSpliceOrbitToAmbient RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter) := by
  intro orbit
  let source := ambientRetainedFaceOrbitToSplice RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter orbit
  refine ⟨source, ?_⟩
  apply Subtype.ext
  let root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)) :=
    Sum.inl (ambientRetainedFaceOrbitInternalDart RS keep orbit)
  have hsourceCycle : (splicePhi).SameCycle source.1.out root := by
    have hquot :
        Quotient.mk (Equiv.Perm.SameCycle.setoid splicePhi) source.1.out =
          Quotient.mk (Equiv.Perm.SameCycle.setoid splicePhi) root := calc
      Quotient.mk (Equiv.Perm.SameCycle.setoid splicePhi) source.1.out =
          source.1 := Quotient.out_eq source.1
      _ = Quotient.mk (Equiv.Perm.SameCycle.setoid splicePhi) root := by
        rfl
    exact Quotient.exact hquot
  let sourcePoint : {point //
      (splicePhi).SameCycle source.1.out point} :=
    ⟨root, hsourceCycle⟩
  have hambientCycle :=
    (nonHitSpliceCycleForget RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter source sourcePoint).2
  change RS.phi.SameCycle (forgetDart source.1.out)
    (forgetDart sourcePoint.1) at hambientCycle
  have hambientRoot : RS.phi.SameCycle (forgetDart source.1.out)
      (forgetDart root) := by
    simpa only [sourcePoint] using hambientCycle
  have hrootUnderlying : forgetDart root = orbit.1.out := by
    rfl
  have hambientOut : RS.phi.SameCycle (forgetDart source.1.out)
      orbit.1.out := by
    rw [hrootUnderlying] at hambientRoot
    exact hambientRoot
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      (forgetDart source.1.out) = orbit.1
  exact (Quotient.sound hambientOut).trans (Quotient.out_eq orbit.1)

/-- Untouched ambient faces are canonically the seam-avoiding output faces. -/
def nonHitSpliceOrbitEquivAmbientRetainedFaceOrbit :
    SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter ≃
      AmbientRetainedFaceOrbit RS keep :=
  Equiv.ofBijective
    (nonHitSpliceOrbitToAmbient RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter)
    ⟨nonHitSpliceOrbitToAmbient_injective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter,
      nonHitSpliceOrbitToAmbient_surjective RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter⟩

/-- The count of seam-avoiding output faces is exactly the count of ambient
faces avoiding every deleted vertex. -/
theorem card_spliceNonSeamOrbit_eq_ambientRetainedFaceOrbit :
    Fintype.card
        (SpliceNonSeamOrbit RS keep leftCrossing rightCrossing
          hleftCrosses hrightCrosses hleftInjective hrightInjective
          hcover hdisjoint houter) =
      Fintype.card (AmbientRetainedFaceOrbit RS keep) :=
  Fintype.card_congr
    (nonHitSpliceOrbitEquivAmbientRetainedFaceOrbit RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter)

/-- Exact relative face count after deleting a region and matching its two
ordered interfaces: untouched ambient faces survive once, while every changed
face is one cycle of the computed ordered-port successor. -/
theorem card_orderedCutRetainedVertex_faceCycleLengths_eq_ambient_add_return
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
      Fintype.card (AmbientRetainedFaceOrbit RS keep) +
      (actualOrderedCutFaceReturnSuccessor RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).partition.parts.card := by
  rw [card_orderedCutRetainedVertex_faceCycleLengths RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints]
  rw [card_spliceNonSeamOrbit_eq_ambientRetainedFaceOrbit RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter]

end

end GoertzelV24RetainedSpliceAmbientFaceCount

end Mettapedia.GraphTheory.FourColor

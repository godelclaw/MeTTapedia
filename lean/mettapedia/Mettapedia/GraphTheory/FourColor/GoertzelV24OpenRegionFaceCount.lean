import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionBoundaryOrbitClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondSpliceEuler

/-!
# Exact untouched-face count for a literal open region

Opening a retained vertex side creates one fresh degree-one stub at every
crossing edge.  This file proves the generic face-count bridge needed by the
C-3 annular-cellulation step: opened face cycles avoiding every fresh stub are
canonically the ambient face cycles whose every dart is based at a retained
vertex.

This is an exact finite-permutation statement.  It neither assumes that the
opened carrier is an annulus nor identifies the stub-touching cycles; those
boundary cycles are computed separately from the retained boundary successor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionFaceCount

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24OpenRegionBoundaryOrbit
open GoertzelV24OpenRegionBoundaryOrbitClassification
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24PlanarBondSpliceEuler
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The fresh degree-one darts of a literal open region. -/
def IsBoundaryStub (RS : RotationSystem V E) (keep : V → Prop) :
    Dart RS keep → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- Opened face cycles which avoid every fresh degree-one stub. -/
abbrev OpenNonBoundaryOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :=
  NonHitOrbit (rotationSystem RS keep outer).phi (IsBoundaryStub RS keep)

/-- Every dart on a stub-free opened face cycle is an old retained dart. -/
theorem nonHitOpenOrbit_all_old
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : OpenNonBoundaryOrbit RS keep outer)
    (point : {point //
      (rotationSystem RS keep outer).phi.SameCycle orbit.1.out point}) :
    ∃ dart : RetainedDart RS keep, point.1 = Sum.inl dart := by
  cases hpointValue : point.1 with
  | inl old => exact ⟨old, rfl⟩
  | inr stub =>
      have hcycle : (rotationSystem RS keep outer).phi.SameCycle
          orbit.1.out (Sum.inr stub) := by
        rw [← hpointValue]
        exact point.2
      exact False.elim
        (nonHitOrbit_not_hit_of_sameCycle
          (rotationSystem RS keep outer).phi (IsBoundaryStub RS keep)
          orbit (Sum.inr stub) hcycle (by simp [IsBoundaryStub]))

/-- Along a stub-free opened face, forgetting the open tag commutes with one
face-permutation step. -/
theorem nonHitOpenOrbit_forget_commutes
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : OpenNonBoundaryOrbit RS keep outer)
    (point : Dart RS keep)
    (hpoint : (rotationSystem RS keep outer).phi.SameCycle orbit.1.out point) :
    forgetOpenDart RS keep ((rotationSystem RS keep outer).phi point) =
      RS.phi (forgetOpenDart RS keep point) := by
  rcases nonHitOpenOrbit_all_old RS keep outer orbit ⟨point, hpoint⟩ with
    ⟨dart, rfl⟩
  have hinternal : keep (RS.vertOf (RS.alpha dart.1)) := by
    by_contra hboundary
    let boundary : BoundaryDart RS keep := ⟨dart, hboundary⟩
    have hstep : (rotationSystem RS keep outer).phi (Sum.inl dart) =
        Sum.inr boundary :=
      rotationSystem_phi_old_boundary RS keep outer boundary
    have hnextCycle : (rotationSystem RS keep outer).phi.SameCycle
        orbit.1.out ((rotationSystem RS keep outer).phi (Sum.inl dart)) :=
      hpoint.trans
        (Mettapedia.GraphTheory.EquivPermSameCycle.step_right
          (rotationSystem RS keep outer).phi (Sum.inl dart))
    have hnotStub := nonHitOrbit_not_hit_of_sameCycle
      (rotationSystem RS keep outer).phi (IsBoundaryStub RS keep)
      orbit ((rotationSystem RS keep outer).phi (Sum.inl dart)) hnextCycle
    apply hnotStub
    rw [hstep]
    simp [IsBoundaryStub]
  rw [RotationSystem.phi_apply,
    rotationSystem_alpha_old_of_internal RS keep outer dart hinternal,
    rotationSystem_rho_old, RotationSystem.phi_apply]
  rfl

/-- Forgetting tags maps one stub-free opened face cycle into its complete
ambient face cycle. -/
def nonHitOpenCycleForget
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : OpenNonBoundaryOrbit RS keep outer) :
    {point // (rotationSystem RS keep outer).phi.SameCycle orbit.1.out point} →
      {dart // RS.phi.SameCycle
        (forgetOpenDart RS keep orbit.1.out) dart} :=
  fun point => ⟨forgetOpenDart RS keep point.1, by
    rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
    have htransport := map_pow_of_map_apply_on_cycle
      (rotationSystem RS keep outer).phi RS.phi
      (forgetOpenDart RS keep) orbit.1.out
      (nonHitOpenOrbit_forget_commutes RS keep outer orbit) power
    rw [hpower] at htransport
    rw [htransport]
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl RS.phi
        (forgetOpenDart RS keep orbit.1.out))⟩

theorem nonHitOpenCycleForget_bijective
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : OpenNonBoundaryOrbit RS keep outer) :
    Function.Bijective (nonHitOpenCycleForget RS keep outer orbit) := by
  let cycleForget := nonHitOpenCycleForget RS keep outer orbit
  have hinjective : Function.Injective cycleForget := by
    intro first second heq
    apply Subtype.ext
    rcases nonHitOpenOrbit_all_old RS keep outer orbit first with
      ⟨firstOld, hfirst⟩
    rcases nonHitOpenOrbit_all_old RS keep outer orbit second with
      ⟨secondOld, hsecond⟩
    have hunderlying : forgetOpenDart RS keep first.1 =
        forgetOpenDart RS keep second.1 := congrArg Subtype.val heq
    rw [hfirst, hsecond] at hunderlying ⊢
    exact congrArg Sum.inl (Subtype.ext hunderlying)
  refine ⟨hinjective, ?_⟩
  intro target
  rcases target.2.exists_nat_pow_eq with ⟨power, hpower⟩
  let sourcePoint := ((rotationSystem RS keep outer).phi ^ power) orbit.1.out
  have hsourcePoint : (rotationSystem RS keep outer).phi.SameCycle
      orbit.1.out sourcePoint :=
    (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl _ orbit.1.out)
  refine ⟨⟨sourcePoint, hsourcePoint⟩, ?_⟩
  apply Subtype.ext
  exact (map_pow_of_map_apply_on_cycle
    (rotationSystem RS keep outer).phi RS.phi
    (forgetOpenDart RS keep) orbit.1.out
    (nonHitOpenOrbit_forget_commutes RS keep outer orbit) power).trans hpower

/-- The ambient face containing a stub-free opened cycle avoids every deleted
vertex. -/
theorem nonHitOpenOrbit_ambient_avoids_deleted
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : OpenNonBoundaryOrbit RS keep outer) :
    ¬ ∃ point : RS.D, ¬ keep (RS.vertOf point) ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) point =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetOpenDart RS keep orbit.1.out) := by
  rintro ⟨point, hdeleted, hpoint⟩
  have hcycle : RS.phi.SameCycle
      (forgetOpenDart RS keep orbit.1.out) point :=
    Quotient.exact hpoint.symm
  let target : {dart // RS.phi.SameCycle
      (forgetOpenDart RS keep orbit.1.out) dart} := ⟨point, hcycle⟩
  rcases (nonHitOpenCycleForget_bijective RS keep outer orbit).2 target with
    ⟨source, hsource⟩
  apply hdeleted
  have hunderlying : forgetOpenDart RS keep source.1 = point :=
    congrArg Subtype.val hsource
  rw [← hunderlying]
  rcases nonHitOpenOrbit_all_old RS keep outer orbit source with ⟨old, hold⟩
  rw [hold]
  exact old.2

/-- Send a stub-free opened face to its unchanged ambient face. -/
def nonHitOpenOrbitToAmbient
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    OpenNonBoundaryOrbit RS keep outer → AmbientRetainedFaceOrbit RS keep :=
  fun orbit =>
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
        (forgetOpenDart RS keep orbit.1.out),
      nonHitOpenOrbit_ambient_avoids_deleted RS keep outer orbit⟩

theorem nonHitOpenOrbitToAmbient_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Function.Injective (nonHitOpenOrbitToAmbient RS keep outer) := by
  intro left right heq
  apply Subtype.ext
  have hambientQuotient :
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetOpenDart RS keep left.1.out) =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          (forgetOpenDart RS keep right.1.out) :=
    congrArg Subtype.val heq
  have hambientCycle : RS.phi.SameCycle
      (forgetOpenDart RS keep left.1.out)
      (forgetOpenDart RS keep right.1.out) :=
    Quotient.exact hambientQuotient
  let target : {dart // RS.phi.SameCycle
      (forgetOpenDart RS keep left.1.out) dart} :=
    ⟨forgetOpenDart RS keep right.1.out, hambientCycle⟩
  rcases (nonHitOpenCycleForget_bijective RS keep outer left).2 target with
    ⟨source, hsource⟩
  have hunderlying : forgetOpenDart RS keep source.1 =
      forgetOpenDart RS keep right.1.out := congrArg Subtype.val hsource
  rcases nonHitOpenOrbit_all_old RS keep outer left source with
    ⟨sourceOld, hsourceOld⟩
  have hrightCycle : (rotationSystem RS keep outer).phi.SameCycle
      right.1.out right.1.out := Equiv.Perm.SameCycle.refl _ _
  rcases nonHitOpenOrbit_all_old RS keep outer right ⟨right.1.out, hrightCycle⟩ with
    ⟨rightOld, hrightOld⟩
  have hrightOld' : right.1.out = Sum.inl rightOld := by
    simpa only using hrightOld
  have hsourceEq : source.1 = right.1.out := by
    rw [hsourceOld, hrightOld'] at hunderlying ⊢
    exact congrArg Sum.inl (Subtype.ext hunderlying)
  have hopenCycle : (rotationSystem RS keep outer).phi.SameCycle
      left.1.out right.1.out := by simpa only [hsourceEq] using source.2
  exact (Quotient.out_eq left.1).symm.trans
    ((Quotient.sound hopenCycle).trans (Quotient.out_eq right.1))

/-- The untouched ambient orbit predicate supplies retainedness at every
representative of the face. -/
theorem ambientRetainedFaceOrbit_fullyRetained
    (RS : RotationSystem V E) (keep : V → Prop)
    (orbit : AmbientRetainedFaceOrbit RS keep) :
    FaceFullyRetained RS keep orbit.1.out := by
  intro point hpoint
  exact ambientRetainedFaceOrbit_keep RS keep orbit point hpoint

/-- Transport an untouched ambient face into the literal opening. -/
def ambientRetainedFaceOrbitToOpen
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : AmbientRetainedFaceOrbit RS keep) :
    OpenNonBoundaryOrbit RS keep outer := by
  let hface := ambientRetainedFaceOrbit_fullyRetained RS keep orbit
  refine ⟨openFaceOrbit RS keep outer orbit.1.out hface, ?_⟩
  rintro ⟨point, hstub, hpoint⟩
  have hcycle : (rotationSystem RS keep outer).phi.SameCycle
      (openFaceRoot RS keep orbit.1.out hface) point :=
    (Quotient.exact hpoint).symm
  let target : {point // (rotationSystem RS keep outer).phi.SameCycle
      (openFaceRoot RS keep orbit.1.out hface) point} := ⟨point, hcycle⟩
  rcases (openFaceCycleEquiv RS keep outer orbit.1.out hface).surjective target with
    ⟨source, hsource⟩
  have hopen : openFaceDart RS keep orbit.1.out hface source = point :=
    congrArg Subtype.val hsource
  rw [← hopen] at hstub
  exact hstub

/-- Transporting an untouched ambient face to the opening and forgetting the
open tags returns the original ambient face. -/
theorem nonHitOpenOrbitToAmbient_ambientRetainedFaceOrbitToOpen
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep)
    (orbit : AmbientRetainedFaceOrbit RS keep) :
    nonHitOpenOrbitToAmbient RS keep outer
        (ambientRetainedFaceOrbitToOpen RS keep outer orbit) = orbit := by
  apply Subtype.ext
  let hface := ambientRetainedFaceOrbit_fullyRetained RS keep orbit
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      (forgetOpenDart RS keep
        (openFaceOrbit RS keep outer orbit.1.out hface).out) = orbit.1
  have hopenOut : (rotationSystem RS keep outer).phi.SameCycle
      (openFaceRoot RS keep orbit.1.out hface)
      (openFaceOrbit RS keep outer orbit.1.out hface).out := by
    have hquot :
        Quotient.mk (Equiv.Perm.SameCycle.setoid
          (rotationSystem RS keep outer).phi)
            (openFaceRoot RS keep orbit.1.out hface) =
          openFaceOrbit RS keep outer orbit.1.out hface := rfl
    exact Quotient.exact (hquot.trans
      (Quotient.out_eq (openFaceOrbit RS keep outer orbit.1.out hface)).symm)
  let target : {point // (rotationSystem RS keep outer).phi.SameCycle
      (openFaceRoot RS keep orbit.1.out hface) point} :=
    ⟨(openFaceOrbit RS keep outer orbit.1.out hface).out, hopenOut⟩
  rcases (openFaceCycleEquiv RS keep outer orbit.1.out hface).surjective target with
    ⟨source, hsource⟩
  have hunderlying : forgetOpenDart RS keep
      (openFaceOrbit RS keep outer orbit.1.out hface).out = source.1 := by
    rw [← forgetOpenDart_openFaceDart RS keep orbit.1.out hface source]
    exact (congrArg (forgetOpenDart RS keep)
      (congrArg Subtype.val hsource)).symm
  rw [hunderlying]
  exact (Quotient.sound source.2.symm).trans (Quotient.out_eq orbit.1)

theorem nonHitOpenOrbitToAmbient_surjective
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Function.Surjective (nonHitOpenOrbitToAmbient RS keep outer) := by
  intro orbit
  exact ⟨ambientRetainedFaceOrbitToOpen RS keep outer orbit,
    nonHitOpenOrbitToAmbient_ambientRetainedFaceOrbitToOpen
      RS keep outer orbit⟩

/-- Stub-free opened faces are canonically the ambient faces wholly supported
on the retained side. -/
def openNonBoundaryOrbitEquivAmbientRetainedFaceOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    OpenNonBoundaryOrbit RS keep outer ≃ AmbientRetainedFaceOrbit RS keep :=
  Equiv.ofBijective (nonHitOpenOrbitToAmbient RS keep outer)
    ⟨nonHitOpenOrbitToAmbient_injective RS keep outer,
      nonHitOpenOrbitToAmbient_surjective RS keep outer⟩

/-- Exact generic count of the opened faces which avoid every new stub. -/
theorem card_openNonBoundaryOrbit_eq_ambientRetainedFaceOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Fintype.card (OpenNonBoundaryOrbit RS keep outer) =
      Fintype.card (AmbientRetainedFaceOrbit RS keep) :=
  Fintype.card_congr
    (openNonBoundaryOrbitEquivAmbientRetainedFaceOrbit RS keep outer)

/-- Geometric form of the exact count: stub-free opened faces are counted by
the ambient face orbits all of whose darts lie on the retained side. -/
theorem card_openNonBoundaryOrbit_eq_allOnSide
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Fintype.card (OpenNonBoundaryOrbit RS keep outer) =
      (orbitFacesAllOnSide RS keep).card := by
  rw [card_openNonBoundaryOrbit_eq_ambientRetainedFaceOrbit,
    card_ambientRetainedFaceOrbit_eq_allOnSide]

/-- A retained boundary dart is exactly a marked fresh stub of the opened
carrier. -/
def boundaryDartEquivStub
    (RS : RotationSystem V E) (keep : V → Prop) :
    BoundaryDart RS keep ≃ {point : Dart RS keep // IsBoundaryStub RS keep point} where
  toFun boundary := ⟨Sum.inr boundary, by simp [IsBoundaryStub]⟩
  invFun point := by
    rcases point with ⟨old | stub, hpoint⟩
    · exact False.elim hpoint
    · exact stub
  left_inv boundary := rfl
  right_inv point := by
    rcases point with ⟨old | stub, hpoint⟩
    · exact False.elim hpoint
    · rfl

/-- A boundary-successor cycle determines the opened face containing its
fresh stub. -/
def boundaryOrbitToOpenHitOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Quotient (Equiv.Perm.SameCycle.setoid
        (retainedRegionBoundarySuccessor RS keep)) →
      HitOrbit (rotationSystem RS keep outer).phi (IsBoundaryStub RS keep) :=
  Quotient.lift
    (fun boundary =>
      ⟨dartOrbitFace (rotationSystem RS keep outer) (Sum.inr boundary),
        ⟨Sum.inr boundary, by simp [IsBoundaryStub], rfl⟩⟩)
    (by
      intro first second hsame
      apply Subtype.ext
      exact dartOrbitFace_stub_eq_of_boundarySuccessor_sameCycle
        RS keep outer first second hsame)

theorem boundaryOrbitToOpenHitOrbit_injective
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Function.Injective (boundaryOrbitToOpenHitOrbit RS keep outer) := by
  intro left right heq
  induction left, right using Quotient.inductionOn₂ with
  | _ left right =>
      apply Quotient.sound
      apply (dartOrbitFace_stub_eq_iff_boundarySuccessor_sameCycle
        RS keep outer left right).1
      exact congrArg Subtype.val heq

theorem boundaryOrbitToOpenHitOrbit_surjective
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Function.Surjective (boundaryOrbitToOpenHitOrbit RS keep outer) := by
  rintro ⟨orbit, point, hstub, hpointOrbit⟩
  rcases point with old | boundary
  · exact False.elim hstub
  · refine ⟨Quotient.mk _ boundary, ?_⟩
    apply Subtype.ext
    exact hpointOrbit

/-- Stub-touching opened faces are canonically the cycles of the computed
retained-boundary successor. -/
def boundaryOrbitEquivOpenHitOrbit
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Quotient (Equiv.Perm.SameCycle.setoid
        (retainedRegionBoundarySuccessor RS keep)) ≃
      HitOrbit (rotationSystem RS keep outer).phi (IsBoundaryStub RS keep) :=
  Equiv.ofBijective (boundaryOrbitToOpenHitOrbit RS keep outer)
    ⟨boundaryOrbitToOpenHitOrbit_injective RS keep outer,
      boundaryOrbitToOpenHitOrbit_surjective RS keep outer⟩

/-- Exact count of opened faces which touch at least one fresh stub. -/
theorem card_openBoundaryHitOrbit_eq_boundarySuccessor_parts
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    Fintype.card
        (HitOrbit (rotationSystem RS keep outer).phi
          (IsBoundaryStub RS keep)) =
      (retainedRegionBoundarySuccessor RS keep).partition.parts.card := by
  calc
    Fintype.card
        (HitOrbit (rotationSystem RS keep outer).phi
          (IsBoundaryStub RS keep)) =
        Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid
            (retainedRegionBoundarySuccessor RS keep))) :=
      Fintype.card_congr (boundaryOrbitEquivOpenHitOrbit RS keep outer).symm
    _ = (retainedRegionBoundarySuccessor RS keep).partition.parts.card :=
      card_permOrbit_eq_card_partition_parts
        (retainedRegionBoundarySuccessor RS keep)

/-- Exact generic face decomposition after literally opening a retained
vertex side: untouched ambient faces plus the computed boundary-successor
cycles. -/
theorem card_openRegion_faceCycleLengths_eq_allOnSide_add_boundary
    (RS : RotationSystem V E) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart RS keep) :
    (GoertzelV24CurvatureScope.faceCycleLengths
        (rotationSystem RS keep outer)).card =
      (orbitFacesAllOnSide RS keep).card +
        (retainedRegionBoundarySuccessor RS keep).partition.parts.card := by
  let openPhi := (rotationSystem RS keep outer).phi
  have horbits := card_permOrbit_eq_hit_add_nonHit openPhi
    (IsBoundaryStub RS keep)
  rw [card_openBoundaryHitOrbit_eq_boundarySuccessor_parts RS keep outer,
    card_openNonBoundaryOrbit_eq_allOnSide RS keep outer] at horbits
  change openPhi.partition.parts.card = _
  rw [← card_permOrbit_eq_card_partition_parts openPhi]
  simpa only [Nat.add_comm] using horbits

end

end GoertzelV24OpenRegionFaceCount

end Mettapedia.GraphTheory.FourColor

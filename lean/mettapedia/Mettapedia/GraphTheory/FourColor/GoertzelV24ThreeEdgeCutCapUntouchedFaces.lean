import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceAmbientFaceCount

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RetainedSpliceAmbientFaceCount
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

namespace RotationSystem

namespace ThreeEdgeCutSideData

noncomputable section

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- Cap-return cycles which never reach an exposed retained dart. -/
abbrev CapNonBoundaryOrbit :=
  NonHitOrbit data.capTargetReturn
    (fun dart : RetainedDart RS data.keep =>
      ¬ data.keep (RS.vertOf (RS.alpha dart.1)))

/-- Away from the boundary, a cap-return step is exactly the old ambient
face step after forgetting the retainedness proof. -/
theorem capTargetReturn_internal_val
    (dart : InternalDart RS data.keep) :
    (data.capTargetReturn dart.1).1 = RS.phi dart.1.1 := by
  rw [data.capTargetReturn_eq]
  simp only [Equiv.Perm.mul_apply,
    extendBoundaryPerm_apply_internal RS data.keep data.capBoundaryCycle dart,
    retainedCappedFacePerm, retainedCappedAlpha_apply_internal RS data.keep
      dart.1 dart.2, retainedRho_val]
  rfl

/-- Every point on a boundary-avoiding cap-return cycle is an internal old
dart. -/
theorem capNonBoundaryOrbit_all_internal
    (orbit : data.CapNonBoundaryOrbit)
    (point : {point // data.capTargetReturn.SameCycle orbit.1.out point}) :
    ∃ dart : InternalDart RS data.keep, point.1 = dart.1 := by
  have hnotBoundary := nonHitOrbit_not_hit_of_sameCycle
    data.capTargetReturn
    (fun dart : RetainedDart RS data.keep =>
      ¬ data.keep (RS.vertOf (RS.alpha dart.1)))
    orbit point.1 point.2
  have hopposite : data.keep
      (RS.vertOf (RS.alpha point.1.1)) := by
    simpa using hnotBoundary
  exact ⟨⟨point.1, hopposite⟩, rfl⟩

/-- Forgetting retainedness commutes with face steps along any
boundary-avoiding cap-return cycle. -/
theorem capNonBoundaryOrbit_forget_commutes
    (orbit : data.CapNonBoundaryOrbit)
    (point : RetainedDart RS data.keep)
    (hpoint : data.capTargetReturn.SameCycle orbit.1.out point) :
    (data.capTargetReturn point).1 = RS.phi point.1 := by
  rcases data.capNonBoundaryOrbit_all_internal orbit ⟨point, hpoint⟩ with
    ⟨dart, rfl⟩
  exact data.capTargetReturn_internal_val dart

/-- Forgetting retainedness maps one complete boundary-avoiding cap cycle
onto its ambient facial cycle. -/
def capNonBoundaryCycleForget
    (orbit : data.CapNonBoundaryOrbit) :
    {point // data.capTargetReturn.SameCycle orbit.1.out point} →
      {dart // RS.phi.SameCycle orbit.1.out.1 dart} :=
  fun point => ⟨point.1.1, by
    rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
    have htransport := map_pow_of_map_apply_on_cycle
      data.capTargetReturn RS.phi
      (fun dart : RetainedDart RS data.keep => dart.1)
      orbit.1.out (data.capNonBoundaryOrbit_forget_commutes orbit) power
    rw [hpower] at htransport
    rw [htransport]
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl RS.phi orbit.1.out.1)⟩

theorem capNonBoundaryCycleForget_bijective
    (orbit : data.CapNonBoundaryOrbit) :
    Function.Bijective (data.capNonBoundaryCycleForget orbit) := by
  let cycleForget := data.capNonBoundaryCycleForget orbit
  have hinjective : Function.Injective cycleForget := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    simpa only [cycleForget, capNonBoundaryCycleForget] using
      congrArg Subtype.val heq
  apply (Fintype.bijective_iff_injective_and_card cycleForget).2
  refine ⟨hinjective, ?_⟩
  have hcard := card_sameCycle_eq_of_injective_map_apply
    data.capTargetReturn RS.phi
    (fun dart : RetainedDart RS data.keep => dart.1)
    Subtype.val_injective orbit.1.out
    (data.capNonBoundaryOrbit_forget_commutes orbit)
  simpa only [cycleForget, Fintype.card_subtype] using hcard

/-- The ambient face containing a boundary-avoiding cap-return cycle never
visits a deleted vertex. -/
theorem capNonBoundaryOrbit_ambient_avoids_deleted
    (orbit : data.CapNonBoundaryOrbit) :
    ¬ ∃ point : RS.D,
      ¬ data.keep (RS.vertOf point) ∧
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) point =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          orbit.1.out.1 := by
  rintro ⟨point, hdeleted, hpoint⟩
  have hcycle : RS.phi.SameCycle orbit.1.out.1 point :=
    Quotient.exact hpoint.symm
  let target : {dart // RS.phi.SameCycle orbit.1.out.1 dart} :=
    ⟨point, hcycle⟩
  rcases (data.capNonBoundaryCycleForget_bijective orbit).2 target with
    ⟨source, hsource⟩
  apply hdeleted
  have hunderlying : source.1.1 = point :=
    congrArg Subtype.val hsource
  rw [← hunderlying]
  exact source.1.2

/-- Send a boundary-avoiding cap face to the unchanged ambient face. -/
def capNonBoundaryOrbitToAmbient
    (orbit : data.CapNonBoundaryOrbit) :
    AmbientRetainedFaceOrbit RS data.keep :=
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) orbit.1.out.1,
    data.capNonBoundaryOrbit_ambient_avoids_deleted orbit⟩

theorem capNonBoundaryOrbitToAmbient_injective :
    Function.Injective data.capNonBoundaryOrbitToAmbient := by
  intro left right heq
  apply Subtype.ext
  have hambientQuotient :
      Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi) left.1.out.1 =
        Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
          right.1.out.1 :=
    congrArg Subtype.val heq
  have hambientCycle : RS.phi.SameCycle left.1.out.1 right.1.out.1 :=
    Quotient.exact hambientQuotient
  let target : {dart // RS.phi.SameCycle left.1.out.1 dart} :=
    ⟨right.1.out.1, hambientCycle⟩
  rcases (data.capNonBoundaryCycleForget_bijective left).2 target with
    ⟨source, hsource⟩
  have hunderlying : source.1.1 = right.1.out.1 := by
    simpa only [capNonBoundaryCycleForget, target] using
      congrArg Subtype.val hsource
  have hsourceEq : source.1 = right.1.out :=
    Subtype.ext hunderlying
  have hcapCycle : data.capTargetReturn.SameCycle
      left.1.out right.1.out := by
    simpa only [hsourceEq] using source.2
  exact (Quotient.out_eq left.1).symm.trans
    ((Quotient.sound hcapCycle).trans (Quotient.out_eq right.1))

/-- One cap-return step from an internal dart on an untouched ambient face
remains internal and follows that same ambient face. -/
theorem ambientRetainedFaceOrbit_capReturn_step
    (orbit : AmbientRetainedFaceOrbit RS data.keep)
    (point : RetainedDart RS data.keep)
    (hpointNonBoundary :
      ¬ (¬ data.keep (RS.vertOf (RS.alpha point.1))))
    (hpointCycle : RS.phi.SameCycle orbit.1.out point.1) :
    ¬ (¬ data.keep
        (RS.vertOf (RS.alpha (data.capTargetReturn point).1))) ∧
      RS.phi.SameCycle orbit.1.out (data.capTargetReturn point).1 := by
  have hopposite : data.keep (RS.vertOf (RS.alpha point.1)) := by
    simpa using hpointNonBoundary
  let internal : InternalDart RS data.keep := ⟨point, hopposite⟩
  have hstep : (data.capTargetReturn point).1 = RS.phi point.1 := by
    simpa only [internal] using data.capTargetReturn_internal_val internal
  have hnextCycle : RS.phi.SameCycle orbit.1.out
      (data.capTargetReturn point).1 := by
    rw [hstep]
    exact hpointCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi point.1)
  have hfollowingCycle : RS.phi.SameCycle orbit.1.out
      (RS.phi (data.capTargetReturn point).1) :=
    hnextCycle.trans
      (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi _)
  have hfollowingKeep := ambientRetainedFaceOrbit_keep RS data.keep orbit
    (RS.phi (data.capTargetReturn point).1) hfollowingCycle
  refine ⟨?_, hnextCycle⟩
  intro hboundary
  apply hboundary
  rw [← RS.vert_phi_eq_vert_alpha]
  exact hfollowingKeep

/-- Every iterate from a chosen dart of an untouched ambient face remains
off the cap boundary and continues around the original ambient face. -/
theorem ambientRetainedFaceOrbit_capReturn_pow
    (orbit : AmbientRetainedFaceOrbit RS data.keep) (power : Nat) :
    let root : RetainedDart RS data.keep :=
      (ambientRetainedFaceOrbitInternalDart RS data.keep orbit).1
    ¬ (¬ data.keep
        (RS.vertOf (RS.alpha ((data.capTargetReturn ^ power) root).1))) ∧
      RS.phi.SameCycle orbit.1.out
        ((data.capTargetReturn ^ power) root).1 := by
  let root : RetainedDart RS data.keep :=
    (ambientRetainedFaceOrbitInternalDart RS data.keep orbit).1
  change ¬ (¬ data.keep
      (RS.vertOf (RS.alpha ((data.capTargetReturn ^ power) root).1))) ∧
    RS.phi.SameCycle orbit.1.out
      ((data.capTargetReturn ^ power) root).1
  induction power with
  | zero =>
      refine ⟨by
        simpa [root] using
          (ambientRetainedFaceOrbitInternalDart RS data.keep orbit).2, ?_⟩
      change RS.phi.SameCycle orbit.1.out orbit.1.out
      exact Equiv.Perm.SameCycle.refl RS.phi orbit.1.out
  | succ power ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact data.ambientRetainedFaceOrbit_capReturn_step orbit
        ((data.capTargetReturn ^ power) root) ih.1 ih.2

/-- Construct the boundary-avoiding cap face represented by an untouched
ambient face. -/
def ambientRetainedFaceOrbitToCapNonBoundary
    (orbit : AmbientRetainedFaceOrbit RS data.keep) :
    data.CapNonBoundaryOrbit :=
  let root : RetainedDart RS data.keep :=
    (ambientRetainedFaceOrbitInternalDart RS data.keep orbit).1
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid data.capTargetReturn) root, by
    rintro ⟨point, hboundary, hpoint⟩
    have hcycle : data.capTargetReturn.SameCycle root point :=
      (Quotient.exact hpoint).symm
    rcases hcycle.exists_nat_pow_eq with ⟨power, hpower⟩
    have hnonBoundary :=
      (data.ambientRetainedFaceOrbit_capReturn_pow orbit power).1
    exact hnonBoundary (hpower.symm ▸ hboundary)⟩

theorem capNonBoundaryOrbitToAmbient_surjective :
    Function.Surjective data.capNonBoundaryOrbitToAmbient := by
  intro orbit
  let source := data.ambientRetainedFaceOrbitToCapNonBoundary orbit
  refine ⟨source, ?_⟩
  apply Subtype.ext
  let root : RetainedDart RS data.keep :=
    (ambientRetainedFaceOrbitInternalDart RS data.keep orbit).1
  have hsourceCycle : data.capTargetReturn.SameCycle source.1.out root := by
    have hquot :
        Quotient.mk (Equiv.Perm.SameCycle.setoid data.capTargetReturn)
            source.1.out =
          Quotient.mk (Equiv.Perm.SameCycle.setoid data.capTargetReturn)
            root := calc
      Quotient.mk (Equiv.Perm.SameCycle.setoid data.capTargetReturn)
          source.1.out = source.1 := Quotient.out_eq source.1
      _ = Quotient.mk (Equiv.Perm.SameCycle.setoid data.capTargetReturn)
          root := by rfl
    exact Quotient.exact hquot
  let sourcePoint : {point //
      data.capTargetReturn.SameCycle source.1.out point} :=
    ⟨root, hsourceCycle⟩
  have hambientCycle :=
    (data.capNonBoundaryCycleForget source sourcePoint).2
  change RS.phi.SameCycle source.1.out.1 sourcePoint.1.1 at hambientCycle
  have hrootUnderlying : sourcePoint.1.1 = orbit.1.out := by
    rfl
  have hambientOut : RS.phi.SameCycle source.1.out.1 orbit.1.out := by
    rw [hrootUnderlying] at hambientCycle
    exact hambientCycle
  change Quotient.mk (Equiv.Perm.SameCycle.setoid RS.phi)
      source.1.out.1 = orbit.1
  exact (Quotient.sound hambientOut).trans (Quotient.out_eq orbit.1)

/-- Boundary-avoiding cap faces are canonically the untouched ambient
faces. -/
def capNonBoundaryOrbitEquivAmbientRetainedFaceOrbit :
    data.CapNonBoundaryOrbit ≃ AmbientRetainedFaceOrbit RS data.keep :=
  Equiv.ofBijective data.capNonBoundaryOrbitToAmbient
    ⟨data.capNonBoundaryOrbitToAmbient_injective,
      data.capNonBoundaryOrbitToAmbient_surjective⟩

theorem card_capNonBoundaryOrbit_eq_ambientRetainedFaceOrbit :
    Fintype.card data.CapNonBoundaryOrbit =
      Fintype.card (AmbientRetainedFaceOrbit RS data.keep) :=
  Fintype.card_congr
    data.capNonBoundaryOrbitEquivAmbientRetainedFaceOrbit

/-- A planar three-star cap has exactly the untouched ambient faces plus its
three separately closed boundary arcs. -/
theorem card_planarOrdered_cap_faceCycleLengths_eq_three_add_ambient
    (htwoSided : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided RS) :
    (GoertzelV24CurvatureScope.faceCycleLengths
      (data.planarOrdered htwoSided).capRotationSystem).card =
      3 + Fintype.card (AmbientRetainedFaceOrbit RS
        (data.planarOrdered htwoSided).keep) := by
  calc
    (GoertzelV24CurvatureScope.faceCycleLengths
        (data.planarOrdered htwoSided).capRotationSystem).card =
        3 + Fintype.card
          (data.planarOrdered htwoSided).CapNonBoundaryOrbit :=
      data.card_planarOrdered_cap_faceCycleLengths_eq_three_add_nonHit
        htwoSided
    _ = 3 + Fintype.card (AmbientRetainedFaceOrbit RS
          (data.planarOrdered htwoSided).keep) := by
      rw [(data.planarOrdered htwoSided).card_capNonBoundaryOrbit_eq_ambientRetainedFaceOrbit]

end

end ThreeEdgeCutSideData

end RotationSystem

end Mettapedia.GraphTheory.FourColor

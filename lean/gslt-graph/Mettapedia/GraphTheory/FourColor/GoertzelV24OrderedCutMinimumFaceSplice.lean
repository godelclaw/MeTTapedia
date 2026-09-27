import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutOldFaceReturn
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutFaceOrbit

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutMinimumFaceSplice

open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutOldFaceReturn
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- If all old faces have length at least five and the old-rotation return
profile accepts every seam port, then every face of the shortened rotation
system has length at least five. This is a global conclusion over all new
face orbits, not merely the seam roots stored in the finite profile. -/
theorem five_le_all_orderedCutRotationSystem_faceOrbits_of_oldProfile
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
    (hminimum : ∀ dart : RS.D, 5 ≤ (RS.faceOrbit dart).card)
    (hprofile : ∀ position : OrderedSeamPosition n,
      (oldRotationOrderedCutFaceReturnProfile RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter).FaceMeetsFive
          position)
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    5 ≤ ((orderedCutRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).faceOrbit root).card := by
  let seamEquiv := orderedSeamPositionEquiv RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective
  let spliceRS := orderedCutRotationSystem RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter hseamEndpoints
  rcases splicedFaceCycle_interior_or_meets_seam RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter root with
    hinterior | ⟨point, hcycle, hpoint⟩
  · rw [orderedCutRotationSystem_interior_faceOrbit_card_eq_ambient
      RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints root hinterior]
    exact hminimum _
  · have hseam : IsSeamDart point := by
      rcases hpoint with ⟨left, rfl⟩ | ⟨right, rfl⟩ <;> trivial
    let marked : { dart // IsSeamDart dart } := ⟨point, hseam⟩
    let position : OrderedSeamPosition n := seamEquiv.symm marked
    have hrootAtPosition :
        orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            position = point := by
      exact congrArg Subtype.val (seamEquiv.apply_symm_apply marked)
    have hsameFace : spliceRS.faceOrbit root =
        spliceRS.faceOrbit
          (orderedSeamRoot RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            position) := by
      apply spliceRS.faceOrbit_eq_of_sameCycle
      change (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root _
      simpa only [hrootAtPosition] using hcycle
    rw [hsameFace]
    exact
      (orderedCutRotationSystem_five_le_seam_faceOrbit_iff_oldProfile
        RS keep leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter
        hseamEndpoints position).2 (hprofile position)

end

end GoertzelV24OrderedCutMinimumFaceSplice

end Mettapedia.GraphTheory.FourColor

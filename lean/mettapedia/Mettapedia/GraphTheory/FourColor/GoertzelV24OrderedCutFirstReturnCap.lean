import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedSpliceFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence

/-!
# Capped face cycles as ambient first returns

A single ordered splice replaces every deleted excursion of the ambient facial
walk by one direct seam step.  When the walk really does leave the retained
side at a seam port and re-enter at its matched partner, the spliced face
permutation is exactly the ambient first-return permutation on retained darts,
transported along the three-part carrier decomposition.

Consequently the capped map has one face for every ambient face that still
contains a retained dart: the faces lost by the splice are precisely the
ambient faces buried entirely inside the deleted region.

The two return hypotheses are local statements about the ambient rotation
system alone, so this file is free of planarity and of graph-backedness.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutFirstReturnCap

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceFaceCount
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A marked point whose immediate successor is already marked returns in one
step. -/
theorem nextHit_val_of_hit_apply
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : {point // hit point})
    (hstep : hit (perm root.1)) :
    (nextHit perm hit root).1 = perm root.1 := by
  classical
  have hpos := firstPositiveHitTime_pos perm hit root.1 root.2
  have hle : firstPositiveHitTime perm hit root.1 root.2 ≤ 1 := by
    refine firstPositiveHitTime_le_of_hit perm hit root.1 root.2
      Nat.one_pos ?_
    simpa using hstep
  have htime : firstPositiveHitTime perm hit root.1 root.2 = 1 := by omega
  simp [nextHit, htime]

/-- An explicitly exhibited minimal return time computes the first return. -/
theorem nextHit_val_of_first_return
    {A : Type*} [Fintype A] [DecidableEq A]
    (perm : Equiv.Perm A) (hit : A → Prop) (root : {point // hit point})
    {time : Nat} (htimePos : 0 < time)
    (hbefore : ∀ step, 0 < step → step < time → ¬ hit ((perm ^ step) root.1))
    (hhit : hit ((perm ^ time) root.1)) :
    (nextHit perm hit root).1 = (perm ^ time) root.1 := by
  classical
  have hle := firstPositiveHitTime_le_of_hit perm hit root.1 root.2
    htimePos hhit
  have hpos := firstPositiveHitTime_pos perm hit root.1 root.2
  have hhits := firstPositiveHitTime_hits perm hit root.1 root.2
  have htime : firstPositiveHitTime perm hit root.1 root.2 = time := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact absurd hhits (hbefore _ hpos hlt)
    · exact heq
  simp [nextHit, htime]

variable {n : Nat}

/-- The retained-dart predicate of a cut side, as a dart marking. -/
def RetainedDartMark (RS : RotationSystem V E) (keep : V → Prop) :
    RS.D → Prop :=
  fun dart => keep (RS.vertOf dart)

section Splice

variable (RS : RotationSystem V E) (keep : V → Prop)
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

/-- The face permutation of the retained-vertex splice is the transported
splice permutation. -/
theorem orderedCutRetainedVertexRotationSystem_phi
    (hseamEndpoints : ∀ step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1) :
    (orderedCutRetainedVertexRotationSystem RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter
      hseamEndpoints).phi =
      orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter :=
  rfl

/-- **First-return identification.**  If the ambient facial walk leaving a
left seam port re-enters through the matched right port, and symmetrically,
then the spliced face permutation is the ambient first-return permutation on
retained darts. -/
theorem orderedCutSplicePhi_eq_permCongr_nextHitPerm
    (hleftReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hrightReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1) :
    orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter =
      (retainedDartEquivMatchedParts RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) hcover hdisjoint).permCongr
        (nextHitPerm RS.phi (RetainedDartMark RS keep)) := by
  classical
  set parts := retainedDartEquivMatchedParts RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing) hcover hdisjoint
    with hparts
  have hsymm : ∀ point, (parts.symm point).1 =
      matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
        (orderedCut rightCrossing) point := by
    intro point
    exact (matchedPartUnderlyingDart_eq_equiv_symm_val RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint point).symm
  have key : ∀ point,
      parts.symm
          (orderedCutSplicePhi RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint houter point) =
        nextHit RS.phi (RetainedDartMark RS keep) (parts.symm point) := by
    intro point
    apply Subtype.ext
    rw [hsymm]
    rcases point with internal | side
    · -- an intact dart: its old facial successor is retained, so the
      -- ambient walk returns immediately
      have hroot : parts.symm (Sum.inl internal) = internal.1 := by
        apply Subtype.ext
        rw [hsymm]
        rfl
      have hstep : RetainedDartMark RS keep (RS.phi internal.1.1) := by
        have hvert : RS.vertOf (RS.phi internal.1.1) =
            RS.vertOf (RS.alpha internal.1.1) := by
          change RS.vertOf (RS.rho (RS.alpha internal.1.1)) = _
          exact RS.vert_rho _
        change keep (RS.vertOf (RS.phi internal.1.1))
        rw [hvert]
        exact internal.2
      rw [hroot, nextHit_val_of_hit_apply RS.phi (RetainedDartMark RS keep)
        internal.1 hstep]
      exact orderedCutSplicePhi_interior_underlying RS keep
        leftCrossing rightCrossing hleftCrosses hrightCrosses
        hleftInjective hrightInjective hcover hdisjoint houter internal
    · rcases side with left | right
      · obtain ⟨step, rfl⟩ :=
          (orderedBoundaryDartEquiv RS keep leftCrossing hleftCrosses
            hleftInjective).surjective left
        rw [orderedBoundaryDartEquiv_apply]
        have hroot : parts.symm
            (Sum.inr (Sum.inl
              (orderedBoundaryDart RS keep leftCrossing hleftCrosses step))) =
            (orderedBoundaryDart RS keep leftCrossing
              hleftCrosses step).1.1 := by
          apply Subtype.ext
          rw [hsymm]
          rfl
        rw [hroot, hleftReturn step]
        exact orderedCutSplicePhi_left_underlying RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter step
      · obtain ⟨step, rfl⟩ :=
          (orderedBoundaryDartEquiv RS keep rightCrossing hrightCrosses
            hrightInjective).surjective right
        rw [orderedBoundaryDartEquiv_apply]
        have hroot : parts.symm
            (Sum.inr (Sum.inr
              (orderedBoundaryDart RS keep rightCrossing
                hrightCrosses step))) =
            (orderedBoundaryDart RS keep rightCrossing
              hrightCrosses step).1.1 := by
          apply Subtype.ext
          rw [hsymm]
          rfl
        rw [hroot, hrightReturn step]
        exact orderedCutSplicePhi_right_underlying RS keep
          leftCrossing rightCrossing hleftCrosses hrightCrosses
          hleftInjective hrightInjective hcover hdisjoint houter step
  ext point
  calc
    orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter point =
        parts (parts.symm
          (orderedCutSplicePhi RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint houter point)) :=
      (parts.apply_symm_apply _).symm
    _ = parts (nextHit RS.phi (RetainedDartMark RS keep)
          (parts.symm point)) := by rw [key point]
    _ = parts.permCongr (nextHitPerm RS.phi (RetainedDartMark RS keep))
          point := rfl

/-- Under the first-return hypotheses the capped map has exactly one face for
each ambient face meeting the retained side. -/
theorem card_orbitFace_cap_eq_card_hitOrbit
    (hseamEndpoints : ∀ step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hleftReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hrightReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1) :
    Fintype.card
        (OrbitFace
          (orderedCutRetainedVertexRotationSystem RS keep
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter
            hseamEndpoints)) =
      Fintype.card (HitOrbit RS.phi (RetainedDartMark RS keep)) := by
  classical
  have hphi := orderedCutSplicePhi_eq_permCongr_nextHitPerm RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter
    hleftReturn hrightReturn
  have hcarrier :
      Fintype.card
        (OrbitFace
          (orderedCutRetainedVertexRotationSystem RS keep
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter
            hseamEndpoints)) =
      Fintype.card
        (Quotient (Equiv.Perm.SameCycle.setoid
          (orderedCutSplicePhi RS keep leftCrossing rightCrossing
            hleftCrosses hrightCrosses hleftInjective hrightInjective
            hcover hdisjoint houter))) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcarrier, hphi]
  calc
    Fintype.card
        (Quotient (Equiv.Perm.SameCycle.setoid
          ((retainedDartEquivMatchedParts RS keep (orderedCut leftCrossing)
            (orderedCut rightCrossing) hcover hdisjoint).permCongr
            (nextHitPerm RS.phi (RetainedDartMark RS keep))))) =
        Fintype.card
          (Quotient (Equiv.Perm.SameCycle.setoid
            (nextHitPerm RS.phi (RetainedDartMark RS keep)))) :=
      Fintype.card_congr
        (permOrbitEquivPermCongr
          (retainedDartEquivMatchedParts RS keep (orderedCut leftCrossing)
            (orderedCut rightCrossing) hcover hdisjoint)
          (nextHitPerm RS.phi (RetainedDartMark RS keep))).symm
    _ = Fintype.card (HitOrbit RS.phi (RetainedDartMark RS keep)) :=
      Fintype.card_congr
        (hitOrbitEquivNextHitOrbit RS.phi (RetainedDartMark RS keep))

/-- The faces destroyed by the splice are exactly the ambient faces buried in
the deleted region. -/
theorem card_orbitFace_cap_add_card_nonHitOrbit
    (hseamEndpoints : ∀ step,
      RS.vertOf (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1 ≠
        RS.vertOf (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hleftReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep leftCrossing hleftCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep rightCrossing
          hrightCrosses step).1.1.1)
    (hrightReturn : ∀ step : Fin n,
      (nextHit RS.phi (RetainedDartMark RS keep)
        (orderedBoundaryDart RS keep rightCrossing hrightCrosses step).1.1).1 =
        RS.rho (orderedBoundaryDart RS keep leftCrossing
          hleftCrosses step).1.1.1) :
    Fintype.card
        (OrbitFace
          (orderedCutRetainedVertexRotationSystem RS keep
            leftCrossing rightCrossing hleftCrosses hrightCrosses
            hleftInjective hrightInjective hcover hdisjoint houter
            hseamEndpoints)) +
        Fintype.card (NonHitOrbit RS.phi (RetainedDartMark RS keep)) =
      Fintype.card (OrbitFace RS) := by
  classical
  rw [card_orbitFace_cap_eq_card_hitOrbit RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective hcover
    hdisjoint houter hseamEndpoints hleftReturn hrightReturn]
  have hsplit := card_permOrbit_eq_hit_add_nonHit RS.phi
    (RetainedDartMark RS keep)
  have hcarrier :
      Fintype.card (OrbitFace RS) =
        Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid RS.phi)) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hcarrier, hsplit]

end Splice

end

end GoertzelV24OrderedCutFirstReturnCap

end Mettapedia.GraphTheory.FourColor

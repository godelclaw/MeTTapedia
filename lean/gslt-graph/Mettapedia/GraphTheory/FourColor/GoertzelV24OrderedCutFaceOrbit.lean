import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedCutRotationSplice

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedCutFaceOrbit

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A one-step semiconjugacy on one finite permutation cycle transports every
nonnegative iterate of the chosen root. -/
theorem map_pow_of_map_apply_on_cycle
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (source : Equiv.Perm A) (target : Equiv.Perm B)
    (map : A → B) (root : A)
    (hmap : ∀ point, source.SameCycle root point →
      map (source point) = target (map point)) :
    ∀ power : Nat,
      map ((source ^ power) root) = (target ^ power) (map root) := by
  intro power
  induction power with
  | zero => simp
  | succ power ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        pow_succ', Equiv.Perm.mul_apply]
      rw [hmap, ih]
      exact (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl source root)

/-- An injective map that commutes with two permutations along one source
cycle gives an equivalence of the complete source and target cycles. The
target surjectivity is derived by lifting its finite nonnegative iterates. -/
theorem card_sameCycle_eq_of_injective_map_apply
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (source : Equiv.Perm A) (target : Equiv.Perm B)
    (map : A → B) (hmapInjective : Function.Injective map) (root : A)
    (hmap : ∀ point, source.SameCycle root point →
      map (source point) = target (map point)) :
    (Finset.univ.filter fun point => source.SameCycle root point).card =
      (Finset.univ.filter fun point =>
        target.SameCycle (map root) point).card := by
  let cycleMap :
      { point // source.SameCycle root point } →
        { point // target.SameCycle (map root) point } :=
    fun point => ⟨map point.1, by
      rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
      have htransport := map_pow_of_map_apply_on_cycle source target map root
        hmap power
      rw [hpower] at htransport
      rw [htransport]
      exact (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl target (map root))⟩
  have hcycleMapInjective : Function.Injective cycleMap := by
    intro left right heq
    apply Subtype.ext
    apply hmapInjective
    exact congrArg Subtype.val heq
  have hcycleMapSurjective : Function.Surjective cycleMap := by
    intro point
    rcases point.2.exists_nat_pow_eq with ⟨power, hpower⟩
    let sourcePoint := (source ^ power) root
    have hsourcePoint : source.SameCycle root sourcePoint :=
      (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl source root)
    refine ⟨⟨sourcePoint, hsourcePoint⟩, ?_⟩
    apply Subtype.ext
    exact (map_pow_of_map_apply_on_cycle source target map root hmap power).trans
      hpower
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.ofBijective cycleMap
      ⟨hcycleMapInjective, hcycleMapSurjective⟩)

/-- If a spliced face cycle contains only intact darts, forgetting the splice
tags gives a cardinality-preserving equivalence with its ambient face cycle.
Thus any face whose length can change must meet one of the two seams. -/
theorem interior_splicedFaceCycle_card_eq_ambient
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
    (hinterior : ∀ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point →
      ∃ dart : InternalDart RS keep, point = Sum.inl dart) :
    (Finset.univ.filter fun point =>
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point).card =
      (RS.faceOrbit
        (matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
          (orderedCut rightCrossing) root)).card := by
  let source := orderedCutSplicePhi RS keep leftCrossing rightCrossing
    hleftCrosses hrightCrosses hleftInjective hrightInjective
    hcover hdisjoint houter
  let forget := matchedPartUnderlyingDart RS keep
    (orderedCut leftCrossing) (orderedCut rightCrossing)
  have hcomm : ∀ point, source.SameCycle root point →
      forget (source point) = RS.phi (forget point) := by
    intro point hpoint
    rcases hinterior point hpoint with ⟨dart, rfl⟩
    exact orderedCutSplicePhi_interior_underlying RS keep
      leftCrossing rightCrossing hleftCrosses hrightCrosses
      hleftInjective hrightInjective hcover hdisjoint houter dart
  have hcard := card_sameCycle_eq_of_injective_map_apply source RS.phi
    forget
    (matchedPartUnderlyingDart_injective RS keep
      (orderedCut leftCrossing) (orderedCut rightCrossing)
      hcover hdisjoint)
    root hcomm
  simpa only [source, forget, RotationSystem.faceOrbit] using hcard

/-- The preceding cycle equality is the literal `faceOrbit` equality in the
complete rotation system whose edge type is computed from the rewired dart
involution. -/
theorem orderedCutRotationSystem_interior_faceOrbit_card_eq_ambient
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
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hinterior : ∀ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point →
      ∃ dart : InternalDart RS keep, point = Sum.inl dart) :
    ((orderedCutRotationSystem RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter hseamEndpoints).faceOrbit root).card =
      (RS.faceOrbit
        (matchedPartUnderlyingDart RS keep (orderedCut leftCrossing)
          (orderedCut rightCrossing) root)).card := by
  change (Finset.univ.filter fun point =>
    (orderedCutSplicePhi RS keep leftCrossing rightCrossing
      hleftCrosses hrightCrosses hleftInjective hrightInjective
      hcover hdisjoint houter).SameCycle root point).card = _
  exact interior_splicedFaceCycle_card_eq_ambient RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hinterior

/-- Every spliced face is either entirely intact or contains an explicitly
tagged dart from one side of the new seam. Together with the preceding
cardinality theorem, this reduces the face-size proof to seam-touching faces. -/
theorem splicedFaceCycle_interior_or_meets_seam
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
      (BoundaryDartOn RS keep (orderedCut rightCrossing))) :
    (∀ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point →
      ∃ dart : InternalDart RS keep, point = Sum.inl dart) ∨
    ∃ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point ∧
      ((∃ dart : BoundaryDartOn RS keep (orderedCut leftCrossing),
          point = Sum.inr (Sum.inl dart)) ∨
        ∃ dart : BoundaryDartOn RS keep (orderedCut rightCrossing),
          point = Sum.inr (Sum.inr dart)) := by
  classical
  by_cases hinterior : ∀ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point →
      ∃ dart : InternalDart RS keep, point = Sum.inl dart
  · exact Or.inl hinterior
  · push Not at hinterior
    rcases hinterior with ⟨point, hcycle, hnotInterior⟩
    refine Or.inr ⟨point, hcycle, ?_⟩
    rcases point with dart | side
    · exact False.elim (hnotInterior dart rfl)
    · rcases side with dart | dart
      · exact Or.inl ⟨dart, rfl⟩
      · exact Or.inr ⟨dart, rfl⟩

/-- Ambient minimum face length transfers unchanged to every seam-free face
of the ordered splice. -/
theorem five_le_interior_splicedFaceCycle_card
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
    (hminimum : ∀ dart, 5 ≤ (RS.faceOrbit dart).card)
    (root : MatchedSeam.Dart (InternalDart RS keep)
      (BoundaryDartOn RS keep (orderedCut leftCrossing))
      (BoundaryDartOn RS keep (orderedCut rightCrossing)))
    (hinterior : ∀ point,
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point →
      ∃ dart : InternalDart RS keep, point = Sum.inl dart) :
    5 ≤ (Finset.univ.filter fun point =>
      (orderedCutSplicePhi RS keep leftCrossing rightCrossing
        hleftCrosses hrightCrosses hleftInjective hrightInjective
        hcover hdisjoint houter).SameCycle root point).card := by
  rw [interior_splicedFaceCycle_card_eq_ambient RS keep
    leftCrossing rightCrossing hleftCrosses hrightCrosses
    hleftInjective hrightInjective hcover hdisjoint houter root hinterior]
  exact hminimum _

end

end GoertzelV24OrderedCutFaceOrbit

end Mettapedia.GraphTheory.FourColor

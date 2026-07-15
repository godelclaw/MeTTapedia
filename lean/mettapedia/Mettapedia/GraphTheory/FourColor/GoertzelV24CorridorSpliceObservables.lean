import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorSpliceObservables

open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24WindingClassification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Saturating both summands before addition preserves their saturated sum. -/
theorem min_add_eq_min_min_add_min (left right threshold : Nat) :
    min (left + right) threshold =
      min (min left threshold + min right threshold) threshold := by
  omega

/-- Pointwise equality of saturated observations composes over a finite sum. -/
theorem min_sum_eq_of_pointwise_min_eq
    {ι : Type*} [DecidableEq ι]
    (items : Finset ι) (left right : ι → Nat) (threshold : Nat)
    (hpointwise : ∀ item ∈ items,
      min (left item) threshold = min (right item) threshold) :
    min (∑ item ∈ items, left item) threshold =
      min (∑ item ∈ items, right item) threshold := by
  induction items using Finset.induction_on with
  | empty => simp
  | @insert item items hnotmem ih =>
      have hitem := hpointwise item (Finset.mem_insert_self item items)
      have hitems : ∀ other ∈ items,
          min (left other) threshold = min (right other) threshold := by
        intro other hother
        exact hpointwise other (Finset.mem_insert_of_mem hother)
      have hrest := ih hitems
      simp only [Finset.sum_insert hnotmem]
      calc
        min (left item + ∑ x ∈ items, left x) threshold =
            min (min (left item) threshold +
              min (∑ x ∈ items, left x) threshold) threshold :=
          min_add_eq_min_min_add_min _ _ _
        _ = min (min (right item) threshold +
              min (∑ x ∈ items, right x) threshold) threshold := by
          rw [hitem, hrest]
        _ = min (right item + ∑ x ∈ items, right x) threshold :=
          (min_add_eq_min_min_add_min _ _ _).symm

/-- A saturated observation contains exactly the information needed to decide
whether adding any common exterior contribution reaches the threshold. -/
theorem threshold_le_add_iff_of_min_eq
    {left right outside threshold : Nat}
    (hcaps : min left threshold = min right threshold) :
    threshold ≤ left + outside ↔ threshold ≤ right + outside := by
  by_cases hleft : threshold ≤ left
  · have hminleft : min left threshold = threshold := min_eq_right hleft
    have hminright : min right threshold = threshold := hcaps.symm.trans hminleft
    have hright : threshold ≤ right := by
      by_contra hnot
      have hright_lt : right < threshold := Nat.lt_of_not_ge hnot
      rw [min_eq_left (Nat.le_of_lt hright_lt)] at hminright
      omega
    omega
  · have hleft_lt : left < threshold := Nat.lt_of_not_ge hleft
    have hminleft : min left threshold = left :=
      min_eq_left (Nat.le_of_lt hleft_lt)
    by_cases hright : threshold ≤ right
    · have hminright : min right threshold = threshold := min_eq_right hright
      have : left = threshold := hminleft.symm.trans (hcaps.trans hminright)
      omega
    · have hright_lt : right < threshold := Nat.lt_of_not_ge hright
      have hminright : min right threshold = right :=
        min_eq_left (Nat.le_of_lt hright_lt)
      have hleft_right : left = right :=
        hminleft.symm.trans (hcaps.trans hminright)
      simp [hleft_right]

/-- Pointwise saturated observations therefore preserve the threshold test for
any finite collection of contributions and any common exterior contribution. -/
theorem threshold_le_sum_add_iff_of_pointwise_min_eq
    {ι : Type*} [DecidableEq ι]
    (items : Finset ι) (left right : ι → Nat)
    (outside threshold : Nat)
    (hpointwise : ∀ item ∈ items,
      min (left item) threshold = min (right item) threshold) :
    threshold ≤ (∑ item ∈ items, left item) + outside ↔
      threshold ≤ (∑ item ∈ items, right item) + outside :=
  threshold_le_add_iff_of_min_eq
    (min_sum_eq_of_pointwise_min_eq items left right threshold hpointwise)

/-- Equal graph-derived profiles identify the complete guarded two-color
reachability proposition for every corresponding pair of ports. -/
theorem trackedPortReachability_iff_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (pair : TrackedColorPair)
    (first second : CorridorPort crossingEdgeCount terminalCount) :
    (left.portEdge first ∈ left.regionEdges ∧
      left.portEdge second ∈ left.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C₁ (left.portEdge first)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C₁ (left.portEdge second)) ∧
      (regionalTrackedEdgeGraph RS left.regionEdges C₁
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (left.portEdge first) (left.portEdge second)) ↔
    (right.portEdge first ∈ right.regionEdges ∧
      right.portEdge second ∈ right.regionEdges ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C₂ (right.portEdge first)) ∧
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2 (C₂ (right.portEdge second)) ∧
      (regionalTrackedEdgeGraph RS right.regionEdges C₂
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (right.portEdge first) (right.portEdge second)) := by
  rw [← left.profile_strandConnected_eq_true_iff C₁ hC₁,
    ← right.profile_strandConnected_eq_true_iff C₂ hC₂,
    strandConnected_eq_of_profiles_eq left right C₁ C₂ hC₁ hC₂ hprofiles]

/-- Equal graph-derived profiles preserve the partition of every selected
finite family of named fragments into ambient faces. -/
theorem fragmentsPairwiseShareFace_iff_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (fragments : Finset (Fin faceFragmentCount)) :
    (∀ first ∈ fragments, ∀ second ∈ fragments,
      left.fragmentFace first = left.fragmentFace second) ↔
    (∀ first ∈ fragments, ∀ second ∈ fragments,
      right.fragmentFace first = right.fragmentFace second) := by
  constructor
  · intro hleft first hfirst second hsecond
    exact (faceContinues_eq_of_profiles_eq left right C₁ C₂ hC₁ hC₂
      hprofiles first second).mp (hleft first hfirst second hsecond)
  · intro hright first hfirst second hsecond
    exact (faceContinues_eq_of_profiles_eq left right C₁ C₂ hC₁ hC₂
      hprofiles first second).mpr (hright first hfirst second hsecond)

/-- Cap-at-five equality preserves the face-length-at-least-five test when a
single named regional fragment is completed by the same exterior length. -/
theorem five_le_fragment_length_add_iff_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (fragment : Fin faceFragmentCount) (outsideLength : Nat) :
    5 ≤ (left.regionalFragmentEdges fragment).card + outsideLength ↔
      5 ≤ (right.regionalFragmentEdges fragment).card + outsideLength :=
  threshold_le_add_iff_of_min_eq
    (faceLengthCap_eq_of_profiles_eq left right C₁ C₂ hC₁ hC₂
      hprofiles fragment)

/-- Cap-at-five observations compose across any selected finite collection of
named fragments. Thus equal graph-derived profiles preserve the threshold test
after adding the same exterior contribution. This arithmetic statement does
not assert that the selected fragments are disjoint or form cyclic intervals. -/
theorem five_le_fragment_sum_add_iff_of_profiles_eq
    {RS : RotationSystem V E}
    {crossingEdgeCount terminalCount faceFragmentCount : Nat}
    (left right : GraphCorridorCutData RS crossingEdgeCount terminalCount
      faceFragmentCount)
    (C₁ C₂ : RS.EdgeColoring Color)
    (hC₁ : RS.IsTaitEdgeColoring C₁) (hC₂ : RS.IsTaitEdgeColoring C₂)
    (hprofiles : left.profile C₁ hC₁ = right.profile C₂ hC₂)
    (fragments : Finset (Fin faceFragmentCount)) (outsideLength : Nat) :
    5 ≤ (∑ fragment ∈ fragments,
      (left.regionalFragmentEdges fragment).card) + outsideLength ↔
    5 ≤ (∑ fragment ∈ fragments,
      (right.regionalFragmentEdges fragment).card) + outsideLength := by
  apply threshold_le_sum_add_iff_of_pointwise_min_eq
  intro fragment _
  exact faceLengthCap_eq_of_profiles_eq left right C₁ C₂ hC₁ hC₂
    hprofiles fragment

end

end GoertzelV24CorridorSpliceObservables

end Mettapedia.GraphTheory.FourColor

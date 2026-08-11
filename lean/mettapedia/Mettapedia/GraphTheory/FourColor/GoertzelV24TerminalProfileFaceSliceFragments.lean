import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceCapUpdate

/-!
# Factor fragments inside a composed face fragment

One face fragment after adjoining a corridor Cell can contain several old
prefix fragments and several Cell fragments.  Its contribution from either
factor is therefore not generally one fragment.  It is, however, exactly the
disjoint union of the factor fragments that meet the composed fragment.

This file proves that component decomposition on cyclic face occurrences and
derives the corresponding cap-at-five sum law.  It retains occurrences until
the final cardinality statement and makes no determinism assumption about the
profile transfer relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileFaceSliceFragments

open GoertzelV24HexFaceRungType
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Enlarging an edge region can only add edges to the common-carrier face
graph. -/
theorem faceRegionalAmbientPositionGraph_mono
    (RS : RotationSystem V E) (root : RS.D)
    {smallRegion largeRegion : Finset E}
    (hregion : smallRegion ⊆ largeRegion) :
    faceRegionalAmbientPositionGraph RS root smallRegion ≤
      faceRegionalAmbientPositionGraph RS root largeRegion := by
  intro left right hadj
  exact ⟨hadj.1, hregion hadj.2.1, hregion hadj.2.2⟩

/-- Factor fragments that contribute at least one occurrence to a named
fragment of a larger region. -/
noncomputable def faceRegionalFactorFragments
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (fragment : FaceRegionalFragment RS root largeRegion) :
    Finset (FaceRegionalFragment RS root factorRegion) := by
  classical
  exact Finset.univ.filter fun factorFragment =>
    ∃ position,
      position ∈ faceRegionalFragmentPositions RS root factorRegion
        factorFragment ∧
      position ∈ faceRegionalFragmentPositions RS root largeRegion fragment

@[simp]
theorem mem_faceRegionalFactorFragments_iff
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (fragment : FaceRegionalFragment RS root largeRegion)
    (factorFragment : FaceRegionalFragment RS root factorRegion) :
    factorFragment ∈ faceRegionalFactorFragments RS root largeRegion
        factorRegion fragment ↔
      ∃ position,
        position ∈ faceRegionalFragmentPositions RS root factorRegion
          factorFragment ∧
        position ∈ faceRegionalFragmentPositions RS root largeRegion
          fragment := by
  classical
  simp [faceRegionalFactorFragments]

/-- If a factor fragment meets a fragment of a larger region, every
occurrence of that factor fragment belongs to the larger fragment. -/
theorem faceRegionalFragmentPositions_subset_of_mem_factorFragments
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (hregion : factorRegion ⊆ largeRegion)
    (fragment : FaceRegionalFragment RS root largeRegion)
    (factorFragment : FaceRegionalFragment RS root factorRegion)
    (hfactor : factorFragment ∈ faceRegionalFactorFragments RS root
      largeRegion factorRegion fragment) :
    faceRegionalFragmentPositions RS root factorRegion factorFragment ⊆
      faceRegionalFragmentPositions RS root largeRegion fragment := by
  classical
  rcases (mem_faceRegionalFactorFragments_iff RS root largeRegion
    factorRegion fragment factorFragment).1 hfactor with
    ⟨anchor, hanchorFactor, hanchorLarge⟩
  intro position hpositionFactor
  rcases (mem_faceRegionalFragmentPositions_iff RS root factorRegion
    factorFragment position).1 hpositionFactor with
    ⟨positionFactor, hpositionFactorSupp, hpositionFactorValue⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root factorRegion
    factorFragment anchor).1 hanchorFactor with
    ⟨anchorFactor, hanchorFactorSupp, hanchorFactorValue⟩
  rcases (mem_faceRegionalFragmentPositions_iff RS root largeRegion
    fragment anchor).1 hanchorLarge with
    ⟨anchorLarge, hanchorLargeSupp, hanchorLargeValue⟩
  have hfactorReachable :
      (faceRegionalPositionGraph RS root factorRegion).Reachable
        positionFactor anchorFactor :=
    faceRegionalFragment_reachable RS root factorRegion factorFragment
      hpositionFactorSupp hanchorFactorSupp
  have hambientFactor :
      (faceRegionalAmbientPositionGraph RS root factorRegion).Reachable
        position anchor := by
    have hreach := (faceRegionalPositionGraph_reachable_iff_ambient RS root
      factorRegion positionFactor anchorFactor).1 hfactorReachable
    simpa [hpositionFactorValue, hanchorFactorValue] using hreach
  have hambientLarge :
      (faceRegionalAmbientPositionGraph RS root largeRegion).Reachable
        position anchor :=
    hambientFactor.mono
      (faceRegionalAmbientPositionGraph_mono RS root hregion)
  have hpositionEdge : faceCycleEdge RS root position ∈ factorRegion := by
    have hregional := positionFactor.2
    rw [mem_faceRegionalPositions_iff] at hregional
    simpa [hpositionFactorValue] using hregional
  let positionLarge : FaceRegionalPosition RS root largeRegion :=
    ⟨position, (mem_faceRegionalPositions_iff RS root largeRegion position).2
      (hregion hpositionEdge)⟩
  have hlargeReachable :
      (faceRegionalPositionGraph RS root largeRegion).Reachable
        positionLarge anchorLarge := by
    apply (faceRegionalPositionGraph_reachable_iff_ambient RS root largeRegion
      positionLarge anchorLarge).2
    simpa [positionLarge, hanchorLargeValue] using hambientLarge
  have hpositionComponent :
      (faceRegionalPositionGraph RS root largeRegion).connectedComponentMk
          positionLarge = fragment := by
    have hpositionAnchor :
        (faceRegionalPositionGraph RS root largeRegion).connectedComponentMk
            positionLarge =
          (faceRegionalPositionGraph RS root largeRegion).connectedComponentMk
            anchorLarge :=
      SimpleGraph.ConnectedComponent.sound hlargeReachable
    have hanchorComponent :
        (faceRegionalPositionGraph RS root largeRegion).connectedComponentMk
            anchorLarge = fragment :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff fragment anchorLarge).1
        hanchorLargeSupp
    exact hpositionAnchor.trans hanchorComponent
  apply (mem_faceRegionalFragmentPositions_iff RS root largeRegion fragment
    position).2
  exact ⟨positionLarge,
    (SimpleGraph.ConnectedComponent.mem_supp_iff fragment positionLarge).2
      hpositionComponent,
    rfl⟩

/-- The slice of a composed fragment contributed by one factor is exactly
the union of the factor fragments that meet it. -/
theorem biUnion_faceRegionalFactorFragments_eq_positionSlice
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (hregion : factorRegion ⊆ largeRegion)
    (fragment : FaceRegionalFragment RS root largeRegion) :
    (faceRegionalFactorFragments RS root largeRegion factorRegion fragment).biUnion
        (faceRegionalFragmentPositions RS root factorRegion) =
      faceRegionalFragmentPositionSlice RS root largeRegion factorRegion
        fragment := by
  classical
  ext position
  constructor
  · intro hposition
    rcases Finset.mem_biUnion.1 hposition with
      ⟨factorFragment, hfactor, hpositionFactor⟩
    have hpositionLarge :=
      faceRegionalFragmentPositions_subset_of_mem_factorFragments RS root
        largeRegion factorRegion hregion fragment factorFragment hfactor
        hpositionFactor
    rcases (mem_faceRegionalFragmentPositions_iff RS root factorRegion
      factorFragment position).1 hpositionFactor with
      ⟨regionalPosition, _hpositionSupp, hpositionValue⟩
    have hpositionEdge := regionalPosition.2
    rw [mem_faceRegionalPositions_iff] at hpositionEdge
    exact Finset.mem_filter.2
      ⟨hpositionLarge, by simpa [hpositionValue] using hpositionEdge⟩
  · intro hposition
    rcases Finset.mem_filter.1 hposition with
      ⟨hpositionLarge, hpositionEdge⟩
    let regionalPosition : FaceRegionalPosition RS root factorRegion :=
      ⟨position, (mem_faceRegionalPositions_iff RS root factorRegion
        position).2 hpositionEdge⟩
    let factorFragment : FaceRegionalFragment RS root factorRegion :=
      (faceRegionalPositionGraph RS root factorRegion).connectedComponentMk
        regionalPosition
    have hpositionFactor :
        position ∈ faceRegionalFragmentPositions RS root factorRegion
          factorFragment := by
      apply (mem_faceRegionalFragmentPositions_iff RS root factorRegion
        factorFragment position).2
      exact ⟨regionalPosition,
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩
    have hfactor : factorFragment ∈ faceRegionalFactorFragments RS root
        largeRegion factorRegion fragment :=
      (mem_faceRegionalFactorFragments_iff RS root largeRegion factorRegion
        fragment factorFragment).2
        ⟨position, hpositionFactor, hpositionLarge⟩
    exact Finset.mem_biUnion.2
      ⟨factorFragment, hfactor, hpositionFactor⟩

/-- Cardinality of a factor slice is the sum of cardinalities of its selected
factor fragments. -/
theorem card_faceRegionalFragmentPositionSlice_eq_sum_factorFragments
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (hregion : factorRegion ⊆ largeRegion)
    (fragment : FaceRegionalFragment RS root largeRegion) :
    (faceRegionalFragmentPositionSlice RS root largeRegion factorRegion
        fragment).card =
      ∑ factorFragment ∈ faceRegionalFactorFragments RS root largeRegion
          factorRegion fragment,
        (faceRegionalFragmentPositions RS root factorRegion
          factorFragment).card := by
  classical
  rw [← biUnion_faceRegionalFactorFragments_eq_positionSlice RS root
    largeRegion factorRegion hregion fragment]
  apply Finset.card_biUnion
  intro left _hleft right _hright hne
  exact disjoint_faceRegionalFragmentPositions_of_ne RS root factorRegion hne

/-- Saturating a finite sum at five depends only on the summands saturated at
five. -/
theorem min_sum_eq_min_sum_min_five
    {α : Type*} (support : Finset α) (weight : α → Nat) :
    min (∑ item ∈ support, weight item) 5 =
      min (∑ item ∈ support, min (weight item) 5) 5 := by
  classical
  induction support using Finset.induction_on with
  | empty => simp
  | @insert item support hitem ih =>
      simp only [Finset.sum_insert, hitem, not_false_eq_true]
      calc
        min (weight item + ∑ x ∈ support, weight x) 5 =
            min (min (weight item) 5 +
              min (∑ x ∈ support, weight x) 5) 5 := by omega
        _ = min (min (weight item) 5 +
              min (∑ x ∈ support, min (weight x) 5) 5) 5 := by rw [ih]
        _ = min (min (weight item) 5 +
              ∑ x ∈ support, min (weight x) 5) 5 := by omega

/-- Consequently the cap-at-five value of a factor slice is computed from
the individual cap-at-five values of exactly the factor fragments that meet
the composed fragment. -/
theorem min_card_faceRegionalFragmentPositionSlice_eq_min_sum_fragmentCaps
    (RS : RotationSystem V E) (root : RS.D)
    (largeRegion factorRegion : Finset E)
    (hregion : factorRegion ⊆ largeRegion)
    (fragment : FaceRegionalFragment RS root largeRegion) :
    min (faceRegionalFragmentPositionSlice RS root largeRegion factorRegion
        fragment).card 5 =
      min
        (∑ factorFragment ∈ faceRegionalFactorFragments RS root largeRegion
              factorRegion fragment,
            min (faceRegionalFragmentPositions RS root factorRegion
              factorFragment).card 5)
        5 := by
  rw [card_faceRegionalFragmentPositionSlice_eq_sum_factorFragments RS root
    largeRegion factorRegion hregion fragment]
  exact min_sum_eq_min_sum_min_five
    (faceRegionalFactorFragments RS root largeRegion factorRegion fragment)
    fun factorFragment =>
      (faceRegionalFragmentPositions RS root factorRegion factorFragment).card

end

end GoertzelV24TerminalProfileFaceSliceFragments

end Mettapedia.GraphTheory.FourColor

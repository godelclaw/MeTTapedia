import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorSpliceObservables
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceUpdate

/-!
# Capped face support across a shared corridor seam

The source transfer profile records face progress only up to five.  When an
old prefix and one adjoining Cell are united, their common cut edges occur in
both regional supports and must be counted once, not twice.  This file proves
the overlap-corrected saturation law and connects the edge-cardinality used by
`CorridorCutProfile` to the occurrence-sensitive face fragments used by the
relational update.

This is the numerical part of the face update.  It neither chooses an outgoing
profile nor assumes that the transfer relation is deterministic.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileFaceCapUpdate

open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceFragments

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Saturating the two contributions before subtracting a shared overlap
preserves their saturated union, provided the overlap itself is below the
threshold.  The lower-bound hypotheses are the exact conditions under which
the natural-number subtraction represents inclusion-exclusion. -/
theorem min_add_sub_eq_min_min_add_sub_of_overlap_lt
    (left right overlap threshold : Nat)
    (hoverlapLeft : overlap ≤ left) (hoverlapRight : overlap ≤ right)
    (hoverlapThreshold : overlap < threshold) :
    min (left + right - overlap) threshold =
      min (min left threshold + min right threshold - overlap) threshold := by
  omega

/-- Inclusion-exclusion followed by saturation depends only on the two
saturated cardinalities and the exact size of their small common seam. -/
theorem min_card_union_eq_min_caps_sub_inter_of_inter_card_lt
    {α : Type*} [DecidableEq α] (left right : Finset α) (threshold : Nat)
    (hinter : (left ∩ right).card < threshold) :
    min (left ∪ right).card threshold =
      min (min left.card threshold + min right.card threshold -
        (left ∩ right).card) threshold := by
  have hoverlapLeft : (left ∩ right).card ≤ left.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hoverlapRight : (left ∩ right).card ≤ right.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hunion : (left ∪ right).card =
      left.card + right.card - (left ∩ right).card := by
    have hcard := Finset.card_union_add_card_inter left right
    omega
  rw [hunion]
  exact min_add_sub_eq_min_min_add_sub_of_overlap_lt
    left.card right.card (left ∩ right).card threshold
      hoverlapLeft hoverlapRight hinter

/-- Inclusion-exclusion remains determined after all three terms are
saturated.  No small-overlap hypothesis is needed: when the overlap reaches
the threshold, both factors and their union have reached it as well. -/
theorem min_add_sub_eq_min_min_add_sub_min
    (left right overlap threshold : Nat)
    (hoverlapLeft : overlap ≤ left) (hoverlapRight : overlap ≤ right) :
    min (left + right - overlap) threshold =
      min (min left threshold + min right threshold -
        min overlap threshold) threshold := by
  omega

/-- The capped cardinality of a union is determined by the capped
cardinalities of both factors and of their intersection.  This is the fully
finite inclusion-exclusion law used by the serial transfer receipt. -/
theorem min_card_union_eq_min_caps_sub_min_inter
    {α : Type*} [DecidableEq α] (left right : Finset α) (threshold : Nat) :
    min (left ∪ right).card threshold =
      min (min left.card threshold + min right.card threshold -
        min (left ∩ right).card threshold) threshold := by
  have hoverlapLeft : (left ∩ right).card ≤ left.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hoverlapRight : (left ∩ right).card ≤ right.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hunion : (left ∪ right).card =
      left.card + right.card - (left ∩ right).card := by
    have hcard := Finset.card_union_add_card_inter left right
    omega
  rw [hunion]
  exact min_add_sub_eq_min_min_add_sub_min
    left.card right.card (left ∩ right).card threshold
      hoverlapLeft hoverlapRight

/-- It is enough to bound the common support by a named seam whose cardinality
is below the saturation threshold.  For the Cell-3 transfer that seam is the
width-two cut, while the profile threshold is five. -/
theorem min_card_union_eq_min_caps_sub_inter_of_inter_subset
    {α : Type*} [DecidableEq α] (left right seam : Finset α)
    (threshold : Nat) (hinter : left ∩ right ⊆ seam)
    (hseam : seam.card < threshold) :
    min (left ∪ right).card threshold =
      min (min left.card threshold + min right.card threshold -
        (left ∩ right).card) threshold := by
  apply min_card_union_eq_min_caps_sub_inter_of_inter_card_lt
  exact lt_of_le_of_lt (Finset.card_le_card hinter) hseam

/-- The Cell-3 specialization: a width-two seam is strictly smaller than the
cap-at-five threshold used by the source profile. -/
theorem min_card_union_eq_min_caps_sub_inter_of_inter_subset_seam_card_le_two
    {α : Type*} [DecidableEq α] (left right seam : Finset α)
    (hinter : left ∩ right ⊆ seam) (hseam : seam.card ≤ 2) :
    min (left ∪ right).card 5 =
      min (min left.card 5 + min right.card 5 - (left ∩ right).card) 5 := by
  apply min_card_union_eq_min_caps_sub_inter_of_inter_subset
    left right seam 5 hinter
  omega

/-- The part of one enlarged regional face fragment contributed by a named
factor region.  Positions, rather than only underlying edges, are retained so
that the decomposition remains correct before two-sidedness is invoked. -/
def faceRegionalFragmentPositionSlice
    (RS : RotationSystem V E) (root : RS.D)
    (unionRegion factorRegion : Finset E)
    (fragment : FaceRegionalFragment RS root unionRegion) :
    Finset (Fin (RS.faceOrbit root).card) :=
  (faceRegionalFragmentPositions RS root unionRegion fragment).filter
    fun position => faceCycleEdge RS root position ∈ factorRegion

/-- An enlarged fragment over `leftRegion ∪ rightRegion` is exactly the
union of its two factor slices.  No face occurrence is lost or introduced. -/
theorem faceRegionalFragmentPositionSlice_union_eq
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (fragment : FaceRegionalFragment RS root (leftRegion ∪ rightRegion)) :
    faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          leftRegion fragment ∪
        faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          rightRegion fragment =
      faceRegionalFragmentPositions RS root (leftRegion ∪ rightRegion)
        fragment := by
  classical
  ext position
  constructor
  · intro hposition
    rcases Finset.mem_union.1 hposition with hleft | hright
    · exact (Finset.mem_filter.1 hleft).1
    · exact (Finset.mem_filter.1 hright).1
  · intro hposition
    rcases (mem_faceRegionalFragmentPositions_iff RS root
      (leftRegion ∪ rightRegion) fragment position).1 hposition with
      ⟨regionalPosition, hfragment, hvalue⟩
    have hregion : faceCycleEdge RS root position ∈
        leftRegion ∪ rightRegion := by
      have hregional := regionalPosition.2
      rw [mem_faceRegionalPositions_iff] at hregional
      simpa [hvalue] using hregional
    rcases Finset.mem_union.1 hregion with hleft | hright
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hposition, hleft⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hposition, hright⟩)

/-- Every occurrence counted by both factor slices lies over an actual edge
of their common seam. -/
theorem image_faceRegionalFragmentPositionSlice_inter_subset_region_inter
    (RS : RotationSystem V E) (root : RS.D)
    (leftRegion rightRegion : Finset E)
    (fragment : FaceRegionalFragment RS root (leftRegion ∪ rightRegion)) :
    (faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          leftRegion fragment ∩
        faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          rightRegion fragment).image (faceCycleEdge RS root) ⊆
      leftRegion ∩ rightRegion := by
  intro edge hedge
  rcases Finset.mem_image.1 hedge with ⟨position, hposition, rfl⟩
  rcases Finset.mem_inter.1 hposition with ⟨hleft, hright⟩
  exact Finset.mem_inter.2
    ⟨(Finset.mem_filter.1 hleft).2, (Finset.mem_filter.1 hright).2⟩

/-- On a two-sided face, the overlap of the two occurrence slices is no
larger than the ambient edge seam. -/
theorem card_faceRegionalFragmentPositionSlice_inter_le_region_inter
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (leftRegion rightRegion : Finset E)
    (fragment : FaceRegionalFragment RS root (leftRegion ∪ rightRegion)) :
    (faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          leftRegion fragment ∩
        faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
          rightRegion fragment).card ≤
      (leftRegion ∩ rightRegion).card := by
  let overlap :=
    faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
        leftRegion fragment ∩
      faceRegionalFragmentPositionSlice RS root (leftRegion ∪ rightRegion)
        rightRegion fragment
  calc
    overlap.card =
        (overlap.image (faceCycleEdge RS root)).card :=
      (Finset.card_image_of_injective overlap
        (faceCycleEdge_injective RS htwoSided root)).symm
    _ ≤ (leftRegion ∩ rightRegion).card :=
      Finset.card_le_card
        (image_faceRegionalFragmentPositionSlice_inter_subset_region_inter
          RS root leftRegion rightRegion fragment)

/-- Exact occurrence-level cap update for one enlarged regional fragment.
The two contributions are saturated separately and their genuine shared
occurrences are subtracted once. -/
theorem min_card_faceRegionalFragmentPositions_union_eq_min_slices_sub_inter
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (leftRegion rightRegion : Finset E)
    (fragment : FaceRegionalFragment RS root (leftRegion ∪ rightRegion))
    (hseam : (leftRegion ∩ rightRegion).card < 5) :
    min (faceRegionalFragmentPositions RS root
          (leftRegion ∪ rightRegion) fragment).card 5 =
      min
        (min (faceRegionalFragmentPositionSlice RS root
            (leftRegion ∪ rightRegion) leftRegion fragment).card 5 +
          min (faceRegionalFragmentPositionSlice RS root
            (leftRegion ∪ rightRegion) rightRegion fragment).card 5 -
          (faceRegionalFragmentPositionSlice RS root
                (leftRegion ∪ rightRegion) leftRegion fragment ∩
            faceRegionalFragmentPositionSlice RS root
                (leftRegion ∪ rightRegion) rightRegion fragment).card)
        5 := by
  let leftSlice := faceRegionalFragmentPositionSlice RS root
    (leftRegion ∪ rightRegion) leftRegion fragment
  let rightSlice := faceRegionalFragmentPositionSlice RS root
    (leftRegion ∪ rightRegion) rightRegion fragment
  have hoverlap : (leftSlice ∩ rightSlice).card < 5 :=
    lt_of_le_of_lt
      (card_faceRegionalFragmentPositionSlice_inter_le_region_inter
        RS htwoSided root leftRegion rightRegion fragment)
      hseam
  have hcap := min_card_union_eq_min_caps_sub_inter_of_inter_card_lt
    leftSlice rightSlice 5 hoverlap
  rw [faceRegionalFragmentPositionSlice_union_eq RS root leftRegion
    rightRegion fragment] at hcap
  exact hcap

/-- On a two-sided face, passing from occurrence support to edge support loses
no cardinality.  This is the bridge that permits the occurrence-sensitive
component update to feed the edge-count cap stored in the finite profile. -/
theorem card_faceRegionalFragmentEdges_eq_positions
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) :
    (faceRegionalFragmentEdges RS root region fragment).card =
      (faceRegionalFragmentPositions RS root region fragment).card := by
  exact Finset.card_image_of_injective
    (faceRegionalFragmentPositions RS root region fragment)
    (faceCycleEdge_injective RS htwoSided root)

/-- Consequently the cap recorded by a graph-derived profile can be computed
on cyclic face occurrences without changing its value. -/
theorem min_card_faceRegionalFragmentEdges_eq_positions
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (region : Finset E)
    (fragment : FaceRegionalFragment RS root region) (threshold : Nat) :
    min (faceRegionalFragmentEdges RS root region fragment).card threshold =
      min (faceRegionalFragmentPositions RS root region fragment).card
        threshold := by
  rw [card_faceRegionalFragmentEdges_eq_positions RS htwoSided]

/-- The same overlap-corrected cap law in the edge-cardinality representation
stored by `CorridorCutProfile.faceLengthCap`. -/
theorem min_card_faceRegionalFragmentEdges_union_eq_min_slices_sub_inter
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (root : RS.D) (leftRegion rightRegion : Finset E)
    (fragment : FaceRegionalFragment RS root (leftRegion ∪ rightRegion))
    (hseam : (leftRegion ∩ rightRegion).card < 5) :
    min (faceRegionalFragmentEdges RS root
          (leftRegion ∪ rightRegion) fragment).card 5 =
      min
        (min (faceRegionalFragmentPositionSlice RS root
            (leftRegion ∪ rightRegion) leftRegion fragment).card 5 +
          min (faceRegionalFragmentPositionSlice RS root
            (leftRegion ∪ rightRegion) rightRegion fragment).card 5 -
          (faceRegionalFragmentPositionSlice RS root
                (leftRegion ∪ rightRegion) leftRegion fragment ∩
            faceRegionalFragmentPositionSlice RS root
                (leftRegion ∪ rightRegion) rightRegion fragment).card)
        5 := by
  rw [min_card_faceRegionalFragmentEdges_eq_positions RS htwoSided]
  exact min_card_faceRegionalFragmentPositions_union_eq_min_slices_sub_inter
    RS htwoSided root leftRegion rightRegion fragment hseam

end

end GoertzelV24TerminalProfileFaceCapUpdate

end Mettapedia.GraphTheory.FourColor

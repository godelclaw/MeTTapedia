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

end

end GoertzelV24TerminalProfileFaceCapUpdate

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareLadder

/-!
# Graph-level square count transport

The profile-resolved count identity for a facial square is already checked at
the finite interface layer: for a multiset of exterior colouring profiles, the
square-extension count of any target profile is the sum of the counts from the
two planar reductions.

What that identity does not carry by itself is the graph-level input its own
statement names: the extraction of a facial square's exterior colouring-profile
multiset from the ambient rotation system.  That extraction is recorded here as
`ExteriorProfileExtraction` and supplied as data rather than assumed, so the
transport below is exactly the interface identity plus the extraction, and
nothing is smuggled in between.

Given the extraction, the graph-level pointed count is additive profile by
profile, and summing over any finite set of target profiles gives the descent
the square rung uses: if the pointed total upstairs is zero then both reduction
totals are zero, so a least zero-target instance descends through both smaller
reductions.  No migration statement occurs anywhere in this module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SquareCountTransport

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The graph-level input the transport needs: a facial square's exterior
colouring profiles, presented as a multiset of interface profiles together
with the identification of the three graph-level pointed counts with the
corresponding interface counts. -/
structure ExteriorProfileExtraction
    (countUp countLeft countRight : SquareInterfaceProfile B → ℕ) where
  /-- The exterior colouring profiles of the ambient instance. -/
  exteriorStates : Multiset (SquareInterfaceProfile B)
  /-- The square's boundary word. -/
  word : SquareBoundaryWord
  /-- The two colours of the pointed majority pair. -/
  first : Color
  second : Color
  word_nonzero : word.Nonzero
  first_ne_zero : first ≠ 0
  second_ne_zero : second ≠ 0
  first_ne_second : first ≠ second
  countUp_eq : ∀ profile, countUp profile =
    (squareGluedExtensionProfileMultiset exteriorStates word first second).count
      profile
  countLeft_eq : ∀ profile, countLeft profile =
    (squareGluedReductionSideProfileMultiset exteriorStates
      SquareReductionSide.join01_23 word first second).count profile
  countRight_eq : ∀ profile, countRight profile =
    (squareGluedReductionSideProfileMultiset exteriorStates
      SquareReductionSide.join12_30 word first second).count profile

variable {countUp countLeft countRight : SquareInterfaceProfile B → ℕ}

/-- **Graph-level square count transport.**  The pointed count upstairs is the
sum of the two reduction counts, profile by profile. -/
theorem countUp_eq_add_of_extraction
    (extraction : ExteriorProfileExtraction countUp countLeft countRight)
    (profile : SquareInterfaceProfile B) :
    countUp profile = countLeft profile + countRight profile := by
  rw [extraction.countUp_eq, extraction.countLeft_eq, extraction.countRight_eq]
  exact squareGluedAdditiveProfileCountIdentity extraction.exteriorStates
    profile extraction.word extraction.first extraction.second
    extraction.word_nonzero extraction.first_ne_zero extraction.second_ne_zero
    extraction.first_ne_second

/-- **The pointed target count is additive.** -/
theorem sum_countUp_eq_add_of_extraction
    (extraction : ExteriorProfileExtraction countUp countLeft countRight)
    (targets : Finset (SquareInterfaceProfile B)) :
    ∑ profile ∈ targets, countUp profile =
      (∑ profile ∈ targets, countLeft profile) +
        (∑ profile ∈ targets, countRight profile) :=
  GoertzelV24SquareLadder.sum_eq_add_of_profilewise targets
    (countUp_eq_add_of_extraction extraction)

/-- **A least zero-target instance descends through both reductions.**  The
pointed total upstairs vanishes exactly when both reduction totals vanish, so
the square rung for a positivity target is additive rather than dynamical. -/
theorem sum_countUp_eq_zero_iff_of_extraction
    (extraction : ExteriorProfileExtraction countUp countLeft countRight)
    (targets : Finset (SquareInterfaceProfile B)) :
    (∑ profile ∈ targets, countUp profile) = 0 ↔
      (∑ profile ∈ targets, countLeft profile) = 0 ∧
        (∑ profile ∈ targets, countRight profile) = 0 :=
  GoertzelV24SquareLadder.sum_eq_zero_iff_of_profilewise targets
    (countUp_eq_add_of_extraction extraction)

end GoertzelV24SquareCountTransport

end Mettapedia.GraphTheory.FourColor

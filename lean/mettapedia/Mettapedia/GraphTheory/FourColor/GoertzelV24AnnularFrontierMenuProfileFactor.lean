import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfile

/-!
# Menu-B factorization through fixed-word connectivity profiles

The compositional `Count` profile is useful only if the counterexample
predicate is determined by it.  This file proves that finite-profile fact for
the Addendum-XXV seed predicate: once the inner word is fixed, Menu B depends
only on the selected-pair component partitions of its active cap ports.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The fixed-word carrier for one selected-pair connectivity coordinate.
Unlike a coloring-indexed subtype, this type is shared by every member of the
same source fiber. -/
abbrev AnnularFrontierWordPairPort
    (word : CAP5BoundaryWord) (first second : Color) :=
  {inner : Fin 5 // inner ∈ cap5ActiveSupport first second word}

/-- Re-index the literal component profile of a coloring by the word of its
fiber.  The equality proof is used only for transport of the finite carrier;
the components themselves are still computed from the actual coloring. -/
noncomputable def annularFrontierWordPairConnectionProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (word : CAP5BoundaryWord)
    (hword : data.innerBoundaryWord coloring = word)
    (first second : Color) :
    Finset
      (AnnularFrontierWordPairPort word first second ×
        AnnularFrontierWordPairPort word first second) := by
  subst word
  exact annularFrontierPairConnectionProfile data hdata coloring first second

/-- The Addendum-VII Menu-B test expressed on the fixed finite carrier of a
fiber. -/
theorem annularFrontierMenuBForPair_iff_exists_not_mem_wordConnectionProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (word : CAP5BoundaryWord)
    (hword : data.innerBoundaryWord coloring = word)
    (first second : Color) :
    AnnularFrontierMenuBForPair data coloring first second ↔
      ∃ left right : AnnularFrontierWordPairPort word first second,
        (left, right) ∉ annularFrontierWordPairConnectionProfile
          data hdata coloring word hword first second := by
  subst word
  exact annularFrontierMenuBForPair_iff_exists_not_mem_connectionProfile
    data hdata coloring first second

/-- Equality of the fixed-word component profile preserves Menu B for the
selected pair.  This is the exact local factorization that a corridor splice
uses; it does not assume any global coloring extension. -/
theorem annularFrontierMenuBForPair_iff_of_wordConnectionProfile_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (word : CAP5BoundaryWord)
    (hleftWord : data.innerBoundaryWord leftColoring = word)
    (hrightWord : data.innerBoundaryWord rightColoring = word)
    (first second : Color)
    (hprofile :
      annularFrontierWordPairConnectionProfile
        data hdata leftColoring word hleftWord first second =
      annularFrontierWordPairConnectionProfile
        data hdata rightColoring word hrightWord first second) :
    AnnularFrontierMenuBForPair data leftColoring first second ↔
      AnnularFrontierMenuBForPair data rightColoring first second := by
  rw [annularFrontierMenuBForPair_iff_exists_not_mem_wordConnectionProfile
        data hdata leftColoring word hleftWord first second,
    annularFrontierMenuBForPair_iff_exists_not_mem_wordConnectionProfile
        data hdata rightColoring word hrightWord first second]
  constructor
  · rintro ⟨left, right, hseparated⟩
    exact ⟨left, right, by simpa only [hprofile] using hseparated⟩
  · rintro ⟨left, right, hseparated⟩
    exact ⟨left, right, by simpa only [hprofile] using hseparated⟩

/-- The complete source Menu-B predicate factors through the finite
fixed-word connectivity profiles of the color pairs.  Thus a future splice
only needs to preserve those profile coordinates to preserve seed membership.
-/
theorem annularFrontierMenuBState_iff_of_wordConnectionProfiles_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (word : CAP5BoundaryWord)
    (hleftWord : data.innerBoundaryWord leftColoring = word)
    (hrightWord : data.innerBoundaryWord rightColoring = word)
    (hprofiles : ∀ first second : Color,
      annularFrontierWordPairConnectionProfile
        data hdata leftColoring word hleftWord first second =
      annularFrontierWordPairConnectionProfile
        data hdata rightColoring word hrightWord first second) :
    AnnularFrontierMenuBState data leftColoring ↔
      AnnularFrontierMenuBState data rightColoring := by
  constructor
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple, hmenu⟩
    have htripleAtWord : AnnularFrontierMajorityTriple
        word majority singletonFirst singletonSecond := by
      simpa only [hleftWord] using htriple
    have htripleRight : AnnularFrontierMajorityTriple
        (data.innerBoundaryWord rightColoring)
        majority singletonFirst singletonSecond := by
      rw [hrightWord]
      exact htripleAtWord
    refine ⟨majority, singletonFirst, singletonSecond, htripleRight, ?_⟩
    rcases hmenu with hfirst | hsecond
    · exact Or.inl
        ((annularFrontierMenuBForPair_iff_of_wordConnectionProfile_eq
          data hdata leftColoring rightColoring word hleftWord hrightWord
            majority singletonFirst (hprofiles majority singletonFirst)).mp hfirst)
    · exact Or.inr
        ((annularFrontierMenuBForPair_iff_of_wordConnectionProfile_eq
          data hdata leftColoring rightColoring word hleftWord hrightWord
            majority singletonSecond (hprofiles majority singletonSecond)).mp hsecond)
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple, hmenu⟩
    have htripleAtWord : AnnularFrontierMajorityTriple
        word majority singletonFirst singletonSecond := by
      simpa only [hrightWord] using htriple
    have htripleLeft : AnnularFrontierMajorityTriple
        (data.innerBoundaryWord leftColoring)
        majority singletonFirst singletonSecond := by
      rw [hleftWord]
      exact htripleAtWord
    refine ⟨majority, singletonFirst, singletonSecond, htripleLeft, ?_⟩
    rcases hmenu with hfirst | hsecond
    · exact Or.inl
        ((annularFrontierMenuBForPair_iff_of_wordConnectionProfile_eq
          data hdata leftColoring rightColoring word hleftWord hrightWord
            majority singletonFirst (hprofiles majority singletonFirst)).mpr hfirst)
    · exact Or.inr
        ((annularFrontierMenuBForPair_iff_of_wordConnectionProfile_eq
          data hdata leftColoring rightColoring word hleftWord hrightWord
            majority singletonSecond (hprofiles majority singletonSecond)).mpr hsecond)

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor

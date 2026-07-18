import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutColor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutStateOverlap

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The four equality types permitted by parity on a nonzero four-edge
boundary, with the cyclic order retained in the two adjacent-pair cases. -/
inductive FourBoundaryClass
  | allEqual
  | adjacent01_23
  | adjacent12_30
  | oppositePairs
  deriving DecidableEq, Fintype

namespace FourBoundaryClass

/-- A concrete boundary word has the named equality type. -/
def Holds (boundaryClass : FourBoundaryClass)
    (word : SquareBoundaryWord) : Prop :=
  match boundaryClass with
  | .allEqual => word.AllEqual
  | .adjacent01_23 => word.Adjacent01_23
  | .adjacent12_30 => word.Adjacent12_30
  | .oppositePairs => word.OppositePairs

instance (boundaryClass : FourBoundaryClass) (word : SquareBoundaryWord) :
    Decidable (boundaryClass.Holds word) := by
  cases boundaryClass <;> simp only [Holds] <;> infer_instance

end FourBoundaryClass

/-- A family of four-pole color states supports an equality class when it
contains a concrete word of that class. -/
def BoundaryClassSupported
    (states : Set SquareBoundaryWord)
    (boundaryClass : FourBoundaryClass) : Prop :=
  ∃ word, word ∈ states ∧ boundaryClass.Holds word

/-- The two noncrossing seam closures and the elementary all-equal Kempe
escape are exactly the class-level data used by the four-pole overlap
argument. The states themselves remain concrete boundary color words. -/
structure NoncrossingFourPoleStateProfile where
  states : Set SquareBoundaryWord
  nonzero : ∀ word, word ∈ states → word.Nonzero
  join01_23 : ∃ word, word ∈ states ∧
    SquareReductionSide.join01_23.Compatible word
  join12_30 : ∃ word, word ∈ states ∧
    SquareReductionSide.join12_30.Compatible word
  allEqualKempeEscape :
    BoundaryClassSupported states .allEqual →
      BoundaryClassSupported states .adjacent01_23 ∨
        BoundaryClassSupported states .adjacent12_30

namespace NoncrossingFourPoleStateProfile

def Supports (profile : NoncrossingFourPoleStateProfile)
    (boundaryClass : FourBoundaryClass) : Prop :=
  BoundaryClassSupported profile.states boundaryClass

/-- A nonzero word compatible with the `01|23` planar seam is either
all-equal or genuinely `01|23` adjacent-paired. -/
theorem nonzero_join01_23_classification :
    ∀ word : SquareBoundaryWord,
      word.Nonzero → SquareReductionSide.join01_23.Compatible word →
        FourBoundaryClass.allEqual.Holds word ∨
          FourBoundaryClass.adjacent01_23.Holds word := by
  decide

/-- The corresponding classification for the other noncrossing seam. -/
theorem nonzero_join12_30_classification :
    ∀ word : SquareBoundaryWord,
      word.Nonzero → SquareReductionSide.join12_30.Compatible word →
        FourBoundaryClass.allEqual.Holds word ∨
          FourBoundaryClass.adjacent12_30.Holds word := by
  decide

theorem supports_allEqual_or_adjacent01_23
    (profile : NoncrossingFourPoleStateProfile) :
    profile.Supports .allEqual ∨ profile.Supports .adjacent01_23 := by
  rcases profile.join01_23 with ⟨word, hword, hcompatible⟩
  rcases nonzero_join01_23_classification word
      (profile.nonzero word hword) hcompatible with hall | hadjacent
  · exact Or.inl ⟨word, hword, hall⟩
  · exact Or.inr ⟨word, hword, hadjacent⟩

theorem supports_allEqual_or_adjacent12_30
    (profile : NoncrossingFourPoleStateProfile) :
    profile.Supports .allEqual ∨ profile.Supports .adjacent12_30 := by
  rcases profile.join12_30 with ⟨word, hword, hcompatible⟩
  rcases nonzero_join12_30_classification word
      (profile.nonzero word hword) hcompatible with hall | hadjacent
  · exact Or.inl ⟨word, hword, hall⟩
  · exact Or.inr ⟨word, hword, hadjacent⟩

/-- If the all-equal class is absent, both adjacent-pair classes occur. -/
theorem supports_both_adjacent_of_not_allEqual
    (profile : NoncrossingFourPoleStateProfile)
    (hnot : ¬ profile.Supports .allEqual) :
    profile.Supports .adjacent01_23 ∧
      profile.Supports .adjacent12_30 := by
  exact ⟨(profile.supports_allEqual_or_adjacent01_23.resolve_left hnot),
    profile.supports_allEqual_or_adjacent12_30.resolve_left hnot⟩

/-- Two noncrossing four-pole profiles share one of the three reducible
boundary classes. The opposite-pair Birkhoff class is never needed: either
both profiles contain an all-equal state, or an all-equal state on one side
escapes by a Kempe switch into an adjacent class already forced on the
other side by its two seam closures. -/
theorem exists_common_reducible_class
    (left right : NoncrossingFourPoleStateProfile) :
    ∃ boundaryClass : FourBoundaryClass,
      (boundaryClass = .allEqual ∨ boundaryClass = .adjacent01_23 ∨
        boundaryClass = .adjacent12_30) ∧
      left.Supports boundaryClass ∧ right.Supports boundaryClass := by
  by_cases hleftAll : left.Supports .allEqual
  · by_cases hrightAll : right.Supports .allEqual
    · exact ⟨.allEqual, Or.inl rfl, hleftAll, hrightAll⟩
    · have hrightAdjacent :=
        right.supports_both_adjacent_of_not_allEqual hrightAll
      rcases left.allEqualKempeEscape hleftAll with hleft01 | hleft12
      · exact ⟨.adjacent01_23, Or.inr (Or.inl rfl),
          hleft01, hrightAdjacent.1⟩
      · exact ⟨.adjacent12_30, Or.inr (Or.inr rfl),
          hleft12, hrightAdjacent.2⟩
  · have hleftAdjacent :=
      left.supports_both_adjacent_of_not_allEqual hleftAll
    by_cases hrightAll : right.Supports .allEqual
    · rcases right.allEqualKempeEscape hrightAll with hright01 | hright12
      · exact ⟨.adjacent01_23, Or.inr (Or.inl rfl),
          hleftAdjacent.1, hright01⟩
      · exact ⟨.adjacent12_30, Or.inr (Or.inr rfl),
          hleftAdjacent.2, hright12⟩
    · have hrightAdjacent :=
        right.supports_both_adjacent_of_not_allEqual hrightAll
      exact ⟨.adjacent01_23, Or.inr (Or.inl rfl),
        hleftAdjacent.1, hrightAdjacent.1⟩

/-- Words in the same reducible equality class differ only by a global
permutation of the three nonzero Tait colors. The permutation fixes zero. -/
theorem exists_zeroFixingColorEquiv_of_same_reducible_class :
    ∀ (boundaryClass : FourBoundaryClass)
      (left right : SquareBoundaryWord),
      (boundaryClass = .allEqual ∨
        boundaryClass = .adjacent01_23 ∨
        boundaryClass = .adjacent12_30) →
      left.Nonzero → right.Nonzero →
      boundaryClass.Holds left → boundaryClass.Holds right →
      ∃ colorEquiv : Color ≃ Color,
        colorEquiv 0 = 0 ∧
          ∀ port : Fin 4, colorEquiv (left port) = right port := by
  intro boundaryClass left right hclass hleftNonzero hrightNonzero
    hleftClass hrightClass
  have exists_pair_alignment : ∀ {sourceFirst sourceSecond
      targetFirst targetSecond : Color},
      sourceFirst ≠ 0 → sourceSecond ≠ 0 →
      sourceFirst ≠ sourceSecond →
      targetFirst ≠ 0 → targetSecond ≠ 0 →
      targetFirst ≠ targetSecond →
      ∃ colorEquiv : Color ≃ Color,
        colorEquiv 0 = 0 ∧
        colorEquiv sourceFirst = targetFirst ∧
        colorEquiv sourceSecond = targetSecond := by
    intro sourceFirst sourceSecond targetFirst targetSecond
      hsourceFirst hsourceSecond hsourceNe
      htargetFirst htargetSecond htargetNe
    have hsourceThird := third_color_properties
      hsourceFirst hsourceSecond hsourceNe
    have htargetThird := third_color_properties
      htargetFirst htargetSecond htargetNe
    have hsourceTriple : IsTaitColorTriple
        sourceFirst sourceSecond (sourceFirst + sourceSecond) :=
      ⟨hsourceFirst, hsourceSecond, hsourceThird.1, hsourceNe,
        hsourceThird.2.1.symm, hsourceThird.2.2.symm⟩
    have htargetTriple : IsTaitColorTriple
        targetFirst targetSecond (targetFirst + targetSecond) :=
      ⟨htargetFirst, htargetSecond, htargetThird.1, htargetNe,
        htargetThird.2.1.symm, htargetThird.2.2.symm⟩
    let colorEquiv :=
      GoertzelV24ThreeEdgeCutColor.alignTaitTripleColorEquiv
        hsourceTriple htargetTriple
    exact ⟨colorEquiv,
      GoertzelV24ThreeEdgeCutColor.alignTaitTripleColorEquiv_zero
        hsourceTriple htargetTriple,
      GoertzelV24ThreeEdgeCutColor.alignTaitTripleColorEquiv_first
        hsourceTriple htargetTriple,
      GoertzelV24ThreeEdgeCutColor.alignTaitTripleColorEquiv_second
        hsourceTriple htargetTriple⟩
  rcases hclass with rfl | rfl | rfl
  · let colorEquiv : Color ≃ Color := Equiv.swap (left 0) (right 0)
    refine ⟨colorEquiv, ?_, ?_⟩
    · simp only [colorEquiv, Equiv.swap_apply_def]
      rw [if_neg (Ne.symm hleftNonzero.1),
        if_neg (Ne.symm hrightNonzero.1)]
    · intro port
      rcases hleftClass with ⟨hleft01, hleft12, hleft23⟩
      rcases hrightClass with ⟨hright01, hright12, hright23⟩
      fin_cases port
      · simp [colorEquiv]
      · simp [colorEquiv, ← hleft01, ← hright01]
      · simp [colorEquiv, ← hleft12, ← hleft01,
          ← hright12, ← hright01]
      · simp [colorEquiv, ← hleft23, ← hleft12, ← hleft01,
          ← hright23, ← hright12, ← hright01]
  · rcases hleftClass with ⟨hleft01, hleft23, hleftNe⟩
    rcases hrightClass with ⟨hright01, hright23, hrightNe⟩
    rcases exists_pair_alignment
        hleftNonzero.1 hleftNonzero.2.2.1 hleftNe
        hrightNonzero.1 hrightNonzero.2.2.1 hrightNe with
      ⟨colorEquiv, hzero, hfirst, hsecond⟩
    refine ⟨colorEquiv, hzero, ?_⟩
    intro port
    fin_cases port
    · exact hfirst
    · simpa [← hleft01, ← hright01] using hfirst
    · exact hsecond
    · simpa [← hleft23, ← hright23] using hsecond
  · rcases hleftClass with ⟨hleft12, hleft30, hleftNe⟩
    rcases hrightClass with ⟨hright12, hright30, hrightNe⟩
    rcases exists_pair_alignment
        hleftNonzero.2.1 hleftNonzero.2.2.2 hleftNe
        hrightNonzero.2.1 hrightNonzero.2.2.2 hrightNe with
      ⟨colorEquiv, hzero, hfirst, hsecond⟩
    refine ⟨colorEquiv, hzero, ?_⟩
    intro port
    fin_cases port
    · simpa [← hleft30, ← hright30] using hsecond
    · exact hfirst
    · simpa [← hleft12, ← hright12] using hfirst
    · exact hsecond

/-- Concrete interface form of the overlap theorem: the two profiles
contain boundary words that agree after one zero-fixing global color
permutation. -/
theorem exists_aligned_common_boundary_words
    (left right : NoncrossingFourPoleStateProfile) :
    ∃ (boundaryClass : FourBoundaryClass)
      (leftWord rightWord : SquareBoundaryWord)
      (colorEquiv : Color ≃ Color),
      (boundaryClass = .allEqual ∨
        boundaryClass = .adjacent01_23 ∨
        boundaryClass = .adjacent12_30) ∧
      leftWord ∈ left.states ∧ rightWord ∈ right.states ∧
      boundaryClass.Holds leftWord ∧ boundaryClass.Holds rightWord ∧
      colorEquiv 0 = 0 ∧
      ∀ port : Fin 4, colorEquiv (leftWord port) = rightWord port := by
  rcases exists_common_reducible_class left right with
    ⟨boundaryClass, hclass, ⟨leftWord, hleftMem, hleftClass⟩,
      ⟨rightWord, hrightMem, hrightClass⟩⟩
  rcases exists_zeroFixingColorEquiv_of_same_reducible_class
      boundaryClass leftWord rightWord hclass
      (left.nonzero leftWord hleftMem) (right.nonzero rightWord hrightMem)
      hleftClass hrightClass with ⟨colorEquiv, hzero, halign⟩
  exact ⟨boundaryClass, leftWord, rightWord, colorEquiv, hclass,
    hleftMem, hrightMem, hleftClass, hrightClass, hzero, halign⟩

end NoncrossingFourPoleStateProfile

end GoertzelV24FourEdgeCutStateOverlap

end Mettapedia.GraphTheory.FourColor

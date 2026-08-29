import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonTreeReplacementObstruction

/-!
# A single colour orbit cannot block all three smaller hexagon replacements

The literal hexagonal cell has no smaller connected cubic replacement whose
whole boundary support is contained in the hexagon support.  For one fixed
exterior, however, support inclusion is stronger than necessary: it suffices
that the exterior support be disjoint from the replacement support.

This file isolates the first exact restriction on such an exterior.  The
three canonical four-vertex plane-tree supports have empty common
intersection.  Since each support is invariant under a global permutation of
the three nonzero Tait colours, an exterior language contained in one global
colour orbit is disjoint from at least one of them.  Thus any exterior which
blocks all three local reductions must contain at least two colour orbits.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonSingleOrbitReplacement

open GoertzelV24HexagonTreeReplacementObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Apply one global colour renaming to a six-port boundary word. -/
def mapBoundaryWord (relabel : Color ≃ Color)
    (word : HexagonBoundaryWord) : HexagonBoundaryWord :=
  fun port => relabel (word port)

/-- Apply one global colour renaming to the three internal tree edges. -/
def mapTreeInternalColoring (relabel : Color ≃ Color)
    (internal : TreeInternalColoring) : TreeInternalColoring :=
  fun edge => relabel (internal edge)

/-- Properness of a cubic colour triple is preserved by an injective colour
renaming which fixes zero. -/
theorem properColorTriple_map_equiv_of_map_zero
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0)
    {first second third : Color}
    (hproper : ProperColorTriple first second third) :
    ProperColorTriple (relabel first) (relabel second) (relabel third) := by
  rcases hproper with
    ⟨hfirst, hsecond, hthird, hfirstSecond, hfirstThird, hsecondThird⟩
  refine ⟨?_, ?_, ?_, relabel.injective.ne hfirstSecond,
    relabel.injective.ne hfirstThird, relabel.injective.ne hsecondThird⟩
  · intro h
    exact hfirst (relabel.injective (h.trans hzero.symm))
  · intro h
    exact hsecond (relabel.injective (h.trans hzero.symm))
  · intro h
    exact hthird (relabel.injective (h.trans hzero.symm))

/-- A zero-fixing global colour renaming carries every proper colouring of a
canonical four-vertex tree to another proper colouring of the same tree. -/
theorem isTreeExtension_map_equiv_of_map_zero
    (shape : PlaneSixPortTreeShape)
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0)
    {word : HexagonBoundaryWord} {internal : TreeInternalColoring}
    (hextends : IsTreeExtension shape word internal) :
    IsTreeExtension shape (mapBoundaryWord relabel word)
      (mapTreeInternalColoring relabel internal) := by
  cases shape <;>
    rcases hextends with ⟨h₀, h₁, h₂, h₃⟩ <;>
    exact ⟨properColorTriple_map_equiv_of_map_zero relabel hzero h₀,
      properColorTriple_map_equiv_of_map_zero relabel hzero h₁,
      properColorTriple_map_equiv_of_map_zero relabel hzero h₂,
      properColorTriple_map_equiv_of_map_zero relabel hzero h₃⟩

/-- The inverse of a zero-fixing colour equivalence also fixes zero. -/
theorem symm_apply_zero_of_apply_zero
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0) :
    relabel.symm 0 = 0 := by
  apply relabel.injective
  simp [hzero]

/-- Two boundary words lie in the same global colour orbit when one is
obtained from the other by a zero-fixing colour equivalence. -/
def SameGlobalColorOrbit
    (left right : HexagonBoundaryWord) : Prop :=
  ∃ relabel : Color ≃ Color,
    relabel 0 = 0 ∧ mapBoundaryWord relabel left = right

/-- Membership in a canonical tree support can be pulled back along a global
colour-orbit witness. -/
theorem mem_treeSupport_of_sameGlobalColorOrbit_left
    {left right : HexagonBoundaryWord}
    (horbit : SameGlobalColorOrbit left right)
    (shape : PlaneSixPortTreeShape)
    (hright : right ∈ treeSupport shape) :
    left ∈ treeSupport shape := by
  rcases horbit with ⟨relabel, hzero, hmap⟩
  rcases hright with ⟨internal, hinternal⟩
  refine ⟨mapTreeInternalColoring relabel.symm internal, ?_⟩
  have hmapped := isTreeExtension_map_equiv_of_map_zero shape relabel.symm
    (symm_apply_zero_of_apply_zero relabel hzero) hinternal
  have hword : mapBoundaryWord relabel.symm right = left := by
    funext port
    have hport := congrFun hmap port
    change relabel.symm (right port) = left port
    rw [← hport]
    exact relabel.symm_apply_apply (left port)
  simpa [hword] using hmapped

/-- In the three-colour space, a proper triple consists of all three nonzero
colours.  Hence any other nonzero colour different from the first entry is
one of the remaining two entries. -/
theorem eq_second_or_eq_third_of_ne_zero_of_ne_first
    {first second third other : Color}
    (hproper : ProperColorTriple first second third)
    (hotherZero : other ≠ 0) (hotherFirst : other ≠ first) :
    other = second ∨ other = third := by
  rcases hproper with
    ⟨hfirstZero, hsecondZero, hthirdZero,
      hfirstSecond, hfirstThird, hsecondThird⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirstZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecondZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthirdZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero other hotherZero with
      rfl | rfl | rfl <;>
    simp_all

/-- A proper colour triple has zero Klein sum. -/
theorem properColorTriple_sum_eq_zero
    {first second third : Color}
    (hproper : ProperColorTriple first second third) :
    first + second + third = 0 := by
  rcases hproper with
    ⟨hfirstZero, hsecondZero, hthirdZero,
      hfirstSecond, hfirstThird, hsecondThird⟩
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirstZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecondZero with
      rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthirdZero with
      rfl | rfl | rfl <;>
    simp_all

/-- With two ordered entries fixed, the third entry of a proper colour
triple is unique. -/
theorem properColorTriple_first_eq_of_same_second_third
    {first other second third : Color}
    (hleft : ProperColorTriple first second third)
    (hright : ProperColorTriple other second third) :
    first = other := by
  have hleftSum := properColorTriple_sum_eq_zero hleft
  have hrightSum := properColorTriple_sum_eq_zero hright
  have heq : first + (second + third) = other + (second + third) := by
    rw [← add_assoc, hleftSum, ← add_assoc, hrightSum]
  exact add_right_cancel heq

/-- With the first two ordered entries fixed, the third entry of a proper
colour triple is unique. -/
theorem properColorTriple_third_eq_of_same_first_second
    {first second third other : Color}
    (hleft : ProperColorTriple first second third)
    (hright : ProperColorTriple first second other) :
    third = other := by
  have hleftSum := properColorTriple_sum_eq_zero hleft
  have hrightSum := properColorTriple_sum_eq_zero hright
  have heq : (first + second) + third = (first + second) + other := by
    exact hleftSum.trans hrightSum.symm
  exact add_left_cancel heq

/-- If two proper triples have the same first entry, their remaining two
entries agree up to exchange. -/
theorem properColorTriple_same_first_pair
    {root first second third fourth : Color}
    (hleft : ProperColorTriple root first second)
    (hright : ProperColorTriple root third fourth) :
    (first = third ∧ second = fourth) ∨
      (first = fourth ∧ second = third) := by
  have hthirdZero : third ≠ 0 := hright.2.1
  have hthirdRoot : third ≠ root := hright.2.2.2.1.symm
  rcases eq_second_or_eq_third_of_ne_zero_of_ne_first hleft
      hthirdZero hthirdRoot with hthird | hthird
  · left
    refine ⟨hthird.symm, ?_⟩
    subst third
    have hleftSum := properColorTriple_sum_eq_zero hleft
    have hrightSum := properColorTriple_sum_eq_zero hright
    have heq : (root + first) + second = (root + first) + fourth := by
      simpa [add_assoc] using hleftSum.trans hrightSum.symm
    exact add_left_cancel heq
  · right
    refine ⟨?_, hthird.symm⟩
    subst third
    have hleftSum := properColorTriple_sum_eq_zero hleft
    have hrightSum := properColorTriple_sum_eq_zero hright
    have heq : (root + second) + first = (root + second) + fourth := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hleftSum.trans hrightSum.symm
    exact add_left_cancel heq

/-- A word extending through both path-shaped replacements has equal colours
at ports `2` and `3`. -/
theorem path_extensions_force_port_two_eq_three
    {word : HexagonBoundaryWord}
    {separatedInternal adjacentInternal : TreeInternalColoring}
    (hseparated : IsTreeExtension .pathSeparated word separatedInternal)
    (hadjacent : IsTreeExtension .pathAdjacent word adjacentInternal) :
    word 2 = word 3 := by
  rcases hseparated with ⟨hs₀, hs₁, hs₂, hs₃⟩
  rcases hadjacent with ⟨ha₀, ha₁, ha₂, ha₃⟩
  have houter : separatedInternal 1 = adjacentInternal 2 :=
    properColorTriple_third_eq_of_same_first_second hs₂ ha₃
  have hinteriorPair := properColorTriple_same_first_pair hs₁ ha₁
  have hinterior :
      separatedInternal 0 = adjacentInternal 0 ∧
        separatedInternal 2 = adjacentInternal 2 := by
    rcases hinteriorPair with h | h
    · exact h
    · exact (hs₀.2.2.2.2.2 (h.1.trans houter.symm)).elim
  have had := hinterior.1
  have hlast := hinterior.2
  have hlastSeparated : separatedInternal 2 = separatedInternal 1 :=
    hlast.trans houter.symm
  have hremainingPair := properColorTriple_same_first_pair hs₀ ha₂
  have hright : separatedInternal 1 = adjacentInternal 1 := by
    rcases hremainingPair with h | h
    · exact h.2
    · exact (hs₃.2.2.2.2.1
        (h.2.symm.trans hlastSeparated.symm)).elim
  have hzeroEq : word 0 = word 3 := by
    apply properColorTriple_first_eq_of_same_second_third hs₀
    simpa [had, houter] using ha₁
  have htwoEq : word 0 = word 2 := by
    apply properColorTriple_first_eq_of_same_second_third hs₀
    simpa [had, hright] using ha₀
  exact htwoEq.symm.trans hzeroEq

/-- A word extending through the tripod replacement has different colours at
ports `2` and `3`, because they meet at one leaf. -/
theorem tripod_extension_forces_port_two_ne_three
    {word : HexagonBoundaryWord} {internal : TreeInternalColoring}
    (htripod : IsTreeExtension .tripod word internal) :
    word 2 ≠ word 3 :=
  htripod.2.2.1.2.2.2.1

theorem no_word_mem_three_treeSupports :
    ¬ ∃ word : HexagonBoundaryWord,
      word ∈ treeSupport .pathSeparated ∧
        word ∈ treeSupport .pathAdjacent ∧
          word ∈ treeSupport .tripod := by
  rintro ⟨word, hseparated, hadjacent, htripod⟩
  rcases hseparated with ⟨separatedInternal, hseparated⟩
  rcases hadjacent with ⟨adjacentInternal, hadjacent⟩
  rcases htripod with ⟨tripodInternal, htripod⟩
  exact tripod_extension_forces_port_two_ne_three htripod
    (path_extensions_force_port_two_eq_three hseparated hadjacent)

/-- Quantified form of the empty triple-intersection computation. -/
theorem no_word_mem_all_treeSupports :
    ¬ ∃ word : HexagonBoundaryWord,
      ∀ shape : PlaneSixPortTreeShape, word ∈ treeSupport shape := by
  rintro ⟨word, hword⟩
  exact no_word_mem_three_treeSupports
    ⟨word, hword .pathSeparated, hword .pathAdjacent, hword .tripod⟩

/-- A boundary language is contained in one global colour orbit if all its
words are global colour renamings of one representative.  The representative
need not itself belong to the language, so the empty language is included. -/
def IsSingleGlobalColorOrbit (support : Set HexagonBoundaryWord) : Prop :=
  ∃ representative : HexagonBoundaryWord,
    ∀ word ∈ support, SameGlobalColorOrbit representative word

/-- A single-orbit exterior language misses at least one of the three
canonical smaller plane-tree supports. -/
theorem exists_treeSupport_disjoint_of_singleGlobalColorOrbit
    {exteriorSupport : Set HexagonBoundaryWord}
    (horbit : IsSingleGlobalColorOrbit exteriorSupport) :
    ∃ shape : PlaneSixPortTreeShape,
      Disjoint exteriorSupport (treeSupport shape) := by
  rcases horbit with ⟨representative, horbit⟩
  by_cases hseparated : Disjoint exteriorSupport (treeSupport .pathSeparated)
  · exact ⟨.pathSeparated, hseparated⟩
  by_cases hadjacent : Disjoint exteriorSupport (treeSupport .pathAdjacent)
  · exact ⟨.pathAdjacent, hadjacent⟩
  by_cases htripod : Disjoint exteriorSupport (treeSupport .tripod)
  · exact ⟨.tripod, htripod⟩
  rcases Set.not_disjoint_iff.mp hseparated with
    ⟨separatedWord, hseparatedExterior, hseparatedTree⟩
  rcases Set.not_disjoint_iff.mp hadjacent with
    ⟨adjacentWord, hadjacentExterior, hadjacentTree⟩
  rcases Set.not_disjoint_iff.mp htripod with
    ⟨tripodWord, htripodExterior, htripodTree⟩
  exfalso
  apply no_word_mem_all_treeSupports
  refine ⟨representative, ?_⟩
  intro shape
  cases shape
  · exact mem_treeSupport_of_sameGlobalColorOrbit_left
      (horbit separatedWord hseparatedExterior) .pathSeparated hseparatedTree
  · exact mem_treeSupport_of_sameGlobalColorOrbit_left
      (horbit adjacentWord hadjacentExterior) .pathAdjacent hadjacentTree
  · exact mem_treeSupport_of_sameGlobalColorOrbit_left
      (horbit tripodWord htripodExterior) .tripod htripodTree

/-- Target-aware consequence.  If the original hexagon is uncolourable with
one fixed single-orbit exterior, then one canonical four-vertex tree is also
uncolourable with that exterior. -/
theorem exists_strict_tree_replacement_of_singleGlobalColorOrbit
    {exteriorSupport : Set HexagonBoundaryWord}
    (horbit : IsSingleGlobalColorOrbit exteriorSupport)
    (hzero : Disjoint exteriorSupport hexagonRawSupport) :
    ∃ shape : PlaneSixPortTreeShape,
      Disjoint exteriorSupport hexagonRawSupport ∧
        Disjoint exteriorSupport (treeSupport shape) := by
  rcases exists_treeSupport_disjoint_of_singleGlobalColorOrbit horbit with
    ⟨shape, hshape⟩
  exact ⟨shape, hzero, hshape⟩

end GoertzelV24HexagonSingleOrbitReplacement

end Mettapedia.GraphTheory.FourColor

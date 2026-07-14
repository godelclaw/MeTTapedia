import Mathlib.Tactic
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24WindingClassification

open scoped BigOperators

set_option maxRecDepth 100000

/-- The three nonzero Tait colors, separated from the ambient four-element
`Color` type so finite face-word checks never enumerate the forbidden zero. -/
inductive StrandColor where
  | a
  | b
  | c
deriving DecidableEq, Fintype

namespace StrandColor

/-- Embedding of the three-symbol alphabet into the existing `F2 x F2`
edge-color type. -/
def toColor : StrandColor -> Color
  | a => red
  | b => blue
  | c => purple

theorem toColor_injective : Function.Injective toColor := by
  intro x y h
  cases x <;> cases y
  · rfl
  · exact False.elim (red_ne_blue h)
  · exact False.elim (red_ne_purple h)
  · exact False.elim (red_ne_blue h.symm)
  · rfl
  · exact False.elim (blue_ne_purple h)
  · exact False.elim (red_ne_purple h.symm)
  · exact False.elim (blue_ne_purple h.symm)
  · rfl

theorem toColor_ne_zero (x : StrandColor) : x.toColor ≠ 0 := by
  cases x <;> simp [toColor]

/-- Every nonzero ambient color has a unique three-symbol representative. -/
theorem existsUnique_toColor_eq_of_ne_zero (color : Color) (hcolor : color ≠ 0) :
    ∃! x : StrandColor, x.toColor = color := by
  rcases color with ⟨x, y⟩
  fin_cases x <;> fin_cases y
  · exact False.elim (hcolor rfl)
  · refine ⟨.b, rfl, ?_⟩
    intro z hz
    cases z
    · change red = blue at hz
      exact False.elim (red_ne_blue hz)
    · rfl
    · change purple = blue at hz
      exact False.elim (blue_ne_purple hz.symm)
  · refine ⟨.a, rfl, ?_⟩
    intro z hz
    cases z
    · rfl
    · change blue = red at hz
      exact False.elim (red_ne_blue hz.symm)
    · change purple = red at hz
      exact False.elim (red_ne_purple hz.symm)
  · refine ⟨.c, rfl, ?_⟩
    intro z hz
    cases z
    · change red = purple at hz
      exact False.elim (red_ne_purple hz)
    · change blue = purple at hz
      exact False.elim (blue_ne_purple hz)
    · rfl

end StrandColor

/-- Successor in a nonempty cyclic index type. -/
def cyclicSucc {n : Nat} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- Signed step in the cyclic nonzero-color order
`red -> blue -> purple -> red`. Invalid or repeated steps score zero. -/
def colorStep (x y : StrandColor) : Int :=
  if (x = .a ∧ y = .b) ∨
      (x = .b ∧ y = .c) ∨
      (x = .c ∧ y = .a) then
    1
  else if (x = .b ∧ y = .a) ∨
      (x = .c ∧ y = .b) ∨
      (x = .a ∧ y = .c) then
    -1
  else
    0

/-- Total signed color change around a cyclic word. -/
def windingScore {n : Nat} (word : Fin (n + 1) -> StrandColor) : Int :=
  ∑ i, colorStep (word i) (word (cyclicSucc i))

/-- Local Tait condition on a cyclic boundary word: colors are nonzero and
successive boundary edges have different colors. -/
abbrev IsProperCyclicColorWord {n : Nat}
    (word : Fin (n + 1) -> StrandColor) : Prop :=
  ∀ i, word i ≠ word (cyclicSucc i)

/-- Every step of the word follows the positive cyclic color order. -/
abbrev IsPositiveChiral {n : Nat} (word : Fin (n + 1) -> StrandColor) : Prop :=
  ∀ i, colorStep (word i) (word (cyclicSucc i)) = 1

/-- Every step of the word follows the negative cyclic color order. -/
abbrev IsNegativeChiral {n : Nat} (word : Fin (n + 1) -> StrandColor) : Prop :=
  ∀ i, colorStep (word i) (word (cyclicSucc i)) = -1

/-- A word is rainbow when each of the three nonzero colors occurs. -/
abbrev IsRainbow {n : Nat} (word : Fin (n + 1) -> StrandColor) : Prop :=
  (∃ i, word i = .a) ∧ (∃ i, word i = .b) ∧ (∃ i, word i = .c)

/-- A word is bicolored when all entries lie in some pair of distinct
nonzero colors. The definition does not identify bicoloredness with winding. -/
abbrev IsBicolored {n : Nat} (word : Fin (n + 1) -> StrandColor) : Prop :=
  ∃ x y : StrandColor, x ≠ y ∧ ∀ i, word i = x ∨ word i = y

/-- On a pentagonal word over exactly three available colors, being supported
on two colors is equivalent to omitting at least one color. -/
theorem pentagon_bicolored_iff_not_rainbow :
    ∀ word : Fin 5 -> StrandColor, IsBicolored word ↔ ¬ IsRainbow word := by
  decide

/-- Hexagonal form of the same bicolored/rainbow equivalence. -/
theorem hexagon_bicolored_iff_not_rainbow :
    ∀ word : Fin 6 -> StrandColor, IsBicolored word ↔ ¬ IsRainbow word := by
  decide

/-- A proper pentagon is necessarily rainbow: an odd cyclic word cannot
alternate between only two colors. -/
theorem proper_pentagon_rainbow :
    ∀ word : Fin 5 -> StrandColor,
      IsProperCyclicColorWord word -> IsRainbow word := by
  decide

/-- Every proper pentagonal color word has winding score `+3` or `-3`, hence
winding number `+1` or `-1`. -/
theorem proper_pentagon_windingScore :
    ∀ word : Fin 5 -> StrandColor,
      IsProperCyclicColorWord word ->
        windingScore word = 3 ∨ windingScore word = -3 := by
  decide

/-- Every proper hexagonal color word has score `0`, `+6`, or `-6`, hence
winding number `0`, `+2`, or `-2`. -/
theorem proper_hexagon_windingScore :
    ∀ word : Fin 6 -> StrandColor,
      IsProperCyclicColorWord word ->
        windingScore word = 0 ∨ windingScore word = 6 ∨ windingScore word = -6 := by
  decide

/-- A proper hexagon has extremal positive winding exactly when all six steps
follow the positive cyclic color order. -/
theorem proper_hexagon_windingScore_eq_six_iff_positiveChiral :
    ∀ word : Fin 6 -> StrandColor,
      IsProperCyclicColorWord word ->
        (windingScore word = 6 ↔ IsPositiveChiral word) := by
  decide

/-- A proper hexagon has extremal negative winding exactly when all six steps
follow the negative cyclic color order. -/
theorem proper_hexagon_windingScore_eq_neg_six_iff_negativeChiral :
    ∀ word : Fin 6 -> StrandColor,
      IsProperCyclicColorWord word ->
        (windingScore word = -6 ↔ IsNegativeChiral word) := by
  decide

/-- A proper bicolored hexagon has winding zero. -/
theorem proper_bicolored_hexagon_windingScore_eq_zero :
    ∀ word : Fin 6 -> StrandColor,
      IsProperCyclicColorWord word ->
      IsBicolored word ->
        windingScore word = 0 := by
  decide

/-- The manuscript's melted rainbow hexagon `red,blue,red,purple,red,blue`. -/
def meltedRainbowHexagon : Fin 6 -> StrandColor
  | 0 => .a
  | 1 => .b
  | 2 => .a
  | 3 => .c
  | 4 => .a
  | 5 => .b

theorem meltedRainbowHexagon_proper :
    IsProperCyclicColorWord meltedRainbowHexagon := by
  decide

theorem meltedRainbowHexagon_rainbow : IsRainbow meltedRainbowHexagon := by
  exact ⟨⟨0, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩⟩

theorem meltedRainbowHexagon_not_bicolored :
    ¬ IsBicolored meltedRainbowHexagon := by
  decide

/-- Winding zero does not characterize bicolored hexagons: the melted rainbow
word is proper and rainbow but also has score zero. -/
theorem meltedRainbowHexagon_windingScore_eq_zero :
    windingScore meltedRainbowHexagon = 0 := by
  decide

end GoertzelV24WindingClassification

end Mettapedia.GraphTheory.FourColor

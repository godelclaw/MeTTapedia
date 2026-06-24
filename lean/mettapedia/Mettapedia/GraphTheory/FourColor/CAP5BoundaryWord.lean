import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

/-!
Finite boundary-word layer for the CAP5 obstruction in the latest Goertzel manuscript.

This file isolates the purely local 5-cycle coloring calculation: which boundary words on
the five dangling cap edges extend across the internal 5-cycle.
-/

/-- A CAP5 boundary word records the colors on the five dangling cap edges. -/
abbrev CAP5BoundaryWord := Fin 5 → Color

/-- A coloring of the five internal edges of the cap 5-cycle. Edge `i` joins cap vertices
`i` and `i + 1`, so vertex `i` sees internal edges `i - 1` and `i`. -/
abbrev CAP5InternalCycleColoring := Fin 5 → Color

/-- A proper cubic vertex color triple over the three nonzero `𝔽₂²` colors. -/
def IsTaitColorTriple (a b c : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- The boundary word `w` extends across the internal cap 5-cycle by internal edge coloring `x`. -/
def CAP5ExtendsAcrossCycleWith (w : CAP5BoundaryWord) (x : CAP5InternalCycleColoring) : Prop :=
  IsTaitColorTriple (w 0) (x 4) (x 0) ∧
  IsTaitColorTriple (w 1) (x 0) (x 1) ∧
  IsTaitColorTriple (w 2) (x 1) (x 2) ∧
  IsTaitColorTriple (w 3) (x 2) (x 3) ∧
  IsTaitColorTriple (w 4) (x 3) (x 4)

/-- A boundary word is CAP5-extendable when some internal 5-cycle coloring makes each cap vertex
proper. -/
def CAP5WordExtendsAcrossCycle (w : CAP5BoundaryWord) : Prop :=
  ∃ x : CAP5InternalCycleColoring, CAP5ExtendsAcrossCycleWith w x

/-- Normal-form good CAP5 word with block structure `(3,1,1)`. -/
def cap5GoodBoundaryWord311 : CAP5BoundaryWord
  | 0 => red
  | 1 => red
  | 2 => red
  | 3 => blue
  | 4 => purple

/-- The internal 5-cycle coloring that extends `cap5GoodBoundaryWord311`. -/
def cap5GoodInternalColoring311 : CAP5InternalCycleColoring
  | 0 => purple
  | 1 => blue
  | 2 => purple
  | 3 => red
  | 4 => blue

/-- The canonical block-`(3,1,1)` CAP5 boundary word extends across the cap. -/
theorem cap5GoodBoundaryWord311_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle cap5GoodBoundaryWord311 := by
  refine ⟨cap5GoodInternalColoring311, ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5GoodBoundaryWord311,
    cap5GoodInternalColoring311, red, blue, purple]

/-- Normal-form bad CAP5 word with block structure `(2,1,1,1)`. -/
def cap5BadBoundaryWord2111 : CAP5BoundaryWord
  | 0 => red
  | 1 => red
  | 2 => blue
  | 3 => red
  | 4 => purple

theorem color_eq_purple_of_ne_zero_of_ne_red_of_ne_blue {c : Color}
    (h0 : c ≠ 0) (hr : c ≠ red) (hb : c ≠ blue) :
    c = purple := by
  rcases c with ⟨c₁, c₂⟩
  fin_cases c₁ <;> fin_cases c₂
  · exfalso
    exact h0 rfl
  · exfalso
    exact hb rfl
  · exfalso
    exact hr rfl
  · rfl

/-- The canonical block-`(2,1,1,1)` CAP5 boundary word does not extend across the cap. -/
theorem not_cap5BadBoundaryWord2111_extendsAcrossCycle :
    ¬ CAP5WordExtendsAcrossCycle cap5BadBoundaryWord2111 := by
  rintro ⟨x, hx⟩
  rcases hx with ⟨_hv0, hv1, hv2, hv3, _hv4⟩
  rcases hv1 with ⟨_hw1, _hx0, hx1, _hw1_x0, hw1_x1, _hx0_x1⟩
  rcases hv2 with ⟨_hw2, _hx1', hx2, hw2_x1, hw2_x2, hx1_x2⟩
  rcases hv3 with ⟨_hw3, _hx2', _hx3, hw3_x2, _hw3_x3, _hx2_x3⟩
  have hx1_ne_red : x 1 ≠ red := by
    intro h
    exact hw1_x1 (by simp [cap5BadBoundaryWord2111, h])
  have hx1_ne_blue : x 1 ≠ blue := by
    intro h
    exact hw2_x1 (by simp [cap5BadBoundaryWord2111, h])
  have hx1_eq_purple : x 1 = purple :=
    color_eq_purple_of_ne_zero_of_ne_red_of_ne_blue hx1 hx1_ne_red hx1_ne_blue
  have hx2_ne_blue : x 2 ≠ blue := by
    intro h
    exact hw2_x2 (by simp [cap5BadBoundaryWord2111, h])
  have hx2_ne_red : x 2 ≠ red := by
    intro h
    exact hw3_x2 (by simp [cap5BadBoundaryWord2111, h])
  have hx2_eq_purple : x 2 = purple :=
    color_eq_purple_of_ne_zero_of_ne_red_of_ne_blue hx2 hx2_ne_red hx2_ne_blue
  exact hx1_x2 (hx1_eq_purple.trans hx2_eq_purple.symm)

/-- Swap two colors, leaving the third color fixed. -/
def cap5SwapColor (a b : Color) (c : Color) : Color :=
  if c = a then b else if c = b then a else c

/-- Boundary operation that swaps colors `a` and `b` exactly on support `S`. -/
def cap5BoundarySwap (a b : Color) (S : Finset (Fin 5))
    (w : CAP5BoundaryWord) : CAP5BoundaryWord :=
  fun i => if i ∈ S then cap5SwapColor a b (w i) else w i

/-- First red/blue finite CAP5 repair type: swap positions `{0,1}`. -/
theorem cap5BadBoundaryWord2111_repair_red_blue_01_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => purple
    | 1 => red
    | 2 => purple
    | 3 => blue
    | 4 => red), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Second red/blue finite CAP5 repair type: swap positions `{0,2}`. -/
theorem cap5BadBoundaryWord2111_repair_red_blue_02_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => purple
    | 1 => blue
    | 2 => purple
    | 3 => blue
    | 4 => red), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Third red/blue finite CAP5 repair type: swap positions `{1,3}`. -/
theorem cap5BadBoundaryWord2111_repair_red_blue_13_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => purple
    | 1 => red
    | 2 => purple
    | 3 => red
    | 4 => blue), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Fourth red/blue finite CAP5 repair type: swap positions `{2,3}`. -/
theorem cap5BadBoundaryWord2111_repair_red_blue_23_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => purple
    | 1 => blue
    | 2 => purple
    | 3 => red
    | 4 => blue), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- First red/purple finite CAP5 repair type: swap positions `{0,1}`. -/
theorem cap5BadBoundaryWord2111_repair_red_purple_01_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => blue
    | 1 => red
    | 2 => purple
    | 3 => blue
    | 4 => red), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Second red/purple finite CAP5 repair type: swap positions `{0,3}`. -/
theorem cap5BadBoundaryWord2111_repair_red_purple_03_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({0, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => blue
    | 1 => purple
    | 2 => red
    | 3 => blue
    | 4 => red), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Third red/purple finite CAP5 repair type: swap positions `{1,4}`. -/
theorem cap5BadBoundaryWord2111_repair_red_purple_14_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({1, 4} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => blue
    | 1 => red
    | 2 => purple
    | 3 => blue
    | 4 => purple), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- Fourth red/purple finite CAP5 repair type: swap positions `{3,4}`. -/
theorem cap5BadBoundaryWord2111_repair_red_purple_34_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({3, 4} : Finset (Fin 5)) cap5BadBoundaryWord2111) := by
  refine ⟨(fun
    | 0 => blue
    | 1 => purple
    | 2 => red
    | 3 => blue
    | 4 => purple), ?_⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundarySwap,
    cap5SwapColor, cap5BadBoundaryWord2111, red, blue, purple]

/-- The eight canonical finite repair types from the CAP5 normal-form calculation all turn the
canonical bad boundary word into a CAP5-extendable boundary word. -/
theorem cap5BadBoundaryWord2111_repairBasis_extendsAcrossCycle :
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({0, 1} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({0, 2} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({1, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red blue ({2, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({0, 1} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({0, 3} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({1, 4} : Finset (Fin 5)) cap5BadBoundaryWord2111) ∧
    CAP5WordExtendsAcrossCycle
      (cap5BoundarySwap red purple ({3, 4} : Finset (Fin 5)) cap5BadBoundaryWord2111) :=
  ⟨cap5BadBoundaryWord2111_repair_red_blue_01_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_blue_02_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_blue_13_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_blue_23_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_purple_01_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_purple_03_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_purple_14_extendsAcrossCycle,
    cap5BadBoundaryWord2111_repair_red_purple_34_extendsAcrossCycle⟩

/-- The eight canonical finite CAP5 repair types in the normal-form boundary word calculation. -/
inductive CAP5RepairType where
  | redBlue01
  | redBlue02
  | redBlue13
  | redBlue23
  | redPurple01
  | redPurple03
  | redPurple14
  | redPurple34

namespace CAP5RepairType

/-- The color pair swapped by a finite CAP5 repair type. -/
def colorPair : CAP5RepairType → Color × Color
  | redBlue01 => (red, blue)
  | redBlue02 => (red, blue)
  | redBlue13 => (red, blue)
  | redBlue23 => (red, blue)
  | redPurple01 => (red, purple)
  | redPurple03 => (red, purple)
  | redPurple14 => (red, purple)
  | redPurple34 => (red, purple)

/-- The two boundary positions acted on by a finite CAP5 repair type. -/
def support : CAP5RepairType → Finset (Fin 5)
  | redBlue01 => {0, 1}
  | redBlue02 => {0, 2}
  | redBlue13 => {1, 3}
  | redBlue23 => {2, 3}
  | redPurple01 => {0, 1}
  | redPurple03 => {0, 3}
  | redPurple14 => {1, 4}
  | redPurple34 => {3, 4}

/-- Apply a finite CAP5 repair type as a boundary-word operation. -/
def apply (τ : CAP5RepairType) (w : CAP5BoundaryWord) : CAP5BoundaryWord :=
  cap5BoundarySwap (colorPair τ).1 (colorPair τ).2 (support τ) w

/-- Every canonical finite CAP5 repair type repairs the canonical bad word into an
extendable boundary word. -/
theorem apply_bad_extendsAcrossCycle (τ : CAP5RepairType) :
    CAP5WordExtendsAcrossCycle (τ.apply cap5BadBoundaryWord2111) := by
  cases τ <;> simp [apply, colorPair, support]
  · exact cap5BadBoundaryWord2111_repair_red_blue_01_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_blue_02_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_blue_13_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_blue_23_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_purple_01_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_purple_03_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_purple_14_extendsAcrossCycle
  · exact cap5BadBoundaryWord2111_repair_red_purple_34_extendsAcrossCycle

end CAP5RepairType

/-- A boundary word `w'` realizes one of the finite repair actions on `w`.  Later
graph-level Kempe-component realizability theorems should target this interface. -/
def CAP5RealizesRepairType (w w' : CAP5BoundaryWord) : Prop :=
  ∃ τ : CAP5RepairType, w' = τ.apply w

/-- If a boundary action realizes one of the finite CAP5 repair types on the canonical bad word,
then the resulting boundary word extends across the cap. -/
theorem cap5_extendsAcrossCycle_of_realizesRepairType_bad
    {w' : CAP5BoundaryWord}
    (h : CAP5RealizesRepairType cap5BadBoundaryWord2111 w') :
    CAP5WordExtendsAcrossCycle w' := by
  rcases h with ⟨τ, rfl⟩
  exact τ.apply_bad_extendsAcrossCycle

end Mettapedia.GraphTheory.FourColor

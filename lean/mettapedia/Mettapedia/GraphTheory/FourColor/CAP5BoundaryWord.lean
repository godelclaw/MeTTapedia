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

/-- A boundary action transforms CAP5 boundary words.  A graph-level outside-only Kempe component
will later supply this map by restricting its color swap to the five cap boundary edges. -/
abbrev CAP5BoundaryAction := CAP5BoundaryWord → CAP5BoundaryWord

/-- A boundary action induces a named finite repair type at a given boundary word. -/
def CAP5BoundaryActionInducesRepairType
    (action : CAP5BoundaryAction) (w : CAP5BoundaryWord) (τ : CAP5RepairType) : Prop :=
  action w = τ.apply w

/-- Boundary-action form of `CAP5RealizesRepairType`: if the action induces a repair type, its
output word realizes that repair type. -/
theorem cap5RealizesRepairType_of_boundaryActionInducesRepairType
    {action : CAP5BoundaryAction} {w : CAP5BoundaryWord} {τ : CAP5RepairType}
    (h : CAP5BoundaryActionInducesRepairType action w τ) :
    CAP5RealizesRepairType w (action w) := by
  exact ⟨τ, h⟩

/-- A boundary action realizes some finite repair type at a given boundary word. -/
def CAP5BoundaryActionRealizesSomeRepairType
    (action : CAP5BoundaryAction) (w : CAP5BoundaryWord) : Prop :=
  ∃ τ : CAP5RepairType, CAP5BoundaryActionInducesRepairType action w τ

/-- If a boundary action induces a particular finite repair type on the canonical bad word, then
the action's output extends across the CAP5 cap. -/
theorem cap5_extendsAcrossCycle_of_boundaryActionInducesRepairType_bad
    {action : CAP5BoundaryAction} {τ : CAP5RepairType}
    (h : CAP5BoundaryActionInducesRepairType action cap5BadBoundaryWord2111 τ) :
    CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) :=
  cap5_extendsAcrossCycle_of_realizesRepairType_bad
    (cap5RealizesRepairType_of_boundaryActionInducesRepairType h)

/-- If a boundary action realizes some finite repair type on the canonical bad word, then the
action's output extends across the CAP5 cap. -/
theorem cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeRepairType_bad
    {action : CAP5BoundaryAction}
    (h : CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111) :
    CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) := by
  rcases h with ⟨τ, hτ⟩
  exact cap5_extendsAcrossCycle_of_boundaryActionInducesRepairType_bad (τ := τ) hτ

/-- The boundary indices carrying one of two colors in a CAP5 word. -/
def cap5ActiveSupport (a b : Color) (w : CAP5BoundaryWord) : Finset (Fin 5) :=
  Finset.univ.filter fun i => w i = a ∨ w i = b

/-- In the canonical bad CAP5 word, the red/blue active indices are `{0,1,2,3}`. -/
theorem cap5BadBoundaryWord2111_activeSupport_red_blue :
    cap5ActiveSupport red blue cap5BadBoundaryWord2111 = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;> simp [cap5ActiveSupport, cap5BadBoundaryWord2111, red, blue, purple]

/-- In the canonical bad CAP5 word, the red/purple active indices are `{0,1,3,4}`. -/
theorem cap5BadBoundaryWord2111_activeSupport_red_purple :
    cap5ActiveSupport red purple cap5BadBoundaryWord2111 = ({0, 1, 3, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;> simp [cap5ActiveSupport, cap5BadBoundaryWord2111, red, blue, purple]

/-- The two red/blue pair supports in the exceptional CAP5 pairing pattern. -/
def CAP5BadRedBlueExceptionalSupport (S : Finset (Fin 5)) : Prop :=
  S = {0, 3} ∨ S = {1, 2}

/-- The two red/purple pair supports in the exceptional CAP5 pairing pattern. -/
def CAP5BadRedPurpleExceptionalSupport (S : Finset (Fin 5)) : Prop :=
  S = {0, 4} ∨ S = {1, 3}

/-- Red/blue pair supports that are immediate finite repairs for the canonical bad word. -/
def CAP5BadRedBlueRepairSupport (S : Finset (Fin 5)) : Prop :=
  S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 3} ∨ S = {2, 3}

/-- Red/purple pair supports that are immediate finite repairs for the canonical bad word. -/
def CAP5BadRedPurpleRepairSupport (S : Finset (Fin 5)) : Prop :=
  S = {0, 1} ∨ S = {0, 3} ∨ S = {1, 4} ∨ S = {3, 4}

/-- The three unordered red/blue pairings of the active support `{0,1,2,3}` for the
canonical bad CAP5 word, written with ordered component slots. -/
def CAP5BadRedBlueActivePairing (S₁ S₂ : Finset (Fin 5)) : Prop :=
  (S₁ = {0, 1} ∧ S₂ = {2, 3}) ∨
  (S₁ = {2, 3} ∧ S₂ = {0, 1}) ∨
  (S₁ = {0, 2} ∧ S₂ = {1, 3}) ∨
  (S₁ = {1, 3} ∧ S₂ = {0, 2}) ∨
  (S₁ = {0, 3} ∧ S₂ = {1, 2}) ∨
  (S₁ = {1, 2} ∧ S₂ = {0, 3})

/-- The three unordered red/purple pairings of the active support `{0,1,3,4}` for the
canonical bad CAP5 word, written with ordered component slots. -/
def CAP5BadRedPurpleActivePairing (S₁ S₂ : Finset (Fin 5)) : Prop :=
  (S₁ = {0, 1} ∧ S₂ = {3, 4}) ∨
  (S₁ = {3, 4} ∧ S₂ = {0, 1}) ∨
  (S₁ = {0, 3} ∧ S₂ = {1, 4}) ∨
  (S₁ = {1, 4} ∧ S₂ = {0, 3}) ∨
  (S₁ = {0, 4} ∧ S₂ = {1, 3}) ∨
  (S₁ = {1, 3} ∧ S₂ = {0, 4})

/-- The exceptional red/blue pairing in the canonical bad CAP5 word. -/
def CAP5BadRedBlueExceptionalPairing (S₁ S₂ : Finset (Fin 5)) : Prop :=
  (S₁ = {0, 3} ∧ S₂ = {1, 2}) ∨
  (S₁ = {1, 2} ∧ S₂ = {0, 3})

/-- The exceptional red/purple pairing in the canonical bad CAP5 word. -/
def CAP5BadRedPurpleExceptionalPairing (S₁ S₂ : Finset (Fin 5)) : Prop :=
  (S₁ = {0, 4} ∧ S₂ = {1, 3}) ∨
  (S₁ = {1, 3} ∧ S₂ = {0, 4})

/-- The simultaneous exceptional pairing pattern from the manuscript, stated at the level of
boundary supports.  The order of the two components in each color pair is irrelevant. -/
def CAP5BadExceptionalPairingPattern
    (redBlue₁ redBlue₂ redPurple₁ redPurple₂ : Finset (Fin 5)) : Prop :=
  CAP5BadRedBlueExceptionalPairing redBlue₁ redBlue₂ ∧
  CAP5BadRedPurpleExceptionalPairing redPurple₁ redPurple₂

/-- Every red/blue pairing of `{0,1,2,3}` either exposes a repair support or is the exceptional
red/blue pairing. -/
theorem cap5BadRedBlueActivePairing_repair_or_exceptional
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedBlueActivePairing S₁ S₂) :
    CAP5BadRedBlueRepairSupport S₁ ∨
      CAP5BadRedBlueRepairSupport S₂ ∨
      CAP5BadRedBlueExceptionalPairing S₁ S₂ := by
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [CAP5BadRedBlueRepairSupport, CAP5BadRedBlueExceptionalPairing]

/-- Every red/purple pairing of `{0,1,3,4}` either exposes a repair support or is the exceptional
red/purple pairing. -/
theorem cap5BadRedPurpleActivePairing_repair_or_exceptional
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedPurpleActivePairing S₁ S₂) :
    CAP5BadRedPurpleRepairSupport S₁ ∨
      CAP5BadRedPurpleRepairSupport S₂ ∨
      CAP5BadRedPurpleExceptionalPairing S₁ S₂ := by
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [CAP5BadRedPurpleRepairSupport, CAP5BadRedPurpleExceptionalPairing]

/-- The exceptional red/blue pairing exposes no red/blue repair support. -/
theorem not_cap5BadRedBlueRepairSupport_of_exceptionalPairing
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedBlueExceptionalPairing S₁ S₂) :
    ¬ CAP5BadRedBlueRepairSupport S₁ ∧ ¬ CAP5BadRedBlueRepairSupport S₂ := by
  rcases h with h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [CAP5BadRedBlueRepairSupport] <;>
    decide

/-- The exceptional red/purple pairing exposes no red/purple repair support. -/
theorem not_cap5BadRedPurpleRepairSupport_of_exceptionalPairing
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedPurpleExceptionalPairing S₁ S₂) :
    ¬ CAP5BadRedPurpleRepairSupport S₁ ∧ ¬ CAP5BadRedPurpleRepairSupport S₂ := by
  rcases h with h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [CAP5BadRedPurpleRepairSupport] <;>
    decide

/-- Any red/blue support on the repair side of the CAP5 split induces one of the eight finite
repair types on the canonical bad word. -/
theorem cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad
    {S : Finset (Fin 5)}
    (hS : CAP5BadRedBlueRepairSupport S) :
    CAP5BoundaryActionRealizesSomeRepairType (cap5BoundarySwap red blue S)
      cap5BadBoundaryWord2111 := by
  rcases hS with rfl | rfl | rfl | rfl
  · exact ⟨CAP5RepairType.redBlue01, rfl⟩
  · exact ⟨CAP5RepairType.redBlue02, rfl⟩
  · exact ⟨CAP5RepairType.redBlue13, rfl⟩
  · exact ⟨CAP5RepairType.redBlue23, rfl⟩

/-- Any red/purple support on the repair side of the CAP5 split induces one of the eight finite
repair types on the canonical bad word. -/
theorem cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad
    {S : Finset (Fin 5)}
    (hS : CAP5BadRedPurpleRepairSupport S) :
    CAP5BoundaryActionRealizesSomeRepairType (cap5BoundarySwap red purple S)
      cap5BadBoundaryWord2111 := by
  rcases hS with rfl | rfl | rfl | rfl
  · exact ⟨CAP5RepairType.redPurple01, rfl⟩
  · exact ⟨CAP5RepairType.redPurple03, rfl⟩
  · exact ⟨CAP5RepairType.redPurple14, rfl⟩
  · exact ⟨CAP5RepairType.redPurple34, rfl⟩

/-- Red/blue support-level form of immediate CAP5 repair. -/
theorem cap5_extendsAcrossCycle_of_redBlueRepairSupport_bad
    {S : Finset (Fin 5)}
    (hS : CAP5BadRedBlueRepairSupport S) :
    CAP5WordExtendsAcrossCycle (cap5BoundarySwap red blue S cap5BadBoundaryWord2111) :=
  cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeRepairType_bad
    (cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad hS)

/-- Red/purple support-level form of immediate CAP5 repair. -/
theorem cap5_extendsAcrossCycle_of_redPurpleRepairSupport_bad
    {S : Finset (Fin 5)}
    (hS : CAP5BadRedPurpleRepairSupport S) :
    CAP5WordExtendsAcrossCycle (cap5BoundarySwap red purple S cap5BadBoundaryWord2111) :=
  cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeRepairType_bad
    (cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad hS)

/-- The four two-color component supports that appear in the normalized CAP5 bad-word
move-realizability split: two red/blue components and two red/purple components. -/
structure CAP5BadPairingSupports where
  redBlue₁ : Finset (Fin 5)
  redBlue₂ : Finset (Fin 5)
  redPurple₁ : Finset (Fin 5)
  redPurple₂ : Finset (Fin 5)

namespace CAP5BadPairingSupports

/-- One of the four component supports is already on the finite repair side. -/
def HasRepair (p : CAP5BadPairingSupports) : Prop :=
  CAP5BadRedBlueRepairSupport p.redBlue₁ ∨
  CAP5BadRedBlueRepairSupport p.redBlue₂ ∨
  CAP5BadRedPurpleRepairSupport p.redPurple₁ ∨
  CAP5BadRedPurpleRepairSupport p.redPurple₂

/-- The simultaneous exceptional pattern left over when no immediate repair support appears. -/
def IsExceptional (p : CAP5BadPairingSupports) : Prop :=
  CAP5BadExceptionalPairingPattern p.redBlue₁ p.redBlue₂ p.redPurple₁ p.redPurple₂

/-- The exact finite target for the graph-level move-realizability lemma: either an immediate
repair support is present, or the exceptional pairing pattern is the remaining obstruction. -/
def RepairOrExceptional (p : CAP5BadPairingSupports) : Prop :=
  p.HasRepair ∨ p.IsExceptional

/-- The two color-pair component families really pair the active CAP5 boundary supports in the
normalized bad word: red/blue pairs `{0,1,2,3}` and red/purple pairs `{0,1,3,4}`. -/
def HasActivePairings (p : CAP5BadPairingSupports) : Prop :=
  CAP5BadRedBlueActivePairing p.redBlue₁ p.redBlue₂ ∧
  CAP5BadRedPurpleActivePairing p.redPurple₁ p.redPurple₂

/-- Finite pairing enumeration for the normalized CAP5 bad word: once the outside components
give pairings of the two active four-point supports, either a repair support appears or the
simultaneous exceptional pairing pattern is the only remaining case. -/
theorem repairOrExceptional_of_activePairings
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    p.RepairOrExceptional := by
  rcases h with ⟨hredBlue, hredPurple⟩
  have hredBlue' :=
    cap5BadRedBlueActivePairing_repair_or_exceptional hredBlue
  have hredPurple' :=
    cap5BadRedPurpleActivePairing_repair_or_exceptional hredPurple
  rcases hredBlue' with hredBlue₁ | hredBlue₂ | hredBlueExceptional
  · exact Or.inl (Or.inl hredBlue₁)
  · exact Or.inl (Or.inr (Or.inl hredBlue₂))
  · rcases hredPurple' with hredPurple₁ | hredPurple₂ | hredPurpleExceptional
    · exact Or.inl (Or.inr (Or.inr (Or.inl hredPurple₁)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr hredPurple₂)))
    · exact Or.inr ⟨hredBlueExceptional, hredPurpleExceptional⟩

/-- The simultaneous exceptional active-pairing pattern has no immediate repair support. -/
theorem not_hasRepair_of_isExceptional
    {p : CAP5BadPairingSupports} (h : p.IsExceptional) :
    ¬ p.HasRepair := by
  rcases h with ⟨hredBlue, hredPurple⟩
  obtain ⟨hredBlue₁, hredBlue₂⟩ :=
    not_cap5BadRedBlueRepairSupport_of_exceptionalPairing hredBlue
  obtain ⟨hredPurple₁, hredPurple₂⟩ :=
    not_cap5BadRedPurpleRepairSupport_of_exceptionalPairing hredPurple
  intro hrepair
  rcases hrepair with hrepair | hrepair | hrepair | hrepair
  · exact hredBlue₁ hrepair
  · exact hredBlue₂ hrepair
  · exact hredPurple₁ hrepair
  · exact hredPurple₂ hrepair

/-- Under the active-pairing hypotheses, failure to find an immediate finite repair is exactly
the simultaneous exceptional pairing pattern. -/
theorem isExceptional_iff_not_hasRepair_of_activePairings
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    p.IsExceptional ↔ ¬ p.HasRepair := by
  constructor
  · exact not_hasRepair_of_isExceptional
  · intro hnoRepair
    rcases repairOrExceptional_of_activePairings h with hrepair | hexceptional
    · exact False.elim (hnoRepair hrepair)
    · exact hexceptional

/-- Under active pairings, excluding the simultaneous exceptional pattern is exactly the same
as exposing at least one immediate finite repair support. -/
theorem hasRepair_iff_not_isExceptional_of_activePairings
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    p.HasRepair ↔ ¬ p.IsExceptional := by
  constructor
  · intro hrepair hexceptional
    exact not_hasRepair_of_isExceptional hexceptional hrepair
  · intro hnotExceptional
    by_cases hrepair : p.HasRepair
    · exact hrepair
    · exact False.elim (hnotExceptional
        ((isExceptional_iff_not_hasRepair_of_activePairings h).2 hrepair))

/-- If a component-support package has a repair support, then some induced boundary action repairs
the canonical bad CAP5 word and the repaired word extends across the cap. -/
theorem exists_repairingBoundaryAction_of_hasRepair
    {p : CAP5BadPairingSupports} (h : p.HasRepair) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) := by
  rcases h with h₁ | h₂ | h₃ | h₄
  · refine ⟨cap5BoundarySwap red blue p.redBlue₁, ?_, ?_⟩
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad h₁
    · exact cap5_extendsAcrossCycle_of_redBlueRepairSupport_bad h₁
  · refine ⟨cap5BoundarySwap red blue p.redBlue₂, ?_, ?_⟩
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad h₂
    · exact cap5_extendsAcrossCycle_of_redBlueRepairSupport_bad h₂
  · refine ⟨cap5BoundarySwap red purple p.redPurple₁, ?_, ?_⟩
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad h₃
    · exact cap5_extendsAcrossCycle_of_redPurpleRepairSupport_bad h₃
  · refine ⟨cap5BoundarySwap red purple p.redPurple₂, ?_, ?_⟩
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad h₄
    · exact cap5_extendsAcrossCycle_of_redPurpleRepairSupport_bad h₄

/-- Packaged outcome of the finite CAP5 move-realizability split.  The graph-level proof should
produce `RepairOrExceptional`; this theorem turns its repair side into the concrete boundary
extension endpoint and leaves the exceptional pattern explicit. -/
theorem repairOrExceptional_outcome
    {p : CAP5BadPairingSupports} (h : p.RepairOrExceptional) :
    (∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111)) ∨
    p.IsExceptional := by
  rcases h with hrepair | hexceptional
  · exact Or.inl (exists_repairingBoundaryAction_of_hasRepair hrepair)
  · exact Or.inr hexceptional

/-- Boundary-action outcome for active CAP5 pairings: graph-level component pairings immediately
yield a finite repair action unless they are exactly the simultaneous exceptional pattern. -/
theorem activePairings_outcome
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    (∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111)) ∨
    p.IsExceptional :=
  repairOrExceptional_outcome (repairOrExceptional_of_activePairings h)

/-- Final finite CAP5 move-realizability endpoint after the graph-level separator proof excludes
the simultaneous exceptional pattern.  Once active pairings are supplied, a proof that the
exceptional pattern cannot occur produces an explicit repair action whose boundary word extends
across the cap. -/
theorem exists_repairingBoundaryAction_of_activePairings_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hpair : p.HasActivePairings) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) :=
  exists_repairingBoundaryAction_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_activePairings hpair).2 hnotExceptional)

end CAP5BadPairingSupports

end Mettapedia.GraphTheory.FourColor

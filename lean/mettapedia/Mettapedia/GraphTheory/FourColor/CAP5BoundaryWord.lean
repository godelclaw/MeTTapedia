import Mettapedia.GraphTheory.FourColor.ColorAlgebra

open scoped BigOperators

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

/-- The number of CAP5 boundary edges carrying a fixed color. -/
def cap5BoundaryColorCount (w : CAP5BoundaryWord) (c : Color) : Nat :=
  (Finset.univ.filter fun i : Fin 5 => w i = c).card

/-- Every CAP5 boundary edge carries a genuine Tait color. -/
def CAP5BoundaryWordIsNonzero (w : CAP5BoundaryWord) : Prop :=
  ∀ i : Fin 5, w i ≠ 0

/-- The three nonzero Tait colors each occur an odd number of times in a CAP5 boundary word. -/
def CAP5BoundaryWordHasOddColorCounts (w : CAP5BoundaryWord) : Prop :=
  Odd (cap5BoundaryColorCount w red) ∧
  Odd (cap5BoundaryColorCount w blue) ∧
  Odd (cap5BoundaryColorCount w purple)

private def cap5ColorIndicator (c d : Color) : F2 :=
  if d = c then 1 else 0

private theorem natCast_f2_eq_zero_of_even {n : Nat} (h : Even n) : (n : F2) = 0 := by
  rcases h with ⟨k, rfl⟩
  norm_num [two_mul]

private theorem odd_of_natCast_f2_eq_one {n : Nat} (h : (n : F2) = 1) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · have hzero : (n : F2) = 0 := natCast_f2_eq_zero_of_even he
    rw [hzero] at h
    norm_num at h
  · exact ho

private theorem color_eq_red_or_blue_or_purple {c : Color} (hc : c ≠ 0) :
    c = red ∨ c = blue ∨ c = purple := by
  rcases c with ⟨c₁, c₂⟩
  fin_cases c₁ <;> fin_cases c₂
  · exfalso
    exact hc rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

private theorem isTaitColorTriple_color_mem {a b d c : Color}
    (hc : c ≠ 0) (h : IsTaitColorTriple a b d) :
    c = a ∨ c = b ∨ c = d := by
  rcases h with ⟨ha0, hb0, hd0, hab, had, hbd⟩
  rcases color_eq_red_or_blue_or_purple hc with rfl | rfl | rfl <;>
    rcases color_eq_red_or_blue_or_purple ha0 with rfl | rfl | rfl <;>
    rcases color_eq_red_or_blue_or_purple hb0 with rfl | rfl | rfl <;>
    rcases color_eq_red_or_blue_or_purple hd0 with rfl | rfl | rfl <;>
    simp [red_ne_blue, red_ne_purple, blue_ne_purple] at hab had hbd ⊢

private theorem colorIndicator_sum_tait_triple {a b d c : Color}
    (hc : c ≠ 0) (h : IsTaitColorTriple a b d) :
    cap5ColorIndicator c a + cap5ColorIndicator c b + cap5ColorIndicator c d = 1 := by
  rcases h with ⟨ha0, hb0, hd0, hab, had, hbd⟩
  have htriple : IsTaitColorTriple a b d := ⟨ha0, hb0, hd0, hab, had, hbd⟩
  rcases isTaitColorTriple_color_mem hc htriple with rfl | rfl | rfl
  · simp [cap5ColorIndicator, hab.symm, had.symm]
  · simp [cap5ColorIndicator, hab, hbd.symm]
  · simp [cap5ColorIndicator, had, hbd]

private theorem cap5BoundaryColorCount_cast_eq_sum_indicator
    (w : CAP5BoundaryWord) (c : Color) :
    (cap5BoundaryColorCount w c : F2) = ∑ i : Fin 5, cap5ColorIndicator c (w i) := by
  rw [cap5BoundaryColorCount, Finset.card_filter]
  change (Nat.castAddMonoidHom F2) (∑ i : Fin 5, if w i = c then 1 else 0) =
    ∑ i : Fin 5, cap5ColorIndicator c (w i)
  rw [map_sum]
  simp [cap5ColorIndicator]

private theorem sum_fin5_expand (f : Fin 5 → F2) :
    (∑ i : Fin 5, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_one]
  abel_nf

private theorem boundary_indicator_sum_eq_one_of_extendsWith
    {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring} {c : Color}
    (hc : c ≠ 0) (h : CAP5ExtendsAcrossCycleWith w x) :
    (∑ i : Fin 5, cap5ColorIndicator c (w i)) = 1 := by
  rcases h with ⟨hv0, hv1, hv2, hv3, hv4⟩
  have h0 := colorIndicator_sum_tait_triple hc hv0
  have h1 := colorIndicator_sum_tait_triple hc hv1
  have h2 := colorIndicator_sum_tait_triple hc hv2
  have h3 := colorIndicator_sum_tait_triple hc hv3
  have h4 := colorIndicator_sum_tait_triple hc hv4
  rw [sum_fin5_expand]
  have hsum :
      (cap5ColorIndicator c (w 0) + cap5ColorIndicator c (x 4) +
          cap5ColorIndicator c (x 0)) +
        (cap5ColorIndicator c (w 1) + cap5ColorIndicator c (x 0) +
          cap5ColorIndicator c (x 1)) +
        (cap5ColorIndicator c (w 2) + cap5ColorIndicator c (x 1) +
          cap5ColorIndicator c (x 2)) +
        (cap5ColorIndicator c (w 3) + cap5ColorIndicator c (x 2) +
          cap5ColorIndicator c (x 3)) +
        (cap5ColorIndicator c (w 4) + cap5ColorIndicator c (x 3) +
          cap5ColorIndicator c (x 4)) = 1 := by
    rw [h0, h1, h2, h3, h4]
    decide
  abel_nf at hsum ⊢
  simpa [two_nsmul, zmod2_add_self] using hsum

/-- CAP5 boundary parity: in any extendable CAP5 boundary word, every nonzero color occurs
an odd number of times on the five boundary edges. -/
theorem cap5BoundaryColorCount_odd_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} {c : Color}
    (hc : c ≠ 0) (h : CAP5WordExtendsAcrossCycle w) :
    Odd (cap5BoundaryColorCount w c) := by
  rcases h with ⟨x, hx⟩
  apply odd_of_natCast_f2_eq_one
  rw [cap5BoundaryColorCount_cast_eq_sum_indicator]
  exact boundary_indicator_sum_eq_one_of_extendsWith hc hx

/-- A fixed CAP5 internal extension forces every boundary edge to carry a nonzero color. -/
theorem cap5BoundaryWordIsNonzero_of_extendsAcrossCycleWith
    {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}
    (h : CAP5ExtendsAcrossCycleWith w x) :
    CAP5BoundaryWordIsNonzero w := by
  intro i
  rcases h with ⟨hv0, hv1, hv2, hv3, hv4⟩
  fin_cases i
  · exact hv0.1
  · exact hv1.1
  · exact hv2.1
  · exact hv3.1
  · exact hv4.1

/-- CAP5 extendability forces every boundary edge to carry a nonzero color. -/
theorem cap5BoundaryWordIsNonzero_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    CAP5BoundaryWordIsNonzero w := by
  rcases h with ⟨x, hx⟩
  exact cap5BoundaryWordIsNonzero_of_extendsAcrossCycleWith hx

/-- CAP5 extendability forces the parity shape used in the manuscript extension criterion:
red, blue, and purple each occur an odd number of times. -/
theorem cap5BoundaryWordHasOddColorCounts_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    CAP5BoundaryWordHasOddColorCounts w :=
  ⟨cap5BoundaryColorCount_odd_of_extendsAcrossCycle red_ne_zero h,
    cap5BoundaryColorCount_odd_of_extendsAcrossCycle blue_ne_zero h,
    cap5BoundaryColorCount_odd_of_extendsAcrossCycle purple_ne_zero h⟩

/-- Relabel every color in a CAP5 boundary word. -/
def cap5MapBoundaryWord (σ : Color → Color) (w : CAP5BoundaryWord) : CAP5BoundaryWord :=
  fun i => σ (w i)

/-- Relabel every color in a CAP5 internal 5-cycle coloring. -/
def cap5MapInternalCycleColoring (σ : Color → Color)
    (x : CAP5InternalCycleColoring) : CAP5InternalCycleColoring :=
  fun i => σ (x i)

/-- An equivalence of color names that fixes `0` transports proper Tait triples. -/
theorem isTaitColorTriple_map_equiv_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    IsTaitColorTriple (σ a) (σ b) (σ c) := by
  rcases h with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha
    have hσ : σ a = σ 0 := by simpa [hσ0] using ha
    exact ha0 (σ.injective hσ)
  · intro hb
    have hσ : σ b = σ 0 := by simpa [hσ0] using hb
    exact hb0 (σ.injective hσ)
  · intro hc
    have hσ : σ c = σ 0 := by simpa [hσ0] using hc
    exact hc0 (σ.injective hσ)
  · intro h
    exact hab (σ.injective h)
  · intro h
    exact hac (σ.injective h)
  · intro h
    exact hbc (σ.injective h)

theorem isTaitColorTriple_red_blue_purple : IsTaitColorTriple red blue purple := by
  simp [IsTaitColorTriple]

/-- The unique color-name equivalence sending the standard Tait triple
`(red, blue, purple)` to any given Tait triple `(a,b,c)`, while fixing `0`. -/
private def colorEquivOfTaitTriple {a b c : Color}
    (h : IsTaitColorTriple a b c) : Color ≃ Color where
  toFun d := if d = 0 then 0 else if d = red then a else if d = blue then b else c
  invFun d := if d = 0 then 0 else if d = a then red else if d = b then blue else purple
  left_inv := by
    intro d
    rcases h with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
    rcases color_eq_red_or_blue_or_purple ha0 with rfl | rfl | rfl <;>
      rcases color_eq_red_or_blue_or_purple hb0 with rfl | rfl | rfl <;>
      rcases color_eq_red_or_blue_or_purple hc0 with rfl | rfl | rfl <;>
      rcases d with ⟨d₁, d₂⟩ <;>
      fin_cases d₁ <;> fin_cases d₂ <;>
      simp [red, blue, purple] at hab hac hbc
    all_goals decide
  right_inv := by
    intro d
    rcases h with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
    rcases color_eq_red_or_blue_or_purple ha0 with rfl | rfl | rfl <;>
      rcases color_eq_red_or_blue_or_purple hb0 with rfl | rfl | rfl <;>
      rcases color_eq_red_or_blue_or_purple hc0 with rfl | rfl | rfl <;>
      rcases d with ⟨d₁, d₂⟩ <;>
      fin_cases d₁ <;> fin_cases d₂ <;>
      simp [red, blue, purple] at hab hac hbc
    all_goals decide

@[simp] private theorem colorEquivOfTaitTriple_zero {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    colorEquivOfTaitTriple h 0 = 0 := by
  simp [colorEquivOfTaitTriple]

@[simp] private theorem colorEquivOfTaitTriple_red {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    colorEquivOfTaitTriple h red = a := by
  simp [colorEquivOfTaitTriple, red_ne_zero]

@[simp] private theorem colorEquivOfTaitTriple_blue {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    colorEquivOfTaitTriple h blue = b := by
  simp [colorEquivOfTaitTriple, blue_ne_zero, red_ne_blue.symm]

@[simp] private theorem colorEquivOfTaitTriple_purple {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    colorEquivOfTaitTriple h purple = c := by
  simp [colorEquivOfTaitTriple, purple_ne_zero, red_ne_purple.symm, blue_ne_purple.symm]

/-- CAP5 extension by a fixed internal coloring is invariant under zero-fixing color relabeling. -/
theorem cap5ExtendsAcrossCycleWith_map_equiv_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}
    (h : CAP5ExtendsAcrossCycleWith w x) :
    CAP5ExtendsAcrossCycleWith (cap5MapBoundaryWord σ w)
      (cap5MapInternalCycleColoring σ x) := by
  rcases h with ⟨hv0, hv1, hv2, hv3, hv4⟩
  exact ⟨isTaitColorTriple_map_equiv_of_map_zero hσ0 hv0,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 hv1,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 hv2,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 hv3,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 hv4⟩

/-- CAP5 extendability is preserved by zero-fixing color relabeling. -/
theorem cap5WordExtendsAcrossCycle_map_equiv_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (cap5MapBoundaryWord σ w) := by
  rcases h with ⟨x, hx⟩
  exact ⟨cap5MapInternalCycleColoring σ x,
    cap5ExtendsAcrossCycleWith_map_equiv_of_map_zero hσ0 hx⟩

private theorem colorEquiv_symm_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) :
    σ.symm 0 = 0 := by
  apply σ.injective
  simp [hσ0]

/-- CAP5 extendability is unchanged by any color-name equivalence fixing `0`. -/
theorem cap5WordExtendsAcrossCycle_map_equiv_iff_of_map_zero {σ : Color ≃ Color}
    (hσ0 : σ 0 = 0) {w : CAP5BoundaryWord} :
    CAP5WordExtendsAcrossCycle (cap5MapBoundaryWord σ w) ↔
      CAP5WordExtendsAcrossCycle w := by
  constructor
  · intro h
    have hsymm0 : σ.symm 0 = 0 := colorEquiv_symm_map_zero hσ0
    have h' :=
      cap5WordExtendsAcrossCycle_map_equiv_of_map_zero (σ := σ.symm) hsymm0 h
    convert h' using 1
    funext i
    simp [cap5MapBoundaryWord]
  · intro h
    exact cap5WordExtendsAcrossCycle_map_equiv_of_map_zero hσ0 h

/-- Rotate a CAP5 boundary word one step around the cyclic boundary. -/
def cap5RotateBoundaryWord (w : CAP5BoundaryWord) : CAP5BoundaryWord
  | 0 => w 1
  | 1 => w 2
  | 2 => w 3
  | 3 => w 4
  | 4 => w 0

/-- Rotate a CAP5 internal 5-cycle coloring compatibly with `cap5RotateBoundaryWord`. -/
def cap5RotateInternalCycleColoring
    (x : CAP5InternalCycleColoring) : CAP5InternalCycleColoring
  | 0 => x 1
  | 1 => x 2
  | 2 => x 3
  | 3 => x 4
  | 4 => x 0

/-- Rotate a CAP5 boundary word one step in the inverse cyclic direction. -/
def cap5UnrotateBoundaryWord (w : CAP5BoundaryWord) : CAP5BoundaryWord
  | 0 => w 4
  | 1 => w 0
  | 2 => w 1
  | 3 => w 2
  | 4 => w 3

/-- Rotate a CAP5 internal 5-cycle coloring in the inverse cyclic direction. -/
def cap5UnrotateInternalCycleColoring
    (x : CAP5InternalCycleColoring) : CAP5InternalCycleColoring
  | 0 => x 4
  | 1 => x 0
  | 2 => x 1
  | 3 => x 2
  | 4 => x 3

@[simp] theorem cap5Unrotate_rotate_boundaryWord (w : CAP5BoundaryWord) :
    cap5UnrotateBoundaryWord (cap5RotateBoundaryWord w) = w := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem cap5Rotate_unrotate_boundaryWord (w : CAP5BoundaryWord) :
    cap5RotateBoundaryWord (cap5UnrotateBoundaryWord w) = w := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem cap5Unrotate_rotate_internalCycleColoring
    (x : CAP5InternalCycleColoring) :
    cap5UnrotateInternalCycleColoring (cap5RotateInternalCycleColoring x) = x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem cap5Rotate_unrotate_internalCycleColoring
    (x : CAP5InternalCycleColoring) :
    cap5RotateInternalCycleColoring (cap5UnrotateInternalCycleColoring x) = x := by
  funext i
  fin_cases i <;> rfl

/-- CAP5 extension by a fixed internal coloring is invariant under one cyclic rotation. -/
theorem cap5ExtendsAcrossCycleWith_rotate
    {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}
    (h : CAP5ExtendsAcrossCycleWith w x) :
    CAP5ExtendsAcrossCycleWith (cap5RotateBoundaryWord w)
      (cap5RotateInternalCycleColoring x) := by
  rcases h with ⟨hv0, hv1, hv2, hv3, hv4⟩
  exact ⟨hv1, hv2, hv3, hv4, hv0⟩

/-- CAP5 extension by a fixed internal coloring is invariant under inverse cyclic rotation. -/
theorem cap5ExtendsAcrossCycleWith_unrotate
    {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}
    (h : CAP5ExtendsAcrossCycleWith w x) :
    CAP5ExtendsAcrossCycleWith (cap5UnrotateBoundaryWord w)
      (cap5UnrotateInternalCycleColoring x) := by
  rcases h with ⟨hv0, hv1, hv2, hv3, hv4⟩
  exact ⟨hv4, hv0, hv1, hv2, hv3⟩

/-- CAP5 extendability is preserved by one cyclic boundary rotation. -/
theorem cap5WordExtendsAcrossCycle_rotate {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (cap5RotateBoundaryWord w) := by
  rcases h with ⟨x, hx⟩
  exact ⟨cap5RotateInternalCycleColoring x, cap5ExtendsAcrossCycleWith_rotate hx⟩

/-- CAP5 extendability is preserved by inverse cyclic boundary rotation. -/
theorem cap5WordExtendsAcrossCycle_unrotate {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (cap5UnrotateBoundaryWord w) := by
  rcases h with ⟨x, hx⟩
  exact ⟨cap5UnrotateInternalCycleColoring x, cap5ExtendsAcrossCycleWith_unrotate hx⟩

/-- CAP5 extendability is unchanged by one cyclic boundary rotation. -/
theorem cap5WordExtendsAcrossCycle_rotate_iff {w : CAP5BoundaryWord} :
    CAP5WordExtendsAcrossCycle (cap5RotateBoundaryWord w) ↔
      CAP5WordExtendsAcrossCycle w := by
  constructor
  · intro h
    have h' := cap5WordExtendsAcrossCycle_unrotate h
    simpa using h'
  · intro h
    exact cap5WordExtendsAcrossCycle_rotate h

/-- CAP5 extendability is unchanged by inverse cyclic boundary rotation. -/
theorem cap5WordExtendsAcrossCycle_unrotate_iff {w : CAP5BoundaryWord} :
    CAP5WordExtendsAcrossCycle (cap5UnrotateBoundaryWord w) ↔
      CAP5WordExtendsAcrossCycle w := by
  constructor
  · intro h
    have h' := cap5WordExtendsAcrossCycle_rotate h
    simpa using h'
  · intro h
    exact cap5WordExtendsAcrossCycle_unrotate h

/-- Rotate a CAP5 boundary word forward `n` cyclic steps. -/
def cap5RotateBoundaryWordN : Nat → CAP5BoundaryWord → CAP5BoundaryWord
  | 0, w => w
  | n + 1, w => cap5RotateBoundaryWord (cap5RotateBoundaryWordN n w)

/-- CAP5 extendability is preserved by any finite forward cyclic rotation. -/
theorem cap5WordExtendsAcrossCycle_rotateN {n : Nat} {w : CAP5BoundaryWord}
    (h : CAP5WordExtendsAcrossCycle w) :
    CAP5WordExtendsAcrossCycle (cap5RotateBoundaryWordN n w) := by
  induction n with
  | zero =>
      simpa [cap5RotateBoundaryWordN] using h
  | succ n ih =>
      simpa [cap5RotateBoundaryWordN] using cap5WordExtendsAcrossCycle_rotate ih

/-- CAP5 extendability is unchanged by any finite forward cyclic rotation. -/
theorem cap5WordExtendsAcrossCycle_rotateN_iff (n : Nat) {w : CAP5BoundaryWord} :
    CAP5WordExtendsAcrossCycle (cap5RotateBoundaryWordN n w) ↔
      CAP5WordExtendsAcrossCycle w := by
  induction n with
  | zero =>
      simp [cap5RotateBoundaryWordN]
  | succ n ih =>
      exact (cap5WordExtendsAcrossCycle_rotate_iff (w := cap5RotateBoundaryWordN n w)).trans ih

/-- CAP5 extendability is unchanged by zero-fixing color relabeling followed by cyclic rotation. -/
theorem cap5WordExtendsAcrossCycle_rotateN_map_equiv_iff_of_map_zero
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) (n : Nat) {w : CAP5BoundaryWord} :
    CAP5WordExtendsAcrossCycle (cap5RotateBoundaryWordN n (cap5MapBoundaryWord σ w)) ↔
      CAP5WordExtendsAcrossCycle w :=
  (cap5WordExtendsAcrossCycle_rotateN_iff n (w := cap5MapBoundaryWord σ w)).trans
    (cap5WordExtendsAcrossCycle_map_equiv_iff_of_map_zero hσ0)

/-- Parameterized normal-form good CAP5 word with block structure `(3,1,1)`. -/
def cap5BoundaryWord311Of (a b c : Color) : CAP5BoundaryWord
  | 0 => a
  | 1 => a
  | 2 => a
  | 3 => b
  | 4 => c

/-- The internal 5-cycle coloring that extends `cap5BoundaryWord311Of a b c` when
`a,b,c` are the three distinct nonzero Tait colors. -/
def cap5InternalCycleColoring311Of (a b c : Color) : CAP5InternalCycleColoring
  | 0 => c
  | 1 => b
  | 2 => c
  | 3 => a
  | 4 => b

/-- Every parameterized `(3,1,1)` CAP5 boundary word extends across the cap. -/
theorem cap5BoundaryWord311Of_extendsAcrossCycle {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    CAP5WordExtendsAcrossCycle (cap5BoundaryWord311Of a b c) := by
  refine ⟨cap5InternalCycleColoring311Of a b c, ?_⟩
  rcases h with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
  simp [CAP5ExtendsAcrossCycleWith, IsTaitColorTriple, cap5BoundaryWord311Of,
    cap5InternalCycleColoring311Of, ha0, hb0, hc0, hab, hac, hbc, hab.symm,
    hac.symm, hbc.symm]

/-- Parameterized normal-form bad CAP5 word with block structure `(2,1,1,1)`. -/
def cap5BoundaryWord2111Of (a b c : Color) : CAP5BoundaryWord
  | 0 => a
  | 1 => a
  | 2 => b
  | 3 => a
  | 4 => c

/-- No parameterized `(2,1,1,1)` CAP5 boundary word extends across the cap. -/
theorem not_cap5BoundaryWord2111Of_extendsAcrossCycle {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWord2111Of a b c) := by
  intro hextends
  rcases hextends with ⟨x, hx⟩
  rcases h with ⟨ha0, hb0, hc0, hab, hac, hbc⟩
  have htriple : IsTaitColorTriple a b c := ⟨ha0, hb0, hc0, hab, hac, hbc⟩
  rcases hx with ⟨_hv0, hv1, hv2, hv3, _hv4⟩
  rcases hv1 with ⟨_hw1, _hx0, hx1, _hw1_x0, hw1_x1, _hx0_x1⟩
  rcases hv2 with ⟨_hw2, _hx1', hx2, hw2_x1, hw2_x2, hx1_x2⟩
  rcases hv3 with ⟨_hw3, _hx2', _hx3, hw3_x2, _hw3_x3, _hx2_x3⟩
  have hx1_eq_c : x 1 = c := by
    have hx1_ne_a : x 1 ≠ a := by
      intro hx1a
      exact hw1_x1 (by simp [cap5BoundaryWord2111Of, hx1a])
    have hx1_ne_b : x 1 ≠ b := by
      intro hx1b
      exact hw2_x1 (by simp [cap5BoundaryWord2111Of, hx1b])
    rcases isTaitColorTriple_color_mem hx1 htriple with hx1a | hx1b | hx1c
    · exact False.elim (hx1_ne_a hx1a)
    · exact False.elim (hx1_ne_b hx1b)
    · exact hx1c
  have hx2_eq_c : x 2 = c := by
    have hx2_ne_b : x 2 ≠ b := by
      intro hx2b
      exact hw2_x2 (by simp [cap5BoundaryWord2111Of, hx2b])
    have hx2_ne_a : x 2 ≠ a := by
      intro hx2a
      exact hw3_x2 (by simp [cap5BoundaryWord2111Of, hx2a])
    rcases isTaitColorTriple_color_mem hx2 htriple with hx2a | hx2b | hx2c
    · exact False.elim (hx2_ne_a hx2a)
    · exact False.elim (hx2_ne_b hx2b)
    · exact hx2c
  exact hx1_x2 (hx1_eq_c.trans hx2_eq_c.symm)

/-- CAP5 block structure `(3,1,1)` with explicit color names. -/
def CAP5BoundaryWordHasColoredBlock311 (w : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    ∃ n : Nat, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c)

/-- CAP5 block structure `(2,1,1,1)` with explicit color names. -/
def CAP5BoundaryWordHasColoredBlock2111 (w : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    ∃ n : Nat, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c)

/-- Any CAP5 boundary word with colored block structure `(3,1,1)` extends across the cap. -/
theorem cap5_extendsAcrossCycle_of_coloredBlock311
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock311 w) :
    CAP5WordExtendsAcrossCycle w := by
  rcases h with ⟨a, b, c, htriple, n, rfl⟩
  exact cap5WordExtendsAcrossCycle_rotateN
    (cap5BoundaryWord311Of_extendsAcrossCycle htriple)

/-- Any CAP5 boundary word with colored block structure `(2,1,1,1)` does not extend
across the cap. -/
theorem not_cap5_extendsAcrossCycle_of_coloredBlock2111
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock2111 w) :
    ¬ CAP5WordExtendsAcrossCycle w := by
  rcases h with ⟨a, b, c, htriple, n, rfl⟩
  intro hextends
  exact not_cap5BoundaryWord2111Of_extendsAcrossCycle htriple
    ((cap5WordExtendsAcrossCycle_rotateN_iff n).mp hextends)

/-- Normal-form good CAP5 word with block structure `(3,1,1)`. -/
def cap5GoodBoundaryWord311 : CAP5BoundaryWord
  | 0 => red
  | 1 => red
  | 2 => red
  | 3 => blue
  | 4 => purple

theorem cap5MapBoundaryWord_goodBoundaryWord311 (σ : Color → Color) :
    cap5MapBoundaryWord σ cap5GoodBoundaryWord311 =
      cap5BoundaryWord311Of (σ red) (σ blue) (σ purple) := by
  funext i
  fin_cases i <;> rfl

theorem cap5MapBoundaryWord_goodBoundaryWord311_of_taitTriple {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    cap5MapBoundaryWord (colorEquivOfTaitTriple h) cap5GoodBoundaryWord311 =
      cap5BoundaryWord311Of a b c := by
  rw [cap5MapBoundaryWord_goodBoundaryWord311]
  simp

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

/-- The canonical good CAP5 boundary word transported by color relabeling and cyclic rotation. -/
def cap5TransportedGoodBoundaryWord (σ : Color → Color) (n : Nat) : CAP5BoundaryWord :=
  cap5RotateBoundaryWordN n (cap5MapBoundaryWord σ cap5GoodBoundaryWord311)

/-- Every zero-fixing color relabeling and cyclic rotation of the canonical good word
extends across the CAP5 cap. -/
theorem cap5TransportedGoodBoundaryWord_extendsAcrossCycle
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) (n : Nat) :
    CAP5WordExtendsAcrossCycle (cap5TransportedGoodBoundaryWord σ n) := by
  unfold cap5TransportedGoodBoundaryWord
  exact cap5WordExtendsAcrossCycle_rotateN
    (cap5WordExtendsAcrossCycle_map_equiv_of_map_zero hσ0
      cap5GoodBoundaryWord311_extendsAcrossCycle)

/-- CAP5 block structure `(3,1,1)`, represented as the orbit of the canonical good word
under cyclic rotation and zero-fixing color relabeling. -/
def CAP5BoundaryWordHasBlock311 (w : CAP5BoundaryWord) : Prop :=
  ∃ (σ : Color ≃ Color) (n : Nat),
    σ 0 = 0 ∧ w = cap5TransportedGoodBoundaryWord σ n

theorem cap5BoundaryWordHasColoredBlock311_of_block311
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasBlock311 w) :
    CAP5BoundaryWordHasColoredBlock311 w := by
  rcases h with ⟨σ, n, hσ0, hw⟩
  refine ⟨σ red, σ blue, σ purple,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 isTaitColorTriple_red_blue_purple,
    n, ?_⟩
  rw [hw]
  unfold cap5TransportedGoodBoundaryWord
  rw [cap5MapBoundaryWord_goodBoundaryWord311]

theorem cap5BoundaryWordHasBlock311_of_coloredBlock311
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock311 w) :
    CAP5BoundaryWordHasBlock311 w := by
  rcases h with ⟨a, b, c, htriple, n, hw⟩
  refine ⟨colorEquivOfTaitTriple htriple, n, colorEquivOfTaitTriple_zero htriple, ?_⟩
  rw [hw]
  unfold cap5TransportedGoodBoundaryWord
  rw [cap5MapBoundaryWord_goodBoundaryWord311_of_taitTriple htriple]

theorem cap5BoundaryWordHasColoredBlock311_iff_block311
    {w : CAP5BoundaryWord} :
    CAP5BoundaryWordHasColoredBlock311 w ↔ CAP5BoundaryWordHasBlock311 w :=
  ⟨cap5BoundaryWordHasBlock311_of_coloredBlock311,
    cap5BoundaryWordHasColoredBlock311_of_block311⟩

/-- Any CAP5 boundary word with normalized block structure `(3,1,1)` extends across the cap. -/
theorem cap5_extendsAcrossCycle_of_block311
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasBlock311 w) :
    CAP5WordExtendsAcrossCycle w := by
  rcases h with ⟨σ, n, hσ0, rfl⟩
  exact cap5TransportedGoodBoundaryWord_extendsAcrossCycle hσ0 n

/-- Normal-form bad CAP5 word with block structure `(2,1,1,1)`. -/
def cap5BadBoundaryWord2111 : CAP5BoundaryWord
  | 0 => red
  | 1 => red
  | 2 => blue
  | 3 => red
  | 4 => purple

theorem cap5MapBoundaryWord_badBoundaryWord2111 (σ : Color → Color) :
    cap5MapBoundaryWord σ cap5BadBoundaryWord2111 =
      cap5BoundaryWord2111Of (σ red) (σ blue) (σ purple) := by
  funext i
  fin_cases i <;> rfl

theorem cap5MapBoundaryWord_badBoundaryWord2111_of_taitTriple {a b c : Color}
    (h : IsTaitColorTriple a b c) :
    cap5MapBoundaryWord (colorEquivOfTaitTriple h) cap5BadBoundaryWord2111 =
      cap5BoundaryWord2111Of a b c := by
  rw [cap5MapBoundaryWord_badBoundaryWord2111]
  simp

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

/-- Every rotated, zero-fixing color relabeling of the canonical bad CAP5 word is still bad. -/
theorem not_cap5BadBoundaryWord2111_rotateN_map_equiv_extendsAcrossCycle
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) (n : Nat) :
    ¬ CAP5WordExtendsAcrossCycle
      (cap5RotateBoundaryWordN n (cap5MapBoundaryWord σ cap5BadBoundaryWord2111)) := by
  intro h
  exact not_cap5BadBoundaryWord2111_extendsAcrossCycle
    ((cap5WordExtendsAcrossCycle_rotateN_map_equiv_iff_of_map_zero hσ0 n).mp h)

/-- The canonical bad CAP5 boundary word transported by color relabeling and cyclic rotation. -/
def cap5TransportedBadBoundaryWord (σ : Color → Color) (n : Nat) : CAP5BoundaryWord :=
  cap5RotateBoundaryWordN n (cap5MapBoundaryWord σ cap5BadBoundaryWord2111)

/-- Every zero-fixing color relabeling and cyclic rotation of the canonical bad word is still bad. -/
theorem not_cap5TransportedBadBoundaryWord_extendsAcrossCycle
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) (n : Nat) :
    ¬ CAP5WordExtendsAcrossCycle (cap5TransportedBadBoundaryWord σ n) :=
  not_cap5BadBoundaryWord2111_rotateN_map_equiv_extendsAcrossCycle hσ0 n

/-- CAP5 block structure `(2,1,1,1)`, represented as the orbit of the canonical bad word
under cyclic rotation and zero-fixing color relabeling. -/
def CAP5BoundaryWordHasBlock2111 (w : CAP5BoundaryWord) : Prop :=
  ∃ (σ : Color ≃ Color) (n : Nat),
    σ 0 = 0 ∧ w = cap5TransportedBadBoundaryWord σ n

theorem cap5BoundaryWordHasColoredBlock2111_of_block2111
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasBlock2111 w) :
    CAP5BoundaryWordHasColoredBlock2111 w := by
  rcases h with ⟨σ, n, hσ0, hw⟩
  refine ⟨σ red, σ blue, σ purple,
    isTaitColorTriple_map_equiv_of_map_zero hσ0 isTaitColorTriple_red_blue_purple,
    n, ?_⟩
  rw [hw]
  unfold cap5TransportedBadBoundaryWord
  rw [cap5MapBoundaryWord_badBoundaryWord2111]

theorem cap5BoundaryWordHasBlock2111_of_coloredBlock2111
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock2111 w) :
    CAP5BoundaryWordHasBlock2111 w := by
  rcases h with ⟨a, b, c, htriple, n, hw⟩
  refine ⟨colorEquivOfTaitTriple htriple, n, colorEquivOfTaitTriple_zero htriple, ?_⟩
  rw [hw]
  unfold cap5TransportedBadBoundaryWord
  rw [cap5MapBoundaryWord_badBoundaryWord2111_of_taitTriple htriple]

theorem cap5BoundaryWordHasColoredBlock2111_iff_block2111
    {w : CAP5BoundaryWord} :
    CAP5BoundaryWordHasColoredBlock2111 w ↔ CAP5BoundaryWordHasBlock2111 w :=
  ⟨cap5BoundaryWordHasBlock2111_of_coloredBlock2111,
    cap5BoundaryWordHasColoredBlock2111_of_block2111⟩

/-- Bounded CAP5 block structure `(3,1,1)`: the rotation witness is reduced to
`Fin 5`. This finite variant is only used to prove the exhaustive CAP5 boundary
classifier. -/
private def CAP5BoundaryWordHasColoredBlock311Bounded (w : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c)

/-- Bounded CAP5 block structure `(2,1,1,1)`: the rotation witness is reduced to
`Fin 5`. This finite variant is only used to prove the exhaustive CAP5 boundary
classifier. -/
private def CAP5BoundaryWordHasColoredBlock2111Bounded (w : CAP5BoundaryWord) : Prop :=
  ∃ a b c : Color, IsTaitColorTriple a b c ∧
    ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c)

private def decidableIsTaitColorTriple (a b c : Color) :
    Decidable (IsTaitColorTriple a b c) := by
  unfold IsTaitColorTriple
  infer_instance

private def decidableCAP5BoundaryWordIsNonzero (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordIsNonzero w) := by
  unfold CAP5BoundaryWordIsNonzero
  exact @Fintype.decidableForallFintype (Fin 5) (fun i => w i ≠ 0)
    (fun _ => inferInstance) inferInstance

private def decidableCAP5BoundaryWordHasOddColorCounts (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasOddColorCounts w) := by
  unfold CAP5BoundaryWordHasOddColorCounts
  infer_instance

private def decidableCAP5BoundaryWordHasColoredBlock311Rotation
    (w : CAP5BoundaryWord) (a b c : Color) :
    Decidable (∃ n : Fin 5,
      w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c)) :=
  @Fintype.decidableExistsFintype (Fin 5)
    (fun n => w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c))
    (fun _ => inferInstance) inferInstance

private def decidableCAP5BoundaryWordHasColoredBlock2111Rotation
    (w : CAP5BoundaryWord) (a b c : Color) :
    Decidable (∃ n : Fin 5,
      w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c)) :=
  @Fintype.decidableExistsFintype (Fin 5)
    (fun n => w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c))
    (fun _ => inferInstance) inferInstance

private def decidableCAP5BoundaryWordHasColoredBlock311Core
    (w : CAP5BoundaryWord) (a b c : Color) :
    Decidable (IsTaitColorTriple a b c ∧
      ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c)) := by
  letI : Decidable (IsTaitColorTriple a b c) := decidableIsTaitColorTriple a b c
  letI : Decidable (∃ n : Fin 5,
      w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c)) :=
    decidableCAP5BoundaryWordHasColoredBlock311Rotation w a b c
  infer_instance

private def decidableCAP5BoundaryWordHasColoredBlock2111Core
    (w : CAP5BoundaryWord) (a b c : Color) :
    Decidable (IsTaitColorTriple a b c ∧
      ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c)) := by
  letI : Decidable (IsTaitColorTriple a b c) := decidableIsTaitColorTriple a b c
  letI : Decidable (∃ n : Fin 5,
      w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c)) :=
    decidableCAP5BoundaryWordHasColoredBlock2111Rotation w a b c
  infer_instance

private def decidableCAP5BoundaryWordHasColoredBlock311Bounded
    (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasColoredBlock311Bounded w) :=
  @Fintype.decidableExistsFintype Color
    (fun a => ∃ b c : Color, IsTaitColorTriple a b c ∧
      ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c))
    (fun a => @Fintype.decidableExistsFintype Color
      (fun b => ∃ c : Color, IsTaitColorTriple a b c ∧
        ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c))
      (fun b => @Fintype.decidableExistsFintype Color
        (fun c => IsTaitColorTriple a b c ∧
          ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord311Of a b c))
        (fun c => decidableCAP5BoundaryWordHasColoredBlock311Core w a b c)
        inferInstance)
      inferInstance)
    inferInstance

private def decidableCAP5BoundaryWordHasColoredBlock2111Bounded
    (w : CAP5BoundaryWord) :
    Decidable (CAP5BoundaryWordHasColoredBlock2111Bounded w) :=
  @Fintype.decidableExistsFintype Color
    (fun a => ∃ b c : Color, IsTaitColorTriple a b c ∧
      ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c))
    (fun a => @Fintype.decidableExistsFintype Color
      (fun b => ∃ c : Color, IsTaitColorTriple a b c ∧
        ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c))
      (fun b => @Fintype.decidableExistsFintype Color
        (fun c => IsTaitColorTriple a b c ∧
          ∃ n : Fin 5, w = cap5RotateBoundaryWordN n (cap5BoundaryWord2111Of a b c))
        (fun c => decidableCAP5BoundaryWordHasColoredBlock2111Core w a b c)
        inferInstance)
      inferInstance)
    inferInstance

private theorem cap5BoundaryWordHasColoredBlock311_of_bounded
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock311Bounded w) :
    CAP5BoundaryWordHasColoredBlock311 w := by
  rcases h with ⟨a, b, c, htriple, n, hw⟩
  exact ⟨a, b, c, htriple, n, hw⟩

private theorem cap5BoundaryWordHasColoredBlock2111_of_bounded
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasColoredBlock2111Bounded w) :
    CAP5BoundaryWordHasColoredBlock2111 w := by
  rcases h with ⟨a, b, c, htriple, n, hw⟩
  exact ⟨a, b, c, htriple, n, hw⟩

set_option maxRecDepth 10000 in
private theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_bounded_of_nonzero_of_odd :
    ∀ w : CAP5BoundaryWord,
      CAP5BoundaryWordIsNonzero w →
      CAP5BoundaryWordHasOddColorCounts w →
      CAP5BoundaryWordHasColoredBlock311Bounded w ∨
        CAP5BoundaryWordHasColoredBlock2111Bounded w := by
  letI : DecidablePred CAP5BoundaryWordIsNonzero := decidableCAP5BoundaryWordIsNonzero
  letI : DecidablePred CAP5BoundaryWordHasOddColorCounts :=
    decidableCAP5BoundaryWordHasOddColorCounts
  letI : DecidablePred CAP5BoundaryWordHasColoredBlock311Bounded :=
    decidableCAP5BoundaryWordHasColoredBlock311Bounded
  letI : DecidablePred CAP5BoundaryWordHasColoredBlock2111Bounded :=
    decidableCAP5BoundaryWordHasColoredBlock2111Bounded
  decide

/-- Exhaustive CAP5 parity-shape classifier: every nonzero boundary word whose three Tait
colors occur with odd parity is either a colored `(3,1,1)` block or a colored `(2,1,1,1)`
block, up to cyclic rotation. -/
theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w) :
    CAP5BoundaryWordHasColoredBlock311 w ∨ CAP5BoundaryWordHasColoredBlock2111 w := by
  rcases cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_bounded_of_nonzero_of_odd
      w hnz hodd with h311 | h2111
  · exact Or.inl (cap5BoundaryWordHasColoredBlock311_of_bounded h311)
  · exact Or.inr (cap5BoundaryWordHasColoredBlock2111_of_bounded h2111)

/-- Any CAP5 boundary word with normalized block structure `(2,1,1,1)` does not extend
across the cap. -/
theorem not_cap5_extendsAcrossCycle_of_block2111
    {w : CAP5BoundaryWord} (h : CAP5BoundaryWordHasBlock2111 w) :
    ¬ CAP5WordExtendsAcrossCycle w := by
  rcases h with ⟨σ, n, hσ0, rfl⟩
  exact not_cap5TransportedBadBoundaryWord_extendsAcrossCycle hσ0 n

/-- An extendable CAP5 boundary word cannot have normalized block structure `(2,1,1,1)`. -/
theorem not_cap5BoundaryWordHasBlock2111_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    ¬ CAP5BoundaryWordHasBlock2111 w := by
  intro hblock
  exact not_cap5_extendsAcrossCycle_of_block2111 hblock h

/-- Once a CAP5 boundary word has been classified into one of the two parity-allowed block
orbits, extendability is exactly the `(3,1,1)` case. -/
theorem cap5_extendsAcrossCycle_iff_block311_of_block311_or_block2111
    {w : CAP5BoundaryWord}
    (hclass : CAP5BoundaryWordHasBlock311 w ∨ CAP5BoundaryWordHasBlock2111 w) :
    CAP5WordExtendsAcrossCycle w ↔ CAP5BoundaryWordHasBlock311 w := by
  constructor
  · intro hextends
    rcases hclass with h311 | h2111
    · exact h311
    · exact False.elim (not_cap5_extendsAcrossCycle_of_block2111 h2111 hextends)
  · exact cap5_extendsAcrossCycle_of_block311

/-- Once a CAP5 boundary word has been classified into one of the two parity-allowed block
orbits, nonextendability is exactly the `(2,1,1,1)` case. -/
theorem not_cap5_extendsAcrossCycle_iff_block2111_of_block311_or_block2111
    {w : CAP5BoundaryWord}
    (hclass : CAP5BoundaryWordHasBlock311 w ∨ CAP5BoundaryWordHasBlock2111 w) :
    ¬ CAP5WordExtendsAcrossCycle w ↔ CAP5BoundaryWordHasBlock2111 w := by
  constructor
  · intro hnotExtends
    rcases hclass with h311 | h2111
    · exact False.elim (hnotExtends (cap5_extendsAcrossCycle_of_block311 h311))
    · exact h2111
  · exact not_cap5_extendsAcrossCycle_of_block2111

/-- CAP5 extension criterion from the finite parity shape alone: under the nonzero
odd-count hypotheses forced by any extendable boundary word, extendability is exactly the
colored `(3,1,1)` block case. -/
theorem cap5_extendsAcrossCycle_iff_coloredBlock311_of_nonzero_of_odd
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w) :
    CAP5WordExtendsAcrossCycle w ↔ CAP5BoundaryWordHasColoredBlock311 w := by
  have hclassColored :=
    cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd hnz hodd
  have hclassBlock : CAP5BoundaryWordHasBlock311 w ∨ CAP5BoundaryWordHasBlock2111 w := by
    rcases hclassColored with h311 | h2111
    · exact Or.inl (cap5BoundaryWordHasBlock311_of_coloredBlock311 h311)
    · exact Or.inr (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 h2111)
  exact (cap5_extendsAcrossCycle_iff_block311_of_block311_or_block2111 hclassBlock).trans
    cap5BoundaryWordHasColoredBlock311_iff_block311.symm

/-- Dual CAP5 extension criterion from the finite parity shape alone: under the nonzero
odd-count hypotheses, nonextendability is exactly the colored `(2,1,1,1)` block case. -/
theorem not_cap5_extendsAcrossCycle_iff_coloredBlock2111_of_nonzero_of_odd
    {w : CAP5BoundaryWord}
    (hnz : CAP5BoundaryWordIsNonzero w)
    (hodd : CAP5BoundaryWordHasOddColorCounts w) :
    ¬ CAP5WordExtendsAcrossCycle w ↔ CAP5BoundaryWordHasColoredBlock2111 w := by
  have hclassColored :=
    cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd hnz hodd
  have hclassBlock : CAP5BoundaryWordHasBlock311 w ∨ CAP5BoundaryWordHasBlock2111 w := by
    rcases hclassColored with h311 | h2111
    · exact Or.inl (cap5BoundaryWordHasBlock311_of_coloredBlock311 h311)
    · exact Or.inr (cap5BoundaryWordHasBlock2111_of_coloredBlock2111 h2111)
  exact (not_cap5_extendsAcrossCycle_iff_block2111_of_block311_or_block2111 hclassBlock).trans
    cap5BoundaryWordHasColoredBlock2111_iff_block2111.symm

/-- Manuscript-facing CAP5 extension consequence: every extendable CAP5 boundary word has
the good colored `(3,1,1)` block structure. -/
theorem cap5BoundaryWordHasColoredBlock311_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    CAP5BoundaryWordHasColoredBlock311 w := by
  exact (cap5_extendsAcrossCycle_iff_coloredBlock311_of_nonzero_of_odd
    (cap5BoundaryWordIsNonzero_of_extendsAcrossCycle h)
    (cap5BoundaryWordHasOddColorCounts_of_extendsAcrossCycle h)).mp h

/-- Manuscript-facing CAP5 obstruction consequence: an extendable CAP5 boundary word cannot
have the bad colored `(2,1,1,1)` block structure. -/
theorem not_cap5BoundaryWordHasColoredBlock2111_of_extendsAcrossCycle
    {w : CAP5BoundaryWord} (h : CAP5WordExtendsAcrossCycle w) :
    ¬ CAP5BoundaryWordHasColoredBlock2111 w := by
  intro hbad
  exact not_cap5_extendsAcrossCycle_of_coloredBlock2111 hbad h

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

/-- Apply a canonical CAP5 repair type, then transport the repaired word by color relabeling and
cyclic rotation.  This is the finite repair-basis counterpart of the manuscript's
"up to cyclic rotation and permutation of color names" normalization. -/
def transportedApply (τ : CAP5RepairType) (σ : Color → Color) (n : Nat) :
    CAP5BoundaryWord :=
  cap5RotateBoundaryWordN n (cap5MapBoundaryWord σ (τ.apply cap5BadBoundaryWord2111))

/-- Every transported canonical CAP5 repair type yields an extendable boundary word. -/
theorem transportedApply_extendsAcrossCycle (τ : CAP5RepairType)
    {σ : Color ≃ Color} (hσ0 : σ 0 = 0) (n : Nat) :
    CAP5WordExtendsAcrossCycle (τ.transportedApply σ n) := by
  unfold transportedApply
  exact cap5WordExtendsAcrossCycle_rotateN
    (cap5WordExtendsAcrossCycle_map_equiv_of_map_zero hσ0 τ.apply_bad_extendsAcrossCycle)

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

/-- A boundary action induces a transported canonical finite repair type at a transported
normal-form bad CAP5 word.  This is the graph-facing target for outside-only Kempe switches
after normalizing by color relabeling and cyclic rotation. -/
def CAP5BoundaryActionInducesTransportedRepairType
    (action : CAP5BoundaryAction) (τ : CAP5RepairType) (σ : Color → Color) (n : Nat) : Prop :=
  action (cap5TransportedBadBoundaryWord σ n) = τ.transportedApply σ n

/-- A boundary action realizes some transported canonical finite repair type at a transported
normal-form bad CAP5 word. -/
def CAP5BoundaryActionRealizesSomeTransportedRepairType
    (action : CAP5BoundaryAction) (σ : Color → Color) (n : Nat) : Prop :=
  ∃ τ : CAP5RepairType, CAP5BoundaryActionInducesTransportedRepairType action τ σ n

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

/-- If a boundary action induces a transported finite repair type on a transported canonical bad
word, then the action's output extends across the CAP5 cap. -/
theorem cap5_extendsAcrossCycle_of_boundaryActionInducesTransportedRepairType_bad
    {action : CAP5BoundaryAction} {τ : CAP5RepairType} {σ : Color ≃ Color} {n : Nat}
    (hσ0 : σ 0 = 0)
    (h : CAP5BoundaryActionInducesTransportedRepairType action τ σ n) :
    CAP5WordExtendsAcrossCycle (action (cap5TransportedBadBoundaryWord σ n)) := by
  rw [h]
  exact τ.transportedApply_extendsAcrossCycle hσ0 n

/-- If a boundary action realizes some transported finite repair type on a transported canonical
bad word, then the action's output extends across the CAP5 cap. -/
theorem cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeTransportedRepairType_bad
    {action : CAP5BoundaryAction} {σ : Color ≃ Color} {n : Nat}
    (hσ0 : σ 0 = 0)
    (h : CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5WordExtendsAcrossCycle (action (cap5TransportedBadBoundaryWord σ n)) := by
  rcases h with ⟨τ, hτ⟩
  exact cap5_extendsAcrossCycle_of_boundaryActionInducesTransportedRepairType_bad hσ0 hτ

/-- A CAP5 boundary action genuinely repairs a boundary word when the input word does not extend
across the cap but the action's output word does. -/
def CAP5BoundaryActionRepairsWord (action : CAP5BoundaryAction) (w : CAP5BoundaryWord) : Prop :=
  ¬ CAP5WordExtendsAcrossCycle w ∧ CAP5WordExtendsAcrossCycle (action w)

/-- A canonical finite-repair action is a genuine repair of the canonical bad CAP5 word. -/
theorem cap5_boundaryActionRepairsWord_of_boundaryActionRealizesSomeRepairType_bad
    {action : CAP5BoundaryAction}
    (h : CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111) :
    CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 :=
  ⟨not_cap5BadBoundaryWord2111_extendsAcrossCycle,
    cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeRepairType_bad h⟩

/-- A transported finite-repair action is a genuine repair of the transported canonical bad
CAP5 word. -/
theorem cap5_boundaryActionRepairsWord_of_boundaryActionRealizesSomeTransportedRepairType_bad
    {action : CAP5BoundaryAction} {σ : Color ≃ Color} {n : Nat}
    (hσ0 : σ 0 = 0)
    (h : CAP5BoundaryActionRealizesSomeTransportedRepairType action σ n) :
    CAP5BoundaryActionRepairsWord action (cap5TransportedBadBoundaryWord σ n) :=
  ⟨not_cap5TransportedBadBoundaryWord_extendsAcrossCycle hσ0 n,
    cap5_extendsAcrossCycle_of_boundaryActionRealizesSomeTransportedRepairType_bad hσ0 h⟩

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

/-- Graph-facing red/blue component cover condition for the normalized CAP5 bad word:
two disjoint two-point supports cover exactly the active red/blue boundary positions
`{0,1,2,3}`. -/
def CAP5BadRedBlueComponentCover (S₁ S₂ : Finset (Fin 5)) : Prop :=
  S₁.card = 2 ∧ S₂.card = 2 ∧ Disjoint S₁ S₂ ∧
    S₁ ∪ S₂ = ({0, 1, 2, 3} : Finset (Fin 5))

/-- Graph-facing red/purple component cover condition for the normalized CAP5 bad word:
two disjoint two-point supports cover exactly the active red/purple boundary positions
`{0,1,3,4}`. -/
def CAP5BadRedPurpleComponentCover (S₁ S₂ : Finset (Fin 5)) : Prop :=
  S₁.card = 2 ∧ S₂.card = 2 ∧ Disjoint S₁ S₂ ∧
    S₁ ∪ S₂ = ({0, 1, 3, 4} : Finset (Fin 5))

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

private theorem cap5_subset_left_of_union_eq {S₁ S₂ A : Finset (Fin 5)}
    (hunion : S₁ ∪ S₂ = A) : S₁ ⊆ A := by
  intro i hi
  simpa [hunion] using (Finset.mem_union_left S₂ hi)

private theorem cap5_complement_of_disjoint_union_eq {S₁ S₂ A : Finset (Fin 5)}
    (hdisj : Disjoint S₁ S₂) (hunion : S₁ ∪ S₂ = A) :
    S₂ = A \ S₁ := by
  ext i
  have hmem := congrArg (fun T : Finset (Fin 5) => i ∈ T) hunion
  constructor
  · intro hi
    have hnot : i ∉ S₁ := by
      intro hi₁
      exact (Finset.disjoint_left.mp hdisj) hi₁ hi
    simp [← hmem, hi, hnot]
  · intro hi
    simp at hi
    rcases hi with ⟨hiA, hnotS₁⟩
    have hiUnion : i ∈ S₁ ∪ S₂ := by
      simpa [hmem] using hiA
    simp at hiUnion
    exact hiUnion.resolve_left hnotS₁

private theorem cap5RedBluePairCases_of_card_two_subset
    {S : Finset (Fin 5)}
    (hcard : S.card = 2)
    (hsubset : S ⊆ ({0, 1, 2, 3} : Finset (Fin 5))) :
    S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨
      S = {1, 2} ∨ S = {1, 3} ∨ S = ({2, 3} : Finset (Fin 5)) := by
  rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, hS⟩
  rw [hS] at hsubset ⊢
  fin_cases a <;> fin_cases b <;> simp [Finset.subset_iff] at hab hsubset ⊢
  all_goals first
    | exact Or.inl (by decide)
    | exact Or.inr (Or.inl (by decide))
    | exact Or.inr (Or.inr (Or.inl (by decide)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))

private theorem cap5RedPurplePairCases_of_card_two_subset
    {S : Finset (Fin 5)}
    (hcard : S.card = 2)
    (hsubset : S ⊆ ({0, 1, 3, 4} : Finset (Fin 5))) :
    S = {0, 1} ∨ S = {0, 3} ∨ S = {0, 4} ∨
      S = {1, 3} ∨ S = {1, 4} ∨ S = ({3, 4} : Finset (Fin 5)) := by
  rcases Finset.card_eq_two.mp hcard with ⟨a, b, hab, hS⟩
  rw [hS] at hsubset ⊢
  fin_cases a <;> fin_cases b <;> simp [Finset.subset_iff] at hab hsubset ⊢
  all_goals first
    | exact Or.inl (by decide)
    | exact Or.inr (Or.inl (by decide))
    | exact Or.inr (Or.inr (Or.inl (by decide)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))

/-- A disjoint two-component cover of the active red/blue support is one of the three
red/blue active pairings, with ordered component slots. -/
theorem cap5BadRedBlueActivePairing_of_componentCover
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedBlueComponentCover S₁ S₂) :
    CAP5BadRedBlueActivePairing S₁ S₂ := by
  rcases h with ⟨hcard₁, _hcard₂, hdisj, hunion⟩
  have hsubset : S₁ ⊆ ({0, 1, 2, 3} : Finset (Fin 5)) :=
    cap5_subset_left_of_union_eq hunion
  rcases cap5RedBluePairCases_of_card_two_subset hcard₁ hsubset with
    hS₁ | hS₁ | hS₁ | hS₁ | hS₁ | hS₁
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({2, 3} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({1, 3} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({1, 2} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 3} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 2} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 1} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedBlueActivePairing, hS₂']

/-- A disjoint two-component cover of the active red/purple support is one of the three
red/purple active pairings, with ordered component slots. -/
theorem cap5BadRedPurpleActivePairing_of_componentCover
    {S₁ S₂ : Finset (Fin 5)}
    (h : CAP5BadRedPurpleComponentCover S₁ S₂) :
    CAP5BadRedPurpleActivePairing S₁ S₂ := by
  rcases h with ⟨hcard₁, _hcard₂, hdisj, hunion⟩
  have hsubset : S₁ ⊆ ({0, 1, 3, 4} : Finset (Fin 5)) :=
    cap5_subset_left_of_union_eq hunion
  rcases cap5RedPurplePairCases_of_card_two_subset hcard₁ hsubset with
    hS₁ | hS₁ | hS₁ | hS₁ | hS₁ | hS₁
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({3, 4} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({1, 4} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({1, 3} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 4} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 3} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']
  · rw [hS₁] at hdisj hunion ⊢
    have hS₂ := cap5_complement_of_disjoint_union_eq hdisj hunion
    have hS₂' : S₂ = ({0, 1} : Finset (Fin 5)) := by
      rw [hS₂]
      ext i
      fin_cases i <;> simp
    simp [CAP5BadRedPurpleActivePairing, hS₂']

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

/-- A boundary action is one of the four swaps carried by the component-support package.  This
is the local finite target for an outside-only Kempe component: graph-level data should identify
which support its boundary action uses. -/
def BoundaryActionUsesSupport (p : CAP5BadPairingSupports)
    (action : CAP5BoundaryAction) : Prop :=
  action = cap5BoundarySwap red blue p.redBlue₁ ∨
  action = cap5BoundarySwap red blue p.redBlue₂ ∨
  action = cap5BoundarySwap red purple p.redPurple₁ ∨
  action = cap5BoundarySwap red purple p.redPurple₂

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

/-- Graph-facing cover hypotheses for the two active color pairs in the normalized CAP5 bad word. -/
def HasComponentCovers (p : CAP5BadPairingSupports) : Prop :=
  CAP5BadRedBlueComponentCover p.redBlue₁ p.redBlue₂ ∧
  CAP5BadRedPurpleComponentCover p.redPurple₁ p.redPurple₂

/-- Component-cover data from the graph-level Kempe-component proof supplies the active-pairing
hypotheses needed by the finite CAP5 repair enumeration. -/
theorem hasActivePairings_of_componentCovers
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    p.HasActivePairings := by
  exact ⟨cap5BadRedBlueActivePairing_of_componentCover h.1,
    cap5BadRedPurpleActivePairing_of_componentCover h.2⟩

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

/-- Component-cover form of the finite CAP5 move split: graph-level component covers already
force either an immediate repair support or the simultaneous exceptional pattern. -/
theorem repairOrExceptional_of_componentCovers
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    p.RepairOrExceptional :=
  repairOrExceptional_of_activePairings (hasActivePairings_of_componentCovers h)

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

/-- Component-cover form of the exact obstruction statement: under graph-level cover data,
failure to find a repair support is exactly the simultaneous exceptional pattern. -/
theorem isExceptional_iff_not_hasRepair_of_componentCovers
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    p.IsExceptional ↔ ¬ p.HasRepair :=
  isExceptional_iff_not_hasRepair_of_activePairings
    (hasActivePairings_of_componentCovers h)

/-- Component-cover form of the repair criterion: under graph-level cover data, excluding the
simultaneous exceptional pattern is exactly the same as exposing a finite repair support. -/
theorem hasRepair_iff_not_isExceptional_of_componentCovers
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    p.HasRepair ↔ ¬ p.IsExceptional :=
  hasRepair_iff_not_isExceptional_of_activePairings
    (hasActivePairings_of_componentCovers h)

/-- Support-aware form of immediate CAP5 repair.  If one of the component supports lies on the
repair side, then one of the four support-carried boundary swaps realizes a finite repair type
and the resulting word extends across the cap. -/
theorem exists_repairingBoundaryAction_usingSupport_of_hasRepair
    {p : CAP5BadPairingSupports} (h : p.HasRepair) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) := by
  rcases h with h₁ | h₂ | h₃ | h₄
  · refine ⟨cap5BoundarySwap red blue p.redBlue₁, ?_, ?_, ?_⟩
    · exact Or.inl rfl
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad h₁
    · exact cap5_extendsAcrossCycle_of_redBlueRepairSupport_bad h₁
  · refine ⟨cap5BoundarySwap red blue p.redBlue₂, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inl rfl)
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redBlueRepairSupport_bad h₂
    · exact cap5_extendsAcrossCycle_of_redBlueRepairSupport_bad h₂
  · refine ⟨cap5BoundarySwap red purple p.redPurple₁, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad h₃
    · exact cap5_extendsAcrossCycle_of_redPurpleRepairSupport_bad h₃
  · refine ⟨cap5BoundarySwap red purple p.redPurple₂, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact cap5BoundaryActionRealizesSomeRepairType_of_redPurpleRepairSupport_bad h₄
    · exact cap5_extendsAcrossCycle_of_redPurpleRepairSupport_bad h₄

/-- If a component-support package has a repair support, then some induced boundary action repairs
the canonical bad CAP5 word and the repaired word extends across the cap. -/
theorem exists_repairingBoundaryAction_of_hasRepair
    {p : CAP5BadPairingSupports} (h : p.HasRepair) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) := by
  rcases exists_repairingBoundaryAction_usingSupport_of_hasRepair h with
    ⟨action, _huses, hrealizes, hextends⟩
  exact ⟨action, hrealizes, hextends⟩

/-- Support-aware immediate CAP5 repair, packaged as an actual repair of the canonical bad word:
the input is nonextendable and the support-carried boundary action's output is extendable. -/
theorem exists_boundaryActionRepairsWord_usingSupport_of_hasRepair
    {p : CAP5BadPairingSupports} (h : p.HasRepair) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 := by
  rcases exists_repairingBoundaryAction_usingSupport_of_hasRepair h with
    ⟨action, huses, hrealizes, _hextends⟩
  exact ⟨action, huses, hrealizes,
    cap5_boundaryActionRepairsWord_of_boundaryActionRealizesSomeRepairType_bad hrealizes⟩

/-- Immediate CAP5 repair, packaged as an actual repair of the canonical bad word. -/
theorem exists_boundaryActionRepairsWord_of_hasRepair
    {p : CAP5BadPairingSupports} (h : p.HasRepair) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 := by
  rcases exists_boundaryActionRepairsWord_usingSupport_of_hasRepair h with
    ⟨action, _huses, hrealizes, hrepairs⟩
  exact ⟨action, hrealizes, hrepairs⟩

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

/-- Repair-predicate form of the finite CAP5 move-realizability split: the repair side gives a
boundary action whose input is the canonical bad word and whose output extends across the cap. -/
theorem repairOrExceptional_repairOutcome
    {p : CAP5BadPairingSupports} (h : p.RepairOrExceptional) :
    (∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional := by
  rcases h with hrepair | hexceptional
  · exact Or.inl (exists_boundaryActionRepairsWord_of_hasRepair hrepair)
  · exact Or.inr hexceptional

/-- Support-aware repair-predicate form of the finite CAP5 split.  On the repair side, the
boundary action is one of the four swaps carried by the component supports. -/
theorem repairOrExceptional_repairOutcome_usingSupport
    {p : CAP5BadPairingSupports} (h : p.RepairOrExceptional) :
    (∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional := by
  rcases h with hrepair | hexceptional
  · exact Or.inl (exists_boundaryActionRepairsWord_usingSupport_of_hasRepair hrepair)
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

/-- Repair-predicate outcome for active CAP5 pairings: a graph-level active-pairing package
either exposes a genuine boundary-action repair or is exactly the simultaneous exceptional
pattern. -/
theorem activePairings_repairOutcome
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    (∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional :=
  repairOrExceptional_repairOutcome (repairOrExceptional_of_activePairings h)

/-- Support-aware repair-predicate outcome for active CAP5 pairings. -/
theorem activePairings_repairOutcome_usingSupport
    {p : CAP5BadPairingSupports} (h : p.HasActivePairings) :
    (∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional :=
  repairOrExceptional_repairOutcome_usingSupport (repairOrExceptional_of_activePairings h)

/-- Repair-predicate outcome from graph-level component-cover data. -/
theorem componentCovers_repairOutcome
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    (∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional :=
  activePairings_repairOutcome (hasActivePairings_of_componentCovers h)

/-- Support-aware repair-predicate outcome from graph-level component-cover data. -/
theorem componentCovers_repairOutcome_usingSupport
    {p : CAP5BadPairingSupports} (h : p.HasComponentCovers) :
    (∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111) ∨
    p.IsExceptional :=
  activePairings_repairOutcome_usingSupport (hasActivePairings_of_componentCovers h)

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

/-- Non-support-aware graph-facing endpoint from component covers. -/
theorem exists_repairingBoundaryAction_of_componentCovers_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) :=
  exists_repairingBoundaryAction_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_componentCovers hcovers).2 hnotExceptional)

/-- Packaged graph-facing endpoint from active CAP5 pairings after excluding the simultaneous
exceptional pattern: the produced boundary action genuinely repairs the canonical bad word. -/
theorem exists_boundaryActionRepairsWord_of_activePairings_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hpair : p.HasActivePairings) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 :=
  exists_boundaryActionRepairsWord_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_activePairings hpair).2 hnotExceptional)

/-- Packaged non-support-aware graph-facing endpoint from component covers after excluding the
simultaneous exceptional pattern. -/
theorem exists_boundaryActionRepairsWord_of_componentCovers_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 :=
  exists_boundaryActionRepairsWord_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_componentCovers hcovers).2 hnotExceptional)

/-- Support-aware final endpoint after the graph-level separator proof excludes the simultaneous
exceptional pattern.  The produced repair action is one of the four swaps attached to the active
component supports. -/
theorem exists_repairingBoundaryAction_usingSupport_of_activePairings_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hpair : p.HasActivePairings) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) :=
  exists_repairingBoundaryAction_usingSupport_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_activePairings hpair).2 hnotExceptional)

/-- Packaged support-aware final endpoint from active CAP5 pairings after excluding the simultaneous
exceptional pattern. -/
theorem exists_boundaryActionRepairsWord_usingSupport_of_activePairings_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hpair : p.HasActivePairings) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 :=
  exists_boundaryActionRepairsWord_usingSupport_of_hasRepair
    ((hasRepair_iff_not_isExceptional_of_activePairings hpair).2 hnotExceptional)

/-- Graph-facing final CAP5 endpoint: disjoint component covers of both active supports already
supply active pairings, so excluding the simultaneous exceptional pattern produces a support-carried
repair action whose boundary word extends across the cap. -/
theorem exists_repairingBoundaryAction_usingSupport_of_componentCovers_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5WordExtendsAcrossCycle (action cap5BadBoundaryWord2111) :=
  exists_repairingBoundaryAction_usingSupport_of_activePairings_of_not_isExceptional
    (hasActivePairings_of_componentCovers hcovers) hnotExceptional

/-- Packaged graph-facing final CAP5 endpoint: disjoint component covers of both active supports,
plus exclusion of the simultaneous exceptional pattern, produce a support-carried boundary action
that genuinely repairs the canonical bad word. -/
theorem exists_boundaryActionRepairsWord_usingSupport_of_componentCovers_of_not_isExceptional
    {p : CAP5BadPairingSupports}
    (hcovers : p.HasComponentCovers) (hnotExceptional : ¬ p.IsExceptional) :
    ∃ action : CAP5BoundaryAction,
      p.BoundaryActionUsesSupport action ∧
      CAP5BoundaryActionRealizesSomeRepairType action cap5BadBoundaryWord2111 ∧
      CAP5BoundaryActionRepairsWord action cap5BadBoundaryWord2111 :=
  exists_boundaryActionRepairsWord_usingSupport_of_activePairings_of_not_isExceptional
    (hasActivePairings_of_componentCovers hcovers) hnotExceptional

end CAP5BadPairingSupports

end Mettapedia.GraphTheory.FourColor

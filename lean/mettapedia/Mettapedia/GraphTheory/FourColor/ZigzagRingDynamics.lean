import Mettapedia.GraphTheory.FourColor.ZigzagRingTangle

/-!
# Colour dynamics of a zigzag ring

The cursor description, conservation of each colour multiplicity, and the
complementary second ring are uniform in the circumference. The relation is
the boundary support of the actual two-sided ring tangle; no terminal-routing
condition is imposed.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open scoped BigOperators

variable (k : Nat) [NeZero k]

/-- Move the boundary origin by one port. -/
def shift (x : Fin k → Color) : Fin k → Color := fun i => x (i + 1)

/-- A genuine properly coloured ring. -/
abbrev Step (x y : Fin k → Color) : Prop := (ring k).AcceptsBoundaryWords x y

/-- Multiplicity of a colour, including zero for convenience. -/
def colourCount (x : Fin k → Color) (c : Color) : Nat :=
  ∑ i, if x i = c then 1 else 0

private theorem cursor_local {p q r : Color}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hrq : r ≠ q) (hproper : p ≠ q + r) :
    (p ≠ q → r = p ∧ p + (q + r) = q) ∧
    (p = q → p + (q + r) = r) := by
  revert p q r
  decide +kernel

/-- Away from a collision the cursor must stay fixed; at a collision the
new output is exactly the new cursor colour. -/
theorem Valid.cursor {x a : Fin k → Color} (h : Valid k x a) (i : Fin k) :
    (a i ≠ x (i + 1) → a (i + 1) = a i ∧ outWord k x a i = x (i + 1)) ∧
    (a i = x (i + 1) → outWord k x a i = a (i + 1)) :=
  cursor_local (h.a_ne_zero i) (h.x_ne_zero (i + 1)) (h.a_ne_zero (i + 1))
    (h.a_ne_x (i + 1)) (h.a_ne_b i)

private theorem cursor_balance {p q r c : Color}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hrq : r ≠ q) (hproper : p ≠ q + r) :
    (if p + (q + r) = c then 1 else 0) + (if p = c then 1 else 0) =
      (if q = c then 1 else 0) + (if r = c then 1 else 0) := by
  revert p q r c
  decide +kernel

theorem colourCount_shift (x : Fin k → Color) (c : Color) :
    colourCount k (shift k x) c = colourCount k x c := by
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin k)) (fun i => if x i = c then 1 else 0)

/-- Each colour's port multiplicity is conserved, not just its parity. -/
theorem Valid.colourCount_eq {x a : Fin k → Color} (h : Valid k x a) (c : Color) :
    colourCount k (outWord k x a) c = colourCount k x c := by
  have hlocal : ∀ i : Fin k,
      (if outWord k x a i = c then 1 else 0) + (if a i = c then 1 else 0) =
        (if x (i + 1) = c then 1 else 0) + (if a (i + 1) = c then 1 else 0) :=
    fun i => cursor_balance (h.a_ne_zero i) (h.x_ne_zero (i + 1))
      (h.a_ne_zero (i + 1)) (h.a_ne_x (i + 1)) (h.a_ne_b i)
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hlocal i)
  simp only [Finset.sum_add_distrib] at hs
  change colourCount k (outWord k x a) c + colourCount k a c =
    colourCount k (shift k x) c + colourCount k (shift k a) c at hs
  rw [colourCount_shift, colourCount_shift] at hs
  exact Nat.add_right_cancel hs

theorem Step.colourCount {x y : Fin k → Color} (h : Step k x y) (c : Color) :
    colourCount k y c = colourCount k x c := by
  obtain ⟨a, ha, rfl⟩ := (accepts_iff k x y).1 h
  exact ha.colourCount_eq k c

private theorem cancel_middle (p q r : Color) : p + ((q + r) + r) = p + q := by
  rw [add_assoc q r r, color_add_self, add_zero]

/-- The complementary cursor supplies a second valid ring. -/
theorem Valid.complement {x a : Fin k → Color} (h : Valid k x a) :
    Valid k (outWord k x a) (bColor k x a) := by
  constructor
  · exact h.out_ne_zero k
  · exact h.b_ne_zero k
  · intro i
    exact (add_ne_right_of_ne_zero (h.a_ne_zero i)).symm
  · intro i
    change bColor k x a i ≠ outWord k x a (i + 1) + bColor k x a (i + 1)
    simp only [outWord, add_assoc, color_add_self, add_zero]
    exact add_ne_right_of_ne_zero (h.x_ne_zero (i + 1))

/-- Every ring followed by its complementary colouring shifts the input
word once. This provides idle steps when following a rotating boundary. -/
theorem outWord_complement (x a : Fin k → Color) :
    outWord k (outWord k x a) (bColor k x a) = shift k x := by
  funext i
  change bColor k x a i + ((a (i + 1) + bColor k x a (i + 1)) +
    bColor k x a (i + 1)) = x (i + 1)
  rw [cancel_middle]
  simp only [bColor, add_assoc, color_add_self, add_zero]

theorem Step.two_ring_shift {x y : Fin k → Color} (h : Step k x y) :
    Step k y (shift k x) := by
  obtain ⟨a, ha, rfl⟩ := (accepts_iff k x y).1 h
  exact (accepts_iff k _ _).2 ⟨bColor k x a, ha.complement k,
    (outWord_complement k x a).symm⟩

/-- Exchange two neighbouring boundary letters. -/
def swapAt (x : Fin k → Color) (j : Fin k) : Fin k → Color :=
  fun i => if i = j then x (j + 1) else if i = j + 1 then x j else x i

/-- Modify the complementary second cursor at the chosen collision. -/
def swapCursor (x a : Fin k → Color) (j : Fin k) : Fin k → Color :=
  fun i => if i = j then x (j + 1) else bColor k x a i

private theorem swap_output_first (p q r : Color) : p + ((q + p + r) + r) = q := by
  revert p q r
  decide +kernel

private theorem swap_output_second (p q : Color) :
    (p + q) + (q + (q + (p + q)) + q) = q := by
  revert p q
  decide +kernel

/-- The algebra of the two-ring swap, given its two anchored cursor values. -/
theorem outWord_swapCursor (x a : Fin k → Color) (j : Fin k)
    (hne : x j ≠ x (j + 1)) (ha : a j = x (j + 1))
    (ha' : a (j + 1) = x j + x (j + 1)) :
    outWord k (outWord k x a) (swapCursor k x a j) = shift k (swapAt k x j) := by
  have hj : j + 1 ≠ j := fun h => hne (congrArg x h.symm)
  funext i
  by_cases hi : i = j
  · subst i
    simp only [outWord, bColor, swapCursor, shift, swapAt, ite_true, hj, ite_false]
    rw [ha']
    exact swap_output_first _ _ _
  · by_cases hi' : i + 1 = j
    · have hi'' : i + 1 ≠ j + 1 := fun h => hi (add_right_cancel h)
      simp only [outWord, bColor, swapCursor, shift, swapAt, hi, hi', ite_false,
        ite_true, ha, ha']
      exact swap_output_second _ _
    · have hi'' : i + 1 ≠ j + 1 := fun h => hi (add_right_cancel h)
      change outWord k (outWord k x a) (swapCursor k x a j) i = _
      have heq : outWord k (outWord k x a) (swapCursor k x a j) i =
          outWord k (outWord k x a) (bColor k x a) i := by
        simp [outWord, bColor, swapCursor, hi, hi']
      rw [heq, outWord_complement]
      simp [shift, swapAt, hi', hi'']

theorem Valid.swapCursor_valid {x a : Fin k → Color} (h : Valid k x a) (j : Fin k)
    (hne : x j ≠ x (j + 1)) (ha : a j = x (j + 1))
    (ha' : a (j + 1) = x j + x (j + 1)) :
    Valid k (outWord k x a) (swapCursor k x a j) := by
  have hout := outWord_swapCursor k x a j hne ha ha'
  constructor
  · exact h.out_ne_zero k
  · intro i
    by_cases hi : i = j
    · simp only [swapCursor, hi, ite_true]
      exact h.x_ne_zero _
    · simp only [swapCursor, hi, ite_false]
      exact h.b_ne_zero k i
  · intro i
    by_cases hi : i = j
    · subst i
      have hy := (h.cursor k j).2 ha
      simpa only [swapCursor, ite_true, hy] using (h.a_ne_x (j + 1)).symm
    · simpa only [swapCursor, hi, ite_false] using (h.complement k).a_ne_x i
  · intro i heq
    have hzero : outWord k (outWord k x a) (swapCursor k x a j) i = 0 := by
      simp only [outWord, heq, color_add_self]
    rw [hout] at hzero
    simp only [shift, swapAt] at hzero
    split_ifs at hzero <;> exact h.x_ne_zero _ hzero

/-- An anchored first cursor produces the adjacent swap in two physical rings. -/
theorem two_ring_swap_of_cursor {x a : Fin k → Color} (h : Valid k x a)
    (j : Fin k) (hne : x j ≠ x (j + 1)) (ha : a j = x (j + 1))
    (ha' : a (j + 1) = x j + x (j + 1)) :
    ∃ y, Step k x y ∧ Step k y (shift k (swapAt k x j)) := by
  refine ⟨outWord k x a, (accepts_iff k _ _).2 ⟨a, h, rfl⟩, ?_⟩
  exact (accepts_iff k _ _).2 ⟨swapCursor k x a j, h.swapCursor_valid k j hne ha ha',
    (outWord_swapCursor k x a j hne ha ha').symm⟩

end Mettapedia.GraphTheory.FourColor.ZigzagRing

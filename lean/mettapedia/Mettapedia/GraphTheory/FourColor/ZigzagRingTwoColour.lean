import Mettapedia.GraphTheory.FourColor.ZigzagRingErgodicity

/-!
# Rigidity of zigzag tubes when a colour is absent

With at most two input colours a ring either preserves the word or shifts
it once. A cursor that ever takes the missing colour must keep that colour
around the whole ring. A cursor that avoids it produces the identity.
Consequently colour counts alone do not classify all mixing components.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping

variable (k : Nat) [NeZero k]

private theorem cursor_constant_of_missing {x a : Fin k → Color}
    (ha : Valid k x a) {c : Color} (hx : ∀ i, x i ≠ c)
    {j : Fin k} (hj : a j = c) : ∀ i, a i = c := by
  have hsucc : ∀ i, a i = c → a (i + 1) = c := by
    intro i hi
    have hne : a i ≠ x (i + 1) := by rw [hi]; exact (hx _).symm
    exact ((ha.cursor k i).1 hne).1.trans hi
  have hwalk : ∀ n, a (j + Fin.ofNat k n) = c := by
    intro n
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      have hcast : Fin.ofNat k (n + 1) = Fin.ofNat k n + 1 := by
        apply Fin.ext
        change (n + 1) % k = (n % k + 1 % k) % k
        exact Nat.add_mod n 1 k
      rw [hcast, ← add_assoc]
      exact hsucc _ ih
  intro i
  have h := hwalk (i - j).val
  simpa [add_comm, sub_add_cancel] using h

/-- If a nonzero colour is absent, a physical ring cannot do more than
preserve or cyclically shift the boundary word. -/
theorem Step.eq_or_shift_of_missing {x y : Fin k → Color} (h : Step k x y)
    {c : Color} (hc : c ≠ 0) (hx : ∀ i, x i ≠ c) :
    y = x ∨ y = shift k x := by
  obtain ⟨a, ha, rfl⟩ := (accepts_iff k x y).mp h
  by_cases hsome : ∃ j, a j = c
  · obtain ⟨j, hj⟩ := hsome
    have hconst := cursor_constant_of_missing k ha hx hj
    right
    funext i
    exact ((ha.cursor k i).1 (by rw [hconst]; exact (hx _).symm)).2
  · have hane : ∀ i, a i ≠ c := fun i hi => hsome ⟨i, hi⟩
    have hsum : ∀ i, x i + a i = c := fun i =>
      (third_eq_add (ha.x_ne_zero i) (ha.a_ne_zero i) hc
        (ha.a_ne_x i).symm (hx i) (hane i)).symm
    left
    funext i
    change a i + (x (i + 1) + a (i + 1)) = x i
    rw [hsum, ← hsum i]
    simp [add_left_comm]

/-- Both alternatives are physically realizable, at every circumference. -/
theorem step_iff_of_missing (x y : Fin k → Color) (hnz : ∀ i, x i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hx : ∀ i, x i ≠ c) :
    Step k x y ↔ y = x ∨ y = shift k x := by
  constructor
  · exact fun h => h.eq_or_shift_of_missing k hc hx
  · rintro (heq | heq) <;> subst y
    · apply (accepts_iff k _ _).mpr
      refine ⟨fun i => x i + c, ⟨hnz, ?_, ?_, ?_⟩, ?_⟩
      · exact fun i => add_ne_zero_of_ne (hx i)
      · exact fun i => add_ne_left_of_ne_zero hc
      · intro i
        change x i + c ≠ x (i + 1) + (x (i + 1) + c)
        rw [← add_assoc (x (i + 1)), color_add_self, zero_add]
        exact add_ne_right_of_ne_zero (hnz i)
      · funext i
        change x i = (x i + c) + (x (i + 1) + (x (i + 1) + c))
        rw [← add_assoc (x (i + 1)), color_add_self, zero_add,
          add_assoc, color_add_self, add_zero]
    · apply (accepts_iff k _ _).mpr
      refine ⟨fun _ => c, ⟨hnz, fun _ => hc, fun i => (hx i).symm, ?_⟩, ?_⟩
      · intro i
        exact (add_ne_right_of_ne_zero (hnz (i + 1))).symm
      · funext i
        change x (i + 1) = c + (x (i + 1) + c)
        rw [add_left_comm c, color_add_self, add_zero]

/-- Along any number of rings, a word missing a colour can only rotate.
The exponent counts the rings on which a shift was chosen. -/
theorem transfer_rotation_of_missing {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) n x y) {c : Color} (hc : c ≠ 0) :
    (∀ i, x i ≠ c) → ∃ m, m ≤ n ∧ y = (shift k)^[m] x := by
  induction h with
  | zero => intro _; exact ⟨0, le_rfl, rfl⟩
  | @succ n x z y hstep htail ih =>
      intro hx
      rcases hstep.eq_or_shift_of_missing k hc hx with rfl | rfl
      · obtain ⟨m, hm, hy⟩ := ih hx
        exact ⟨m, by omega, hy⟩
      · obtain ⟨m, hm, hy⟩ := ih (fun i => hx (i + 1))
        exact ⟨m + 1, by omega, by simpa only [Function.iterate_succ_apply] using hy⟩

/-- Equal admissible colour counts do not guarantee tube reachability when
the third colour is absent. The two words have cyclic runs of lengths 2+2
and 1+1+1+1, respectively. -/
theorem two_colour_nonmixing :
    let x : Fin 4 → Color := ![red, red, blue, blue]
    let y : Fin 4 → Color := ![red, blue, red, blue]
    (∀ c, colourCount 4 x c = colourCount 4 y c) ∧
    (∑ i, x i) = 0 ∧ (∑ i, y i) = 0 ∧
    ∀ n, ¬ ExactRelationalTransfer (Step 4) n x y := by
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro n h
  obtain ⟨m, _, hm⟩ := transfer_rotation_of_missing 4 h purple_ne_zero (by decide +kernel)
  have hpairs : ∀ r, ∃ i : Fin 4,
      ((shift 4)^[r] ![red, red, blue, blue]) i =
        ((shift 4)^[r] ![red, red, blue, blue]) (i + 1) := by
    intro r
    induction r with
    | zero => exact ⟨0, rfl⟩
    | succ r ih =>
      obtain ⟨i, hi⟩ := ih
      refine ⟨i - 1, ?_⟩
      simpa only [Function.iterate_succ_apply', shift, sub_add_cancel] using hi
  obtain ⟨i, hi⟩ := hpairs m
  rw [← hm] at hi
  have hneq : ∀ i : Fin 4,
      (![red, blue, red, blue] : Fin 4 → Color) i ≠
        (![red, blue, red, blue] : Fin 4 → Color) (i + 1) := by decide +kernel
  exact hneq i hi

end Mettapedia.GraphTheory.FourColor.ZigzagRing

import Mettapedia.GraphTheory.FourColor.ZigzagRingDynamics

/-!
# Constructing a closed cursor with a prescribed collision

After the prescribed first collision the cursor carries the third colour
until it encounters that colour in the input. Thereafter it uses only the
other two colours, which forces compatibility at the closing seam.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

private def nextCursor (u v input old : Color) : Color :=
  if old ≠ input then old else if input = u then v else u

private theorem nextCursor_valid (u v input old : Color)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hi : input ≠ 0) (ho : old ≠ 0) :
    nextCursor u v input old ≠ 0 ∧ nextCursor u v input old ≠ input ∧
      old ≠ input + nextCursor u v input old := by
  revert u v input old
  decide +kernel

private theorem nextCursor_stays (u v t input old : Color)
    (hu : u ≠ t) (hv : v ≠ t) (ho : old ≠ t) :
    nextCursor u v input old ≠ t := by
  unfold nextCursor
  split_ifs <;> assumption

private theorem nextCursor_leaves (u v t old : Color) (hu : u ≠ t) (hv : v ≠ t) :
    nextCursor u v t old ≠ t := by
  unfold nextCursor
  split_ifs <;> assumption

/-- The sequence starts at port one, after the prescribed collision. -/
private def cursorSeq (u v t : Color) (x : Nat → Color) : Nat → Color
  | 0 => t
  | n + 1 => nextCursor u v (x (n + 2)) (cursorSeq u v t x n)

private theorem cursorSeq_ne_zero (u v t : Color) (x : Nat → Color)
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0) (huv : u ≠ v)
    (hx : ∀ n, x n ≠ 0) (n : Nat) : cursorSeq u v t x n ≠ 0 := by
  induction n with
  | zero => exact ht
  | succ n ih => exact (nextCursor_valid u v _ _ hu hv huv (hx _) ih).1

private theorem cursorSeq_ne_input (u v t : Color) (x : Nat → Color)
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0) (huv : u ≠ v)
    (htv : t ≠ v) (hx : ∀ n, x n ≠ 0) (h1 : x 1 = v) (n : Nat) :
    cursorSeq u v t x n ≠ x (n + 1) := by
  cases n with
  | zero => simpa [cursorSeq, h1] using htv
  | succ n =>
      exact (nextCursor_valid u v _ _ hu hv huv (hx _)
        (cursorSeq_ne_zero u v t x hu hv ht huv hx n)).2.1

private theorem cursorSeq_transition (u v t : Color) (x : Nat → Color)
    (hu : u ≠ 0) (hv : v ≠ 0) (ht : t ≠ 0) (huv : u ≠ v)
    (hx : ∀ n, x n ≠ 0) (n : Nat) :
    cursorSeq u v t x n ≠ x (n + 2) + cursorSeq u v t x (n + 1) :=
  (nextCursor_valid u v _ _ hu hv huv (hx _)
    (cursorSeq_ne_zero u v t x hu hv ht huv hx n)).2.2

private theorem cursorSeq_stays (u v t : Color) (x : Nat → Color)
    (hut : u ≠ t) (hvt : v ≠ t) (n : Nat)
    (hn : cursorSeq u v t x n ≠ t) (d : Nat) :
    cursorSeq u v t x (n + d) ≠ t := by
  induction d with
  | zero => simpa using hn
  | succ d ih => exact nextCursor_stays u v t _ _ hut hvt ih

private theorem cursorSeq_after_third (u v t : Color) (x : Nat → Color)
    (hut : u ≠ t) (hvt : v ≠ t) (p n : Nat) (hp : x (p + 2) = t)
    (hpn : p + 1 ≤ n) : cursorSeq u v t x n ≠ t := by
  have hleave : cursorSeq u v t x (p + 1) ≠ t := by
    simp only [cursorSeq, hp]
    exact nextCursor_leaves u v t _ hut hvt
  have hs := cursorSeq_stays u v t x hut hvt (p + 1) hleave (n - (p + 1))
  simpa only [Nat.add_sub_of_le hpn] using hs

variable (k : Nat) [NeZero k]

private def natWord (x : Fin k → Color) (n : Nat) : Color := x (Fin.ofNat k n)

private theorem natWord_val (x : Fin k → Color) (i : Fin k) :
    natWord k x i.val = x i := by simp [natWord]

private def anchoredCursor (x : Fin k → Color) (u v t : Color) (i : Fin k) : Color :=
  if i = 0 then v else cursorSeq u v t (natWord k x) (i.val - 1)

/-- Close a cursor whose first two values force the required adjacent swap. -/
theorem exists_cursor_at_zero (hk : 3 ≤ k) (x : Fin k → Color)
    (hx : ∀ i, x i ≠ 0) (hne : x 0 ≠ x 1)
    (hthird : ∃ i, x i = x 0 + x 1) :
    ∃ a, Valid k x a ∧ a 0 = x 1 ∧ a 1 = x 0 + x 1 := by
  let u := x 0
  let v := x 1
  let t := u + v
  have hu : u ≠ 0 := hx 0
  have hv : v ≠ 0 := hx 1
  have huv : u ≠ v := hne
  obtain ⟨ht, htu, htv⟩ := third_color_properties hu hv huv
  have hnz : ∀ n, natWord k x n ≠ 0 := fun n => hx _
  have h1 : natWord k x 1 = v := rfl
  have hone : (1 : Fin k).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hone0 : (1 : Fin k) ≠ 0 := by
    intro h
    have hz : (0 : Fin k).val = 0 := rfl
    have he := congrArg Fin.val h
    rw [hone, hz] at he
    omega
  let a := anchoredCursor k x u v t
  have ha0 : a 0 = v := by simp [a, anchoredCursor]
  have ha1 : a 1 = t := by
    simp only [a, anchoredCursor, hone0, ite_false, hone, Nat.sub_self, cursorSeq]
  have han : ∀ i : Fin k, i ≠ 0 → a i = cursorSeq u v t (natWord k x) (i.val - 1) := by
    intro i hi
    simp [a, anchoredCursor, hi]
  have ha_nz : ∀ i, a i ≠ 0 := by
    intro i
    by_cases hi : i = 0
    · simpa [hi, ha0] using hv
    · rw [han i hi]
      exact cursorSeq_ne_zero u v t _ hu hv ht huv hnz _
  have ha_x : ∀ i, a i ≠ x i := by
    intro i
    by_cases hi : i = 0
    · simpa [hi, ha0] using huv.symm
    · have hiv : 0 < i.val := by
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      rw [han i hi]
      have hs := cursorSeq_ne_input u v t _ hu hv ht huv htv hnz h1 (i.val - 1)
      simpa only [Nat.sub_add_cancel hiv, natWord_val] using hs
  obtain ⟨q, hq⟩ := hthird
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    exact htu hq.symm
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact htv hq.symm
  have hqval : 2 ≤ q.val := by
    have hqv0 : q.val ≠ 0 := fun h => hq0 (Fin.ext h)
    have hqv1 : q.val ≠ 1 := fun h => hq1 (Fin.ext (h.trans hone.symm))
    omega
  have hlast : cursorSeq u v t (natWord k x) (k - 2) ≠ t := by
    apply cursorSeq_after_third u v t _ htu.symm htv.symm (q.val - 2) (k - 2)
    · simpa only [Nat.sub_add_cancel hqval, natWord_val] using hq
    · have := q.isLt
      omega
  refine ⟨a, ⟨hx, ha_nz, ha_x, ?_⟩, ha0, ha1⟩
  intro i
  by_cases hwrap : i + 1 = 0
  · have hiv : i.val = k - 1 := by
      have hm := congrArg Fin.val hwrap
      change (i.val + 1 % k) % k = 0 at hm
      rw [Nat.mod_eq_of_lt (by omega : 1 < k)] at hm
      have := i.isLt
      by_contra hval
      have hlt : i.val + 1 < k := by omega
      rw [Nat.mod_eq_of_lt hlt] at hm
      omega
    have hi : i ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      change i.val = 0 at this
      rw [hiv] at this
      omega
    simp only [bColor, hwrap, ha0]
    rw [han i hi, hiv]
    have hn : k - 1 - 1 = k - 2 := by omega
    rw [hn]
    exact hlast
  · have hvnext : (i + 1).val = i.val + 1 := by
      have hm : (i + 1).val = (i.val + 1) % k := by simp only [Fin.val_add, hone]
      have hn : (i + 1).val ≠ 0 := fun h => hwrap (Fin.ext h)
      have := i.isLt
      rw [hm]
      apply Nat.mod_eq_of_lt
      by_contra hlt
      have heq : i.val + 1 = k := by omega
      exact hn (by rw [hm, heq, Nat.mod_self])
    by_cases hi : i = 0
    · subst i
      simp only [zero_add, bColor, ha0, ha1]
      exact (add_ne_left_of_ne_zero ht).symm
    · have hiv : 0 < i.val := by
        have : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      rw [han i hi]
      simp only [bColor, han (i + 1) hwrap, hvnext, Nat.add_sub_cancel]
      have hs := cursorSeq_transition u v t _ hu hv ht huv hnz (i.val - 1)
      have hn : i.val - 1 + 2 = (i + 1).val := by omega
      simpa only [hn, Nat.sub_add_cancel hiv, natWord_val] using hs

/-- Reindex a word by a cyclic displacement. -/
def rotate (x : Fin k → Color) (j : Fin k) : Fin k → Color := fun i => x (i + j)

theorem Valid.rotate_valid {x a : Fin k → Color} (h : Valid k x a) (j : Fin k) :
    Valid k (rotate k x j) (rotate k a j) := by
  constructor
  · exact fun i => h.x_ne_zero (i + j)
  · exact fun i => h.a_ne_zero (i + j)
  · exact fun i => h.a_ne_x (i + j)
  · intro i
    simpa [rotate, bColor, add_assoc, add_left_comm, add_comm] using h.a_ne_b (i + j)

theorem Step.rotate_step {x y : Fin k → Color} (h : Step k x y) (j : Fin k) :
    Step k (rotate k x j) (rotate k y j) := by
  obtain ⟨a, ha, rfl⟩ := (accepts_iff k x y).1 h
  refine (accepts_iff k _ _).2 ⟨rotate k a j, ha.rotate_valid k j, ?_⟩
  funext i
  simp [rotate, outWord, bColor, add_assoc, add_comm]

/-- The prescribed collision may be placed at any port of the ring. -/
theorem exists_cursor (hk : 3 ≤ k) (x : Fin k → Color)
    (hx : ∀ i, x i ≠ 0) (j : Fin k) (hne : x j ≠ x (j + 1))
    (hthird : ∃ i, x i = x j + x (j + 1)) :
    ∃ a, Valid k x a ∧ a j = x (j + 1) ∧ a (j + 1) = x j + x (j + 1) := by
  have hrne : rotate k x j 0 ≠ rotate k x j 1 := by
    simpa [rotate, add_comm] using hne
  have hrthird : ∃ i, rotate k x j i = rotate k x j 0 + rotate k x j 1 := by
    obtain ⟨i, hi⟩ := hthird
    exact ⟨i - j, by simpa [rotate, add_comm] using hi⟩
  obtain ⟨a, ha, ha0, ha1⟩ := exists_cursor_at_zero k hk (rotate k x j)
    (fun i => hx _) hrne hrthird
  have hback : rotate k (rotate k x j) (-j) = x := by
    funext i
    simp [rotate, add_assoc]
  refine ⟨rotate k a (-j), ?_, ?_, ?_⟩
  · simpa only [hback] using ha.rotate_valid k (-j)
  · simpa [rotate, add_comm] using ha0
  · simpa [rotate, add_assoc, add_left_comm, add_comm] using ha1

/-- The two-ring swap needs only nonzero inputs and occurrence of the third
colour. No parity-admissibility or bound on the circumference is required. -/
theorem two_ring_swap (hk : 3 ≤ k) (x : Fin k → Color)
    (hx : ∀ i, x i ≠ 0) (j : Fin k) (hne : x j ≠ x (j + 1))
    (hthird : ∃ i, x i = x j + x (j + 1)) :
    ∃ y, Step k x y ∧ Step k y (shift k (swapAt k x j)) := by
  obtain ⟨a, ha, ha0, ha1⟩ := exists_cursor k hk x hx j hne hthird
  exact two_ring_swap_of_cursor k ha j hne ha0 ha1

end Mettapedia.GraphTheory.FourColor.ZigzagRing

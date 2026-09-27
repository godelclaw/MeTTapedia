import Mettapedia.GraphTheory.FourColor.ZigzagRingCursor
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorPumping
import Mathlib.GroupTheory.Perm.Sign

/-!
# Mixing within colour-count classes of zigzag tubes

Adjacent swaps and idle steps in rotating coordinates yield exact-length
colouring paths between words with the same multiplicities. The circumference
is arbitrary; only the use of all three nonzero colours is required.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping
open scoped BigOperators

variable (k : Nat) [NeZero k]

/-- A boundary word uses precisely the three Tait colours. -/
def Full (x : Fin k → Color) : Prop :=
  (∀ i, x i ≠ 0) ∧ ∀ c : Color, c ≠ 0 → ∃ i, x i = c

/-- Elementary word operations before accounting for the moving origin. -/
def Move (x y : Fin k → Color) : Prop := y = x ∨ ∃ j, y = swapAt k x j

theorem swapAt_eq_comp_swap (x : Fin k → Color) (j : Fin k) :
    swapAt k x j = x ∘ Equiv.swap j (j + 1) := by
  funext i
  simp only [swapAt, Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> rfl

omit [NeZero k] in
theorem Full.comp_perm {x : Fin k → Color} (hx : Full k x) (p : Equiv.Perm (Fin k)) :
    Full k (x ∘ p) := by
  refine ⟨fun i => hx.1 _, ?_⟩
  intro c hc
  obtain ⟨i, hi⟩ := hx.2 c hc
  exact ⟨p.symm i, by simpa using hi⟩

theorem Move.full {x y : Fin k → Color} (h : Move k x y) (hx : Full k x) : Full k y := by
  rcases h with rfl | ⟨j, rfl⟩
  · exact hx
  · rw [swapAt_eq_comp_swap]
    exact hx.comp_perm k _

omit [NeZero k] in
private theorem count_eq_card (x : Fin k → Color) (c : Color) :
    colourCount k x c = Fintype.card {i // x i = c} := by
  rw [Fintype.card_subtype]
  simp only [colourCount, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Equality of the three colour counts is exactly rearrangement of the word. -/
theorem exists_perm_of_counts (x y : Fin k → Color)
    (hcounts : ∀ c, colourCount k x c = colourCount k y c) :
    ∃ p : Equiv.Perm (Fin k), y = x ∘ p := by
  classical
  have hc : ∀ c, Fintype.card {i // y i = c} = Fintype.card {i // x i = c} := by
    intro c
    rw [← count_eq_card, ← count_eq_card]
    exact (hcounts c).symm
  let e := fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map e i).symm

theorem Step.full_target {x y : Fin k → Color} (h : Step k x y) (hx : Full k x) :
    Full k y := by
  obtain ⟨p, rfl⟩ := exists_perm_of_counts k x y (fun c => (h.colourCount k c).symm)
  exact hx.comp_perm k p

private theorem move_const (n : Nat) (x : Fin k → Color) :
    ExactRelationalTransfer (Move k) n x x := by
  induction n with
  | zero => exact .zero x
  | succ n ih => exact .succ (Or.inl rfl) ih

/-- A permutation has one fixed finite adjacent-swap program, for every word. -/
private def movePermutations : Submonoid (Equiv.Perm (Fin k)) where
  carrier := {p | ∃ n, ∀ x, ExactRelationalTransfer (Move k) n x (x ∘ p)}
  one_mem' := ⟨0, fun x => .zero x⟩
  mul_mem' := by
    rintro p q ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, fun x => (hn x).comp (hm (x ∘ p))⟩

private theorem all_movePermutations (p : Equiv.Perm (Fin k)) :
    p ∈ movePermutations k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  have hle : Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ movePermutations (n + 1) := by
    apply Submonoid.closure_le.mpr
    rintro p ⟨i, rfl⟩
    refine ⟨1, fun x => .succ ?_ (.zero _)⟩
    right
    refine ⟨i.castSucc, ?_⟩
    rw [swapAt_eq_comp_swap]
    have heq : i.castSucc + 1 = i.succ := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_castSucc, Fin.val_succ, Fin.val_one']
      have hn : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (by have := i.isLt; omega)
      rw [hn, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    rw [heq]
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
  exact hle (Submonoid.mem_top p)

/-- Idle moves pad every permutation program to any sufficiently large length.
The bound depends only on the circumference, not on a chosen count class. -/
theorem exists_move_threshold :
    ∃ N, ∀ (p : Equiv.Perm (Fin k)) (n : Nat), N ≤ n →
      ∀ x, ExactRelationalTransfer (Move k) n x (x ∘ p) := by
  classical
  have hprogram : ∀ p : Equiv.Perm (Fin k),
      ∃ n, ∀ x, ExactRelationalTransfer (Move k) n x (x ∘ p) := all_movePermutations k
  choose length hlength using hprogram
  let N := Finset.univ.sup length
  refine ⟨N, ?_⟩
  intro p n hn x
  have hp : length p ≤ N := Finset.le_sup (f := length) (Finset.mem_univ p)
  have h := (hlength p x).comp (move_const k (n - length p) (x ∘ p))
  simpa only [Nat.add_sub_of_le (hp.trans hn)] using h

/-- Every full word has a pair of unequal neighbours. -/
theorem Full.exists_neighbour {x : Fin k → Color} (hx : Full k x) :
    ∃ j, x j ≠ x (j + 1) := by
  by_contra hnone
  have heq : ∀ j, x (j + 1) = x j := by
    intro j
    by_contra h
    exact hnone ⟨j, fun he => h he.symm⟩
  have hc : ∀ m, x (Fin.ofNat k m) = x 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        have hcast : Fin.ofNat k (m + 1) = Fin.ofNat k m + 1 := by
          apply Fin.ext
          change (m + 1) % k = (m % k + 1 % k) % k
          exact Nat.add_mod m 1 k
        rw [hcast, heq, ih]
  obtain ⟨i, hi⟩ := hx.2 red red_ne_zero
  obtain ⟨j, hj⟩ := hx.2 blue blue_ne_zero
  have hci : x i = x 0 := by simpa using hc i.val
  have hcj : x j = x 0 := by simpa using hc j.val
  exact red_ne_blue (hi.symm.trans (hci.trans (hcj.symm.trans hj)))

theorem Full.exists_step (hk : 3 ≤ k) {x : Fin k → Color} (hx : Full k x) :
    ∃ y, Step k x y := by
  obtain ⟨j, hj⟩ := hx.exists_neighbour k
  obtain ⟨y, hy, _⟩ := two_ring_swap k hk x hx.1 j hj
    (hx.2 _ (add_ne_zero_of_ne hj))
  exact ⟨y, hy⟩

theorem Full.two_ring_shift (hk : 3 ≤ k) {x : Fin k → Color} (hx : Full k x) :
    ∃ y, Step k x y ∧ Step k y (shift k x) := by
  obtain ⟨y, hy⟩ := hx.exists_step k hk
  exact ⟨y, hy, hy.two_ring_shift k⟩

/-- Every elementary move is realized by two rings and one boundary shift. -/
theorem Move.two_rings (hk : 3 ≤ k) {x y : Fin k → Color}
    (h : Move k x y) (hx : Full k x) :
    ∃ z, Step k x z ∧ Step k z (shift k y) := by
  rcases h with rfl | ⟨j, rfl⟩
  · exact hx.two_ring_shift k hk
  · by_cases heq : x j = x (j + 1)
    · have hsame : swapAt k x j = x := by
        funext i
        by_cases hi : i = j
        · simp [swapAt, hi, heq]
        · by_cases hi' : i = j + 1 <;> simp [swapAt, hi, hi', heq]
      rw [hsame]
      exact hx.two_ring_shift k hk
    · exact two_ring_swap k hk x hx.1 j heq (hx.2 _ (add_ne_zero_of_ne heq))

/-- The boundary shift is a permutation of the whole word space. -/
def shiftEquiv : Equiv.Perm (Fin k → Color) where
  toFun := shift k
  invFun := fun x i => x (i - 1)
  left_inv := by intro x; funext i; simp [shift]
  right_inv := by intro x; funext i; simp [shift]

private theorem shiftEquiv_pow_succ (n : Nat) (x : Fin k → Color) :
    (shiftEquiv k ^ (n + 1)) x = shift k ((shiftEquiv k ^ n) x) := by
  rw [pow_succ', Equiv.Perm.mul_apply]
  rfl

theorem colourCount_shiftEquiv_pow (n : Nat) (x : Fin k → Color) (c : Color) :
    colourCount k ((shiftEquiv k ^ n) x) c = colourCount k x c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [shiftEquiv_pow_succ, colourCount_shift, ih]

private theorem transfer_shift {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) n x y) :
    ExactRelationalTransfer (Step k) n (shift k x) (shift k y) := by
  induction h with
  | zero => exact .zero _
  | succ hstep htail ih =>
      have hs : Step k (shift k _) (shift k _) := hstep.rotate_step k 1
      exact .succ hs ih

/-- Follow the moving boundary while realizing a whole adjacent-swap program. -/
theorem transfer_of_movePath (hk : 3 ≤ k) {n : Nat} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Move k) n x y) (hx : Full k x) :
    ExactRelationalTransfer (Step k) (2 * n) x ((shiftEquiv k ^ n) y) := by
  revert hx
  induction h with
  | zero => intro _; exact .zero _
  | @succ n x z y hmove htail ih =>
      intro hx
      obtain ⟨middle, hfirst, hsecond⟩ := hmove.two_rings k hk hx
      have hp : ExactRelationalTransfer (Step k) 2 x (shift k z) :=
        .succ hfirst (.succ hsecond (.zero _))
      have hrest := transfer_shift k (ih (hmove.full k hx))
      have hwhole := hp.comp hrest
      rw [← shiftEquiv_pow_succ] at hwhole
      convert hwhole using 1
      omega

/-- **Uniform tube ergodicity.** For each circumference there is a threshold
after which every word in a full three-colour count class reaches every other
word of the class in exactly the specified number of physical rings. -/
theorem tube_ergodicity (hk : 3 ≤ k) :
    ∃ R, ∀ (x y : Fin k → Color), Full k x →
      (∀ c, colourCount k x c = colourCount k y c) →
      ∀ r, R ≤ r → ExactRelationalTransfer (Step k) r x y := by
  classical
  obtain ⟨N, hN⟩ := exists_move_threshold k
  have heven : ∀ (x y : Fin k → Color), Full k x →
      (∀ c, colourCount k x c = colourCount k y c) →
      ∀ n, N ≤ n → ExactRelationalTransfer (Step k) (2 * n) x y := by
    intro x y hx hcounts n hn
    let z := (shiftEquiv k ^ n).symm y
    have hz : ∀ c, colourCount k x c = colourCount k z c := by
      intro c
      have he := colourCount_shiftEquiv_pow k n z c
      have hcancel : (shiftEquiv k ^ n) z = y := Equiv.apply_symm_apply _ y
      rw [hcancel] at he
      exact (hcounts c).trans he
    obtain ⟨p, hp⟩ := exists_perm_of_counts k x z hz
    have hm := hN p n hn x
    rw [← hp] at hm
    have hraw := transfer_of_movePath k hk hm hx
    simpa only [z, Equiv.apply_symm_apply] using hraw
  refine ⟨2 * N, ?_⟩
  intro x y hx hcounts r hr
  by_cases hparity : r % 2 = 0
  · have hlen : 2 * (r / 2) = r := by omega
    have hn : N ≤ r / 2 := by omega
    simpa only [hlen] using heven x y hx hcounts (r / 2) hn
  · have hlen : 1 + 2 * (r / 2) = r := by omega
    have hn : N ≤ r / 2 := by omega
    obtain ⟨w, hw⟩ := hx.exists_step k hk
    have hcounts' : ∀ c, colourCount k w c = colourCount k y c :=
      fun c => (hw.colourCount k c).trans (hcounts c)
    have ht := heven w y (hw.full_target k hx) hcounts' (r / 2) hn
    have hp : ExactRelationalTransfer (Step k) 1 x w := .succ hw (.zero w)
    simpa only [hlen] using hp.comp ht

/-- Connectivity within each full count class. -/
theorem same_counts_reachable (hk : 3 ≤ k) (x y : Fin k → Color) (hx : Full k x)
    (hcounts : ∀ c, colourCount k x c = colourCount k y c) :
    ∃ r, ExactRelationalTransfer (Step k) r x y := by
  obtain ⟨R, hR⟩ := tube_ergodicity k hk
  exact ⟨R, hR x y hx hcounts R le_rfl⟩

/-- Positive consecutive return lengths certify aperiodicity. -/
theorem consecutive_returns (hk : 3 ≤ k) (x : Fin k → Color) (hx : Full k x) :
    ∃ r, 0 < r ∧ ExactRelationalTransfer (Step k) r x x ∧
      ExactRelationalTransfer (Step k) (r + 1) x x := by
  obtain ⟨R, hR⟩ := tube_ergodicity k hk
  exact ⟨R + 1, by omega, hR x x hx (fun _ => rfl) (R + 1) (by omega),
    hR x x hx (fun _ => rfl) (R + 1 + 1) (by omega)⟩

end Mettapedia.GraphTheory.FourColor.ZigzagRing

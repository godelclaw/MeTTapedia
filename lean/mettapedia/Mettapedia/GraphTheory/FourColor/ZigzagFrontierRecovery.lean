import Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier
import Mettapedia.GraphTheory.FourColor.ZigzagRingTwoColour

/-!
# Recovery of boundary support after a split

Three-colour words are rearranged using uniform tube mixing. For words with
an absent colour, a cyclic rotation places unequal neighbours at the split,
and identity/shift rings rotate back with arbitrary sufficient padding.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

open ZigzagRing GoertzelV24CorridorPumping

variable (k : Nat) [NeZero k]

theorem Nonconstant.exists_neighbour {w : Fin k → Color} (hw : Nonconstant w) :
    ∃ j, w j ≠ w (j + 1) := by
  by_contra hnone
  have heq : ∀ j, w (j + 1) = w j := by
    intro j
    by_contra h
    exact hnone ⟨j, fun he => h he.symm⟩
  have hc : ∀ m, w (Fin.ofNat k m) = w 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      have hcast : Fin.ofNat k (m + 1) = Fin.ofNat k m + 1 := by
        apply Fin.ext
        change (m + 1) % k = (m % k + 1 % k) % k
        exact Nat.add_mod m 1 k
      rw [hcast, heq, ih]
  obtain ⟨i, j, hij⟩ := hw
  have hi : w i = w 0 := by simpa using hc i.val
  have hj : w j = w 0 := by simpa using hc j.val
  exact hij (hi.trans hj.symm)

private theorem shift_iterate (w : Fin k → Color) (m : Nat) :
    (shift k)^[m] w = rotate k w (Fin.ofNat k m) := by
  induction m with
  | zero => funext i; simp [rotate]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have hcast : Fin.ofNat k (m + 1) = Fin.ofNat k m + 1 := by
      apply Fin.ext
      change (m + 1) % k = (m % k + 1 % k) % k
      exact Nat.add_mod m 1 k
    rw [hcast]
    funext i
    change w ((i + 1) + Fin.ofNat k m) = w (i + (Fin.ofNat k m + 1))
    congr 1
    abel

private theorem missing_idle_path (w : Fin k → Color) (hnz : ∀ i, w i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hmiss : ∀ i, w i ≠ c) (m : Nat) :
    ExactRelationalTransfer (Step k) m w w := by
  induction m with
  | zero => exact .zero _
  | succ m ih => exact .succ ((step_iff_of_missing k w w hnz hc hmiss).mpr (Or.inl rfl)) ih

private theorem missing_shift_path (m : Nat) (w : Fin k → Color)
    (hnz : ∀ i, w i ≠ 0) {c : Color} (hc : c ≠ 0) (hmiss : ∀ i, w i ≠ c) :
    ExactRelationalTransfer (Step k) m w ((shift k)^[m] w) := by
  induction m generalizing w with
  | zero => exact .zero _
  | succ m ih =>
    have hstep := (step_iff_of_missing k w (shift k w) hnz hc hmiss).mpr (Or.inr rfl)
    have htail := ih (shift k w) (fun i => hnz (i + 1)) (fun i => hmiss (i + 1))
    simpa only [Function.iterate_succ_apply] using ExactRelationalTransfer.succ hstep htail

/-- Every rotation of a word with a missing colour rotates back in any
specified number of rings at least `k - 1`. -/
theorem rotation_returns (w : Fin k → Color) (hnz : ∀ i, w i ≠ 0)
    {c : Color} (hc : c ≠ 0) (hmiss : ∀ i, w i ≠ c)
    (j : Fin k) (r : Nat) (hr : k - 1 ≤ r) :
    ExactRelationalTransfer (Step k) r (rotate k w j) w := by
  let m := (-j).val
  have hm : m ≤ r := by have := (-j).isLt; dsimp [m]; omega
  have hpath := missing_shift_path k m (rotate k w j)
    (fun i => hnz (i + j)) hc (fun i => hmiss (i + j))
  have hend : (shift k)^[m] (rotate k w j) = w := by
    rw [shift_iterate]
    funext i
    simp [rotate, m, add_assoc]
  rw [hend] at hpath
  have hpad := missing_idle_path k w hnz hc hmiss (r - m)
  simpa only [Nat.add_sub_of_le hm] using hpath.comp hpad

/-- A rotation places an unequal pair at the first two ports. Contracting
the pair creates the absent colour, so the predecessor is nonconstant. -/
theorem missing_contract_seed {n : Nat} (hn : 2 ≤ n) (w : Fin (n + 2) → Color)
    (hw : Required w) {c : Color} (hc : c ≠ 0) (hmiss : ∀ i, w i ≠ c) :
    ∃ j : Fin (n + 2), (rotate (n + 2) w j) 0 ≠ (rotate (n + 2) w j) 1 ∧
      Required (contract n (rotate (n + 2) w j)) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨j, hj⟩ := hw.2.exists_neighbour (n + 2)
  let z := rotate (n + 2) w j
  have hnz : ∀ i, z i ≠ 0 := fun i => hw.1.1 (i + j)
  have hzmiss : ∀ i, z i ≠ c := fun i => hmiss (i + j)
  have hne : z 0 ≠ z 1 := by simpa [z, rotate, add_comm] using hj
  have hza : Admissible z := hw.1.comp_perm (Equiv.addRight j)
  have hsum : z 0 + z 1 = c :=
    (third_eq_add (hnz 0) (hnz 1) hc hne (hzmiss 0) (hzmiss 1)).symm
  refine ⟨j, hne, contract_admissible hza hne, ⟨0, (0 : Fin n).succ, ?_⟩⟩
  change z 0 + z 1 ≠ z (0 : Fin n).succ.succ
  rw [hsum]
  exact (hzmiss _).symm

omit [NeZero k] in
/-- After a split, one uniform ring threshold restores every required word.
The precursor supplied here is suitable for the literal cubic-vertex rule. -/
theorem split_recovery (n : Nat) (hn : 2 ≤ n) :
    ∃ R, ∀ r, R ≤ r → ∀ y : Fin (n + 2) → Color, Required y →
      ∃ z : Fin (n + 2) → Color, Admissible z ∧ Required (contract n z) ∧
        z 0 ≠ z 1 ∧ ExactRelationalTransfer (Step (n + 2)) r z y := by
  obtain ⟨R, hR⟩ := tube_ergodicity (n + 2) (by omega)
  refine ⟨max R (n + 1), ?_⟩
  intro r hr y hy
  by_cases hfull : Full (n + 2) y
  · obtain ⟨p, hne, hrequired⟩ := full_contract_seed hn y hy.1 hfull
    exact ⟨y ∘ p, hy.1.comp_perm p, hrequired, hne, hR _ _ (hfull.comp_perm (n + 2) p)
      (colourCount_comp_perm (n + 2) y p) r (le_trans (le_max_left _ _) hr)⟩
  · have hmissing : ∃ c : Color, c ≠ 0 ∧ ∀ i, y i ≠ c := by
      classical
      by_contra hnone
      apply hfull
      refine ⟨hy.1.1, ?_⟩
      intro c hc
      by_contra hocc
      apply hnone
      refine ⟨c, hc, ?_⟩
      intro i hi
      exact hocc ⟨i, hi⟩
    obtain ⟨c, hc, hmiss⟩ := hmissing
    obtain ⟨j, hne, hrequired⟩ := missing_contract_seed hn y hy hc hmiss
    refine ⟨rotate (n + 2) y j, hy.1.comp_perm (Equiv.addRight j), hrequired, hne, ?_⟩
    exact rotation_returns (n + 2) y hy.1.1 hc hmiss j r (by omega)

end Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

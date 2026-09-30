import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mathlib.Data.Finset.Max

/-!
# An adjacent pair in a noncrossing perfect matching

A shortest displayed chord has no port strictly between its endpoints.
Otherwise the mate of an interior port lies inside that chord and gives a
shorter one. This supplies an adjacent component at every boundary width,
without a table of matchings.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

variable {n : ℕ} [NeZero n]

/-- Every fixed-point-free noncrossing involution has a pair of consecutive
ports in the displayed order. -/
theorem exists_adjacent (mate : Fin n → Fin n)
    (hinv : ∀ i, mate (mate i) = i)
    (hfree : ∀ i, mate i ≠ i) (hplanar : IsNoncrossingMatching mate) :
    ∃ i, (mate i).val = i.val + 1 := by
  classical
  let chords := Finset.univ.filter (fun i : Fin n => i < mate i)
  have hzero : (0 : Fin n) < mate 0 := by
    have hne := hfree 0
    have hv : (mate 0).val ≠ 0 := by
      intro h
      apply hne
      exact Fin.ext h
    change 0 < (mate 0).val
    omega
  have hnonempty : chords.Nonempty := ⟨0, by simp [chords, hzero]⟩
  obtain ⟨a, ha, hminimal⟩ := chords.exists_min_image
    (fun i => (mate i).val - i.val) hnonempty
  have hab : a < mate a := (Finset.mem_filter.mp ha).2
  by_cases hadj : (mate a).val = a.val + 1
  · exact ⟨a, hadj⟩
  have hgap : a.val + 1 < (mate a).val := by
    have := hab
    change a.val < (mate a).val at this
    omega
  let c : Fin n := ⟨a.val + 1, by have := (mate a).isLt; omega⟩
  have hac : a < c := by change a.val < a.val + 1; omega
  have hcb : c < mate a := hgap
  have hda : mate c ≠ a := by
    intro h
    have he := congrArg mate h
    rw [hinv] at he
    exact (ne_of_lt hcb) he
  have hdb : mate c ≠ mate a := by
    intro h
    have he := congrArg mate h
    rw [hinv, hinv] at he
    exact (ne_of_gt hac) he
  have hdav : (mate c).val ≠ a.val := fun h => hda (Fin.ext h)
  have hdbv : (mate c).val ≠ (mate a).val := fun h => hdb (Fin.ext h)
  have hcross := hplanar a c
  have hinside : a < mate c ∧ mate c < mate a := by
    change a.val < (mate c).val ∧ (mate c).val < (mate a).val
    have hav : a.val < c.val := hac
    have hb : c.val < (mate a).val := hcb
    unfold ChordsCross at hcross
    change a.val < (mate a).val at hab
    rw [Nat.min_eq_left (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt hab)] at hcross
    by_cases hdc : (mate c).val < c.val
    · rw [Nat.min_eq_right (Nat.le_of_lt hdc), Nat.max_eq_left (Nat.le_of_lt hdc)] at hcross
      omega
    · rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)] at hcross
      omega
  by_cases hcd : c < mate c
  · have hmem : c ∈ chords := by simp [chords, hcd]
    have hm := hminimal c hmem
    have hd := hinside.2
    change (mate c).val < (mate a).val at hd
    change a.val < (mate a).val at hab
    change a.val < c.val at hac
    omega
  · have hdc : mate c < c := lt_of_le_of_ne (le_of_not_gt hcd) (hfree c)
    have hmem : mate c ∈ chords := by simp [chords, hinv, hdc]
    have hm := hminimal (mate c) hmem
    rw [hinv] at hm
    have hd := hinside.1
    change a.val < (mate c).val at hd
    change c.val < (mate a).val at hcb
    change a.val < (mate a).val at hab
    omega

end Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

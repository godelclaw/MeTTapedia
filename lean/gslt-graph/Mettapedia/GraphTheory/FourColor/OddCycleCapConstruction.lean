import Mettapedia.GraphTheory.FourColor.CycleCapTangle
import Mettapedia.GraphTheory.FourColor.ZigzagRingErgodicity

/-!
# Constructing odd cycle caps with prescribed colour counts

Walk around the triangle of nonzero colours along three alternating arcs.
Odd arc lengths close the walk, and their lengths are exactly the three
spoke-colour multiplicities. Thus a cycle cap meets every odd count class,
at every circumference, without enumeration of boundary words.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleCap

open ZigzagRing
open scoped BigOperators

private def alternating (a b : Color) (i : Nat) : Color :=
  if i % 2 = 0 then a else b

private theorem alternating_add (a b : Color) (i : Nat) :
    alternating a b i + alternating a b (i + 1) = a + b := by
  unfold alternating
  split_ifs <;> first | omega | rfl | exact add_comm _ _

private theorem alternating_ne (a b : Color) (hab : a ≠ b) (i : Nat) :
    alternating a b i ≠ alternating a b (i + 1) := by
  unfold alternating
  split_ifs <;> first | omega | exact hab | exact hab.symm

private def arcEdges (m n i : Nat) : Color :=
  if i < m then alternating red blue i
  else if i < m + n then alternating blue purple (i - m)
  else alternating purple red (i - (m + n))

private def arcSpokes (m n i : Nat) : Color :=
  if i < m then purple else if i < m + n then red else blue

private theorem arcEdges_first {m n : Nat} (hm : Odd m) (hn : 0 < n)
    {i : Nat} (hi : i ≤ m) : arcEdges m n i = alternating red blue i := by
  by_cases hlt : i < m
  · simp [arcEdges, hlt]
  · have heq : i = m := by omega
    subst i
    obtain ⟨t, rfl⟩ := hm
    simp [arcEdges, alternating, show 2 * t + 1 < 2 * t + 1 + n by omega]

private theorem arcEdges_second {m n : Nat} (hn : Odd n)
    {i : Nat} (hlo : m ≤ i) (hhi : i ≤ m + n) :
    arcEdges m n i = alternating blue purple (i - m) := by
  by_cases hlt : i < m + n
  · simp [arcEdges, show ¬i < m by omega, hlt]
  · have heq : i = m + n := by omega
    subst i
    obtain ⟨t, rfl⟩ := hn
    simp [arcEdges, alternating]

private theorem arcEdges_third {m n i : Nat} (hi : m + n ≤ i) :
    arcEdges m n i = alternating purple red (i - (m + n)) := by
  simp [arcEdges, show ¬i < m by omega, show ¬i < m + n by omega]

private theorem arcEdges_ne_zero (m n i : Nat) : arcEdges m n i ≠ 0 := by
  unfold arcEdges alternating
  split_ifs <;> simp

private theorem arcEdges_step {m n : Nat} (hm : Odd m) (hn : Odd n) (i : Nat) :
    arcEdges m n i ≠ arcEdges m n (i + 1) ∧
      arcEdges m n i + arcEdges m n (i + 1) = arcSpokes m n i := by
  have hnpos : 0 < n := by obtain ⟨t, rfl⟩ := hn; omega
  by_cases hfirst : i < m
  · rw [arcEdges_first hm hnpos (by omega), arcEdges_first hm hnpos (by omega)]
    exact ⟨alternating_ne _ _ red_ne_blue i,
      by simpa [arcSpokes, hfirst] using alternating_add red blue i⟩
  · by_cases hsecond : i < m + n
    · rw [arcEdges_second hn (by omega) (by omega),
        arcEdges_second hn (by omega) (by omega)]
      have hsub : i + 1 - m = (i - m) + 1 := by omega
      rw [hsub]
      exact ⟨alternating_ne _ _ blue_ne_purple _,
        by simpa [arcSpokes, hfirst, hsecond] using alternating_add blue purple (i - m)⟩
    · rw [arcEdges_third (by omega), arcEdges_third (by omega)]
      have hsub : i + 1 - (m + n) = (i - (m + n)) + 1 := by omega
      rw [hsub]
      exact ⟨alternating_ne _ _ red_ne_purple.symm _,
        by simpa [arcSpokes, hfirst, hsecond] using
          alternating_add purple red (i - (m + n))⟩

private theorem arcEdges_close {m n p : Nat} (hm : Odd m) (hp : Odd p) :
    arcEdges m n (m + n + p) = arcEdges m n 0 := by
  have hmpos : 0 < m := by obtain ⟨t, rfl⟩ := hm; omega
  rw [arcEdges_third (by omega)]
  obtain ⟨t, rfl⟩ := hp
  simp [arcEdges, alternating, hmpos]

/-- Three alternating arcs with the given odd lengths form a proper cycle. -/
theorem exists_cap_of_odd_counts (k : Nat) [NeZero k] (m n p : Nat)
    (hsize : m + n + p = k) (hm : Odd m) (hn : Odd n) (hp : Odd p) :
    ∃ a : Fin k → Color, Valid k a ∧
      ∀ c, colourCount k (spokes k a) c =
        m * (if purple = c then 1 else 0) + n * (if red = c then 1 else 0) +
          p * (if blue = c then 1 else 0) := by
  subst k
  have hmpos : 0 < m := by obtain ⟨t, rfl⟩ := hm; omega
  have hnpos : 0 < n := by obtain ⟨t, rfl⟩ := hn; omega
  have hppos : 0 < p := by obtain ⟨t, rfl⟩ := hp; omega
  let a : Fin (m + n + p) → Color := fun i => arcEdges m n i.val
  have hnext (i : Fin (m + n + p)) : a (i + 1) = arcEdges m n (i.val + 1) := by
    change arcEdges m n (i + 1).val = _
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m + n + p by omega)]
    by_cases hlt : i.val + 1 < m + n + p
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : i.val + 1 = m + n + p := by have := i.isLt; omega
      rw [heq, Nat.mod_self]
      exact (arcEdges_close hm hp).symm
  have hspokes : spokes (m + n + p) a = fun i => arcSpokes m n i.val := by
    funext i
    rw [spokes, hnext]
    exact (arcEdges_step hm hn i.val).2
  refine ⟨a, ⟨fun i => arcEdges_ne_zero _ _ _, ?_⟩, ?_⟩
  · intro i
    rw [hnext]
    exact (arcEdges_step hm hn i.val).1
  · intro c
    rw [hspokes, colourCount, Fin.sum_univ_add, Fin.sum_univ_add]
    have hfirst : (∑ i : Fin m,
        if arcSpokes m n ((i.castAdd n).castAdd p).val = c then 1 else 0) =
        m * (if purple = c then 1 else 0) := by
      simp only [Fin.val_castAdd]
      simp_rw [show ∀ i : Fin m, arcSpokes m n i.val = purple from
        fun i => by simp [arcSpokes, i.isLt]]
      simp
    have hsecond : (∑ i : Fin n,
        if arcSpokes m n ((i.natAdd m).castAdd p).val = c then 1 else 0) =
        n * (if red = c then 1 else 0) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      simp_rw [show ∀ i : Fin n, arcSpokes m n (m + i.val) = red from
        fun i => by simp [arcSpokes, show ¬m + i.val < m by omega,
          show m + i.val < m + n by have := i.isLt; omega]]
      simp
    have hthird : (∑ i : Fin p,
        if arcSpokes m n (i.natAdd (m + n)).val = c then 1 else 0) =
        p * (if blue = c then 1 else 0) := by
      simp only [Fin.val_natAdd]
      simp_rw [show ∀ i : Fin p, arcSpokes m n (m + n + i.val) = blue from
        fun i => by simp [arcSpokes, show ¬m + n + i.val < m by omega]]
      simp
    rw [hfirst, hsecond, hthird]

/-- The three multiplicities account for every letter of a nonzero word. -/
theorem colourCount_sum (k : Nat) (w : Fin k → Color) (hnz : ∀ i, w i ≠ 0) :
    colourCount k w purple + colourCount k w red + colourCount k w blue = k := by
  simp only [colourCount, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin k, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero (w i) (hnz i) with h | h | h <;>
        simp [h, red, blue, purple]
    _ = k := by simp

/-- On an odd boundary, each nonzero colour has an odd multiplicity. -/
def OddCounts (k : Nat) (w : Fin k → Color) : Prop :=
  ∀ c : Color, c ≠ 0 → Odd (colourCount k w c)

private theorem word_sum_eq_counts (k : Nat) (w : Fin k → Color) :
    (∑ i, w i) = colourCount k w purple • purple +
      colourCount k w red • red + colourCount k w blue • blue := by
  simp only [colourCount, ← Finset.sum_nsmul_assoc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple (w i) with h | h | h | h <;>
    simp [h, red, blue, purple]
  decide

/-- Cut parity on an odd boundary forces all three multiplicities to be odd. -/
theorem oddCounts_of_sum_eq_zero (k : Nat) (hk : Odd k) (w : Fin k → Color)
    (hnz : ∀ i, w i ≠ 0) (hsum : ∑ i, w i = 0) : OddCounts k w := by
  have hword := word_sum_eq_counts k w
  rw [hsum] at hword
  have hred : (colourCount k w purple : F2) + (colourCount k w red : F2) = 0 := by
    have h := congrArg Prod.fst hword.symm
    simpa [purple, red, blue, nsmul_eq_mul] using h
  have hblue : (colourCount k w purple : F2) + (colourCount k w blue : F2) = 0 := by
    have h := congrArg Prod.snd hword.symm
    simpa [purple, red, blue, nsmul_eq_mul] using h
  have hrp : (colourCount k w red : F2) = (colourCount k w purple : F2) := by
    apply add_left_cancel (a := (colourCount k w purple : F2))
    rw [hred, zmod2_add_self]
  have hbp : (colourCount k w blue : F2) = (colourCount k w purple : F2) := by
    apply add_left_cancel (a := (colourCount k w purple : F2))
    rw [hblue, zmod2_add_self]
  have htotal : ((colourCount k w purple + colourCount k w red +
      colourCount k w blue : Nat) : F2) = 1 := by
    rw [colourCount_sum k w hnz]
    exact hk.natCast_zmod_two
  simp only [Nat.cast_add, hrp, hbp, zmod2_add_self, zero_add] at htotal
  intro c hc
  apply ZMod.natCast_eq_one_iff_odd.mp
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl
  · exact hrp.trans htotal
  · exact hbp.trans htotal
  · exact htotal

theorem full_of_oddCounts (k : Nat) (w : Fin k → Color)
    (hnz : ∀ i, w i ≠ 0) (hodd : OddCounts k w) : Full k w := by
  refine ⟨hnz, ?_⟩
  intro c hc
  by_contra hnone
  push Not at hnone
  have hzero : colourCount k w c = 0 := by simp [colourCount, hnone]
  have h := hodd c hc
  rw [hzero] at h
  obtain ⟨n, hn⟩ := h
  omega

/-- A literal cycle cap realizes a representative of every odd count class. -/
theorem cap_meets_odd_count_class (k : Nat) [NeZero k] (hk : 2 ≤ k)
    (w : Fin k → Color) (hnz : ∀ i, w i ≠ 0) (hodd : OddCounts k w) :
    ∃ x, (cap k hk).AcceptsBoundaryWords Empty.elim x ∧
      ∀ c, colourCount k x c = colourCount k w c := by
  obtain ⟨a, ha, hcounts⟩ := exists_cap_of_odd_counts k
    (colourCount k w purple) (colourCount k w red) (colourCount k w blue)
    (colourCount_sum k w hnz) (hodd purple purple_ne_zero)
    (hodd red red_ne_zero) (hodd blue blue_ne_zero)
  refine ⟨spokes k a, accepts_spokes k hk ha, ?_⟩
  intro c
  rw [hcounts]
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple c with rfl | rfl | rfl | rfl
  · simp [colourCount, hnz]
  all_goals simp [red, blue, purple]

end Mettapedia.GraphTheory.FourColor.CycleCap

import Mettapedia.GraphTheory.FourColor.KempeCertificate

/-!
# Enumerating noncrossing matchings, completely

`enumPairs` lists the noncrossing perfect matchings of a sorted list of ports:
the first port is matched to each port at even distance, the ports between
are matched among themselves, the rest after.  `complete`: every involution
that is fixed-point-free on the ports, closed on them, and noncrossing, agrees
on the ports with some listed matching.  This lets a checker quantify over the
listed matchings instead of all port maps.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation

open Compositional.CyclicBoundaryMatching

variable {n : Nat}

/-- noncrossing matchings of a sorted port list, as pair lists; `f` is fuel -/
def enumPairs : Nat → List (Fin n) → List (List (Fin n × Fin n))
  | _, [] => [[]]
  | 0, _ :: _ => []
  | f + 1, a :: rest =>
    (List.range rest.length).flatMap fun m =>
      if m % 2 = 0 then
        match rest[m]? with
        | some b => (enumPairs f (rest.take m)).flatMap fun inside =>
            (enumPairs f (rest.drop (m + 1))).map fun outside => (a, b) :: (inside ++ outside)
        | none => []
      else []

/-- the mate function of a pair list -/
def mateOf (pairs : List (Fin n × Fin n)) (i : Fin n) : Fin n :=
  match pairs.find? (fun p => decide (p.1 = i ∨ p.2 = i)) with
  | some p => if p.1 = i then p.2 else p.1
  | none => i

theorem mateOf_nil (i : Fin n) : mateOf [] i = i := rfl

theorem mateOf_cons_of_ne (p : Fin n × Fin n) (pairs : List (Fin n × Fin n)) (i : Fin n)
    (h1 : p.1 ≠ i) (h2 : p.2 ≠ i) : mateOf (p :: pairs) i = mateOf pairs i := by
  unfold mateOf
  simp [List.find?_cons, h1, h2]

theorem mateOf_cons_fst (p : Fin n × Fin n) (pairs : List (Fin n × Fin n)) :
    mateOf (p :: pairs) p.1 = p.2 := by
  unfold mateOf; simp [List.find?_cons]

theorem mateOf_cons_snd (p : Fin n × Fin n) (pairs : List (Fin n × Fin n)) (h : p.1 ≠ p.2) :
    mateOf (p :: pairs) p.2 = p.1 := by
  unfold mateOf; simp [List.find?_cons, h]

/-- if no pair of the first list mentions `i`, the mate is read in the second list -/
theorem mateOf_append_of_forall (pairs pairs' : List (Fin n × Fin n)) (i : Fin n)
    (h : ∀ p ∈ pairs, p.1 ≠ i ∧ p.2 ≠ i) : mateOf (pairs ++ pairs') i = mateOf pairs' i := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    rw [List.cons_append, mateOf_cons_of_ne p _ i (h p (List.mem_cons_self)).1
      (h p (List.mem_cons_self)).2]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- if the first list has a pair mentioning `i`, the mate is read there -/
theorem mateOf_append_of_ne (pairs pairs' : List (Fin n × Fin n)) (i : Fin n)
    (h : mateOf pairs i ≠ i) : mateOf (pairs ++ pairs') i = mateOf pairs i := by
  induction pairs with
  | nil => exact absurd rfl h
  | cons p ps ih =>
    by_cases h1 : p.1 = i
    · subst h1; rw [List.cons_append, mateOf_cons_fst, mateOf_cons_fst]
    · by_cases h2 : p.2 = i
      · subst h2
        have hne : p.1 ≠ p.2 := h1
        rw [List.cons_append, mateOf_cons_snd _ _ hne, mateOf_cons_snd _ _ hne]
      · rw [List.cons_append, mateOf_cons_of_ne p _ i h1 h2, mateOf_cons_of_ne p _ i h1 h2]
        rw [mateOf_cons_of_ne p _ i h1 h2] at h
        exact ih h

/-- every pair of a listed matching lies in the port list -/
theorem mem_of_mem_enumPairs : ∀ (f : Nat) (pts : List (Fin n)) (pairs : List (Fin n × Fin n)),
    pairs ∈ enumPairs f pts → ∀ p ∈ pairs, p.1 ∈ pts ∧ p.2 ∈ pts
  | _, [], pairs, h => by
    simp [enumPairs] at h; subst h; simp
  | 0, _ :: _, _, h => by simp [enumPairs] at h
  | f + 1, a :: rest, pairs, h => by
    simp only [enumPairs, List.mem_flatMap, List.mem_range] at h
    obtain ⟨m, hm, hmem⟩ := h
    split_ifs at hmem with heven
    · split at hmem
      · rename_i b hb
        simp only [List.mem_flatMap, List.mem_map] at hmem
        obtain ⟨inside, hin, outside, hout, rfl⟩ := hmem
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_of_getElem? hb)⟩
        · rcases List.mem_append.mp hp with hp | hp
          · have := mem_of_mem_enumPairs f _ inside hin p hp
            exact ⟨List.mem_cons_of_mem _ (List.mem_of_mem_take this.1),
              List.mem_cons_of_mem _ (List.mem_of_mem_take this.2)⟩
          · have := mem_of_mem_enumPairs f _ outside hout p hp
            exact ⟨List.mem_cons_of_mem _ (List.mem_of_mem_drop this.1),
              List.mem_cons_of_mem _ (List.mem_of_mem_drop this.2)⟩
      · simp at hmem
    · simp at hmem

/-! ## Completeness -/

/-- a finite set closed under a fixed-point-free involution has even cardinality -/
theorem even_card_of_involution (g : Fin n → Fin n) (hinv : ∀ x, g (g x) = x) :
    ∀ (S : Finset (Fin n)), (∀ x ∈ S, g x ∈ S) → (∀ x ∈ S, g x ≠ x) → Even S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hclosed hfpf
    rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · let S' := (S.erase x).erase (g x)
      have hgx : g x ∈ S := hclosed x hx
      have hne : g x ≠ x := hfpf x hx
      have hsub : S' ⊂ S := by
        refine Finset.ssubset_of_subset_of_ssubset ?_ (Finset.erase_ssubset hx)
        exact Finset.erase_subset _ _
      have hcard : S'.card + 2 = S.card := by
        have h1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
        have h2 : S'.card + 1 = (S.erase x).card :=
          Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hne, hgx⟩)
        omega
      have hS' : Even S'.card := by
        refine ih S' hsub ?_ ?_
        · intro y hy
          simp only [S', Finset.mem_erase] at hy ⊢
          refine ⟨?_, ?_, hclosed y hy.2.2⟩
          · intro h
            apply hy.2.1
            calc y = g (g y) := (hinv y).symm
              _ = g (g x) := by rw [h]
              _ = x := hinv x
          · intro h
            apply hy.1
            calc y = g (g y) := (hinv y).symm
              _ = g x := by rw [h]
        · intro y hy
          exact hfpf y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
      rw [← hcard]
      exact hS'.add (by decide)

theorem cross_of_between {mate : Fin n → Fin n} (hnc : IsNoncrossingMatching mate)
    {a b i : Fin n} (hab : mate a = b) (h1 : a < i) (h2 : i < b) : ¬ b < mate i := by
  intro h3
  apply hnc a i
  rw [hab]
  have h1' : a.val < i.val := h1
  have h2' : i.val < b.val := h2
  have h3' : b.val < (mate i).val := h3
  unfold Compositional.CyclicBoundaryMatching.ChordsCross
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

theorem cross_of_outside {mate : Fin n → Fin n} (hnc : IsNoncrossingMatching mate)
    {a b i : Fin n} (hab : mate a = b) (h1 : a < mate i) (h2 : mate i < b) : ¬ b < i := by
  intro h3
  apply hnc a i
  rw [hab]
  have h1' : a.val < (mate i).val := h1
  have h2' : (mate i).val < b.val := h2
  have h3' : b.val < i.val := h3
  unfold Compositional.CyclicBoundaryMatching.ChordsCross
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

/-- **completeness**: every noncrossing fixed-point-free involution closed on a sorted port
list agrees on the ports with a listed matching -/
theorem complete : ∀ (f : Nat) (pts : List (Fin n)), pts.length ≤ f →
    pts.Pairwise (· < ·) → ∀ (mate : Fin n → Fin n), (∀ i, mate (mate i) = i) →
    (∀ i ∈ pts, mate i ∈ pts ∧ mate i ≠ i) → IsNoncrossingMatching mate →
    ∃ pairs ∈ enumPairs f pts, ∀ i ∈ pts, mateOf pairs i = mate i
  | _, [], _, _, mate, _, _, _ => ⟨[], by simp [enumPairs], by simp⟩
  | 0, _ :: _, hlen, _, _, _, _, _ => by simp at hlen
  | f + 1, a :: rest, hlen, hsorted, mate, hinv, hperf, hnc => by
    have hlen' : rest.length ≤ f := by simpa using hlen
    obtain ⟨hlt, hrest⟩ := List.pairwise_cons.mp hsorted
    obtain ⟨hbmem, hba⟩ := hperf a List.mem_cons_self
    set b := mate a with hb
    have hb_rest : b ∈ rest := by
      rcases List.mem_cons.mp hbmem with h | h
      · exact absurd h hba
      · exact h
    obtain ⟨m, hm, hbm⟩ := List.getElem_of_mem hb_rest
    have hsplit : rest = rest.take m ++ b :: rest.drop (m + 1) := by
      conv_lhs => rw [← List.take_append_drop m rest]
      rw [List.drop_eq_getElem_cons hm, hbm]
    have hpw := hsplit ▸ hrest
    rw [List.pairwise_append, List.pairwise_cons] at hpw
    obtain ⟨hin_sorted, ⟨hb_out, hout_sorted⟩, hcross⟩ := hpw
    have hin_lt : ∀ x ∈ rest.take m, a < x ∧ x < b := fun x hx =>
      ⟨hlt x (List.mem_of_mem_take hx), hcross x hx b List.mem_cons_self⟩
    have hout_gt : ∀ x ∈ rest.drop (m + 1), b < x := hb_out
    have ha_lt_b : a < b := hlt b hb_rest
    have hmem_split : ∀ x ∈ rest, x = b ∨ x ∈ rest.take m ∨ x ∈ rest.drop (m + 1) := by
      intro x hx
      rw [hsplit] at hx
      rcases List.mem_append.mp hx with h | h
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    -- the inside is closed under the mate
    have hin_closed : ∀ x ∈ rest.take m, mate x ∈ rest.take m ∧ mate x ≠ x := by
      intro x hx
      have hxr := List.mem_of_mem_take hx
      obtain ⟨hmx, hne⟩ := hperf x (List.mem_cons_of_mem _ hxr)
      refine ⟨?_, hne⟩
      have hxb : x ≠ b := ne_of_lt (hin_lt x hx).2
      have hmx_ne_a : mate x ≠ a := fun h => hxb (by rw [← hinv x, h])
      have hmx_ne_b : mate x ≠ b := fun h => by
        have : x = a := by rw [← hinv x, h, hb, hinv]
        exact (ne_of_lt (hin_lt x hx).1) this.symm
      rcases List.mem_cons.mp hmx with h | h
      · exact absurd h hmx_ne_a
      · rcases hmem_split _ h with h | h | h
        · exact absurd h hmx_ne_b
        · exact h
        · exact absurd (hout_gt _ h) (cross_of_between hnc hb.symm (hin_lt x hx).1 (hin_lt x hx).2)
    have hout_closed : ∀ x ∈ rest.drop (m + 1), mate x ∈ rest.drop (m + 1) ∧ mate x ≠ x := by
      intro x hx
      have hxr := List.mem_of_mem_drop hx
      obtain ⟨hmx, hne⟩ := hperf x (List.mem_cons_of_mem _ hxr)
      refine ⟨?_, hne⟩
      have hxb : x ≠ b := ne_of_gt (hout_gt x hx)
      have hmx_ne_a : mate x ≠ a := fun h => hxb (by rw [← hinv x, h])
      have hmx_ne_b : mate x ≠ b := fun h => by
        have : x = a := by rw [← hinv x, h, hb, hinv]
        exact (ne_of_gt (ha_lt_b.trans (hout_gt x hx))) this
      rcases List.mem_cons.mp hmx with h | h
      · exact absurd h hmx_ne_a
      · rcases hmem_split _ h with h | h | h
        · exact absurd h hmx_ne_b
        · exact absurd (hout_gt x hx)
            (cross_of_outside hnc hb.symm (hin_lt _ h).1 (hin_lt _ h).2)
        · exact h
    -- the inside has even length
    have hin_nodup : (rest.take m).Nodup := hin_sorted.imp ne_of_lt
    have heven : m % 2 = 0 := by
      have hcard : (rest.take m).toFinset.card = m := by
        rw [List.toFinset_card_of_nodup hin_nodup, List.length_take]; omega
      have := even_card_of_involution mate hinv (rest.take m).toFinset
        (fun x hx => List.mem_toFinset.mpr (hin_closed x (List.mem_toFinset.mp hx)).1)
        (fun x hx => (hin_closed x (List.mem_toFinset.mp hx)).2)
      rw [hcard] at this
      exact Nat.even_iff.mp this
    obtain ⟨pin, hpin, hpin_agree⟩ := complete f (rest.take m)
      (by rw [List.length_take]; omega) hin_sorted mate hinv hin_closed hnc
    obtain ⟨pout, hpout, hpout_agree⟩ := complete f (rest.drop (m + 1))
      (by rw [List.length_drop]; omega) hout_sorted mate hinv hout_closed hnc
    refine ⟨(a, b) :: (pin ++ pout), ?_, ?_⟩
    · simp only [enumPairs, List.mem_flatMap, List.mem_range]
      refine ⟨m, hm, ?_⟩
      rw [if_pos heven, List.getElem?_eq_getElem hm, hbm]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨pin, hpin, pout, hpout, rfl⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact mateOf_cons_fst (i, b) _
      · rcases hmem_split i hi with rfl | hi | hi
        · show mateOf ((a, b) :: (pin ++ pout)) (a, b).2 = mate (a, b).2
          rw [mateOf_cons_snd (a, b) _ (ne_of_lt ha_lt_b)]
          show a = mate b
          rw [hb, hinv]
        · have h1 : (a, b).1 ≠ i := ne_of_lt (hin_lt i hi).1
          have h2 : (a, b).2 ≠ i := ne_of_gt (hin_lt i hi).2
          rw [mateOf_cons_of_ne _ _ i h1 h2, mateOf_append_of_ne]
          · exact hpin_agree i hi
          · rw [hpin_agree i hi]; exact (hin_closed i hi).2
        · have h1 : (a, b).1 ≠ i := ne_of_lt (ha_lt_b.trans (hout_gt i hi))
          have h2 : (a, b).2 ≠ i := ne_of_lt (hout_gt i hi)
          rw [mateOf_cons_of_ne _ _ i h1 h2, mateOf_append_of_forall]
          · exact hpout_agree i hi
          · intro p hp
            have hp' := mem_of_mem_enumPairs f _ pin hpin p hp
            exact ⟨ne_of_lt ((hin_lt _ hp'.1).2.trans (hout_gt i hi)),
              ne_of_lt ((hin_lt _ hp'.2).2.trans (hout_gt i hi))⟩

end KempeDerivation
end Mettapedia.GraphTheory.FourColor

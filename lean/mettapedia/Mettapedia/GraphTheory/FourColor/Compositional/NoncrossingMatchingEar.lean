import Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

/-!
# An adjacent pair in a noncrossing perfect matching

A shortest displayed chord has no port strictly between its endpoints.
Otherwise the mate of an interior port lies inside that chord and gives a
shorter one. This supplies an adjacent component at every boundary width,
without a table of matchings.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

variable {n : ℕ}

/-- Any chord whose endpoints lie in a convex block contains an adjacent
matched pair in that same block. -/
theorem exists_adjacent_within (mate : Fin n → Fin n)
    (hinv : ∀ i, mate (mate i) = i)
    (hfree : ∀ i, mate i ≠ i) (hplanar : IsNoncrossingMatching mate)
    (s : Finset (Fin n))
    (hconvex : ∀ a ∈ s, ∀ b ∈ s, ∀ c, a < c → c < b → c ∈ s)
    (hchord : ∃ a ∈ s, mate a ∈ s) :
    ∃ i ∈ s, mate i ∈ s ∧ (mate i).val = i.val + 1 := by
  classical
  let chords := s.filter (fun i => mate i ∈ s ∧ i < mate i)
  have hnonempty : chords.Nonempty := by
    obtain ⟨a,ha,hb⟩ := hchord
    by_cases h : a < mate a
    · exact ⟨a, by simp [chords, ha, hb, h]⟩
    · have h' : mate a < a := lt_of_le_of_ne (le_of_not_gt h) (hfree a)
      exact ⟨mate a, by simp [chords, ha, hb, hinv, h']⟩
  obtain ⟨a, ha, hminimal⟩ := chords.exists_min_image
    (fun i => (mate i).val - i.val) hnonempty
  have has : a ∈ s := (Finset.mem_filter.mp ha).1
  have hbs : mate a ∈ s := (Finset.mem_filter.mp ha).2.1
  have hab : a < mate a := (Finset.mem_filter.mp ha).2.2
  by_cases hadj : (mate a).val = a.val + 1
  · exact ⟨a, has, hbs, hadj⟩
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
  have hcs : c ∈ s := hconvex a has (mate a) hbs c hac hcb
  have hds : mate c ∈ s := hconvex a has (mate a) hbs (mate c) hinside.1 hinside.2
  by_cases hcd : c < mate c
  · have hmem : c ∈ chords := by simp [chords, hcs, hds, hcd]
    have hm := hminimal c hmem
    have hd := hinside.2
    change (mate c).val < (mate a).val at hd
    change a.val < (mate a).val at hab
    change a.val < c.val at hac
    omega
  · have hdc : mate c < c := lt_of_le_of_ne (le_of_not_gt hcd) (hfree c)
    have hmem : mate c ∈ chords := by simp [chords, hcs, hds, hinv, hdc]
    have hm := hminimal (mate c) hmem
    rw [hinv] at hm
    have hd := hinside.1
    change a.val < (mate c).val at hd
    change c.val < (mate a).val at hcb
    change a.val < (mate a).val at hab
    omega

/-- A block containing more than half the ports must contain both ends of
some chord. Convexity and noncrossing then force an adjacent pair there. -/
theorem exists_adjacent_majority (mate : Fin n → Fin n)
    (hinv : Function.Involutive mate)
    (hfree : ∀ i, mate i ≠ i) (hplanar : IsNoncrossingMatching mate)
    (s : Finset (Fin n))
    (hconvex : ∀ a ∈ s, ∀ b ∈ s, ∀ c, a < c → c < b → c ∈ s)
    (hmajor : n < 2 * s.card) :
    ∃ i ∈ s, mate i ∈ s ∧ (mate i).val = i.val + 1 := by
  classical
  apply exists_adjacent_within mate hinv hfree hplanar s hconvex
  by_contra hn
  have maps : Set.MapsTo mate s (sᶜ : Finset (Fin n)) := by
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_compl] at *
    exact fun hm => hn ⟨i,hi,hm⟩
  have bound := Finset.card_le_card_of_injOn mate maps hinv.injective.injOn
  rw [Finset.card_compl, Fintype.card_fin] at bound
  omega

/-- Every fixed-point-free noncrossing involution has a pair of consecutive
ports in the displayed order. -/
theorem exists_adjacent [NeZero n] (mate : Fin n → Fin n)
    (hinv : ∀ i, mate (mate i) = i)
    (hfree : ∀ i, mate i ≠ i) (hplanar : IsNoncrossingMatching mate) :
    ∃ i, (mate i).val = i.val + 1 := by
  obtain ⟨i,_,_,hi⟩ := exists_adjacent_within mate hinv hfree hplanar Finset.univ
    (by simp) ⟨0, Finset.mem_univ _, Finset.mem_univ _⟩
  exact ⟨i,hi⟩

end Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

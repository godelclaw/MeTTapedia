import Mettapedia.GraphTheory.CoupledThreeColouring

/-!
# Ordered three-colour extension with fixed boundary choices

A partial colouring remains fixed while uncoloured vertices are inserted
in a finite order. The sufficient condition counts distinct earlier colours,
including every already coloured boundary neighbour. Actual coupled and
low-degree consumers supply this condition from graph structure.

This is the greedy extension mechanism used in Brooks' theorem and in
M. Zając, *A short proof of Brooks' theorem* (2018), arXiv:1805.11176.
-/

namespace Mettapedia.GraphTheory.OrderedBoundaryColouring

open SimpleGraph Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Fixed boundary neighbours are already coloured regardless of their
rank; every other earlier neighbour contributes its current choice. -/
def usedNeighbours (fixed : V → Prop) [DecidablePred fixed] (rank : V → ℕ) (v : V) :
    Finset V := (G.neighborFinset v).filter (fun w => fixed w ∨ rank w < rank v)

/-- The greedy extension retains every fixed value. Availability is a
uniform consequence of the boundary choices and order, rather than a
separate colouring certificate for each intermediate stage. -/
theorem extend (fixed : V → Prop) [DecidablePred fixed]
    (rank : V → ℕ)
    (hinj : ∀ x y, ¬fixed x → ¬fixed y → rank x = rank y → x = y)
    (initial : V → Fin 3)
    (hproper : ∀ x y, fixed x → fixed y → G.Adj x y → initial x ≠ initial y)
    (hsmall : ∀ c : V → Fin 3, (∀ w, fixed w → c w = initial w) →
      ∀ v, ¬fixed v → ((usedNeighbours G fixed rank v).image c).card < 3) :
    ∃ c : G.Coloring (Fin 3), ∀ w, fixed w → c w = initial w := by
  classical
  have hpref : ∀ n : ℕ, ∃ c : V → Fin 3,
      (∀ w, fixed w → c w = initial w) ∧
      ∀ x y, (fixed x ∨ rank x < n) → (fixed y ∨ rank y < n) →
        G.Adj x y → c x ≠ c y := by
    intro n
    induction n with
    | zero =>
      refine ⟨initial, fun _ _ => rfl, ?_⟩
      intro x y hx hy hxy
      exact hproper x y (hx.resolve_right (by omega)) (hy.resolve_right (by omega)) hxy
    | succ n ih =>
      obtain ⟨c, hfixed, hc⟩ := ih
      by_cases hex : ∃ v, ¬fixed v ∧ rank v = n
      · obtain ⟨v, hvf, hv⟩ := hex
        let used := (usedNeighbours G fixed rank v).image c
        have hused : used.card < 3 := hsmall c hfixed v hvf
        obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ∉ used := by
          by_contra hn
          push Not at hn
          have hsub : (Finset.univ : Finset (Fin 3)) ⊆ used := fun x _ => hn x
          have := Finset.card_le_card hsub
          simp only [Finset.card_univ, Fintype.card_fin] at this
          omega
        let c' : V → Fin 3 := fun w => if w = v then j else c w
        have earlier : ∀ w, w ≠ v → (fixed w ∨ rank w < n + 1) →
            fixed w ∨ rank w < n := by
          intro w hw hp
          by_cases hf : fixed w
          · exact Or.inl hf
          · right
            have hn : rank w ≠ n := fun he => hw (hinj w v hf hvf (he.trans hv.symm))
            have := hp.resolve_left hf
            omega
        have hav : ∀ w, G.Adj v w → (fixed w ∨ rank w < n) → j ≠ c w := by
          intro w hw he hjc
          apply hj
          exact Finset.mem_image.mpr ⟨w,
            Finset.mem_filter.mpr ⟨by simpa using hw, by simpa [hv] using he⟩, hjc.symm⟩
        refine ⟨c', ?_, ?_⟩
        · intro w hw
          have hne : w ≠ v := by intro he; subst w; exact hvf hw
          simpa [c', hne] using hfixed w hw
        · intro x y hx hy hxy
          by_cases hxv : x = v <;> by_cases hyv : y = v
          · subst x; subst y; exact (G.irrefl hxy).elim
          · subst x
            simpa [c', hyv] using hav y hxy (earlier y hyv hy)
          · subst y
            simpa [c', hxv] using (hav x hxy.symm (earlier x hxv hx)).symm
          · simpa [c', hxv, hyv] using hc x y (earlier x hxv hx) (earlier y hyv hy) hxy
      · refine ⟨c, hfixed, ?_⟩
        have earlier : ∀ w, (fixed w ∨ rank w < n + 1) → fixed w ∨ rank w < n := by
          intro w hw
          by_cases hf : fixed w
          · exact Or.inl hf
          · have hn : rank w ≠ n := fun he => hex ⟨w, hf, he⟩
            right
            have := hw.resolve_left hf
            omega
        intro x y hx hy hxy
        exact hc x y (earlier x hx) (earlier y hy) hxy
  obtain ⟨c, hf, hc⟩ := hpref (Finset.univ.sup rank + 1)
  have hrank : ∀ v, rank v < Finset.univ.sup rank + 1 := by
    intro v
    have := Finset.le_sup (f := rank) (Finset.mem_univ v)
    omega
  exact ⟨Coloring.mk c (fun h => hc _ _ (Or.inr (hrank _)) (Or.inr (hrank _)) h), hf⟩

/-- A vertex with fewer than three neighbours can be inserted without
changing any supplied exterior colour. -/
theorem low_degree_extension {v : V} (hdeg : G.degree v < 3)
    (outside : (G.induce {w | w ≠ v}).Coloring (Fin 3)) :
    ∃ c : G.Coloring (Fin 3), ∀ w (hw : w ≠ v), c w = outside ⟨w, hw⟩ := by
  classical
  let initial : V → Fin 3 := fun w => if h : w = v then 0 else outside ⟨w, h⟩
  obtain ⟨c, hc⟩ := extend G (fun w => w ≠ v) (fun _ => 0) (by
    intro x y hx hy _
    exact (not_ne_iff.mp hx).trans (not_ne_iff.mp hy).symm) initial (by
    intro x y hx hy hxy
    simpa [initial, hx, hy] using outside.valid (show
      (G.induce {w | w ≠ v}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)) (by
    intro c _ w hw
    have he : w = v := not_ne_iff.mp hw
    subst w
    have hn : (G.neighborFinset v).card < 3 := hdeg
    exact (Finset.card_image_le.trans
      (Finset.card_le_card (Finset.filter_subset _ _))).trans_lt hn)
  refine ⟨c, ?_⟩
  intro w hw
  simpa [initial, hw] using hc w hw

/-- A region order starts with a fixed internal seed. Every other vertex
except the closing root has a later uncoloured neighbour in the region. -/
structure CoupledRegionOrder (inside : Finset V) (seed root : V) where
  rank : V → ℕ
  injective : ∀ x y, x ∈ inside → y ∈ inside → x ≠ seed → y ≠ seed →
    rank x = rank y → x = y
  later : ∀ v, v ∈ inside → v ≠ seed → v ≠ root →
    ∃ w, w ∈ inside ∧ w ≠ seed ∧ G.Adj v w ∧ rank v < rank w

/-- Copying an exterior neighbour's colour to an internally supported seed
permits closing at their common neighbour. All supplied exterior choices
remain fixed. The hypotheses retain exactly the needed joint choice. -/
theorem coupled_region_extension (inside : Finset V) {a b r : V}
    (hb : b ∈ inside) (ha : a ∉ inside)
    (hseed : ∀ w, G.Adj b w → w ∈ inside)
    (har : G.Adj r a) (hbr : G.Adj r b)
    (o : CoupledRegionOrder G inside b r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (outside : (G.induce {v | v ∉ inside}).Coloring (Fin 3)) :
    ∃ c : G.Coloring (Fin 3), c b = outside ⟨a, ha⟩ ∧
      ∀ w (hw : w ∉ inside), c w = outside ⟨w, hw⟩ := by
  classical
  let fixed : V → Prop := fun v => v ∉ inside ∨ v = b
  let initial : V → Fin 3 := fun v =>
    if v = b then outside ⟨a, ha⟩ else if hv : v ∉ inside then outside ⟨v, hv⟩ else 0
  have hab : a ≠ b := by intro he; subst a; exact ha hb
  have hproper : ∀ x y, fixed x → fixed y → G.Adj x y → initial x ≠ initial y := by
    intro x y hx hy hxy
    rcases hx with hx | rfl <;> rcases hy with hy | rfl
    · have hxb : x ≠ b := by intro he; subst x; exact hx hb
      have hyb : y ≠ b := by intro he; subst y; exact hy hb
      simpa [initial, hxb, hyb, hx, hy] using outside.valid
        (show (G.induce {v | v ∉ inside}).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · exact (hx (hseed x hxy.symm)).elim
    · exact (hy (hseed y hxy)).elim
    · exact (G.irrefl hxy).elim
  have hsmall : ∀ c : V → Fin 3, (∀ w, fixed w → c w = initial w) →
      ∀ v, ¬fixed v → ((usedNeighbours G fixed o.rank v).image c).card < 3 := by
    intro c hc v hv
    have hvi : v ∈ inside := by
      by_contra hn
      exact hv (Or.inl hn)
    have hvb : v ≠ b := fun he => hv (Or.inr he)
    let s := usedNeighbours G fixed o.rank v
    have hsub : s ⊆ G.neighborFinset v := Finset.filter_subset _ _
    have hdegree : (G.neighborFinset v).card ≤ 3 := hdeg v
    by_cases hvr : v = r
    · subst v
      have ha_s : a ∈ s := Finset.mem_filter.mpr
        ⟨by simpa using har, Or.inl (Or.inl ha)⟩
      have hb_s : b ∈ s := Finset.mem_filter.mpr
        ⟨by simpa using hbr, Or.inl (Or.inr rfl)⟩
      have hequal : c a = c b := by
        rw [hc a (Or.inl ha), hc b (Or.inr rfl)]
        simp [initial, hab, ha]
      have himage : s.image c = (s.erase b).image c := by
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          by_cases hwb : w = b
          · subst w
            exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab, ha_s⟩, hequal⟩
          · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwb, hw⟩, rfl⟩
        · intro x hx
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_image.mpr ⟨w, Finset.mem_of_mem_erase hw, rfl⟩
      have hscard : s.card ≤ 3 := (Finset.card_le_card hsub).trans hdegree
      change (s.image c).card < 3
      rw [himage]
      have := Finset.card_image_le (f := c) (s := s.erase b)
      have := Finset.card_erase_of_mem hb_s
      omega
    · obtain ⟨w, hwi, hwb, hw, hlate⟩ := o.later v hvi hvb hvr
      have hw_n : w ∈ G.neighborFinset v := by simpa using hw
      have hw_s : w ∉ s := by
        intro hs
        rcases (Finset.mem_filter.mp hs).2 with hf | hrank
        · exact hf.elim (fun hn => hn hwi) hwb
        · omega
      have hproper : s ⊂ G.neighborFinset v := Finset.ssubset_iff_subset_ne.mpr
        ⟨hsub, fun he => hw_s (he.symm ▸ hw_n)⟩
      have := Finset.card_lt_card hproper
      have := Finset.card_image_le (f := c) (s := s)
      change (s.image c).card < 3
      omega
  obtain ⟨c, hc⟩ := extend G fixed o.rank (by
    intro x y hx hy he
    apply o.injective x y
    · by_contra hn; exact hx (Or.inl hn)
    · by_contra hn; exact hy (Or.inl hn)
    · exact fun h => hx (Or.inr h)
    · exact fun h => hy (Or.inr h)
    · exact he) initial hproper hsmall
  refine ⟨c, ?_, ?_⟩
  · simpa [initial] using hc b (Or.inr rfl)
  · intro w hw
    have hwb : w ≠ b := by intro he; subst w; exact hw hb
    simpa [initial, hwb, hw] using hc w (Or.inl hw)

/-- Connectivity of the region with its seed removed constructs the order
from actual distances. No per-instance order certificate is required. -/
def regionOrder_of_connected_deletion (inside : Finset V) {b r : V}
    (hr : r ∈ inside) (hbr : G.Adj r b)
    (hconn : (G.induce {v | v ∈ inside ∧ v ≠ b}).Connected) :
    CoupledRegionOrder G inside b r := by
  classical
  let H := G.induce {v | v ∈ inside ∧ v ≠ b}
  let root : {v : V // v ∈ inside ∧ v ≠ b} := ⟨r, hr, hbr.ne⟩
  let rank : V → ℕ := fun v =>
    if h : v ∈ inside ∧ v ≠ b then CoupledThreeColouring.reverseDistanceRank H root ⟨v, h⟩
    else 0
  refine ⟨rank, ?_, ?_⟩
  · intro x y hxi hyi hxb hyb he
    have he' : CoupledThreeColouring.reverseDistanceRank H root ⟨x, hxi, hxb⟩ =
        CoupledThreeColouring.reverseDistanceRank H root ⟨y, hyi, hyb⟩ := by
      simpa [rank, hxi, hxb, hyi, hyb] using he
    exact congrArg Subtype.val
      (CoupledThreeColouring.reverseDistanceRank_injective H root he')
  · intro v hvi hvb hvr
    obtain ⟨w, hw, hd⟩ := CoupledThreeColouring.closer_neighbour H hconn
      (x := ⟨v, hvi, hvb⟩) (root := root) (fun he => hvr (congrArg Subtype.val he))
    refine ⟨w.val, w.property.1, w.property.2, hw, ?_⟩
    simpa [rank, hvi, hvb, w.property.1, w.property.2] using
      CoupledThreeColouring.reverseDistanceRank_lt_of_dist_lt H hd

theorem coupled_extension_of_connected_deletion (inside : Finset V) {a b r : V}
    (hb : b ∈ inside) (ha : a ∉ inside) (hr : r ∈ inside)
    (hseed : ∀ w, G.Adj b w → w ∈ inside)
    (har : G.Adj r a) (hbr : G.Adj r b)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hconn : (G.induce {v | v ∈ inside ∧ v ≠ b}).Connected)
    (outside : (G.induce {v | v ∉ inside}).Coloring (Fin 3)) :
    ∃ c : G.Coloring (Fin 3), c b = outside ⟨a, ha⟩ ∧
      ∀ w (hw : w ∉ inside), c w = outside ⟨w, hw⟩ :=
  coupled_region_extension G inside hb ha hseed har hbr
    (regionOrder_of_connected_deletion G inside hr hbr hconn) hdeg outside

end
end Mettapedia.GraphTheory.OrderedBoundaryColouring

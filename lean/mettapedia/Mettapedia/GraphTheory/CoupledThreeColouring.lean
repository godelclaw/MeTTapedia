import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max

/-!
# Three-colouring with a coupled pair of insertions

Two nonadjacent neighbours of a closing vertex may be assigned the same
colour. A reverse rooted order then colours every earlier vertex while
leaving one neighbour uncoloured. At the closing vertex the shared pair
uses only one colour, so three colours suffice there as well.

The ordered argument is a finite specialization of the method in
R. L. Brooks, *On Colouring the Nodes of a Network* (1941),
doi:10.1017/S030500410002168X. It preserves a joint choice for the two
insertions; it does not assert that arbitrary nonadjacent vertices can
be made equal by recolouring.
-/

namespace Mettapedia.GraphTheory.CoupledThreeColouring

open SimpleGraph Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite insertion order with two initial neighbours and one closing
vertex. Every other vertex has a neighbour that is inserted later. -/
structure CoupledOrder (a b r : V) where
  rank : V → ℕ
  injective : Function.Injective rank
  rank_a : rank a = 0
  rank_b : rank b = 1
  remaining : ∀ v, v ≠ a → v ≠ b → 2 ≤ rank v
  later : ∀ v, v ≠ a → v ≠ b → v ≠ r →
    ∃ w, G.Adj v w ∧ rank v < rank w

private theorem earlier_colours_small {a b r : V}
    (o : CoupledOrder G a b r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (ha : G.Adj r a) (hb : G.Adj r b)
    (c : V → Fin 3) (hc : c a = c b)
    {v : V} (hva : v ≠ a) (hvb : v ≠ b) :
    (((G.neighborFinset v).filter (fun w => o.rank w < o.rank v)).image c).card < 3 := by
  classical
  let s := (G.neighborFinset v).filter (fun w => o.rank w < o.rank v)
  have hs : s ⊆ G.neighborFinset v := Finset.filter_subset _ _
  have hdegree : (G.neighborFinset v).card ≤ 3 := hdeg v
  by_cases hvr : v = r
  · subst v
    have hab : a ≠ b := by
      intro h
      have := congrArg o.rank h
      rw [o.rank_a, o.rank_b] at this
      omega
    have ha_s : a ∈ s := by
      simp only [s, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨ha, by have := o.remaining r ha.ne hb.ne; rw [o.rank_a]; omega⟩
    have hb_s : b ∈ s := by
      simp only [s, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨hb, by have := o.remaining r ha.ne hb.ne; rw [o.rank_b]; omega⟩
    have himage : s.image c = (s.erase b).image c := by
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        by_cases hwb : w = b
        · subst w
          exact Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab, ha_s⟩, hc⟩
        · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwb, hw⟩, rfl⟩
      · intro x hx
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨w, Finset.mem_of_mem_erase hw, rfl⟩
    have hscard : s.card ≤ 3 := (Finset.card_le_card hs).trans hdegree
    rw [show ((G.neighborFinset r).filter (fun w => o.rank w < o.rank r)) = s from rfl,
      himage]
    have hbound := Finset.card_image_le (f := c) (s := s.erase b)
    have herase := Finset.card_erase_of_mem hb_s
    omega
  · obtain ⟨w, hw, hlate⟩ := o.later v hva hvb hvr
    have hw_n : w ∈ G.neighborFinset v := by simpa using hw
    have hw_s : w ∉ s := by simp only [s, Finset.mem_filter]; omega
    have hproper : s ⊂ G.neighborFinset v := Finset.ssubset_iff_subset_ne.mpr
      ⟨hs, fun he => hw_s (he.symm ▸ hw_n)⟩
    have := Finset.card_lt_card hproper
    have := Finset.card_image_le (f := c) (s := s)
    change (s.image c).card < 3
    omega

/-- One uniform ordered argument constructs a genuine colouring while
keeping the two initial insertion choices equal. -/
theorem colouring_of_coupledOrder {a b r : V}
    (o : CoupledOrder G a b r)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hab : ¬G.Adj a b) (ha : G.Adj r a) (hb : G.Adj r b) :
    ∃ c : G.Coloring (Fin 3), c a = c b := by
  classical
  have hpref : ∀ n : ℕ, ∃ c : V → Fin 3, c a = 0 ∧ c b = 0 ∧
      ∀ v w, o.rank v < n + 2 → o.rank w < n + 2 →
        G.Adj v w → c v ≠ c w := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => 0, rfl, rfl, ?_⟩
      intro v w hv hw hvw
      have hseed : ∀ x, o.rank x < 2 → x = a ∨ x = b := by
        intro x hx
        by_contra hn
        push Not at hn
        have := o.remaining x hn.1 hn.2
        omega
      rcases hseed v hv with rfl | rfl <;> rcases hseed w hw with rfl | rfl
      · exact (G.irrefl hvw).elim
      · exact (hab hvw).elim
      · exact (hab hvw.symm).elim
      · exact (G.irrefl hvw).elim
    | succ n ih =>
      obtain ⟨c, hca, hcb, hproper⟩ := ih
      by_cases hex : ∃ v, o.rank v = n + 2
      · obtain ⟨v, hv⟩ := hex
        have hva : v ≠ a := by intro h; subst v; rw [o.rank_a] at hv; omega
        have hvb : v ≠ b := by intro h; subst v; rw [o.rank_b] at hv; omega
        let used := ((G.neighborFinset v).filter (fun w => o.rank w < o.rank v)).image c
        have hused : used.card < 3 :=
          earlier_colours_small G o hdeg ha hb c (hca.trans hcb.symm) hva hvb
        obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ∉ used := by
          by_contra hn
          push Not at hn
          have hall : (Finset.univ : Finset (Fin 3)) ⊆ used := fun x _ => hn x
          have := Finset.card_le_card hall
          simp only [Finset.card_univ, Fintype.card_fin] at this
          omega
        let c' : V → Fin 3 := fun w => if w = v then j else c w
        refine ⟨c', by simp [c', hva.symm, hca], by simp [c', hvb.symm, hcb], ?_⟩
        have hav : ∀ w, G.Adj v w → o.rank w < o.rank v → j ≠ c w := by
          intro w hw hwr heq
          apply hj
          exact Finset.mem_image.mpr ⟨w,
            Finset.mem_filter.mpr ⟨by simpa using hw, hwr⟩, heq.symm⟩
        intro x y hx hy hxy
        by_cases hxv : x = v <;> by_cases hyv : y = v
        · subst x; subst y; exact (G.irrefl hxy).elim
        · subst x
          have hyr : o.rank y < o.rank v := by
            have hyn : o.rank y ≠ o.rank v := fun he => hyv (o.injective he)
            omega
          simpa [c', hyv] using hav y hxy hyr
        · subst y
          have hxr : o.rank x < o.rank v := by
            have hxn : o.rank x ≠ o.rank v := fun he => hxv (o.injective he)
            omega
          simpa [c', hxv] using (hav x hxy.symm hxr).symm
        · have hxr : o.rank x < n + 2 := by
            have hxn : o.rank x ≠ o.rank v := fun he => hxv (o.injective he)
            omega
          have hyr : o.rank y < n + 2 := by
            have hyn : o.rank y ≠ o.rank v := fun he => hyv (o.injective he)
            omega
          simpa [c', hxv, hyv] using hproper x y hxr hyr hxy
      · refine ⟨c, hca, hcb, ?_⟩
        intro x y hx hy hxy
        have hxne : o.rank x ≠ n + 2 := fun he => hex ⟨x, he⟩
        have hyne : o.rank y ≠ n + 2 := fun he => hex ⟨y, he⟩
        exact hproper x y (by omega) (by omega) hxy
  obtain ⟨c, hca, hcb, hc⟩ := hpref (Finset.univ.sup o.rank)
  have hrank : ∀ v, o.rank v < Finset.univ.sup o.rank + 2 := by
    intro v
    have := Finset.le_sup (s := (Finset.univ : Finset V)) (f := o.rank) (Finset.mem_univ v)
    omega
  exact ⟨SimpleGraph.Coloring.mk c (fun h => hc _ _ (hrank _) (hrank _) h),
    hca.trans hcb.symm⟩

section RootedOrder

variable {W : Type*} [Fintype W] (H : SimpleGraph W)

/-- Distance from the root is the primary order; a finite enumeration breaks
ties. No colouring or per-graph insertion order is supplied as input. -/
def reverseDistanceRank (root w : W) : ℕ :=
  (Finset.univ.sup (fun x => H.dist x root) - H.dist w root) *
      (Fintype.card W + 1) + (Fintype.equivFin W w).val

theorem reverseDistanceRank_injective (root : W) :
    Function.Injective (reverseDistanceRank H root) := by
  classical
  intro x y he
  have hx : (Fintype.equivFin W x).val < Fintype.card W + 1 :=
    (Fintype.equivFin W x).isLt.trans (Nat.lt_succ_self _)
  have hy : (Fintype.equivFin W y).val < Fintype.card W + 1 :=
    (Fintype.equivFin W y).isLt.trans (Nat.lt_succ_self _)
  have hm := congrArg (fun n => n % (Fintype.card W + 1)) he
  have hid : (Fintype.equivFin W x).val = (Fintype.equivFin W y).val := by
    simpa [reverseDistanceRank, Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
      using hm
  exact (Fintype.equivFin W).injective (Fin.ext hid)

theorem reverseDistanceRank_lt_of_dist_lt {root x y : W}
    (h : H.dist y root < H.dist x root) :
    reverseDistanceRank H root x < reverseDistanceRank H root y := by
  classical
  let D := Finset.univ.sup (fun w => H.dist w root)
  let B := Fintype.card W + 1
  have hdx : H.dist x root ≤ D :=
    Finset.le_sup (f := fun w => H.dist w root) (Finset.mem_univ x)
  have hdy : H.dist y root ≤ D :=
    Finset.le_sup (f := fun w => H.dist w root) (Finset.mem_univ y)
  have hsub : D - H.dist x root + 1 ≤ D - H.dist y root := by omega
  have hid : (Fintype.equivFin W x).val < B :=
    (Fintype.equivFin W x).isLt.trans (Nat.lt_succ_self _)
  have hmul := Nat.mul_le_mul_right B hsub
  change (D - H.dist x root) * B + (Fintype.equivFin W x).val <
    (D - H.dist y root) * B + (Fintype.equivFin W y).val
  calc
    _ < (D - H.dist x root) * B + B := Nat.add_lt_add_left hid _
    _ = (D - H.dist x root + 1) * B := by simp [Nat.add_mul]
    _ ≤ (D - H.dist y root) * B := hmul
    _ ≤ _ := Nat.le_add_right _ _

omit [Fintype W] in
/-- Actual connectivity supplies the later neighbour required by the order. -/
theorem closer_neighbour (hconn : H.Connected) {x root : W} (hx : x ≠ root) :
    ∃ y, H.Adj x y ∧ H.dist y root < H.dist x root := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x root
  cases p with
  | nil => exact (hx rfl).elim
  | @cons x y root hxy p =>
    refine ⟨y, hxy, ?_⟩
    have hd := H.dist_le p
    simp only [Walk.length_cons] at hp
    omega

end RootedOrder

/-- Removing the two initial choices leaves the actual graph on which the
rooted insertion order is constructed. -/
abbrev Retained (a b : V) := {v : V // v ≠ a ∧ v ≠ b}

/-- Connectivity after deleting the pair supplies a coupled order uniformly,
without a separate ordering certificate for each graph. -/
def coupledOrder_of_connected_pair {a b r : V} (hab : a ≠ b)
    (ha : G.Adj r a) (hb : G.Adj r b)
    (hconn : (G.induce {v | v ≠ a ∧ v ≠ b}).Connected) : CoupledOrder G a b r := by
  classical
  let H := G.induce {v | v ≠ a ∧ v ≠ b}
  let root : Retained a b := ⟨r, ha.ne, hb.ne⟩
  let rank : V → ℕ := fun v =>
    if h : v = a then 0 else if h' : v = b then 1
    else reverseDistanceRank H root ⟨v, h, h'⟩ + 2
  have hra : rank a = 0 := by simp [rank]
  have hrb : rank b = 1 := by simp [rank, hab.symm]
  have hrank : ∀ v (hva : v ≠ a) (hvb : v ≠ b),
      rank v = reverseDistanceRank H root ⟨v, hva, hvb⟩ + 2 := by
    intro v hva hvb
    simp [rank, hva, hvb]
  have hrem : ∀ v, v ≠ a → v ≠ b → 2 ≤ rank v := by
    intro v hva hvb
    rw [hrank v hva hvb]
    omega
  refine ⟨rank, ?_, hra, hrb, hrem, ?_⟩
  · intro x y he
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · exact hya.symm
      · by_cases hyb : y = b
        · subst y; rw [hra, hrb] at he; omega
        · have := hrem y hya hyb; rw [hra] at he; omega
    · by_cases hxb : x = b
      · subst x
        by_cases hyb : y = b
        · exact hyb.symm
        · by_cases hya : y = a
          · subst y; rw [hra, hrb] at he; omega
          · have := hrem y hya hyb; rw [hrb] at he; omega
      · by_cases hya : y = a
        · subst y; have := hrem x hxa hxb; rw [hra] at he; omega
        · by_cases hyb : y = b
          · subst y; have := hrem x hxa hxb; rw [hrb] at he; omega
          · have he' : reverseDistanceRank H root ⟨x, hxa, hxb⟩ =
                reverseDistanceRank H root ⟨y, hya, hyb⟩ := by
              rw [hrank x hxa hxb, hrank y hya hyb] at he
              omega
            exact congrArg Subtype.val (reverseDistanceRank_injective H root he')
  · intro v hva hvb hvr
    obtain ⟨w, hw, hd⟩ := closer_neighbour H hconn
      (x := (⟨v, hva, hvb⟩ : Retained a b)) (root := root)
      (fun h => hvr (congrArg Subtype.val h))
    refine ⟨w.val, hw, ?_⟩
    rw [hrank v hva hvb, hrank w.val w.property.1 w.property.2]
    exact Nat.add_lt_add_right (reverseDistanceRank_lt_of_dist_lt H hd) 2

/-- A structural graph hypothesis supplies the shared colouring witness:
two nonadjacent neighbours may be deleted while leaving a connected graph.
The conclusion retains their joint colour choice. -/
theorem colouring_of_connected_pair {a b r : V}
    (hdeg : ∀ v, G.degree v ≤ 3)
    (hab : a ≠ b) (hnadj : ¬G.Adj a b)
    (ha : G.Adj r a) (hb : G.Adj r b)
    (hconn : (G.induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    ∃ c : G.Coloring (Fin 3), c a = c b :=
  colouring_of_coupledOrder G (coupledOrder_of_connected_pair G hab ha hb hconn)
    hdeg hnadj ha hb

/-- Connected noncomplete graphs supply two nonadjacent neighbours from the
first three vertices of an actual shortest path. -/
theorem exists_nonadjacent_neighbours (hconn : G.Connected)
    (hnot : ¬∀ x y : V, x ≠ y → G.Adj x y) :
    ∃ a b r, a ≠ b ∧ ¬G.Adj a b ∧ G.Adj r a ∧ G.Adj r b := by
  classical
  push Not at hnot
  obtain ⟨x, y, hxy, hnadj⟩ := hnot
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  obtain ⟨a, r, b, har, hrb, hab, hne⟩ :=
    p.exists_adj_adj_not_adj_ne hp (hconn.one_lt_dist_of_ne_of_not_adj hxy hnadj)
  exact ⟨a, b, r, hne, hab, har.symm, hrb⟩

/-- Brooks' three-colour argument on the domain where deleting any two
distinct vertices leaves a connected graph. The shared insertion pair is
derived, rather than supplied as another witness hypothesis. -/
theorem colourable_of_pairDeletionConnected
    (hdeg : ∀ v, G.degree v ≤ 3) (hconn : G.Connected)
    (hnot : ¬∀ x y : V, x ≠ y → G.Adj x y)
    (hdelete : ∀ a b : V, a ≠ b → (G.induce {v | v ≠ a ∧ v ≠ b}).Connected) :
    G.Colorable 3 := by
  obtain ⟨a, b, r, hab, hnadj, ha, hb⟩ := exists_nonadjacent_neighbours G hconn hnot
  obtain ⟨c, _⟩ := colouring_of_connected_pair G hdeg hab hnadj ha hb (hdelete a b hab)
  exact ⟨c⟩

end
end Mettapedia.GraphTheory.CoupledThreeColouring

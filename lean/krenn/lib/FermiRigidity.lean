import Mathlib
import FermiDescent
import CharTwoRigidity

/-!
# Rigidity of fermionic GHZ systems

On four sites `a < b < x < y` the signed matching sum is
`W(ab) W(xy) - W(ax) W(by) + W(ay) W(bx)`: the unsigned sum of the weights with the pair `ax`
negated (`pfSum_univ_eq_amplitude_twist`).  So a fermionic GHZ system on four sites is a GHZ
system after one sign change, and four-site rigidity (`KrennCharTwo.fourRigid`) and the `K4`
shape transfer to it: the vanishing of a weight does not see its sign.
-/

namespace KrennFermi

open Amplitude MatchingSum MatchingPfaffian MatchingBlockRank KrennCharTwo

variable {F : Type*} [Field F]

section Small

variable {V C R : Type*} [DecidableEq V] [LinearOrder V] [CommRing R]

/-- The signed matching sum of a pair of sites is the weight of the pair. -/
theorem pfSum_pair (W : Sym2 (V × C) → R) (c : V → C) {u v : V} (huv : u ≠ v) :
    pfSum W c {u, v} = W (Sym2.map (paint c) s(u, v)) := by
  have key : ∀ {s t : V}, s < t → pfSum W c {s, t} = W (Sym2.map (paint c) s(s, t)) := by
    intro s t hst
    have hs : s ∈ ({s, t} : Finset V) := by simp
    have hmin : ∀ w ∈ ({s, t} : Finset V), s ≤ w := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact le_rfl
      · exact hst.le
    rw [pfSum_min W c hs hmin]
    have herase : ({s, t} : Finset V).erase s = {t} := by
      rw [Finset.erase_insert (by simp [hst.ne])]
    rw [herase, Finset.sum_singleton, Finset.erase_singleton, pfSum_empty, mul_one]
    have hpos : pos {s, t} t = 1 := by
      unfold pos
      rw [Finset.filter_insert, if_pos hst, Finset.filter_singleton, if_neg (lt_irrefl t)]
      simp
    rw [hpos]
    norm_num
  rcases lt_or_gt_of_ne huv with h | h
  · exact key h
  · rw [Finset.pair_comm, key h, Sym2.eq_swap]

/-- **The signed matching sum of four ordered sites.** -/
theorem pfSum_four (W : Sym2 (V × C) → R) (c : V → C) {a b x y : V}
    (hab : a < b) (hbx : b < x) (hxy : x < y) :
    pfSum W c {a, b, x, y}
      = W (Sym2.map (paint c) s(a, b)) * W (Sym2.map (paint c) s(x, y))
        - W (Sym2.map (paint c) s(a, x)) * W (Sym2.map (paint c) s(b, y))
        + W (Sym2.map (paint c) s(a, y)) * W (Sym2.map (paint c) s(b, x)) := by
  have hax : a < x := hab.trans hbx
  have hay : a < y := hax.trans hxy
  have hby : b < y := hbx.trans hxy
  have ha : a ∈ ({a, b, x, y} : Finset V) := by simp
  have hmin : ∀ w ∈ ({a, b, x, y} : Finset V), a ≤ w := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact le_rfl
    · exact hab.le
    · exact hax.le
    · exact hay.le
  rw [pfSum_min W c ha hmin]
  have herase : ({a, b, x, y} : Finset V).erase a = {b, x, y} := by
    rw [Finset.erase_insert (by simp [hab.ne, hax.ne, hay.ne])]
  rw [herase]
  have hbxy : b ∉ ({x, y} : Finset V) := by simp [hbx.ne, hby.ne]
  have hxy' : x ∉ ({y} : Finset V) := by simp [hxy.ne]
  rw [Finset.sum_insert hbxy, Finset.sum_insert hxy', Finset.sum_singleton]
  -- positions and the remaining pairs
  have pb : pos ({a, b, x, y} : Finset V) b = 1 := by
    unfold pos
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
      if_pos hab, if_neg (lt_irrefl b), if_neg (not_lt.mpr hbx.le), if_neg (not_lt.mpr hby.le)]
    simp
  have px : pos ({a, b, x, y} : Finset V) x = 2 := by
    unfold pos
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
      if_pos hax, if_pos hbx, if_neg (lt_irrefl x), if_neg (not_lt.mpr hxy.le)]
    rw [Finset.card_insert_of_notMem (by simp [hab.ne])]
    simp
  have py : pos ({a, b, x, y} : Finset V) y = 3 := by
    unfold pos
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
      if_pos hay, if_pos hby, if_pos hxy, if_neg (lt_irrefl y)]
    rw [Finset.card_insert_of_notMem (by simp [hab.ne, hax.ne]),
      Finset.card_insert_of_notMem (by simp [hbx.ne])]
    simp
  have r1 : (({b, x, y} : Finset V).erase b) = {x, y} := by
    rw [Finset.erase_insert hbxy]
  have r2 : (({b, x, y} : Finset V).erase x) = {b, y} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact absurd rfl hz
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hbx.ne, Or.inl rfl⟩
      · exact ⟨hxy.ne', Or.inr (Or.inr rfl)⟩
  have r3 : (({b, x, y} : Finset V).erase y) = {b, x} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hz
    · rintro (rfl | rfl)
      · exact ⟨hby.ne, Or.inl rfl⟩
      · exact ⟨hxy.ne, Or.inr (Or.inl rfl)⟩
  rw [r1, r2, r3, pb, px, py, pfSum_pair W c hxy.ne, pfSum_pair W c hby.ne,
    pfSum_pair W c hbx.ne]
  ring

end Small

section Four

variable {U : Type} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The weights with the pair `a, x` negated. -/
def twist (W : Sym2 (U × Fin 3) → F) (a x : U) : Sym2 (U × Fin 3) → F :=
  fun z => if Sym2.map Prod.fst z = s(a, x) then - W z else W z

omit [Fintype U] [LinearOrder U] in
theorem twist_eq_zero_iff (W : Sym2 (U × Fin 3) → F) (a x : U) (z : Sym2 (U × Fin 3)) :
    twist W a x z = 0 ↔ W z = 0 := by
  unfold twist
  split_ifs <;> simp

/-- **On four sites the signed matching sum is an unsigned one after one sign change.** -/
theorem pfSum_univ_eq_amplitude_twist (W : Sym2 (U × Fin 3) → F) {a b x y : U}
    (hab : a < b) (hbx : b < x) (hxy : x < y)
    (huniv : (Finset.univ : Finset U) = {a, b, x, y}) (col : U → Fin 3) :
    pfSum W col Finset.univ = amplitude (twist W a x) col := by
  have hax : a < x := hab.trans hbx
  have hay : a < y := hax.trans hxy
  have hby : b < y := hbx.trans hxy
  rw [← pmSum_univ, huniv, pfSum_four W col hab hbx hxy,
    pmSum_four _ col hab.ne hax.ne hay.ne hbx.ne hby.ne hxy.ne]
  have tw : ∀ u v : U, s(u, v) ≠ s(a, x) → twist W a x (Sym2.map (paint col) s(u, v))
      = W (Sym2.map (paint col) s(u, v)) := by
    intro u v h
    unfold twist
    rw [if_neg]
    simpa [Sym2.map_mk, paint] using h
  have tax : twist W a x (Sym2.map (paint col) s(a, x)) = - W (Sym2.map (paint col) s(a, x)) := by
    unfold twist
    rw [if_pos]
    simp [Sym2.map_mk, paint]
  have n1 : s(a, b) ≠ s(a, x) := fun h => hbx.ne (by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd h1 hax.ne)
  have n2 : s(x, y) ≠ s(a, x) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hax.ne' h1
    · exact hay.ne' h2
  have n3 : s(b, y) ≠ s(a, x) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hab.ne' h1
    · exact hbx.ne h1
  have n4 : s(a, y) ≠ s(a, x) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hxy.ne' h2
    · exact hax.ne h1
  have n5 : s(b, x) ≠ s(a, x) := fun h => by
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hab.ne' h1
    · exact hbx.ne h1
  rw [tw a b n1, tw x y n2, tw b y n3, tw a y n4, tw b x n5, tax]
  ring

/-- The four sites of a four-site linear order, in increasing order. -/
theorem exists_sorted_four (hU : Fintype.card U = 4) :
    ∃ a b x y : U, a < b ∧ b < x ∧ x < y ∧ (Finset.univ : Finset U) = {a, b, x, y} := by
  let e := Fintype.orderIsoFinOfCardEq U hU
  refine ⟨e 0, e 1, e 2, e 3, e.lt_iff_lt.mpr (by decide), e.lt_iff_lt.mpr (by decide),
    e.lt_iff_lt.mpr (by decide), ?_⟩
  ext z
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  obtain ⟨i, rfl⟩ := e.surjective z
  fin_cases i <;> simp

/-- A four-site fermionic GHZ system is a GHZ system after one sign change. -/
theorem isGHZOver_twist (hU : Fintype.card U = 4) {W : Sym2 (U × Fin 3) → F}
    (hW : IsFermiGHZ W) :
    ∃ a x : U, a ≠ x ∧ IsGHZOver (twist W a x) := by
  obtain ⟨a, b, x, y, hab, hbx, hxy, huniv⟩ := exists_sorted_four hU
  refine ⟨a, x, (hab.trans hbx).ne, fun k => ?_, fun c hc => ?_⟩
  · rw [← pfSum_univ_eq_amplitude_twist W hab hbx hxy huniv]; exact hW.1 k
  · rw [← pfSum_univ_eq_amplitude_twist W hab hbx hxy huniv]; exact hW.2 c hc

/-- **Four-site rigidity for fermionic systems.**  Over an infinite field the weights of a
four-site fermionic GHZ system vanish off the diagonal, and no pair carries two diagonal
colours. -/
theorem fourRigid_fermi [Infinite F] (hU : Fintype.card U = 4) {W : Sym2 (U × Fin 3) → F}
    (hW : IsFermiGHZ W) :
    (∀ u v : U, u ≠ v → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0) ∧
    (∀ u v : U, u ≠ v → ∀ a b : Fin 3, a ≠ b →
      W s((u, a), (v, a)) = 0 ∨ W s((u, b), (v, b)) = 0) := by
  obtain ⟨a, x, -, hG⟩ := isGHZOver_twist hU hW
  obtain ⟨h1, h2⟩ := (fourRigid : FourRigid F) U hU _ hG
  refine ⟨fun u v huv α β hαβ => (twist_eq_zero_iff W a x _).mp (h1 u v huv α β hαβ),
    fun u v huv α β hαβ => ?_⟩
  rcases h2 u v huv α β hαβ with h | h
  · exact Or.inl ((twist_eq_zero_iff W a x _).mp h)
  · exact Or.inr ((twist_eq_zero_iff W a x _).mp h)

/-- **The `K4` shape for fermionic systems.** -/
theorem k4_shape_fermi [Infinite F] (hU : Fintype.card U = 4) {W : Sym2 (U × Fin 3) → F}
    (hW : IsFermiGHZ W) {a b x y : U} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x)
    (hby : b ≠ y) (hxy : x ≠ y) (huniv : (Finset.univ : Finset U) = {a, b, x, y}) :
    ∃ π : Equiv.Perm (Fin 3),
      (W s((a, π 0), (b, π 0)) ≠ 0 ∧ W s((x, π 0), (y, π 0)) ≠ 0) ∧
      (W s((a, π 1), (x, π 1)) ≠ 0 ∧ W s((b, π 1), (y, π 1)) ≠ 0) ∧
      (W s((a, π 2), (y, π 2)) ≠ 0 ∧ W s((b, π 2), (x, π 2)) ≠ 0) := by
  obtain ⟨a', x', -, hG⟩ := isGHZOver_twist hU hW
  obtain ⟨π, ⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2, h2'⟩⟩ :=
    k4_shape fourRigid hU hG hab hax hay hbx hby hxy huniv
  have t := fun z (h : twist W a' x' z ≠ 0) => fun h' : W z = 0 => h ((twist_eq_zero_iff W a' x' z).mpr h')
  exact ⟨π, ⟨t _ h0, t _ h0'⟩, ⟨t _ h1, t _ h1'⟩, ⟨t _ h2, t _ h2'⟩⟩

end Four

section Pair

open MvPolynomial

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The colouring painting `p, q, u, v` with `c, d, a, b`. -/
def paintFour (p q u _v : V) (c d a b : Fin 3) : V → Fin 3 :=
  fun w => if w = p then c else if w = q then d else if w = u then a else b

/-- The signed matching sum of the four sites `p, q, u, v` painted `c, d, a, b`. -/
noncomputable def fourPtF (W : Sym2 (V × Fin 3) → F) (p q u v : V) (c d a b : Fin 3) : F :=
  pfSum W (paintFour p q u v c d a b) {p, q, u, v}

omit [Fintype V] [LinearOrder V] in
theorem paintFour_apply {p q u v : V} (hpq : p ≠ q) (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u)
    (hqv : q ≠ v) (huv : u ≠ v) (c d a b : Fin 3) :
    paintFour p q u v c d a b p = c ∧ paintFour p q u v c d a b q = d ∧
      paintFour p q u v c d a b u = a ∧ paintFour p q u v c d a b v = b := by
  unfold paintFour
  refine ⟨by simp, by simp [Ne.symm hpq], by simp [Ne.symm hpu, Ne.symm hqu],
    by simp [Ne.symm hpv, Ne.symm hqv, Ne.symm huv]⟩

omit [Fintype V] in
/-- A signed four-point sum depends only on the colours of its four sites. -/
theorem pfSum_eq_fourPtF (W : Sym2 (V × Fin 3) → F) {p q u v : V} (hpq : p ≠ q) (hpu : p ≠ u)
    (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v) (col : V → Fin 3) :
    pfSum W col {p, q, u, v} = fourPtF W p q u v (col p) (col q) (col u) (col v) := by
  unfold fourPtF
  obtain ⟨h1, h2, h3, h4⟩ := paintFour_apply hpq hpu hpv hqu hqv huv (col p) (col q) (col u) (col v)
  refine pfSum_congr_colour W fun w hw => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

/-- The polynomial of a contracted weight on the pair `uv`, in colours `a, b`. -/
noncomputable def pairPolyF (W : Sym2 (V × Fin 3) → F) (p q u v : V) (a b : Fin 3) :
    MvPolynomial (Fin 3 ⊕ Fin 3) F :=
  bil (fun c d => fourPtF W p q u v c d a b)

omit [Fintype V] in
/-- **Capping the pivots of a four-point signed sum gives the contracted weight**, up to a
sign. -/
theorem sum_cap_fourPtF (W : Sym2 (V × Fin 3) → F) {p q u v : V} (hpq : p ≠ q) (hpu : p ≠ u)
    (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v) (κ μ : Fin 3 → F)
    (hs : capVal W p q κ μ ≠ 0) (a b : Fin 3) :
    ∃ ε : F, ε ≠ 0 ∧ ∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b
      = ε * update W (profile W p κ) (profile W q μ) (capVal W p q κ μ) s((u, a), (v, b)) := by
  set col : V → Fin 3 := paintFour p q u v 0 0 a b with hcol
  have hcu : col u = a := (paintFour_apply hpq hpu hpv hqu hqv huv (0 : Fin 3) 0 a b).2.2.1
  have hcv : col v = b := (paintFour_apply hpq hpu hpv hqu hqv huv (0 : Fin 3) 0 a b).2.2.2
  have hp : p ∉ ({u, v} : Finset V) := by simp [hpu, hpv]
  have hq : q ∉ ({u, v} : Finset V) := by simp [hqu, hqv]
  have key := capVal_mul_pfSum_update_eq_cap W κ μ col hpq hp hq
  rw [pfSum_pair _ col huv] at key
  have hcard : ({u, v} : Finset V).card / 2 = 1 := by rw [Finset.card_pair huv]
  rw [hcard, pow_one] at key
  set σ : F := (-1) ^ (pos {u, v} p + pos {u, v} q + if q < p then 1 else 0) with hσ
  have hσ0 : σ ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← pow_add, ← two_mul, pow_mul]; norm_num
  refine ⟨σ, hσ0, ?_⟩
  have hcap : capPf W p q κ μ col {u, v} = ∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b := by
    unfold capPf
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    congr 1
    have hset : insert p (insert q ({u, v} : Finset V)) = {p, q, u, v} := rfl
    rw [hset, pfSum_eq_fourPtF W hpq hpu hpv hqu hqv huv, paintTwo_fst col hpq,
      paintTwo_snd col p q, paintTwo_other col (Ne.symm hpu) (Ne.symm hqu),
      paintTwo_other col (Ne.symm hpv) (Ne.symm hqv), hcu, hcv]
  have hup : update W (profile W p κ) (profile W q μ) (capVal W p q κ μ)
      (Sym2.map (paint col) s(u, v)) =
        update W (profile W p κ) (profile W q μ) (capVal W p q κ μ) s((u, a), (v, b)) := by
    show update _ _ _ _ s((u, col u), (v, col v)) = _
    rw [hcu, hcv]
  rw [hup, hcap] at key
  -- cancel the cap value and the sign
  have := mul_left_cancel₀ hs (key.trans (by ring : σ * capVal W p q κ μ *
    (∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b) = capVal W p q κ μ *
      (σ * ∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b)))
  calc ∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b
      = σ * σ * ∑ c, ∑ d, κ c * μ d * fourPtF W p q u v c d a b := by rw [hσσ, one_mul]
    _ = σ * update W (profile W p κ) (profile W q μ) (capVal W p q κ μ) s((u, a), (v, b)) := by
      rw [mul_assoc, ← this]

/-- **Rigidity at a valid cap, for fermionic systems.**  On six sites, at every cap where the cap
polynomial is nonzero, the contracted weights of a pair of the other four sites vanish off the
diagonal and on all but one diagonal colour.  No assumption on the characteristic. -/
theorem rigid_at_cap_fermi [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W) {p q : V} (hpq : p ≠ q)
    {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q) (huv : u ≠ v)
    (z : Fin 3 ⊕ Fin 3 → F) (hz : eval z (capPoly W p q) ≠ 0) :
    (∀ a b, a ≠ b → eval z (pairPolyF W p q u v a b) = 0) ∧
    (∀ a b, a ≠ b → eval z (pairPolyF W p q u v a a) = 0 ∨
      eval z (pairPolyF W p q u v b b) = 0) := by
  classical
  set κ : Fin 3 → F := fun k => z (Sum.inl k)
  set μ : Fin 3 → F := fun k => z (Sum.inr k)
  have hz' := hz
  rw [capPoly, map_mul, eval_bil] at hz'
  have hs0 : (∑ a, ∑ b, κ a * μ b * W s((p, a), (q, b))) ≠ 0 := left_ne_zero_of_mul hz'
  have hs : capVal W p q κ μ ≠ 0 := by
    unfold capVal orient
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hs0
  have hdiag : ∀ k, κ k * μ k ≠ 0 := by
    intro k
    have hprod := right_ne_zero_of_mul hz'
    rw [map_prod, Finset.prod_ne_zero_iff] at hprod
    simpa [κ, μ] using hprod k (Finset.mem_univ k)
  have hcard4 : Fintype.card ↥(rest p q) = 4 := by
    rw [Fintype.card_coe]
    have := card_rest (V := V) hpq
    omega
  have hG := isFermiGHZ_contract hW hpq (by omega) κ μ hs hdiag
  obtain ⟨hoff, hone⟩ := fourRigid_fermi hcard4 hG
  have hpu : p ≠ u := fun h => p_notMem_rest p q (h ▸ hu)
  have hpv : p ≠ v := fun h => p_notMem_rest p q (h ▸ hv)
  have hqu : q ≠ u := fun h => q_notMem_rest p q (h ▸ hu)
  have hqv : q ≠ v := fun h => q_notMem_rest p q (h ▸ hv)
  have hu'v' : (⟨u, hu⟩ : ↥(rest p q)) ≠ ⟨v, hv⟩ := fun h => huv (congrArg Subtype.val h)
  have hev : ∀ a b, ∃ ε : F, ε ≠ 0 ∧ eval z (pairPolyF W p q u v a b)
      = ε * contractW W p q κ μ s((⟨u, hu⟩, a), (⟨v, hv⟩, b)) := by
    intro a b
    obtain ⟨ε, hε, h⟩ := sum_cap_fourPtF W hpq hpu hpv hqu hqv huv κ μ hs a b
    exact ⟨ε, hε, by rw [pairPolyF, eval_bil]; exact h⟩
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨ε, -, h⟩ := hev a b
    rw [h, hoff _ _ hu'v' a b hab, mul_zero]
  · obtain ⟨ε, -, h⟩ := hev a a
    obtain ⟨ε', -, h'⟩ := hev b b
    rcases hone _ _ hu'v' a b hab with h0 | h0
    · left; rw [h, h0, mul_zero]
    · right; rw [h', h0, mul_zero]

/-- Every colouring of `p, q, u, v` with a nonzero signed sum paints `u` and `v` with `k`, and
some colouring has a nonzero sum. -/
def PinPairF (W : Sym2 (V × Fin 3) → F) (p q u v : V) (k : Fin 3) : Prop :=
  (∀ col : V → Fin 3, pfSum W col {p, q, u, v} ≠ 0 → col u = k ∧ col v = k) ∧
  ∃ col : V → Fin 3, pfSum W col {p, q, u, v} ≠ 0

/-- **From rigidity at every valid cap to pins, for fermionic systems.** -/
theorem pinPair_of_pairPolyF [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W) {p q : V} (hpq : p ≠ q)
    (hD : capPoly W p q ≠ 0) {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q)
    (huv : u ≠ v) {k : Fin 3} (hk : pairPolyF W p q u v k k ≠ 0) : PinPairF W p q u v k := by
  classical
  have hpu : p ≠ u := fun h => p_notMem_rest p q (h ▸ hu)
  have hpv : p ≠ v := fun h => p_notMem_rest p q (h ▸ hv)
  have hqu : q ≠ u := fun h => q_notMem_rest p q (h ▸ hu)
  have hqv : q ≠ v := fun h => q_notMem_rest p q (h ▸ hv)
  have hoff : ∀ a b, a ≠ b → pairPolyF W p q u v a b = 0 := fun a b hab =>
    eq_zero_of_eval_imp hD fun z hz => (rigid_at_cap_fermi hV hW hpq hu hv huv z hz).1 a b hab
  have hone : ∀ a b, a ≠ b → pairPolyF W p q u v a a = 0 ∨ pairPolyF W p q u v b b = 0 := by
    intro a b hab
    refine mul_eq_zero.mp (eq_zero_of_eval_imp hD fun z hz => ?_)
    rw [map_mul]
    rcases (rigid_at_cap_fermi hV hW hpq hu hv huv z hz).2 a b hab with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  refine ⟨fun col hcol => ?_, ?_⟩
  · rw [pfSum_eq_fourPtF W hpq hpu hpv hqu hqv huv] at hcol
    have hne : pairPolyF W p q u v (col u) (col v) ≠ 0 := fun h =>
      hcol ((bil_eq_zero_iff _).mp h _ _)
    have hcuv : col u = col v := by
      by_contra h
      exact hne (hoff _ _ h)
    rw [← hcuv] at hne
    have hck : col u = k := by
      by_contra h
      rcases hone _ _ h with h' | h'
      · exact hne h'
      · exact hk h'
    exact ⟨hck, hcuv ▸ hck⟩
  · obtain ⟨c, d, hcd⟩ : ∃ c d, fourPtF W p q u v c d k k ≠ 0 := by
      by_contra h
      push Not at h
      exact hk ((bil_eq_zero_iff _).mpr h)
    refine ⟨paintFour p q u v c d k k, ?_⟩
    rw [pfSum_eq_fourPtF W hpq hpu hpv hqu hqv huv]
    obtain ⟨h1, h2, h3, h4⟩ := paintFour_apply hpq hpu hpv hqu hqv huv c d k k
    rw [h1, h2, h3, h4]
    exact hcd

/-- **Rigidity at a live pair, for fermionic systems.**  On six sites, a live pair `pq` colours
the three perfect matchings of the other four sites bijectively, and each pair `uv` of such a
matching pins `u, v` to that colour in every nonzero signed four-point sum on `p, q, u, v`. -/
theorem rigid_pair_fermi [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsFermiGHZ W) {p q : V} (hpq : p ≠ q)
    (hlive : ∃ c d, W s((p, c), (q, d)) ≠ 0) {a b x y : V} (hab : a ≠ b) (hax : a ≠ x)
    (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hrest : rest p q = {a, b, x, y}) :
    ∃ π : Equiv.Perm (Fin 3),
      PinPairF W p q a b (π 0) ∧ PinPairF W p q x y (π 0) ∧
      PinPairF W p q a x (π 1) ∧ PinPairF W p q b y (π 1) ∧
      PinPairF W p q a y (π 2) ∧ PinPairF W p q b x (π 2) := by
  classical
  have hD := capPoly_ne_zero hlive
  obtain ⟨z, hz⟩ := exists_eval_ne_zero hD
  set κ : Fin 3 → F := fun k => z (Sum.inl k)
  set μ : Fin 3 → F := fun k => z (Sum.inr k)
  have hz' := hz
  rw [capPoly, map_mul, eval_bil] at hz'
  have hs0 : (∑ a, ∑ b, κ a * μ b * W s((p, a), (q, b))) ≠ 0 := left_ne_zero_of_mul hz'
  have hs : capVal W p q κ μ ≠ 0 := by
    unfold capVal orient
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hs0
  have hdiag : ∀ k, κ k * μ k ≠ 0 := by
    intro k
    have hprod := right_ne_zero_of_mul hz'
    rw [map_prod, Finset.prod_ne_zero_iff] at hprod
    simpa [κ, μ] using hprod k (Finset.mem_univ k)
  have hcard4 : Fintype.card ↥(rest p q) = 4 := by
    rw [Fintype.card_coe]
    have := card_rest (V := V) hpq
    omega
  have hG := isFermiGHZ_contract hW hpq (by omega) κ μ hs hdiag
  have ha : a ∈ rest p q := by rw [hrest]; simp
  have hb : b ∈ rest p q := by rw [hrest]; simp
  have hx : x ∈ rest p q := by rw [hrest]; simp
  have hy : y ∈ rest p q := by rw [hrest]; simp
  have huniv : (Finset.univ : Finset ↥(rest p q))
      = {⟨a, ha⟩, ⟨b, hb⟩, ⟨x, hx⟩, ⟨y, hy⟩} := by
    ext ⟨w, hw⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      true_iff]
    rw [hrest] at hw
    simpa using hw
  obtain ⟨π, ⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2', h2''⟩⟩ := k4_shape_fermi hcard4 hG
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (fun h => hab (congrArg Subtype.val h)) (fun h => hax (congrArg Subtype.val h))
    (fun h => hay (congrArg Subtype.val h)) (fun h => hbx (congrArg Subtype.val h))
    (fun h => hby (congrArg Subtype.val h)) (fun h => hxy (congrArg Subtype.val h)) huniv
  have hpoly : ∀ {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q) (huv : u ≠ v) (k : Fin 3),
      contractW W p q κ μ s((⟨u, hu⟩, k), (⟨v, hv⟩, k)) ≠ 0 →
      pairPolyF W p q u v k k ≠ 0 := by
    intro u v hu hv huv k hne h0
    have hpu : p ≠ u := fun h => p_notMem_rest p q (h ▸ hu)
    have hpv : p ≠ v := fun h => p_notMem_rest p q (h ▸ hv)
    have hqu : q ≠ u := fun h => q_notMem_rest p q (h ▸ hu)
    have hqv : q ≠ v := fun h => q_notMem_rest p q (h ▸ hv)
    obtain ⟨ε, hε, h⟩ := sum_cap_fourPtF W hpq hpu hpv hqu hqv huv κ μ hs k k
    apply hne
    have := congrArg (eval z) h0
    rw [map_zero, pairPolyF, eval_bil] at this
    rw [this] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hε
  exact ⟨π,
    pinPair_of_pairPolyF hV hW hpq hD ha hb hab (hpoly ha hb hab _ h0),
    pinPair_of_pairPolyF hV hW hpq hD hx hy hxy (hpoly hx hy hxy _ h0'),
    pinPair_of_pairPolyF hV hW hpq hD ha hx hax (hpoly ha hx hax _ h1),
    pinPair_of_pairPolyF hV hW hpq hD hb hy hby (hpoly hb hy hby _ h1'),
    pinPair_of_pairPolyF hV hW hpq hD ha hy hay (hpoly ha hy hay _ h2'),
    pinPair_of_pairPolyF hV hW hpq hD hb hx hbx (hpoly hb hx hbx _ h2'')⟩

end Pair

end KrennFermi

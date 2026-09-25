import Mathlib
import FermiRigidity
import CharTwoSix

/-!
# No six-site fermionic GHZ system

Read each atom of the six-site formula of `CharTwoSixCNF` as the statement it names about a
six-site fermionic GHZ system, with signed matching sums in place of unsigned ones.  Every clause
still holds:
- the witnesses come from expanding a constant signed sum at a site;
- the assignments come from rigidity at a live pair (`rigid_pair_fermi`);
- the remaining clauses hold by the meaning of the atoms alone.

The formula is unsatisfiable, so no six-site fermionic GHZ system exists over an infinite field.
This holds in every characteristic.
-/

namespace KrennFermi

open Amplitude MatchingSum MatchingPfaffian MatchingBlockRank KrennCharTwo SixCNF

variable {F : Type*} [Field F]

section Relabel

variable {V V' C R : Type*} [DecidableEq V] [LinearOrder V] [DecidableEq V'] [LinearOrder V']
  [CommRing R]

/-- **Signed matching sums are preserved by an order isomorphism of the sites.** -/
theorem pfSum_map_orderIso (W : Sym2 (V × C) → R) (e : V' ≃o V) (c : V → C) (T : Finset V') :
    pfSum W c (T.map e.toEquiv.toEmbedding)
      = pfSum (relabelW W e.toEquiv) (fun u => c (e u)) T := by
  set f : V' ↪ V := e.toEquiv.toEmbedding with hf
  have hfe : ∀ x, f x = e x := fun _ => rfl
  induction hn : T.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
  rcases T.eq_empty_or_nonempty with hT | hne
  · subst hT; simp
  set m := T.min' hne with hm
  have hmT : m ∈ T := T.min'_mem hne
  have hmin : ∀ w ∈ T, m ≤ w := fun w hw => Finset.min'_le T w hw
  have hmT' : f m ∈ T.map f := Finset.mem_map_of_mem _ hmT
  have hmin' : ∀ w ∈ T.map f, f m ≤ w := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hw
    rw [hfe, hfe]
    exact e.le_iff_le.mpr (hmin t ht)
  rw [pfSum_min W c hmT' hmin', pfSum_min _ _ hmT hmin, ← Finset.map_erase, Finset.sum_map]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hlt : ((T.erase m).erase v).card < n := by
    rw [← hn]
    exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hmT)
  have hpos : MatchingPfaffian.pos (T.map f) (f v) = MatchingPfaffian.pos T v := by
    unfold MatchingPfaffian.pos
    rw [← Finset.card_map f, Finset.filter_map]
    congr 2
    ext w
    simp only [Function.comp_apply, hfe, e.lt_iff_lt]
  rw [← Finset.map_erase, ih _ hlt _ rfl, hpos]
  rfl

end Relabel

section Atoms

variable (W : Sym2 (Fin 6 × Fin 3) → F)

/-- Some colouring of the four-site set `T` has a nonzero signed matching sum. -/
def IsAliveF (T : Nat) : Prop := ∃ col : Fin 6 → Fin 3, pfSum W col (set4 T) ≠ 0

/-- The constant colouring `d` of `T` has a nonzero signed matching sum. -/
def IsConstF (T d : Nat) : Prop := pfSum W (Amplitude.const (colr d)) (set4 T) ≠ 0

/-- Every colouring of `T` with a nonzero signed matching sum paints `v` with `c`. -/
def IsPinF (T v c : Nat) : Prop :=
  ∀ col : Fin 6 → Fin 3, pfSum W col (set4 T) ≠ 0 → col (site v) = colr c

/-- The edge `px` in colour `d` and the constant colouring `d` of the other four sites both
carry nonzero weight. -/
def IsWitnessF (p d x : Nat) : Prop :=
  W s((site p, colr d), (site x, colr d)) ≠ 0 ∧ IsConstF W (pairIdx p x) d

/-- The bijection `π` pins both pairs of every perfect matching of the complement of `f`. -/
def IsAssignF (f π : Nat) : Prop :=
  ∀ x ∈ (matchings f).zipIdx, ∀ eo ∈ [(x.1.1, x.1.2), (x.1.2, x.1.1)],
    IsAliveF W (pairIdx eo.2.1 eo.2.2) ∧
    IsPinF W (pairIdx eo.2.1 eo.2.2) eo.1.1 (permApply π x.2) ∧
    IsPinF W (pairIdx eo.2.1 eo.2.2) eo.1.2 (permApply π x.2)

/-- The valuation reading every atom as the statement it names. -/
def valF : Sat.Valuation := fun n =>
  if n < 15 then IsLive W n
  else if n < 105 then IsAssignF W ((n - 15) / 6) ((n - 15) % 6)
  else if n < 120 then IsAliveF W (n - 105)
  else if n < 165 then IsConstF W ((n - 120) / 3) ((n - 120) % 3)
  else if n < 435 then IsPinF W ((n - 165) / 18) ((n - 165) % 18 / 3) ((n - 165) % 3)
  else IsWitnessF W ((n - 435) / 18) ((n - 435) % 18 / 6) ((n - 435) % 6)

theorem valF_live {e : Nat} (he : e < 15) : valF W (live e) ↔ IsLive W e := by
  simp only [valF, live, if_pos he]

theorem valF_assign {f π : Nat} (hf : f < 15) (hπ : π < 6) :
    valF W (assign f π) ↔ IsAssignF W f π := by
  have h1 : ¬ 15 + 6 * f + π < 15 := by omega
  have h2 : 15 + 6 * f + π < 105 := by omega
  have h3 : (15 + 6 * f + π - 15) / 6 = f := by omega
  have h4 : (15 + 6 * f + π - 15) % 6 = π := by omega
  simp only [valF, assign, if_neg h1, if_pos h2, h3, h4]

theorem valF_alive {T : Nat} (hT : T < 15) : valF W (alive T) ↔ IsAliveF W T := by
  have h1 : ¬ 105 + T < 15 := by omega
  have h2 : ¬ 105 + T < 105 := by omega
  have h3 : 105 + T < 120 := by omega
  have h4 : 105 + T - 105 = T := by omega
  simp only [valF, alive, if_neg h1, if_neg h2, if_pos h3, h4]

theorem valF_const {T d : Nat} (hT : T < 15) (hd : d < 3) :
    valF W (SixCNF.const T d) ↔ IsConstF W T d := by
  have h1 : ¬ 120 + 3 * T + d < 15 := by omega
  have h2 : ¬ 120 + 3 * T + d < 105 := by omega
  have h3 : ¬ 120 + 3 * T + d < 120 := by omega
  have h4 : 120 + 3 * T + d < 165 := by omega
  have h5 : (120 + 3 * T + d - 120) / 3 = T := by omega
  have h6 : (120 + 3 * T + d - 120) % 3 = d := by omega
  simp only [valF, SixCNF.const, if_neg h1, if_neg h2, if_neg h3, if_pos h4, h5, h6]

theorem valF_pin {T v c : Nat} (hT : T < 15) (hv : v < 6) (hc : c < 3) :
    valF W (pin T v c) ↔ IsPinF W T v c := by
  have h1 : ¬ 165 + 18 * T + 3 * v + c < 15 := by omega
  have h2 : ¬ 165 + 18 * T + 3 * v + c < 105 := by omega
  have h3 : ¬ 165 + 18 * T + 3 * v + c < 120 := by omega
  have h4 : ¬ 165 + 18 * T + 3 * v + c < 165 := by omega
  have h5 : 165 + 18 * T + 3 * v + c < 435 := by omega
  have h6 : (165 + 18 * T + 3 * v + c - 165) / 18 = T := by omega
  have h7 : (165 + 18 * T + 3 * v + c - 165) % 18 / 3 = v := by omega
  have h8 : (165 + 18 * T + 3 * v + c - 165) % 3 = c := by omega
  simp only [valF, pin, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, h6, h7, h8]

theorem valF_witness {p d x : Nat} (hp : p < 6) (hd : d < 3) (hx : x < 6) :
    valF W (witness p d x) ↔ IsWitnessF W p d x := by
  have h1 : ¬ 435 + 18 * p + 6 * d + x < 15 := by omega
  have h2 : ¬ 435 + 18 * p + 6 * d + x < 105 := by omega
  have h3 : ¬ 435 + 18 * p + 6 * d + x < 120 := by omega
  have h4 : ¬ 435 + 18 * p + 6 * d + x < 165 := by omega
  have h5 : ¬ 435 + 18 * p + 6 * d + x < 435 := by omega
  have h6 : (435 + 18 * p + 6 * d + x - 435) / 18 = p := by omega
  have h7 : (435 + 18 * p + 6 * d + x - 435) % 18 / 6 = d := by omega
  have h8 : (435 + 18 * p + 6 * d + x - 435) % 6 = x := by omega
  simp only [valF, witness, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, h6, h7, h8]

end Atoms

section Clauses

variable (W : Sym2 (Fin 6 × Fin 3) → F)

theorem live_of_witnessF {p d x : Nat} (hp : p < 6) (hx : x < 6) (hpx : p ≠ x)
    (hw : IsWitnessF W p d x) : IsLive W (pairIdx p x) := by
  unfold IsLive
  rw [pairOf_pairIdx p hp x hx hpx]
  rcases le_total p x with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact ⟨_, _, hw.1⟩
  · rw [min_eq_right h, max_eq_left h]
    exact ⟨_, _, by rw [Sym2.eq_swap]; exact hw.1⟩

/-- Every site has a witness in every colour: expand the constant signed sum at the site. -/
theorem exists_witnessF {W : Sym2 (Fin 6 × Fin 3) → F} (hW : IsFermiGHZ W) {p d : Nat}
    (hp : p < 6) : ∃ x, x < 6 ∧ x ≠ p ∧ IsWitnessF W p d x := by
  have h0 := hW.1 (colr d)
  rw [pfSum_expand W _ (Finset.mem_univ (site p))] at h0
  obtain ⟨y, hy, hne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  have hyp : y ≠ site p := (Finset.mem_erase.mp hy).1
  have hne : y.val ≠ p := fun h => hyp (by rw [← site_val y, h])
  have hw : W s((site p, colr d), (y, colr d)) ≠ 0 := fun h => hne0 (by
    show _ * W s((site p, Amplitude.const (colr d) (site p)), (y, Amplitude.const (colr d) y)) * _ = 0
    simp only [Amplitude.const]
    rw [h, mul_zero, zero_mul])
  have hs : pfSum W (Amplitude.const (colr d)) ((Finset.univ.erase (site p)).erase y) ≠ 0 :=
    fun h => hne0 (by rw [h, mul_zero])
  refine ⟨y.val, y.isLt, hne, ?_, ?_⟩
  · rw [site_val]
    exact hw
  · unfold IsConstF
    rw [set4_pairIdx hp y.isLt (Ne.symm hne), site_val]
    exact hs

theorem sat_clausesA_F {W : Sym2 (Fin 6 × Fin 3) → F} (hW : IsFermiGHZ W) :
    ∀ c ∈ clausesA, (valF W).satisfies c := by
  intro c hc
  simp only [clausesA, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq] at hc
  obtain ⟨p, hp, d, hd, hc⟩ := hc
  rcases hc with ⟨x, ⟨hx, hxp⟩, hc | hc⟩ | hc
  · subst hc
    apply sat_imp
    intro hw
    rw [valF_witness W hp hd hx] at hw
    rw [valF_live W (pairIdx_lt p hp x hx (Ne.symm hxp))]
    exact live_of_witnessF W hp hx (Ne.symm hxp) hw
  · subst hc
    apply sat_imp
    intro hw
    rw [valF_witness W hp hd hx] at hw
    rw [valF_const W (pairIdx_lt p hp x hx (Ne.symm hxp)) hd]
    exact hw.2
  · subst hc
    obtain ⟨x, hx, hxp, hw⟩ := exists_witnessF (d := d) hW hp
    refine sat_of_pos_mem (n := witness p d x) ?_ ((valF_witness W hp hd hx).mpr hw)
    simp only [cl, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
    exact ⟨x, ⟨hx, hxp⟩, rfl⟩

theorem sat_clausesC_F : ∀ c ∈ clausesC, (valF W).satisfies c := by
  intro c hc
  simp only [clausesC, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map,
    List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq] at hc
  obtain ⟨T, hT, hc⟩ := hc
  rcases hc with ⟨d, hd, rfl⟩ | ⟨v, hv, hc⟩
  · apply sat_imp
    intro h
    rw [valF_const W hT hd] at h
    rw [valF_alive W hT]
    exact ⟨_, h⟩
  · have hv6 := compl_lt T hT v hv
    rcases hc with ⟨cc, hcc, rfl⟩ | ⟨c', hc3, d, ⟨hd3, hdc⟩, rfl⟩
    · rcases hcc with rfl | rfl | rfl <;>
      · apply sat_nand3
        intro ha h1 h2
        rw [valF_alive W hT] at ha
        rw [valF_pin W hT hv6 (by norm_num)] at h1 h2
        obtain ⟨col, hcol⟩ := ha
        exact absurd ((h1 col hcol).symm.trans (h2 col hcol)) (by decide)
    · apply sat_nand2
      intro h1 h2
      rw [valF_const W hT hd3] at h1
      rw [valF_pin W hT hv6 hc3] at h2
      exact hdc (colr_inj hd3 hc3 (h2 _ h1))

theorem pin_of_pinPairF {P Q : Fin 6} {u v k T : Nat} {κ : Fin 3}
    (h : PinPairF W P Q (site u) (site v) κ) (hT : set4 T = {P, Q, site u, site v})
    (hk : colr k = κ) : IsAliveF W T ∧ IsPinF W T u k ∧ IsPinF W T v k := by
  refine ⟨?_, fun col hcol => ?_, fun col hcol => ?_⟩
  · obtain ⟨col, hcol⟩ := h.2
    exact ⟨col, by rw [hT]; exact hcol⟩
  · rw [hT] at hcol
    rw [hk]
    exact (h.1 col hcol).1
  · rw [hT] at hcol
    rw [hk]
    exact (h.1 col hcol).2

/-- **A live pair has an assignment**, for fermionic systems. -/
theorem live_assignF [Infinite F] {W : Sym2 (Fin 6 × Fin 3) → F}
    (hW : IsFermiGHZ W) {f : Nat} (hf : f < 15) (hl : IsLive W f) :
    ∃ i, i < 6 ∧ IsAssignF W f i := by
  obtain ⟨a, b, c, d, hcompl, hPQ, hab, hac, had, hbc, hbd, hcd, hrest, h_cd, h_ab, h_bd,
    h_ac, h_bc, h_ad⟩ := good_data hf
  have hz : (matchings f).zipIdx
      = [(((a, b), (c, d)), 0), (((a, c), (b, d)), 1), (((a, d), (b, c)), 2)] := by
    simp only [matchings, hcompl]
    rfl
  obtain ⟨π, p0, p0', p1, p1', p2, p2'⟩ :=
    rigid_pair_fermi (Fintype.card_fin 6) hW hPQ hl hab hac had hbc hbd hcd hrest
  have hinj : ∀ {m n : Fin 3}, m ≠ n → π m ≠ π n := fun h e => h (π.injective e)
  obtain ⟨i, hi, hi0, hi1, hi2⟩ := exists_permIdx (π 0) (π 1) (π 2) (hinj (by decide))
    (hinj (by decide)) (hinj (by decide))
  have c0 : colr (permApply i 0) = π 0 := by rw [hi0, colr_val]
  have c1 : colr (permApply i 1) = π 1 := by rw [hi1, colr_val]
  have c2 : colr (permApply i 2) = π 2 := by rw [hi2, colr_val]
  refine ⟨i, hi, ?_⟩
  intro x hx eo heo
  rw [hz] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at heo <;>
    rcases heo with rfl | rfl
  · exact pin_of_pinPairF W p0 h_cd c0
  · exact pin_of_pinPairF W p0' h_ab c0
  · exact pin_of_pinPairF W p1 h_bd c1
  · exact pin_of_pinPairF W p1' h_ac c1
  · exact pin_of_pinPairF W p2 h_bc c2
  · exact pin_of_pinPairF W p2' h_ad c2

theorem sat_clausesB_F [Infinite F] {W : Sym2 (Fin 6 × Fin 3) → F}
    (hW : IsFermiGHZ W) : ∀ c ∈ clausesB, (valF W).satisfies c := by
  intro c hc
  simp only [clausesB, List.mem_flatMap, List.mem_range, List.mem_append,
    List.mem_singleton] at hc
  obtain ⟨f, hf, hc⟩ := hc
  rcases hc with ⟨π, hπ, ⟨⟨e1, e2⟩, m⟩, hx, hc⟩ | rfl
  · obtain ⟨h11, h12, h21, h22, hi1, hi2⟩ := matchings_ok f hf _ hx
    have hm3 := permApply_lt π m
    simp only [clausesBOne, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> apply sat_imp <;> intro ha <;>
      rw [valF_assign W hf hπ] at ha
    · rw [valF_alive W hi2]
      exact (ha _ hx (e1, e2) (by simp)).1
    · rw [valF_pin W hi2 h11 hm3]
      exact (ha _ hx (e1, e2) (by simp)).2.1
    · rw [valF_pin W hi2 h12 hm3]
      exact (ha _ hx (e1, e2) (by simp)).2.2
    · rw [valF_alive W hi1]
      exact (ha _ hx (e2, e1) (by simp)).1
    · rw [valF_pin W hi1 h21 hm3]
      exact (ha _ hx (e2, e1) (by simp)).2.1
    · rw [valF_pin W hi1 h22 hm3]
      exact (ha _ hx (e2, e1) (by simp)).2.2
  · by_cases hl : IsLive W f
    · obtain ⟨i, hi, ha⟩ := live_assignF hW hf hl
      refine sat_of_pos_mem (n := assign f i) ?_ ((valF_assign W hf hi).mpr ha)
      simp only [cl, List.mem_cons, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    · refine sat_of_neg_mem (n := live f) ?_ (by rw [valF_live W hf]; exact hl)
      exact List.mem_cons_self

end Clauses

/-- **No six-site fermionic GHZ system on `Fin 6`**, over any infinite field. -/
theorem no_isFermiGHZ_fin_six [Infinite F] (W : Sym2 (Fin 6 × Fin 3) → F) : ¬ IsFermiGHZ W := by
  intro hW
  refine sixFmla_unsat (valF W) fun c hc => ?_
  simp only [sixFmla, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact sat_clausesA_F hW c hc
  · exact sat_clausesB_F hW c hc
  · exact sat_clausesC_F W c hc

/-- **No six-site fermionic GHZ system**, over any infinite field and for any order of the
sites. -/
theorem no_isFermiGHZ_six [Infinite F] :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [LinearOrder V], Fintype.card V = 6 →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsFermiGHZ W := by
  intro V _ _ _ hV W hW
  let e : Fin 6 ≃o V := Fintype.orderIsoFinOfCardEq V hV
  have huniv : (Finset.univ : Finset (Fin 6)).map e.toEquiv.toEmbedding = Finset.univ := by
    ext v; simp
  have key : ∀ c : V → Fin 3,
      pfSum (relabelW W e.toEquiv) (fun u => c (e u)) Finset.univ = pfSum W c Finset.univ := by
    intro c
    rw [← pfSum_map_orderIso W e c, huniv]
  apply no_isFermiGHZ_fin_six (relabelW W e.toEquiv)
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · have := key (Amplitude.const k)
    rw [show (fun u : Fin 6 => Amplitude.const (V := V) k (e u)) = Amplitude.const k from rfl]
      at this
    rw [this]
    exact hW.1 k
  · have := key (fun v => c (e.symm v))
    simp only [OrderIso.symm_apply_apply] at this
    rw [this]
    apply hW.2
    rintro ⟨k, hk⟩
    exact hc ⟨k, fun u => by simpa using hk (e u)⟩

end KrennFermi

import Mathlib
import CharTwoRigidity
import CharTwoSixCNF

/-!
# No six-site GHZ system in characteristic two

Read each atom of the six-site formula of `CharTwoSixCNF` as the statement it names about a
six-site GHZ system over an infinite field of characteristic two.  Every clause then holds:
the witnesses come from expanding a constant amplitude at a site, the assignments from
rigidity at a live pair (`rigid_pair`), and the remaining clauses from the meaning of the
atoms alone.  The formula is unsatisfiable, so no such system exists.
-/

namespace KrennCharTwo

open Amplitude MatchingSum MatchingCharTwo SixCNF

variable {F : Type*} [Field F]

section Atoms

/-- The site with number `n`. -/
def site (n : Nat) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The colour with number `n`. -/
def colr (n : Nat) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The four sites outside the pair with index `T`. -/
def set4 (T : Nat) : Finset (Fin 6) := rest (site (pairOf T).1) (site (pairOf T).2)

theorem site_val (w : Fin 6) : site w.val = w := Fin.ext (Nat.mod_eq_of_lt w.isLt)

theorem colr_val (k : Fin 3) : colr k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)

theorem colr_inj {c d : Nat} (hc : c < 3) (hd : d < 3) (h : colr c = colr d) : c = d := by
  have := congrArg Fin.val h
  simpa [colr, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] using this

theorem rest_comm {V : Type*} [Fintype V] [DecidableEq V] (p q : V) : rest p q = rest q p :=
  Finset.erase_right_comm

variable (W : Sym2 (Fin 6 × Fin 3) → F)

/-- Some weight on the pair `e` is nonzero. -/
def IsLive (e : Nat) : Prop :=
  ∃ a b : Fin 3, W s((site (pairOf e).1, a), (site (pairOf e).2, b)) ≠ 0

/-- Some colouring of the four-site set `T` has a nonzero matching sum. -/
def IsAlive (T : Nat) : Prop := ∃ col : Fin 6 → Fin 3, pmSum W col (set4 T) ≠ 0

/-- The constant colouring `d` of `T` has a nonzero matching sum. -/
def IsConst (T d : Nat) : Prop := pmSum W (Amplitude.const (colr d)) (set4 T) ≠ 0

/-- Every colouring of `T` with a nonzero matching sum paints `v` with `c`. -/
def IsPin (T v c : Nat) : Prop :=
  ∀ col : Fin 6 → Fin 3, pmSum W col (set4 T) ≠ 0 → col (site v) = colr c

/-- The edge `px` in colour `d` and the constant colouring `d` of the other four sites both
carry nonzero weight. -/
def IsWitness (p d x : Nat) : Prop :=
  W s((site p, colr d), (site x, colr d)) ≠ 0 ∧ IsConst W (pairIdx p x) d

/-- The bijection `π` pins both pairs of every perfect matching of the complement of `f`,
each inside the four-site set it spans with `f`, to the matching's colour. -/
def IsAssign (f π : Nat) : Prop :=
  ∀ x ∈ (matchings f).zipIdx, ∀ eo ∈ [(x.1.1, x.1.2), (x.1.2, x.1.1)],
    IsAlive W (pairIdx eo.2.1 eo.2.2) ∧
    IsPin W (pairIdx eo.2.1 eo.2.2) eo.1.1 (permApply π x.2) ∧
    IsPin W (pairIdx eo.2.1 eo.2.2) eo.1.2 (permApply π x.2)

/-- The valuation reading every atom as the statement it names. -/
def val : Sat.Valuation := fun n =>
  if n < 15 then IsLive W n
  else if n < 105 then IsAssign W ((n - 15) / 6) ((n - 15) % 6)
  else if n < 120 then IsAlive W (n - 105)
  else if n < 165 then IsConst W ((n - 120) / 3) ((n - 120) % 3)
  else if n < 435 then IsPin W ((n - 165) / 18) ((n - 165) % 18 / 3) ((n - 165) % 3)
  else IsWitness W ((n - 435) / 18) ((n - 435) % 18 / 6) ((n - 435) % 6)

theorem val_live {e : Nat} (he : e < 15) : val W (live e) ↔ IsLive W e := by
  simp only [val, live, if_pos he]

theorem val_assign {f π : Nat} (hf : f < 15) (hπ : π < 6) :
    val W (assign f π) ↔ IsAssign W f π := by
  have h1 : ¬ 15 + 6 * f + π < 15 := by omega
  have h2 : 15 + 6 * f + π < 105 := by omega
  have h3 : (15 + 6 * f + π - 15) / 6 = f := by omega
  have h4 : (15 + 6 * f + π - 15) % 6 = π := by omega
  simp only [val, assign, if_neg h1, if_pos h2, h3, h4]

theorem val_alive {T : Nat} (hT : T < 15) : val W (alive T) ↔ IsAlive W T := by
  have h1 : ¬ 105 + T < 15 := by omega
  have h2 : ¬ 105 + T < 105 := by omega
  have h3 : 105 + T < 120 := by omega
  have h4 : 105 + T - 105 = T := by omega
  simp only [val, alive, if_neg h1, if_neg h2, if_pos h3, h4]

theorem val_const {T d : Nat} (hT : T < 15) (hd : d < 3) :
    val W (SixCNF.const T d) ↔ IsConst W T d := by
  have h1 : ¬ 120 + 3 * T + d < 15 := by omega
  have h2 : ¬ 120 + 3 * T + d < 105 := by omega
  have h3 : ¬ 120 + 3 * T + d < 120 := by omega
  have h4 : 120 + 3 * T + d < 165 := by omega
  have h5 : (120 + 3 * T + d - 120) / 3 = T := by omega
  have h6 : (120 + 3 * T + d - 120) % 3 = d := by omega
  simp only [val, SixCNF.const, if_neg h1, if_neg h2, if_neg h3, if_pos h4, h5, h6]

theorem val_pin {T v c : Nat} (hT : T < 15) (hv : v < 6) (hc : c < 3) :
    val W (pin T v c) ↔ IsPin W T v c := by
  have h1 : ¬ 165 + 18 * T + 3 * v + c < 15 := by omega
  have h2 : ¬ 165 + 18 * T + 3 * v + c < 105 := by omega
  have h3 : ¬ 165 + 18 * T + 3 * v + c < 120 := by omega
  have h4 : ¬ 165 + 18 * T + 3 * v + c < 165 := by omega
  have h5 : 165 + 18 * T + 3 * v + c < 435 := by omega
  have h6 : (165 + 18 * T + 3 * v + c - 165) / 18 = T := by omega
  have h7 : (165 + 18 * T + 3 * v + c - 165) % 18 / 3 = v := by omega
  have h8 : (165 + 18 * T + 3 * v + c - 165) % 3 = c := by omega
  simp only [val, pin, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5, h6, h7, h8]

theorem val_witness {p d x : Nat} (hp : p < 6) (hd : d < 3) (hx : x < 6) :
    val W (witness p d x) ↔ IsWitness W p d x := by
  have h1 : ¬ 435 + 18 * p + 6 * d + x < 15 := by omega
  have h2 : ¬ 435 + 18 * p + 6 * d + x < 105 := by omega
  have h3 : ¬ 435 + 18 * p + 6 * d + x < 120 := by omega
  have h4 : ¬ 435 + 18 * p + 6 * d + x < 165 := by omega
  have h5 : ¬ 435 + 18 * p + 6 * d + x < 435 := by omega
  have h6 : (435 + 18 * p + 6 * d + x - 435) / 18 = p := by omega
  have h7 : (435 + 18 * p + 6 * d + x - 435) % 18 / 6 = d := by omega
  have h8 : (435 + 18 * p + 6 * d + x - 435) % 6 = x := by omega
  simp only [val, witness, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, h6, h7, h8]

end Atoms

section Clauses

/-- A clause holds when one of its positive literals does. -/
theorem sat_of_pos_mem {v : Sat.Valuation} {c : List Sat.Literal} {n : Nat}
    (hm : Sat.Literal.pos n ∈ c) (hv : v n) : v.satisfies c := by
  induction c with
  | nil => simp at hm
  | cons l c ih =>
    show v.neg l → v.satisfies c
    intro hl
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact absurd hv hl
    · exact ih hm'

/-- A clause holds when one of its negative literals does. -/
theorem sat_of_neg_mem {v : Sat.Valuation} {c : List Sat.Literal} {n : Nat}
    (hm : Sat.Literal.neg n ∈ c) (hv : ¬ v n) : v.satisfies c := by
  induction c with
  | nil => simp at hm
  | cons l c ih =>
    show v.neg l → v.satisfies c
    intro hl
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact absurd hl hv
    · exact ih hm'

theorem sat_imp {v : Sat.Valuation} {a b : Nat} (h : v a → v b) :
    v.satisfies (cl [SixCNF.neg a, SixCNF.pos b]) :=
  fun ha hb => hb (h ha)

theorem sat_nand2 {v : Sat.Valuation} {a b : Nat} (h : v a → v b → False) :
    v.satisfies (cl [SixCNF.neg a, SixCNF.neg b]) :=
  h

theorem sat_nand3 {v : Sat.Valuation} {a b c : Nat} (h : v a → v b → v c → False) :
    v.satisfies (cl [SixCNF.neg a, SixCNF.neg b, SixCNF.neg c]) :=
  h

theorem pairIdx_lt : ∀ p < 6, ∀ x < 6, p ≠ x → pairIdx p x < 15 := by decide

theorem pairOf_pairIdx :
    ∀ p < 6, ∀ x < 6, p ≠ x → pairOf (pairIdx p x) = (min p x, max p x) := by decide

theorem compl_lt : ∀ T < 15, ∀ v ∈ SixCNF.compl T, v < 6 := by decide

theorem matchings_ok : ∀ f < 15, ∀ x ∈ (matchings f).zipIdx,
    x.1.1.1 < 6 ∧ x.1.1.2 < 6 ∧ x.1.2.1 < 6 ∧ x.1.2.2 < 6 ∧
    pairIdx x.1.1.1 x.1.1.2 < 15 ∧ pairIdx x.1.2.1 x.1.2.2 < 15 := by decide

theorem permApply_lt (π m : Nat) : permApply π m < 3 := by
  unfold permApply
  split <;> omega

theorem exists_permIdx : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∃ i < 6, permApply i 0 = a.val ∧ permApply i 1 = b.val ∧ permApply i 2 = c.val := by
  decide

theorem set4_pairIdx {p x : Nat} (hp : p < 6) (hx : x < 6) (hpx : p ≠ x) :
    set4 (pairIdx p x) = rest (site p) (site x) := by
  rw [set4, pairOf_pairIdx p hp x hx hpx]
  rcases le_total p x with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, rest_comm]

variable (W : Sym2 (Fin 6 × Fin 3) → F)

theorem live_of_witness {p d x : Nat} (hp : p < 6) (hx : x < 6) (hpx : p ≠ x)
    (hw : IsWitness W p d x) : IsLive W (pairIdx p x) := by
  unfold IsLive
  rw [pairOf_pairIdx p hp x hx hpx]
  rcases le_total p x with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact ⟨_, _, hw.1⟩
  · rw [min_eq_right h, max_eq_left h]
    exact ⟨_, _, by rw [Sym2.eq_swap]; exact hw.1⟩

/-- Every site has a witness in every colour: expand the constant amplitude at the site. -/
theorem exists_witness {W : Sym2 (Fin 6 × Fin 3) → F} (hW : IsGHZOver W) {p d : Nat}
    (hp : p < 6) : ∃ x, x < 6 ∧ x ≠ p ∧ IsWitness W p d x := by
  have h0 := hW.1 (colr d)
  rw [← pmSum_univ] at h0
  obtain ⟨y, hy, hw, hs⟩ := exists_partner_ne_zero W _ (Finset.mem_univ (site p)) h0
  have hyp : y ≠ site p := (Finset.mem_erase.mp hy).1
  have hne : y.val ≠ p := fun h => hyp (by rw [← site_val y, h])
  refine ⟨y.val, y.isLt, hne, ?_, ?_⟩
  · rw [site_val]
    exact hw
  · unfold IsConst
    rw [set4_pairIdx hp y.isLt (Ne.symm hne), site_val]
    exact hs

theorem sat_clausesA {W : Sym2 (Fin 6 × Fin 3) → F} (hW : IsGHZOver W) :
    ∀ c ∈ clausesA, (val W).satisfies c := by
  intro c hc
  simp only [clausesA, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq] at hc
  obtain ⟨p, hp, d, hd, hc⟩ := hc
  rcases hc with ⟨x, ⟨hx, hxp⟩, hc | hc⟩ | hc
  · subst hc
    apply sat_imp
    intro hw
    rw [val_witness W hp hd hx] at hw
    rw [val_live W (pairIdx_lt p hp x hx (Ne.symm hxp))]
    exact live_of_witness W hp hx (Ne.symm hxp) hw
  · subst hc
    apply sat_imp
    intro hw
    rw [val_witness W hp hd hx] at hw
    rw [val_const W (pairIdx_lt p hp x hx (Ne.symm hxp)) hd]
    exact hw.2
  · subst hc
    obtain ⟨x, hx, hxp, hw⟩ := exists_witness (d := d) hW hp
    refine sat_of_pos_mem (n := witness p d x) ?_ ((val_witness W hp hd hx).mpr hw)
    simp only [cl, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq]
    exact ⟨x, ⟨hx, hxp⟩, rfl⟩

theorem sat_clausesC : ∀ c ∈ clausesC, (val W).satisfies c := by
  intro c hc
  simp only [clausesC, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map,
    List.mem_filter, List.mem_cons, List.not_mem_nil, or_false, bne_iff_ne, ne_eq] at hc
  obtain ⟨T, hT, hc⟩ := hc
  rcases hc with ⟨d, hd, rfl⟩ | ⟨v, hv, hc⟩
  · apply sat_imp
    intro h
    rw [val_const W hT hd] at h
    rw [val_alive W hT]
    exact ⟨_, h⟩
  · have hv6 := compl_lt T hT v hv
    rcases hc with ⟨cc, hcc, rfl⟩ | ⟨c', hc3, d, ⟨hd3, hdc⟩, rfl⟩
    · rcases hcc with rfl | rfl | rfl <;>
      · apply sat_nand3
        intro ha h1 h2
        rw [val_alive W hT] at ha
        rw [val_pin W hT hv6 (by norm_num)] at h1 h2
        obtain ⟨col, hcol⟩ := ha
        exact absurd ((h1 col hcol).symm.trans (h2 col hcol)) (by decide)
    · apply sat_nand2
      intro h1 h2
      rw [val_const W hT hd3] at h1
      rw [val_pin W hT hv6 hc3] at h2
      exact hdc (colr_inj hd3 hc3 (h2 _ h1))

/-- The data of a pair index: its complement, listed in ascending order, spans the four-site
sets that the certificate reads. -/
def goodB (f : Nat) : Bool :=
  match SixCNF.compl f with
  | [a, b, c, d] =>
    decide (site (pairOf f).1 ≠ site (pairOf f).2) &&
    decide (site a ≠ site b) && decide (site a ≠ site c) && decide (site a ≠ site d) &&
    decide (site b ≠ site c) && decide (site b ≠ site d) && decide (site c ≠ site d) &&
    decide (rest (site (pairOf f).1) (site (pairOf f).2) = {site a, site b, site c, site d}) &&
    decide (set4 (pairIdx c d) = {site (pairOf f).1, site (pairOf f).2, site a, site b}) &&
    decide (set4 (pairIdx a b) = {site (pairOf f).1, site (pairOf f).2, site c, site d}) &&
    decide (set4 (pairIdx b d) = {site (pairOf f).1, site (pairOf f).2, site a, site c}) &&
    decide (set4 (pairIdx a c) = {site (pairOf f).1, site (pairOf f).2, site b, site d}) &&
    decide (set4 (pairIdx b c) = {site (pairOf f).1, site (pairOf f).2, site a, site d}) &&
    decide (set4 (pairIdx a d) = {site (pairOf f).1, site (pairOf f).2, site b, site c})
  | _ => false

theorem goodB_spec : ∀ f < 15, goodB f = true := by decide

theorem good_data {f : Nat} (hf : f < 15) :
    ∃ a b c d : Nat, SixCNF.compl f = [a, b, c, d] ∧
      site (pairOf f).1 ≠ site (pairOf f).2 ∧
      site a ≠ site b ∧ site a ≠ site c ∧ site a ≠ site d ∧
      site b ≠ site c ∧ site b ≠ site d ∧ site c ≠ site d ∧
      rest (site (pairOf f).1) (site (pairOf f).2) = {site a, site b, site c, site d} ∧
      set4 (pairIdx c d) = {site (pairOf f).1, site (pairOf f).2, site a, site b} ∧
      set4 (pairIdx a b) = {site (pairOf f).1, site (pairOf f).2, site c, site d} ∧
      set4 (pairIdx b d) = {site (pairOf f).1, site (pairOf f).2, site a, site c} ∧
      set4 (pairIdx a c) = {site (pairOf f).1, site (pairOf f).2, site b, site d} ∧
      set4 (pairIdx b c) = {site (pairOf f).1, site (pairOf f).2, site a, site d} ∧
      set4 (pairIdx a d) = {site (pairOf f).1, site (pairOf f).2, site b, site c} := by
  have h := goodB_spec f hf
  unfold goodB at h
  split at h
  · rename_i a b c d hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
    exact ⟨a, b, c, d, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  · exact absurd h (by simp)

theorem pin_of_pinPair {P Q : Fin 6} {u v k T : Nat} {κ : Fin 3}
    (h : PinPair W P Q (site u) (site v) κ) (hT : set4 T = {P, Q, site u, site v})
    (hk : colr k = κ) : IsAlive W T ∧ IsPin W T u k ∧ IsPin W T v k := by
  refine ⟨?_, fun col hcol => ?_, fun col hcol => ?_⟩
  · obtain ⟨col, hcol⟩ := h.2
    exact ⟨col, by rw [hT]; exact hcol⟩
  · rw [hT] at hcol
    rw [hk]
    exact (h.1 col hcol).1
  · rw [hT] at hcol
    rw [hk]
    exact (h.1 col hcol).2

/-- **A live pair has an assignment.**  Rigidity at the pair colours the three perfect
matchings of its complement bijectively, and pins each of their pairs. -/
theorem live_assign (h2 : (2 : F) = 0) [Infinite F] {W : Sym2 (Fin 6 × Fin 3) → F}
    (hW : IsGHZOver W) {f : Nat} (hf : f < 15) (hl : IsLive W f) :
    ∃ i, i < 6 ∧ IsAssign W f i := by
  obtain ⟨a, b, c, d, hcompl, hPQ, hab, hac, had, hbc, hbd, hcd, hrest, h_cd, h_ab, h_bd,
    h_ac, h_bc, h_ad⟩ := good_data hf
  have hz : (matchings f).zipIdx
      = [(((a, b), (c, d)), 0), (((a, c), (b, d)), 1), (((a, d), (b, c)), 2)] := by
    simp only [matchings, hcompl]
    rfl
  obtain ⟨π, p0, p0', p1, p1', p2, p2'⟩ :=
    rigid_pair h2 (Fintype.card_fin 6) hW hPQ hl hab hac had hbc hbd hcd hrest
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
  · exact pin_of_pinPair W p0 h_cd c0
  · exact pin_of_pinPair W p0' h_ab c0
  · exact pin_of_pinPair W p1 h_bd c1
  · exact pin_of_pinPair W p1' h_ac c1
  · exact pin_of_pinPair W p2 h_bc c2
  · exact pin_of_pinPair W p2' h_ad c2

theorem sat_clausesB (h2 : (2 : F) = 0) [Infinite F] {W : Sym2 (Fin 6 × Fin 3) → F}
    (hW : IsGHZOver W) : ∀ c ∈ clausesB, (val W).satisfies c := by
  intro c hc
  simp only [clausesB, List.mem_flatMap, List.mem_range, List.mem_append,
    List.mem_singleton] at hc
  obtain ⟨f, hf, hc⟩ := hc
  rcases hc with ⟨π, hπ, ⟨⟨e1, e2⟩, m⟩, hx, hc⟩ | rfl
  · obtain ⟨h11, h12, h21, h22, hi1, hi2⟩ := matchings_ok f hf _ hx
    have hm3 := permApply_lt π m
    simp only [clausesBOne, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;> apply sat_imp <;> intro ha <;>
      rw [val_assign W hf hπ] at ha
    · rw [val_alive W hi2]
      exact (ha _ hx (e1, e2) (by simp)).1
    · rw [val_pin W hi2 h11 hm3]
      exact (ha _ hx (e1, e2) (by simp)).2.1
    · rw [val_pin W hi2 h12 hm3]
      exact (ha _ hx (e1, e2) (by simp)).2.2
    · rw [val_alive W hi1]
      exact (ha _ hx (e2, e1) (by simp)).1
    · rw [val_pin W hi1 h21 hm3]
      exact (ha _ hx (e2, e1) (by simp)).2.1
    · rw [val_pin W hi1 h22 hm3]
      exact (ha _ hx (e2, e1) (by simp)).2.2
  · by_cases hl : IsLive W f
    · obtain ⟨i, hi, ha⟩ := live_assign h2 hW hf hl
      refine sat_of_pos_mem (n := assign f i) ?_ ((val_assign W hf hi).mpr ha)
      simp only [cl, List.mem_cons, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    · refine sat_of_neg_mem (n := live f) ?_ (by rw [val_live W hf]; exact hl)
      exact List.mem_cons_self

end Clauses

/-- **No six-site GHZ system on `Fin 6`** over an infinite field of characteristic two. -/
theorem no_isGHZOver_fin_six (h2 : (2 : F) = 0) [Infinite F]
    (W : Sym2 (Fin 6 × Fin 3) → F) : ¬ IsGHZOver W := by
  intro hW
  refine sixFmla_unsat (val W) fun c hc => ?_
  simp only [sixFmla, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact sat_clausesA hW c hc
  · exact sat_clausesB h2 hW c hc
  · exact sat_clausesC W c hc

/-- **No six-site GHZ system** over an infinite field of characteristic two. -/
theorem no_isGHZOver_six (h2 : (2 : F) = 0) [Infinite F] :
    ∀ (V : Type) [Fintype V] [DecidableEq V], Fintype.card V = 6 →
      ∀ W : Sym2 (V × Fin 3) → F, ¬ IsGHZOver W := by
  intro V _ _ hV W hW
  let e : Fin 6 ≃ V := (Fintype.equivFinOfCardEq hV).symm
  apply no_isGHZOver_fin_six h2 (relabelW W e)
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · have := amplitude_relabel W e (Amplitude.const k)
    rw [show (fun u : Fin 6 => Amplitude.const (V := V) k (e u)) = Amplitude.const k from rfl]
      at this
    rw [this]
    exact hW.1 k
  · have := amplitude_relabel W e (fun v => c (e.symm v))
    simp only [Equiv.symm_apply_apply] at this
    rw [this]
    apply hW.2
    rintro ⟨k, hk⟩
    exact hc ⟨k, fun u => by simpa using hk (e u)⟩

end KrennCharTwo

import Mathlib
import CharTwoDescent

/-!
# Four-site rigidity and its consequences

A three-colour GHZ system on four sites, over any infinite field, has a rigid shape: each
pair carries exactly one nonzero weight, on the diagonal, and the three perfect matchings
carry the three colours (`fourRigid`, `k4_shape`).  The reason is a determinant: capping
two sites with torus vectors `x, y` leaves an invertible diagonal matrix, equal to the
other pair's weights times the bilinear form `∑ x i * y j * W(u i, v j)` plus a matrix of
rank at most two, so that form never vanishes on the torus, and such a form has a single
nonzero entry.

On six sites in characteristic two, contracting a live pair produces four-site GHZ systems
for every valid cap.  The contracted weights are bilinear polynomials in the cap, so
rigidity at every valid cap becomes a statement about the four-point matching sums
themselves (`rigid_pair`): the live pair colours the matchings of its complement
bijectively, and pins every pair of them in every nonzero four-point sum.
-/

namespace KrennCharTwo

open Amplitude MatchingSum MatchingBlockRank MatchingCharTwo

variable {F : Type*} [Field F]

/-- **Four-site rigidity.**  On every four-site GHZ system the weights vanish off the
diagonal, and no pair carries two diagonal colours. -/
def FourRigid (F : Type*) [Field F] : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U], Fintype.card U = 4 →
    ∀ W : Sym2 (U × Fin 3) → F, IsGHZOver W →
      (∀ u v : U, u ≠ v → ∀ a b : Fin 3, a ≠ b → W s((u, a), (v, b)) = 0) ∧
      (∀ u v : U, u ≠ v → ∀ a b : Fin 3, a ≠ b →
        W s((u, a), (v, a)) = 0 ∨ W s((u, b), (v, b)) = 0)

section Four

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommRing R]

/-- **A four-site matching sum is the sum over the three perfect matchings.** -/
theorem pmSum_four (W : Sym2 (V × C) → R) (c : V → C) {a b x y : V}
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y) :
    pmSum W c {a, b, x, y}
      = W (Sym2.map (paint c) s(a, b)) * W (Sym2.map (paint c) s(x, y))
        + W (Sym2.map (paint c) s(a, x)) * W (Sym2.map (paint c) s(b, y))
        + W (Sym2.map (paint c) s(a, y)) * W (Sym2.map (paint c) s(b, x)) := by
  classical
  have ha : a ∈ ({a, b, x, y} : Finset V) := by simp
  rw [pmSum_expand W c ha]
  have herase : ({a, b, x, y} : Finset V).erase a = {b, x, y} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hza, hz⟩; rcases hz with rfl | rfl | rfl | rfl
      · exact absurd rfl hza
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨fun h => hab h.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨fun h => hax h.symm, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨fun h => hay h.symm, Or.inr (Or.inr (Or.inr rfl))⟩
  rw [herase]
  have hb : b ∉ ({x, y} : Finset V) := by simp [hbx, hby]
  have hx : x ∉ ({y} : Finset V) := by simp [hxy]
  rw [Finset.sum_insert hb, Finset.sum_insert hx, Finset.sum_singleton]
  have e1 : ({b, x, y} : Finset V).erase b = {x, y} := Finset.erase_insert hb
  have e2 : ({b, x, y} : Finset V).erase x = {b, y} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzx, hz⟩; rcases hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl hzx
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hbx, Or.inl rfl⟩
      · exact ⟨fun h => hxy h.symm, Or.inr (Or.inr rfl)⟩
  have e3 : ({b, x, y} : Finset V).erase y = {b, x} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzy, hz⟩; rcases hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hzy
    · rintro (rfl | rfl)
      · exact ⟨hby, Or.inl rfl⟩
      · exact ⟨hxy, Or.inr (Or.inl rfl)⟩
  rw [e1, e2, e3, pmSum_pair W c (Ne.symm hxy), pmSum_pair W c (Ne.symm hby),
    pmSum_pair W c (Ne.symm hbx), ← add_assoc]
  rfl

end Four

section Torus

/-- **A linear form with two nonzero coefficients vanishes on the torus.** -/
theorem exists_torus_zero [Infinite F] (ℓ : Fin 3 → F) {j j' : Fin 3} (hjj : j ≠ j')
    (hj : ℓ j ≠ 0) (hj' : ℓ j' ≠ 0) :
    ∃ y : Fin 3 → F, (∀ l, y l ≠ 0) ∧ ∑ l, ℓ l * y l = 0 := by
  classical
  have hsplit : ∀ z : Fin 3 → F, ∑ l, ℓ l * z l
      = ℓ j * z j + ℓ j' * z j' + (∑ l, ℓ l - ℓ j - ℓ j')
        + ∑ l, ℓ l * (if l = j ∨ l = j' then 0 else z l - 1) := by
    intro z
    fin_cases j <;> fin_cases j' <;> simp [Fin.sum_univ_three] at hjj ⊢ <;> ring
  -- the remaining coefficient
  obtain ⟨r, hr⟩ : ∃ r : F, r = ∑ l, ℓ l - ℓ j - ℓ j' := ⟨_, rfl⟩
  rw [← hr] at hsplit
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, -r / ℓ j} : Finset F)
  have ht0 : t ≠ 0 := fun h => ht (by simp [h])
  have ht1 : ℓ j * t + r ≠ 0 := by
    intro h
    apply ht
    have : t = -r / ℓ j := by
      field_simp
      linear_combination h
    simp [this]
  refine ⟨fun l => if l = j then t else if l = j' then -(ℓ j * t + r) / ℓ j' else 1, ?_, ?_⟩
  · intro l
    dsimp only
    split_ifs
    · exact ht0
    · exact div_ne_zero (neg_ne_zero.mpr ht1) hj'
    · exact one_ne_zero
  · rw [hsplit]
    have hz : ∑ l, ℓ l * ((if l = j ∨ l = j' then 0 else
        (if l = j then t else if l = j' then -(ℓ j * t + r) / ℓ j' else 1) - 1)) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h : l = j ∨ l = j'
      · rw [if_pos h, mul_zero]
      · push Not at h
        rw [if_neg (by tauto), if_neg h.1, if_neg h.2, sub_self, mul_zero]
    rw [hz, add_zero, if_pos rfl, if_neg (Ne.symm hjj), if_pos rfl]
    field_simp
    ring

/-- **Two nonzero linear forms are simultaneously nonzero on the torus.** -/
theorem exists_torus_ne_zero [Infinite F] (w w' : Fin 3 → F) (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∃ x : Fin 3 → F, (∀ i, x i ≠ 0) ∧ ∑ i, x i * w i ≠ 0 ∧ ∑ i, x i * w' i ≠ 0 := by
  classical
  let L : (Fin 3 → F) → Polynomial F := fun v =>
    Polynomial.C (v 0) + Polynomial.C (v 1) * Polynomial.X
      + Polynomial.C (v 2) * Polynomial.X ^ 2
  have hL : ∀ v : Fin 3 → F, v ≠ 0 → L v ≠ 0 := by
    intro v hv h
    apply hv
    have h0 := congrArg (fun f => Polynomial.coeff f 0) h
    have h1 := congrArg (fun f => Polynomial.coeff f 1) h
    have h2 := congrArg (fun f => Polynomial.coeff f 2) h
    simp [L, Polynomial.coeff_X_pow, Polynomial.coeff_X] at h0 h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hev : ∀ (v : Fin 3 → F) (t : F), (L v).eval t = ∑ i, ![1, t, t ^ 2] i * v i := by
    intro v t
    simp [L, Fin.sum_univ_three]
    ring
  let P := Polynomial.X * L w * L w'
  have hP : P ≠ 0 := mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero (hL w hw)) (hL w' hw')
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset P.roots.toFinset
  have hPt : P.eval t ≠ 0 := fun h =>
    ht (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr h))
  simp only [P, Polynomial.eval_mul, Polynomial.eval_X] at hPt
  have ht0 : t ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hPt)
  refine ⟨![1, t, t ^ 2], fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> simp [ht0]
  · rw [← hev]; exact right_ne_zero_of_mul (left_ne_zero_of_mul hPt)
  · rw [← hev]; exact right_ne_zero_of_mul hPt

/-- Two nonzero entries of a bilinear form that never vanishes on the torus share a column. -/
theorem col_eq_of_torus_ne_zero [Infinite F] (M : Fin 3 → Fin 3 → F)
    (h : ∀ x y : Fin 3 → F, (∀ i, x i ≠ 0) → (∀ j, y j ≠ 0) →
      ∑ i, ∑ j, x i * y j * M i j ≠ 0)
    {i j i' j' : Fin 3} (h1 : M i j ≠ 0) (h2 : M i' j' ≠ 0) : j = j' := by
  by_contra hjj
  have hw : (fun a => M a j) ≠ 0 := fun h0 => h1 (congrFun h0 i)
  have hw' : (fun a => M a j') ≠ 0 := fun h0 => h2 (congrFun h0 i')
  obtain ⟨x, hx, hxj, hxj'⟩ := exists_torus_ne_zero _ _ hw hw'
  obtain ⟨y, hy, hzero⟩ := exists_torus_zero (fun l => ∑ a, x a * M a l) hjj hxj hxj'
  apply h x y hx hy
  rw [← hzero]
  simp only [Fin.sum_univ_three]
  ring

/-- **A bilinear form that never vanishes on the torus has a single nonzero entry.** -/
theorem eq_of_torus_ne_zero [Infinite F] (M : Fin 3 → Fin 3 → F)
    (h : ∀ x y : Fin 3 → F, (∀ i, x i ≠ 0) → (∀ j, y j ≠ 0) →
      ∑ i, ∑ j, x i * y j * M i j ≠ 0)
    {i j i' j' : Fin 3} (h1 : M i j ≠ 0) (h2 : M i' j' ≠ 0) : i = i' ∧ j = j' := by
  refine ⟨?_, col_eq_of_torus_ne_zero M h h1 h2⟩
  refine col_eq_of_torus_ne_zero (fun b a => M a b) (fun y x hy hx => ?_) h1 h2
  have := h x y hx hy
  intro h0
  apply this
  rw [← h0]
  simp only [Fin.sum_univ_three]
  ring

end Torus

/-- **A matrix of rank at most two is not an invertible diagonal.**  If
`P a * Q b + R a * S b` is diagonal with entries `d`, then `d 0 * d 1 * d 2 = 0`. -/
theorem rank_two_diag {P Q R S d : Fin 3 → F}
    (h : ∀ a b, P a * Q b + R a * S b = if a = b then d a else 0) : d 0 * d 1 * d 2 = 0 := by
  have hM : (Matrix.of fun a b => P a * Q b + R a * S b) = Matrix.diagonal d := by
    ext a b
    simp [Matrix.diagonal_apply, h a b]
  have h0 : (Matrix.of fun a b => P a * Q b + R a * S b).det = 0 := by
    simp [Matrix.det_fin_three]
    ring
  rw [hM, Matrix.det_diagonal, Fin.prod_univ_three] at h0
  exact h0

section K4

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The two sites of a four-site set outside a given pair. -/
theorem exists_compl_of_card_four (hU : Fintype.card U = 4) {u v : U} (huv : u ≠ v) :
    ∃ p q : U, u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q ∧ p ≠ q ∧
      (Finset.univ : Finset U) = {u, v, p, q} := by
  classical
  have hc := card_rest (V := U) huv
  rw [hU] at hc
  obtain ⟨p, q, hpq, hr⟩ := Finset.card_eq_two.mp (by omega : (rest u v).card = 2)
  have hp : p ∈ rest u v := by rw [hr]; simp
  have hq : q ∈ rest u v := by rw [hr]; simp
  simp only [rest, Finset.mem_erase, Finset.mem_univ, and_true] at hp hq
  refine ⟨p, q, fun h => hp.2 h.symm, fun h => hq.2 h.symm, fun h => hp.1 h.symm,
    fun h => hq.1 h.symm, hpq, ?_⟩
  rw [← insert_insert_rest u v, hr]

/-- **The pair form never vanishes on the torus.**  Capping two sites of a four-site GHZ
system with torus vectors `x, y` leaves the pair form of the other two, times the pair's
bilinear form `∑ x i * y j * W(u i, v j)`, plus a matrix of rank at most two; since the
capped system is an invertible diagonal, the bilinear form cannot vanish. -/
theorem bilinear_ne_zero_of_isGHZ {W : Sym2 (U × Fin 3) → F} (hW : IsGHZOver W)
    {u v p q : U} (huv : u ≠ v) (hup : u ≠ p) (huq : u ≠ q) (hvp : v ≠ p) (hvq : v ≠ q)
    (hpq : p ≠ q) (huniv : (Finset.univ : Finset U) = {u, v, p, q})
    (x y : Fin 3 → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ j, y j ≠ 0) :
    ∑ i, ∑ j, x i * y j * W s((u, i), (v, j)) ≠ 0 := by
  classical
  intro hβ
  -- the colouring painting `p, q, u, v` with `a, b, i, j`
  let col : Fin 3 → Fin 3 → Fin 3 → Fin 3 → U → Fin 3 := fun a b i j w =>
    if w = p then a else if w = q then b else if w = u then i else j
  have hcp : ∀ a b i j, col a b i j p = a := by intro a b i j; simp [col]
  have hcq : ∀ a b i j, col a b i j q = b := by intro a b i j; simp [col, Ne.symm hpq]
  have hcu : ∀ a b i j, col a b i j u = i := by intro a b i j; simp [col, hup, huq]
  have hcv : ∀ a b i j, col a b i j v = j := by
    intro a b i j; simp [col, hvp, hvq, Ne.symm huv]
  have huniv' : (Finset.univ : Finset U) = {p, q, u, v} := by
    rw [huniv]; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hexp : ∀ a b i j, amplitude W (col a b i j)
      = W s((p, a), (q, b)) * W s((u, i), (v, j)) + W s((p, a), (u, i)) * W s((q, b), (v, j))
        + W s((p, a), (v, j)) * W s((q, b), (u, i)) := by
    intro a b i j
    rw [← pmSum_univ, huniv', pmSum_four W _ hpq (Ne.symm hup) (Ne.symm hvp) (Ne.symm huq)
      (Ne.symm hvq) huv]
    simp only [Sym2.map_mk, paint, hcp, hcq, hcu, hcv]
  have hghz : ∀ a b i j, amplitude W (col a b i j)
      = if a = b ∧ b = i ∧ i = j then amplitude W (Amplitude.const (V := U) a) else 0 := by
    intro a b i j
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      congr 1
      funext w
      simp only [col, Amplitude.const]
      split_ifs <;> rfl
    · apply hW.2
      rintro ⟨k, hk⟩
      apply h
      have e1 := hk p
      have e2 := hk q
      have e3 := hk u
      have e4 := hk v
      rw [hcp] at e1
      rw [hcq] at e2
      rw [hcu] at e3
      rw [hcv] at e4
      exact ⟨e1.trans e2.symm, e2.trans e3.symm, e3.trans e4.symm⟩
  -- the capped system, read two ways
  have hrank : ∀ a b, (∑ i, x i * W s((p, a), (u, i))) * (∑ j, y j * W s((q, b), (v, j)))
      + (∑ j, y j * W s((p, a), (v, j))) * (∑ i, x i * W s((q, b), (u, i)))
      = if a = b then x a * y a * amplitude W (Amplitude.const (V := U) a) else 0 := by
    intro a b
    have hsum : ∑ i, ∑ j, x i * y j * amplitude W (col a b i j)
        = (∑ i, x i * W s((p, a), (u, i))) * (∑ j, y j * W s((q, b), (v, j)))
          + (∑ j, y j * W s((p, a), (v, j))) * (∑ i, x i * W s((q, b), (u, i))) := by
      simp only [hexp]
      simp only [Fin.sum_univ_three] at hβ ⊢
      linear_combination W s((p, a), (q, b)) * hβ
    rw [← hsum]
    simp only [hghz]
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three]
  have hd := rank_two_diag hrank
  have hne : ∀ a, x a * y a * amplitude W (Amplitude.const (V := U) a) ≠ 0 :=
    fun a => mul_ne_zero (mul_ne_zero (hx a) (hy a)) (hW.1 a)
  exact mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2) hd

/-- **Each pair carries a single nonzero weight.** -/
theorem single_weight_of_isGHZ [Infinite F] (hU : Fintype.card U = 4)
    {W : Sym2 (U × Fin 3) → F} (hW : IsGHZOver W) {u v : U} (huv : u ≠ v)
    {a b a' b' : Fin 3} (h1 : W s((u, a), (v, b)) ≠ 0) (h2 : W s((u, a'), (v, b')) ≠ 0) :
    a = a' ∧ b = b' := by
  obtain ⟨p, q, hup, huq, hvp, hvq, hpq, huniv⟩ := exists_compl_of_card_four hU huv
  exact eq_of_torus_ne_zero (fun i j => W s((u, i), (v, j)))
    (bilinear_ne_zero_of_isGHZ hW huv hup huq hvp hvq hpq huniv) h1 h2

/-- **Four-site rigidity holds over every infinite field.** -/
theorem fourRigid [Infinite F] : FourRigid F := by
  intro U _ _ hU W hW
  have hone := fun {u v : U} (huv : u ≠ v) {a b a' b' : Fin 3} =>
    single_weight_of_isGHZ (a := a) (b := b) (a' := a') (b' := b') hU hW huv
  refine ⟨fun u v huv a b hab => ?_, fun u v huv a b hab => ?_⟩
  · by_contra hw
    obtain ⟨p, q, hup, huq, hvp, hvq, hpq, huniv⟩ := exists_compl_of_card_four hU huv
    -- the pair `uv` carries no diagonal weight, so each colour uses another matching
    have hk : ∀ k : Fin 3,
        (W s((u, k), (p, k)) ≠ 0 ∧ W s((v, k), (q, k)) ≠ 0) ∨
        (W s((u, k), (q, k)) ≠ 0 ∧ W s((v, k), (p, k)) ≠ 0) := by
      intro k
      have hdiag : W s((u, k), (v, k)) = 0 := by
        by_contra hd
        exact hab ((hone huv hw hd).1.trans (hone huv hw hd).2.symm)
      have h := hW.1 k
      rw [← pmSum_univ, huniv, pmSum_four W _ huv hup huq hvp hvq hpq] at h
      change W s((u, k), (v, k)) * W s((p, k), (q, k)) + W s((u, k), (p, k)) * W s((v, k), (q, k))
        + W s((u, k), (q, k)) * W s((v, k), (p, k)) ≠ 0 at h
      rw [hdiag, zero_mul, zero_add] at h
      by_contra hcon
      push Not at hcon
      apply h
      have e1 : W s((u, k), (p, k)) * W s((v, k), (q, k)) = 0 := by
        by_cases hz : W s((u, k), (p, k)) = 0
        · rw [hz, zero_mul]
        · rw [hcon.1 hz, mul_zero]
      have e2 : W s((u, k), (q, k)) * W s((v, k), (p, k)) = 0 := by
        by_cases hz : W s((u, k), (q, k)) = 0
        · rw [hz, zero_mul]
        · rw [hcon.2 hz, mul_zero]
      rw [e1, e2, add_zero]
    -- three colours, two matchings: two colours share a pair
    rcases hk 0 with h0 | h0 <;> rcases hk 1 with h1 | h1 <;> rcases hk 2 with h2 | h2 <;>
    first
    | exact absurd (hone hup h0.1 h1.1).1 (by decide)
    | exact absurd (hone hup h0.1 h2.1).1 (by decide)
    | exact absurd (hone hup h1.1 h2.1).1 (by decide)
    | exact absurd (hone huq h0.1 h1.1).1 (by decide)
    | exact absurd (hone huq h0.1 h2.1).1 (by decide)
    | exact absurd (hone huq h1.1 h2.1).1 (by decide)
  · by_contra hcon
    push Not at hcon
    exact hab (hone huv hcon.1 hcon.2).1

/-- On a four-site GHZ system, each constant colour has a perfect matching both of whose
pairs carry that colour. -/
theorem exists_live_matching {W : Sym2 (U × Fin 3) → F} (hW : IsGHZOver W)
    {a b x y : U} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hxy : x ≠ y) (huniv : (Finset.univ : Finset U) = {a, b, x, y}) (k : Fin 3) :
    (W s((a, k), (b, k)) ≠ 0 ∧ W s((x, k), (y, k)) ≠ 0) ∨
    (W s((a, k), (x, k)) ≠ 0 ∧ W s((b, k), (y, k)) ≠ 0) ∨
    (W s((a, k), (y, k)) ≠ 0 ∧ W s((b, k), (x, k)) ≠ 0) := by
  have h := hW.1 k
  rw [← pmSum_univ, huniv, pmSum_four W _ hab hax hay hbx hby hxy] at h
  change W s((a, k), (b, k)) * W s((x, k), (y, k)) + W s((a, k), (x, k)) * W s((b, k), (y, k))
    + W s((a, k), (y, k)) * W s((b, k), (x, k)) ≠ 0 at h
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply h
  have e1 : W s((a, k), (b, k)) * W s((x, k), (y, k)) = 0 := by
    by_cases hz : W s((a, k), (b, k)) = 0
    · rw [hz, zero_mul]
    · rw [h1 hz, mul_zero]
  have e2 : W s((a, k), (x, k)) * W s((b, k), (y, k)) = 0 := by
    by_cases hz : W s((a, k), (x, k)) = 0
    · rw [hz, zero_mul]
    · rw [h2 hz, mul_zero]
  have e3 : W s((a, k), (y, k)) * W s((b, k), (x, k)) = 0 := by
    by_cases hz : W s((a, k), (y, k)) = 0
    · rw [hz, zero_mul]
    · rw [h3 hz, mul_zero]
  rw [e1, e2, e3]; ring

/-- **The K4 shape.**  Under four-site rigidity, the three perfect matchings of a four-site
GHZ system carry the three colours: there is a bijection `π` from the matchings `ab|xy`,
`ax|by`, `ay|bx` (in that order) onto the colours, and each pair is live in its matching's
colour. -/
theorem k4_shape (hrig : FourRigid F) (hU : Fintype.card U = 4) {W : Sym2 (U × Fin 3) → F}
    (hW : IsGHZOver W) {a b x y : U} (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x)
    (hby : b ≠ y) (hxy : x ≠ y) (huniv : (Finset.univ : Finset U) = {a, b, x, y}) :
    ∃ π : Equiv.Perm (Fin 3),
      (W s((a, π 0), (b, π 0)) ≠ 0 ∧ W s((x, π 0), (y, π 0)) ≠ 0) ∧
      (W s((a, π 1), (x, π 1)) ≠ 0 ∧ W s((b, π 1), (y, π 1)) ≠ 0) ∧
      (W s((a, π 2), (y, π 2)) ≠ 0 ∧ W s((b, π 2), (x, π 2)) ≠ 0) := by
  classical
  obtain ⟨-, hone⟩ := hrig U hU W hW
  -- the matching index serving each colour
  have hm : ∀ k : Fin 3, ∃ m : Fin 3,
      (m = 0 ∧ W s((a, k), (b, k)) ≠ 0 ∧ W s((x, k), (y, k)) ≠ 0) ∨
      (m = 1 ∧ W s((a, k), (x, k)) ≠ 0 ∧ W s((b, k), (y, k)) ≠ 0) ∨
      (m = 2 ∧ W s((a, k), (y, k)) ≠ 0 ∧ W s((b, k), (x, k)) ≠ 0) := by
    intro k
    rcases exists_live_matching hW hab hax hay hbx hby hxy huniv k with h | h | h
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨1, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · exact ⟨2, Or.inr (Or.inr ⟨rfl, h⟩)⟩
  choose g hg using hm
  -- two colours never share a matching: a pair cannot be live in two colours
  have hinj : Function.Injective g := by
    intro k k' hkk
    by_contra hne
    rcases hg k with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ <;>
    rcases hg k' with ⟨h0', h1', -⟩ | ⟨h0', h1', -⟩ | ⟨h0', h1', -⟩ <;>
    first
    | (exfalso; rw [h0, h0'] at hkk; exact absurd hkk (by decide))
    | (rcases hone a b hab k k' hne with hz | hz <;> contradiction)
    | (rcases hone a x hax k k' hne with hz | hz <;> contradiction)
    | (rcases hone a y hay k k' hne with hz | hz <;> contradiction)
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective g ((Finite.injective_iff_bijective).mp hinj)
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · have := hg (e.symm 0)
    have he : g (e.symm 0) = 0 := e.apply_symm_apply 0
    rcases this with ⟨_, h⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
    · exact h
    · rw [he] at h0; exact absurd h0 (by decide)
    · rw [he] at h0; exact absurd h0 (by decide)
  · have := hg (e.symm 1)
    have he : g (e.symm 1) = 1 := e.apply_symm_apply 1
    rcases this with ⟨h0, _⟩ | ⟨_, h⟩ | ⟨h0, _⟩
    · rw [he] at h0; exact absurd h0 (by decide)
    · exact h
    · rw [he] at h0; exact absurd h0 (by decide)
  · have := hg (e.symm 2)
    have he : g (e.symm 2) = 2 := e.apply_symm_apply 2
    rcases this with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h⟩
    · rw [he] at h0; exact absurd h0 (by decide)
    · rw [he] at h0; exact absurd h0 (by decide)
    · exact h

end K4

section Poly

open MvPolynomial

/-- The bilinear polynomial `∑ κ a * μ b * H a b`, in the cap variables `κ` (left copy of
`Fin 3`) and `μ` (right copy). -/
noncomputable def bil (H : Fin 3 → Fin 3 → F) : MvPolynomial (Fin 3 ⊕ Fin 3) F :=
  ∑ a, ∑ b, X (Sum.inl a) * X (Sum.inr b) * MvPolynomial.C (H a b)

theorem eval_bil (H : Fin 3 → Fin 3 → F) (z : Fin 3 ⊕ Fin 3 → F) :
    eval z (bil H) = ∑ a, ∑ b, z (Sum.inl a) * z (Sum.inr b) * H a b := by
  simp [bil]

/-- A bilinear polynomial vanishes exactly when all its coefficients do: evaluate at the
unit caps. -/
theorem bil_eq_zero_iff (H : Fin 3 → Fin 3 → F) : bil H = 0 ↔ ∀ a b, H a b = 0 := by
  constructor
  · intro h a b
    have := congrArg (eval (Sum.elim (fun c => if c = a then (1 : F) else 0)
      (fun d => if d = b then (1 : F) else 0))) h
    rw [eval_bil, map_zero] at this
    fin_cases a <;> fin_cases b <;> simpa [Fin.sum_univ_three] using this
  · intro h
    simp [bil, h]

/-- A nonzero polynomial over an infinite field is nonzero somewhere. -/
theorem exists_eval_ne_zero [Infinite F] {σ : Type*} {P : MvPolynomial σ F} (hP : P ≠ 0) :
    ∃ z, eval z P ≠ 0 := by
  by_contra h
  push Not at h
  exact hP (MvPolynomial.funext fun z => by rw [h z, map_zero])

/-- A polynomial vanishing wherever a nonzero polynomial does not is zero. -/
theorem eq_zero_of_eval_imp [Infinite F] {σ : Type*} {D P : MvPolynomial σ F} (hD : D ≠ 0)
    (h : ∀ z, eval z D ≠ 0 → eval z P = 0) : P = 0 := by
  have hDP : D * P = 0 := MvPolynomial.funext fun z => by
    rw [map_mul, map_zero]
    by_cases hz : eval z D = 0
    · rw [hz, zero_mul]
    · rw [h z hz, mul_zero]
  exact (mul_eq_zero.mp hDP).resolve_left hD

end Poly

section Pair

open MvPolynomial

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The matching sum of the four sites `p, q, u, v` painted `c, d, a, b`. -/
def fourPt (W : Sym2 (V × Fin 3) → F) (p q u v : V) (c d a b : Fin 3) : F :=
  W s((p, c), (q, d)) * W s((u, a), (v, b)) + W s((p, c), (u, a)) * W s((q, d), (v, b))
    + W s((p, c), (v, b)) * W s((q, d), (u, a))

theorem pmSum_fourPt (W : Sym2 (V × Fin 3) → F) {p q u v : V} (hpq : p ≠ q) (hpu : p ≠ u)
    (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) (huv : u ≠ v) (col : V → Fin 3) :
    pmSum W col {p, q, u, v} = fourPt W p q u v (col p) (col q) (col u) (col v) := by
  rw [pmSum_four W col hpq hpu hpv hqu hqv huv]
  simp only [Sym2.map_mk, paint, fourPt]

omit [Fintype V] [DecidableEq V] in
/-- **Capping the pivots of a four-point sum gives the contracted weight.** -/
theorem sum_cap_fourPt (W : Sym2 (V × Fin 3) → F) (p q u v : V) (κ μ : Fin 3 → F)
    (a b : Fin 3) :
    ∑ c, ∑ d, κ c * μ d * fourPt W p q u v c d a b
      = contracted W p q κ μ s((u, a), (v, b)) := by
  rw [contracted_apply]
  simp only [capValue, pivotProfile, fourPt, Fin.sum_univ_three]
  ring

/-- The cap polynomial: the cap value times the diagonal of the cap.  Its nonvanishing is
exactly the validity of a cap. -/
noncomputable def capPoly (W : Sym2 (V × Fin 3) → F) (p q : V) :
    MvPolynomial (Fin 3 ⊕ Fin 3) F :=
  bil (fun c d => W s((p, c), (q, d))) * ∏ k, (X (Sum.inl k) * X (Sum.inr k))

omit [Fintype V] [DecidableEq V] in
theorem capPoly_ne_zero {W : Sym2 (V × Fin 3) → F} {p q : V}
    (hlive : ∃ c d, W s((p, c), (q, d)) ≠ 0) : capPoly W p q ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · intro h
    obtain ⟨c, d, hcd⟩ := hlive
    exact hcd ((bil_eq_zero_iff _).mp h c d)
  · rw [Finset.prod_ne_zero_iff]
    intro k _
    exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

/-- The polynomial of a contracted weight on the pair `uv`, in colours `a, b`. -/
noncomputable def pairPoly (W : Sym2 (V × Fin 3) → F) (p q u v : V) (a b : Fin 3) :
    MvPolynomial (Fin 3 ⊕ Fin 3) F :=
  bil (fun c d => fourPt W p q u v c d a b)

/-- **Rigidity at a valid cap.**  On six sites in characteristic two, at every cap where the
cap polynomial is nonzero, the contracted weights of a pair of the other four sites vanish
off the diagonal and on all but one diagonal colour. -/
theorem rigid_at_cap (h2 : (2 : F) = 0) [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {p q : V} (hpq : p ≠ q)
    {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q) (huv : u ≠ v)
    (z : Fin 3 ⊕ Fin 3 → F) (hz : eval z (capPoly W p q) ≠ 0) :
    (∀ a b, a ≠ b → eval z (pairPoly W p q u v a b) = 0) ∧
    (∀ a b, a ≠ b → eval z (pairPoly W p q u v a a) = 0 ∨
      eval z (pairPoly W p q u v b b) = 0) := by
  classical
  set κ : Fin 3 → F := fun k => z (Sum.inl k)
  set μ : Fin 3 → F := fun k => z (Sum.inr k)
  have hz' := hz
  rw [capPoly, map_mul, eval_bil] at hz'
  have hs : capValue W p q κ μ ≠ 0 := left_ne_zero_of_mul hz'
  have hdiag : ∀ k, κ k * μ k ≠ 0 := by
    intro k
    have hprod := right_ne_zero_of_mul hz'
    rw [map_prod, Finset.prod_ne_zero_iff] at hprod
    simpa [κ, μ] using hprod k (Finset.mem_univ k)
  have hcard4 : Fintype.card ↥(rest p q) = 4 := by
    rw [Fintype.card_coe]
    have := card_rest (V := V) hpq
    omega
  have hG := isGHZOver_contract h2 hW hpq (by omega) κ μ hs hdiag
  obtain ⟨hoff, hone⟩ := fourRigid (↥(rest p q)) hcard4 _ hG
  have hu'v' : (⟨u, hu⟩ : ↥(rest p q)) ≠ ⟨v, hv⟩ := fun h => huv (congrArg Subtype.val h)
  have hev : ∀ a b, eval z (pairPoly W p q u v a b)
      = restrictW (contracted W p q κ μ) (rest p q) s((⟨u, hu⟩, a), (⟨v, hv⟩, b)) := by
    intro a b
    rw [pairPoly, eval_bil]
    exact sum_cap_fourPt W p q u v κ μ a b
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · rw [hev]
    exact hoff _ _ hu'v' a b hab
  · rw [hev, hev]
    exact hone _ _ hu'v' a b hab

/-- Every colouring of `p, q, u, v` with a nonzero matching sum paints `u` and `v` with
`k`, and some colouring has a nonzero sum. -/
def PinPair (W : Sym2 (V × Fin 3) → F) (p q u v : V) (k : Fin 3) : Prop :=
  (∀ col : V → Fin 3, pmSum W col {p, q, u, v} ≠ 0 → col u = k ∧ col v = k) ∧
  ∃ col : V → Fin 3, pmSum W col {p, q, u, v} ≠ 0

/-- **From rigidity at every valid cap to pins.**  If the diagonal polynomial of colour `k`
on the pair `uv` is nonzero, every nonzero four-point sum on `p, q, u, v` paints `u, v`
with `k`. -/
theorem pinPair_of_pairPoly (h2 : (2 : F) = 0) [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {p q : V} (hpq : p ≠ q)
    (hD : capPoly W p q ≠ 0) {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q)
    (huv : u ≠ v) {k : Fin 3} (hk : pairPoly W p q u v k k ≠ 0) : PinPair W p q u v k := by
  classical
  have hpu : p ≠ u := fun h => p_notMem_rest p q (h ▸ hu)
  have hpv : p ≠ v := fun h => p_notMem_rest p q (h ▸ hv)
  have hqu : q ≠ u := fun h => q_notMem_rest p q (h ▸ hu)
  have hqv : q ≠ v := fun h => q_notMem_rest p q (h ▸ hv)
  have hoff : ∀ a b, a ≠ b → pairPoly W p q u v a b = 0 := fun a b hab =>
    eq_zero_of_eval_imp hD fun z hz => (rigid_at_cap h2 hV hW hpq hu hv huv z hz).1 a b hab
  have hone : ∀ a b, a ≠ b → pairPoly W p q u v a a = 0 ∨ pairPoly W p q u v b b = 0 := by
    intro a b hab
    refine mul_eq_zero.mp (eq_zero_of_eval_imp hD fun z hz => ?_)
    rw [map_mul]
    rcases (rigid_at_cap h2 hV hW hpq hu hv huv z hz).2 a b hab with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  refine ⟨fun col hcol => ?_, ?_⟩
  · rw [pmSum_fourPt W hpq hpu hpv hqu hqv huv] at hcol
    have hne : pairPoly W p q u v (col u) (col v) ≠ 0 := fun h =>
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
  · obtain ⟨c, d, hcd⟩ : ∃ c d, fourPt W p q u v c d k k ≠ 0 := by
      by_contra h
      push Not at h
      exact hk ((bil_eq_zero_iff _).mpr h)
    refine ⟨fun w => if w = p then c else if w = q then d else k, ?_⟩
    rw [pmSum_fourPt W hpq hpu hpv hqu hqv huv]
    simpa [Ne.symm hpq, Ne.symm hpu, Ne.symm hpv, Ne.symm hqu, Ne.symm hqv] using hcd

/-- **Rigidity at a live pair.**  On six sites in characteristic two, a live pair `pq`
colours the three perfect matchings of the other four sites bijectively: in the order
`ab|xy`, `ax|by`, `ay|bx`, the matching `m` gets the colour `π m`, and each pair `uv` of
it pins `u, v` to that colour in every nonzero four-point sum on `p, q, u, v`. -/
theorem rigid_pair (h2 : (2 : F) = 0) [Infinite F] (hV : Fintype.card V = 6)
    {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {p q : V} (hpq : p ≠ q)
    (hlive : ∃ c d, W s((p, c), (q, d)) ≠ 0) {a b x y : V} (hab : a ≠ b) (hax : a ≠ x)
    (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (hrest : rest p q = {a, b, x, y}) :
    ∃ π : Equiv.Perm (Fin 3),
      PinPair W p q a b (π 0) ∧ PinPair W p q x y (π 0) ∧
      PinPair W p q a x (π 1) ∧ PinPair W p q b y (π 1) ∧
      PinPair W p q a y (π 2) ∧ PinPair W p q b x (π 2) := by
  classical
  have hD := capPoly_ne_zero hlive
  obtain ⟨z, hz⟩ := exists_eval_ne_zero hD
  set κ : Fin 3 → F := fun k => z (Sum.inl k)
  set μ : Fin 3 → F := fun k => z (Sum.inr k)
  have hz' := hz
  rw [capPoly, map_mul, eval_bil] at hz'
  have hs : capValue W p q κ μ ≠ 0 := left_ne_zero_of_mul hz'
  have hdiag : ∀ k, κ k * μ k ≠ 0 := by
    intro k
    have hprod := right_ne_zero_of_mul hz'
    rw [map_prod, Finset.prod_ne_zero_iff] at hprod
    simpa [κ, μ] using hprod k (Finset.mem_univ k)
  have hcard4 : Fintype.card ↥(rest p q) = 4 := by
    rw [Fintype.card_coe]
    have := card_rest (V := V) hpq
    omega
  have hG := isGHZOver_contract h2 hW hpq (by omega) κ μ hs hdiag
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
  obtain ⟨π, ⟨h0, h0'⟩, ⟨h1, h1'⟩, ⟨h2', h2''⟩⟩ := k4_shape fourRigid hcard4 hG
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (fun h => hab (congrArg Subtype.val h)) (fun h => hax (congrArg Subtype.val h))
    (fun h => hay (congrArg Subtype.val h)) (fun h => hbx (congrArg Subtype.val h))
    (fun h => hby (congrArg Subtype.val h)) (fun h => hxy (congrArg Subtype.val h)) huniv
  have hpoly : ∀ {u v : V} (hu : u ∈ rest p q) (hv : v ∈ rest p q) (k : Fin 3),
      restrictW (contracted W p q κ μ) (rest p q) s((⟨u, hu⟩, k), (⟨v, hv⟩, k)) ≠ 0 →
      pairPoly W p q u v k k ≠ 0 := by
    intro u v hu hv k hne h0
    apply hne
    have := congrArg (eval z) h0
    rw [map_zero, pairPoly, eval_bil] at this
    rw [← this]
    exact (sum_cap_fourPt W p q u v κ μ k k).symm
  exact ⟨π,
    pinPair_of_pairPoly h2 hV hW hpq hD ha hb hab (hpoly ha hb _ h0),
    pinPair_of_pairPoly h2 hV hW hpq hD hx hy hxy (hpoly hx hy _ h0'),
    pinPair_of_pairPoly h2 hV hW hpq hD ha hx hax (hpoly ha hx _ h1),
    pinPair_of_pairPoly h2 hV hW hpq hD hb hy hby (hpoly hb hy _ h1'),
    pinPair_of_pairPoly h2 hV hW hpq hD ha hy hay (hpoly ha hy _ h2'),
    pinPair_of_pairPoly h2 hV hW hpq hD hb hx hbx (hpoly hb hx _ h2'')⟩

end Pair

end KrennCharTwo

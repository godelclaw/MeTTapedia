import Mathlib
import Mettapedia.Combinatorics.Matching.SiteVectors
import CharTwoRigidity

/-!
# Rigidity lemmas valid for every number of sites

A GHZ system contracted against a vector at every site sees only the three constant colourings
(`pmSum_formW_univ_of_isGHZ`).  Contract all but two sites and the result is a `3 × 3` matrix in the
colours of the two free sites, which a GHZ system forces to be diagonal with entries
`λ k * ∏ z p k`.  Whenever the contracted weights make that matrix visibly of rank at most two, the
diagonal has a zero entry.  Nothing here depends on the characteristic or on the number of sites.

**The split lemma** (`split_lemma`).  Fix two free sites and split the others into two parts of
odd size.  If the cross forms `∑ z x i * z y j * W(x i, y j)` all vanish, the free sites must be
matched into different parts and the contracted matrix again has rank at most two.

**Three single-coloured partners** (`three_monoAt`).  With one part a single site, the split lemma
says: over an infinite field every site has at least three partners whose weights with it are not
all zero and all use one colour at the partner.

**The cap lemma** (`cap_lemma`).  Cap a pair `u, v` with vectors `κ, μ` on which the pair's
bilinear form vanishes, and contract every other site except two free sites `α, β` against a vector
orthogonal to both profiles `∑ κ a W(u a, g ·)` and `∑ μ b W(v b, g ·)`.  Then `u` and `v` can only
be matched to `α` and `β`, the contracted matrix has rank at most two, and so the vectors cannot all
have nonzero entries.  On four sites there is nothing to contract and this is four-site rigidity.
-/

namespace KrennUniform

open Amplitude MatchingSum MatchingSiteVectors KrennCharTwo

variable {F : Type*} [Field F] {V : Type*} [Fintype V] [DecidableEq V]

/-- **A contracted GHZ system sees only the constant colourings.** -/
theorem pmSum_formW_univ_of_isGHZ [Nonempty V] {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W)
    (z : V → Fin 3 → F) :
    pmSum (formW W z) (fun _ => ()) Finset.univ
      = ∑ k, amplitude W (Amplitude.const k) * ∏ p, z p k := by
  classical
  have hcol : colourings (Finset.univ : Finset V) (Amplitude.const (V := V) (0 : Fin 3))
      = Finset.univ := by
    ext f; simp [mem_colourings]
  rw [pmSum_formW W z (Amplitude.const 0) Finset.univ, hcol]
  have hinj : Function.Injective (Amplitude.const (V := V) (C := Fin 3)) := by
    intro k k' h
    obtain ⟨p⟩ := ‹Nonempty V›
    exact congrFun h p
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Amplitude.const)),
    Finset.sum_image fun k _ k' _ h => hinj h]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [pmSum_univ, mul_comm]
    rfl
  · intro f _ hf
    rw [pmSum_univ, hW.2 f ?_, mul_zero]
    rintro ⟨k, hk⟩
    exact hf (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, funext fun p => (hk p).symm⟩)

/-- The contraction vectors of the cap lemma: `κ, μ` at the capped pair, unit vectors at the two
free sites, `x` elsewhere. -/
def capVectors (u v α β : V) (κ μ : Fin 3 → F) (x : V → Fin 3 → F) (a b : Fin 3) :
    V → Fin 3 → F := fun p =>
  if p = u then κ else if p = v then μ else if p = α then Pi.single a 1
  else if p = β then Pi.single b 1 else x p

/-- **The cap lemma.**  In a GHZ system, cap a pair `u, v` with vectors `κ, μ` without zero
entries on which the pair's bilinear form vanishes, and pick two further sites `α, β`.  Then some
other site `g` admits no vector without zero entries orthogonal to both of its profiles
`∑ κ a W(u a, g ·)` and `∑ μ b W(v b, g ·)`. -/
theorem cap_lemma {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {u v α β : V}
    (huv : u ≠ v) (huα : u ≠ α) (huβ : u ≠ β) (hvα : v ≠ α) (hvβ : v ≠ β) (hαβ : α ≠ β)
    (κ μ : Fin 3 → F) (hκ : ∀ a, κ a ≠ 0) (hμ : ∀ a, μ a ≠ 0)
    (hs : ∑ a, ∑ b, κ a * μ b * W s((u, a), (v, b)) = 0)
    (x : V → Fin 3 → F)
    (hxu : ∀ g, g ≠ u → g ≠ v → g ≠ α → g ≠ β →
      ∑ a, ∑ c, κ a * x g c * W s((u, a), (g, c)) = 0)
    (hxv : ∀ g, g ≠ u → g ≠ v → g ≠ α → g ≠ β →
      ∑ b, ∑ c, μ b * x g c * W s((v, b), (g, c)) = 0)
    (hxt : ∀ g, g ≠ u → g ≠ v → g ≠ α → g ≠ β → ∀ c, x g c ≠ 0) : False := by
  classical
  haveI : Nonempty V := ⟨u⟩
  set K : Finset V := (((Finset.univ.erase u).erase v).erase α).erase β with hK
  have hmemK : ∀ g, g ∈ K ↔ g ≠ u ∧ g ≠ v ∧ g ≠ α ∧ g ≠ β := by
    intro g; simp only [hK, Finset.mem_erase, Finset.mem_univ, and_true]; tauto
  have huniv : (Finset.univ : Finset V) = insert u (insert v (insert α (insert β K))) := by
    ext g; simp only [Finset.mem_univ, Finset.mem_insert, true_iff, hmemK]; tauto
  set z := capVectors u v α β κ μ x with hz
  have zu : ∀ a b, z a b u = κ := fun a b => by simp [hz, capVectors]
  have zv : ∀ a b, z a b v = μ := fun a b => by simp [hz, capVectors, Ne.symm huv]
  have zα : ∀ a b, z a b α = Pi.single a 1 := fun a b => by
    simp [hz, capVectors, Ne.symm huα, Ne.symm hvα]
  have zβ : ∀ a b, z a b β = Pi.single b 1 := fun a b => by
    simp [hz, capVectors, Ne.symm huβ, Ne.symm hvβ, Ne.symm hαβ]
  have zK : ∀ a b, ∀ g ∈ K, z a b g = x g := fun a b g hg => by
    obtain ⟨h1, h2, h3, h4⟩ := (hmemK g).mp hg
    simp [hz, capVectors, h1, h2, h3, h4]
  -- the profiles read at the free sites
  let Pα : Fin 3 → F := fun a => ∑ a', κ a' * W s((u, a'), (α, a))
  let Pβ : Fin 3 → F := fun b => ∑ a', κ a' * W s((u, a'), (β, b))
  let Qα : Fin 3 → F := fun a => ∑ b', μ b' * W s((v, b'), (α, a))
  let Qβ : Fin 3 → F := fun b => ∑ b', μ b' * W s((v, b'), (β, b))
  let φ : F := pmSum (formW W x) (fun _ => ()) K
  have hφ : ∀ a b, pmSum (formW W (z a b)) (fun _ => ()) K = φ := fun a b =>
    pmSum_congr _ _ _ fun p hp q hq => by
      simp only [formW_paint, zK a b p hp, zK a b q hq]
  -- contracted weights at `u` and `v`
  have wu : ∀ a b w, w ∈ Finset.univ.erase u → w ≠ α → w ≠ β →
      formW W (z a b) (Sym2.map (paint fun _ => ()) s(u, w)) = 0 := by
    intro a b w hw hwα hwβ
    rw [formW_paint, zu]
    by_cases hwv : w = v
    · subst hwv; rw [zv]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hs
    · have hwu : w ≠ u := (Finset.mem_erase.mp hw).1
      rw [zK a b w ((hmemK w).mpr ⟨hwu, hwv, hwα, hwβ⟩)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hxu w hwu hwv hwα hwβ
  have wv : ∀ a b w, w ≠ u → w ≠ v → w ≠ α → w ≠ β →
      formW W (z a b) (Sym2.map (paint fun _ => ()) s(v, w)) = 0 := by
    intro a b w hwu hwv hwα hwβ
    rw [formW_paint, zv, zK a b w ((hmemK w).mpr ⟨hwu, hwv, hwα, hwβ⟩)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hxv w hwu hwv hwα hwβ
  have uα : ∀ a b, formW W (z a b) (Sym2.map (paint fun _ => ()) s(u, α)) = Pα a := by
    intro a b; rw [formW_paint, zu, zα]; simp [Pα, Pi.single_apply]
  have uβ : ∀ a b, formW W (z a b) (Sym2.map (paint fun _ => ()) s(u, β)) = Pβ b := by
    intro a b; rw [formW_paint, zu, zβ]; simp [Pβ, Pi.single_apply]
  have vα : ∀ a b, formW W (z a b) (Sym2.map (paint fun _ => ()) s(v, α)) = Qα a := by
    intro a b; rw [formW_paint, zv, zα]; simp [Qα, Pi.single_apply]
  have vβ : ∀ a b, formW W (z a b) (Sym2.map (paint fun _ => ()) s(v, β)) = Qβ b := by
    intro a b; rw [formW_paint, zv, zβ]; simp [Qβ, Pi.single_apply]
  -- the structure: `u` goes to `α` or `β`, and then `v` is forced
  have hstruct : ∀ a b, pmSum (formW W (z a b)) (fun _ => ()) Finset.univ
      = (Pα a * Qβ b + Pβ b * Qα a) * φ := by
    intro a b
    rw [pmSum_expand _ _ (Finset.mem_univ u),
      Finset.sum_eq_add α β hαβ (fun w hw hne => by rw [wu a b w hw hne.1 hne.2, zero_mul])
        (fun h => absurd (Finset.mem_erase.mpr ⟨Ne.symm huα, Finset.mem_univ α⟩) h)
        (fun h => absurd (Finset.mem_erase.mpr ⟨Ne.symm huβ, Finset.mem_univ β⟩) h),
      uα, uβ]
    have hv1 : v ∈ (Finset.univ.erase u).erase α := by simp [Ne.symm huv, hvα]
    have hβ1 : β ∈ ((Finset.univ.erase u).erase α).erase v := by
      simp [Ne.symm huβ, hαβ.symm, hvβ.symm]
    have hv2 : v ∈ (Finset.univ.erase u).erase β := by simp [Ne.symm huv, hvβ]
    have hα2 : α ∈ ((Finset.univ.erase u).erase β).erase v := by
      simp [Ne.symm huα, hαβ, hvα.symm]
    rw [pmSum_of_forced _ _ hv1 hβ1 (fun w hw hwβ => by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
        exact wv a b w hw.2.2 hw.1 hw.2.1 hwβ),
      pmSum_of_forced _ _ hv2 hα2 (fun w hw hwα => by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hw
        exact wv a b w hw.2.2 hw.1 hwα hw.2.1),
      vβ, vα]
    have e1 : (((Finset.univ.erase u).erase α).erase v).erase β = K := by
      ext g; simp only [Finset.mem_erase, Finset.mem_univ, and_true, hmemK]; tauto
    have e2 : (((Finset.univ.erase u).erase β).erase v).erase α = K := by
      ext g; simp only [Finset.mem_erase, Finset.mem_univ, and_true, hmemK]; tauto
    rw [e1, e2, hφ]
    ring
  -- the GHZ side: a diagonal matrix
  set d : Fin 3 → F := fun k => amplitude W (Amplitude.const k) * (κ k * μ k * ∏ g ∈ K, x g k)
  have hghz : ∀ a b, pmSum (formW W (z a b)) (fun _ => ()) Finset.univ
      = if a = b then d a else 0 := by
    intro a b
    rw [pmSum_formW_univ_of_isGHZ hW]
    have hprod : ∀ k, ∏ p, z a b p k
        = κ k * μ k * ((Pi.single a 1 : Fin 3 → F) k * (Pi.single b 1 : Fin 3 → F) k)
          * ∏ g ∈ K, x g k := by
      intro k
      have hαK : α ∉ K := fun h => ((hmemK α).mp h).2.2.1 rfl
      have hβK : β ∉ K := fun h => ((hmemK β).mp h).2.2.2 rfl
      rw [huniv, Finset.prod_insert (by simp [huv, huα, huβ, hmemK]),
        Finset.prod_insert (by simp [hvα, hvβ, hmemK]),
        Finset.prod_insert (by simp [hαβ, hαK]), Finset.prod_insert hβK, zu, zv, zα, zβ,
        Finset.prod_congr rfl fun g hg => by rw [zK a b g hg]]
      ring
    simp only [hprod]
    split_ifs with hab
    · subst hab
      rw [Finset.sum_eq_single a (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp [d]
    · refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hka : k = a
      · subst hka; simp [Ne.symm hab]
      · simp [hka]
  have hdiag := rank_two_diag (P := fun a => Pα a * φ) (Q := Qβ) (R := fun a => Qα a * φ)
    (S := Pβ) (d := d) (fun a b => by rw [← hghz a b, hstruct a b]; ring)
  have hne : ∀ k, d k ≠ 0 := fun k =>
    mul_ne_zero (hW.1 k) (mul_ne_zero (mul_ne_zero (hκ k) (hμ k))
      (Finset.prod_ne_zero_iff.mpr fun g hg => by
        obtain ⟨h1, h2, h3, h4⟩ := (hmemK g).mp hg
        exact hxt g h1 h2 h3 h4 k))
  exact mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2) hdiag

/-- **The split lemma.**  In a GHZ system, fix two sites `u, v` and split the other sites into
two parts of odd size.  Then there are no vectors without zero entries at the other sites for which
every cross form `∑ z x i * z y j * W(x i, y j)` (`x` in one part, `y` in the other) vanishes:
the two free sites would have to be matched into different parts, making the contracted matrix
of rank at most two, while a GHZ system makes it an invertible diagonal. -/
theorem split_lemma {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) {u v : V} (huv : u ≠ v)
    {A B : Finset V} (hAB : Disjoint A B) (hcover : ∀ g, g ≠ u → g ≠ v → g ∈ A ∨ g ∈ B)
    (huA : u ∉ A) (huB : u ∉ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hA : ¬ Even A.card) (hB : ¬ Even B.card)
    (z : V → Fin 3 → F) (hzt : ∀ g, g ≠ u → g ≠ v → ∀ c, z g c ≠ 0)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ∑ i, ∑ j, z x i * z y j * W s((x, i), (y, j)) = 0) : False := by
  classical
  haveI : Nonempty V := ⟨u⟩
  have huniv : (Finset.univ : Finset V) = insert u (insert v (A ∪ B)) := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, true_iff]
    by_cases hgu : g = u
    · exact Or.inl hgu
    · by_cases hgv : g = v
      · exact Or.inr (Or.inl hgv)
      · exact Or.inr (Or.inr (hcover g hgu hgv))
  have hTne : ∀ g ∈ A ∪ B, g ≠ u ∧ g ≠ v := by
    intro g hg
    rcases Finset.mem_union.mp hg with h | h
    · exact ⟨fun e => huA (e ▸ h), fun e => hvA (e ▸ h)⟩
    · exact ⟨fun e => huB (e ▸ h), fun e => hvB (e ▸ h)⟩
  let z' : Fin 3 → Fin 3 → V → Fin 3 → F := fun a b p =>
    if p = u then Pi.single a 1 else if p = v then Pi.single b 1 else z p
  have z'u : ∀ a b, z' a b u = Pi.single a 1 := fun a b => by simp [z']
  have z'v : ∀ a b, z' a b v = Pi.single b 1 := fun a b => by simp [z', Ne.symm huv]
  have z'T : ∀ a b, ∀ g ∈ A ∪ B, z' a b g = z g := fun a b g hg => by
    simp [z', (hTne g hg).1, (hTne g hg).2]
  -- the parts' matching sums do not see the free sites
  let hA' : V → F := fun w => pmSum (formW W z) (fun _ => ()) (A.erase w)
  let hB' : V → F := fun w => pmSum (formW W z) (fun _ => ()) (B.erase w)
  have hpart : ∀ a b (X : Finset V), X ⊆ A ∪ B →
      pmSum (formW W (z' a b)) (fun _ => ()) X = pmSum (formW W z) (fun _ => ()) X :=
    fun a b X hX => pmSum_congr _ _ _ fun p hp q hq => by
      simp only [formW_paint, z'T a b p (hX hp), z'T a b q (hX hq)]
  let lu : V → Fin 3 → F := fun w a => ∑ j, z w j * W s((u, a), (w, j))
  let lv : V → Fin 3 → F := fun w b => ∑ j, z w j * W s((v, b), (w, j))
  have hlu : ∀ a b, ∀ w ∈ A ∪ B, formW W (z' a b) (Sym2.map (paint fun _ => ()) s(u, w)) = lu w a :=
    fun a b w hw => by
      rw [formW_paint, z'u, z'T a b w hw]; simp [lu, Pi.single_apply]
  have hlv : ∀ a b, ∀ w ∈ A ∪ B, formW W (z' a b) (Sym2.map (paint fun _ => ()) s(v, w)) = lv w b :=
    fun a b w hw => by
      rw [formW_paint, z'v, z'T a b w hw]; simp [lv, Pi.single_apply]
  have hstruct : ∀ a b, pmSum (formW W (z' a b)) (fun _ => ()) Finset.univ
      = (∑ w ∈ A, lu w a * hA' w) * (∑ l ∈ B, lv l b * hB' l)
        + (∑ w ∈ B, lu w a * hB' w) * (∑ l ∈ A, lv l b * hA' l) := by
    intro a b
    rw [huniv, pmSum_two_over_odd_cut _ _ huv hAB huA huB hvA hvB hA hB (fun x hx y hy => by
      rw [formW_apply, z'T a b x (Finset.mem_union_left _ hx), z'T a b y (Finset.mem_union_right _ hy)]
      exact hcross x hx y hy)]
    have eA : ∀ w ∈ A, pmSum (formW W (z' a b)) (fun _ => ()) (A.erase w) = hA' w :=
      fun w _ => hpart a b _ ((Finset.erase_subset w A).trans Finset.subset_union_left)
    have eB : ∀ w ∈ B, pmSum (formW W (z' a b)) (fun _ => ()) (B.erase w) = hB' w :=
      fun w _ => hpart a b _ ((Finset.erase_subset w B).trans Finset.subset_union_right)
    refine congrArg₂ (· + ·) (congrArg₂ (· * ·) ?_ ?_) (congrArg₂ (· * ·) ?_ ?_)
    · exact Finset.sum_congr rfl fun w hw => by
        rw [hlu a b w (Finset.mem_union_left _ hw), eA w hw]
    · exact Finset.sum_congr rfl fun l hl => by
        rw [hlv a b l (Finset.mem_union_right _ hl), eB l hl]
    · exact Finset.sum_congr rfl fun w hw => by
        rw [hlu a b w (Finset.mem_union_right _ hw), eB w hw]
    · exact Finset.sum_congr rfl fun l hl => by
        rw [hlv a b l (Finset.mem_union_left _ hl), eA l hl]
  set d : Fin 3 → F := fun k => amplitude W (Amplitude.const k) * ∏ g ∈ A ∪ B, z g k
  have hghz : ∀ a b, pmSum (formW W (z' a b)) (fun _ => ()) Finset.univ
      = if a = b then d a else 0 := by
    intro a b
    rw [pmSum_formW_univ_of_isGHZ hW]
    have hprod : ∀ k, ∏ p, z' a b p k
        = ((Pi.single a 1 : Fin 3 → F) k * (Pi.single b 1 : Fin 3 → F) k) * ∏ g ∈ A ∪ B, z g k := by
      intro k
      have hvT : v ∉ A ∪ B := by simp [hvA, hvB]
      rw [huniv, Finset.prod_insert (by simp [huv, huA, huB]), Finset.prod_insert hvT, z'u, z'v,
        Finset.prod_congr rfl fun g hg => by rw [z'T a b g hg]]
      ring
    simp only [hprod]
    split_ifs with hab
    · subst hab
      rw [Finset.sum_eq_single a (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp [d]
    · refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hka : k = a
      · subst hka; simp [Ne.symm hab]
      · simp [hka]
  have hdiag := rank_two_diag (P := fun a => ∑ w ∈ A, lu w a * hA' w)
    (Q := fun b => ∑ l ∈ B, lv l b * hB' l) (R := fun a => ∑ w ∈ B, lu w a * hB' w)
    (S := fun b => ∑ l ∈ A, lv l b * hA' l) (d := d)
    (fun a b => by rw [← hghz a b, hstruct a b])
  have hne : ∀ k, d k ≠ 0 := fun k =>
    mul_ne_zero (hW.1 k) (Finset.prod_ne_zero_iff.mpr fun g hg =>
      hzt g (hTne g hg).1 (hTne g hg).2 k)
  exact mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2) hdiag

/-- The pair `w, b` uses a single colour at `b`: its weights are not all zero, and all its nonzero
weights sit in one colour of `b`. -/
def MonoAt (W : Sym2 (V × Fin 3) → F) (w b : V) : Prop :=
  ∃ j, (∃ a, W s((w, a), (b, j)) ≠ 0) ∧ ∀ a c, c ≠ j → W s((w, a), (b, c)) = 0

/-- A GHZ system lives on an even number of sites. -/
theorem even_card_of_isGHZ {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) :
    Even (Fintype.card V) := by
  by_contra h
  apply hW.1 0
  rw [← pmSum_univ, pmSum_of_odd _ _ (by rw [Finset.card_univ]; exact h)]

omit [Fintype V] [DecidableEq V] in
/-- A weight matrix that is nonzero and not single-coloured at `b` has two nonzero colours at `b`. -/
theorem two_columns_of_not_monoAt {W : Sym2 (V × Fin 3) → F} {w b : V}
    (hne : ∃ a c, W s((w, a), (b, c)) ≠ 0) (hm : ¬ MonoAt W w b) :
    ∃ j j', j ≠ j' ∧ (∃ a, W s((w, a), (b, j)) ≠ 0) ∧ ∃ a, W s((w, a), (b, j')) ≠ 0 := by
  obtain ⟨a, j, hj⟩ := hne
  have : ¬ ∀ a' c, c ≠ j → W s((w, a'), (b, c)) = 0 := fun h => hm ⟨j, ⟨a, hj⟩, h⟩
  push Not at this
  obtain ⟨a', c, hcj, hc⟩ := this
  exact ⟨j, c, Ne.symm hcj, ⟨a, hj⟩, ⟨a', hc⟩⟩

open MvPolynomial Classical in
/-- **Every site has three single-coloured partners.**  In a GHZ system over an infinite field, every
site `w` has at least three partners `b` whose weights with `w` are not all zero and all use one
colour at `b`.  Otherwise put the at most two such partners among two free sites, pick a vector at
`w` for which every other partner's weights read in two colours, and make all of `w`'s contracted
weights vanish: `w` alone is an odd part, and the split lemma applies. -/
theorem three_monoAt [Infinite F] {W : Sym2 (V × Fin 3) → F} (hW : IsGHZOver W) (w : V)
    (hcard : 4 ≤ Fintype.card V) :
    3 ≤ ((Finset.univ.erase w).filter fun b => MonoAt W w b).card := by
  classical
  by_contra hlt
  push Not at hlt
  set Mw := (Finset.univ.erase w).filter fun b => MonoAt W w b with hMw
  -- two free sites covering the single-coloured partners
  have hrest : 3 ≤ (Finset.univ.erase w).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]; omega
  obtain ⟨u, v, huv, huw, hvw, hcov⟩ : ∃ u v, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ Mw ⊆ {u, v} := by
    have hsub : Mw ⊆ Finset.univ.erase w := Finset.filter_subset _ _
    obtain ⟨T, hMT, hT, hTc⟩ := Finset.exists_subsuperset_card_eq hsub (n := 2) (by omega) (by omega)
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hTc
    exact ⟨u, v, huv, (Finset.mem_erase.mp (hT (by simp))).1,
      (Finset.mem_erase.mp (hT (by simp))).1, hMT⟩
  set B := ((Finset.univ.erase w).erase u).erase v with hB
  have hmemB : ∀ b, b ∈ B ↔ b ≠ w ∧ b ≠ u ∧ b ≠ v := by
    intro b; simp only [hB, Finset.mem_erase, Finset.mem_univ, and_true]; tauto
  have hnotmono : ∀ b ∈ B, ¬ MonoAt W w b := by
    intro b hb hmono
    obtain ⟨hbw, hbu, hbv⟩ := (hmemB b).mp hb
    have : b ∈ Mw := by simp [hMw, hbw, hmono]
    rcases Finset.mem_insert.mp (hcov this) with h | h
    · exact hbu h
    · exact hbv (Finset.mem_singleton.mp h)
  -- two nonzero colours at each partner with nonzero weights
  let nz : V → Prop := fun b => ∃ a c, W s((w, a), (b, c)) ≠ 0
  have htwo : ∀ b ∈ B, nz b → ∃ j j', j ≠ j' ∧ (∃ a, W s((w, a), (b, j)) ≠ 0) ∧
      ∃ a, W s((w, a), (b, j')) ≠ 0 :=
    fun b hb h => two_columns_of_not_monoAt h (hnotmono b hb)
  let J : V → Fin 3 × Fin 3 := fun b =>
    if h : b ∈ B ∧ nz b then ((htwo b h.1 h.2).choose, (htwo b h.1 h.2).choose_spec.choose) else (0, 1)
  have hJ : ∀ b ∈ B, nz b → (J b).1 ≠ (J b).2 ∧ (∃ a, W s((w, a), (b, (J b).1)) ≠ 0) ∧
      ∃ a, W s((w, a), (b, (J b).2)) ≠ 0 := by
    intro b hb h
    simp only [J, dif_pos (And.intro hb h)]
    exact (htwo b hb h).choose_spec.choose_spec
  -- a generic vector at `w`
  let L : V → Fin 3 → MvPolynomial (Fin 3) F := fun b j => ∑ a, X a * C (W s((w, a), (b, j)))
  have hevL : ∀ n b j, eval n (L b j) = ∑ a, n a * W s((w, a), (b, j)) := by
    intro n b j; simp [L]
  have hLne : ∀ b j, (∃ a, W s((w, a), (b, j)) ≠ 0) → L b j ≠ 0 := by
    rintro b j ⟨a, ha⟩ h0
    apply ha
    have := congrArg (eval (Pi.single a 1)) h0
    rw [hevL, map_zero] at this
    simpa [Pi.single_apply] using this
  set Bnz := B.filter nz with hBnz
  let P : MvPolynomial (Fin 3) F :=
    (X 0 * X 1 * X 2) * ∏ b ∈ Bnz, (L b (J b).1 * L b (J b).2)
  have hP : P ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _)) (X_ne_zero _)) ?_
    rw [Finset.prod_ne_zero_iff]
    intro b hb
    obtain ⟨hbB, hbnz⟩ := Finset.mem_filter.mp hb
    obtain ⟨-, h1, h2⟩ := hJ b hbB hbnz
    exact mul_ne_zero (hLne b _ h1) (hLne b _ h2)
  obtain ⟨n, hn⟩ := KrennCharTwo.exists_eval_ne_zero hP
  simp only [P, map_mul, map_prod, eval_X] at hn
  have hn0 : ∀ i, n i ≠ 0 := by
    have h := left_ne_zero_of_mul hn
    intro i; fin_cases i
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul h)
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul h)
    · exact right_ne_zero_of_mul h
  have hnB : ∀ b ∈ Bnz, eval n (L b (J b).1) ≠ 0 ∧ eval n (L b (J b).2) ≠ 0 := by
    intro b hb
    have := (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hn)) b hb
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  -- a vector at every other site killing the contracted weight to `w`
  have hzb : ∀ b ∈ B, ∃ y : Fin 3 → F, (∀ c, y c ≠ 0) ∧
      ∑ j, (∑ a, n a * W s((w, a), (b, j))) * y j = 0 := by
    intro b hb
    by_cases hbnz : nz b
    · obtain ⟨hjj, -, -⟩ := hJ b hb hbnz
      have h12 := hnB b (Finset.mem_filter.mpr ⟨hb, hbnz⟩)
      rw [hevL, hevL] at h12
      exact exists_torus_zero (fun j => ∑ a, n a * W s((w, a), (b, j))) hjj h12.1 h12.2
    · refine ⟨fun _ => 1, fun _ => one_ne_zero, Finset.sum_eq_zero fun j _ => ?_⟩
      have : ∀ a, W s((w, a), (b, j)) = 0 := by
        intro a; by_contra h; exact hbnz ⟨a, j, h⟩
      simp [this]
  choose! y hy using hzb
  let z : V → Fin 3 → F := fun p => if p = w then n else y p
  have hN := even_card_of_isGHZ hW
  have hBcard : ¬ Even B.card := by
    have hc : B.card + 3 = Fintype.card V := by
      rw [hB, Finset.card_erase_of_mem (by simp [hvw, huv.symm] : v ∈ (Finset.univ.erase w).erase u),
        Finset.card_erase_of_mem (by simp [huw] : u ∈ Finset.univ.erase w),
        Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ]
      omega
    rw [← hc] at hN
    intro hB2
    exact Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr (by
      rcases hB2 with ⟨k, hk⟩; rcases hN with ⟨m, hm⟩; omega)) hN
  refine split_lemma (u := u) (v := v) hW huv (A := {w}) (B := B)
    (Finset.disjoint_singleton_left.mpr fun h => ((hmemB w).mp h).1 rfl)
    (fun g hgu hgv => by
      by_cases hgw : g = w
      · exact Or.inl (Finset.mem_singleton.mpr hgw)
      · exact Or.inr ((hmemB g).mpr ⟨hgw, hgu, hgv⟩))
    (by simp [huw]) (fun h => ((hmemB u).mp h).2.1 rfl) (by simp [hvw])
    (fun h => ((hmemB v).mp h).2.2 rfl) (by simp) hBcard z ?_ ?_
  · intro g hgu hgv c
    by_cases hgw : g = w
    · simp only [z, if_pos hgw]; exact hn0 c
    · simp only [z, if_neg hgw]; exact (hy g ((hmemB g).mpr ⟨hgw, hgu, hgv⟩)).1 c
  · intro a ha b hb
    rw [Finset.mem_singleton.mp ha]
    have hbw : b ≠ w := ((hmemB b).mp hb).1
    simp only [z, if_pos rfl, if_neg hbw]
    rw [← (hy b hb).2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring

end KrennUniform

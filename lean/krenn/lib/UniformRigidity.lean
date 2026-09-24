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

end KrennUniform

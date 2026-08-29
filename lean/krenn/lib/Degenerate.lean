import Mathlib
import Amplitude
import MatchingSum
import PurePartner
import SingleFlip
import Covector

/-!
# Some colour is degenerate

At a site whose live partners are its three named ones and a single live extra, the
colour-`k` matching sum on the complement of the site and the extra cannot be non-zero for
all three colours.

If it were, the constant reading of the spared relation would put every off-colour column of
the extra block on that colour's named line; the flip relation would put each basis vector
in the span of a named column and an extra column; and the three lines would collapse,
leaving two distinct basis vectors on one line.
-/

namespace Degenerate

open Amplitude MatchingSum PurePartner SingleFlip Covector

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Some colour is degenerate.** -/
theorem exists_degenerate_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (hS : ((Finset.univ.erase u).erase v).Nonempty)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (hlive : ∃ a b : Fin 3, W s((u, a), (v, b)) ≠ 0) :
    ∃ k : Fin 3, pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase u).erase v) = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  set m : Fin 3 → ℂ := fun k =>
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) with hmdef
  set mw : Fin 3 → ℂ := fun k =>
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase (wn k)) with hmwdef
  set vv : Fin 3 → (Fin 3 → ℂ) := fun k a => W s((u, a), (wn k, k)) with hvvdef
  set cc : Fin 3 → (Fin 3 → ℂ) := fun b a => W s((u, a), (v, b)) with hccdef
  set ek : Fin 3 → (Fin 3 → ℂ) := fun k j => if j = k then (1 : ℂ) else 0 with hekdef
  -- Every off-colour column of the extra block lies on the colour's named line.
  have step1 : ∀ k b : Fin 3, b ≠ k → cc b ∈ Submodule.span ℂ {vv k} := by
    intro k b hbk
    by_contra hnot
    obtain ⟨f, hfy, hfker⟩ := Submodule.exists_le_ker_of_notMem hnot
    set ρ : Fin 3 → ℂ := fun a => f (fun j => if a = j then (1 : ℂ) else 0) with hρdef
    have hf : ∀ z : Fin 3 → ℂ, f z = ∑ a : Fin 3, z a * ρ a := by
      intro z
      rw [LinearMap.pi_apply_eq_sum_univ f z]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul]
    have hvk : (∑ a : Fin 3, ρ a * vv k a) = 0 := by
      have hmem : vv k ∈ Submodule.span ℂ ({vv k} : Set (Fin 3 → ℂ)) :=
        Submodule.mem_span_singleton_self _
      have h0 := hfker hmem
      rw [LinearMap.mem_ker, hf] at h0
      rw [← h0]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hann : ∀ w ∈ (Finset.univ.erase u).erase v,
        (∑ a : Fin 3, ρ a * W s((u, a), (w, k))) = 0 := by
      intro w hw
      by_cases hj : ∃ j, w = wn j
      · obtain ⟨j, hjw⟩ := hj
        by_cases hjk : j = k
        · rw [hjw, hjk]; exact hvk
        · refine Finset.sum_eq_zero fun a _ => ?_
          rw [hjw, hcol j a k (fun h => hjk h.symm), mul_zero]
      · push_neg at hj
        have hwu' : w ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1
        have hwv' : w ≠ v := (Finset.mem_erase.mp hw).1
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [hlone w hwu' hwv' hj a k, mul_zero]
    have hkey := covector_constant W hzero hvu k hS ρ
      (fun y => if y = b then (1 : ℂ) else 0) hann
    have hxk : (if k = b then (1 : ℂ) else 0) = 0 := if_neg fun h => hbk h.symm
    rw [hxk, mul_zero] at hkey
    have hlhs : (∑ a : Fin 3, ρ a *
        (∑ b' : Fin 3, (if b' = b then (1 : ℂ) else 0) * W s((u, a), (v, b'))))
        = ∑ a : Fin 3, ρ a * cc b a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      simp [hccdef]
    rw [hlhs] at hkey
    have hcb : (∑ a : Fin 3, ρ a * cc b a) = 0 := (mul_eq_zero.mp hkey).resolve_right (hcon k)
    apply hfy
    rw [hf, ← hcb]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- The flip relation, read as a vector identity.
  have step2 : ∀ k : Fin 3, mw k • vv k + m k • cc k
      = amplitude W (Amplitude.const (V := V) k) • ek k := by
    intro k
    funext a
    have hp := flip_pair W hvu wn hwu hvw hcol hlone k a
    by_cases hak : a = k
    · subst hak
      rw [flip_diag_eq W u a] at hp
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hekdef, hvvdef, hccdef,
        hmdef, hmwdef, if_true, mul_one]
      linear_combination -hp
    · rw [flip_orthogonal W hzero u k a hak ⟨v, hvu⟩] at hp
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hekdef, if_neg hak, mul_zero,
        hvvdef, hccdef, hmdef, hmwdef]
      linear_combination -hp
  -- Every column of the extra block vanishes.
  have hzeroall : ∀ b : Fin 3, cc b = 0 := by
    intro b
    by_contra hne
    have hfin : ∀ b : Fin 3, b + 1 ≠ b ∧ b + 2 ≠ b ∧ b + 1 ≠ b + 2 := by decide
    obtain ⟨h1, h2, h3⟩ := hfin b
    set k' : Fin 3 := b + 1 with hk'
    set k'' : Fin 3 := b + 2 with hk''
    set L : Submodule ℂ (Fin 3 → ℂ) := Submodule.span ℂ {cc b} with hL
    have hccL : cc b ∈ L := Submodule.mem_span_singleton_self _
    have hline : ∀ k : Fin 3, k ≠ b → vv k ∈ L := by
      intro k hk
      obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (step1 k b (fun h => hk h.symm))
      have hα0 : α ≠ 0 := by
        intro h; rw [h, zero_smul] at hα; exact hne hα.symm
      refine Submodule.mem_span_singleton.mpr ⟨α⁻¹, ?_⟩
      rw [← hα, smul_smul, inv_mul_cancel₀ hα0, one_smul]
    have hek : ∀ k : Fin 3, k ≠ b → ek k ∈ L := by
      intro k hk
      have hvvL : vv k ∈ L := hline k hk
      have hccL' : cc k ∈ L := by
        by_cases hkk' : k = k'
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hline k'' h2))
            (step1 k'' k (by rw [hkk']; exact h3))
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (hline k' h1))
            (step1 k' k hkk')
      have hsum : mw k • vv k + m k • cc k ∈ L := L.add_mem (L.smul_mem _ hvvL)
        (L.smul_mem _ hccL')
      rw [step2 k] at hsum
      have := L.smul_mem (amplitude W (Amplitude.const (V := V) k))⁻¹ hsum
      rwa [smul_smul, inv_mul_cancel₀ (hone k), one_smul] at this
    obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp (hek k' h1)
    obtain ⟨δ, hδ⟩ := Submodule.mem_span_singleton.mp (hek k'' h2)
    have hg : γ * cc b k' = 1 := by
      have := congrFun hγ k'
      simpa [hekdef] using this
    have hd : δ * cc b k' = 0 := by
      have := congrFun hδ k'
      simpa [hekdef, h3] using this
    have hcb : cc b k' ≠ 0 := by intro h; rw [h, mul_zero] at hg; exact one_ne_zero hg.symm
    have hδ0 : δ = 0 := by
      rcases mul_eq_zero.mp hd with h | h
      · exact h
      · exact absurd h hcb
    have := congrFun hδ k''
    rw [hδ0] at this
    simp [hekdef] at this
  obtain ⟨a, b, hab⟩ := hlive
  exact hab (congrFun (hzeroall b) a)

/-! ### Inert edges delete -/

/-- **An inert edge can be zeroed.**  If the matching sum on the complement of a pair
vanishes for every colouring, then the edges between that pair contribute to no amplitude:
the term of the expansion that uses one is multiplied by exactly that sum, and no other term
sees them, because every other term's matching sum runs over a set missing one endpoint. -/
theorem amplitude_of_inert (W W' : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (hinert : ∀ c : V → Fin 3,
      pmSum W c ((Finset.univ.erase u).erase v) = 0)
    (hagree : ∀ (x y : V) (a b : Fin 3), ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) →
      W' s((x, a), (y, b)) = W s((x, a), (y, b)))
    (hkill : ∀ a b : Fin 3, W' s((u, a), (v, b)) = 0)
    (c : V → Fin 3) : amplitude W' c = amplitude W c := by
  classical
  have hexp : ∀ X : Sym2 (V × Fin 3) → ℂ, amplitude X c
      = ∑ y ∈ Finset.univ.erase u,
          X s((u, c u), (y, c y)) * pmSum X c ((Finset.univ.erase u).erase y) := by
    intro X
    rw [← pmSum_univ, pmSum_expand X c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl fun y _ => ?_
    first
      | rfl
      | (congr 1; simp [Sym2.map_pair_eq, paint])
  rw [hexp W', hexp W]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyu : y ≠ u := (Finset.mem_erase.mp hy).1
  by_cases hyv : y = v
  · subst hyv
    rw [hkill, hinert c, mul_zero, zero_mul]
  · have hedge : W' s((u, c u), (y, c y)) = W s((u, c u), (y, c y)) :=
      hagree u y (c u) (c y) (fun h => hyv h.2) (fun h => hvu h.1.symm)
    have hsum : pmSum W' c ((Finset.univ.erase u).erase y)
        = pmSum W c ((Finset.univ.erase u).erase y) := by
      refine pmSum_congr W' W c fun x hx z hz => ?_
      have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
      have hzu : z ≠ u := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1
      have : W' s((x, c x), (z, c z)) = W s((x, c x), (z, c z)) :=
        hagree x z (c x) (c z) (fun h => hxu h.1) (fun h => hzu h.2)
      exact this
    rw [hedge, hsum]

/-! ### The local identity at a site -/

/-- **The fan relation.**  At a site whose live partners are its three named ones and a
single extra, the test sum in colour `α` splits into exactly four terms: the extra's block
read against its test vector, times the matching sum on the complement, plus one term per
named partner in which only that partner's own colour survives. -/
theorem fan_relation (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (ψ : V → Fin 3 → ℂ) :
    amplitude W (Amplitude.const (V := V) α) * ∏ w ∈ Finset.univ.erase u, ψ w α
      = (∑ b : Fin 3, ψ v b * W s((u, α), (v, b))) * pairK W u v 0 0 ψ
        + ∑ j : Fin 3, W s((u, α), (wn j, j)) * ψ (wn j) j * pairK W u (wn j) 0 0 ψ := by
  classical
  rw [← testSum_eq W hzero u α ψ, testSum_expand_full W u α ψ]
  set T : Finset V := insert v (Finset.image wn Finset.univ) with hT
  have hvimg : v ∉ Finset.image wn Finset.univ := by
    simp only [Finset.mem_image, not_exists]
    rintro j ⟨-, hj⟩
    exact hvw j hj.symm
  have hsub : T ⊆ Finset.univ.erase u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_erase.mpr ⟨hwu j, Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub]
  · rw [hT, Finset.sum_insert hvimg,
      Finset.sum_image (fun j _ k _ h => hwinj h)]
    congr 1
    · rw [pairK_pin_indep W hvu α α 0 0 ψ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [pairK_pin_indep W (hwu j) α α 0 0 ψ]
      congr 1
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
        (fun b _ hb => by rw [hcol j α b hb, mul_zero])]
      ring
  · intro z hz hzT
    have hzu : z ≠ u := (Finset.mem_erase.mp hz).1
    have hzv : z ≠ v := fun h => hzT (by rw [hT, h]; exact Finset.mem_insert_self _ _)
    have hzw : ∀ j, z ≠ wn j := fun j h => hzT (by
      rw [hT, h]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
    have : (∑ b : Fin 3, ψ z b * W s((u, α), (z, b))) = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hlone z hzu hzv hzw α b, mul_zero]
    rw [this, zero_mul]

/-! ### Pinning, read off the fan relation -/

/-- **A live row pins its named partner.**  If the named blocks are single diagonal entries
and row `α` of the extra block is live, then the matching sum on the complement of the site
and the extra vanishes for every test vector that misses colour `α` at the `α`-named
partner. -/
theorem pairK_zero_of_live_row (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) {b₀ : Fin 3} (hrow : W s((u, α), (v, b₀)) ≠ 0)
    (ψ : V → Fin 3 → ℂ) (hψ : ψ (wn α) α = 0) :
    pairK W u v 0 0 ψ = 0 := by
  classical
  have hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0 :=
    fun j a b hb => hdiag j a b (Or.inr hb)
  set ψ' : V → Fin 3 → ℂ :=
    fun w y => if w = v then (if y = b₀ then (1 : ℂ) else 0) else ψ w y with hψ'
  have hagree : ∀ w ∈ (Finset.univ.erase u).erase v, ψ' w = ψ w := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    funext y; rw [hψ']; simp [hwv]
  have hpair : pairK W u v 0 0 ψ' = pairK W u v 0 0 ψ := pairK_congr W u v 0 0 hagree
  have hwα : ψ' (wn α) α = 0 := by
    have hnev : wn α ≠ v := fun h => hvw α h.symm
    show (if wn α = v then (if α = b₀ then (1 : ℂ) else 0) else ψ (wn α) α) = 0
    rw [if_neg hnev]; exact hψ
  have hkey := fan_relation W hzero hvu wn hwu hvw hwinj hcol hlone α ψ'
  have hlhs : amplitude W (Amplitude.const (V := V) α)
      * ∏ w ∈ Finset.univ.erase u, ψ' w α = 0 := by
    have hmem : wn α ∈ Finset.univ.erase u :=
      Finset.mem_erase.mpr ⟨hwu α, Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hmem hwα, mul_zero]
  have hnamed : ∑ j : Fin 3, W s((u, α), (wn j, j)) * ψ' (wn j) j
      * pairK W u (wn j) 0 0 ψ' = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = α
    · subst hj
      rw [hwα, mul_zero, zero_mul]
    · rw [hdiag j α j (Or.inl fun h => hj h.symm), zero_mul, zero_mul]
  rw [hlhs, hnamed, add_zero] at hkey
  have hrowval : (∑ b : Fin 3, ψ' v b * W s((u, α), (v, b)))
      = W s((u, α), (v, b₀)) := by
    have : ∀ b : Fin 3, ψ' v b = if b = b₀ then (1 : ℂ) else 0 := by
      intro b; rw [hψ']; simp
    rw [Finset.sum_congr rfl fun b _ => by rw [this b]]
    simp
  rw [hrowval] at hkey
  rw [← hpair]
  exact (mul_eq_zero.mp hkey.symm).resolve_left hrow

/-- The colouring form: any colouring of the complement whose matching sum survives puts the
named partner of each live row on that row's colour. -/
theorem named_on_colour (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (c : V → Fin 3) (hc : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0)
    (α : Fin 3) {b₀ : Fin 3} (hrow : W s((u, α), (v, b₀)) ≠ 0) : c (wn α) = α := by
  classical
  by_contra hne
  refine hc ?_
  rw [← pairK_basis W hvu c]
  refine pairK_zero_of_live_row W hzero hvu wn hwu hvw hwinj hdiag hlone α hrow _ ?_
  exact if_neg fun h => hne h.symm

/-! ### A dead row determines its named partner's complement -/

/-- **A dead row leaves a monomial.**  If the named blocks are single diagonal entries and
row `α` of the extra block is dead, the matching sum on the complement of the site and its
`α`-named partner is determined outright: it is the colour-`α` amplitude divided by that
partner's weight, times the pure colour-`α` monomial. -/
theorem pairK_named_monomial (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hdead : ∀ b : Fin 3, W s((u, α), (v, b)) = 0) (ψ : V → Fin 3 → ℂ) :
    W s((u, α), (wn α, α)) * pairK W u (wn α) 0 0 ψ
      = amplitude W (Amplitude.const (V := V) α)
        * ∏ w ∈ (Finset.univ.erase u).erase (wn α), ψ w α := by
  classical
  have hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0 :=
    fun j a b hb => hdiag j a b (Or.inr hb)
  set ψ' : V → Fin 3 → ℂ :=
    fun w y => if w = wn α then (if y = α then (1 : ℂ) else 0) else ψ w y with hψ'
  have hoff : ∀ w : V, w ≠ wn α → ψ' w = ψ w := by
    intro w hw; funext y; rw [hψ']; simp [hw]
  have hat : ψ' (wn α) α = 1 := by
    show (if wn α = wn α then (if α = α then (1 : ℂ) else 0) else ψ (wn α) α) = 1
    simp
  have hkey := fan_relation W hzero hvu wn hwu hvw hwinj hcol hlone α ψ'
  -- the extra's term dies
  have hextra : (∑ b : Fin 3, ψ' v b * W s((u, α), (v, b))) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [hdead b, mul_zero]
  -- only the `α`-named term survives
  have hnamed : ∑ j : Fin 3, W s((u, α), (wn j, j)) * ψ' (wn j) j
      * pairK W u (wn j) 0 0 ψ'
      = W s((u, α), (wn α, α)) * pairK W u (wn α) 0 0 ψ' := by
    rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α)]
    · rw [hat, mul_one]
    · intro j _ hj
      rw [hdiag j α j (Or.inl fun h => hj h.symm), zero_mul, zero_mul]
  rw [hextra, zero_mul, zero_add, hnamed] at hkey
  -- the paired sum does not see the named partner
  have hpair : pairK W u (wn α) 0 0 ψ' = pairK W u (wn α) 0 0 ψ := by
    refine pairK_congr W u (wn α) 0 0 fun w hw => ?_
    exact hoff w (Finset.mem_erase.mp hw).1
  -- and the left side loses exactly that factor
  have hprod : ∏ w ∈ Finset.univ.erase u, ψ' w α
      = ∏ w ∈ (Finset.univ.erase u).erase (wn α), ψ w α := by
    have hmem : wn α ∈ Finset.univ.erase u :=
      Finset.mem_erase.mpr ⟨hwu α, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ hmem, hat, one_mul]
    exact Finset.prod_congr rfl fun w hw => by rw [hoff w (Finset.mem_erase.mp hw).1]
  rw [hpair, hprod] at hkey
  exact hkey.symm

/-- The colouring form: with a dead row, every colouring of that complement other than the
constant one has vanishing matching sum. -/
theorem pmSum_named_eq_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hdead : ∀ b : Fin 3, W s((u, α), (v, b)) = 0)
    (hlive : W s((u, α), (wn α, α)) ≠ 0)
    (c : V → Fin 3) {z₀ : V} (hz₀ : z₀ ∈ (Finset.univ.erase u).erase (wn α))
    (hcz : c z₀ ≠ α) :
    pmSum W c ((Finset.univ.erase u).erase (wn α)) = 0 := by
  classical
  have hkey := pairK_named_monomial W hzero hvu wn hwu hvw hwinj hdiag hlone α hdead
    (fun w y => if y = c w then (1 : ℂ) else 0)
  rw [pairK_basis W (hwu α) c] at hkey
  have hprod : ∏ w ∈ (Finset.univ.erase u).erase (wn α),
      (if α = c w then (1 : ℂ) else 0) = 0 :=
    Finset.prod_eq_zero hz₀ (if_neg fun h => hcz h.symm)
  rw [hprod, mul_zero] at hkey
  exact (mul_eq_zero.mp hkey).resolve_left hlive

/-! ### The site carries its named partner's amplitude alone -/

/-- **A dead row makes the site carry its named partner.**  If the named blocks are single
diagonal entries and row `α` of the extra block is dead, then at the `α`-named partner every
colour-`α` edge other than the one back to the site contributes nothing in aggregate, against
every row: the site alone accounts for that partner's colour-`α` amplitude. -/
theorem named_carried_by_site (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hdead : ∀ b : Fin 3, W s((u, α), (v, b)) = 0) (a : Fin 3) :
    ∑ z ∈ (Finset.univ.erase (wn α)).erase u,
        W s((wn α, a), (z, α)) * pmSum W (Amplitude.const (V := V) α)
          ((Finset.univ.erase (wn α)).erase z) = 0 := by
  classical
  have hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0 :=
    fun j a b hb => hdiag j a b (Or.inr hb)
  have humem : u ∈ Finset.univ.erase (wn α) :=
    Finset.mem_erase.mpr ⟨fun h => hwu α h.symm, Finset.mem_univ u⟩
  have hswap : W s((wn α, a), (u, α)) = W s((u, α), (wn α, a)) := by
    rw [Sym2.eq_swap]
  have hcomm : (Finset.univ.erase (wn α)).erase u
      = (Finset.univ.erase u).erase (wn α) := Finset.erase_right_comm
  by_cases ha : a = α
  · -- the site's own edge already carries the whole amplitude
    subst ha
    have htot := flip_diag_eq W (wn a) a
    rw [← Finset.add_sum_erase _ _ humem, hswap] at htot
    have hval : pmSum W (Amplitude.const (V := V) a)
        ((Finset.univ.erase (wn a)).erase u)
        = pmSum W (Amplitude.const (V := V) a)
          ((Finset.univ.erase u).erase (wn a)) := by rw [hcomm]
    rw [hval] at htot
    have hfp := flip_pair W hvu wn hwu hvw hcol hlone a a
    rw [flip_diag_eq W u a, hdead a, zero_mul, add_zero] at hfp
    rw [← hfp] at htot
    linear_combination htot
  · have htot := flip_orthogonal W hzero (wn α) α a ha ⟨u, fun h => hwu α h.symm⟩
    rw [← Finset.add_sum_erase _ _ humem, hswap,
      hdiag α α a (Or.inr ha), zero_mul, zero_add] at htot
    exact htot

/-! ### Sparing the named partner -/

/-- **The named partner's complement, spared.**  Choose test vectors that annihilate the
extra's row in colour `α` and miss colour `α` somewhere.  The fan relation then leaves only
the `α`-named term, so the matching sum on the complement of the site and that partner
vanishes.  With a dead row the annihilation is automatic and this recovers the monomial;
with a live row it is a genuine condition, and the statement is new. -/
theorem pairK_named_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hlive : W s((u, α), (wn α, α)) ≠ 0)
    (ψ : V → Fin 3 → ℂ) (hψα : ψ (wn α) α = 1)
    (hann : (∑ b : Fin 3, ψ v b * W s((u, α), (v, b))) = 0)
    {z₀ : V} (hz₀ : z₀ ∈ Finset.univ.erase u) (hz : ψ z₀ α = 0) :
    pairK W u (wn α) 0 0 ψ = 0 := by
  classical
  have hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0 :=
    fun j a b hb => hdiag j a b (Or.inr hb)
  have hkey := fan_relation W hzero hvu wn hwu hvw hwinj hcol hlone α ψ
  have hlhs : amplitude W (Amplitude.const (V := V) α)
      * ∏ w ∈ Finset.univ.erase u, ψ w α = 0 := by
    rw [Finset.prod_eq_zero hz₀ hz, mul_zero]
  have hnamed : ∑ j : Fin 3, W s((u, α), (wn j, j)) * ψ (wn j) j
      * pairK W u (wn j) 0 0 ψ
      = W s((u, α), (wn α, α)) * pairK W u (wn α) 0 0 ψ := by
    rw [Finset.sum_eq_single_of_mem α (Finset.mem_univ α)]
    · rw [hψα, mul_one]
    · intro j _ hj
      rw [hdiag j α j (Or.inl fun h => hj h.symm), zero_mul, zero_mul]
  rw [hlhs, hann, zero_mul, zero_add, hnamed] at hkey
  exact (mul_eq_zero.mp hkey.symm).resolve_left hlive

/-- The colouring form. -/
theorem pmSum_named_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hlive : W s((u, α), (wn α, α)) ≠ 0)
    (c : V → Fin 3) (hcα : c (wn α) = α) (hann : W s((u, α), (v, c v)) = 0)
    {z₀ : V} (hz₀ : z₀ ∈ Finset.univ.erase u) (hz : c z₀ ≠ α) :
    pmSum W c ((Finset.univ.erase u).erase (wn α)) = 0 := by
  classical
  rw [← pairK_basis W (hwu α) c]
  refine pairK_named_zero W hzero hvu wn hwu hvw hwinj hdiag hlone α hlive _ ?_ ?_ hz₀ ?_
  · simp [hcα]
  · rw [Finset.sum_eq_single_of_mem (c v) (Finset.mem_univ _)
      (fun b _ hb => by rw [if_neg hb, zero_mul]), if_pos rfl, one_mul, hann]
  · exact if_neg fun h => hz h.symm

/-! ### The amplitude splits into two terms -/

/-- **Two terms, and no more.**  At a site whose live partners are its three named ones and a
single extra, a colouring that sends the site and its `α`-named partner both to colour `α`
splits the amplitude into exactly two pieces: the named edge times its complement's matching
sum, and the extra's edge times its complement's.  Every other named partner is killed by
diagonality on the row, and every other site by having no live edge at all.

This is the engine that consumes a non-inertness certificate: with the extra's complementary
sum known non-zero, the identity determines the named partner's complementary sum outright. -/
theorem amplitude_split (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (c : V → Fin 3) (hcu : c u = α) (hcw : c (wn α) = α) :
    amplitude W c
      = W s((u, α), (wn α, α)) * pmSum W c ((Finset.univ.erase u).erase (wn α))
        + W s((u, α), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v) := by
  classical
  have hexp : amplitude W c
      = ∑ y ∈ Finset.univ.erase u,
          W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y) := by
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl fun y _ => ?_
    first
      | rfl
      | (congr 1; simp [Sym2.map_pair_eq, paint])
  rw [hexp, hcu]
  have hsub : ({wn α, v} : Finset V) ⊆ Finset.univ.erase u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hwu α, Finset.mem_univ _⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub, Finset.sum_pair (fun h => hvw α h.symm), hcw]
  intro z hzmem hz
  have hzu : z ≠ u := (Finset.mem_erase.mp hzmem).1
  have hzw : z ≠ wn α := fun h => hz (by rw [h]; exact Finset.mem_insert_self _ _)
  have hzv : z ≠ v := fun h => hz (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  by_cases hj : ∀ j, z ≠ wn j
  · rw [hlone z hzu hzv hj α (c z), zero_mul]
  · push_neg at hj
    obtain ⟨j, hjz⟩ := hj
    have hjα : j ≠ α := fun h => hzw (by rw [hjz, h])
    rw [hjz, hdiag j α (c (wn j)) (Or.inl fun h => hjα h.symm), zero_mul]

/-- **The named complement is determined by the extra's row.**  On a non-constant colouring
sending the site and its `α`-named partner to `α`, the two pieces of the split cancel: the
named partner's complementary sum is the extra's row entry times the extra's complementary
sum, up to the named weight. -/
theorem named_complement_determined (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (c : V → Fin 3) (hcu : c u = α) (hcw : c (wn α) = α)
    (hnc : ¬ Amplitude.Monochromatic c) :
    W s((u, α), (wn α, α)) * pmSum W c ((Finset.univ.erase u).erase (wn α))
      = -(W s((u, α), (v, c v)) * pmSum W c ((Finset.univ.erase u).erase v)) := by
  have hsplit := amplitude_split W hvu wn hwu hvw hdiag hlone α c hcu hcw
  rw [hzero c hnc] at hsplit
  linear_combination -hsplit

/-- A dead entry at the colouring kills the named partner's complement. -/
theorem named_complement_eq_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (hlive : W s((u, α), (wn α, α)) ≠ 0)
    (c : V → Fin 3) (hcu : c u = α) (hcw : c (wn α) = α)
    (hnc : ¬ Amplitude.Monochromatic c) (hrow : W s((u, α), (v, c v)) = 0) :
    pmSum W c ((Finset.univ.erase u).erase (wn α)) = 0 := by
  have h := named_complement_determined W hzero hvu wn hwu hvw hdiag hlone α c hcu hcw hnc
  rw [hrow, zero_mul, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hlive

/-- A live entry, against a participating extra, hands a certificate to the named pair. -/
theorem named_complement_ne_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (c : V → Fin 3) (hcu : c u = α) (hcw : c (wn α) = α)
    (hnc : ¬ Amplitude.Monochromatic c) (hrow : W s((u, α), (v, c v)) ≠ 0)
    (hP : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) :
    pmSum W c ((Finset.univ.erase u).erase (wn α)) ≠ 0 := by
  intro h
  have hd := named_complement_determined W hzero hvu wn hwu hvw hdiag hlone α c hcu hcw hnc
  rw [h, mul_zero] at hd
  rcases mul_eq_zero.mp (neg_eq_zero.mp hd.symm) with h1 | h1
  · exact hrow h1
  · exact hP h1

/-- **A certificate that misses a colour kills that row.**  If a colouring sends the site to
`α` but its `α`-named partner elsewhere, every named term of the expansion dies --- the other
two on the row by diagonality, and this one because the partner is off its colour.  Only the
extra's term survives, so a non-vanishing complementary sum at the extra forces the entry to
be zero.

This is the form that consumes support minimality: on a minimal representative the
complementary sum at any live pair is non-zero for some colouring, and every such colouring
must then pin the named partner of every live row. -/
theorem row_eq_zero_of_certificate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (c : V → Fin 3) (hcu : c u = α) (hcw : c (wn α) ≠ α)
    (hnc : ¬ Amplitude.Monochromatic c)
    (hP : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) :
    W s((u, α), (v, c v)) = 0 := by
  classical
  have hexp : amplitude W c
      = ∑ y ∈ Finset.univ.erase u,
          W s((u, c u), (y, c y)) * pmSum W c ((Finset.univ.erase u).erase y) := by
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl fun y _ => ?_
    first
      | rfl
      | (congr 1; simp [Sym2.map_pair_eq, paint])
  have hsub : ({v} : Finset V) ⊆ Finset.univ.erase u := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    exact Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
  have hzero' : amplitude W c = W s((u, α), (v, c v))
      * pmSum W c ((Finset.univ.erase u).erase v) := by
    rw [hexp, hcu, ← Finset.sum_subset hsub, Finset.sum_singleton]
    intro z hzmem hz
    have hzu : z ≠ u := (Finset.mem_erase.mp hzmem).1
    have hzv : z ≠ v := fun h => hz (by rw [h]; exact Finset.mem_singleton_self _)
    by_cases hj : ∀ j, z ≠ wn j
    · rw [hlone z hzu hzv hj α (c z), zero_mul]
    · push_neg at hj
      obtain ⟨j, hjz⟩ := hj
      by_cases hjα : j = α
      · rw [hjz, hdiag j α (c (wn j)) (Or.inr (by rw [hjα]; exact hcw)), zero_mul]
      · rw [hjz, hdiag j α (c (wn j)) (Or.inl fun h => hjα h.symm), zero_mul]
  rw [hzero c hnc] at hzero'
  exact (mul_eq_zero.mp hzero'.symm).resolve_right hP

/-- Contrapositive: a live row pins its named partner on every certificate colouring. -/
theorem named_pinned_of_certificate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hdiag : ∀ j a b : Fin 3, (a ≠ j ∨ b ≠ j) → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (α : Fin 3) (c : V → Fin 3) (hcu : c u = α)
    (hnc : ¬ Amplitude.Monochromatic c)
    (hP : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0)
    (hrow : W s((u, α), (v, c v)) ≠ 0) : c (wn α) = α := by
  by_contra hcw
  exact hrow (row_eq_zero_of_certificate W hzero hvu wn hwu hvw hdiag hlone α c hcu hcw hnc hP)

/-- **A dead extra column gives diagonality for free.**  At a site whose live partners are its
three named ones and a single extra, if the extra's colour-`k` column is dead then that
colour's named block is the single diagonal entry --- no degeneracy hypothesis, no vanishing
matching sum, just the rank statement and the support.

Since the extra is live, at least one of its columns is alive; so this hands over diagonality
in every colour but those, and the remaining columns are genuine objects to analyse rather than
an undifferentiated obstruction. -/
theorem diag_of_dead_extra_column (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (k : Fin 3) (hdead : ∀ a : Fin 3, W s((u, a), (v, k)) = 0)
    {a : Fin 3} (ha : a ≠ k) : W s((u, a), (wn k, k)) = 0 := by
  classical
  refine SingleFlip.diag_of_unique_colour_column W hone hzero ⟨v, hvu⟩ (hwu k) k ?_ ha
  intro z hzu hzw a'
  by_cases hzv : z = v
  · rw [hzv]; exact hdead a'
  · by_cases hj : ∀ j, z ≠ wn j
    · exact hlone z hzu hzv hj a' k
    · push_neg at hj
      obtain ⟨j, hjz⟩ := hj
      have hjk : j ≠ k := fun h => hzw (by rw [hjz, h])
      rw [hjz]
      exact hcol j a' k (fun h => hjk h.symm)

/-- **The fan can be swapped onto a column-supported extra.**  If the extra block is
column-supported in one colour --- which is exactly the branch where only that colour's column
survives --- then exchanging the extra for that colour's named partner gives another valid
column fan, with the old named partner as the new extra.

So in that branch the site really has two column-supported partners in one colour, and every
site-local theorem can be applied from either side. -/
theorem fan_swap (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hfanlive : ∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn j, j)) ≠ 0)
    (m : Fin 3) (hvcol : ∀ a b : Fin 3, b ≠ m → W s((u, a), (v, b)) = 0)
    (hvlive : ∃ a : Fin 3, W s((u, a), (v, m)) ≠ 0) :
    ∃ wn' : Fin 3 → V, Function.Injective wn' ∧ (∀ j, wn' j ≠ u) ∧ wn' m = v ∧
      (∀ j, j ≠ m → wn' j = wn j) ∧
      (∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn' j, b)) = 0) ∧
      (∀ j : Fin 3, ∃ a : Fin 3, W s((u, a), (wn' j, j)) ≠ 0) := by
  classical
  refine ⟨Function.update wn m v, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = m <;> by_cases hj : j = m
    · rw [hi, hj]
    · rw [hi, Function.update_self, Function.update_of_ne hj] at hij
      exact absurd hij.symm (fun h => hvw j h.symm)
    · rw [hj, Function.update_self, Function.update_of_ne hi] at hij
      exact absurd hij (fun h => hvw i h.symm)
    · rw [Function.update_of_ne hi, Function.update_of_ne hj] at hij
      exact hwinj hij
  · intro j
    by_cases hj : j = m
    · rw [hj, Function.update_self]; exact hvu
    · rw [Function.update_of_ne hj]; exact hwu j
  · intro j hj; rw [Function.update_of_ne hj]
  · intro j a b hb
    by_cases hj : j = m
    · rw [hj, Function.update_self]
      exact hvcol a b (by rw [← hj]; exact hb)
    · rw [Function.update_of_ne hj]; exact hcol j a b hb
  · intro j
    by_cases hj : j = m
    · rw [hj, Function.update_self]
      obtain ⟨a, ha⟩ := hvlive
      exact ⟨a, ha⟩
    · rw [Function.update_of_ne hj]; exact hfanlive j

/-- **The off-colour named block is pinned by the other colours' complements.**  Colour a site
`k` everywhere except itself, which wears `a`, and the `m`-named partner, which wears `m`.
Column support kills every other named term --- the `k`-named one by diagonality since `a ≠ k`,
the rest because they are off their colour --- and the extra's term dies because its colour-`k`
column is dead.  Only the `m`-named term survives, so it vanishes.

This reaches the colour-`k` matching sum on the complement of the site and its `m`-named
partner, which no relation among the constant colourings touches: column support removes that
partner from every colour-`k` relation at the site.  A non-constant colouring does not. -/
theorem named_offcolour_pinned (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    {k m : Fin 3} (hkm : k ≠ m)
    (hdiagk : ∀ a : Fin 3, a ≠ k → W s((u, a), (wn k, k)) = 0)
    (hextra : ∀ a : Fin 3, W s((u, a), (v, k)) = 0)
    {a : Fin 3} (hak : a ≠ k) :
    W s((u, a), (wn m, m))
      * pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase (wn m)) = 0 := by
  classical
  set c : V → Fin 3 :=
    Function.update (Function.update (Amplitude.const (V := V) k) u a) (wn m) m with hc
  have hcu : c u = a := by
    rw [hc, Function.update_of_ne (fun h => hwu m h.symm), Function.update_self]
  have hcwm : c (wn m) = m := by rw [hc]; simp
  have hcoff : ∀ z : V, z ≠ u → z ≠ wn m → c z = k := by
    intro z hzu hzw
    rw [hc, Function.update_of_ne hzw, Function.update_of_ne hzu]; rfl
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨j, hj⟩
    have h1 : m = j := by rw [← hj (wn m), hcwm]
    have h2 : k = j := by
      rw [← hj (wn k), hcoff (wn k) (hwu k) (fun h => hkm (hwinj h))]
    exact hkm (h2.trans h1.symm)
  have hexp : amplitude W c
      = ∑ z ∈ Finset.univ.erase u,
          W s((u, c u), (z, c z)) * pmSum W c ((Finset.univ.erase u).erase z) := by
    rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ u)]
    refine Finset.sum_congr rfl fun z _ => ?_
    first
      | rfl
      | (congr 1; simp [Sym2.map_pair_eq, paint])
  have hmem : wn m ∈ Finset.univ.erase u :=
    Finset.mem_erase.mpr ⟨hwu m, Finset.mem_univ _⟩
  have hsingle : ∑ z ∈ Finset.univ.erase u,
      W s((u, c u), (z, c z)) * pmSum W c ((Finset.univ.erase u).erase z)
      = W s((u, a), (wn m, m)) * pmSum W c ((Finset.univ.erase u).erase (wn m)) := by
    rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr hmem), Finset.sum_singleton,
      hcu, hcwm]
    intro z hzmem hz
    have hzu : z ≠ u := (Finset.mem_erase.mp hzmem).1
    have hzw : z ≠ wn m := fun h => hz (by rw [h]; exact Finset.mem_singleton_self _)
    rw [hcu, hcoff z hzu hzw]
    by_cases hzv : z = v
    · rw [hzv, hextra a, zero_mul]
    · by_cases hj : ∀ j, z ≠ wn j
      · rw [hlone z hzu hzv hj a k, zero_mul]
      · push_neg at hj
        obtain ⟨j, hjz⟩ := hj
        by_cases hjk : j = k
        · rw [hjz, hjk, hdiagk a hak, zero_mul]
        · rw [hjz, hcol j a k (fun h => hjk h.symm), zero_mul]
  have hzeroamp : (0 : ℂ) = W s((u, a), (wn m, m))
      * pmSum W c ((Finset.univ.erase u).erase (wn m)) := by
    rw [← hzero c hnm, hexp, hsingle]
  have hsame : pmSum W c ((Finset.univ.erase u).erase (wn m))
      = pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase (wn m)) :=
    pmSum_congr_colour W fun z hz =>
      hcoff z (Finset.mem_erase.mp (Finset.mem_of_mem_erase hz)).1 (Finset.mem_erase.mp hz).1
  rw [← hsame]
  exact hzeroamp.symm

/-- **Some off-colour complement degenerates.**  Run the pinning for both colours other than
`m`.  If neither complement sum vanished, the `m`-named block's colour-`m` column would have to
point along two different basis vectors at once, hence be zero --- and the fan says it is not.

So at least one colour other than `m` has its matching sum vanishing on the complement of the
site and its `m`-named partner. -/
theorem exists_offcolour_degenerate (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hwinj : Function.Injective wn)
    (hcol : ∀ j a b : Fin 3, b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (m : Fin 3)
    (hdiag : ∀ k : Fin 3, k ≠ m → ∀ a : Fin 3, a ≠ k → W s((u, a), (wn k, k)) = 0)
    (hextra : ∀ k : Fin 3, k ≠ m → ∀ a : Fin 3, W s((u, a), (v, k)) = 0)
    (hlive : ∃ a : Fin 3, W s((u, a), (wn m, m)) ≠ 0) :
    ∃ k : Fin 3, k ≠ m ∧
      pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase (wn m)) = 0 := by
  classical
  by_contra hno
  push_neg at hno
  have hfin : ∀ b : Fin 3, b + 1 ≠ b ∧ b + 2 ≠ b ∧ b + 1 ≠ b + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hfin m
  have hM1 := hno (m + 1) h1
  have hM2 := hno (m + 2) h2
  obtain ⟨a, ha⟩ := hlive
  have hcover : ∀ a : Fin 3, a ≠ m + 1 ∨ a ≠ m + 2 := by
    intro a
    by_cases h : a = m + 1
    · exact Or.inr (by rw [h]; exact h12)
    · exact Or.inl h
  rcases hcover a with hne | hne
  · exact ha ((mul_eq_zero.mp (named_offcolour_pinned W hzero hvu wn hwu hvw hwinj hcol hlone
      (k := m + 1) (m := m) h1 (hdiag (m + 1) h1) (hextra (m + 1) h1)
      (a := a) hne)).resolve_right hM1)
  · exact ha ((mul_eq_zero.mp (named_offcolour_pinned W hzero hvu wn hwu hvw hwinj hcol hlone
      (k := m + 2) (m := m) h2 (hdiag (m + 2) h2) (hextra (m + 2) h2)
      (a := a) hne)).resolve_right hM2)

end Degenerate

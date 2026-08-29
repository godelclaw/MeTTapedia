import Mathlib
import Amplitude
import MatchingSum

/-!
# Matching sums factor across a cut

If no live edge joins a part to its complement, every matching that crosses contributes
nothing and the rest split, so the matching sum is the product of the two parts' sums.  The
proof is an induction on the part's size rather than a bijection between matchings: expand at
one of its sites, discard the crossing terms, and apply the induction to what is left.

The consequence for the equations is immediate and global: the live graph is connected.
Otherwise every amplitude factors, every part's constant sums are non-zero in every colour,
and colouring the two parts differently gives a non-constant colouring with non-zero
amplitude.
-/

namespace Separation

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The matching sum factors across a cut.** -/
theorem pmSum_split (W : Sym2 (V × Fin 3) → ℂ) (c : V → Fin 3) :
    ∀ (n : ℕ) (S T : Finset V), S.card = n → S ⊆ T →
      (∀ x ∈ S, ∀ y ∈ T \ S, W s((x, c x), (y, c y)) = 0) →
      pmSum W c T = pmSum W c S * pmSum W c (T \ S) :=
  MatchingSum.pmSum_factor_of_no_crossing W c

/-- **The live graph is connected.**  No non-trivial part of the sites is separated from its
complement by dead edges alone. -/
theorem no_cut (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Finset.univ \ S).Nonempty)
    (hcut : ∀ x ∈ S, ∀ y ∈ Finset.univ \ S, ∀ a b : Fin 3, W s((x, a), (y, b)) = 0) :
    False := by
  classical
  obtain ⟨p, hp⟩ := hS
  obtain ⟨q, hq⟩ := hSc
  set c : V → Fin 3 := fun z => if z ∈ S then 0 else 1 with hc
  have hsplit : ∀ d : V → Fin 3, pmSum W d Finset.univ
      = pmSum W d S * pmSum W d (Finset.univ \ S) := fun d =>
    pmSum_split W d S.card S Finset.univ rfl (Finset.subset_univ S)
      (fun x hx y hy => hcut x hx y hy _ _)
  -- both parts are non-zero in every colour
  have hpart : ∀ k : Fin 3, pmSum W (Amplitude.const (V := V) k) S ≠ 0
      ∧ pmSum W (Amplitude.const (V := V) k) (Finset.univ \ S) ≠ 0 := by
    intro k
    have := hone k
    rw [← pmSum_univ, hsplit] at this
    exact ⟨fun h => this (by rw [h, zero_mul]), fun h => this (by rw [h, mul_zero])⟩
  -- the two-colour colouring is not monochromatic
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨j, hj⟩
    have h1 : c p = 0 := by rw [hc]; exact if_pos hp
    have h2 : c q = 1 := by rw [hc]; exact if_neg (Finset.mem_sdiff.mp hq).2
    rw [hj p] at h1; rw [hj q] at h2
    exact absurd (h1.symm.trans h2) (by decide)
  -- yet its amplitude is a product of two non-zero numbers
  have hS0 : pmSum W c S = pmSum W (Amplitude.const (V := V) 0) S :=
    pmSum_congr_colour W fun z hz => by rw [hc]; exact if_pos hz
  have hSc1 : pmSum W c (Finset.univ \ S)
      = pmSum W (Amplitude.const (V := V) 1) (Finset.univ \ S) :=
    pmSum_congr_colour W fun z hz => by
      rw [hc]; exact if_neg (Finset.mem_sdiff.mp hz).2
  have hamp : amplitude W c ≠ 0 := by
    rw [← pmSum_univ, hsplit, hS0, hSc1]
    exact mul_ne_zero (hpart 0).1 (hpart 1).2
  exact hamp (hzero c hnm)

/-! ### Two colours cannot both respect the same cut -/

/-- **No set is closed in two colours.**  Suppose a non-empty proper set of sites has no live
colour-`k` edge and no live colour-`l` edge leaving it, and also no live edge from colour `l`
inside to colour `k` outside.  Then both monochromatic amplitudes factor across the cut, so
all four factors are non-zero; but the colouring that wears `l` inside and `k` outside has no
live edge crossing either, and it is not constant, so its amplitude vanishes while factoring
into two of those same non-zero numbers.

This is the alternating-cycle obstruction in set form: an alternating cycle of two colours
inside the three-regular part is exactly such a set, and cannot exist. -/
theorem no_two_colour_closed (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (C : Finset V) (hCne : C.Nonempty) (hCc : (Finset.univ \ C).Nonempty)
    {k l : Fin 3} (hkl : k ≠ l)
    (hcutk : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, k), (y, k)) = 0)
    (hcutl : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, l), (y, l)) = 0)
    (hcutm : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, l), (y, k)) = 0) : False := by
  classical
  obtain ⟨p, hp⟩ := hCne
  obtain ⟨q, hq⟩ := hCc
  -- both monochromatic amplitudes factor
  have hsplitk : pmSum W (Amplitude.const (V := V) k) Finset.univ
      = pmSum W (Amplitude.const (V := V) k) C
        * pmSum W (Amplitude.const (V := V) k) (Finset.univ \ C) :=
    pmSum_split W _ C.card C Finset.univ rfl (Finset.subset_univ C)
      (fun x hx y hy => hcutk x hx y hy)
  have hsplitl : pmSum W (Amplitude.const (V := V) l) Finset.univ
      = pmSum W (Amplitude.const (V := V) l) C
        * pmSum W (Amplitude.const (V := V) l) (Finset.univ \ C) :=
    pmSum_split W _ C.card C Finset.univ rfl (Finset.subset_univ C)
      (fun x hx y hy => hcutl x hx y hy)
  have hkne := hone k
  have hlne := hone l
  rw [← pmSum_univ, hsplitk] at hkne
  rw [← pmSum_univ, hsplitl] at hlne
  have hCl : pmSum W (Amplitude.const (V := V) l) C ≠ 0 := fun h => hlne (by rw [h, zero_mul])
  have hOk : pmSum W (Amplitude.const (V := V) k) (Finset.univ \ C) ≠ 0 :=
    fun h => hkne (by rw [h, mul_zero])
  -- the mixed colouring also respects the cut
  set c : V → Fin 3 := fun x => if x ∈ C then l else k with hc
  have hsplitc : pmSum W c Finset.univ = pmSum W c C * pmSum W c (Finset.univ \ C) := by
    refine pmSum_split W c C.card C Finset.univ rfl (Finset.subset_univ C) ?_
    intro x hx y hy
    have hcx : c x = l := by rw [hc]; exact if_pos hx
    have hcy : c y = k := by rw [hc]; exact if_neg (Finset.mem_sdiff.mp hy).2
    rw [hcx, hcy]
    exact hcutm x hx y hy
  have hCsame : pmSum W c C = pmSum W (Amplitude.const (V := V) l) C :=
    pmSum_congr_colour W fun z hz => by rw [hc]; exact if_pos hz
  have hOsame : pmSum W c (Finset.univ \ C)
      = pmSum W (Amplitude.const (V := V) k) (Finset.univ \ C) :=
    pmSum_congr_colour W fun z hz => by
      rw [hc]; exact if_neg (Finset.mem_sdiff.mp hz).2
  have hnm : ¬ Amplitude.Monochromatic c := by
    rintro ⟨j, hj⟩
    have h1 : c p = l := by rw [hc]; exact if_pos hp
    have h2 : c q = k := by rw [hc]; exact if_neg (Finset.mem_sdiff.mp hq).2
    rw [hj p] at h1; rw [hj q] at h2
    exact hkl (h2.symm.trans h1)
  have hamp : amplitude W c ≠ 0 := by
    rw [← pmSum_univ, hsplitc, hCsame, hOsame]
    exact mul_ne_zero hCl hOk
  exact hamp (hzero c hnm)

/-- **The usable direction: a mixed crossing edge must exist.**  Any non-empty proper set
closed under live edges in two colours carries, on its boundary, a live edge joining one of
those colours inside to the other outside --- and by symmetry in the two colours, one in each
direction.

This is the contrapositive of the closure theorem, and it is the form later arguments consume:
it turns a non-existence statement into an existence one. -/
theorem exists_mixed_crossing (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (C : Finset V) (hCne : C.Nonempty) (hCc : (Finset.univ \ C).Nonempty)
    {k l : Fin 3} (hkl : k ≠ l)
    (hcutk : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, k), (y, k)) = 0)
    (hcutl : ∀ x ∈ C, ∀ y ∈ Finset.univ \ C, W s((x, l), (y, l)) = 0) :
    ∃ x ∈ C, ∃ y ∈ Finset.univ \ C, W s((x, l), (y, k)) ≠ 0 := by
  by_contra h
  push_neg at h
  exact no_two_colour_closed W hone hzero C hCne hCc hkl hcutk hcutl h

/-! ### A rank-two flattening is impossible -/

/-- **The amplitude never splits into two products across a cut.**  If for some bipartition the
amplitude can be written as a sum of two terms, each a function of the colouring on one side
times a function of the colouring on the other, the equations are contradictory.

The reason is that the flattening of a GHZ amplitude across any bipartition has rank exactly
three: read at the constant colourings it is a diagonal matrix with non-zero entries, since a
colouring constant on each side but with different constants is not monochromatic. A sum of
two products has rank at most two.

This is the uniform principle behind the connectivity theorem — no crossing edge means one
product — and it applies wherever the crossing structure of a cut is thin enough. -/
theorem no_rank_two_flattening (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Finset.univ \ S).Nonempty)
    (f g : Fin 2 → (V → Fin 3) → ℂ)
    (hf : ∀ (j : Fin 2) (c c' : V → Fin 3), (∀ x ∈ S, c x = c' x) → f j c = f j c')
    (hg : ∀ (j : Fin 2) (c c' : V → Fin 3),
      (∀ x ∈ Finset.univ \ S, c x = c' x) → g j c = g j c')
    (hrep : ∀ c : V → Fin 3, amplitude W c = ∑ j : Fin 2, f j c * g j c) : False := by
  classical
  obtain ⟨p, hp⟩ := hS
  obtain ⟨q, hq⟩ := hSc
  -- the two-sided constant colourings
  set d : Fin 3 → Fin 3 → V → Fin 3 := fun k k' x => if x ∈ S then k else k' with hd
  have hdS : ∀ k k' x, x ∈ S → d k k' x = k := by intro k k' x hx; rw [hd]; exact if_pos hx
  have hdSc : ∀ k k' x, x ∈ Finset.univ \ S → d k k' x = k' := by
    intro k k' x hx; rw [hd]; exact if_neg (Finset.mem_sdiff.mp hx).2
  -- the flattening at those colourings is diagonal with non-zero entries
  have hdiag : ∀ k k' : Fin 3, amplitude W (d k k')
      = if k = k' then amplitude W (Amplitude.const (V := V) k) else 0 := by
    intro k k'
    by_cases hkk : k = k'
    · rw [if_pos hkk]
      congr 1
      funext x
      by_cases hx : x ∈ S
      · rw [hdS k k' x hx]; rfl
      · rw [hdSc k k' x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩), hkk]; rfl
    · rw [if_neg hkk]
      refine hzero _ ?_
      rintro ⟨j, hj⟩
      have h1 : k = j := by rw [← hj p, hdS k k' p hp]
      have h2 : k' = j := by
        rw [← hj q, hdSc k k' q hq]
      exact hkk (h1.trans h2.symm)
  -- three vectors in a two-dimensional space are dependent
  set F : Fin 3 → (Fin 2 → ℂ) := fun k j => f j (d k k) with hF
  obtain ⟨lam, hlam, i₀, hi₀⟩ :
      ∃ lam : Fin 3 → ℂ, ∑ k : Fin 3, lam k • F k = 0 ∧ ∃ i, lam i ≠ 0 := by
    have : ¬ LinearIndependent ℂ F := by
      intro hind
      have := hind.fintype_card_le_finrank
      simp [Module.finrank_pi] at this
    rw [Fintype.not_linearIndependent_iff] at this
    obtain ⟨lam, hsum, i, hi⟩ := this
    exact ⟨lam, hsum, i, hi⟩
  -- pair the relation against the diagonal
  have hkey : ∀ k' : Fin 3, lam k' * amplitude W (Amplitude.const (V := V) k') = 0 := by
    intro k'
    have hexp : ∑ k : Fin 3, lam k * amplitude W (d k k') = 0 := by
      have : ∀ k : Fin 3, amplitude W (d k k') = ∑ j : Fin 2, f j (d k k) * g j (d k' k') := by
        intro k
        rw [hrep (d k k')]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        · exact hf j _ _ (fun x hx => by rw [hdS k k' x hx, hdS k k x hx])
        · exact hg j _ _ (fun x hx => by rw [hdSc k k' x hx, hdSc k' k' x hx])
      rw [Finset.sum_congr rfl fun k _ => by rw [this k]]
      have hswap : ∑ k : Fin 3, lam k * ∑ j : Fin 2, F k j * g j (d k' k')
          = ∑ j : Fin 2, (∑ k : Fin 3, lam k * F k j) * g j (d k' k') := by
        rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.mul_sum _ _ _,
          Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hswap]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : (∑ k : Fin 3, lam k * F k j) = 0 := by
        have := congrFun hlam j
        simpa [Finset.sum_apply, smul_eq_mul] using this
      rw [this, zero_mul]
    rw [Finset.sum_congr rfl fun k _ => by rw [hdiag k k']] at hexp
    rw [Finset.sum_eq_single_of_mem k' (Finset.mem_univ k')
      (fun k _ hk => by rw [if_neg hk, mul_zero])] at hexp
    rw [if_pos rfl] at hexp
    exact hexp
  exact hi₀ ((mul_eq_zero.mp (hkey i₀)).resolve_right (hone i₀))

/-- **Two rank-one crossings at one site are too few.**  Let an odd part of the sites have all
its outward live edges at a single site, reaching at most two partners, with rank-one blocks.
Expanding at that site, the terms that keep it inside the part die on parity — the part minus
two sites is still odd — and what is left is two products across the cut.  A rank-two
flattening is impossible.

This strictly generalises the bridge theorem, which is the case of one outward partner. -/
theorem no_two_crossings_at_one_site (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Finset.univ \ S).Nonempty)
    (hodd : ¬ Even S.card)
    {x : V} (hxS : x ∈ S) {y₁ y₂ : V} (hy12 : y₁ ≠ y₂)
    (hy1 : y₁ ∈ Finset.univ \ S) (hy2 : y₂ ∈ Finset.univ \ S)
    (hcut : ∀ p ∈ S, ∀ q ∈ Finset.univ \ S, ∀ a b : Fin 3,
      (p ≠ x ∨ (q ≠ y₁ ∧ q ≠ y₂)) → W s((p, a), (q, b)) = 0)
    (α₁ β₁ α₂ β₂ : Fin 3 → ℂ)
    (h1 : ∀ a b : Fin 3, W s((x, a), (y₁, b)) = α₁ a * β₁ b)
    (h2 : ∀ a b : Fin 3, W s((x, a), (y₂, b)) = α₂ a * β₂ b) : False := by
  classical
  -- factorisation of any complement of `x` and one outside site
  have hsplit : ∀ (c : V → Fin 3) (T : Finset V), T ⊆ Finset.univ → x ∉ T →
      pmSum W c T = pmSum W c (T ∩ S) * pmSum W c (T \ (T ∩ S)) := by
    intro c T _ hxT
    refine pmSum_split W c (T ∩ S).card (T ∩ S) T rfl (Finset.inter_subset_left) ?_
    intro p hp q hq
    have hpS : p ∈ S := (Finset.mem_inter.mp hp).2
    have hpx : p ≠ x := fun h => hxT (h ▸ (Finset.mem_inter.mp hp).1)
    have hqT : q ∈ T := (Finset.mem_sdiff.mp hq).1
    have hqS : q ∉ S := fun h => (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mpr ⟨hqT, h⟩)
    exact hcut p hpS q (Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hqS⟩) _ _ (Or.inl hpx)
  -- the representation
  refine no_rank_two_flattening W hone hzero S hS hSc
    (fun j c => if j = 0 then α₁ (c x) * pmSum W c (S.erase x)
                else α₂ (c x) * pmSum W c (S.erase x))
    (fun j c => if j = 0 then β₁ (c y₁) * pmSum W c ((Finset.univ \ S).erase y₁)
                else β₂ (c y₂) * pmSum W c ((Finset.univ \ S).erase y₂)) ?_ ?_ ?_
  · intro j c c' hcc
    have hx : c x = c' x := hcc x hxS
    have hp : pmSum W c (S.erase x) = pmSum W c' (S.erase x) :=
      pmSum_congr_colour W fun z hz => hcc z (Finset.mem_of_mem_erase hz)
    by_cases hj : j = 0 <;> simp [hj, hx, hp]
  · intro j c c' hcc
    have h1' : c y₁ = c' y₁ := hcc y₁ hy1
    have h2' : c y₂ = c' y₂ := hcc y₂ hy2
    have hp1 : pmSum W c ((Finset.univ \ S).erase y₁)
        = pmSum W c' ((Finset.univ \ S).erase y₁) :=
      pmSum_congr_colour W fun z hz => hcc z (Finset.mem_of_mem_erase hz)
    have hp2 : pmSum W c ((Finset.univ \ S).erase y₂)
        = pmSum W c' ((Finset.univ \ S).erase y₂) :=
      pmSum_congr_colour W fun z hz => hcc z (Finset.mem_of_mem_erase hz)
    by_cases hj : j = 0 <;> simp [hj, h1', h2', hp1, hp2]
  · intro c
    have hexp : amplitude W c
        = ∑ z ∈ Finset.univ.erase x,
            W s((x, c x), (z, c z)) * pmSum W c ((Finset.univ.erase x).erase z) := by
      rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      first
        | rfl
        | (congr 1; simp [Sym2.map_pair_eq, paint])
    have hsub : ({y₁, y₂} : Finset V) ⊆ Finset.univ.erase x := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_sdiff.mp hy1).2 (h ▸ hxS),
          Finset.mem_univ _⟩
      · rw [Finset.mem_singleton] at hz
        subst hz
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_sdiff.mp hy2).2 (h ▸ hxS),
          Finset.mem_univ _⟩
    have hzero_off : ∀ z ∈ Finset.univ.erase x, z ∉ ({y₁, y₂} : Finset V) →
        W s((x, c x), (z, c z)) * pmSum W c ((Finset.univ.erase x).erase z) = 0 := by
      intro z hzmem hz
      have hzx : z ≠ x := (Finset.mem_erase.mp hzmem).1
      by_cases hzS : z ∈ S
      · -- parity kills it
        have hxT : x ∉ (Finset.univ.erase x).erase z :=
          fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
        have hinter : ((Finset.univ.erase x).erase z) ∩ S = (S.erase x).erase z := by
          ext w
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
          constructor
          · rintro ⟨⟨hw1, hw2⟩, hw3⟩; exact ⟨hw1, hw2, hw3⟩
          · rintro ⟨hw1, hw2, hw3⟩; exact ⟨⟨hw1, hw2⟩, hw3⟩
        have h2card : 2 ≤ S.card :=
          Finset.one_lt_card.mpr ⟨x, hxS, z, hzS, fun h => hzx h.symm⟩
        have hcard2 : ((S.erase x).erase z).card = S.card - 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hzx, hzS⟩),
            Finset.card_erase_of_mem hxS]
          omega
        have hoddz : ¬ Even ((S.erase x).erase z).card := by
          rw [hcard2, Nat.even_iff]
          rw [Nat.even_iff] at hodd
          omega
        rw [hsplit c _ (Finset.subset_univ _) hxT, hinter, pmSum_of_odd W c hoddz,
          zero_mul, mul_zero]
      · have hzc : z ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzS⟩
        have hz1 : z ≠ y₁ := fun h => hz (by rw [h]; exact Finset.mem_insert_self _ _)
        have hz2 : z ≠ y₂ := fun h => hz (by
          rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [hcut x hxS z hzc _ _ (Or.inr ⟨hz1, hz2⟩), zero_mul]
    have hfac : ∀ y : V, y ∈ Finset.univ \ S →
        pmSum W c ((Finset.univ.erase x).erase y)
          = pmSum W c (S.erase x) * pmSum W c ((Finset.univ \ S).erase y) := by
      intro y hy
      have hyS : y ∉ S := (Finset.mem_sdiff.mp hy).2
      have hxT : x ∉ (Finset.univ.erase x).erase y :=
        fun h => (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
      have hA : ((Finset.univ.erase x).erase y) ∩ S = S.erase x := by
        ext w
        simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · rintro ⟨⟨hw1, hw2⟩, hw3⟩; exact ⟨hw2, hw3⟩
        · rintro ⟨hw1, hw2⟩; exact ⟨⟨fun h => hyS (h ▸ hw2), hw1⟩, hw2⟩
      have hB : ((Finset.univ.erase x).erase y) \ S = (Finset.univ \ S).erase y := by
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
        constructor
        · rintro ⟨⟨hw1, hw2⟩, hw3⟩; exact ⟨hw1, hw3⟩
        · rintro ⟨hw1, hw2⟩; exact ⟨⟨hw1, fun h => hw2 (h ▸ hxS)⟩, hw2⟩
      rw [hsplit c _ (Finset.subset_univ _) hxT, Finset.sdiff_inter_self_left, hA, hB]
    rw [hexp, ← Finset.sum_subset hsub hzero_off, Finset.sum_pair hy12]
    rw [hfac y₁ hy1, hfac y₂ hy2, h1, h2, Fin.sum_univ_two]
    norm_num
    ring

end Separation

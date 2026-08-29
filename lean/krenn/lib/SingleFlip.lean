import Mathlib
import Amplitude
import MatchingSum

/-!
# Single flips

The only non-vanishing the equations hand us is at the constant colourings.  Every other
matching sum has to be traced back to those, and a colouring that differs from a constant
at exactly one site can be: expanding at the flipped site leaves the flipped edge carrying
the sole off-colour weight and a monochromatic sum behind it.

The consequence is an orthogonality: the vector of single-colour matching sums over the
complements of a site's edges is killed by that site's off-colour rows, and is not killed
by its own colour's row.
-/

namespace SingleFlip

open Amplitude MatchingSum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The matching sum of a colouring that differs from a constant at one site, written in
single-colour matching sums. -/
theorem pmSum_single_flip (W : Sym2 (V × Fin 3) → ℂ) {S : Finset V} {w : V} (hw : w ∈ S)
    (k₀ k₁ : Fin 3) :
    pmSum W (Function.update (Amplitude.const (V := V) k₀) w k₁) S
      = ∑ z ∈ S.erase w, W s((w, k₁), (z, k₀))
          * pmSum W (Amplitude.const (V := V) k₀) ((S.erase w).erase z) := by
  rw [pmSum_expand W _ hw]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hzw : z ≠ w := (Finset.mem_erase.mp hz).1
  have hc1 : Function.update (Amplitude.const (V := V) k₀) w k₁ w = k₁ := by simp
  have hc2 : Function.update (Amplitude.const (V := V) k₀) w k₁ z = k₀ := by
    rw [Function.update_of_ne hzw]; rfl
  have hpaint :
      W (Sym2.map (paint (Function.update (Amplitude.const (V := V) k₀) w k₁)) s(w, z))
        = W s((w, k₁), (z, k₀)) := by
    rw [show Sym2.map (paint (Function.update (Amplitude.const (V := V) k₀) w k₁)) s(w, z)
      = s((w, Function.update (Amplitude.const (V := V) k₀) w k₁ w),
          (z, Function.update (Amplitude.const (V := V) k₀) w k₁ z)) from rfl, hc1, hc2]
  rw [hpaint]
  congr 1
  refine pmSum_congr_colour W fun x hx => ?_
  have hxw : x ≠ w := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
  rw [Function.update_of_ne hxw]

/-- **The off-colour rows annihilate the single-colour sums.**  Flipping one site off the
constant colouring makes the amplitude vanish, and the flip formula reads that vanishing as
an orthogonality between the site's off-colour row and the vector of single-colour matching
sums over the complements of its edges. -/
theorem flip_orthogonal (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (w : V) (k₀ k₁ : Fin 3) (hk : k₁ ≠ k₀) (hV : ∃ x : V, x ≠ w) :
    ∑ z ∈ Finset.univ.erase w, W s((w, k₁), (z, k₀))
        * pmSum W (Amplitude.const (V := V) k₀)
            ((Finset.univ.erase w).erase z) = 0 := by
  obtain ⟨x, hx⟩ := hV
  have hnm : ¬ Amplitude.Monochromatic
      (Function.update (Amplitude.const (V := V) k₀) w k₁) := by
    rintro ⟨j, hj⟩
    have h1 : k₁ = j := by rw [← hj w]; simp
    have h2 : k₀ = j := by rw [← hj x, Function.update_of_ne hx]; rfl
    exact hk (h1.trans h2.symm)
  rw [← pmSum_single_flip W (Finset.mem_univ w) k₀ k₁, pmSum_univ]
  exact hzero _ hnm

/-- **Its own colour's row does not.**  The same expansion at the constant colouring returns
the amplitude, which the equations keep away from zero. -/
theorem flip_diag_eq (W : Sym2 (V × Fin 3) → ℂ) (w : V) (k₀ : Fin 3) :
    ∑ z ∈ Finset.univ.erase w, W s((w, k₀), (z, k₀))
        * pmSum W (Amplitude.const (V := V) k₀)
            ((Finset.univ.erase w).erase z)
      = amplitude W (Amplitude.const (V := V) k₀) := by
  have hupd : Function.update (Amplitude.const (V := V) k₀) w k₀
      = Amplitude.const (V := V) k₀ := by
    funext x
    by_cases h : x = w
    · subst h; simp [Amplitude.const]
    · rw [Function.update_of_ne h]
  rw [← pmSum_single_flip W (Finset.mem_univ w) k₀ k₀, hupd, pmSum_univ]

theorem flip_nonzero (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (w : V) (k₀ : Fin 3) :
    ∑ z ∈ Finset.univ.erase w, W s((w, k₀), (z, k₀))
        * pmSum W (Amplitude.const (V := V) k₀)
            ((Finset.univ.erase w).erase z) ≠ 0 := by
  rw [flip_diag_eq W w k₀]
  exact hone k₀

/-! ### Diagonality from a vanishing complementary sum -/

variable {W : Sym2 (V × Fin 3) → ℂ}

/-- The flip relation with the sum confined by column support.  At a site whose live
partners are its three named ones and a single extra, only the colour's own named partner
and that extra can contribute. -/
theorem flip_pair (W : Sym2 (V × Fin 3) → ℂ) {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ (j : Fin 3) (a b : Fin 3), b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (k a : Fin 3) :
    ∑ z ∈ Finset.univ.erase u, W s((u, a), (z, k))
        * pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase z)
      = W s((u, a), (wn k, k))
          * pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase (wn k))
        + W s((u, a), (v, k))
          * pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) := by
  classical
  have hsub : ({wn k, v} : Finset V) ⊆ Finset.univ.erase u := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hwu k, Finset.mem_univ _⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub, Finset.sum_pair (fun h => hvw k h.symm)]
  intro z hzmem hz
  have hzu : z ≠ u := (Finset.mem_erase.mp hzmem).1
  have hzw : z ≠ wn k := fun h => hz (by rw [h]; exact Finset.mem_insert_self _ _)
  have hzv : z ≠ v := fun h => hz (by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  by_cases hj : ∀ j, z ≠ wn j
  · rw [hlone z hzu hzv hj a k, zero_mul]
  · push_neg at hj
    obtain ⟨j, hjz⟩ := hj
    have hjk : j ≠ k := fun h => hzw (by rw [hjz, h])
    rw [hjz, hcol j a k (fun h => hjk h.symm), zero_mul]

/-- **Diagonality from a vanishing complementary sum.**  If the colour-`k` matching sum on
the complement of the site and its single extra partner vanishes, the colour-`k` named block
is the single diagonal entry. -/
theorem diag_of_complement_zero (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hvu : v ≠ u)
    (wn : Fin 3 → V) (hwu : ∀ j, wn j ≠ u) (hvw : ∀ j, v ≠ wn j)
    (hcol : ∀ (j : Fin 3) (a b : Fin 3), b ≠ j → W s((u, a), (wn j, b)) = 0)
    (hlone : ∀ z : V, z ≠ u → z ≠ v → (∀ j, z ≠ wn j) → ∀ a b : Fin 3,
      W s((u, a), (z, b)) = 0)
    (k : Fin 3)
    (hm : pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) = 0)
    (a : Fin 3) (ha : a ≠ k) : W s((u, a), (wn k, k)) = 0 := by
  have hV : ∃ x : V, x ≠ u := ⟨v, hvu⟩
  have hdiag := flip_nonzero W hone u k
  rw [flip_pair W hvu wn hwu hvw hcol hlone k k, hm, mul_zero, add_zero] at hdiag
  have hmw : pmSum W (Amplitude.const (V := V) k)
      ((Finset.univ.erase u).erase (wn k)) ≠ 0 := by
    intro h; exact hdiag (by rw [h, mul_zero])
  have hoff := flip_orthogonal W hzero u k a ha hV
  rw [flip_pair W hvu wn hwu hvw hcol hlone k a, hm, mul_zero, add_zero] at hoff
  rcases mul_eq_zero.mp hoff with h | h
  · exact h
  · exact absurd h hmw

/-! ### No covector annihilates a site -/

/-- **Each colour's columns at a site already span its own direction.**  A covector
annihilating every colour-`k` column at a site has zero `k`-component: contracting the flip
relation against it makes the colour-`k` amplitude vanish.

Equivalently `e_k` lies in the span of the colour-`k` columns at every site --- a rank
statement per colour, holding at every site of every solution with no hypothesis on the
support.  It is the dual of the column lemma: the fan says each colour has a column-supported
partner, this says that colour's columns reach that colour's direction. -/
theorem colour_column_span (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (x : V) (hV : ∃ z : V, z ≠ x) (ρ : Fin 3 → ℂ) (k : Fin 3)
    (hann : ∀ (y : V), y ≠ x → (∑ a : Fin 3, ρ a * W s((x, a), (y, k))) = 0) :
    ρ k = 0 := by
  classical
  set N : V → ℂ := fun z =>
    pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase x).erase z) with hN
  have hrow : ∀ a : Fin 3,
      ∑ z ∈ Finset.univ.erase x, W s((x, a), (z, k)) * N z
        = if a = k then amplitude W (Amplitude.const (V := V) k) else 0 := by
    intro a
    by_cases hak : a = k
    · rw [if_pos hak, hak]; exact flip_diag_eq W x k
    · rw [if_neg hak]; exact flip_orthogonal W hzero x k a hak hV
  have hkey : ρ k * amplitude W (Amplitude.const (V := V) k) = 0 := by
    have hL : ∑ a : Fin 3, ρ a * (if a = k then amplitude W (Amplitude.const (V := V) k)
        else 0) = ρ k * amplitude W (Amplitude.const (V := V) k) := by
      rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
        (fun a _ ha => by rw [if_neg ha, mul_zero]), if_pos rfl]
    rw [← hL]
    rw [Finset.sum_congr rfl fun a _ => by rw [← hrow a]]
    have hswap : ∑ a : Fin 3, ρ a * ∑ z ∈ Finset.univ.erase x, W s((x, a), (z, k)) * N z
        = ∑ z ∈ Finset.univ.erase x, (∑ a : Fin 3, ρ a * W s((x, a), (z, k))) * N z := by
      rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => Finset.mul_sum _ _ _,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hswap]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [hann z (Finset.mem_erase.mp hz).1, zero_mul]
  exact (mul_eq_zero.mp hkey).resolve_right (hone k)

/-- **The blocks at a site span the colour space.**  No non-zero covector annihilates every
block at a site; equivalently the horizontal stack of a site's blocks has full rank three. -/
theorem no_annihilating_covector (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (x : V) (hV : ∃ z : V, z ≠ x) (ρ : Fin 3 → ℂ)
    (hann : ∀ (y : V), y ≠ x → ∀ b : Fin 3, (∑ a : Fin 3, ρ a * W s((x, a), (y, b))) = 0) :
    ρ = 0 := by
  funext k
  exact colour_column_span W hone hzero x hV ρ k (fun y hy => hann y hy k)

/-- **Diagonality from a support condition alone.**  If a site's only partner with a live
colour-`k` column is that colour's named partner, then the block's colour-`k` column is a
multiple of `e_k`: its only live entry is the diagonal one.

Because `e_k` lies in the span of the colour-`k` columns and there is only one of them, that
column must point along `e_k`.  No degeneracy hypothesis is needed --- this derives diagonality
from where the support is, not from a vanishing matching sum. -/
theorem diag_of_unique_colour_column (W : Sym2 (V × Fin 3) → ℂ)
    (hone : ∀ j : Fin 3, amplitude W (Amplitude.const (V := V) j) ≠ 0)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u : V} (hV : ∃ z : V, z ≠ u) {p : V} (hpu : p ≠ u) (k : Fin 3)
    (hother : ∀ z : V, z ≠ u → z ≠ p → ∀ a : Fin 3, W s((u, a), (z, k)) = 0)
    {a : Fin 3} (ha : a ≠ k) : W s((u, a), (p, k)) = 0 := by
  classical
  by_contra hne
  set ρ : Fin 3 → ℂ := fun j =>
    if j = k then W s((u, a), (p, k))
    else if j = a then -(W s((u, k), (p, k))) else 0 with hρ
  have hρk : ρ k = W s((u, a), (p, k)) := by rw [hρ]; simp
  have hρa : ρ a = -(W s((u, k), (p, k))) := by
    rw [hρ]; simp [ha]
  have hρ0 : ∀ j : Fin 3, j ≠ k → j ≠ a → ρ j = 0 := by
    intro j hjk hja; rw [hρ]; simp [hjk, hja]
  have hann : ∀ y : V, y ≠ u → (∑ j : Fin 3, ρ j * W s((u, j), (y, k))) = 0 := by
    intro y hyu
    by_cases hyp : y = p
    · subst hyp
      rw [Finset.sum_eq_add_of_mem k a (Finset.mem_univ k) (Finset.mem_univ a)
        (fun h => ha h.symm) (fun j _ hj => by rw [hρ0 j hj.1 hj.2, zero_mul])]
      rw [hρk, hρa]; ring
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [hother y hyu hyp j, mul_zero]
  exact hne (hρk ▸ colour_column_span W hone hzero u hV ρ k hann)

end SingleFlip

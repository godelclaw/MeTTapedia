import Mathlib
import Amplitude
import MatchingSum
import PurePartner

/-!
# The spared relation for a covector

Expanding the test sum at a site isolates, for each row of that site's colour, the matchings
that join it to one spared partner.  The rows can be combined into a single covector
statement, and that is what a separation argument needs: a covector is free to annihilate a
subspace, a single row is not.

The one obstacle is bookkeeping.  The paired sum carries two vestigial colour pins, one at
each end of the spared edge; they select a value and contribute nothing, so the sum does not
depend on them, and the rows can be added.
-/

namespace Covector

open Amplitude MatchingSum PurePartner

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colour pins in the paired sum are vestigial. -/
theorem pairK_pin_indep (W : Sym2 (V × Fin 3) → ℂ) {u₁ u₂ : V} (h : u₂ ≠ u₁)
    (α β α' β' : Fin 3) (ψ : V → Fin 3 → ℂ) :
    pairK W u₁ u₂ α β ψ = pairK W u₁ u₂ α' β' ψ := by
  classical
  have h1 : u₁ ≠ u₂ := fun hc => h hc.symm
  have hsw : ∀ p q x : Fin 3, (Equiv.swap p q x = q) ↔ (x = p) := by
    intro p q x
    constructor
    · intro hx
      have := congrArg (Equiv.swap p q) hx
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    · intro hx; subst hx; exact Equiv.swap_apply_left _ _
  set e : (V → Fin 3) → (V → Fin 3) := fun c =>
    Function.update (Function.update c u₁ (Equiv.swap α α' (c u₁))) u₂
      (Equiv.swap β β' (c u₂)) with he
  have he1 : ∀ c, e c u₁ = Equiv.swap α α' (c u₁) := by
    intro c; rw [he]; simp [Function.update_of_ne h1]
  have he2 : ∀ c, e c u₂ = Equiv.swap β β' (c u₂) := by
    intro c; rw [he]; simp
  have he3 : ∀ c w, w ≠ u₁ → w ≠ u₂ → e c w = c w := by
    intro c w hw1 hw2; rw [he]; simp [Function.update_of_ne hw1, Function.update_of_ne hw2]
  have hinv : Function.Involutive e := by
    intro c
    funext w
    by_cases hw2 : w = u₂
    · subst hw2
      rw [he2, he2, Equiv.swap_apply_self]
    · by_cases hw1 : w = u₁
      · subst hw1
        rw [he1, he1, Equiv.swap_apply_self]
      · rw [he3 _ _ hw1 hw2, he3 _ _ hw1 hw2]
  set S : Finset V := (Finset.univ.erase u₁).erase u₂ with hS
  have hSne : ∀ w ∈ S, w ≠ u₁ ∧ w ≠ u₂ := by
    intro w hw
    exact ⟨(Finset.mem_erase.mp (Finset.mem_of_mem_erase hw)).1, (Finset.mem_erase.mp hw).1⟩
  have hkey : ∀ c : V → Fin 3,
      ((if e c u₁ = α' then (1 : ℂ) else 0) * (if e c u₂ = β' then 1 else 0)
          * pmSum W (e c) S * ∏ w ∈ S, ψ w (e c w))
        = ((if c u₁ = α then (1 : ℂ) else 0) * (if c u₂ = β then 1 else 0)
          * pmSum W c S * ∏ w ∈ S, ψ w (c w)) := by
    intro c
    have hp : pmSum W (e c) S = pmSum W c S :=
      pmSum_congr_colour W fun w hw => he3 c w (hSne w hw).1 (hSne w hw).2
    have hq : ∏ w ∈ S, ψ w (e c w) = ∏ w ∈ S, ψ w (c w) :=
      Finset.prod_congr rfl fun w hw => by rw [he3 c w (hSne w hw).1 (hSne w hw).2]
    have hA : (if Equiv.swap α α' (c u₁) = α' then (1 : ℂ) else 0)
        = (if c u₁ = α then (1 : ℂ) else 0) := if_congr (hsw α α' (c u₁)) rfl rfl
    have hB : (if Equiv.swap β β' (c u₂) = β' then (1 : ℂ) else 0)
        = (if c u₂ = β then (1 : ℂ) else 0) := if_congr (hsw β β' (c u₂)) rfl rfl
    rw [he1, he2, hp, hq, hA, hB]
  have hsum := Equiv.sum_comp (hinv.toPerm e)
    (fun c : V → Fin 3 => (if c u₁ = α' then (1 : ℂ) else 0) * (if c u₂ = β' then 1 else 0)
      * pmSum W c S * ∏ w ∈ S, ψ w (c w))
  simp only [Function.Involutive.coe_toPerm] at hsum
  rw [pairK, pairK, ← hsum]
  exact (Finset.sum_congr rfl fun c _ => hkey c).symm

/-- **The spared relation for a covector.**  Expanding at a site and combining the rows
against a covector: each partner contributes its covector-contracted block times the paired
sum on the complement, and the total is the covector read against the constant amplitudes. -/
theorem covector_expand (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    (u : V) (ρ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ) :
    ∑ v ∈ Finset.univ.erase u,
        (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))))
          * pairK W u v 0 0 ψ
      = ∑ a : Fin 3, ρ a * amplitude W (Amplitude.const (V := V) a)
          * ∏ w ∈ Finset.univ.erase u, ψ w a := by
  classical
  have hrow : ∀ a : Fin 3,
      amplitude W (Amplitude.const (V := V) a) * ∏ w ∈ Finset.univ.erase u, ψ w a
        = ∑ v ∈ Finset.univ.erase u,
            (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))) * pairK W u v 0 0 ψ := by
    intro a
    rw [← testSum_eq W hzero u a ψ, testSum_expand_full W u a ψ]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [pairK_pin_indep W (Finset.mem_erase.mp hv).1 a a 0 0 ψ]
  calc ∑ v ∈ Finset.univ.erase u,
        (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))))
          * pairK W u v 0 0 ψ
      = ∑ v ∈ Finset.univ.erase u, ∑ a : Fin 3,
          ρ a * ((∑ b : Fin 3, ψ v b * W s((u, a), (v, b))) * pairK W u v 0 0 ψ) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a : Fin 3, ρ a * ∑ v ∈ Finset.univ.erase u,
          (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))) * pairK W u v 0 0 ψ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ a : Fin 3, ρ a * amplitude W (Amplitude.const (V := V) a)
          * ∏ w ∈ Finset.univ.erase u, ψ w a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← hrow a, mul_assoc]

/-- **One partner spared.**  When the covector annihilates every partner's block but one,
that one carries the whole relation. -/
theorem covector_spared (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (ρ : Fin 3 → ℂ) (ψ : V → Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ w b * W s((u, a), (w, b)))) = 0) :
    (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ v b * W s((u, a), (v, b))))
        * pairK W u v 0 0 ψ
      = ∑ a : Fin 3, ρ a * amplitude W (Amplitude.const (V := V) a)
          * ∏ w ∈ Finset.univ.erase u, ψ w a := by
  classical
  rw [← covector_expand W hzero u ρ ψ]
  have hmem : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have hrest : ∑ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ w b * W s((u, a), (w, b))))
        * pairK W u w 0 0 ψ = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [hann w hw, zero_mul]
  rw [hrest, add_zero]

/-! ### Span domination without a diagonality hypothesis -/

/-- The paired sum only sees the test vectors on the complement. -/
theorem pairK_congr (W : Sym2 (V × Fin 3) → ℂ) (u v : V) (α β : Fin 3)
    {ψ ψ' : V → Fin 3 → ℂ}
    (h : ∀ w ∈ (Finset.univ.erase u).erase v, ψ w = ψ' w) :
    pairK W u v α β ψ = pairK W u v α β ψ' := by
  rw [pairK, pairK]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun w hw => by rw [h w hw]

/-- **Span domination.**  If a colouring of the complement misses every colour somewhere and
its matching sum does not vanish, the column image of the spared block lies in the span of
the columns that colouring selects.  Nothing is assumed about the named blocks. -/
theorem span_domination (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (c : V → Fin 3)
    (hnc : ∀ a : Fin 3, ∃ w ∈ (Finset.univ.erase u).erase v, c w ≠ a)
    (hc : pmSum W c ((Finset.univ.erase u).erase v) ≠ 0) (x : Fin 3 → ℂ) :
    (fun a : Fin 3 => ∑ b : Fin 3, W s((u, a), (v, b)) * x b)
      ∈ Submodule.span ℂ ((fun w : V => (fun a : Fin 3 => W s((u, a), (w, c w))))
          '' ↑((Finset.univ.erase u).erase v)) := by
  classical
  by_contra hnot
  obtain ⟨f, hfy, hfker⟩ := Submodule.exists_le_ker_of_notMem hnot
  set ρ : Fin 3 → ℂ := fun a => f (fun j => if a = j then (1 : ℂ) else 0) with hρ
  have hf : ∀ z : Fin 3 → ℂ, f z = ∑ a : Fin 3, z a * ρ a := by
    intro z
    rw [LinearMap.pi_apply_eq_sum_univ f z]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul]
  set ψ : V → Fin 3 → ℂ :=
    fun w y => if w = v then x y else (if y = c w then 1 else 0) with hψdef
  have hψS : ∀ w ∈ (Finset.univ.erase u).erase v,
      ψ w = fun y => if y = c w then (1 : ℂ) else 0 := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    funext y; rw [hψdef]; simp [hwv]
  have hψv : ∀ y, ψ v y = x y := by intro y; rw [hψdef]; simp
  have hcol : ∀ w ∈ (Finset.univ.erase u).erase v, ∀ a : Fin 3,
      (∑ b : Fin 3, ψ w b * W s((u, a), (w, b))) = W s((u, a), (w, c w)) := by
    intro w hw a
    rw [hψS w hw]
    simp
  have hann : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ w b * W s((u, a), (w, b)))) = 0 := by
    intro w hw
    have hmem : (fun a : Fin 3 => W s((u, a), (w, c w)))
        ∈ Submodule.span ℂ ((fun w : V => (fun a : Fin 3 => W s((u, a), (w, c w))))
            '' ↑((Finset.univ.erase u).erase v)) := Submodule.subset_span ⟨w, hw, rfl⟩
    have h0 := hfker hmem
    rw [LinearMap.mem_ker, hf] at h0
    rw [Finset.sum_congr rfl fun a _ => by rw [hcol w hw a]]
    rw [← h0]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hkey := covector_spared W hzero hv ρ ψ hann
  have hzeroRHS : ∑ a : Fin 3, ρ a * amplitude W (Amplitude.const (V := V) a)
      * ∏ w ∈ Finset.univ.erase u, ψ w a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    obtain ⟨w, hw, hwa⟩ := hnc a
    have hwmem : w ∈ Finset.univ.erase u := Finset.mem_of_mem_erase hw
    have hzero0 : ψ w a = 0 := by
      rw [hψS w hw]; exact if_neg fun h => hwa h.symm
    rw [Finset.prod_eq_zero hwmem hzero0, mul_zero]
  rw [hzeroRHS] at hkey
  have hpair : pairK W u v 0 0 ψ = pmSum W c ((Finset.univ.erase u).erase v) := by
    rw [pairK_congr W u v 0 0 hψS, pairK_basis W hv c]
  rw [hpair] at hkey
  have hlin : (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ v b * W s((u, a), (v, b)))) = 0 :=
    (mul_eq_zero.mp hkey).resolve_right hc
  apply hfy
  rw [hf]
  rw [← hlin]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by rw [hψv b]; ring

/-- **The spared relation at a constant colouring.**  The only colourings the equations keep
away from zero are the constant ones, so this is the case that carries a certificate: the
spared block's covector reading, times the colour's matching sum on the complement, is the
covector's own component in that colour times the amplitude. -/
theorem covector_constant (W : Sym2 (V × Fin 3) → ℂ)
    (hzero : ∀ c : V → Fin 3, ¬ Amplitude.Monochromatic c → amplitude W c = 0)
    {u v : V} (hv : v ≠ u) (k : Fin 3)
    (hS : ((Finset.univ.erase u).erase v).Nonempty) (ρ x : Fin 3 → ℂ)
    (hann : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, ρ a * W s((u, a), (w, k))) = 0) :
    (∑ a : Fin 3, ρ a * (∑ b : Fin 3, x b * W s((u, a), (v, b))))
        * pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v)
      = ρ k * amplitude W (Amplitude.const (V := V) k) * x k := by
  classical
  set ψ : V → Fin 3 → ℂ :=
    fun w y => if w = v then x y else (if y = k then 1 else 0) with hψdef
  have hψS : ∀ w ∈ (Finset.univ.erase u).erase v,
      ψ w = fun y => if y = Amplitude.const (V := V) k w then (1 : ℂ) else 0 := by
    intro w hw
    have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
    funext y; rw [hψdef]; simp [hwv, Amplitude.const]
  have hψv : ∀ y, ψ v y = x y := by intro y; rw [hψdef]; simp
  have hann' : ∀ w ∈ (Finset.univ.erase u).erase v,
      (∑ a : Fin 3, ρ a * (∑ b : Fin 3, ψ w b * W s((u, a), (w, b)))) = 0 := by
    intro w hw
    rw [← hann w hw]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    rw [hψS w hw]
    simp [Amplitude.const]
  have hkey := covector_spared W hzero hv ρ ψ hann'
  have hvmem : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩
  have hprod : ∀ a : Fin 3, ∏ w ∈ Finset.univ.erase u, ψ w a
      = x a * ∏ w ∈ (Finset.univ.erase u).erase v, ψ w a := by
    intro a
    rw [← Finset.mul_prod_erase _ _ hvmem, hψv a]
  have hRHS : ∑ a : Fin 3, ρ a * amplitude W (Amplitude.const (V := V) a)
      * ∏ w ∈ Finset.univ.erase u, ψ w a
      = ρ k * amplitude W (Amplitude.const (V := V) k) * x k := by
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · rw [hprod k]
      have : ∏ w ∈ (Finset.univ.erase u).erase v, ψ w k = 1 := by
        refine Finset.prod_eq_one fun w hw => ?_
        rw [hψS w hw]; simp [Amplitude.const]
      rw [this, mul_one]
    · intro a _ hak
      obtain ⟨w, hw⟩ := hS
      have : ψ w a = 0 := by rw [hψS w hw]; simp [Amplitude.const, hak]
      rw [hprod a, Finset.prod_eq_zero hw this, mul_zero, mul_zero]
  rw [hRHS] at hkey
  have hpair : pairK W u v 0 0 ψ
      = pmSum W (Amplitude.const (V := V) k) ((Finset.univ.erase u).erase v) := by
    rw [pairK_congr W u v 0 0 hψS, pairK_basis W hv (Amplitude.const (V := V) k)]
  rw [hpair] at hkey
  rw [← hkey]
  refine congrArg (· * _) (Finset.sum_congr rfl fun a _ => ?_)
  congr 1
  exact Finset.sum_congr rfl fun b _ => by rw [hψv b]

end Covector

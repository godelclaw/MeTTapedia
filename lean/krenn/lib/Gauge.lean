import Amplitude
import Mettapedia.Combinatorics.Matching.Gauge

/-!
# Gauge transformations of Krenn–Gu configurations

Generic colour and site gauges live in
`Mettapedia.Combinatorics.Matching.Gauge`.  This file records only their
consequences for the three-colour GHZ predicate.
-/

namespace Gauge

open Amplitude

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The normalisation is free.**  A GHZ configuration can be rescaled so that its
monochromatic amplitudes are exactly one, with every vanishing condition
preserved.  So requiring the value one rather than merely nonzero excludes no
solution. -/
theorem exists_normalized [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ) (h : KrennGu.IsGHZ W) :
    ∃ W' : Sym2 (V × Fin 3) → ℂ,
      (∀ k : Fin 3, amplitude W' (Amplitude.const k) = 1) ∧
      (∀ c : V → Fin 3, ¬ Monochromatic c → amplitude W' c = 0) := by
  obtain ⟨hne, hzero⟩ := h
  have hcard : 0 < Fintype.card V := Fintype.card_pos
  choose s hs using fun k : Fin 3 =>
    IsAlgClosed.exists_pow_nat_eq (amplitude W (Amplitude.const k))⁻¹ hcard
  refine ⟨fun e => colourScale s e * W e, fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_colourScale]
    have hprod : ∏ _v : V, s k = s k ^ Fintype.card V := by
      rw [Finset.prod_const, Finset.card_univ]
    have hconst : ∏ v : V, s (Amplitude.const k v) = s k ^ Fintype.card V := hprod
    rw [hconst, hs k, inv_mul_cancel₀ (hne k)]
  · rw [amplitude_colourScale, hzero c hc, mul_zero]

/-- **A solution stays a solution under any nowhere-vanishing gauge.** -/
theorem isGHZ_siteScale [Nonempty V] (W : Sym2 (V × Fin 3) → ℂ) (μ : V × Fin 3 → ℂ)
    (hμ : ∀ p, μ p ≠ 0) (h : KrennGu.IsGHZ W) :
    KrennGu.IsGHZ (fun e => siteScale μ e * W e) := by
  classical
  refine ⟨fun k => ?_, fun c hc => ?_⟩
  · rw [amplitude_siteScale W (Amplitude.const (V := V) k) μ]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun v _ => hμ _)) (h.1 k)
  · rw [amplitude_siteScale W c μ, h.2 c hc, mul_zero]


end Gauge

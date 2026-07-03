import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DyadicPancakeClosure

/-!
# Blockwise sufficiency interface for the scale-local pancake strain budget

`ScaleLocalPancakeStrainBudget` — the named open input of the dyadic
pancake closure — is stated at the level of the *summed* functionals: one
time envelope for the whole pancake-sector stretching sum
`Σ_{q≥Q} λ_q^{−2} ‖A_q ω_q^{pan}(t)‖_∞`.  Any analytic attack would instead
work scale by scale, and the 2026-07-03 repair analysis's own taxonomy
names three genuinely Navier–Stokes-specific mechanisms that could bound a
single dyadic block: pressure/Hessian feedback, multi-scale Biot–Savart
self-depletion, and frequency-cascade accounting.

This file machine-checks the summation step of that reduction:

* `BlockwisePancakeDecompositionData` packages a scale decomposition
  `blockStretch q t` of the pancake stretching sum together with one
  nonnegative envelope per mechanism at each scale, per-scale `D_Q`-gains
  summing to `gainTotal`, an integrable summed time budget, and the
  per-scale inequality bounding each block by its three envelopes plus its
  gain times `D_Q(t)`;
* `BlockwisePancakeDecomposition D B ε` is the public interface with
  explicit budget bound `B` and total-gain bound `ε`;
* `scaleLocalPancakeStrainBudget_of_blockwiseDecomposition` is the
  headline: summing the per-scale inequalities over the dyadic scales
  recovers `ScaleLocalPancakeStrainBudget D B ε`, so the blockwise
  interface is *sufficient* for the named open input.

No analytic content is claimed.  The reduction replaces the open summed
budget by open per-scale estimates, giving each candidate mechanism a named
face; nothing here proves any of the three per-scale estimates for the
Navier–Stokes strain on any data class.

## References

* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear
  Partial Differential Equations*, Springer 2011 (the dyadic blocks behind
  the per-scale functionals).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BlockwiseData

/-- A scale-by-scale (blockwise) decomposition of the pancake-sector
stretching sum, with one envelope per candidate mechanism.

In the notation of the 2026-07-03 repair analysis: `blockStretch q t` plays
the role of the single-block value `λ_q^{−2} ‖A_q ω_q^{pan}(t)‖_∞`, so the
summed functional `D.pancakeStretchSum t` is recovered by unconditional
summation over the dyadic scales `q`.  On `[0, T]` each block is bounded by
the sum of the three mechanism envelopes at its scale plus a per-scale gain
`gain q` times the full block sum `D_Q(t)`; the envelopes sum across scales
to the time budget `budgetFn t`, and the gains sum to `gainTotal`. -/
structure BlockwisePancakeDecompositionData
    (D : DyadicVorticityStretchingData) where
  /-- The pancake-sector stretching value carried by the single dyadic
  block at scale `q`. -/
  blockStretch : ℕ → ℝ → ℝ
  blockStretch_nonneg : ∀ q t, 0 ≤ blockStretch q t
  /-- The blocks decompose the summed pancake functional scale by scale. -/
  blockStretch_hasSum :
    ∀ t, HasSum (fun q => blockStretch q t) (D.pancakeStretchSum t)
  /-- Envelope of the pressure/Hessian feedback mechanism at scale `q`:
  the candidate per-scale bound extracted from the pressure Hessian's
  nonlocal reaction to the pancake configuration.  First of the three
  genuinely Navier–Stokes-specific mechanisms in the source analysis's
  taxonomy — one of the three faces of the open scale-local budget on
  which analysis can land. -/
  pressureEnvelope : ℕ → ℝ → ℝ
  pressureEnvelope_nonneg : ∀ q t, 0 ≤ pressureEnvelope q t
  /-- Envelope of the multi-scale Biot–Savart self-depletion mechanism at
  scale `q`: the candidate per-scale bound extracted from depletion of the
  strain that the vorticity's own pancake configuration generates through
  the Biot–Savart law.  Second of the three mechanisms. -/
  selfDepletionEnvelope : ℕ → ℝ → ℝ
  selfDepletionEnvelope_nonneg : ∀ q t, 0 ≤ selfDepletionEnvelope q t
  /-- Envelope of the frequency-cascade accounting mechanism at scale `q`:
  the candidate per-scale bound extracted from tracking how stretching is
  transferred across dyadic scales.  Third of the three mechanisms. -/
  cascadeEnvelope : ℕ → ℝ → ℝ
  cascadeEnvelope_nonneg : ∀ q t, 0 ≤ cascadeEnvelope q t
  /-- The `D_Q`-gain conceded at scale `q`. -/
  gain : ℕ → ℝ
  gain_nonneg : ∀ q, 0 ≤ gain q
  /-- The total gain across all scales. -/
  gainTotal : ℝ
  gain_hasSum : HasSum gain gainTotal
  /-- The summed time budget of the three mechanism envelopes. -/
  budgetFn : ℝ → ℝ
  budgetFn_integrable :
    IntervalIntegrable budgetFn MeasureTheory.volume 0 D.T
  /-- At each time the mechanism envelopes sum across scales to the
  budget. -/
  envelopes_hasSum : ∀ t, HasSum
    (fun q => pressureEnvelope q t + selfDepletionEnvelope q t +
      cascadeEnvelope q t)
    (budgetFn t)
  /-- The per-scale mechanism inequality on `[0, T]`: each block is bounded
  by its three envelopes plus its gain times the block sum. -/
  block_le : ∀ q : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) D.T,
    blockStretch q t ≤ pressureEnvelope q t + selfDepletionEnvelope q t +
      cascadeEnvelope q t + gain q * D.highBlockSum t

end BlockwiseData

section BlockwiseSufficiency

/-- **The blockwise pancake decomposition interface** with summed budget
bound `B` and total-gain bound `ε`: some blockwise decomposition of the
pancake stretching sum has its mechanism budget integrating to at most `B`
and its per-scale gains summing to at most `ε`.  This is a sufficient
interface for the open `ScaleLocalPancakeStrainBudget` (see
`scaleLocalPancakeStrainBudget_of_blockwiseDecomposition`), separating the
three candidate mechanisms scale by scale.  It is itself open for the
self-consistent Navier–Stokes strain: the only instance in this repository
is the rest state. -/
def BlockwisePancakeDecomposition (D : DyadicVorticityStretchingData)
    (B ε : ℝ) : Prop :=
  ∃ data : BlockwisePancakeDecompositionData D,
    (∫ t in (0 : ℝ)..D.T, data.budgetFn t) ≤ B ∧ data.gainTotal ≤ ε

/-- **Blockwise sufficiency for the scale-local strain budget:** summing
the per-scale mechanism inequalities over the dyadic scales yields
`ScaleLocalPancakeStrainBudget` with the same `(B, ε)`.  The proof is an
unconditional-summation comparison (`hasSum_le`) between the block
decomposition of the pancake sum and the envelope-plus-gain family, followed
by the gain estimate `gainTotal * D_Q(t) ≤ ε * D_Q(t)`; all analytic
content remains in the blockwise hypotheses. -/
theorem scaleLocalPancakeStrainBudget_of_blockwiseDecomposition
    (D : DyadicVorticityStretchingData) {B ε : ℝ}
    (h : BlockwisePancakeDecomposition D B ε) :
    ScaleLocalPancakeStrainBudget D B ε := by
  obtain ⟨data, hB, hgain⟩ := h
  refine ⟨data.budgetFn, data.budgetFn_integrable, hB, ?_⟩
  intro t ht
  have hrhs : HasSum
      (fun q => data.pressureEnvelope q t + data.selfDepletionEnvelope q t +
        data.cascadeEnvelope q t + data.gain q * D.highBlockSum t)
      (data.budgetFn t + data.gainTotal * D.highBlockSum t) :=
    (data.envelopes_hasSum t).add
      (data.gain_hasSum.mul_right (D.highBlockSum t))
  have hsum : D.pancakeStretchSum t ≤
      data.budgetFn t + data.gainTotal * D.highBlockSum t :=
    hasSum_le (fun q => data.block_le q t ht)
      (data.blockStretch_hasSum t) hrhs
  have hmul : data.gainTotal * D.highBlockSum t ≤ ε * D.highBlockSum t :=
    mul_le_mul_of_nonneg_right hgain (D.highBlockSum_nonneg t)
  linarith

end BlockwiseSufficiency

end NavierStokes
end FluidDynamics
end Mettapedia

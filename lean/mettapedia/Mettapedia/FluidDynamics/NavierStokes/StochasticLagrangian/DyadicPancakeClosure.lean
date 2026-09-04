import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingGate

/-!
# The dyadic pancake-closure skeleton and the scale-local strain-budget pin

The 2026-07-03 repair analysis for the stochastic-Lagrangian route (the
cotangent/Weber repair of NS-Proof-v7) reduces Beale–Kato–Majda continuation
to a *transported dyadic relaxation estimate*: with
`D_Q(t) = Σ_{q ≥ Q} ‖Δ_q ω(t)‖_∞`, the weighted stretching sums of the three
angular sectors (pancake, angularly coercive, paraproduct residual) control
`∫₀ᵀ D_Q` up to an absorbable `ε ∫₀ᵀ D_Q`, whence `∫₀ᵀ D_Q < ∞` and the BKM
integrand is controlled.  The pancake sector is the microlocal region where
the wave vector lies within aperture `δ_q = λ_q^{−1/2}` of a compressive
eigendirection of the low-frequency strain `A_q = S(S_{q−L}u)` and the
vorticity is near an expanding eigendirection; its target estimate is

`∫₀ᵀ Σ_{q ≥ Q} λ_q^{−2} ‖A_q ω_q^{pan}‖_∞ dt ≤ C(T,ν,u₀,Q) + ε ∫₀ᵀ D_Q dt.`

This file machine-checks the *skeleton* of that closure at the level of the
summed functionals:

* `DyadicVorticityStretchingData` packages the four time functionals and the
  transported relaxation inequality;
* `PancakeSectorEstimate` / `CoerciveSectorEstimate` /
  `ResidualSectorEstimate` are the three sector estimates with explicit
  constants and gains (no `o(1)`);
* `highBlockIntegral_le_of_sectorEstimates` performs the ε-absorption:
  if the three gains sum below `1`, then `∫₀ᵀ D_Q` is bounded with an
  explicit constant;
* `ScaleLocalPancakeStrainBudget` is **the named open input** (see its
  doc-comment for the adjudication record);
* `pancakeSectorEstimate_of_scaleLocalStrainBudget` derives the pancake
  sector estimate from the budget;
* `stochasticLagrangian_conditional_route_of_pancakeBudget` is the headline:
  momentum-transport data plus the budget (and the two sector interfaces)
  yield the Navier–Stokes equations with the representation pressure *and*
  interval-integrability of the BKM integrand with an explicit bound — the
  same endpoint as `stochasticLagrangian_conditional_route`, with the coarse
  gate `StochasticStretchingEstimate` replaced by the sharper geometric pin.

The a-priori finiteness used by the absorption (the left side of
`relaxation_bound` is a real number) is carried by the integrability fields;
in the analytic setting it is supplied by local-in-time regularity and a
continuation argument, which is standard and not re-derived here.

## References

* J. T. Beale, T. Kato, A. Majda, Comm. Math. Phys. **94** (1984), 61–66.
* P. Constantin, G. Iyer, Comm. Pure Appl. Math. **61** (2008), 330–345.
  arXiv:math/0511067.
* H. Bahouri, J.-Y. Chemin, R. Danchin, *Fourier Analysis and Nonlinear
  Partial Differential Equations*, Springer 2011 (Littlewood–Paley theory,
  Bony decomposition, the objects behind the dyadic functionals).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

section RelaxationData

/-- Time functionals of the transported dyadic relaxation estimate: the
high-frequency block sum `D_Q`, the three weighted stretching sums (pancake
sector, angularly coercive sector, paraproduct residual), and the relaxation
inequality tying them together on `[0, T]`.

Provenance of the fields, in the notation of the 2026-07-03 repair
analysis: `highBlockSum t = D_Q(t) = Σ_{q≥Q} ‖Δ_q ω(t)‖_∞`;
`pancakeStretchSum t = Σ_{q≥Q} λ_q^{−2} ‖A_q ω_q^{pan}(t)‖_∞` with
`A_q = S(S_{q−L}u)` and `ω_q^{pan} = Π_q^{pan} ω_q` the pancake-cone
projection at aperture `δ_q = λ_q^{−1/2}`; `coerciveStretchSum` the same sum
over the angularly coercive complement; `residualSum t =
Σ_{q≥Q} 2^{−2q} ‖R_q(t)‖_∞` the commutator/paraproduct residuals.  The
relaxation inequality is the Duhamel form of the dyadic damping estimate;
its constant depends on `(T, ν, u₀, Q)`. -/
structure DyadicVorticityStretchingData where
  /-- Time horizon. -/
  T : ℝ
  T_nonneg : 0 ≤ T
  /-- The high-frequency dyadic block sum `D_Q(t)`. -/
  highBlockSum : ℝ → ℝ
  highBlockSum_nonneg : ∀ t, 0 ≤ highBlockSum t
  highBlockSum_integrable :
    IntervalIntegrable highBlockSum MeasureTheory.volume 0 T
  /-- The pancake-sector weighted stretching sum. -/
  pancakeStretchSum : ℝ → ℝ
  pancakeStretchSum_nonneg : ∀ t, 0 ≤ pancakeStretchSum t
  pancakeStretchSum_integrable :
    IntervalIntegrable pancakeStretchSum MeasureTheory.volume 0 T
  /-- The angularly coercive weighted stretching sum. -/
  coerciveStretchSum : ℝ → ℝ
  coerciveStretchSum_nonneg : ∀ t, 0 ≤ coerciveStretchSum t
  coerciveStretchSum_integrable :
    IntervalIntegrable coerciveStretchSum MeasureTheory.volume 0 T
  /-- The paraproduct/commutator residual sum. -/
  residualSum : ℝ → ℝ
  residualSum_nonneg : ∀ t, 0 ≤ residualSum t
  residualSum_integrable :
    IntervalIntegrable residualSum MeasureTheory.volume 0 T
  /-- Constant of the transported dyadic relaxation estimate. -/
  relaxationConst : ℝ
  /-- The transported dyadic relaxation estimate: the block-sum integral is
  controlled by the constant plus the three sector integrals. -/
  relaxation_bound :
    (∫ t in (0 : ℝ)..T, highBlockSum t) ≤ relaxationConst +
      ((∫ t in (0 : ℝ)..T, pancakeStretchSum t) +
        (∫ t in (0 : ℝ)..T, coerciveStretchSum t) +
        (∫ t in (0 : ℝ)..T, residualSum t))

end RelaxationData

section SectorEstimates

variable (D : DyadicVorticityStretchingData)

/-- The pancake-sector estimate with explicit constant `C` and gain `ε`:
`∫₀ᵀ Σ_{q≥Q} λ_q^{−2} ‖A_q ω_q^{pan}‖_∞ dt ≤ C + ε ∫₀ᵀ D_Q dt`.  This is
the exact target estimate of the claimed pancake closure. -/
def PancakeSectorEstimate (C ε : ℝ) : Prop :=
  (∫ t in (0 : ℝ)..D.T, D.pancakeStretchSum t) ≤
    C + ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t

/-- The angularly coercive sector estimate (established in the source
analysis by the good-unknown/stretch–diffusion argument under its angular
coercivity condition; consumed here as a named interface, not re-proved). -/
def CoerciveSectorEstimate (C ε : ℝ) : Prop :=
  (∫ t in (0 : ℝ)..D.T, D.coerciveStretchSum t) ≤
    C + ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t

/-- The paraproduct-residual estimate (Coifman–Meyer/commutator bounds in
the source analysis; consumed here as a named interface, not re-proved). -/
def ResidualSectorEstimate (C ε : ℝ) : Prop :=
  (∫ t in (0 : ℝ)..D.T, D.residualSum t) ≤
    C + ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t

end SectorEstimates

section Absorption

/-- Absorption algebra: `a ≤ C + ε a` with `ε < 1` gives `a ≤ C/(1−ε)`. -/
theorem le_div_one_sub_of_le_add_mul {a C ε : ℝ} (hε : ε < 1)
    (h : a ≤ C + ε * a) : a ≤ C / (1 - ε) := by
  have h1 : 0 < 1 - ε := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

/-- **The ε-absorption closure of the transported dyadic relaxation
estimate:** if the three sector estimates hold with gains of total size
below `1`, the block-sum integral is bounded by an explicit constant.  This
is the "choose ε small enough to absorb" step of the source analysis, with
the a-priori finiteness carried by the integrability fields. -/
theorem highBlockIntegral_le_of_sectorEstimates
    (D : DyadicVorticityStretchingData) {Cp εp Cc εc Cr εr : ℝ}
    (hpan : PancakeSectorEstimate D Cp εp)
    (hcoh : CoerciveSectorEstimate D Cc εc)
    (hres : ResidualSectorEstimate D Cr εr)
    (hε : εp + εc + εr < 1) :
    (∫ t in (0 : ℝ)..D.T, D.highBlockSum t) ≤
      (D.relaxationConst + (Cp + Cc + Cr)) / (1 - (εp + εc + εr)) := by
  set I : ℝ := ∫ t in (0 : ℝ)..D.T, D.highBlockSum t with hI
  have hgain : εp * I + εc * I + εr * I = (εp + εc + εr) * I := by ring
  have hstep : I ≤ (D.relaxationConst + (Cp + Cc + Cr)) +
      (εp + εc + εr) * I := by
    have hrelax := D.relaxation_bound
    rw [← hI] at hrelax
    unfold PancakeSectorEstimate at hpan
    unfold CoerciveSectorEstimate at hcoh
    unfold ResidualSectorEstimate at hres
    rw [← hI] at hpan hcoh hres
    linarith [hgain]
  exact le_div_one_sub_of_le_add_mul hε hstep

end Absorption

section StrainBudgetPin

/-- **The scale-local pancake strain budget** (named analytic input;
**OPEN** — the first load-bearing missing lemma of the claimed pancake
closure).  It asserts a pointwise-in-time envelope for the pancake-sector
stretching sum: an integrable budget function plus a small multiple of the
block sum,

`Σ_{q≥Q} λ_q^{−2} ‖A_q ω_q^{pan}(t)‖_∞ ≤ budget(t) + ε · D_Q(t)`
  on `[0, T]`, with `∫₀ᵀ budget ≤ B`.

**Adjudication record (2026-07-03).**  The repair analysis isolates this
bound itself: after exhibiting the frozen-strain pancake packet on which
stochastic covariance depletion admits no uniform bound (machine-checked as
`frozenStrain_no_uniform_amplification_bound`), it states that "the
remaining burden is to prove the scale-local strain-budget bound for the
self-consistent NS strain."  Its subsequent claimed proof of the
pancake-sector estimate establishes two real ingredients — the single-mode
Biot–Savart null stretching (machine-checked exactly as
`strainRateApply_planeWaveVelocityMode_vorticity`) and the anisotropic
Bernstein gain on cones of aperture `λ_q^{−1/2}` — and then charges the
whole non-pancake complement to the stretch–diffusion (angularly coercive)
estimate.  Machine-checked, that charge is equivalent to this budget: the
two mechanisms tile the aperture range **iff** the local strain obeys
`γ ≤ ν λ_q` (`pancakeApertureCovered_iff_strain_le`), the uncovered band is
nonempty exactly when the budget fails (`anisotropic_coverage_gap`), and on
that band both mechanisms fail quantitatively
(`gapAperture_diffusionRate_lt_strain`,
`gapAperture_bernstein_volume_exceeds_planar_budget`).  The claimed proof
therefore consumes at its high-low split the statement it set out to prove,
and the budget remains open.  The budget also cannot be weakened to a
time-integrated hypothesis: the frozen-strain packet amplifies by at least
`e^{budget − 1}` over its coherent window
(`frozenStrainAmplification_peak_ge_exp_integratedStrain_sub_one`), so only
a pointwise-in-time composable envelope of the present shape can feed the
relaxation estimate.

**What a proof must supply:** for the actual Navier–Stokes strain
`A_q = S(S_{q−L}u)` — generated nonlocally from the vorticity by the
Biot–Savart law — a pointwise-in-time pancake-sector envelope with
integrable constant part and small `D_Q`-gain, via a genuinely
Navier–Stokes-specific mechanism (pressure/Hessian feedback, multi-scale
Biot–Savart self-depletion, or frequency-cascade accounting, in the source
analysis's own taxonomy).  Nothing in this repository proves it for any
data class.

A sufficient blockwise interface separating the three candidate mechanisms
(pressure/Hessian, Biot–Savart self-depletion, cascade accounting) is
`BlockwisePancakeDecomposition`; see `BlockwisePancakeDecomposition.lean`. -/
def ScaleLocalPancakeStrainBudget (D : DyadicVorticityStretchingData)
    (B ε : ℝ) : Prop :=
  ∃ budget : ℝ → ℝ,
    IntervalIntegrable budget MeasureTheory.volume 0 D.T ∧
    (∫ t in (0 : ℝ)..D.T, budget t) ≤ B ∧
    ∀ t ∈ Set.Icc (0 : ℝ) D.T,
      D.pancakeStretchSum t ≤ budget t + ε * D.highBlockSum t

/-- The scale-local strain budget yields the pancake-sector estimate with
the same gain (the time-integration step of the source analysis's
conditional pancake estimate, made explicit). -/
theorem pancakeSectorEstimate_of_scaleLocalStrainBudget
    (D : DyadicVorticityStretchingData) {B ε : ℝ}
    (hbudget : ScaleLocalPancakeStrainBudget D B ε) :
    PancakeSectorEstimate D B ε := by
  obtain ⟨budget, hint, hB, hpt⟩ := hbudget
  have hrhs_int : IntervalIntegrable
      (fun t => budget t + ε * D.highBlockSum t) MeasureTheory.volume 0 D.T :=
    hint.add (D.highBlockSum_integrable.const_mul ε)
  unfold PancakeSectorEstimate
  calc (∫ t in (0 : ℝ)..D.T, D.pancakeStretchSum t)
      ≤ ∫ t in (0 : ℝ)..D.T, (budget t + ε * D.highBlockSum t) :=
        intervalIntegral.integral_mono_on D.T_nonneg
          D.pancakeStretchSum_integrable hrhs_int hpt
    _ = (∫ t in (0 : ℝ)..D.T, budget t) +
          ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t := by
        rw [intervalIntegral.integral_add hint
          (D.highBlockSum_integrable.const_mul ε),
          intervalIntegral.integral_const_mul]
    _ ≤ B + ε * ∫ t in (0 : ℝ)..D.T, D.highBlockSum t := by
        exact add_le_add_left hB _

end StrainBudgetPin

section ConditionalRoute

/-- **The conditional route with the sharpened pin.**  Given
momentum-transport data `M` and dyadic relaxation data `D` whose block sum
dominates the high-frequency part of `‖curl u‖` (the Littlewood–Paley
decomposition interface `hdecomp`), if the scale-local pancake strain
budget holds and the coercive/residual sector interfaces hold with total
gain below `1`, then simultaneously:

1. the velocity satisfies the Navier–Stokes equations with the explicit
   representation pressure (the pushdown theorem, unconditional), and
2. for every point the Beale–Kato–Majda integrand `t ↦ ‖curl u(t, x)‖` is
   interval-integrable on `[0, T]` with an explicit integral bound.

This reaches the same endpoint as
`stochasticLagrangian_conditional_route`, with the coarse Jacobian gate
`StochasticStretchingEstimate` replaced by the sharper geometric input
`ScaleLocalPancakeStrainBudget` — the one load-bearing open lemma of the
claimed pancake closure, per its doc-comment. -/
theorem stochasticLagrangian_conditional_route_of_pancakeBudget
    (M : TransportedMomentumData) (D : DyadicVorticityStretchingData)
    (lowFrequencyPart : ℝ → ℝ)
    (hlow_nonneg : ∀ t, 0 ≤ lowFrequencyPart t)
    (hlow_int : IntervalIntegrable lowFrequencyPart MeasureTheory.volume 0 D.T)
    (hmeas : ∀ x : R3, MeasureTheory.AEStronglyMeasurable
      (fun t => curlField (M.u t) x) MeasureTheory.volume)
    (hdecomp : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x : R3,
      ‖curlField (M.u t) x‖ ≤ lowFrequencyPart t + D.highBlockSum t)
    {B εp Cc εc Cr εr : ℝ}
    (hbudget : ScaleLocalPancakeStrainBudget D B εp)
    (hcoh : CoerciveSectorEstimate D Cc εc)
    (hres : ResidualSectorEstimate D Cr εr)
    (hε : εp + εc + εr < 1) :
    (∀ t x, deriv (fun s => M.u s x) t + fderiv ℝ (M.u t) x (M.u t x) +
        gradField (M.pressure t) x = M.ν • coordLaplacian (M.u t) x) ∧
    (∀ x : R3,
      IntervalIntegrable (fun t => ‖curlField (M.u t) x‖)
        MeasureTheory.volume 0 D.T ∧
      ∫ t in (0 : ℝ)..D.T, ‖curlField (M.u t) x‖ ≤
        (∫ t in (0 : ℝ)..D.T, lowFrequencyPart t) +
          (D.relaxationConst + (B + Cc + Cr)) / (1 - (εp + εc + εr))) := by
  have hDbound := highBlockIntegral_le_of_sectorEstimates D
    (pancakeSectorEstimate_of_scaleLocalStrainBudget D hbudget) hcoh hres hε
  have hmaj : IntervalIntegrable
      (fun t => lowFrequencyPart t + D.highBlockSum t)
      MeasureTheory.volume 0 D.T :=
    hlow_int.add D.highBlockSum_integrable
  constructor
  · exact fun t x => M.navierStokes_of_transportedMomentum t x
  · intro x
    have hint : IntervalIntegrable (fun t => ‖curlField (M.u t) x‖)
        MeasureTheory.volume 0 D.T := by
      apply hmaj.mono_fun ((hmeas x).norm.restrict)
      refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
      refine Filter.Eventually.of_forall fun t ht => ?_
      have htIcc : t ∈ Set.Icc (0 : ℝ) D.T := by
        rw [Set.uIoc_of_le D.T_nonneg] at ht
        exact Set.Ioc_subset_Icc_self ht
      dsimp only
      rw [Real.norm_eq_abs, abs_norm, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hlow_nonneg t) (D.highBlockSum_nonneg t))]
      exact hdecomp t htIcc x
    refine ⟨hint, ?_⟩
    calc ∫ t in (0 : ℝ)..D.T, ‖curlField (M.u t) x‖
        ≤ ∫ t in (0 : ℝ)..D.T,
            (lowFrequencyPart t + D.highBlockSum t) := by
          apply intervalIntegral.integral_mono_on D.T_nonneg hint hmaj
          intro t ht
          exact hdecomp t ht x
      _ = (∫ t in (0 : ℝ)..D.T, lowFrequencyPart t) +
            ∫ t in (0 : ℝ)..D.T, D.highBlockSum t :=
          intervalIntegral.integral_add hlow_int D.highBlockSum_integrable
      _ ≤ (∫ t in (0 : ℝ)..D.T, lowFrequencyPart t) +
            (D.relaxationConst + (B + Cc + Cr)) /
              (1 - (εp + εc + εr)) :=
          add_le_add_right hDbound _

end ConditionalRoute

end NavierStokes
end FluidDynamics
end Mettapedia

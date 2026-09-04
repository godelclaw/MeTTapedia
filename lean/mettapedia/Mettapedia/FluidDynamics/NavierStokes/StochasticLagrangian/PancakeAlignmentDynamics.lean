import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DirectionEvolutionTilting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Dynamical damping of vorticity-direction misalignment

This module replaces a singular eigenframe-angle variable by the invariant
alignment energy

`E(xi,e) = 1 - <xi,e>²`.

For a unit vorticity direction `xi` and a unit expanding strain eigenvector
`e`, the transverse strain equation damps `E` at the exact rate

`-2 <xi,e>² (lambda - <xi,S xi>)`.

Motion of the eigenline and non-strain forcing appear as a separate scalar
forcing term.  A gap coercivity hypothesis then yields a linear residence
inequality while `E ≤ 1/2`.  The final lemma integrates any such inequality
and converts it into a bound for the strain-weighted residence integral.  No
inverse eigenvalue gap occurs in the definition of the alignment energy.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAlignmentDynamics

open MeasureTheory
open DirectionEvolutionTilting
open scoped Interval RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Sign-invariant squared misalignment between two directions. -/
def alignmentEnergy (xi e : R3) : ℝ :=
  1 - (inner ℝ xi e) ^ 2

/-- Exact derivative of the alignment energy for two differentiable vector
paths. -/
theorem hasDerivAt_alignmentEnergy
    {xi e : ℝ → R3} {eta theta : R3} {t : ℝ}
    (hxi : HasDerivAt xi eta t) (he : HasDerivAt e theta t) :
    HasDerivAt (fun s ↦ alignmentEnergy (xi s) (e s))
      (-2 * inner ℝ (xi t) (e t) *
        (inner ℝ eta (e t) + inner ℝ (xi t) theta)) t := by
  have hinner := hxi.inner ℝ he
  have hprod := hinner.mul hinner
  simp only [alignmentEnergy, pow_two]
  have hraw := hprod.const_sub 1
  have hderiv :
      -((inner ℝ (xi t) theta + inner ℝ eta (e t)) *
          inner ℝ (xi t) (e t) +
        inner ℝ (xi t) (e t) *
          (inner ℝ (xi t) theta + inner ℝ eta (e t))) =
        -2 * inner ℝ (xi t) (e t) *
          (inner ℝ eta (e t) + inner ℝ (xi t) theta) := by
    ring
  have h := hraw.congr_deriv hderiv
  simpa only [Pi.mul_apply] using h

/-- The transverse strain rate paired with a strain eigenvector. -/
theorem inner_transverseComponent_strain_eigenvector
    (S : R3 →L[ℝ] R3) (xi e : R3) (lambda : ℝ)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (hSe : S e = lambda • e) :
    inner ℝ (transverseComponent xi (S xi)) e =
      (lambda - inner ℝ xi (S xi)) * inner ℝ xi e := by
  unfold transverseComponent
  rw [inner_sub_left, real_inner_smul_left, ← hSsymm xi e, hSe,
    real_inner_smul_right]
  ring

/-- Exact moving-eigenline alignment law.  The vector `d` contains the
non-strain part of the direction equation and `theta` is the eigenline rate. -/
theorem hasDerivAt_alignmentEnergy_of_directionEquation
    {xi e : ℝ → R3} {eta theta d : R3} {t lambda : ℝ}
    (S : R3 →L[ℝ] R3)
    (hxi : HasDerivAt xi eta t) (he : HasDerivAt e theta t)
    (heta : eta = transverseComponent (xi t) (S (xi t)) + d)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (hSe : S (e t) = lambda • e t) :
    HasDerivAt (fun s ↦ alignmentEnergy (xi s) (e s))
      (-2 * inner ℝ (xi t) (e t) *
        ((lambda - inner ℝ (xi t) (S (xi t))) *
            inner ℝ (xi t) (e t) +
          inner ℝ d (e t) + inner ℝ (xi t) theta)) t := by
  have hbase := hasDerivAt_alignmentEnergy hxi he
  convert hbase using 1
  rw [heta, inner_add_left,
    inner_transverseComponent_strain_eigenvector S (xi t) (e t)
      lambda hSsymm hSe]

/-- The alignment energy of two unit vectors is nonnegative. -/
theorem alignmentEnergy_nonneg {xi e : R3}
    (hxi : ‖xi‖ = 1) (he : ‖e‖ = 1) :
    0 ≤ alignmentEnergy xi e := by
  have hinner : |inner ℝ xi e| ≤ 1 := by
    calc
      |inner ℝ xi e| ≤ ‖xi‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hxi, he, one_mul]
  unfold alignmentEnergy
  have hsquare : (inner ℝ xi e) ^ 2 ≤ 1 := by
    calc
      (inner ℝ xi e) ^ 2 = |inner ℝ xi e| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hinner 2
      _ = 1 := by norm_num
  linarith

/-! ## Rayleigh defect and spectral-gap coercivity -/

/-- In spectral coordinates, the deficit from the top Rayleigh quotient is
the sum of the two transverse squared coordinates weighted by their spectral
gaps.  Keeping this scalar identity separate makes explicit exactly what the
later finite-dimensional spectral construction must provide. -/
theorem rayleighDefect_eq_weightedGaps
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2) :
    lambda₀ - rayleigh =
      (lambda₀ - lambda₁) * a₁ ^ 2 +
        (lambda₀ - lambda₂) * a₂ ^ 2 := by
  rw [hrayleigh]
  linear_combination -lambda₀ * hparseval

/-- A lower bound on both transverse spectral gaps makes the Rayleigh defect
coercive for the sign-invariant alignment energy. -/
theorem gap_mul_alignmentDefect_le_rayleighDefect
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh gap : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2)
    (hgap₁ : gap ≤ lambda₀ - lambda₁)
    (hgap₂ : gap ≤ lambda₀ - lambda₂) :
    gap * (1 - a₀ ^ 2) ≤ lambda₀ - rayleigh := by
  have htransverse : 1 - a₀ ^ 2 = a₁ ^ 2 + a₂ ^ 2 := by
    nlinarith [hparseval]
  rw [rayleighDefect_eq_weightedGaps lambda₀ lambda₁ lambda₂
    a₀ a₁ a₂ rayleigh hparseval hrayleigh, htransverse]
  calc
    gap * (a₁ ^ 2 + a₂ ^ 2) =
        gap * a₁ ^ 2 + gap * a₂ ^ 2 := by ring
    _ ≤ (lambda₀ - lambda₁) * a₁ ^ 2 +
          (lambda₀ - lambda₂) * a₂ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_right hgap₁ (sq_nonneg a₁))
        (mul_le_mul_of_nonneg_right hgap₂ (sq_nonneg a₂))

/-- If the full three-dimensional spectrum lies within `width` below its top
eigenvalue, the Rayleigh defect is at most `width` times the alignment
energy.  Thus complete near-degeneracy makes the anisotropic defect small
without choosing a rapidly rotating eigenvector. -/
theorem rayleighDefect_le_width_mul_alignmentDefect
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh width : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2)
    (hwidth₁ : lambda₀ - lambda₁ ≤ width)
    (hwidth₂ : lambda₀ - lambda₂ ≤ width) :
    lambda₀ - rayleigh ≤ width * (1 - a₀ ^ 2) := by
  have htransverse : 1 - a₀ ^ 2 = a₁ ^ 2 + a₂ ^ 2 := by
    nlinarith [hparseval]
  rw [rayleighDefect_eq_weightedGaps lambda₀ lambda₁ lambda₂
    a₀ a₁ a₂ rayleigh hparseval hrayleigh, htransverse]
  calc
    (lambda₀ - lambda₁) * a₁ ^ 2 +
          (lambda₀ - lambda₂) * a₂ ^ 2 ≤
        width * a₁ ^ 2 + width * a₂ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_right hwidth₁ (sq_nonneg a₁))
        (mul_le_mul_of_nonneg_right hwidth₂ (sq_nonneg a₂))
    _ = width * (a₁ ^ 2 + a₂ ^ 2) := by ring

/-- A spectrally narrow self-adjoint strain has uniformly small Rayleigh
defect. -/
theorem rayleighDefect_le_width
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh width : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2)
    (hwidth : 0 ≤ width)
    (hwidth₁ : lambda₀ - lambda₁ ≤ width)
    (hwidth₂ : lambda₀ - lambda₂ ≤ width) :
    lambda₀ - rayleigh ≤ width := by
  have hmain := rayleighDefect_le_width_mul_alignmentDefect
    lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh width
    hparseval hrayleigh hwidth₁ hwidth₂
  have henergy : 1 - a₀ ^ 2 ≤ 1 := by nlinarith [sq_nonneg a₀]
  calc
    lambda₀ - rayleigh ≤ width * (1 - a₀ ^ 2) := hmain
    _ ≤ width * 1 := mul_le_mul_of_nonneg_left henergy hwidth
    _ = width := mul_one width

/-- Route-facing spectral coercivity, expressed directly using the strain
operator and the vorticity/eigenframe coordinates. -/
theorem gap_mul_alignmentEnergy_le_strainDefect
    (S : R3 →L[ℝ] R3) (xi e₀ e₁ e₂ : R3)
    (lambda₀ lambda₁ lambda₂ gap : ℝ)
    (hparseval : (inner ℝ xi e₀) ^ 2 + (inner ℝ xi e₁) ^ 2 +
      (inner ℝ xi e₂) ^ 2 = 1)
    (hrayleigh : inner ℝ xi (S xi) =
      lambda₀ * (inner ℝ xi e₀) ^ 2 +
        lambda₁ * (inner ℝ xi e₁) ^ 2 +
        lambda₂ * (inner ℝ xi e₂) ^ 2)
    (hgap₁ : gap ≤ lambda₀ - lambda₁)
    (hgap₂ : gap ≤ lambda₀ - lambda₂) :
    gap * alignmentEnergy xi e₀ ≤
      lambda₀ - inner ℝ xi (S xi) := by
  unfold alignmentEnergy
  exact gap_mul_alignmentDefect_le_rayleighDefect
    lambda₀ lambda₁ lambda₂ (inner ℝ xi e₀) (inner ℝ xi e₁)
      (inner ℝ xi e₂) (inner ℝ xi (S xi)) gap
      hparseval hrayleigh hgap₁ hgap₂

/-- At each threshold, either a top-to-transverse spectral gap is small, or
the invariant alignment energy is coercively controlled by the strain
Rayleigh defect. -/
theorem smallGap_or_alignmentEnergy_coercive
    (S : R3 →L[ℝ] R3) (xi e₀ e₁ e₂ : R3)
    (lambda₀ lambda₁ lambda₂ gap : ℝ)
    (hparseval : (inner ℝ xi e₀) ^ 2 + (inner ℝ xi e₁) ^ 2 +
      (inner ℝ xi e₂) ^ 2 = 1)
    (hrayleigh : inner ℝ xi (S xi) =
      lambda₀ * (inner ℝ xi e₀) ^ 2 +
        lambda₁ * (inner ℝ xi e₁) ^ 2 +
        lambda₂ * (inner ℝ xi e₂) ^ 2) :
    (lambda₀ - lambda₁ < gap ∨ lambda₀ - lambda₂ < gap) ∨
      gap * alignmentEnergy xi e₀ ≤
        lambda₀ - inner ℝ xi (S xi) := by
  by_cases hgap₁ : gap ≤ lambda₀ - lambda₁
  · by_cases hgap₂ : gap ≤ lambda₀ - lambda₂
    · exact Or.inr (gap_mul_alignmentEnergy_le_strainDefect
        S xi e₀ e₁ e₂ lambda₀ lambda₁ lambda₂ gap
        hparseval hrayleigh hgap₁ hgap₂)
    · exact Or.inl (Or.inr (lt_of_not_ge hgap₂))
  · exact Or.inl (Or.inl (lt_of_not_ge hgap₁))

/-- Scalar damping estimate behind the residence argument. -/
theorem alignmentRate_le_damping_add_forcing
    (a defect E gap force : ℝ)
    (hEdef : E = 1 - a ^ 2) (hE : 0 ≤ E) (hEsmall : E ≤ 1 / 2)
    (hgap : 0 ≤ gap) (hcoercive : gap * E ≤ defect)
    (ha : |a| ≤ 1) :
    -2 * a * (defect * a + force) ≤ -gap * E + 2 * |force| := by
  have haSq : 1 / 2 ≤ a ^ 2 := by linarith
  have hgapE : 0 ≤ gap * E := mul_nonneg hgap hE
  have hdefect : 0 ≤ defect := hgapE.trans hcoercive
  have hdamping : gap * E ≤ 2 * a ^ 2 * defect := by
    calc
      gap * E ≤ defect := hcoercive
      _ = 1 * defect := by ring
      _ ≤ (2 * a ^ 2) * defect := by
        apply mul_le_mul_of_nonneg_right _ hdefect
        linarith
      _ = 2 * a ^ 2 * defect := by ring
  have hforce : -2 * a * force ≤ 2 * |force| := by
    calc
      -2 * a * force ≤ |-2 * a * force| := le_abs_self _
      _ = 2 * |a| * |force| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * 1 * |force| := by
        gcongr
      _ = 2 * |force| := by ring
  nlinarith

/-- Vector form of the gap-damped alignment estimate. -/
theorem alignmentRate_le_of_gapCoercivity
    (S : R3 →L[ℝ] R3) (xi e d theta : R3)
    (lambda gap : ℝ)
    (hxi : ‖xi‖ = 1) (he : ‖e‖ = 1)
    (hEsmall : alignmentEnergy xi e ≤ 1 / 2)
    (hgap : 0 ≤ gap)
    (hcoercive : gap * alignmentEnergy xi e ≤
      lambda - inner ℝ xi (S xi)) :
    -2 * inner ℝ xi e *
        ((lambda - inner ℝ xi (S xi)) * inner ℝ xi e +
          inner ℝ d e + inner ℝ xi theta) ≤
      -gap * alignmentEnergy xi e +
        2 * |inner ℝ d e + inner ℝ xi theta| := by
  have ha : |inner ℝ xi e| ≤ 1 := by
    calc
      |inner ℝ xi e| ≤ ‖xi‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hxi, he, one_mul]
  have h := alignmentRate_le_damping_add_forcing
    (inner ℝ xi e) (lambda - inner ℝ xi (S xi))
      (alignmentEnergy xi e) gap
      (inner ℝ d e + inner ℝ xi theta)
      rfl (alignmentEnergy_nonneg hxi he) hEsmall hgap hcoercive ha
  simpa only [add_assoc] using h

/-- Integration of a differential residence inequality.  If `rate` is the
integrated change of a nonnegative alignment energy and
`rate ≤ -weighted + forcing`, then the weighted residence is bounded by the
initial energy plus the forcing integral. -/
theorem weightedResidence_le_initial_add_forcing
    {T : ℝ} (hT : 0 ≤ T)
    (energy rate weighted forcing : ℝ → ℝ)
    (hrate : IntervalIntegrable rate volume 0 T)
    (hweighted : IntervalIntegrable weighted volume 0 T)
    (hforcing : IntervalIntegrable forcing volume 0 T)
    (hpoint : ∀ t ∈ Set.Icc (0 : ℝ) T,
      rate t ≤ -weighted t + forcing t)
    (hfundamental : (∫ t in (0 : ℝ)..T, rate t) =
      energy T - energy 0)
    (hterminal : 0 ≤ energy T) :
    (∫ t in (0 : ℝ)..T, weighted t) ≤
      energy 0 + ∫ t in (0 : ℝ)..T, forcing t := by
  have hsum : IntervalIntegrable (fun t ↦ -weighted t + forcing t)
      volume 0 T := hweighted.neg.add hforcing
  have hmono := intervalIntegral.integral_mono_on hT hrate hsum hpoint
  have hsplit :
      (∫ t in (0 : ℝ)..T, -weighted t + forcing t) =
        -(∫ t in (0 : ℝ)..T, weighted t) +
          ∫ t in (0 : ℝ)..T, forcing t := by
    calc
      (∫ t in (0 : ℝ)..T, -weighted t + forcing t) =
          (∫ t in (0 : ℝ)..T, (-weighted) t) +
            ∫ t in (0 : ℝ)..T, forcing t :=
        intervalIntegral.integral_add hweighted.neg hforcing
      _ = -(∫ t in (0 : ℝ)..T, weighted t) +
            ∫ t in (0 : ℝ)..T, forcing t := by
        have hneg : (∫ t in (0 : ℝ)..T, -weighted t) =
            -(∫ t in (0 : ℝ)..T, weighted t) :=
          intervalIntegral.integral_neg
        change (∫ t in (0 : ℝ)..T, -weighted t) +
            ∫ t in (0 : ℝ)..T, forcing t = _
        rw [hneg]
  rw [hfundamental, hsplit] at hmono
  linarith

/-! ## Integrated alignment residence for the moving strain eigenline -/

/-- On a gap-coercive interval, the exact direction/eigenline equations bound
the time spent misaligned by the initial alignment energy plus only two
forcing channels: the non-strain direction forcing and motion of the
expanding eigenline.

The hypotheses deliberately expose all analytic inputs.  In particular,
this theorem does not assume that an arbitrary measurable choice of
eigenvector is differentiable; a later gap-separated spectral-projector
construction must produce the path `e` and control `theta`. -/
theorem gapWeightedAlignmentResidence_le
    {T : ℝ} (hT : 0 ≤ T)
    (S : ℝ → R3 →L[ℝ] R3)
    (xi e eta theta d : ℝ → R3) (lambda gap : ℝ → ℝ)
    (hxi : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt xi (eta t) t)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt e (theta t) t)
    (heta : ∀ t ∈ Set.Icc (0 : ℝ) T,
      eta t = transverseComponent (xi t) (S t (xi t)) + d t)
    (hSsymm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ u v : R3,
      inner ℝ u (S t v) = inner ℝ (S t u) v)
    (hSe : ∀ t ∈ Set.Icc (0 : ℝ) T,
      S t (e t) = lambda t • e t)
    (hxiUnit : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖xi t‖ = 1)
    (heUnit : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖e t‖ = 1)
    (hEsmall : ∀ t ∈ Set.Icc (0 : ℝ) T,
      alignmentEnergy (xi t) (e t) ≤ 1 / 2)
    (hgap : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ gap t)
    (hcoercive : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gap t * alignmentEnergy (xi t) (e t) ≤
        lambda t - inner ℝ (xi t) (S t (xi t)))
    (hrate : IntervalIntegrable
      (deriv (fun t ↦ alignmentEnergy (xi t) (e t))) volume 0 T)
    (hweighted : IntervalIntegrable
      (fun t ↦ gap t * alignmentEnergy (xi t) (e t)) volume 0 T)
    (hforcing : IntervalIntegrable
      (fun t ↦ 2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|)
      volume 0 T) :
    (∫ t in (0 : ℝ)..T,
      gap t * alignmentEnergy (xi t) (e t)) ≤
      alignmentEnergy (xi 0) (e 0) +
        ∫ t in (0 : ℝ)..T,
          2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)| := by
  let energy : ℝ → ℝ := fun t ↦ alignmentEnergy (xi t) (e t)
  let rate : ℝ → ℝ := deriv energy
  let weighted : ℝ → ℝ := fun t ↦ gap t * energy t
  let forcing : ℝ → ℝ := fun t ↦
    2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|
  have hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      DifferentiableAt ℝ energy t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := by
      rwa [Set.uIcc_of_le hT] at ht
    exact (hasDerivAt_alignmentEnergy (hxi t htIcc) (he t htIcc)).differentiableAt
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) T,
      rate t ≤ -weighted t + forcing t := by
    intro t ht
    have hexact := hasDerivAt_alignmentEnergy_of_directionEquation
      (S t) (hxi t ht) (he t ht) (heta t ht)
        (hSsymm t ht) (hSe t ht)
    have hrateEq : rate t =
        -2 * inner ℝ (xi t) (e t) *
          ((lambda t - inner ℝ (xi t) (S t (xi t))) *
              inner ℝ (xi t) (e t) +
            inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)) := by
      exact hexact.deriv
    rw [hrateEq]
    have hbound := alignmentRate_le_of_gapCoercivity
      (S t) (xi t) (e t) (d t) (theta t) (lambda t) (gap t)
        (hxiUnit t ht) (heUnit t ht) (hEsmall t ht)
        (hgap t ht) (hcoercive t ht)
    change _ ≤ -(gap t * alignmentEnergy (xi t) (e t)) +
      2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|
    convert hbound using 1 <;> ring
  have hfundamental : (∫ t in (0 : ℝ)..T, rate t) =
      energy T - energy 0 :=
    intervalIntegral.integral_deriv_eq_sub hdiff hrate
  have hterminal : 0 ≤ energy T := by
    apply alignmentEnergy_nonneg
    · exact hxiUnit T ⟨hT, le_rfl⟩
    · exact heUnit T ⟨hT, le_rfl⟩
  exact weightedResidence_le_initial_add_forcing hT
    energy rate weighted forcing hrate hweighted hforcing hpoint
      hfundamental hterminal

end PancakeAlignmentDynamics
end NavierStokes
end FluidDynamics
end Mettapedia

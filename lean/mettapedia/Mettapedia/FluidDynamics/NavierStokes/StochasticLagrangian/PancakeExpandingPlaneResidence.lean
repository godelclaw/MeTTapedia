import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralClusterDichotomy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Collision-safe residence in the expanding strain plane

When the two largest strain eigenvalues collide, a distinguished expanding
eigenline can rotate arbitrarily, but the plane orthogonal to a separated
bottom eigenline remains stable.  This module develops the corresponding
dynamic estimate.

The sign-invariant energy

`C(xi,e) = <xi,e>^2`

measures escape of the vorticity direction `xi` from the expanding plane into
the contracting line `e`.  Along the direction equation its strain part is
damped by the Rayleigh excess above the bottom eigenvalue.  The bottom
spectral gap makes that excess coercive while `C <= 1/2`, giving a weighted
residence inequality whose only forcing channels are the non-strain direction
forcing and motion of the contracting line.

This is the cluster-safe counterpart of the top-eigenline estimate in
`PancakeAlignmentDynamics`.  It does not yet estimate the pressure-Hessian
forcing or construct a differentiable eigenline path from a Navier--Stokes
solution; those are the remaining dynamical inputs.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeExpandingPlaneResidence

open MeasureTheory
open DirectionEvolutionTilting
open PancakeAlignmentDynamics
open PancakeEigenframePerturbation
open PancakeSpectralClusterDichotomy
open PancakeSpectralClusterDichotomy.SymmetricStrain
open PancakeSpectralProjectorRegularity
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeStrainSpectralFrame
open scoped Interval RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- Squared vorticity-direction energy in a contracting line.  The square
makes the quantity independent of the sign chosen for the eigenvector. -/
def contractingLineEnergy (xi e : R3) : ℝ :=
  (inner ℝ xi e) ^ 2

theorem contractingLineEnergy_nonneg (xi e : R3) :
    0 ≤ contractingLineEnergy xi e := by
  exact sq_nonneg _

/-- The contracting-line energy is the quadratic form of the corresponding
rank-one projector. -/
theorem contractingLineEnergy_eq_inner_lineProjector (xi e : R3) :
    contractingLineEnergy xi e = inner ℝ xi (lineProjector e xi) := by
  unfold contractingLineEnergy lineProjector
  simp only [InnerProductSpace.rankOne_apply, real_inner_smul_right]
  rw [real_inner_comm e xi]
  ring

/-- For a unit direction, contracting-line energy is exactly the energy
missing from the complementary plane projector. -/
theorem contractingLineEnergy_eq_planeEscape
    (xi e : R3) (hxi : ‖xi‖ = 1) :
    contractingLineEnergy xi e =
      1 - inner ℝ xi ((ContinuousLinearMap.id ℝ R3 - lineProjector e) xi) := by
  rw [contractingLineEnergy_eq_inner_lineProjector]
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right]
  rw [real_inner_self_eq_norm_sq, hxi]
  norm_num

/-- In the constructed ordered frame, the preceding plane is precisely the
stable expanding-plane projector used on the bottom-gap-separated branch. -/
theorem contractingLineEnergy_eq_expandingPlaneEscape
    (S : SymmetricStrain) (xi : R3) (hxi : ‖xi‖ = 1) :
    contractingLineEnergy xi
        ((orderedEigenframe S.1 S.2).eigenbasis 2) =
      1 - inner ℝ xi (expandingPlaneProjector S xi) := by
  exact contractingLineEnergy_eq_planeEscape xi
    ((orderedEigenframe S.1 S.2).eigenbasis 2) hxi

/-! ## Exact differential law -/

/-- Exact derivative of the sign-invariant contracting-line energy. -/
theorem hasDerivAt_contractingLineEnergy
    {xi e : ℝ → R3} {eta theta : R3} {t : ℝ}
    (hxi : HasDerivAt xi eta t) (he : HasDerivAt e theta t) :
    HasDerivAt (fun s ↦ contractingLineEnergy (xi s) (e s))
      (2 * inner ℝ (xi t) (e t) *
        (inner ℝ eta (e t) + inner ℝ (xi t) theta)) t := by
  have h := (hasDerivAt_alignmentEnergy hxi he).const_sub 1
  convert h using 1
  · rfl
  · rfl
  · funext s
    simp [contractingLineEnergy, alignmentEnergy]
  · ring

/-- Exact moving-bottom-eigenline law.  The strain contribution is negative
because the bottom eigenvalue lies below the Rayleigh quotient. -/
theorem hasDerivAt_contractingLineEnergy_of_directionEquation
    {xi e : ℝ → R3} {eta theta d : R3} {t mu : ℝ}
    (S : R3 →L[ℝ] R3)
    (hxi : HasDerivAt xi eta t) (he : HasDerivAt e theta t)
    (heta : eta = transverseComponent (xi t) (S (xi t)) + d)
    (hSsymm : ∀ (u v : R3), inner ℝ u (S v) = inner ℝ (S u) v)
    (hSe : S (e t) = mu • e t) :
    HasDerivAt (fun s ↦ contractingLineEnergy (xi s) (e s))
      (2 * inner ℝ (xi t) (e t) *
        ((mu - inner ℝ (xi t) (S (xi t))) *
            inner ℝ (xi t) (e t) +
          inner ℝ d (e t) + inner ℝ (xi t) theta)) t := by
  have hbase := hasDerivAt_contractingLineEnergy hxi he
  convert hbase using 1
  rw [heta, inner_add_left,
    inner_transverseComponent_strain_eigenvector S (xi t) (e t)
      mu hSsymm hSe]

/-! ## Bottom-gap coercivity -/

/-- Spectral-coordinate identity for the excess of a Rayleigh quotient over
the bottom eigenvalue. -/
theorem rayleighExcess_eq_weightedBottomGaps
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2) :
    rayleigh - lambda₂ =
      (lambda₀ - lambda₂) * a₀ ^ 2 +
        (lambda₁ - lambda₂) * a₁ ^ 2 := by
  rw [hrayleigh]
  linear_combination lambda₂ * hparseval

/-- A lower bound on the two gaps above the bottom eigenvalue makes the
Rayleigh excess coercive for energy in the complementary expanding plane. -/
theorem gap_mul_expandingPlaneEnergy_le_rayleighExcess
    (lambda₀ lambda₁ lambda₂ a₀ a₁ a₂ rayleigh gap : ℝ)
    (hparseval : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1)
    (hrayleigh : rayleigh =
      lambda₀ * a₀ ^ 2 + lambda₁ * a₁ ^ 2 + lambda₂ * a₂ ^ 2)
    (hgap₀ : gap ≤ lambda₀ - lambda₂)
    (hgap₁ : gap ≤ lambda₁ - lambda₂) :
    gap * (1 - a₂ ^ 2) ≤ rayleigh - lambda₂ := by
  have hplane : 1 - a₂ ^ 2 = a₀ ^ 2 + a₁ ^ 2 := by
    nlinarith [hparseval]
  rw [rayleighExcess_eq_weightedBottomGaps lambda₀ lambda₁ lambda₂
    a₀ a₁ a₂ rayleigh hparseval hrayleigh, hplane]
  calc
    gap * (a₀ ^ 2 + a₁ ^ 2) =
        gap * a₀ ^ 2 + gap * a₁ ^ 2 := by ring
    _ ≤ (lambda₀ - lambda₂) * a₀ ^ 2 +
          (lambda₁ - lambda₂) * a₁ ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_right hgap₀ (sq_nonneg a₀))
        (mul_le_mul_of_nonneg_right hgap₁ (sq_nonneg a₁))

/-- Route-facing bottom-gap coercivity in the constructed strain frame. -/
theorem bottomGap_mul_expandingPlaneEnergy_le_rayleighExcess
    (S : SymmetricStrain) (xi : R3) (hxi : ‖xi‖ = 1) :
    bottomGap S *
        (1 - contractingLineEnergy xi
          ((orderedEigenframe S.1 S.2).eigenbasis 2)) ≤
      inner ℝ xi (S.1 xi) - thirdEigenvalue S := by
  let F := orderedEigenframe S.1 S.2
  have hparse := parseval_three F.eigenbasis xi hxi
  have hray := rayleigh_three S.1 S.2 F.eigenvalue F.eigenbasis
    F.apply_eigenbasis xi
  have h10 : F.eigenvalue 1 ≤ F.eigenvalue 0 :=
    F.antitone_eigenvalue (by decide)
  change (F.eigenvalue 1 - F.eigenvalue 2) *
      (1 - (inner ℝ xi (F.eigenbasis 2)) ^ 2) ≤
    inner ℝ xi (S.1 xi) - F.eigenvalue 2
  exact gap_mul_expandingPlaneEnergy_le_rayleighExcess
    (F.eigenvalue 0) (F.eigenvalue 1) (F.eigenvalue 2)
    (inner ℝ xi (F.eigenbasis 0))
    (inner ℝ xi (F.eigenbasis 1))
    (inner ℝ xi (F.eigenbasis 2))
    (inner ℝ xi (S.1 xi))
    (F.eigenvalue 1 - F.eigenvalue 2)
    hparse hray (sub_le_sub_right h10 _) le_rfl

/-! ## Damping and integrated residence -/

/-- Scalar damping estimate for contracting-line residence. -/
theorem contractingLineRate_le_damping_add_forcing
    (a excess E gap force : ℝ)
    (hEdef : E = a ^ 2) (hE : 0 ≤ E) (hEsmall : E ≤ 1 / 2)
    (hgap : 0 ≤ gap)
    (hcoercive : gap * (1 - E) ≤ excess)
    (ha : |a| ≤ 1) :
    2 * a * ((-excess) * a + force) ≤
      -gap * E + 2 * |force| := by
  have hhalf : (1 / 2 : ℝ) ≤ 1 - E := by linarith
  have hgapHalf : gap * (1 / 2 : ℝ) ≤ gap * (1 - E) :=
    mul_le_mul_of_nonneg_left hhalf hgap
  have hexcess : 0 ≤ excess := by
    have : 0 ≤ gap * (1 - E) := by positivity
    exact this.trans hcoercive
  have hgapExcess : gap ≤ 2 * excess := by
    linarith [hgapHalf.trans hcoercive]
  have hdamping : gap * E ≤ 2 * E * excess := by
    exact (mul_le_mul_of_nonneg_right hgapExcess hE).trans_eq (by ring)
  have hforce : 2 * a * force ≤ 2 * |force| := by
    calc
      2 * a * force ≤ |2 * a * force| := le_abs_self _
      _ = 2 * |a| * |force| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 2 * 1 * |force| := by gcongr
      _ = 2 * |force| := by ring
  rw [hEdef] at hdamping
  nlinarith

/-- Vector form of the bottom-gap damping estimate. -/
theorem contractingLineRate_le_of_bottomGapCoercivity
    (S : R3 →L[ℝ] R3) (xi e d theta : R3)
    (mu gap : ℝ)
    (hxi : ‖xi‖ = 1) (he : ‖e‖ = 1)
    (hEsmall : contractingLineEnergy xi e ≤ 1 / 2)
    (hgap : 0 ≤ gap)
    (hcoercive : gap * (1 - contractingLineEnergy xi e) ≤
      inner ℝ xi (S xi) - mu) :
    2 * inner ℝ xi e *
        ((mu - inner ℝ xi (S xi)) * inner ℝ xi e +
          inner ℝ d e + inner ℝ xi theta) ≤
      -gap * contractingLineEnergy xi e +
        2 * |inner ℝ d e + inner ℝ xi theta| := by
  have ha : |inner ℝ xi e| ≤ 1 := by
    calc
      |inner ℝ xi e| ≤ ‖xi‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hxi, he, one_mul]
  have h := contractingLineRate_le_damping_add_forcing
    (inner ℝ xi e) (inner ℝ xi (S xi) - mu)
    (contractingLineEnergy xi e) gap
    (inner ℝ d e + inner ℝ xi theta)
    rfl (contractingLineEnergy_nonneg xi e) hEsmall hgap hcoercive ha
  convert h using 1 <;> ring

/-- On a bottom-gap-coercive interval, the vorticity direction has bounded
weighted residence in the contracting line.  The right side exposes exactly
the non-strain direction forcing and contracting-line motion. -/
theorem bottomGapWeightedContractingResidence_le
    {T : ℝ} (hT : 0 ≤ T)
    (S : ℝ → R3 →L[ℝ] R3)
    (xi e eta theta d : ℝ → R3) (mu gap : ℝ → ℝ)
    (hxi : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt xi (eta t) t)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt e (theta t) t)
    (heta : ∀ t ∈ Set.Icc (0 : ℝ) T,
      eta t = transverseComponent (xi t) (S t (xi t)) + d t)
    (hSsymm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ u v : R3,
      inner ℝ u (S t v) = inner ℝ (S t u) v)
    (hSe : ∀ t ∈ Set.Icc (0 : ℝ) T,
      S t (e t) = mu t • e t)
    (hxiUnit : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖xi t‖ = 1)
    (heUnit : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖e t‖ = 1)
    (hEsmall : ∀ t ∈ Set.Icc (0 : ℝ) T,
      contractingLineEnergy (xi t) (e t) ≤ 1 / 2)
    (hgap : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ gap t)
    (hcoercive : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gap t * (1 - contractingLineEnergy (xi t) (e t)) ≤
        inner ℝ (xi t) (S t (xi t)) - mu t)
    (hrate : IntervalIntegrable
      (deriv (fun t ↦ contractingLineEnergy (xi t) (e t))) volume 0 T)
    (hweighted : IntervalIntegrable
      (fun t ↦ gap t * contractingLineEnergy (xi t) (e t)) volume 0 T)
    (hforcing : IntervalIntegrable
      (fun t ↦ 2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|)
      volume 0 T) :
    (∫ t in (0 : ℝ)..T,
      gap t * contractingLineEnergy (xi t) (e t)) ≤
      contractingLineEnergy (xi 0) (e 0) +
        ∫ t in (0 : ℝ)..T,
          2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)| := by
  let energy : ℝ → ℝ := fun t ↦ contractingLineEnergy (xi t) (e t)
  let rate : ℝ → ℝ := deriv energy
  let weighted : ℝ → ℝ := fun t ↦ gap t * energy t
  let forcing : ℝ → ℝ := fun t ↦
    2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|
  have hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      DifferentiableAt ℝ energy t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := by
      rwa [Set.uIcc_of_le hT] at ht
    exact (hasDerivAt_contractingLineEnergy
      (hxi t htIcc) (he t htIcc)).differentiableAt
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) T,
      rate t ≤ -weighted t + forcing t := by
    intro t ht
    have hexact := hasDerivAt_contractingLineEnergy_of_directionEquation
      (S t) (hxi t ht) (he t ht) (heta t ht)
        (hSsymm t ht) (hSe t ht)
    have hrateEq : rate t =
        2 * inner ℝ (xi t) (e t) *
          ((mu t - inner ℝ (xi t) (S t (xi t))) *
              inner ℝ (xi t) (e t) +
            inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)) :=
      hexact.deriv
    rw [hrateEq]
    have hbound := contractingLineRate_le_of_bottomGapCoercivity
      (S t) (xi t) (e t) (d t) (theta t) (mu t) (gap t)
      (hxiUnit t ht) (heUnit t ht) (hEsmall t ht)
      (hgap t ht) (hcoercive t ht)
    change _ ≤ -(gap t * contractingLineEnergy (xi t) (e t)) +
      2 * |inner ℝ (d t) (e t) + inner ℝ (xi t) (theta t)|
    convert hbound using 1 <;> ring
  have hfundamental : (∫ t in (0 : ℝ)..T, rate t) =
      energy T - energy 0 :=
    intervalIntegral.integral_deriv_eq_sub hdiff hrate
  have hterminal : 0 ≤ energy T :=
    contractingLineEnergy_nonneg (xi T) (e T)
  exact weightedResidence_le_initial_add_forcing hT
    energy rate weighted forcing hrate hweighted hforcing hpoint
      hfundamental hterminal

end PancakeExpandingPlaneResidence
end NavierStokes
end FluidDynamics
end Mettapedia

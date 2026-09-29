import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainCycleReserve

/-!
# Compatible spatial jets and a pressure-coupled diffusion correction

The local velocity jet is `(-2y+z, 2x-my², x+2myz)`.
Its divergence vanishes identically. Its strain and curl give the five
moment polynomials below. Their sixth-order resource has zero spatial
first derivative at the origin and a negative quadratic trace.

The exact periodic realization and its complete unforced NS tangent are
derived analytically and checked in `labs/strain_cycle_diffusion.py`.
This file certifies the polynomial expansion and the resulting rate
comparisons, not that PDE realization or a positive-time invariant.

Reweighting the instantaneous pressure-strain expression by `|ω|²`
cancels a quartic diffusion cost for this family. A rotated packet has
negative corrected reserve, so arbitrary-flow positivity and the signed
history budget remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainCycleDiffusion

open StrainCycleReserve

/-- Here `W=|ω|²`, `V=ω·Sω` and `N=ω·Pω`. The physical derivative
identities are used only where `W>0`. -/
def quartic (W V N : ℝ) : ℝ := 5 * V ^ 2 / W + (63/95) * W ^ 2 - 2 * N

def corePressurePair (Q W Z : ℝ) : ℝ :=
  -(2/7) * Z - (5/21) * Q * W + W ^ 2 / 10

theorem quartic_eq_core (Q W V Z N : ℝ) :
    quartic W V N = 5 * V ^ 2 / W + (4/7) * Z + (10/21) * Q * W +
      (44/95) * W ^ 2 - 2 * (N - corePressurePair Q W Z) := by
  unfold quartic corePressurePair
  ring

/-- The positive core controls vorticity when the directional pressure
defect is nonpositive. This hypothesis is not asserted for arbitrary NS. -/
theorem quartic_coercive_of_pressure_le (Q W V Z N : ℝ)
    (hQ : 0 ≤ Q) (hW : 0 ≤ W) (hZ : 0 ≤ Z)
    (hN : N ≤ corePressurePair Q W Z) :
    (44/95) * W ^ 2 ≤ quartic W V N := by
  rw [quartic_eq_core Q W V Z N]
  have hd : 0 ≤ -2 * (N - corePressurePair Q W Z) := by linarith
  have hs : 0 ≤ 5 * V ^ 2 / W + (4/7) * Z + (10/21) * Q * W +
      (-2 * (N - corePressurePair Q W Z)) := add_nonneg (by positivity) hd
  calc
    _ ≤ (44/95) * W ^ 2 +
        (5 * V ^ 2 / W + (4/7) * Z + (10/21) * Q * W +
          (-2 * (N - corePressurePair Q W Z))) := le_add_of_nonneg_right hs
    _ = _ := by ring

def localJet (m y z : ℝ) : ℝ :=
  reserve (2 + 8 * m ^ 2 * y ^ 2 + 2 * m ^ 2 * z ^ 2) (6 * m * y)
    (16 + 4 * m ^ 2 * z ^ 2) (16 * m * (z + 2 * y))
    (16 + m ^ 2 * (20 * z ^ 2 + 32 * y * z + 64 * y ^ 2))

def quadraticPart (m y z : ℝ) : ℝ :=
  -(24/9025) * m ^ 2 * (103757 * y ^ 2 + 45108 * y * z - 32272 * z ^ 2)

theorem localJet_expansion (m y z : ℝ) :
    localJet m y z = 2776/95 + quadraticPart m y z +
      (48/9025) * m ^ 4 * (136040 * y ^ 4 + 95760 * y ^ 3 * z +
        74614 * y ^ 2 * z ^ 2 + 18648 * y * z ^ 3 + 10151 * z ^ 4) +
      (128/9025) * m ^ 6 * (4 * y ^ 2 + z ^ 2) * (95 * y ^ 2 + 8 * z ^ 2) ^ 2 := by
  dsimp [localJet, quadraticPart, reserve, polynomial, coefficient]
  ring

/-- Twice the two pure quadratic coefficients; there is no x dependence. -/
def quadraticTrace (m : ℝ) : ℝ :=
  2 * quadraticPart m 1 0 + 2 * quadraticPart m 0 1

theorem quadraticTrace_eq (m : ℝ) :
    quadraticTrace m = -(686256/1805) * m ^ 2 := by
  dsimp [quadraticTrace, quadraticPart]
  ring

/-- These slots are the actual parabolic rates of sigma², |ω|² and
directional pressure at the initial receiver of the periodic family. -/
def bracketRate (m ν : ℝ) : ℝ :=
  (3325/2) * (-10 * ν * m ^ 2) + (441/2) * (-8 * ν * m ^ 2) -
    665 * ((2/5) * ν * m ^ 2 * (11 - m ^ 2))

/-- Divide the pressure-strain reserve's rate by its initial |ω|^p.
The extra term is the actual vorticity-weight production. -/
def parabolicProfile (p m ν : ℝ) : ℝ :=
  bracketRate m ν - (p/4) * ν * m ^ 2 * (4193 + 532 * m ^ 2)

theorem parabolicProfile_eq (p m ν : ℝ) :
    parabolicProfile p m ν =
      ν * m ^ 2 * ((266 - 133 * p) * m ^ 2 - 21315 - (4193/4) * p) := by
  dsimp [parabolicProfile, bracketRate]
  ring

theorem original_weight_positive (ν : ℝ) (hν : 0 < ν) :
    0 < parabolicProfile (5/7) 12 ν := by
  rw [parabolicProfile_eq]
  norm_num
  positivity

theorem quadratic_weight_rate (m ν : ℝ) :
    parabolicProfile 2 m ν = -(46823/2) * ν * m ^ 2 := by
  rw [parabolicProfile_eq]
  ring

theorem weight_at_least_two_nonpos (p m ν : ℝ) (hp : 2 ≤ p) (hν : 0 ≤ ν) :
    parabolicProfile p m ν ≤ 0 := by
  rw [parabolicProfile_eq]
  have hc : 266 - 133 * p ≤ 0 := by linarith
  have hm := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg m)
  have hb : (266 - 133 * p) * m ^ 2 - 21315 - (4193/4) * p ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hν (sq_nonneg m)) hb

/-- The physical quartic expression is
`5(ω·Sω)²/|ω|² + (63/95)|ω|⁴ - 2ω·Pω`. -/
def quarticRate (m ν : ℝ) : ℝ := (32/665) * parabolicProfile 2 m ν

theorem quarticRate_eq (m ν : ℝ) :
    quarticRate m ν = -(107024/95) * ν * m ^ 2 := by
  rw [quarticRate, quadratic_weight_rate]
  ring

/-- In the stated family this correction pays the sixth-order resource's
positive initial parabolic source. This is not an all-time NS budget. -/
theorem joint_diffusion_payment (m ν : ℝ) :
    -ν * quadraticTrace m + quarticRate m ν = -(269440/361) * ν * m ^ 2 := by
  rw [quadraticTrace_eq, quarticRate_eq]
  ring

/-- Rotating only the parent packet preserves the observed strain and
vorticity but can reverse positivity through its actual pressure. -/
theorem rotated_quartic_negative : (32/95 : ℝ) * (599 - 76 * 3 ^ 2) < 0 := by
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.StrainCycleDiffusion

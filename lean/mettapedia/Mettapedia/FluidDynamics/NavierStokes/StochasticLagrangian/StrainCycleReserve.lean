import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# A sixth-order resource for transverse strain histories

For the compact-core comparison, the moments are
`Q=tr(S²)`, `R=tr(S³)`, `W=|ω|²`, `V=ω·Sω`, `Z=ω·S²ω`.
This file proves their polynomial invariant, its exact signed defect
production, and a nonnegative eigenframe representation. The analytic
matrix/PDE identification and a spectral-regime coercivity estimate are
in `labs/strain_cycle_reserve.py` and its README derivation.

The normalized turning-work lemma is a consumer of two quantitative
controls from that estimate. It charges an entire compatible history;
it does not grant a new initial resource after compression. The invariant
alone is not coercive in vorticity, and physical pressure and viscosity
can change it. No arbitrary-flow bound on those defects is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainCycleReserve

def coefficient : ℝ := 63 / 190

def polynomial (c Q R W V Z : ℝ) : ℝ :=
  Q ^ 3 - 6 * R ^ 2 - 2 * c * Q ^ 2 * W + c ^ 2 * Q * W ^ 2 +
    6 * c * Q * Z - 6 * c * R * V + c ^ 2 * V ^ 2 / 2 - 2 * c ^ 2 * W * Z

def reserve (Q R W V Z : ℝ) : ℝ := polynomial coefficient Q R W V Z

def differential (Q R W V Z dQ dR dW dV dZ : ℝ) : ℝ :=
  (3 * Q ^ 2 - 4 * coefficient * Q * W + coefficient ^ 2 * W ^ 2 +
      6 * coefficient * Z) * dQ +
    (-12 * R - 6 * coefficient * V) * dR +
    (-2 * coefficient * Q ^ 2 + 2 * coefficient ^ 2 * Q * W -
      2 * coefficient ^ 2 * Z) * dW +
    (-6 * coefficient * R + coefficient ^ 2 * V) * dV +
    (6 * coefficient * Q - 2 * coefficient ^ 2 * W) * dZ

def qRate (R V : ℝ) : ℝ := -(10/7) * R - (3/10) * V
def rRate (Q W Z : ℝ) : ℝ := -(5/14) * Q ^ 2 - (9/20) * Z + (3/20) * W * Q
def wRate (V : ℝ) : ℝ := 2 * V
def vRate (Q W Z : ℝ) : ℝ := (9/7) * Z + (5/21) * Q * W - W ^ 2 / 10
def zRate (Q R W V : ℝ) : ℝ := (16/21) * Q * V + (4/21) * R * W - W * V / 5

theorem core_production_zero (Q R W V Z : ℝ) :
    differential Q R W V Z (qRate R V) (rRate Q W Z) (wRate V)
      (vRate Q W Z) (zRate Q R W V) = 0 := by
  dsimp [differential, coefficient, qRate, rRate, wRate, vRate, zRate]
  ring

/-- Every physical moment defect remains with its sign. -/
theorem production_with_defects (Q R W V Z eQ eR eW eV eZ : ℝ) :
    differential Q R W V Z (qRate R V + eQ) (rRate Q W Z + eR) (wRate V + eW)
      (vRate Q W Z + eV) (zRate Q R W V + eZ) =
        differential Q R W V Z eQ eR eW eV eZ := by
  have h := core_production_zero Q R W V Z
  dsimp [differential] at h ⊢
  linear_combination h

theorem hasDerivAt_reserve (Q R W V Z : ℝ → ℝ) (dQ dR dW dV dZ t : ℝ)
    (hQ : HasDerivAt Q dQ t) (hR : HasDerivAt R dR t)
    (hW : HasDerivAt W dW t) (hV : HasDerivAt V dV t) (hZ : HasDerivAt Z dZ t) :
    HasDerivAt (fun s ↦ reserve (Q s) (R s) (W s) (V s) (Z s))
      (differential (Q t) (R t) (W t) (V t) (Z t) dQ dR dW dV dZ) t := by
  have hd := (((((((hQ.pow 3).sub ((hR.pow 2).const_mul 6)).sub
    (((hQ.pow 2).mul hW).const_mul (2 * coefficient))).add
    ((hQ.mul (hW.pow 2)).const_mul (coefficient ^ 2))).add
    ((hQ.mul hZ).const_mul (6 * coefficient))).sub
    ((hR.mul hV).const_mul (6 * coefficient))).add
    ((hV.pow 2).const_mul (coefficient ^ 2 / 2))).sub
    ((hW.mul hZ).const_mul (2 * coefficient ^ 2))
  convert! hd using 1
  · ext s
    simp only [reserve, polynomial, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [differential, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
    ring

/-- Vorticity is rescaled by the fixed positive coefficient in the
eigenframe identity. Its squared components are the nonnegative masses. -/
theorem scale_identity (c Q R W V Z : ℝ) :
    polynomial c Q R W V Z = polynomial 1 Q R (c * W) (c * V) (c * Z) := by
  unfold polynomial
  ring

def eigenCertificate (a b x y z : ℝ) : ℝ :=
  (a + b) ^ 2 * (2 * a * b - y) ^ 2 / 2 +
    (a + b) * (b * x + a * z) * (2 * a * b + y) + (b * x - a * z) ^ 2 / 2

theorem eigen_identity (a b x y z : ℝ) :
    polynomial 1 ((2/3) * (a ^ 2 + a * b + b ^ 2))
      ((2 * a + b) * (a - b) * (a + 2 * b) / 9) (x + y + z)
      (((2 * a + b) * x + (b - a) * y - (a + 2 * b) * z) / 3)
      (((2 * a + b) ^ 2 * x + (b - a) ^ 2 * y + (a + 2 * b) ^ 2 * z) / 9) =
        eigenCertificate a b x y z := by
  unfold polynomial eigenCertificate
  ring

theorem eigenCertificate_nonneg (a b x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ eigenCertificate a b x y z := by
  unfold eigenCertificate
  positivity

/-- The invariant alone cannot control vorticity: this whole aligned
state family has zero invariant with arbitrary amplitude. -/
theorem aligned_degeneracy (σ Ω : ℝ) :
    reserve ((3/2) * σ ^ 2) ((3/4) * σ ^ 3) (Ω ^ 2)
      (σ * Ω ^ 2) (σ ^ 2 * Ω ^ 2) = 0 := by
  dsimp [reserve, polynomial]
  ring

/-- `A` is the absolute intrinsic turning numerator `|σ|G`, and `Ω=w⁷`.
The analytic spectral-regime estimate supplies both hypotheses. A single
bound on the retained sixth-order resource pays through every episode. -/
theorem normalized_turning_numerator_le (w A J : ℝ) (hw : 0 < w)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hsmall : A ≤ w ^ 21) (hlarge : A ^ 2 ≤ 16 * J) :
    A ≤ 4 * (1 + J) * w ^ 10 := by
  have hC : 0 ≤ 4 * (1 + J) := by positivity
  by_cases hw1 : w ≤ 1
  · have hp11 : w ^ 11 ≤ 1 := pow_le_one₀ hw.le hw1
    have hp : w ^ 21 ≤ w ^ 10 := by
      calc
        w ^ 21 = w ^ 10 * w ^ 11 := by ring
        _ ≤ w ^ 10 * 1 := mul_le_mul_of_nonneg_left hp11 (by positivity)
        _ = w ^ 10 := by ring
    have hmul := mul_le_mul_of_nonneg_right (show 1 ≤ 4 * (1 + J) by linarith)
      (show 0 ≤ w ^ 10 by positivity)
    linarith
  · have hw1' : 1 ≤ w := le_of_lt (lt_of_not_ge hw1)
    have hp : 1 ≤ w ^ 10 := one_le_pow₀ hw1'
    have ha : A ≤ 4 * (1 + J) := by nlinarith [sq_nonneg J]
    have hmul := mul_le_mul_of_nonneg_left hp hC
    linarith

theorem normalized_turning_rate_le (w A J : ℝ) (hw : 0 < w)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hsmall : A ≤ w ^ 21) (hlarge : A ^ 2 ≤ 16 * J) :
    (171/7) * A / w ^ 10 ≤ (684/7) * (1 + J) := by
  have hn := normalized_turning_numerator_le w A J hw hA hJ hsmall hlarge
  apply (div_le_iff₀ (show 0 < w ^ 10 by positivity)).mpr
  nlinarith

end Mettapedia.FluidDynamics.NavierStokes.StrainCycleReserve

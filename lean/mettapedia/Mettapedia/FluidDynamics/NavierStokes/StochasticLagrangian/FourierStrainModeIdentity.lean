import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPairedStretchIdentity
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Signed strain transfer and the frequency-difference remainder

For a complex symmetric trace-free matrix `S`, transverse input and output
amplitudes split the vorticity-strain pairing into a normal-compression term,
a frequency-weighted velocity-strain term, and two terms containing the
frequency difference. A nonconstant strain couples different frequencies;
discarding those last two terms would replace it by a constant strain.

These are exact complex bilinear identities. In a Fourier energy pairing the
first amplitude is the conjugated output amplitude. No sign, time-integrated
bound, or uniform control of the frequency-weighted energy transfer follows
from the identity alone.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierStrainModeIdentity

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicComplexStretch

/-- Complex bilinear matrix pairing, before taking any real part or absolute value. -/
def strainPair (S : Matrix (Fin 3) (Fin 3) ℂ) (a b : VelocityCoefficient) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, a i * S i j * b j

theorem strainPair_comm (S : Matrix (Fin 3) (Fin 3) ℂ) (hS : S.IsSymm)
    (a b : VelocityCoefficient) : strainPair S a b = strainPair S b a := by
  unfold strainPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hS.apply i j]
  ring

/-- The matrix-weighted cross-product identity, valid before imposing trace or transverse constraints. -/
theorem cross_pair_trace (S : Matrix (Fin 3) (Fin 3) ℂ) (hS : S.IsSymm)
    (k l a b : VelocityCoefficient) :
    strainPair S (coefficientCross k a) (coefficientCross l b) =
      Matrix.trace S * (coefficientDot k l * coefficientDot a b -
        coefficientDot k b * coefficientDot a l) -
      strainPair S k l * coefficientDot a b - coefficientDot k l * strainPair S a b +
      coefficientDot k b * strainPair S a l + coefficientDot a l * strainPair S k b := by
  simp [strainPair, coefficientDot, coefficientCross, Matrix.trace, Matrix.diag,
    Fin.sum_univ_three,
    hS.apply 0 1, hS.apply 0 2, hS.apply 1 2]
  ring

/-- For transverse modes the spatial-variation terms explicitly carry `k-l`. -/
theorem cross_pair_gap (S : Matrix (Fin 3) (Fin 3) ℂ) (hS : S.IsSymm)
    (htrace : Matrix.trace S = 0) (k l a b : VelocityCoefficient)
    (hka : coefficientDot k a = 0) (hlb : coefficientDot l b = 0) :
    strainPair S (coefficientCross k a) (coefficientCross l b) =
      -(strainPair S k l * coefficientDot a b) - coefficientDot k l * strainPair S a b +
      coefficientDot (k - l) b * strainPair S l a -
      coefficientDot a (k - l) * strainPair S b k := by
  have hkb : coefficientDot (k - l) b = coefficientDot k b := by
    simp only [coefficientDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at hlb ⊢
    rw [hlb, sub_zero]
  have haq : coefficientDot a (k - l) = -coefficientDot a l := by
    have hak : coefficientDot a k = 0 := by simpa [coefficientDot, mul_comm] using hka
    simp only [coefficientDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at hak ⊢
    rw [hak, zero_sub]
  rw [cross_pair_trace S hS, htrace, zero_mul, zero_sub, hkb, haq,
    strainPair_comm S hS l a, strainPair_comm S hS b k]
  ring

/-- A constant strain has no frequency-difference remainder. -/
theorem cross_pair_same_mode (S : Matrix (Fin 3) (Fin 3) ℂ) (hS : S.IsSymm)
    (htrace : Matrix.trace S = 0) (k a b : VelocityCoefficient)
    (hka : coefficientDot k a = 0) (hkb : coefficientDot k b = 0) :
    strainPair S (coefficientCross k a) (coefficientCross k b) =
      -(strainPair S k k * coefficientDot a b) - coefficientDot k k * strainPair S a b := by
  simpa [coefficientDot] using cross_pair_gap S hS htrace k k a b hka hkb

end Mettapedia.FluidDynamics.NavierStokes.FourierStrainModeIdentity

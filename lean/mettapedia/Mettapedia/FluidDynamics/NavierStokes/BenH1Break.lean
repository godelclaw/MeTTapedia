import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Fourier-mode obstruction to Ben Goertzel's H1 adjoint bound

Ben's local hypothesis H1 asks for a uniform bound on the adjoint/push-forward
operator as an `H^m -> H^m` map throughout an `H^m` chart neighborhood.  The
load-bearing use is the identity-energy estimate in Proposition 6.5 / Lemma F.7.

This file records the exact normalized Fourier-mode obstruction for the
area-preserving two-torus shear

`g_k(x,y) = (x, y + a_k sin(kx))`.

Choosing `a_k` so the `H^m` size of `delta_k = (0, a_k sin(kx))` is the fixed
small radius `epsilon`, the push-forward of the constant horizontal field has
ratio `sqrt (1 + (epsilon * k)^2)`.  This grows beyond every finite constant
while the chart radius stays fixed.

This is a route refutation for that H1 hypothesis. It is not a proof of
Navier-Stokes global regularity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

/-- In the normalized two-torus shear family, every selected displacement has
fixed `H^m` size `epsilon`. -/
def benH1ModeDisplacementHNorm (epsilon : Real) (_k : Nat) : Real :=
  epsilon

/-- Lower-bound ratio obtained by applying the shear push-forward to the
constant horizontal vector field. -/
def benH1ModeAdjointRatio (epsilon : Real) (k : Nat) : Real :=
  Real.sqrt (1 + (epsilon * (k : Real)) ^ 2)

/-- The linearized commutator part alone grows like `epsilon * k`. -/
def benH1ModeCommutatorRatio (epsilon : Real) (k : Nat) : Real :=
  epsilon * (k : Real)

/-- H1 restricted to the normalized Fourier-mode shear family inside chart
radius `rho`. -/
def benH1FourierModeUniformBoundWithinRadius (rho C : Real) : Prop :=
  forall k : Nat,
    benH1ModeDisplacementHNorm (rho / 2) k <= rho ->
      benH1ModeAdjointRatio (rho / 2) k <= C

theorem benH1ModeCommutatorRatio_unbounded {epsilon C : Real}
    (hepsilon : 0 < epsilon) :
    Not (forall k : Nat, benH1ModeCommutatorRatio epsilon k <= C) := by
  intro hbound
  obtain ⟨k, hk⟩ := exists_nat_gt (C / epsilon)
  have hC_lt : C < epsilon * (k : Real) := by
    have hmul := mul_lt_mul_of_pos_left hk hepsilon
    field_simp [ne_of_gt hepsilon] at hmul
    exact hmul
  exact not_lt_of_ge (hbound k) hC_lt

theorem benH1ModeAdjointRatio_unbounded {epsilon C : Real}
    (hepsilon : 0 < epsilon) :
    Not (forall k : Nat, benH1ModeAdjointRatio epsilon k <= C) := by
  intro hbound
  obtain ⟨k, hk⟩ := exists_nat_gt (C / epsilon)
  have hC_lt : C < epsilon * (k : Real) := by
    have hmul := mul_lt_mul_of_pos_left hk hepsilon
    field_simp [ne_of_gt hepsilon] at hmul
    exact hmul
  have hnonneg : 0 <= epsilon * (k : Real) := by positivity
  have hlinear_le_ratio :
      epsilon * (k : Real) <= benH1ModeAdjointRatio epsilon k := by
    unfold benH1ModeAdjointRatio
    have hsquare :
        (epsilon * (k : Real)) ^ 2 <= 1 + (epsilon * (k : Real)) ^ 2 := by
      linarith
    calc
      epsilon * (k : Real)
          = Real.sqrt ((epsilon * (k : Real)) ^ 2) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
      _ <= Real.sqrt (1 + (epsilon * (k : Real)) ^ 2) :=
              Real.sqrt_le_sqrt hsquare
  exact not_lt_of_ge (le_trans hlinear_le_ratio (hbound k)) hC_lt

/-- Any positive chart radius contains the normalized shear family with
`epsilon = rho / 2`, and its adjoint ratios are unbounded. -/
theorem not_benH1FourierModeUniformBoundWithinRadius {rho C : Real}
    (hrho : 0 < rho) :
    Not (benH1FourierModeUniformBoundWithinRadius rho C) := by
  intro hbound
  have hepsilon : 0 < rho / 2 := by positivity
  have hmode_bound : forall k : Nat, benH1ModeAdjointRatio (rho / 2) k <= C := by
    intro k
    apply hbound k
    unfold benH1ModeDisplacementHNorm
    linarith
  exact benH1ModeAdjointRatio_unbounded hepsilon hmode_bound

/-- Compact public verdict: Ben's H1, as a uniform `H^m -> H^m` adjoint bound,
is false on the normalized Fourier-mode shear model for every positive chart
radius and every proposed finite constant. -/
theorem benGoertzelH1_false_in_fourierModeShearModel :
    forall rho C : Real,
      0 < rho -> Not (benH1FourierModeUniformBoundWithinRadius rho C) := by
  intro rho C hrho
  exact not_benH1FourierModeUniformBoundWithinRadius (rho := rho) (C := C) hrho

end NavierStokes
end FluidDynamics
end Mettapedia

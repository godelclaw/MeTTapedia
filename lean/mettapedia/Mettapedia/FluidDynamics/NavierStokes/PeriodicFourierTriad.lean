import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Exact periodic Navier--Stokes Fourier triads

This module begins an independent attack on the periodic three-dimensional
Navier--Stokes problem.  Its carrier is the genuine Fourier lattice `ℤ³` of
the unit three-torus, not an abstract finite-mode ODE.  Finite supports below
are exact trigonometric polynomials and exact Galerkin projections of the
Navier--Stokes convolution.

The principal definitions expose the incompressibility symbol, the Leray
projector, the ordered Fourier convolution, coefficient energy, and flux
through an arbitrary set of retained modes.  The explicit six-mode field at
the end is a real divergence-free trigonometric polynomial supported on one
closed triad and its conjugate.  It is used to test pointwise cascade-rigidity
claims before any infinite-dimensional continuation machinery is built.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PeriodicFourierTriad

open scoped BigOperators ComplexConjugate

/-- Fourier wavevectors on the three-dimensional unit torus. -/
abbrev Wavevector := Fin 3 → ℤ

/-- One complex Fourier velocity coefficient. -/
abbrev VelocityCoefficient := Fin 3 → ℂ

/-- A Fourier velocity field, before imposing support, reality, or
incompressibility. -/
abbrev FourierVelocity := Wavevector → VelocityCoefficient

/-- Bilinear dot product of an integer wavevector with a complex velocity
coefficient.  This is the Fourier symbol of divergence, without the harmless
factor `2πi` coming from the unit-torus convention. -/
def modeDot (k : Wavevector) (v : VelocityCoefficient) : ℂ :=
  ∑ i : Fin 3, (k i : ℂ) * v i

/-- Complex bilinear dot product, used by the convection tensor. -/
def coefficientDot (u v : VelocityCoefficient) : ℂ :=
  ∑ i : Fin 3, u i * v i

/-- Hermitian coefficient pairing, linear in the second entry. -/
def coefficientHermitian (u v : VelocityCoefficient) : ℂ :=
  ∑ i : Fin 3, conj (u i) * v i

/-- Squared wave number, embedded in `ℂ` for the Leray symbol. -/
def modeSquare (k : Wavevector) : ℂ :=
  ∑ i : Fin 3, (k i : ℂ) * (k i : ℂ)

/-- Integral squared wave number, used for exact shell cutoffs. -/
def modeSquareNat (k : Wavevector) : ℕ :=
  ∑ i : Fin 3, (k i).natAbs ^ 2

/-- Fourier-symbol Leray projection onto the plane perpendicular to `k`.
The zero mode is left unchanged; the mean-zero interface excludes it later. -/
def lerayMode (k : Wavevector) (v : VelocityCoefficient) : VelocityCoefficient :=
  if _hk : modeSquare k = 0 then v
  else fun i => v i - (k i : ℂ) * modeDot k v / modeSquare k

/-- The Leray symbol is transverse at every nonzero wave number. -/
theorem modeDot_lerayMode_eq_zero
    (k : Wavevector) (v : VelocityCoefficient)
    (hk : modeSquare k ≠ 0) :
    modeDot k (lerayMode k v) = 0 := by
  unfold lerayMode
  rw [dif_neg hk]
  change
    (∑ i : Fin 3,
      (k i : ℂ) *
        (v i - (k i : ℂ) * modeDot k v / modeSquare k)) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hsecond :
      (∑ i : Fin 3,
        (k i : ℂ) * ((k i : ℂ) * modeDot k v / modeSquare k)) =
        modeDot k v := by
    calc
      _ = ∑ i : Fin 3,
          ((k i : ℂ) * (k i : ℂ)) *
            (modeDot k v / modeSquare k) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin 3, (k i : ℂ) * (k i : ℂ)) *
            (modeDot k v / modeSquare k) := by
        rw [Finset.sum_mul]
      _ = modeSquare k * (modeDot k v / modeSquare k) := by
        rfl
      _ = modeDot k v := by
        field_simp
  rw [hsecond]
  simp [modeDot]

/-- One ordered convection interaction `(u_r · s) u_s`. -/
def orderedConvection
    (r s : Wavevector) (u : FourierVelocity) : VelocityCoefficient :=
  modeDot s (u r) • u s

/-- Exact finite Fourier convolution on a retained mode set.  Both orders of
each interacting pair occur, just as in the Fourier coefficient of
`(u · ∇)u`. -/
def convectionConvolution
    (support : Finset Wavevector) (u : FourierVelocity) (k : Wavevector) :
    VelocityCoefficient :=
  ∑ r ∈ support, ∑ s ∈ support,
    if r + s = k then orderedConvection r s u else 0

/-- Exact projected nonlinear Navier--Stokes coefficient
`-i P_k Σ_{r+s=k} (u_r · s)u_s`, omitting only the common positive `2π`
factor from the unit-torus derivative convention. -/
def projectedNonlinearity
    (support : Finset Wavevector) (u : FourierVelocity) (k : Wavevector) :
    VelocityCoefficient :=
  (-Complex.I) • lerayMode k (convectionConvolution support u k)

/-- Squared Euclidean norm of one complex velocity coefficient. -/
def coefficientEnergy (v : VelocityCoefficient) : ℝ :=
  ∑ i : Fin 3, Complex.normSq (v i)

/-- Parseval-side kinetic energy of a finite collection of Fourier modes. -/
def fourierEnergy
    (modes : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  ∑ k ∈ modes, coefficientEnergy (u k)

/-- The contribution of the projected convection to the derivative of the
coefficient energy on a selected set of modes. -/
def nonlinearEnergyRate
    (support selected : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ k ∈ selected,
    (coefficientHermitian (u k) (projectedNonlinearity support u k)).re

/-- Outward nonlinear flux from `selected` is minus its nonlinear energy
rate.  Positive values mean that the selected modes lose energy. -/
def outwardFlux
    (support selected : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  -nonlinearEnergyRate support selected u

/-- Low modes in a finite exact Galerkin support, cut off by squared wave
number. -/
def lowModes (support : Finset Wavevector) (cutoffSquare : ℕ) :
    Finset Wavevector :=
  support.filter fun k => modeSquareNat k ≤ cutoffSquare

/-- The quadratic viscous dissipation form on selected Fourier modes, without
the common unit-torus factor `(2π)²`. -/
def viscousQuadratic
    (selected : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ k ∈ selected, (modeSquareNat k : ℝ) * coefficientEnergy (u k)

/-! ## An exact real divergence-free six-mode triad -/

def p : Wavevector := ![(1 : ℤ), 0, 0]
def q : Wavevector := ![(0 : ℤ), 1, 0]
def k : Wavevector := ![(1 : ℤ), 1, 0]

def a : VelocityCoefficient := ![(0 : ℂ), 1, 1]
def b : VelocityCoefficient := ![(1 : ℂ), 0, 0]
def c : VelocityCoefficient := ![(0 : ℂ), 0, 1]

@[simp] private theorem int110_third :
    (![(1 : ℤ), 1, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

@[simp] private theorem intNeg110_third :
    (![(-1 : ℤ), -1, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

@[simp] private theorem int100_third :
    (![(1 : ℤ), 0, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

@[simp] private theorem intNeg100_third :
    (![(-1 : ℤ), 0, 0] : Wavevector) (2 : Fin 3) = 0 := by decide

@[simp] private theorem complex100_third :
    (![(1 : ℂ), 0, 0] : VelocityCoefficient) (2 : Fin 3) = 0 := by rfl

@[simp] private theorem complex011_third :
    (![(0 : ℂ), 1, 1] : VelocityCoefficient) (2 : Fin 3) = 1 := by rfl

@[simp] private theorem complex00NegI_third :
    (![(0 : ℂ), 0, -Complex.I] : VelocityCoefficient) (2 : Fin 3) = -Complex.I := by rfl

@[simp] private theorem complex00I_third :
    (![(0 : ℂ), 0, Complex.I] : VelocityCoefficient) (2 : Fin 3) = Complex.I := by rfl

/-- The closed triad `{±p, ±q, ±(p+q)}`. -/
def triadSupport : Finset Wavevector := {p, -p, q, -q, k, -k}

/-- Explicit real field: the low coefficients are real, while the high pair
has opposite imaginary phases. -/
def triadVelocity : FourierVelocity := fun m =>
  if m = p then a
  else if m = -p then a
  else if m = q then b
  else if m = -q then b
  else if m = k then (-Complex.I) • c
  else if m = -k then Complex.I • c
  else 0

/-- The chosen high wavevector is the sum of the two low wavevectors. -/
theorem p_add_q_eq_k : p + q = k := by
  ext i
  fin_cases i <;> rfl

/-- All six retained modes are nonzero. -/
theorem zero_not_mem_triadSupport : (0 : Wavevector) ∉ triadSupport := by
  decide

/-- Exact support of the explicit field. -/
theorem triadVelocity_eq_zero_of_not_mem
    {m : Wavevector} (hm : m ∉ triadSupport) :
    triadVelocity m = 0 := by
  simp only [triadSupport, Finset.mem_insert, Finset.mem_singleton] at hm
  push Not at hm
  rcases hm with ⟨hp, hnp, hq, hnq, hk, hnk⟩
  simp [triadVelocity, hp, hnp, hq, hnq, hk, hnk]

/-- The explicit Fourier field has the conjugate symmetry of a real-valued
trigonometric polynomial. -/
theorem triadVelocity_reality (m : Wavevector) :
    triadVelocity (-m) = fun i => conj (triadVelocity m i) := by
  classical
  by_cases hp : m = p
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, a]
  by_cases hnp : m = -p
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, a]
  by_cases hq : m = q
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, q, b]
  by_cases hnq : m = -q
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, q, b]
  by_cases hk : m = k
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, q, k, c]
  by_cases hnk : m = -k
  · subst m
    ext i
    fin_cases i <;> simp [triadVelocity, p, q, k, c]
  have hm : m ∉ triadSupport := by
    simp [triadSupport, hp, hnp, hq, hnq, hk, hnk]
  have hneg : -m ∉ triadSupport := by
    simp only [triadSupport, Finset.mem_insert, Finset.mem_singleton]
    simp only [not_or]
    constructor
    · intro h
      apply hnp
      simpa using congrArg Neg.neg h
    constructor
    · intro h
      apply hp
      simpa using congrArg Neg.neg h
    constructor
    · intro h
      apply hnq
      simpa using congrArg Neg.neg h
    constructor
    · intro h
      apply hq
      simpa using congrArg Neg.neg h
    constructor
    · intro h
      apply hnk
      simpa using congrArg Neg.neg h
    · intro h
      apply hk
      simpa using congrArg Neg.neg h
  rw [triadVelocity_eq_zero_of_not_mem hm,
    triadVelocity_eq_zero_of_not_mem hneg]
  ext i
  simp

/-- Every coefficient in the exact triad support is divergence free. -/
theorem triadVelocity_divergenceFree
    {m : Wavevector} (hm : m ∈ triadSupport) :
    modeDot m (triadVelocity m) = 0 := by
  simp only [triadSupport, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [modeDot, triadVelocity, p, q, k, a, b, c, Fin.sum_univ_succ]

/-- The squared wave numbers are `1,1,2` on the positive triad. -/
theorem triad_modeSquares :
    modeSquareNat p = 1 ∧ modeSquareNat q = 1 ∧ modeSquareNat k = 2 := by
  decide

/-- The two low inputs generate the transverse high coefficient `c` before
the common Fourier phase and Leray projection are applied. -/
theorem triad_convectionConvolution_k :
    convectionConvolution triadSupport triadVelocity k = a + b := by
  ext i
  fin_cases i <;>
    norm_num [convectionConvolution, orderedConvection, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c, Fin.sum_univ_succ] <;>
    simp

/-- The conjugate high mode has the conjugate pre-projection convolution. -/
theorem triad_convectionConvolution_neg_k :
    convectionConvolution triadSupport triadVelocity (-k) = -(a + b) := by
  ext i
  fin_cases i <;>
    norm_num [convectionConvolution, orderedConvection, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c, Fin.sum_univ_succ] <;>
    simp

/-- The projected convection increases the chosen positive high coefficient
in its own direction. -/
theorem triad_projectedNonlinearity_k :
    projectedNonlinearity triadSupport triadVelocity k = triadVelocity k := by
  rw [projectedNonlinearity, triad_convectionConvolution_k]
  ext i
  fin_cases i <;>
    norm_num [lerayMode, modeSquare, modeDot, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The same gain occurs on the conjugate high coefficient. -/
theorem triad_projectedNonlinearity_neg_k :
    projectedNonlinearity triadSupport triadVelocity (-k) = triadVelocity (-k) := by
  rw [projectedNonlinearity, triad_convectionConvolution_neg_k]
  ext i
  fin_cases i <;>
    norm_num [lerayMode, modeSquare, modeDot, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The positive `p` mode loses energy to the high pair. -/
theorem triad_projectedNonlinearity_p :
    projectedNonlinearity triadSupport triadVelocity p = -c := by
  ext i
  fin_cases i <;>
    norm_num [projectedNonlinearity, convectionConvolution,
      orderedConvection, lerayMode, modeSquare, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The conjugate `p` mode has the same real transfer coefficient. -/
theorem triad_projectedNonlinearity_neg_p :
    projectedNonlinearity triadSupport triadVelocity (-p) = -c := by
  ext i
  fin_cases i <;>
    norm_num [projectedNonlinearity, convectionConvolution,
      orderedConvection, lerayMode, modeSquare, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The `q` coefficient changes, but orthogonally to its present amplitude. -/
theorem triad_projectedNonlinearity_q :
    projectedNonlinearity triadSupport triadVelocity q = -c := by
  ext i
  fin_cases i <;>
    norm_num [projectedNonlinearity, convectionConvolution,
      orderedConvection, lerayMode, modeSquare, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The conjugate `q` coefficient has the same real transfer coefficient. -/
theorem triad_projectedNonlinearity_neg_q :
    projectedNonlinearity triadSupport triadVelocity (-q) = -c := by
  ext i
  fin_cases i <;>
    norm_num [projectedNonlinearity, convectionConvolution,
      orderedConvection, lerayMode, modeSquare, modeDot,
      triadSupport, triadVelocity, p, q, k, a, b, c,
      Fin.sum_univ_succ]

/-- The exact low shell is `{±p,±q}`. -/
theorem triad_lowModes_one :
    lowModes triadSupport 1 = {p, -p, q, -q} := by
  decide

/-- The high pair receives a strictly positive nonlinear energy rate. -/
theorem triad_high_nonlinearEnergyRate :
    nonlinearEnergyRate triadSupport {k, -k} triadVelocity = 4 := by
  have hpos :
      (coefficientHermitian (triadVelocity k)
        (projectedNonlinearity triadSupport triadVelocity k)).re = 1 := by
    rw [triad_projectedNonlinearity_k]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, c,
      Fin.sum_univ_succ]
  have hneg :
      (coefficientHermitian (triadVelocity (-k))
        (projectedNonlinearity triadSupport triadVelocity (-k))).re = 1 := by
    rw [triad_projectedNonlinearity_neg_k]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, c,
      Fin.sum_univ_succ]
  have hmem : k ∉ ({-k} : Finset Wavevector) := by
    decide
  unfold nonlinearEnergyRate
  rw [Finset.sum_insert hmem, Finset.sum_singleton, hpos, hneg]
  norm_num

/-- The four low modes lose exactly the energy gained by the high pair. -/
theorem triad_low_nonlinearEnergyRate :
    nonlinearEnergyRate triadSupport (lowModes triadSupport 1) triadVelocity = -4 := by
  have hp :
      (coefficientHermitian (triadVelocity p)
        (projectedNonlinearity triadSupport triadVelocity p)).re = -1 := by
    rw [triad_projectedNonlinearity_p]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, a, c,
      Fin.sum_univ_succ]
  have hnp :
      (coefficientHermitian (triadVelocity (-p))
        (projectedNonlinearity triadSupport triadVelocity (-p))).re = -1 := by
    rw [triad_projectedNonlinearity_neg_p]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, a, c,
      Fin.sum_univ_succ]
  have hq :
      (coefficientHermitian (triadVelocity q)
        (projectedNonlinearity triadSupport triadVelocity q)).re = 0 := by
    rw [triad_projectedNonlinearity_q]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, b, c,
      Fin.sum_univ_succ]
  have hnq :
      (coefficientHermitian (triadVelocity (-q))
        (projectedNonlinearity triadSupport triadVelocity (-q))).re = 0 := by
    rw [triad_projectedNonlinearity_neg_q]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, b, c,
      Fin.sum_univ_succ]
  have hp0 : p ∉ ({-p, q, -q} : Finset Wavevector) := by decide
  have hnp0 : -p ∉ ({q, -q} : Finset Wavevector) := by decide
  have hq0 : q ∉ ({-q} : Finset Wavevector) := by decide
  rw [triad_lowModes_one]
  unfold nonlinearEnergyRate
  rw [Finset.sum_insert hp0, Finset.sum_insert hnp0,
    Finset.sum_insert hq0, Finset.sum_singleton, hp, hnp, hq, hnq]
  norm_num

/-- Exact global nonlinear energy cancellation on the closed six-mode triad. -/
theorem triad_global_nonlinearEnergyRate :
    nonlinearEnergyRate triadSupport triadSupport triadVelocity = 0 := by
  have hp :
      (coefficientHermitian (triadVelocity p)
        (projectedNonlinearity triadSupport triadVelocity p)).re = -1 := by
    rw [triad_projectedNonlinearity_p]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, a, c,
      Fin.sum_univ_succ]
  have hnp :
      (coefficientHermitian (triadVelocity (-p))
        (projectedNonlinearity triadSupport triadVelocity (-p))).re = -1 := by
    rw [triad_projectedNonlinearity_neg_p]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, a, c,
      Fin.sum_univ_succ]
  have hq :
      (coefficientHermitian (triadVelocity q)
        (projectedNonlinearity triadSupport triadVelocity q)).re = 0 := by
    rw [triad_projectedNonlinearity_q]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, b, c,
      Fin.sum_univ_succ]
  have hnq :
      (coefficientHermitian (triadVelocity (-q))
        (projectedNonlinearity triadSupport triadVelocity (-q))).re = 0 := by
    rw [triad_projectedNonlinearity_neg_q]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, b, c,
      Fin.sum_univ_succ]
  have hk :
      (coefficientHermitian (triadVelocity k)
        (projectedNonlinearity triadSupport triadVelocity k)).re = 1 := by
    rw [triad_projectedNonlinearity_k]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, c,
      Fin.sum_univ_succ]
  have hnk :
      (coefficientHermitian (triadVelocity (-k))
        (projectedNonlinearity triadSupport triadVelocity (-k))).re = 1 := by
    rw [triad_projectedNonlinearity_neg_k]
    norm_num [coefficientHermitian, triadVelocity, p, q, k, c,
      Fin.sum_univ_succ]
  have hp0 : p ∉ ({-p, q, -q, k, -k} : Finset Wavevector) := by decide
  have hnp0 : -p ∉ ({q, -q, k, -k} : Finset Wavevector) := by decide
  have hq0 : q ∉ ({-q, k, -k} : Finset Wavevector) := by decide
  have hnq0 : -q ∉ ({k, -k} : Finset Wavevector) := by decide
  have hk0 : k ∉ ({-k} : Finset Wavevector) := by decide
  unfold nonlinearEnergyRate
  simp only [triadSupport] at hp hnp hq hnq hk hnk ⊢
  rw [Finset.sum_insert hp0, Finset.sum_insert hnp0,
    Finset.sum_insert hq0, Finset.sum_insert hnq0,
    Finset.sum_insert hk0, Finset.sum_singleton, hp, hnp, hq, hnq, hk, hnk]
  norm_num

/-- The exact outward flux through squared cutoff `1` is positive. -/
theorem triad_cutoffFlux_one :
    outwardFlux triadSupport (lowModes triadSupport 1) triadVelocity = 4 := by
  rw [outwardFlux, triad_low_nonlinearEnergyRate]
  norm_num

/-- The high pair's exact quadratic viscous form. -/
theorem triad_high_viscousQuadratic :
    viscousQuadratic {k, -k} triadVelocity = 8 := by
  norm_num [viscousQuadratic, coefficientEnergy, modeSquareNat,
    triadVelocity, p, q, k, c, Fin.sum_univ_succ]


end PeriodicFourierTriad
end NavierStokes
end FluidDynamics
end Mettapedia

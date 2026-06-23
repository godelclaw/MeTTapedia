import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureClosure
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePressureClosureBridge

/-!
# Finite-mode polynomial-pressure momentum closure criteria.

This module connects polynomial Helmholtz pressure closure to the reconstructed
finite-mode Navier-Stokes momentum equation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- Local finite-mode momentum reconstruction from the general polynomial
Helmholtz solve.  If the non-pressure defect slice is explicitly represented
by a curl-free polynomial vector field, the pressure is constructed as the
polynomial primitive `P_{G(t)}` rather than supplied as an independent pressure
ansatz. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i))
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = (fun t x => finiteModePolynomialPressureMode (G t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    ⟨finiteModeReconstructedVelocity mode a,
      (fun t x => finiteModePolynomialPressureMode (G t) x), rfl, rfl, ?_⟩
  intro t ht x
  rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x]
  unfold spatialPressureGradient
  rw [finiteModePolynomialPressureMode_gradient (G t) (hcurl t ht) x]
  have hdefx := congrFun (hdefect t ht) x
  have hsum :
      finiteModePolynomialVectorFieldEval (G t) x +
          finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
    rw [← hdefx]
    simp
  have hzero :
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            finiteModePolynomialVectorFieldEval (G t) x -
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 := by
    simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hsum
  exact sub_eq_zero.mp hzero

/-- Exact residual-level polynomial Helmholtz criterion for reconstructed
finite-mode momentum: once the represented non-pressure defect is a polynomial
vector field, existence of a time-dependent polynomial pressure making the
reconstructed momentum equation hold is equivalent to curl-freeness of that
polynomial defect on the same local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
              spatialConvection (finiteModeReconstructedVelocity mode a) t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  rw [← finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    (Ioo (-ε) ε) ν mode C a G hdefect]
  constructor
  · rintro ⟨P, hmom⟩
    refine ⟨P, ?_⟩
    intro t ht x
    have hmom' := hmom t ht x
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x] at hmom'
    have hres :
        finiteModeReconstructedAcceleration mode C a t x +
            spatialConvection (finiteModeReconstructedVelocity mode a) t x +
              spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x -
          ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 :=
      sub_eq_zero.mpr hmom'
    have hsum :
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x +
            finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
      simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hres
    exact add_eq_zero_iff_eq_neg.mp hsum
  · rintro ⟨P, hP⟩
    refine ⟨P, ?_⟩
    intro t ht x
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t (ha t ht) x]
    have hsum :
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x +
            finiteModeNonPressureMomentumDefect ν mode C a t x = 0 := by
      rw [hP t ht x]
      simp
    have hres :
        finiteModeReconstructedAcceleration mode C a t x +
            spatialConvection (finiteModeReconstructedVelocity mode a) t x +
              spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x -
          ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x = 0 := by
      simpa [finiteModeNonPressureMomentumDefect, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hsum
    exact sub_eq_zero.mp hres

/-- Residual-level polynomial pressure criterion for polynomial spatial modes:
after acceleration and convection have been computed symbolically, and after
the actual Laplacian slice is represented by `lapPoly`, local polynomial
pressure solvability is exactly curl-freeness of the resulting closing
pressure-gradient polynomial. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (lapPoly : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hLap : ∀ t x,
      spatialLaplacian
          (finiteModeReconstructedVelocity
            (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a) t x =
        finiteModePolynomialVectorFieldEval (lapPoly t) x) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a lapPoly t i) := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialDefect
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha
      (finiteModePolynomialClosingPressureGradientComponents ν modePoly C a lapPoly) ?_
  intro t _ht
  funext x
  ext j
  have hdefj := congrArg (fun v : NSSpace => v j)
    (finiteModePolynomialNonPressureDefect_eq_eval_of_laplacian
      ν modePoly C a lapPoly hLap t x)
  simp [finiteModePolynomialClosingPressureGradientComponents,
    finiteModePolynomialVectorFieldEval_apply, hdefj]

/-- Residual-level polynomial pressure criterion for polynomial spatial modes
with the Laplacian represented by the formal componentwise polynomial
Laplacian proved above. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
          timeVelocityDerivative
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
              spatialConvection
                (finiteModeReconstructedVelocity
                  (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
                t x +
                spatialPressureGradient
                  (fun s y => MvPolynomial.eval y (P s)) t x =
            ν • spatialLaplacian
              (finiteModeReconstructedVelocity
                (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a)
              t x) ↔
      ∀ t ∈ Ioo (-ε) ε, ∀ i j,
        MvPolynomial.pderiv i
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t j) =
          MvPolynomial.pderiv j
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t i) := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_iff_curlFree_of_polynomialModes_laplacian
      ν modePoly C a ε ha
      (fun s => finiteModePolynomialLaplacianComponents
        (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
      (fun s y => finiteModePolynomialReconstructedVelocity_spatialLaplacian modePoly a s y)

/-- Constructive polynomial-mode pressure closure.  For polynomial spatial
modes, if the computed closing pressure-gradient polynomial is curl-free on the
local interval, then its explicit polynomial primitive supplies a concrete
pressure field and the reconstructed velocity-pressure pair satisfies the
pointwise momentum equation. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialModes_curlFree
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (modePoly : ι → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hcurl : ∀ t ∈ Ioo (-ε) ε, ∀ i j,
      MvPolynomial.pderiv i
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t j) =
        MvPolynomial.pderiv j
          (finiteModePolynomialClosingPressureGradientComponents
            ν modePoly C a
              (fun s => finiteModePolynomialLaplacianComponents
                (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
            t i)) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) a ∧
        p = (fun t x =>
          finiteModePolynomialPressureMode
            (finiteModePolynomialClosingPressureGradientComponents
              ν modePoly C a
                (fun s => finiteModePolynomialLaplacianComponents
                  (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
              t) x) ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    finiteModeProjectedNS_local_reconstructed_velocityPolynomialPressure_momentum_of_polynomialHelmholtz
      ν (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y)
      C a ε ha
      (finiteModePolynomialClosingPressureGradientComponents
        ν modePoly C a
          (fun s => finiteModePolynomialLaplacianComponents
            (finiteModePolynomialReconstructedVelocityComponents modePoly a s)))
      hcurl ?_
  intro t _ht
  funext x
  change
    -finiteModeNonPressureMomentumDefect ν
        (fun i y => finiteModePolynomialVectorFieldEval (modePoly i) y) C a t x =
      finiteModePolynomialVectorFieldEval
        (finiteModePolynomialClosingPressureGradientComponents
          ν modePoly C a
            (fun s => finiteModePolynomialLaplacianComponents
              (finiteModePolynomialReconstructedVelocityComponents modePoly a s))
          t) x
  rw [finiteModePolynomialNonPressureDefect_eq_eval ν modePoly C a t x]
  ext j
  simp [finiteModePolynomialClosingPressureGradientComponents,
    finiteModePolynomialVectorFieldEval_apply]

end NavierStokes
end FluidDynamics
end Mettapedia

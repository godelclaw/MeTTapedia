import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressurePrimitive

/-!
# Finite-mode polynomial evaluation calculus
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

/-- The Fréchet derivative of evaluating a multivariate polynomial on
`NSSpace`, written as the coordinate sum of formal partial derivatives. -/
def finiteModePolynomialEvalFDeriv
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) : NSSpace →L[ℝ] ℝ :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).smulRight
    (MvPolynomial.eval x (MvPolynomial.pderiv j p))

/-- The gradient vector associated to polynomial evaluation. -/
def finiteModePolynomialEvalGradient
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) : NSSpace :=
  ∑ j : Fin 3,
    MvPolynomial.eval x (MvPolynomial.pderiv j p) • EuclideanSpace.single j (1 : ℝ)

@[simp]
theorem finiteModePolynomialEvalGradient_apply
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (j : Fin 3) :
    finiteModePolynomialEvalGradient p x j =
      MvPolynomial.eval x (MvPolynomial.pderiv j p) := by
  simp [finiteModePolynomialEvalGradient, Pi.single_apply]

@[simp]
theorem finiteModePolynomialEvalFDeriv_apply
    (p : MvPolynomial (Fin 3) ℝ) (x v : NSSpace) :
    finiteModePolynomialEvalFDeriv p x v =
      ∑ j : Fin 3, v j * MvPolynomial.eval x (MvPolynomial.pderiv j p) := by
  simp [finiteModePolynomialEvalFDeriv]

theorem finiteModePolynomialEvalFDeriv_C
    (a : ℝ) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (MvPolynomial.C a) x = 0 := by
  ext v
  simp [finiteModePolynomialEvalFDeriv]

theorem finiteModePolynomialEvalFDeriv_add
    (p q : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (p + q) x =
      finiteModePolynomialEvalFDeriv p x + finiteModePolynomialEvalFDeriv q x := by
  ext v
  calc
    finiteModePolynomialEvalFDeriv (p + q) x v =
        ∑ j : Fin 3,
          (v j * MvPolynomial.eval x (MvPolynomial.pderiv j p) +
            v j * MvPolynomial.eval x (MvPolynomial.pderiv j q)) := by
        simp [finiteModePolynomialEvalFDeriv, mul_add]
    _ = finiteModePolynomialEvalFDeriv p x v +
        finiteModePolynomialEvalFDeriv q x v := by
        simp [finiteModePolynomialEvalFDeriv, Finset.sum_add_distrib]

set_option maxHeartbeats 2000000 in
theorem finiteModePolynomialEvalFDeriv_mul_X
    (p : MvPolynomial (Fin 3) ℝ) (n : Fin 3) (x : NSSpace) :
    finiteModePolynomialEvalFDeriv (p * MvPolynomial.X n) x =
      (MvPolynomial.eval x p) • (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ) +
        (x n) • finiteModePolynomialEvalFDeriv p x := by
  ext v
  fin_cases n <;>
    simp [finiteModePolynomialEvalFDeriv, Fin.sum_univ_three, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm] <;>
    ring

theorem finiteModePolynomialEval_hasFDerivAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => MvPolynomial.eval y p)
      (finiteModePolynomialEvalFDeriv p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa [finiteModePolynomialEvalFDeriv_C] using
        (hasFDerivAt_const (x := x) (c := a))
  | add p q hp hq =>
      have hderiv := hp.add hq
      have hfun :
          (fun y : NSSpace => MvPolynomial.eval y (p + q)) =
            ((fun y : NSSpace => MvPolynomial.eval y p) +
              fun y : NSSpace => MvPolynomial.eval y q) := by
        funext y
        simp [MvPolynomial.eval_add]
      rw [hfun]
      simpa [finiteModePolynomialEvalFDeriv_add] using hderiv
  | mul_X p n hp =>
      have hcoord : HasFDerivAt (fun y : NSSpace => y n)
          (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ) x := by
        exact (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).hasFDerivAt
      have hderiv := hp.mul hcoord
      have hmul := finiteModePolynomialEvalFDeriv_mul_X p n x
      have hfun :
          (fun y : NSSpace => MvPolynomial.eval y (p * MvPolynomial.X n)) =
            ((fun y : NSSpace => MvPolynomial.eval y p) *
              fun y : NSSpace => y n) := by
        funext y
        simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [hfun]
      simpa [hmul] using hderiv

/-- The derivative, in the spatial base point, of the polynomial-evaluation
derivative. -/
def finiteModePolynomialEvalFDerivFDeriv
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    NSSpace →L[ℝ] (NSSpace →L[ℝ] ℝ) :=
  ∑ j : Fin 3,
    (finiteModePolynomialEvalFDeriv (MvPolynomial.pderiv j p) x).smulRight
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)

@[simp]
theorem finiteModePolynomialEvalFDerivFDeriv_apply
    (p : MvPolynomial (Fin 3) ℝ) (x w v : NSSpace) :
    finiteModePolynomialEvalFDerivFDeriv p x w v =
      ∑ j : Fin 3,
        (∑ r : Fin 3, w r *
          MvPolynomial.eval x (MvPolynomial.pderiv r (MvPolynomial.pderiv j p))) * v j := by
  simp [finiteModePolynomialEvalFDerivFDeriv, finiteModePolynomialEvalFDeriv_apply]

theorem finiteModePolynomialEvalFDeriv_hasFDerivAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => finiteModePolynomialEvalFDeriv p y)
      (finiteModePolynomialEvalFDerivFDeriv p x) x := by
  let g : NSSpace → (NSSpace →L[ℝ] ℝ) := fun y =>
    ∑ j : Fin 3, MvPolynomial.eval y (MvPolynomial.pderiv j p) •
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
  have hfg : (fun y : NSSpace => finiteModePolynomialEvalFDeriv p y) = g := by
    funext y
    ext v
    simp [g, finiteModePolynomialEvalFDeriv, ContinuousLinearMap.smulRight_apply, mul_comm]
  rw [hfg]
  let G : Fin 3 → NSSpace → (NSSpace →L[ℝ] ℝ) := fun j y =>
    MvPolynomial.eval y (MvPolynomial.pderiv j p) •
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)
  have hg : g = ∑ j : Fin 3, G j := by
    funext y
    simp [g, G]
  rw [hg]
  have hsum :
      HasFDerivAt (∑ j : Fin 3, G j)
        (∑ j : Fin 3,
          (finiteModePolynomialEvalFDeriv (MvPolynomial.pderiv j p) x).smulRight
            (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)) x := by
    exact
      (HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
        (fun j _hj =>
          (finiteModePolynomialEval_hasFDerivAt (MvPolynomial.pderiv j p) x).smul_const
            (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)))
  simpa [G, finiteModePolynomialEvalFDerivFDeriv] using hsum

theorem finiteModePolynomialEval_iteratedFDeriv_two_basis
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (i : Fin 3) :
    (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
        ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
  rw [iteratedFDeriv_two_apply]
  have hf : (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => MvPolynomial.eval z p) y) =
      fun y => finiteModePolynomialEvalFDeriv p y := by
    funext y
    exact (finiteModePolynomialEval_hasFDerivAt p y).fderiv
  change (fderiv ℝ (fun y : NSSpace =>
      fderiv ℝ (fun z : NSSpace => MvPolynomial.eval z p) y) x)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] 0)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] 1) =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p))
  rw [hf]
  rw [(finiteModePolynomialEvalFDeriv_hasFDerivAt p x).fderiv]
  simp [EuclideanSpace.basisFun_apply]

@[simp]
theorem finiteModePolynomialEval_iteratedFDeriv_two_single
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) (i : Fin 3) :
    (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] =
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
  simpa [EuclideanSpace.basisFun_apply] using
    finiteModePolynomialEval_iteratedFDeriv_two_basis p x i

/-- Formal scalar Laplacian of a polynomial in the spatial variables. -/
def finiteModePolynomialScalarLaplacian
    (p : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)

theorem finiteModePolynomialEval_laplacian
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      MvPolynomial.eval x (finiteModePolynomialScalarLaplacian p) := by
  rw [show Δ (fun y : NSSpace => MvPolynomial.eval y p) x =
      ∑ i : Fin 3,
        (iteratedFDeriv ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) x)
          ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
            (EuclideanSpace.basisFun (Fin 3) ℝ) i] by
    simpa using congrArg (fun h : NSSpace → ℝ => h x)
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (f := fun y : NSSpace => MvPolynomial.eval y p)
        (v := EuclideanSpace.basisFun (Fin 3) ℝ))]
  simp [finiteModePolynomialScalarLaplacian, EuclideanSpace.basisFun_apply]

theorem finiteModePolynomialEval_contDiff
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 2 (fun y : NSSpace => MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : NSSpace => a))
  | add p q hp hq =>
      simpa [MvPolynomial.eval_add] using hp.add hq
  | mul_X p n hp =>
      have hcoord : ContDiff ℝ 2 (fun y : NSSpace => y n) := by
        simpa using (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).contDiff
      simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hcoord

/-- Polynomial evaluation on `NSSpace` is smooth.  The existing `C^2` version
feeds the Laplacian API; this `C^∞` variant is used by global regularity
interfaces. -/
theorem finiteModePolynomialEval_contDiff_top
    (p : MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (fun y : NSSpace => MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpace => a))
  | add p q hp hq =>
      simpa [MvPolynomial.eval_add] using hp.add hq
  | mul_X p n hp =>
      have hcoord : ContDiff ℝ ∞ (fun y : NSSpace => y n) := by
        simpa using (EuclideanSpace.proj n : NSSpace →L[ℝ] ℝ).contDiff
      simpa [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hcoord

theorem finiteModePolynomialEval_hasGradientAt
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasGradientAt (fun y : NSSpace => MvPolynomial.eval y p)
      (finiteModePolynomialEvalGradient p x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (finiteModePolynomialEvalGradient p x) =
        finiteModePolynomialEvalFDeriv p x := by
    ext v
    simp [finiteModePolynomialEvalGradient, finiteModePolynomialEvalFDeriv,
      InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_left, mul_comm]
  rw [hdual]
  exact finiteModePolynomialEval_hasFDerivAt p x

theorem finiteModePolynomialEval_gradient
    (p : MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    gradient (fun y : NSSpace => MvPolynomial.eval y p) x =
      finiteModePolynomialEvalGradient p x := by
  apply HasGradientAt.gradient
  exact finiteModePolynomialEval_hasGradientAt p x

/-- Evaluate a polynomial vector field as an `NSSpace` vector. -/
def finiteModePolynomialVectorFieldEval
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : NSSpace → NSSpace :=
  fun x => ∑ j : Fin 3, MvPolynomial.eval x (G j) • EuclideanSpace.single j (1 : ℝ)

@[simp]
theorem finiteModePolynomialVectorFieldEval_apply
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) (j : Fin 3) :
    finiteModePolynomialVectorFieldEval G x j =
      MvPolynomial.eval x (G j) := by
  simp [finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The Fréchet derivative of a polynomial vector field, assembled component by
component from the scalar polynomial derivative formula. -/
def finiteModePolynomialVectorFieldFDeriv
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    NSSpace →L[ℝ] NSSpace :=
  ∑ j : Fin 3,
    (finiteModePolynomialEvalFDeriv (U j) x).smulRight
      (EuclideanSpace.single j (1 : ℝ))

@[simp]
theorem finiteModePolynomialVectorFieldFDeriv_apply
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x v : NSSpace) (j : Fin 3) :
    finiteModePolynomialVectorFieldFDeriv U x v j =
      ∑ r : Fin 3, v r * MvPolynomial.eval x (MvPolynomial.pderiv r (U j)) := by
  simp [finiteModePolynomialVectorFieldFDeriv, finiteModePolynomialEvalFDeriv_apply,
    Pi.single_apply]

/-- A polynomial vector field has the expected componentwise Fréchet
derivative. -/
theorem finiteModePolynomialVectorFieldEval_hasFDerivAt
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    HasFDerivAt (finiteModePolynomialVectorFieldEval U)
      (finiteModePolynomialVectorFieldFDeriv U x) x := by
  let G : Fin 3 → NSSpace → NSSpace := fun j y =>
    MvPolynomial.eval y (U j) • EuclideanSpace.single j (1 : ℝ)
  have hfun : finiteModePolynomialVectorFieldEval U = ∑ j : Fin 3, G j := by
    funext y
    simp [finiteModePolynomialVectorFieldEval, G]
  rw [hfun]
  have hsum :
      HasFDerivAt (∑ j : Fin 3, G j)
        (∑ j : Fin 3,
          (finiteModePolynomialEvalFDeriv (U j) x).smulRight
            (EuclideanSpace.single j (1 : ℝ))) x := by
    exact
      (HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
        (fun j _hj =>
          (finiteModePolynomialEval_hasFDerivAt (U j) x).smul_const
            (EuclideanSpace.single j (1 : ℝ))))
  simpa [G, finiteModePolynomialVectorFieldFDeriv] using hsum

theorem finiteModePolynomialVectorFieldEval_contDiff
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ 2 (finiteModePolynomialVectorFieldEval U) := by
  let G : Fin 3 → NSSpace → NSSpace := fun j y =>
    MvPolynomial.eval y (U j) • EuclideanSpace.single j (1 : ℝ)
  have hfun : finiteModePolynomialVectorFieldEval U = ∑ j : Fin 3, G j := by
    funext y
    simp [finiteModePolynomialVectorFieldEval, G]
  rw [hfun]
  exact
    (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => (finiteModePolynomialEval_contDiff (U j)).smul_const
        (EuclideanSpace.single j (1 : ℝ))))

/-- Polynomial vector fields on `NSSpace` are smooth. -/
theorem finiteModePolynomialVectorFieldEval_contDiff_top
    (U : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    ContDiff ℝ ∞ (finiteModePolynomialVectorFieldEval U) := by
  let G : Fin 3 → NSSpace → NSSpace := fun j y =>
    MvPolynomial.eval y (U j) • EuclideanSpace.single j (1 : ℝ)
  have hfun : finiteModePolynomialVectorFieldEval U = ∑ j : Fin 3, G j := by
    funext y
    simp [finiteModePolynomialVectorFieldEval, G]
  rw [hfun]
  exact
    (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => (finiteModePolynomialEval_contDiff_top (U j)).smul_const
        (EuclideanSpace.single j (1 : ℝ))))

end NavierStokes
end FluidDynamics
end Mettapedia

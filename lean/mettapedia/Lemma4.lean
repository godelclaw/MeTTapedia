import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional

open Real
open scoped InnerProductSpace

variable {n : ℕ}

-- Step 1: Define Laplacian as sum of second partials on EuclideanSpace
-- iteratedFDeriv ℝ 2 f x : (Fin n → ℝ) [×2]→L[ℝ] ℝ
-- We evaluate on basis vectors e_i, e_i and sum
noncomputable def euclideanLaplacian
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (iteratedFDeriv ℝ 2 f x)
    (Pi.basisFun ℝ (Fin n) i) (Pi.basisFun ℝ (Fin n) i)

-- Step 2: Product rule for Laplacian
-- Δ(fg)(x) = f(x) * Δg(x) + g(x) * Δf(x) + 2 * ⟪∇f(x), ∇g(x)⟫
-- Derivation: apply fderiv_mul twice, use inner_gradient_left to connect to gradient

-- Step 3: Carré du champ
noncomputable def carreDuChamp
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1/2 : ℝ) * (euclideanLaplacian (f * g) x
    - f x * euclideanLaplacian g x - g x * euclideanLaplacian f x)

-- Theorem: carre du champ = inner product of gradients
theorem carre_du_champ_euclidean
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf2 : ContDiff ℝ 2 f) (hg2 : ContDiff ℝ 2 g) :
    carreDuChamp f g = fun x => ⟪gradient f x, gradient g x⟫_ℝ := by
  sorry

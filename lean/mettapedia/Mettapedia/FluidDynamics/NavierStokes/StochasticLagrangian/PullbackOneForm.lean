import Mettapedia.FluidDynamics.NavierStokes.OneFormFrameCalculus

/-!
# Pullback of one-forms along maps, in coordinates

For a map `A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι` and a covector field
`u₀` (represented by its component vector field under the flat metric), the
pullback one-form is

`(A^* u₀)_b (x) = Σ_c (∂_b A_c) (x) · (u₀)_c (A x) = ⟪u₀ (A x), ∂_b A (x)⟫`,

i.e. `(DA)ᵀ (u₀ ∘ A)` — the transported momentum of Lagrangian fluid
mechanics.  When `A` is the back-to-labels map of a (possibly noisy) flow,
this is the momentum one-form whose Leray projection recovers the velocity.

## References

* H. Weber, *Ueber eine Transformation der hydrodynamischen Gleichungen*,
  J. Reine Angew. Math. **68** (1868), 286–292 — origin of the pullback form
  of the momentum.
* P. Constantin, *An Eulerian–Lagrangian approach to the Navier–Stokes
  equations*, Comm. Math. Phys. **216** (2001), 663–686. arXiv:math/0005116.
* P. Constantin, G. Iyer, *A stochastic Lagrangian representation of the
  three-dimensional incompressible Navier–Stokes equations*,
  Comm. Pure Appl. Math. **61** (2008), 330–345. arXiv:math/0511067.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pullback of a one-form `u₀` along a map `A`, in coordinates:
`(A^* u₀)(x) = (DA(x))ᵀ (u₀ (A x))`. -/
def pullbackOneForm (A u₀ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  ∑ b, EuclideanSpace.single b
    ⟪u₀ (A x), fderiv ℝ A x (EuclideanSpace.single b 1)⟫

/-- Componentwise evaluation of the pullback. -/
theorem pullbackOneForm_apply (A u₀ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) (b : ι) :
    pullbackOneForm A u₀ x b =
      ⟪u₀ (A x), fderiv ℝ A x (EuclideanSpace.single b 1)⟫ := by
  unfold pullbackOneForm
  simp

/-- Pullback along the identity map is the identity on one-forms. -/
theorem pullbackOneForm_id (u₀ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :
    pullbackOneForm (fun x => x) u₀ = u₀ := by
  funext x
  unfold pullbackOneForm
  have hid : fderiv ℝ (fun x : EuclideanSpace ℝ ι => x) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) := fderiv_fun_id
  rw [hid]
  ext b
  simp [EuclideanSpace.inner_single_right]

/-- The pullback of the zero one-form is zero. -/
theorem pullbackOneForm_zero (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :
    pullbackOneForm A (fun _ => 0) = fun _ => 0 := by
  funext x
  unfold pullbackOneForm
  ext b
  simp

end NavierStokes
end FluidDynamics
end Mettapedia

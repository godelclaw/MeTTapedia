import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureDefect

/-!
# Finite-mode polynomial pressure closure criteria
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

/-- The concrete scalar pressure mode associated to a curl-free polynomial
vector field. -/
def finiteModePolynomialPressureMode
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) : NSSpace → ℝ :=
  fun x => MvPolynomial.eval x (finiteModePolynomialPressurePrimitive G)

theorem finiteModePolynomialPressureMode_differentiableAt
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModePolynomialPressureMode G) x :=
  (finiteModePolynomialEval_hasFDerivAt
    (finiteModePolynomialPressurePrimitive G) x).differentiableAt

/-- General polynomial pressure reconstruction: curl-free polynomial vector
fields are actual spatial gradients of the explicit polynomial primitive. -/
theorem finiteModePolynomialPressureMode_gradient
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (x : NSSpace) :
    gradient (finiteModePolynomialPressureMode G) x =
      finiteModePolynomialVectorFieldEval G x := by
  unfold finiteModePolynomialPressureMode
  rw [finiteModePolynomialEval_gradient]
  ext j
  rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
    finiteModePolynomialPressurePrimitive_pderiv G hcurl j]

theorem finiteModePolynomialPressureMode_spatialPressureGradient
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hcurl : ∀ i j,
      MvPolynomial.pderiv i (G j) =
        MvPolynomial.pderiv j (G i))
    (t : NSTime) (x : NSSpace) :
    spatialPressureGradient (fun _ y => finiteModePolynomialPressureMode G y) t x =
      finiteModePolynomialVectorFieldEval G x := by
  unfold spatialPressureGradient
  exact finiteModePolynomialPressureMode_gradient G hcurl x

/-- A pointwise equality between the actual spatial pressure gradient of a
polynomial pressure and a polynomial vector field is equivalent to coefficient
level derivative identities. -/
theorem finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
    (p : MvPolynomial (Fin 3) ℝ)
    (G : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (t : NSTime) :
    (∀ x : NSSpace,
      spatialPressureGradient (fun _ y => MvPolynomial.eval y p) t x =
        finiteModePolynomialVectorFieldEval G x) ↔
      ∀ j, MvPolynomial.pderiv j p = G j := by
  constructor
  · intro h j
    apply MvPolynomial.funext
    intro x
    have hcomp := congrArg (fun v : NSSpace => v j) (h (WithLp.toLp 2 x))
    simpa [spatialPressureGradient, finiteModePolynomialEval_gradient,
      finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply]
      using hcomp
  · intro hp x
    unfold spatialPressureGradient
    rw [finiteModePolynomialEval_gradient]
    ext j
    rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
      hp j]

/-- Time-dependent version of
`finiteModePolynomialPressureGradient_eq_eval_iff_pderiv`. -/
theorem finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv
    (P : NSTime → MvPolynomial (Fin 3) ℝ)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∀ t x,
      spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
        finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t j, MvPolynomial.pderiv j (P t) = G t j := by
  constructor
  · intro h t
    exact (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
      (P t) (G t) t).mp (h t)
  · intro hp t
    exact (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
      (P t) (G t) t).mpr (hp t)

/-- Time-dependent polynomial pressure existence is exactly curl-freeness of
the polynomial vector field at every time slice.  This is the polynomial
Helmholtz/Poincare pressure theorem through the concrete
`spatialPressureGradient` API. -/
theorem finiteModeTimePolynomialPressureGradient_exists_iff_curlFree
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x) ↔
      ∀ t i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  constructor
  · rintro ⟨P, hP⟩ t
    have hp : ∀ t j, MvPolynomial.pderiv j (P t) = G t j :=
      (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P G).mp hP
    exact (finiteModePolynomialPressurePrimitive_exists_iff_curlFree (G t)).mp
      ⟨P t, hp t⟩
  · intro hcurl
    refine ⟨fun t => finiteModePolynomialPressurePrimitive (G t), ?_⟩
    exact (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv
      (fun t => finiteModePolynomialPressurePrimitive (G t)) G).mpr
      (fun t j => finiteModePolynomialPressurePrimitive_pderiv (G t) (hcurl t) j)

/-- If the non-pressure finite-mode defect is represented by a polynomial
vector field on a time set, then polynomial pressure closure of that defect is
equivalent to curl-freeness of the representing polynomial vector field on the
same time set. -/
theorem finiteModePolynomialPressure_closes_nonPressureDefectOn_iff_curlFree_of_polynomialDefect
    {ι : Type*} [Fintype ι]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (G : NSTime → Fin 3 → MvPolynomial (Fin 3) ℝ)
    (hdefect : ∀ t ∈ I,
      -finiteModeNonPressureMomentumDefect ν mode C a t =
        finiteModePolynomialVectorFieldEval (G t)) :
    (∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t ∈ I, ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect ν mode C a t x) ↔
      ∀ t ∈ I, ∀ i j, MvPolynomial.pderiv i (G t j) =
        MvPolynomial.pderiv j (G t i) := by
  constructor
  · rintro ⟨P, hP⟩ t ht
    have hgrad :
        ∀ x : NSSpace,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            finiteModePolynomialVectorFieldEval (G t) x := by
      intro x
      have hdefx :
          -finiteModeNonPressureMomentumDefect ν mode C a t x =
            finiteModePolynomialVectorFieldEval (G t) x := by
        simpa using congrFun (hdefect t ht) x
      rw [hP t ht x, hdefx]
    have hpderiv :
        ∀ j, MvPolynomial.pderiv j (P t) = G t j :=
      (finiteModePolynomialPressureGradient_eq_eval_iff_pderiv
        (P t) (G t) t).mp hgrad
    exact (finiteModePolynomialPressurePrimitive_exists_iff_curlFree (G t)).mp
      ⟨P t, hpderiv⟩
  · intro hcurl
    refine ⟨fun t => finiteModePolynomialPressurePrimitive (G t), ?_⟩
    intro t ht x
    have hgrad :
        spatialPressureGradient
            (fun s y => MvPolynomial.eval y
              (finiteModePolynomialPressurePrimitive (G s))) t x =
          finiteModePolynomialVectorFieldEval (G t) x := by
      unfold spatialPressureGradient
      rw [finiteModePolynomialEval_gradient]
      ext j
      rw [finiteModePolynomialEvalGradient_apply, finiteModePolynomialVectorFieldEval_apply,
        finiteModePolynomialPressurePrimitive_pderiv (G t) (hcurl t ht) j]
    have hdefx :
        -finiteModeNonPressureMomentumDefect ν mode C a t x =
          finiteModePolynomialVectorFieldEval (G t) x := by
      simpa using congrFun (hdefect t ht) x
    exact hgrad.trans hdefx.symm

end NavierStokes
end FluidDynamics
end Mettapedia

import Mettapedia.FluidDynamics.NavierStokes.GradientOneForm
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PullbackOneForm

/-!
# Momentum-transport pushdown for the stochastic-Lagrangian representation

In the stochastic-Lagrangian representation of the incompressible
Navier–Stokes equations the momentum one-form is the pullback of the initial
datum along the back-to-labels map (`μ = (DA)ᵀ(u₀∘A)`, the Weber transform),
the velocity is the divergence-free part of its expectation, and the momentum
satisfies an averaged transport equation whose viscous term is the sum of
squared Lie derivatives along a divergence-free trigonometric frame.

This file proves the *pushdown* step at model level: if a velocity `u` and a
gauge potential `W` are such that the momentum one-form `μ = u♭ + dW`
satisfies the averaged frame-transport equation

`∂_t μ + L_u μ = ν Σ_i L²_{E_i} μ`

(with `E_i` the normalized truncated coordinate frame), then `u` satisfies
the Navier–Stokes equations with the **explicit pressure**

`p = ∂_t W + ½⟪u, u⟫ + ⟪u, ∇W⟫ − ν ΔW`,

that is, `∂_t u + (u·∇)u + ∇p = νΔu` pointwise
(`navierStokes_of_transportedMomentum`).  The mechanism: the frame identity
converts the frame sum into the componentwise Laplacian
(`frameLaplacian_oneForm_normalized`); the Lie derivative of the momentum
splits as `L_u u♭ = (u·∇)u + d(½⟪u,u⟫)` and `L_u dW = d⟪u, ∇W⟫`
(`lieOneForm_self`, `lieOneForm_gradField`); every exact term is collected
into the pressure gradient.

**Scope and honesty.**  The averaged transport equation enters as a
*hypothesis field* (`TransportedMomentumData.transport`); this file does
**not** derive it from a stochastic flow — the Kunita–Itô–Wentzell transport
theory for one-forms is deliberately out of scope here.  All other steps are
proved.  The conclusion is a pointwise PDE identity for the supplied data;
no existence, uniqueness, or global regularity statement is made or implied
(3D Navier–Stokes global regularity is open).

## References

* P. Constantin, G. Iyer, *A stochastic Lagrangian representation of the
  three-dimensional incompressible Navier–Stokes equations*,
  Comm. Pure Appl. Math. **61** (2008), 330–345. arXiv:math/0511067.
* P. Constantin, *An Eulerian–Lagrangian approach to the Navier–Stokes
  equations*, Comm. Math. Phys. **216** (2001), 663–686. arXiv:math/0005116.
* H. Weber, *Ueber eine Transformation der hydrodynamischen Gleichungen*,
  J. Reine Angew. Math. **68** (1868), 286–292.
* S. Fang, D. Luo, *Constantin and Iyer's representation formula for the
  Navier–Stokes equations on manifolds*, Potential Anal. **48** (2018),
  181–206 (frame form of the viscous term). arXiv:1508.06387.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

section CotangentVocabulary

/-- A transported cotangent state: a back-to-labels map together with the
covector field it carries. -/
structure CotangentState where
  /-- The back-to-labels map `A` (inverse of the flow map). -/
  labelMap : R3 → R3
  /-- The transported covector field. -/
  covector : R3 → R3

/-- The state transports the initial momentum `u₀` when its covector is the
pullback of `u₀` along the back-to-labels map (the Weber transform). -/
def CotangentState.IsTransportOf (s : CotangentState) (u₀ : R3 → R3) : Prop :=
  s.covector = pullbackOneForm s.labelMap u₀

/-- The state at time zero: identity labels carrying the initial datum. -/
def cotangentStateAtId (u₀ : R3 → R3) : CotangentState :=
  ⟨fun x => x, u₀⟩

theorem cotangentStateAtId_isTransportOf (u₀ : R3 → R3) :
    (cotangentStateAtId u₀).IsTransportOf u₀ :=
  (pullbackOneForm_id u₀).symm

/-- Finite probability weights for the model-level expectation. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  /-- Probability weight of each sample. -/
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum_one : ∑ ω, weight ω = 1

/-- Expected covector field of a finite family of transported momenta. -/
def expectedOneForm {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)
    (μ : Ω → R3 → R3) : R3 → R3 :=
  fun x => ∑ ω, P.weight ω • μ ω x

/-- The expectation of a deterministic (constant-in-`ω`) family is the
family member itself. -/
theorem expectedOneForm_const {Ω : Type*} [Fintype Ω]
    (P : FiniteProbability Ω) (μ : R3 → R3) :
    expectedOneForm P (fun _ => μ) = μ := by
  funext x
  unfold expectedOneForm
  rw [← Finset.sum_smul, P.weight_sum_one, one_smul]

end CotangentVocabulary

section FrameSum

/-- The second-order frame sum at the normalized amplitude `1/√2`: the sum of
squared Lie derivatives of a one-form along the truncated coordinate frame
(all axes, both transverse polarizations, cosine and sine phases). -/
def normalizedFrameSecondSum (μ : R3 → R3) (x : R3) : R3 :=
  ∑ j, ∑ p ∈ Finset.univ.erase j,
    (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
        (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
      (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.cos t)
        (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x +
    lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
        (EuclideanSpace.single j 1) (EuclideanSpace.single p 1))
      (lieOneForm (profileMode (fun t => (Real.sqrt 2)⁻¹ * Real.sin t)
        (EuclideanSpace.single j 1) (EuclideanSpace.single p 1)) μ) x)

/-- The frame identity: on `C²` one-forms the normalized frame sum is the
componentwise Laplacian. -/
theorem normalizedFrameSecondSum_eq_coordLaplacian {μ : R3 → R3}
    (hμ : ContDiff ℝ 2 μ) (x : R3) :
    normalizedFrameSecondSum μ x = coordLaplacian μ x :=
  frameLaplacian_oneForm_normalized hμ x

end FrameSum

section Pushdown

/-- Model data for the averaged momentum-transport equation: a velocity `u`,
a gauge potential `W` (the momentum one-form is `μ = u♭ + dW`), their
certified time derivatives, the gradient-exchange form of `ΔdW`, and the
averaged frame-transport equation itself as a hypothesis field. -/
structure TransportedMomentumData where
  /-- Viscosity. -/
  ν : ℝ
  /-- Velocity field. -/
  u : ℝ → R3 → R3
  /-- Time derivative of the velocity. -/
  udot : ℝ → R3 → R3
  /-- Gauge potential: the momentum one-form is `u♭ + dW`. -/
  W : ℝ → R3 → ℝ
  /-- Time derivative of the gauge potential (in gradient-exchange form). -/
  Wdot : ℝ → R3 → ℝ
  /-- Laplacian of the gauge potential (in gradient-exchange form). -/
  WLap : ℝ → R3 → ℝ
  u_contDiff : ∀ t, ContDiff ℝ 2 (u t)
  W_contDiff : ∀ t, ContDiff ℝ 3 (W t)
  Wdot_diff : ∀ t, Differentiable ℝ (Wdot t)
  WLap_diff : ∀ t, Differentiable ℝ (WLap t)
  /-- `udot` is the time derivative of `u`. -/
  u_hasTimeDeriv : ∀ t x, HasDerivAt (fun s => u s x) (udot t x) t
  /-- The gauge gradient's time derivative is the gradient of `Wdot`. -/
  gradW_hasTimeDeriv : ∀ t x,
    HasDerivAt (fun s => gradField (W s) x) (gradField (Wdot t) x) t
  /-- The Laplacian of the gauge gradient is the gradient of `WLap`. -/
  gradW_laplacian_exchange : ∀ t x,
    coordLaplacian (gradField (W t)) x = gradField (WLap t) x
  /-- **The averaged frame-transport equation** for the momentum one-form
  `μ = u♭ + dW`: time derivative plus Lie transport along `u` equals `ν`
  times the frame second-order sum.  This is the Itô-averaged form of the
  stochastic transport of the pullback momentum; it enters as a hypothesis
  (no stochastic calculus is formalized here). -/
  transport : ∀ t x,
    udot t x + gradField (Wdot t) x +
      lieOneForm (u t) (fun y => u t y + gradField (W t) y) x =
    ν • normalizedFrameSecondSum (fun y => u t y + gradField (W t) y) x

namespace TransportedMomentumData

variable (D : TransportedMomentumData)

/-- The momentum one-form carried by the data. -/
def momentum (t : ℝ) : R3 → R3 := fun y => D.u t y + gradField (D.W t) y

/-- The gauge gradient is `C²`. -/
theorem gradW_contDiff (t : ℝ) : ContDiff ℝ 2 (gradField (D.W t)) :=
  contDiff_gradField (n := 2) (D.W_contDiff t)

/-- The momentum one-form is `C²`. -/
theorem momentum_contDiff (t : ℝ) : ContDiff ℝ 2 (D.momentum t) :=
  (D.u_contDiff t).add (D.gradW_contDiff t)

/-- The certified time derivative of the momentum one-form. -/
theorem momentum_time_deriv (t : ℝ) (x : R3) :
    deriv (fun s => D.momentum s x) t =
      D.udot t x + gradField (D.Wdot t) x :=
  ((D.u_hasTimeDeriv t x).add (D.gradW_hasTimeDeriv t x)).deriv

/-- **The pressure of the representation**: the exact terms of the momentum
transport, collected — gauge drift, kinetic energy, gauge advection, and the
viscous gauge term. -/
def pressure (t : ℝ) : R3 → ℝ := fun y =>
  D.Wdot t y + (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫ +
    ⟪D.u t y, gradField (D.W t) y⟫ - D.ν * D.WLap t y

/-- **Pushdown theorem**: the averaged frame-transport equation for the
momentum one-form `u♭ + dW` forces `u` to satisfy the Navier–Stokes
equations with the explicit pressure `p = ∂_tW + ½⟪u,u⟫ + ⟪u,∇W⟫ − νΔW`:

`∂_t u + (u·∇)u + ∇p = ν Δu` pointwise. -/
theorem navierStokes_of_transportedMomentum (t : ℝ) (x : R3) :
    deriv (fun s => D.u s x) t + fderiv ℝ (D.u t) x (D.u t x) +
      gradField (D.pressure t) x =
    D.ν • coordLaplacian (D.u t) x := by
  have htrans := D.transport t x
  -- Convert the frame sum into the Laplacian and split it.
  rw [normalizedFrameSecondSum_eq_coordLaplacian
    (show ContDiff ℝ 2 (fun y => D.u t y + gradField (D.W t) y) from
      D.momentum_contDiff t) x] at htrans
  have hlap : coordLaplacian (fun y => D.u t y + gradField (D.W t) y) x =
      coordLaplacian (D.u t) x + gradField (D.WLap t) x := by
    rw [coordLaplacian_add (D.u_contDiff t) (D.gradW_contDiff t),
      D.gradW_laplacian_exchange t x]
  rw [hlap] at htrans
  -- Split the Lie derivative of the momentum.
  have hu_diff : DifferentiableAt ℝ (D.u t) x :=
    ((D.u_contDiff t).differentiable (by norm_num)).differentiableAt
  have hgw_diff : DifferentiableAt ℝ (gradField (D.W t)) x :=
    ((D.gradW_contDiff t).differentiable (by norm_num)).differentiableAt
  have hW2 : ContDiff ℝ 2 (D.W t) := (D.W_contDiff t).of_le (by norm_num)
  have hlie : lieOneForm (D.u t) (fun y => D.u t y + gradField (D.W t) y) x =
      fderiv ℝ (D.u t) x (D.u t x) +
        gradField (fun y => (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x +
        gradField (fun y => ⟪D.u t y, gradField (D.W t) y⟫) x := by
    rw [lieOneForm_add_right hu_diff hgw_diff, lieOneForm_self hu_diff,
      lieOneForm_gradField hu_diff hW2]
  rw [hlie] at htrans
  -- Split the pressure gradient into its four exact pieces.
  have hkin_diff : DifferentiableAt ℝ
      (fun y => (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x := by
    exact (hu_diff.inner ℝ hu_diff).const_mul _
  have hadv_diff : DifferentiableAt ℝ
      (fun y => ⟪D.u t y, gradField (D.W t) y⟫) x :=
    hu_diff.inner ℝ hgw_diff
  have hgradp : gradField (D.pressure t) x =
      gradField (D.Wdot t) x +
        gradField (fun y => (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x +
        gradField (fun y => ⟪D.u t y, gradField (D.W t) y⟫) x -
        D.ν • gradField (D.WLap t) x := by
    unfold pressure
    have hV12 : DifferentiableAt ℝ
        (fun y => D.Wdot t y + (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x :=
      (D.Wdot_diff t x).add hkin_diff
    have hV1 : DifferentiableAt ℝ
        (fun y => D.Wdot t y + (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫ +
          ⟪D.u t y, gradField (D.W t) y⟫) x :=
      hV12.add hadv_diff
    have hV2 : DifferentiableAt ℝ (fun y => D.ν * D.WLap t y) x :=
      (D.WLap_diff t x).const_mul D.ν
    rw [gradField_sub hV1 hV2, gradField_add hV12 hadv_diff,
      gradField_add (D.Wdot_diff t x) hkin_diff,
      gradField_const_mul D.ν (D.WLap_diff t x)]
  -- Time derivative of the velocity.
  rw [(D.u_hasTimeDeriv t x).deriv, hgradp]
  -- Rearrange: the goal differs from the transport identity by module
  -- algebra in the shared atoms.
  have hdiff :
      (D.udot t x + fderiv ℝ (D.u t) x (D.u t x) +
        (gradField (D.Wdot t) x +
          gradField (fun y => (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x +
          gradField (fun y => ⟪D.u t y, gradField (D.W t) y⟫) x -
          D.ν • gradField (D.WLap t) x)) -
        D.ν • coordLaplacian (D.u t) x =
      (D.udot t x + gradField (D.Wdot t) x +
        (fderiv ℝ (D.u t) x (D.u t x) +
          gradField (fun y => (1 / 2 : ℝ) * ⟪D.u t y, D.u t y⟫) x +
          gradField (fun y => ⟪D.u t y, gradField (D.W t) y⟫) x)) -
        D.ν • (coordLaplacian (D.u t) x + gradField (D.WLap t) x) := by
    module
  exact sub_eq_zero.mp (hdiff.trans (sub_eq_zero.mpr htrans))

end TransportedMomentumData

end Pushdown

section ZeroInstance

/-- The gradient one-form of a constant potential vanishes. -/
theorem gradField_const (c : ℝ) (x : R3) :
    gradField (fun _ : R3 => c) x = 0 := by
  unfold gradField
  have h : ∀ a : Fin 3,
      (EuclideanSpace.single a
        (fderiv ℝ (fun _ : R3 => c) x (EuclideanSpace.single a 1)) :
          R3) = 0 := by
    intro a
    rw [fderiv_fun_const]
    ext b
    simp
  rw [Finset.sum_congr rfl fun a _ => h a]
  simp

/-- The Lie derivative of the zero one-form vanishes, along any field. -/
theorem lieOneForm_zero_right (E : R3 → R3) (x : R3) :
    lieOneForm E (fun _ => (0 : R3)) x = 0 := by
  unfold lieOneForm
  rw [fderiv_fun_const]
  ext b
  simp

/-- The rest state (zero velocity, zero gauge) satisfies the transported
momentum equations for every viscosity: the model layer is inhabited. -/
def TransportedMomentumData.rest (ν : ℝ) : TransportedMomentumData where
  ν := ν
  u := fun _ _ => 0
  udot := fun _ _ => 0
  W := fun _ _ => 0
  Wdot := fun _ _ => 0
  WLap := fun _ _ => 0
  u_contDiff := fun _ => contDiff_const
  W_contDiff := fun _ => contDiff_const
  Wdot_diff := fun _ => differentiable_const 0
  WLap_diff := fun _ => differentiable_const 0
  u_hasTimeDeriv := fun t x => hasDerivAt_const t 0
  gradW_hasTimeDeriv := fun t x => by
    have hfun : (fun s : ℝ => gradField (fun _ : R3 => (0 : ℝ)) x) =
        fun _ : ℝ => (0 : R3) := by
      funext s
      exact gradField_const 0 x
    rw [hfun, gradField_const]
    exact hasDerivAt_const t 0
  gradW_laplacian_exchange := fun t x => by
    have hfun : gradField (fun _ : R3 => (0 : ℝ)) = fun _ : R3 => (0 : R3) := by
      funext y
      exact gradField_const 0 y
    rw [hfun]
    simp [coordLaplacian, dirDeriv2]
  transport := fun t x => by
    have hfun : (fun y : R3 => (0 : R3) + gradField (fun _ : R3 => (0 : ℝ)) y) =
        fun _ : R3 => (0 : R3) := by
      funext y
      rw [gradField_const]
      simp
    rw [gradField_const, hfun, lieOneForm_zero_right]
    have hframe : normalizedFrameSecondSum (fun _ : R3 => (0 : R3)) x = 0 := by
      unfold normalizedFrameSecondSum
      have hinner : ∀ (E : R3 → R3),
          lieOneForm E (fun _ : R3 => (0 : R3)) = fun _ : R3 => (0 : R3) := by
        intro E
        funext y
        exact lieOneForm_zero_right E y
      have hterm : ∀ (j p : Fin 3), ∀ (φ : ℝ → ℝ),
          lieOneForm (profileMode φ (EuclideanSpace.single j 1)
              (EuclideanSpace.single p 1))
            (lieOneForm (profileMode φ (EuclideanSpace.single j 1)
              (EuclideanSpace.single p 1)) (fun _ : R3 => (0 : R3))) x = 0 := by
        intro j p φ
        rw [hinner, lieOneForm_zero_right]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p _ => ?_
      rw [hterm j p, hterm j p]
      simp
    rw [hframe]
    simp

end ZeroInstance

end NavierStokes
end FluidDynamics
end Mettapedia

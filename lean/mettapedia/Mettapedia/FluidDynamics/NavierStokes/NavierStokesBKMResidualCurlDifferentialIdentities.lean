import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# BKM residual-curl differential identities

This module decomposes the residual-curl expansion defect into the concrete
pointwise differential identities needed by the standard vorticity equation:
linearity of curl over the pressure residual, curl/time commutation,
curl/Laplacian commutation, and the incompressible curl-convection identity.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

section BKMContinuation

/-- Velocity field whose value is the time derivative of `u`. -/
def timeVelocityDerivativeField (u : NSVelocityField) : NSVelocityField :=
  fun t x => timeVelocityDerivative u t x

/-- Velocity field whose value is the spatial Laplacian of `u`. -/
def spatialLaplacianField (u : NSVelocityField) : NSVelocityField :=
  fun t x => spatialLaplacian u t x

/-- Velocity field whose value is the convection term `(u . grad)u`. -/
def spatialConvectionField (u : NSVelocityField) : NSVelocityField :=
  fun t x => spatialConvection u t x

/-- Defect in distributing curl over the linear pressure-residual expression. -/
def residualCurlLinearityDefect
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialVorticity (momentumPressureResidual ν u) t x -
    (ν • spatialVorticity (spatialLaplacianField u) t x -
      spatialVorticity (timeVelocityDerivativeField u) t x -
        spatialVorticity (spatialConvectionField u) t x)

/-- Defect in commuting curl with the time derivative. -/
def vorticityTimeCommutationDefect
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialVorticity (timeVelocityDerivativeField u) t x -
    timeVorticityDerivative u t x

/-- Defect in commuting curl with the spatial Laplacian. -/
def vorticityLaplacianCommutationDefect
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialVorticity (spatialLaplacianField u) t x -
    vorticityDiffusionTerm u t x

/-- Defect in the incompressible curl-convection identity
`curl((u . grad)u) = (u . grad)omega - (omega . grad)u`. -/
def vorticityConvectionExpansionDefect
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : NSSpace :=
  spatialVorticity (spatialConvectionField u) t x -
    (vorticityTransportTerm u t x - vorticityStretchingTerm u t x)

/-- Pointwise spatial differentiability needed to distribute curl over the
linear pressure-residual expression. -/
def residualCurlLinearityDifferentiableAt
    (u : NSVelocityField) (t : NSTime) (x : NSSpace) : Prop :=
  DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x ∧
    DifferentiableAt ℝ (fun y : NSSpace => timeVelocityDerivativeField u t y) x ∧
      DifferentiableAt ℝ (fun y : NSSpace => spatialConvectionField u t y) x

/-- Smooth velocities give spatial differentiability of the time-derivative
field. -/
theorem timeVelocityDerivativeField_differentiableAt_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => timeVelocityDerivativeField u t y) x := by
  have hswapMap : ContDiff ℝ ∞ (fun p : NSSpace × NSTime => (p.2, p.1)) := by
    fun_prop
  have hswap :
      ContDiff ℝ ∞
        (Function.uncurry (fun y : NSSpace => fun s : NSTime => u s y)) := by
    exact contDiff_congr_global (hu.comp hswapMap)
      (by intro p; cases p; rfl)
  have hfield :
      ContDiff ℝ ∞
        (fun y : NSSpace => fderiv ℝ (fun s : NSTime => u s y) t (1 : ℝ)) := by
    simpa using
      (hswap.fderiv_apply (g := fun _ : NSSpace => t)
        (k := fun _ : NSSpace => (1 : ℝ)) contDiff_const contDiff_const
          (by simp))
  simpa [timeVelocityDerivativeField, timeVelocityDerivative, timeFDeriv] using
    hfield.differentiable (by simp) x

/-- Smooth velocities give spatial differentiability of the convection field. -/
theorem spatialConvectionField_differentiableAt_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => spatialConvectionField u t y) x := by
  have hslice : ContDiff ℝ ∞ (fun y : NSSpace => u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have hf :
      ContDiff ℝ ∞
        (Function.uncurry (fun _y : NSSpace => fun z : NSSpace => u t z)) := by
    exact contDiff_congr_global (hslice.comp contDiff_snd)
      (by intro p; cases p; rfl)
  have hfield :
      ContDiff ℝ ∞
        (fun y : NSSpace => fderiv ℝ (fun z : NSSpace => u t z) y (u t y)) := by
    simpa using
      (hf.fderiv_apply (g := fun y : NSSpace => y)
        (k := fun y : NSSpace => u t y) contDiff_id hslice (by simp))
  simpa [spatialConvectionField, spatialConvection, spatialFDeriv] using
    hfield.differentiable (by simp) x

/-- Product-rule expansion for a coordinate derivative of the convection field
`(u . grad)u`.  This is the calculus component of the curl-convection identity;
the remaining step is the finite-dimensional Jacobian algebra plus
incompressibility. -/
theorem spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (spatialConvectionField u) t x coord comp =
      (spatialFDeriv u t x
        (spatialFDeriv u t x (EuclideanSpace.single coord (1 : ℝ)))) comp +
        ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x
          (EuclideanSpace.single coord (1 : ℝ))) (u t x)) comp := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  have hslice : ContDiff ℝ ∞ (fun y : NSSpace => u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have huAt : DifferentiableAt ℝ (fun y : NSSpace => u t y) x :=
    hslice.differentiable (by simp) x
  have hgradAt : DifferentiableAt ℝ (fun y : NSSpace => spatialFDeriv u t y) x := by
    exact (hslice.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change (fderiv ℝ
      (fun y : NSSpace => spatialFDeriv u t y (u t y)) x e) comp =
    (spatialFDeriv u t x (spatialFDeriv u t x e)) comp +
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x e) (u t x)) comp
  rw [fderiv_clm_apply hgradAt huAt]
  simp [e, spatialFDeriv]

/-- Smooth velocities give spatial differentiability of the Laplacian field. -/
theorem spatialLaplacianField_differentiableAt_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x := by
  have hslice : ContDiff ℝ ∞ (fun y : NSSpace => u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have hiter :
      Differentiable ℝ
        (fun y : NSSpace => iteratedFDeriv ℝ 2 (fun z : NSSpace => u t z) y) := by
    exact hslice.differentiable_iteratedFDeriv (m := 2) (by
      exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top 2))
  have hterm : ∀ i : Fin (Module.finrank ℝ NSSpace),
      DifferentiableAt ℝ
        (fun y : NSSpace =>
          (iteratedFDeriv ℝ 2 (fun z : NSSpace => u t z) y)
            ![(stdOrthonormalBasis ℝ NSSpace) i,
              (stdOrthonormalBasis ℝ NSSpace) i]) x := by
    intro i
    fun_prop
  have hsum :
      DifferentiableAt ℝ
        (fun y : NSSpace =>
          ∑ i : Fin (Module.finrank ℝ NSSpace),
            (iteratedFDeriv ℝ 2 (fun z : NSSpace => u t z) y)
              ![(stdOrthonormalBasis ℝ NSSpace) i,
                (stdOrthonormalBasis ℝ NSSpace) i]) x := by
    exact DifferentiableAt.fun_sum (u := Finset.univ) (A := fun i y =>
      (iteratedFDeriv ℝ 2 (fun z : NSSpace => u t z) y)
        ![(stdOrthonormalBasis ℝ NSSpace) i,
          (stdOrthonormalBasis ℝ NSSpace) i]) (by
        intro i _hi
        exact hterm i)
  change DifferentiableAt ℝ (fun y : NSSpace => Δ (fun z : NSSpace => u t z) y) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  exact hsum

/-- Smooth space-time velocities have symmetric second Frechet derivatives. -/
theorem smoothSpaceTimeVelocity_isSymmSndFDerivAt
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx : NSSpacetime) :
    IsSymmSndFDerivAt ℝ (spaceTimeVelocityMap u) tx := by
  exact hu.contDiffAt.isSymmSndFDerivAt (by
    simpa using ENat.natCast_le_of_coe_top_le_withTop
      (N := (∞ : WithTop ℕ∞)) (by rfl) 2)

/-- The second derivative of a smooth space-time velocity can swap its two
directions. -/
theorem smoothSpaceTimeVelocity_fderiv_fderiv_swap
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx v w : NSSpacetime) :
    ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) v) w =
      ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx) w) v :=
  (smoothSpaceTimeVelocity_isSymmSndFDerivAt hu tx).eq v w

/-- Each spatial derivative component of a smooth space-time velocity is smooth
as a function of time. -/
theorem spatialDerivativeComponent_contDiff_time_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (x : NSSpace) (coord comp : Fin 3) :
    ContDiff ℝ ∞ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) := by
  have hfield :
      ContDiff ℝ ∞
        (fun s : NSTime =>
          fderiv ℝ (fun y : NSSpace => u s y) x
            (EuclideanSpace.single coord (1 : ℝ))) := by
    simpa [spaceTimeVelocityMap] using
      (hu.fderiv_apply (g := fun _ : NSTime => x)
        (k := fun _ : NSTime => EuclideanSpace.single coord (1 : ℝ))
        contDiff_const contDiff_const (by simp))
  have hproj : ContDiff ℝ ∞ (fun z : NSSpace => z comp) := by
    simpa using (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).contDiff
  change ContDiff ℝ ∞
    (fun s : NSTime =>
      ((fderiv ℝ (fun y : NSSpace => u s y) x)
        (EuclideanSpace.single coord (1 : ℝ))) comp)
  exact contDiff_congr_global (hproj.comp hfield) (by intro s; rfl)

/-- Each spatial derivative component of a smooth space-time velocity is
differentiable in time. -/
theorem spatialDerivativeComponent_differentiableAt_time_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    DifferentiableAt ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t :=
  (spatialDerivativeComponent_contDiff_time_of_smooth hu x coord comp).differentiable
    (by simp) t

/-- Each spatial derivative component of a smooth space-time velocity is smooth
as a function on space-time. -/
theorem spatialDerivativeComponent_contDiff_spacetime_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (coord comp : Fin 3) :
    ContDiff ℝ ∞
      (fun tx : NSSpacetime => spatialDerivativeComponent u tx.1 tx.2 coord comp) := by
  have huncurry :
      ContDiff ℝ ∞
        (Function.uncurry
          (fun tx : NSSpacetime => fun y : NSSpace => u tx.1 y)) := by
    have hmap :
        ContDiff ℝ ∞ (fun p : NSSpacetime × NSSpace => (p.1.1, p.2)) := by
      fun_prop
    exact contDiff_congr_global (hu.comp hmap) (by
      intro p
      rcases p with ⟨⟨t, x⟩, y⟩
      rfl)
  have hfield :
      ContDiff ℝ ∞
        (fun tx : NSSpacetime =>
          fderiv ℝ (fun y : NSSpace => u tx.1 y) tx.2
            (EuclideanSpace.single coord (1 : ℝ))) := by
    simpa using
      (huncurry.fderiv_apply (g := fun tx : NSSpacetime => tx.2)
        (k := fun _tx : NSSpacetime => EuclideanSpace.single coord (1 : ℝ))
          contDiff_snd contDiff_const (by simp))
  have hproj : ContDiff ℝ ∞ (fun z : NSSpace => z comp) := by
    simpa using (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).contDiff
  change ContDiff ℝ ∞
    (fun tx : NSSpacetime =>
      ((fderiv ℝ (fun y : NSSpace => u tx.1 y) tx.2)
        (EuclideanSpace.single coord (1 : ℝ))) comp)
  exact contDiff_congr_global (hproj.comp hfield) (by intro tx; rfl)

/-- The vorticity field of a smooth velocity is smooth in space-time. -/
theorem spatialVorticity_smoothSpaceTimeVelocity_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => spatialVorticity u t x) := by
  rw [smoothSpaceTimeVelocity]
  rw [← (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).comp_contDiff_iff]
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa [Function.comp_def, spaceTimeVelocityMap, spatialVorticity,
      nsCoord0, nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord1 nsCoord2).sub
          (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord2 nsCoord1)
  · simpa [Function.comp_def, spaceTimeVelocityMap, spatialVorticity,
      nsCoord0, nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord2 nsCoord0).sub
          (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord0 nsCoord2)
  · simpa [Function.comp_def, spaceTimeVelocityMap, spatialVorticity,
      nsCoord0, nsCoord1, nsCoord2] using
        (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord0 nsCoord1).sub
          (spatialDerivativeComponent_contDiff_spacetime_of_smooth hu nsCoord1 nsCoord0)

/-- The time-derivative velocity field of a smooth velocity is again smooth in
space-time. -/
theorem timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (timeVelocityDerivativeField u) := by
  have huncurry :
      ContDiff ℝ ∞
        (Function.uncurry
          (fun tx : NSSpacetime => fun s : NSTime => u s tx.2)) := by
    have hmap :
        ContDiff ℝ ∞ (fun p : NSSpacetime × NSTime => (p.2, p.1.2)) := by
      fun_prop
    exact contDiff_congr_global (hu.comp hmap) (by
      intro p
      rcases p with ⟨⟨t, x⟩, s⟩
      rfl)
  have hfield :
      ContDiff ℝ ∞
        (fun tx : NSSpacetime =>
          fderiv ℝ (fun s : NSTime => u s tx.2) tx.1 (1 : ℝ)) := by
    simpa using
      (huncurry.fderiv_apply (g := fun tx : NSSpacetime => tx.1)
        (k := fun _tx : NSSpacetime => (1 : ℝ)) contDiff_fst
          contDiff_const (by simp))
  rw [smoothSpaceTimeVelocity]
  exact contDiff_congr_global hfield (by
    intro tx
    simp [spaceTimeVelocityMap, timeVelocityDerivativeField,
      timeVelocityDerivative, timeFDeriv])

/-- The time derivative of vorticity is smooth when the velocity is smooth. -/
theorem timeVorticityDerivative_smoothSpaceTimeVelocity_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => timeVorticityDerivative u t x) := by
  have hω : smoothSpaceTimeVelocity (fun t x => spatialVorticity u t x) :=
    spatialVorticity_smoothSpaceTimeVelocity_of_smooth hu
  have htime :
      smoothSpaceTimeVelocity
        (timeVelocityDerivativeField (fun t x => spatialVorticity u t x)) :=
    timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth hω
  rw [smoothSpaceTimeVelocity] at htime ⊢
  exact contDiff_congr_global htime (by
    intro tx
    simp [spaceTimeVelocityMap, timeVelocityDerivativeField, timeVelocityDerivative,
      timeFDeriv, timeVorticityDerivative])

/-- The vorticity of the time-derivative velocity field is smooth when the
velocity is smooth. -/
theorem spatialVorticity_timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u) :
    smoothSpaceTimeVelocity (fun t x => spatialVorticity (timeVelocityDerivativeField u) t x) := by
  exact spatialVorticity_smoothSpaceTimeVelocity_of_smooth
    (timeVelocityDerivativeField_smoothSpaceTimeVelocity_of_smooth hu)

/-- The derivative of a fixed-time spacetime embedding is the spatial product
inclusion. -/
theorem fderiv_prodMk_right_const_eq_inr
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun y : NSSpace => (t, y)) x =
      ContinuousLinearMap.inr ℝ NSTime NSSpace := by
  have h : HasFDerivAt (fun y : NSSpace => (t, y))
      (ContinuousLinearMap.inr ℝ NSTime NSSpace) x := by
    simpa [ContinuousLinearMap.inr, ContinuousLinearMap.inr_apply] using
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  exact h.fderiv

/-- The derivative of a fixed-space spacetime embedding is the time product
inclusion. -/
theorem fderiv_prodMk_left_const_eq_inl
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun s : NSTime => (s, x)) t =
      ContinuousLinearMap.inl ℝ NSTime NSSpace := by
  have h : HasFDerivAt (fun s : NSTime => (s, x))
      (ContinuousLinearMap.inl ℝ NSTime NSSpace) t := by
    simpa [ContinuousLinearMap.inl, ContinuousLinearMap.inl_apply] using
      ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t))
  exact h.fderiv

/-- The spatial derivative of a fixed-time slice is the spacetime derivative
restricted along the spatial inclusion. -/
theorem spatialSlice_fderiv_eq_spaceTime_fderiv_inr_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun y : NSSpace => u t y) x =
      (fderiv ℝ (spaceTimeVelocityMap u) (t, x)).comp
        (ContinuousLinearMap.inr ℝ NSTime NSSpace) := by
  have hU : DifferentiableAt ℝ (spaceTimeVelocityMap u) (t, x) :=
    hu.differentiable (by simp) (t, x)
  have hembed : DifferentiableAt ℝ (fun y : NSSpace => (t, y)) x := by
    fun_prop
  have hcomp := fderiv_fun_comp (x := x) (g := spaceTimeVelocityMap u) hU hembed
  rw [fderiv_prodMk_right_const_eq_inr] at hcomp
  simpa [spaceTimeVelocityMap, Function.comp_def, ContinuousLinearMap.comp] using hcomp

/-- The time derivative of a fixed-space slice is the spacetime derivative
restricted along the time inclusion. -/
theorem timeSlice_fderiv_eq_spaceTime_fderiv_inl_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    fderiv ℝ (fun s : NSTime => u s x) t =
      (fderiv ℝ (spaceTimeVelocityMap u) (t, x)).comp
        (ContinuousLinearMap.inl ℝ NSTime NSSpace) := by
  have hU : DifferentiableAt ℝ (spaceTimeVelocityMap u) (t, x) :=
    hu.differentiable (by simp) (t, x)
  have hembed : DifferentiableAt ℝ (fun s : NSTime => (s, x)) t := by
    fun_prop
  have hcomp := fderiv_fun_comp (x := t) (g := spaceTimeVelocityMap u) hU hembed
  rw [fderiv_prodMk_left_const_eq_inl] at hcomp
  simpa [spaceTimeVelocityMap, Function.comp_def, ContinuousLinearMap.comp] using hcomp

/-- For a smooth spacetime velocity, differentiating the derivative applied to
a fixed direction gives the second derivative with that direction in the
second slot. -/
theorem smoothSpaceTimeVelocity_hasFDerivAt_fderiv_apply_const
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (tx v : NSSpacetime) :
    HasFDerivAt (fun p : NSSpacetime => (fderiv ℝ (spaceTimeVelocityMap u) p) v)
      ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx).flip v) tx := by
  have hFdiff : DifferentiableAt ℝ (fderiv ℝ (spaceTimeVelocityMap u)) tx :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) tx
  have hconst : HasFDerivAt (fun _p : NSSpacetime => v)
      (0 : NSSpacetime →L[ℝ] NSSpacetime) tx :=
    hasFDerivAt_const v tx
  have h := hFdiff.hasFDerivAt.clm_apply hconst
  simpa using h

/-- The time derivative of a scalar spatial derivative component is the
spacetime second derivative with the time direction first. -/
theorem spatialDerivativeComponent_time_derivative_eq_spacetime_second
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t (1 : ℝ) =
      (((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x))
          (ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime)))
        (ContinuousLinearMap.inr ℝ NSTime NSSpace
          (EuclideanSpace.single coord (1 : ℝ)))) comp := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  let vSpace : NSSpacetime := ContinuousLinearMap.inr ℝ NSTime NSSpace e
  have hfun :
      (fun s : NSTime => spatialDerivativeComponent u s x coord comp) =
        (fun s : NSTime => ((fderiv ℝ (spaceTimeVelocityMap u) (s, x)) vSpace) comp) := by
    funext s
    have hslice := spatialSlice_fderiv_eq_spaceTime_fderiv_inr_of_smooth hu s x
    simp [spatialDerivativeComponent, spatialFDeriv, e, vSpace, hslice,
      ContinuousLinearMap.comp_apply]
  rw [hfun]
  have hscalar : HasFDerivAt
      (fun p : NSSpacetime => ((fderiv ℝ (spaceTimeVelocityMap u) p) vSpace) comp)
      ((EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).comp
        ((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x)).flip vSpace))
      (t, x) := by
    exact (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp (t, x)
      (smoothSpaceTimeVelocity_hasFDerivAt_fderiv_apply_const hu (t, x) vSpace)
  have htime : HasFDerivAt (fun s : NSTime => (s, x))
      (ContinuousLinearMap.inl ℝ NSTime NSSpace) t := by
    simpa [ContinuousLinearMap.inl, ContinuousLinearMap.inl_apply] using
      ((hasFDerivAt_id t).prodMk (hasFDerivAt_const x t))
  have hcomp := hscalar.comp t htime
  change (fderiv ℝ
      (((fun p : NSSpacetime => ((fderiv ℝ (spaceTimeVelocityMap u) p) vSpace) comp) ∘
        fun s : NSTime => (s, x))) t) (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp [vSpace, e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

/-- The scalar spatial derivative component of the time-derivative velocity
field is the spacetime second derivative with the spatial direction first. -/
theorem spatialDerivativeComponent_timeVelocityDerivativeField_eq_spacetime_second
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (timeVelocityDerivativeField u) t x coord comp =
      (((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x))
          (ContinuousLinearMap.inr ℝ NSTime NSSpace
            (EuclideanSpace.single coord (1 : ℝ))))
        (ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime))) comp := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  let vTime : NSSpacetime := ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime)
  have hfun :
      (fun y : NSSpace => timeVelocityDerivativeField u t y) =
        (fun y : NSSpace => (fderiv ℝ (spaceTimeVelocityMap u) (t, y)) vTime) := by
    funext y
    have hslice := timeSlice_fderiv_eq_spaceTime_fderiv_inl_of_smooth hu t y
    simp [timeVelocityDerivativeField, timeVelocityDerivative, timeFDeriv, vTime,
      hslice, ContinuousLinearMap.comp_apply]
  rw [spatialDerivativeComponent, spatialFDeriv, hfun]
  have hvec : HasFDerivAt
      (((fun p : NSSpacetime => (fderiv ℝ (spaceTimeVelocityMap u) p) vTime) ∘
        fun y : NSSpace => (t, y)))
      (((fderiv ℝ (fderiv ℝ (spaceTimeVelocityMap u)) (t, x)).flip vTime).comp
        (ContinuousLinearMap.inr ℝ NSTime NSSpace)) x := by
    have hbase := smoothSpaceTimeVelocity_hasFDerivAt_fderiv_apply_const hu (t, x) vTime
    have hspace : HasFDerivAt (fun y : NSSpace => (t, y))
        (ContinuousLinearMap.inr ℝ NSTime NSSpace) x := by
      simpa [ContinuousLinearMap.inr, ContinuousLinearMap.inr_apply] using
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    exact hbase.comp x hspace
  change ((fderiv ℝ
      (((fun p : NSSpacetime => (fderiv ℝ (spaceTimeVelocityMap u) p) vTime) ∘
        fun y : NSSpace => (t, y))) x) e) comp = _
  rw [hvec.fderiv]
  simp [vTime, e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

/-- Smooth spacetime velocities commute the time derivative past every scalar
spatial derivative component. -/
theorem spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun s : NSTime => spatialDerivativeComponent u s x coord comp) t (1 : ℝ) =
      spatialDerivativeComponent (timeVelocityDerivativeField u) t x coord comp := by
  rw [spatialDerivativeComponent_time_derivative_eq_spacetime_second hu t x coord comp,
    spatialDerivativeComponent_timeVelocityDerivativeField_eq_spacetime_second hu t x coord comp]
  exact congrArg (fun z : NSSpace => z comp)
    (smoothSpaceTimeVelocity_fderiv_fderiv_swap hu (t, x)
      (ContinuousLinearMap.inl ℝ NSTime NSSpace (1 : NSTime))
      (ContinuousLinearMap.inr ℝ NSTime NSSpace (EuclideanSpace.single coord (1 : ℝ))))

/-- A coordinate of the vector-valued vorticity time derivative is the
derivative of the corresponding coordinate function. -/
theorem timeVorticityDerivative_component_eq_fderiv_coordinate
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (i : Fin 3) :
    (timeVorticityDerivative u t x) i =
      fderiv ℝ (fun s : NSTime => (spatialVorticity u s x) i) t (1 : ℝ) := by
  have hdiff : DifferentiableAt ℝ (fun s : NSTime => spatialVorticity u s x) t :=
    smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (spatialVorticity_smoothSpaceTimeVelocity_of_smooth hu) t x
  have hhas : HasFDerivAt (fun s : NSTime => (spatialVorticity u s x) i)
      ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).comp
        (fderiv ℝ (fun s : NSTime => spatialVorticity u s x) t)) t := by
    exact (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp
      t hdiff.hasFDerivAt
  rw [timeVorticityDerivative, hhas.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- Smooth spacetime velocities commute curl with the time derivative at each
point. -/
theorem timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    timeVorticityDerivative u t x =
      spatialVorticity (timeVelocityDerivativeField u) t x := by
  ext i
  fin_cases i
  · change (timeVorticityDerivative u t x) nsCoord0 =
      (spatialVorticity (timeVelocityDerivativeField u) t x) nsCoord0
    rw [timeVorticityDerivative_component_eq_fderiv_coordinate hu t x nsCoord0]
    have hfun :
        (fun s : NSTime => (spatialVorticity u s x) nsCoord0) =
          (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord1 nsCoord2 -
              spatialDerivativeComponent u s x nsCoord2 nsCoord1) := by
      funext s
      simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    rw [hfun]
    have h12 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord1 nsCoord2
    have h21 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord2 nsCoord1
    rw [show fderiv ℝ
        (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord1 nsCoord2 -
            spatialDerivativeComponent u s x nsCoord2 nsCoord1) t =
        fderiv ℝ (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord1 nsCoord2) t -
          fderiv ℝ (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord2 nsCoord1) t from
        fderiv_sub h12 h21]
    simp [spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField hu t x,
      spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
  · change (timeVorticityDerivative u t x) nsCoord1 =
      (spatialVorticity (timeVelocityDerivativeField u) t x) nsCoord1
    rw [timeVorticityDerivative_component_eq_fderiv_coordinate hu t x nsCoord1]
    have hfun :
        (fun s : NSTime => (spatialVorticity u s x) nsCoord1) =
          (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord2 nsCoord0 -
              spatialDerivativeComponent u s x nsCoord0 nsCoord2) := by
      funext s
      simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    rw [hfun]
    have h20 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord2 nsCoord0
    have h02 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord0 nsCoord2
    rw [show fderiv ℝ
        (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord2 nsCoord0 -
            spatialDerivativeComponent u s x nsCoord0 nsCoord2) t =
        fderiv ℝ (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord2 nsCoord0) t -
          fderiv ℝ (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord0 nsCoord2) t from
        fderiv_sub h20 h02]
    simp [spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField hu t x,
      spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
  · change (timeVorticityDerivative u t x) nsCoord2 =
      (spatialVorticity (timeVelocityDerivativeField u) t x) nsCoord2
    rw [timeVorticityDerivative_component_eq_fderiv_coordinate hu t x nsCoord2]
    have hfun :
        (fun s : NSTime => (spatialVorticity u s x) nsCoord2) =
          (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord0 nsCoord1 -
              spatialDerivativeComponent u s x nsCoord1 nsCoord0) := by
      funext s
      simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    rw [hfun]
    have h01 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord0 nsCoord1
    have h10 := spatialDerivativeComponent_differentiableAt_time_of_smooth
      hu t x nsCoord1 nsCoord0
    rw [show fderiv ℝ
        (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord0 nsCoord1 -
            spatialDerivativeComponent u s x nsCoord1 nsCoord0) t =
        fderiv ℝ (fun s : NSTime =>
          spatialDerivativeComponent u s x nsCoord0 nsCoord1) t -
          fderiv ℝ (fun s : NSTime =>
            spatialDerivativeComponent u s x nsCoord1 nsCoord0) t from
        fderiv_sub h01 h10]
    simp [spatialDerivativeComponent_time_derivative_eq_timeVelocityDerivativeField hu t x,
      spatialVorticity, nsCoord0, nsCoord1, nsCoord2]

/-- A linear map on `NSSpace` is determined componentwise by its values on the
coordinate basis. -/
theorem nsContinuousLinearMap_apply_eq_sum_basis
    (L : NSSpace →L[ℝ] NSSpace) (v : NSSpace) (comp : Fin 3) :
    (L v) comp =
      ∑ i : Fin 3, v i * (L (EuclideanSpace.single i (1 : ℝ))) comp := by
  have hv : v = ∑ i : Fin 3, EuclideanSpace.single i (v i) := by
    ext j
    simp
  nth_rw 1 [hv]
  rw [map_sum]
  change (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ)
      (∑ x : Fin 3, L (EuclideanSpace.single x (v x))) =
    ∑ i : Fin 3, v i * (L (EuclideanSpace.single i (1 : ℝ))) comp
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hsingle :
      EuclideanSpace.single i (v i) =
        v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [EuclideanSpace.single, hji]
  rw [hsingle, map_smul]
  simp

/-- Component form of linearity on a coordinate-basis vector. -/
theorem nsContinuousLinearMap_apply_single
    (L : NSSpace →L[ℝ] NSSpace) (i comp : Fin 3) (a : ℝ) :
    (L (EuclideanSpace.single i a)) comp =
      a * (L (EuclideanSpace.single i (1 : ℝ))) comp := by
  have hsingle :
      EuclideanSpace.single i a =
        a • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [EuclideanSpace.single, hji]
  rw [hsingle, map_smul]
  simp

/-- For a smooth fixed-time velocity slice, the derivative of the spatial
Jacobian is symmetric in the outer direction and the applied vector. -/
theorem spatialFDeriv_fderiv_apply_swap_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x v w : NSSpace) :
    ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x) v) w =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x) w) v := by
  have hslice : ContDiff ℝ ∞ (fun y : NSSpace => u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have hsymm : IsSymmSndFDerivAt ℝ (fun y : NSSpace => u t y) x := by
    exact (hslice.contDiffAt (x := x)).isSymmSndFDerivAt (by
      simpa using ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  simpa [spatialFDeriv] using hsymm.eq v w

/-- Spatial derivative of a scalar coordinate of the velocity Jacobian. -/
theorem fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x v : NSSpace) (coord comp : Fin 3) :
    fderiv ℝ (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) x v =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x v)
        (EuclideanSpace.single coord (1 : ℝ))) comp := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  have hslice : ContDiff ℝ ∞ (fun y : NSSpace => u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have hgradAt : DifferentiableAt ℝ (fun y : NSSpace => spatialFDeriv u t y) x := by
    exact (hslice.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change (fderiv ℝ (fun y : NSSpace => (spatialFDeriv u t y e) comp) x v) =
    ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x v) e) comp
  have happly :
      fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y e) x =
        (fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x).flip e := by
    rw [fderiv_clm_apply hgradAt (differentiableAt_const e)]
    ext z
    simp
  rw [show (fun y : NSSpace => (spatialFDeriv u t y e) comp) =
      (fun z : NSSpace => z comp) ∘ (fun y : NSSpace => spatialFDeriv u t y e) by rfl]
  rw [fderiv_comp]
  · rw [happly]
    have hproj :
        fderiv ℝ (fun z : NSSpace => z comp) ((spatialFDeriv u t x) e) =
          (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ) := by
      change fderiv ℝ (EuclideanSpace.proj comp : NSSpace → ℝ)
          ((spatialFDeriv u t x) e) =
        (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ)
      exact (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).fderiv
    rw [hproj]
    rfl
  · exact (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ).differentiableAt
  · exact hgradAt.clm_apply (differentiableAt_const (c := e))

/-- Smooth velocities make scalar spatial-derivative components differentiable
in the spatial variable. -/
theorem spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    DifferentiableAt ℝ (fun y : NSSpace =>
      spatialDerivativeComponent u t y coord comp) x := by
  have hst :=
    spatialDerivativeComponent_contDiff_spacetime_of_smooth hu coord comp
  have hslice :
      ContDiff ℝ ∞
        (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) :=
    contDiff_congr_global
      (hst.comp (contDiff_prodMk_right (𝕜 := ℝ) t)) (by intro y; rfl)
  exact hslice.differentiable (by simp) x

/-- A coordinate of the transport term is the directional derivative of the
corresponding coordinate of vorticity. -/
theorem vorticityTransportTerm_component_eq_fderiv_coordinate
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (i : Fin 3) :
    (vorticityTransportTerm u t x) i =
      fderiv ℝ (fun y : NSSpace => (spatialVorticity u t y) i) x (u t x) := by
  have hdiff : DifferentiableAt ℝ (fun y : NSSpace => spatialVorticity u t y) x :=
    smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (spatialVorticity_smoothSpaceTimeVelocity_of_smooth hu) t x
  have hhas : HasFDerivAt (fun y : NSSpace => (spatialVorticity u t y) i)
      ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).comp
        (fderiv ℝ (fun y : NSSpace => spatialVorticity u t y) x)) x := by
    exact (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt.comp
      x hdiff.hasFDerivAt
  rw [vorticityTransportTerm, spatialFDeriv, hhas.fderiv]
  simp [ContinuousLinearMap.comp_apply]

/-- First coordinate expansion of `(u . grad) omega`. -/
theorem vorticityTransportTerm_component0_eq_fderiv_spatialFDeriv_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (vorticityTransportTerm u t x) nsCoord0 =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord2 -
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord1 := by
  have h1 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord1 nsCoord2
  have h2 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord2 nsCoord1
  rw [vorticityTransportTerm_component_eq_fderiv_coordinate hu t x nsCoord0]
  have hfun :
      (fun y : NSSpace => (spatialVorticity u t y) nsCoord0) =
        (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord1 nsCoord2 -
            spatialDerivativeComponent u t y nsCoord2 nsCoord1) := by
    funext y
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
  rw [hfun]
  have h12 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord1 nsCoord2
  have h21 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord2 nsCoord1
  rw [show fderiv ℝ
      (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord1 nsCoord2 -
          spatialDerivativeComponent u t y nsCoord2 nsCoord1) x =
      fderiv ℝ (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord1 nsCoord2) x -
        fderiv ℝ (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord2 nsCoord1) x from
      fderiv_sub h12 h21]
  simp only [sub_apply]
  rw [h1, h2]

/-- Second coordinate expansion of `(u . grad) omega`. -/
theorem vorticityTransportTerm_component1_eq_fderiv_spatialFDeriv_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (vorticityTransportTerm u t x) nsCoord1 =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord0 -
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord2 := by
  have h1 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord2 nsCoord0
  have h2 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord0 nsCoord2
  rw [vorticityTransportTerm_component_eq_fderiv_coordinate hu t x nsCoord1]
  have hfun :
      (fun y : NSSpace => (spatialVorticity u t y) nsCoord1) =
        (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord2 nsCoord0 -
            spatialDerivativeComponent u t y nsCoord0 nsCoord2) := by
    funext y
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
  rw [hfun]
  have h20 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord2 nsCoord0
  have h02 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord0 nsCoord2
  rw [show fderiv ℝ
      (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord2 nsCoord0 -
          spatialDerivativeComponent u t y nsCoord0 nsCoord2) x =
      fderiv ℝ (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord2 nsCoord0) x -
        fderiv ℝ (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord0 nsCoord2) x from
      fderiv_sub h20 h02]
  simp only [sub_apply]
  rw [h1, h2]

/-- Third coordinate expansion of `(u . grad) omega`. -/
theorem vorticityTransportTerm_component2_eq_fderiv_spatialFDeriv_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (vorticityTransportTerm u t x) nsCoord2 =
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord1 -
      ((fderiv ℝ (fun y : NSSpace => spatialFDeriv u t y) x (u t x))
        (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord0 := by
  have h1 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord0 nsCoord1
  have h2 :=
    fderiv_spatialDerivativeComponent_eq_fderiv_spatialFDeriv_apply_of_smooth
      hu t x (u t x) nsCoord1 nsCoord0
  rw [vorticityTransportTerm_component_eq_fderiv_coordinate hu t x nsCoord2]
  have hfun :
      (fun y : NSSpace => (spatialVorticity u t y) nsCoord2) =
        (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord0 nsCoord1 -
            spatialDerivativeComponent u t y nsCoord1 nsCoord0) := by
    funext y
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
  rw [hfun]
  have h01 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord0 nsCoord1
  have h10 := spatialDerivativeComponent_differentiableAt_spatial_of_smooth
    hu t x nsCoord1 nsCoord0
  rw [show fderiv ℝ
      (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord0 nsCoord1 -
          spatialDerivativeComponent u t y nsCoord1 nsCoord0) x =
      fderiv ℝ (fun y : NSSpace =>
        spatialDerivativeComponent u t y nsCoord0 nsCoord1) x -
        fderiv ℝ (fun y : NSSpace =>
          spatialDerivativeComponent u t y nsCoord1 nsCoord0) x from
      fderiv_sub h01 h10]
  simp only [sub_apply]
  rw [h1, h2]

/-- First coordinate of the divergence-form curl-convection identity. -/
theorem spatialVorticity_spatialConvectionField_component0_eq_transport_sub_stretching_add_divergence
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (spatialVorticity (spatialConvectionField u) t x) nsCoord0 =
      (vorticityTransportTerm u t x) nsCoord0 -
        (vorticityStretchingTerm u t x) nsCoord0 +
          spatialDivergence u t x * (spatialVorticity u t x) nsCoord0 := by
  rw [vorticityTransportTerm_component0_eq_fderiv_spatialFDeriv_of_smooth hu t x]
  rw [show (spatialVorticity (spatialConvectionField u) t x) nsCoord0 =
    spatialDerivativeComponent (spatialConvectionField u) t x nsCoord1 nsCoord2 -
        spatialDerivativeComponent (spatialConvectionField u) t x nsCoord2 nsCoord1 by
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord1 nsCoord2]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord2 nsCoord1]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord1 (1 : ℝ)) (u t x)]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord2 (1 : ℝ)) (u t x)]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord2]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord1]
  simp [spatialVorticity, vorticityStretchingTerm, spatialDivergence,
    Fin.sum_univ_three]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord0 nsCoord0
    (spatialDerivativeComponent u t x nsCoord1 nsCoord2 -
      spatialDerivativeComponent u t x nsCoord2 nsCoord1)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord1 nsCoord0
    (spatialDerivativeComponent u t x nsCoord2 nsCoord0 -
      spatialDerivativeComponent u t x nsCoord0 nsCoord2)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord2 nsCoord0
    (spatialDerivativeComponent u t x nsCoord0 nsCoord1 -
      spatialDerivativeComponent u t x nsCoord1 nsCoord0)]
  simp [spatialDerivativeComponent, nsCoord0, nsCoord1, nsCoord2]
  ring_nf

/-- Second coordinate of the divergence-form curl-convection identity. -/
theorem spatialVorticity_spatialConvectionField_component1_eq_transport_sub_stretching_add_divergence
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (spatialVorticity (spatialConvectionField u) t x) nsCoord1 =
      (vorticityTransportTerm u t x) nsCoord1 -
        (vorticityStretchingTerm u t x) nsCoord1 +
          spatialDivergence u t x * (spatialVorticity u t x) nsCoord1 := by
  rw [vorticityTransportTerm_component1_eq_fderiv_spatialFDeriv_of_smooth hu t x]
  rw [show (spatialVorticity (spatialConvectionField u) t x) nsCoord1 =
    spatialDerivativeComponent (spatialConvectionField u) t x nsCoord2 nsCoord0 -
        spatialDerivativeComponent (spatialConvectionField u) t x nsCoord0 nsCoord2 by
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord2 nsCoord0]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord0 nsCoord2]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord2 (1 : ℝ)) (u t x)]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord0 (1 : ℝ)) (u t x)]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord2 (1 : ℝ))) nsCoord0]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord2]
  simp [spatialVorticity, vorticityStretchingTerm, spatialDivergence,
    Fin.sum_univ_three]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord0 nsCoord1
    (spatialDerivativeComponent u t x nsCoord1 nsCoord2 -
      spatialDerivativeComponent u t x nsCoord2 nsCoord1)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord1 nsCoord1
    (spatialDerivativeComponent u t x nsCoord2 nsCoord0 -
      spatialDerivativeComponent u t x nsCoord0 nsCoord2)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord2 nsCoord1
    (spatialDerivativeComponent u t x nsCoord0 nsCoord1 -
      spatialDerivativeComponent u t x nsCoord1 nsCoord0)]
  simp [spatialDerivativeComponent, nsCoord0, nsCoord1, nsCoord2]
  ring_nf

/-- Third coordinate of the divergence-form curl-convection identity. -/
theorem spatialVorticity_spatialConvectionField_component2_eq_transport_sub_stretching_add_divergence
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    (spatialVorticity (spatialConvectionField u) t x) nsCoord2 =
      (vorticityTransportTerm u t x) nsCoord2 -
        (vorticityStretchingTerm u t x) nsCoord2 +
          spatialDivergence u t x * (spatialVorticity u t x) nsCoord2 := by
  rw [vorticityTransportTerm_component2_eq_fderiv_spatialFDeriv_of_smooth hu t x]
  rw [show (spatialVorticity (spatialConvectionField u) t x) nsCoord2 =
    spatialDerivativeComponent (spatialConvectionField u) t x nsCoord0 nsCoord1 -
        spatialDerivativeComponent (spatialConvectionField u) t x nsCoord1 nsCoord0 by
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord0 nsCoord1]
  rw [spatialDerivativeComponent_spatialConvectionField_eq_productRule_of_smooth
    hu t x nsCoord1 nsCoord0]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord0 (1 : ℝ)) (u t x)]
  rw [spatialFDeriv_fderiv_apply_swap_of_smooth
    hu t x (EuclideanSpace.single nsCoord1 (1 : ℝ)) (u t x)]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord0 (1 : ℝ))) nsCoord1]
  rw [nsContinuousLinearMap_apply_eq_sum_basis
    (spatialFDeriv u t x)
    (spatialFDeriv u t x (EuclideanSpace.single nsCoord1 (1 : ℝ))) nsCoord0]
  simp [spatialVorticity, vorticityStretchingTerm, spatialDivergence,
    Fin.sum_univ_three]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord0 nsCoord2
    (spatialDerivativeComponent u t x nsCoord1 nsCoord2 -
      spatialDerivativeComponent u t x nsCoord2 nsCoord1)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord1 nsCoord2
    (spatialDerivativeComponent u t x nsCoord2 nsCoord0 -
      spatialDerivativeComponent u t x nsCoord0 nsCoord2)]
  rw [nsContinuousLinearMap_apply_single
    (spatialFDeriv u t x) nsCoord2 nsCoord2
    (spatialDerivativeComponent u t x nsCoord0 nsCoord1 -
      spatialDerivativeComponent u t x nsCoord1 nsCoord0)]
  simp [spatialDerivativeComponent, nsCoord0, nsCoord1, nsCoord2]
  ring_nf

/-- Divergence-form curl-convection identity:
`curl((u . grad)u) = (u . grad)omega - (omega . grad)u + (div u) omega`. -/
theorem spatialVorticity_spatialConvectionField_eq_transport_sub_stretching_add_divergence
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (spatialConvectionField u) t x =
      vorticityTransportTerm u t x - vorticityStretchingTerm u t x +
        spatialDivergence u t x • spatialVorticity u t x := by
  ext i
  fin_cases i
  · change (spatialVorticity (spatialConvectionField u) t x) nsCoord0 =
      (vorticityTransportTerm u t x - vorticityStretchingTerm u t x +
        spatialDivergence u t x • spatialVorticity u t x) nsCoord0
    rw [spatialVorticity_spatialConvectionField_component0_eq_transport_sub_stretching_add_divergence
      hu t x]
    simp
  · change (spatialVorticity (spatialConvectionField u) t x) nsCoord1 =
      (vorticityTransportTerm u t x - vorticityStretchingTerm u t x +
        spatialDivergence u t x • spatialVorticity u t x) nsCoord1
    rw [spatialVorticity_spatialConvectionField_component1_eq_transport_sub_stretching_add_divergence
      hu t x]
    simp
  · change (spatialVorticity (spatialConvectionField u) t x) nsCoord2 =
      (vorticityTransportTerm u t x - vorticityStretchingTerm u t x +
        spatialDivergence u t x • spatialVorticity u t x) nsCoord2
    rw [spatialVorticity_spatialConvectionField_component2_eq_transport_sub_stretching_add_divergence
      hu t x]
    simp

/-- The curl-convection defect is exactly `(div u) omega` for smooth velocity
fields. -/
theorem vorticityConvectionExpansionDefect_eq_divergence_smul_vorticity_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityConvectionExpansionDefect u t x =
      spatialDivergence u t x • spatialVorticity u t x := by
  rw [vorticityConvectionExpansionDefect]
  rw [spatialVorticity_spatialConvectionField_eq_transport_sub_stretching_add_divergence
    hu t x]
  module

/-- Smooth divergence-free velocity fields have zero curl-convection defect at
each point. -/
theorem vorticityConvectionExpansionDefect_eq_zero_of_smooth_divergence
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    {t : NSTime} {x : NSSpace} (hdiv : spatialDivergence u t x = 0) :
    vorticityConvectionExpansionDefect u t x = 0 := by
  rw [vorticityConvectionExpansionDefect_eq_divergence_smul_vorticity_of_smooth
    hu t x, hdiv]
  simp

/-- Differentiating a Laplacian gives the trace of the third Frechet
derivative with the new direction in the first slot. -/
theorem fderiv_laplacian_apply_eq_sum_iteratedFDeriv_three
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x e : NSSpace) :
    fderiv ℝ (fun y : NSSpace => Δ f y) x e =
      ∑ i : Fin (Module.finrank ℝ NSSpace),
        (iteratedFDeriv ℝ 3 f x)
          ![e, (stdOrthonormalBasis ℝ NSSpace) i,
            (stdOrthonormalBasis ℝ NSSpace) i] := by
  have hiter :
      Differentiable ℝ (fun y : NSSpace => iteratedFDeriv ℝ 2 f y) :=
    hf.differentiable_iteratedFDeriv (m := 2) (by
      exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top 2))
  have hterm : ∀ i : Fin (Module.finrank ℝ NSSpace),
      DifferentiableAt ℝ
        (fun y : NSSpace =>
          (iteratedFDeriv ℝ 2 f y)
            ![(stdOrthonormalBasis ℝ NSSpace) i,
              (stdOrthonormalBasis ℝ NSSpace) i]) x := by
    intro i
    exact (hiter x).continuousMultilinear_apply_const
      ![(stdOrthonormalBasis ℝ NSSpace) i,
        (stdOrthonormalBasis ℝ NSSpace) i]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y =>
    (iteratedFDeriv ℝ 2 f y)
      ![(stdOrthonormalBasis ℝ NSSpace) i,
        (stdOrthonormalBasis ℝ NSSpace) i]) (by
      intro i _hi
      exact hterm i)]
  rw [sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [fderiv_continuousMultilinear_apply_const_apply (hiter x)
    ![(stdOrthonormalBasis ℝ NSSpace) i,
      (stdOrthonormalBasis ℝ NSSpace) i] e]
  rw [fderiv_iteratedFDeriv]
  simp [continuousMultilinearCurryLeftEquiv_apply]

/-- The Laplacian of a fixed directional derivative gives the same trace with
the fixed direction in the last slot. -/
theorem laplacian_fderiv_apply_eq_sum_iteratedFDeriv_three
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x e : NSSpace) :
    Δ (fun y : NSSpace => fderiv ℝ f y e) x =
      ∑ i : Fin (Module.finrank ℝ NSSpace),
        (iteratedFDeriv ℝ 3 f x)
          ![(stdOrthonormalBasis ℝ NSSpace) i,
            (stdOrthonormalBasis ℝ NSSpace) i, e] := by
  have hfderiv : ContDiff ℝ ∞ (fun y : NSSpace => fderiv ℝ f y) :=
    hf.fderiv_right (m := ∞) (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [iteratedFDeriv_clm_apply_const_apply (hc := hfderiv)
    (i := 2) (hi := by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2) (u := e)]
  have hright :=
    (iteratedFDeriv_succ_apply_right
      (𝕜 := ℝ) (f := f) (x := x) (n := 2)
      (m := ![(stdOrthonormalBasis ℝ NSSpace) i,
        (stdOrthonormalBasis ℝ NSSpace) i, e])).symm
  rw [show
      Fin.init ![(stdOrthonormalBasis ℝ NSSpace) i,
        (stdOrthonormalBasis ℝ NSSpace) i, e] =
        ![(stdOrthonormalBasis ℝ NSSpace) i,
          (stdOrthonormalBasis ℝ NSSpace) i] by
        ext j
        fin_cases j <;> rfl] at hright
  exact hright

/-- In `C∞`, the first two slots of the third Frechet derivative commute.
This avoids the stronger analytic-only full permutation theorem. -/
theorem iteratedFDeriv_three_swap_first_two_of_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x a b c : NSSpace) :
    (iteratedFDeriv ℝ 3 f x) ![a, b, c] =
      (iteratedFDeriv ℝ 3 f x) ![b, a, c] := by
  have hfderiv : ContDiff ℝ ∞ (fun y : NSSpace => fderiv ℝ f y) :=
    hf.fderiv_right (m := ∞) (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ (fun y : NSSpace => fderiv ℝ f y) x := by
    exact (hfderiv.contDiffAt (x := x)).isSymmSndFDerivAt (by
      simpa using ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  rw [iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x) (n := 2) (m := ![a, b, c])]
  rw [iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := f) (x := x) (n := 2) (m := ![b, a, c])]
  rw [show Fin.init ![a, b, c] = ![a, b] by
      ext j; fin_cases j <;> rfl]
  rw [show Fin.init ![b, a, c] = ![b, a] by
      ext j; fin_cases j <;> rfl]
  change ((iteratedFDeriv ℝ 2 (fun y : NSSpace => fderiv ℝ f y) x) ![a, b]) c =
    ((iteratedFDeriv ℝ 2 (fun y : NSSpace => fderiv ℝ f y) x) ![b, a]) c
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact congrArg (fun L : NSSpace →L[ℝ] F => L c) (hsymm.eq a b)

/-- In `C∞`, the last two slots of the third Frechet derivative commute,
obtained by differentiating the ordinary second-derivative symmetry identity. -/
theorem iteratedFDeriv_three_swap_last_two_of_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x a b c : NSSpace) :
    (iteratedFDeriv ℝ 3 f x) ![a, b, c] =
      (iteratedFDeriv ℝ 3 f x) ![a, c, b] := by
  have hiter :
      Differentiable ℝ (fun y : NSSpace => iteratedFDeriv ℝ 2 f y) :=
    hf.differentiable_iteratedFDeriv (m := 2) (by
      exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top 2))
  have hbc :
      (fun y : NSSpace => (iteratedFDeriv ℝ 2 f y) ![b, c]) =
        fun y : NSSpace => fderiv ℝ (fderiv ℝ f) y b c := by
    funext y
    simpa using
      (iteratedFDeriv_two_apply (𝕜 := ℝ) (f := f) (z := y) (m := ![b, c]))
  have hcb :
      (fun y : NSSpace => (iteratedFDeriv ℝ 2 f y) ![c, b]) =
        fun y : NSSpace => fderiv ℝ (fderiv ℝ f) y c b := by
    funext y
    simpa using
      (iteratedFDeriv_two_apply (𝕜 := ℝ) (f := f) (z := y) (m := ![c, b]))
  have hsymmFun :
      (fun y : NSSpace => fderiv ℝ (fderiv ℝ f) y b c) =
        fun y : NSSpace => fderiv ℝ (fderiv ℝ f) y c b := by
    funext y
    have hsymm : IsSymmSndFDerivAt ℝ f y := by
      exact (hf.contDiffAt (x := y)).isSymmSndFDerivAt (by
        simpa using ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
    exact hsymm.eq b c
  rw [iteratedFDeriv_succ_apply_left
    (𝕜 := ℝ) (f := f) (x := x) (n := 2) (m := ![a, b, c])]
  rw [iteratedFDeriv_succ_apply_left
    (𝕜 := ℝ) (f := f) (x := x) (n := 2) (m := ![a, c, b])]
  rw [show Fin.tail ![a, b, c] = ![b, c] by
      ext j; fin_cases j <;> rfl]
  rw [show Fin.tail ![a, c, b] = ![c, b] by
      ext j; fin_cases j <;> rfl]
  change ((fderiv ℝ (fun y : NSSpace => iteratedFDeriv ℝ 2 f y) x) a) ![b, c] =
    ((fderiv ℝ (fun y : NSSpace => iteratedFDeriv ℝ 2 f y) x) a) ![c, b]
  rw [← fderiv_continuousMultilinear_apply_const_apply (hiter x) ![b, c] a]
  rw [← fderiv_continuousMultilinear_apply_const_apply (hiter x) ![c, b] a]
  rw [hbc, hcb, hsymmFun]

/-- Directional derivatives commute with the spatial Laplacian for smooth
fixed-time slices. -/
theorem fderiv_laplacian_apply_eq_laplacian_fderiv_apply_of_contDiff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : NSSpace → F} (hf : ContDiff ℝ ∞ f)
    (x e : NSSpace) :
    fderiv ℝ (fun y : NSSpace => Δ f y) x e =
      Δ (fun y : NSSpace => fderiv ℝ f y e) x := by
  rw [fderiv_laplacian_apply_eq_sum_iteratedFDeriv_three hf x e]
  rw [laplacian_fderiv_apply_eq_sum_iteratedFDeriv_three hf x e]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let b : NSSpace := (stdOrthonormalBasis ℝ NSSpace) i
  calc
    (iteratedFDeriv ℝ 3 f x) ![e, b, b]
        = (iteratedFDeriv ℝ 3 f x) ![b, e, b] := by
          exact iteratedFDeriv_three_swap_first_two_of_contDiff hf x e b b
    _ = (iteratedFDeriv ℝ 3 f x) ![b, b, e] := by
          exact iteratedFDeriv_three_swap_last_two_of_contDiff hf x b e b

/-- For smooth velocity fields, each coordinate derivative of `Delta u`
equals the Laplacian of the corresponding coordinate derivative of `u`. -/
theorem spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) (coord comp : Fin 3) :
    spatialDerivativeComponent (spatialLaplacianField u) t x coord comp =
      Δ (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) x := by
  let e : NSSpace := EuclideanSpace.single coord (1 : ℝ)
  let f : NSSpace → NSSpace := fun y => u t y
  have hf : ContDiff ℝ ∞ f :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice hu t
  have hcomm :=
    congrArg (fun z : NSSpace => z comp)
      (fderiv_laplacian_apply_eq_laplacian_fderiv_apply_of_contDiff
        (f := f) hf x e)
  have hfderiv : ContDiff ℝ ∞ (fun y : NSSpace => fderiv ℝ f y) :=
    hf.fderiv_right (m := ∞) (by simp)
  have hdir :
      ContDiff ℝ ∞ (fun y : NSSpace => fderiv ℝ f y e) :=
    hfderiv.clm_apply contDiff_const
  have hproj :=
    ((hdir.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)).laplacian_CLM_comp_left
      (l := (EuclideanSpace.proj comp : NSSpace →L[ℝ] ℝ))
  change (fderiv ℝ (fun y : NSSpace => Δ f y) x e) comp =
    Δ (fun y : NSSpace => (fderiv ℝ f y e) comp) x
  calc
    (fderiv ℝ (fun y : NSSpace => Δ f y) x e) comp
        = (Δ (fun y : NSSpace => fderiv ℝ f y e) x) comp := hcomm
    _ = Δ (fun y : NSSpace => (fderiv ℝ f y e) comp) x := by
          simpa [Function.comp_def] using hproj.symm

/-- Smoothness commutes the concrete curl with the spatial Laplacian. -/
theorem spatialVorticity_spatialLaplacianField_eq_vorticityDiffusionTerm_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    spatialVorticity (spatialLaplacianField u) t x =
      vorticityDiffusionTerm u t x := by
  have hωslice :
      ContDiff ℝ ∞ (fun y : NSSpace => spatialVorticity u t y) :=
    smoothSpaceTimeVelocity_contDiff_spatialSlice
      (spatialVorticity_smoothSpaceTimeVelocity_of_smooth hu) t
  have hωproj : ∀ i : Fin 3,
      (vorticityDiffusionTerm u t x) i =
        Δ (fun y : NSSpace => (spatialVorticity u t y) i) x := by
    intro i
    have hproj :=
      ((hωslice.contDiffAt (x := x)).of_le (by
        exact ENat.natCast_le_of_coe_top_le_withTop
          (N := (∞ : WithTop ℕ∞)) (by rfl) 2)).laplacian_CLM_comp_left
        (l := (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ))
    simpa [vorticityDiffusionTerm, spatialLaplacian, Function.comp_def] using hproj.symm
  have hderivAt : ∀ coord comp : Fin 3,
      ContDiffAt ℝ 2
        (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) x := by
    intro coord comp
    have hst :=
      spatialDerivativeComponent_contDiff_spacetime_of_smooth hu coord comp
    have hslice :
        ContDiff ℝ ∞
          (fun y : NSSpace => spatialDerivativeComponent u t y coord comp) :=
      contDiff_congr_global
        (hst.comp (contDiff_prodMk_right (𝕜 := ℝ) t)) (by intro y; rfl)
    exact (hslice.contDiffAt (x := x)).of_le (by
      exact ENat.natCast_le_of_coe_top_le_withTop
        (N := (∞ : WithTop ℕ∞)) (by rfl) 2)
  ext i
  fin_cases i
  · change (spatialVorticity (spatialLaplacianField u) t x) nsCoord0 =
      (vorticityDiffusionTerm u t x) nsCoord0
    rw [hωproj nsCoord0]
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    change
      spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord1 nsCoord2 -
          spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord2 nsCoord1 =
        Δ ((fun y : NSSpace => spatialDerivativeComponent u t y nsCoord1 nsCoord2) -
          fun y : NSSpace => spatialDerivativeComponent u t y nsCoord2 nsCoord1) x
    rw [(hderivAt nsCoord1 nsCoord2).laplacian_sub
      (hderivAt nsCoord2 nsCoord1)]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord1 nsCoord2]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord2 nsCoord1]
  · change (spatialVorticity (spatialLaplacianField u) t x) nsCoord1 =
      (vorticityDiffusionTerm u t x) nsCoord1
    rw [hωproj nsCoord1]
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    change
      spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord2 nsCoord0 -
          spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord0 nsCoord2 =
        Δ ((fun y : NSSpace => spatialDerivativeComponent u t y nsCoord2 nsCoord0) -
          fun y : NSSpace => spatialDerivativeComponent u t y nsCoord0 nsCoord2) x
    rw [(hderivAt nsCoord2 nsCoord0).laplacian_sub
      (hderivAt nsCoord0 nsCoord2)]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord2 nsCoord0]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord0 nsCoord2]
  · change (spatialVorticity (spatialLaplacianField u) t x) nsCoord2 =
      (vorticityDiffusionTerm u t x) nsCoord2
    rw [hωproj nsCoord2]
    simp [spatialVorticity, nsCoord0, nsCoord1, nsCoord2]
    change
      spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord0 nsCoord1 -
          spatialDerivativeComponent (spatialLaplacianField u) t x nsCoord1 nsCoord0 =
        Δ ((fun y : NSSpace => spatialDerivativeComponent u t y nsCoord0 nsCoord1) -
          fun y : NSSpace => spatialDerivativeComponent u t y nsCoord1 nsCoord0) x
    rw [(hderivAt nsCoord0 nsCoord1).laplacian_sub
      (hderivAt nsCoord1 nsCoord0)]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord0 nsCoord1]
    rw [spatialDerivativeComponent_spatialLaplacianField_eq_laplacian_spatialDerivativeComponent
      hu t x nsCoord1 nsCoord0]

/-- Smooth velocities have zero curl/Laplacian commutation defect at each
point. -/
theorem vorticityLaplacianCommutationDefect_eq_zero_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityLaplacianCommutationDefect u t x = 0 := by
  rw [vorticityLaplacianCommutationDefect]
  rw [spatialVorticity_spatialLaplacianField_eq_vorticityDiffusionTerm_of_smooth
    hu t x]
  simp

/-- Smooth spacetime velocities have zero curl/time commutation defect at each
point. -/
theorem vorticityTimeCommutationDefect_eq_zero_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    vorticityTimeCommutationDefect u t x = 0 := by
  rw [vorticityTimeCommutationDefect]
  rw [← timeVorticityDerivative_eq_spatialVorticity_timeVelocityDerivativeField hu t x]
  simp

/-- After the Laplacian-field differentiability bridge, smoothness supplies the
other two differentiability hypotheses needed for residual-curl linearity. -/
theorem residualCurlLinearityDifferentiableAt_of_smooth_laplacian
    {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hu : smoothSpaceTimeVelocity u)
    (hlap : DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x) :
    residualCurlLinearityDifferentiableAt u t x :=
  ⟨hlap, timeVelocityDerivativeField_differentiableAt_of_smooth hu t x,
    spatialConvectionField_differentiableAt_of_smooth hu t x⟩

/-- Smooth velocities give the pointwise differentiability hypotheses needed
for residual-curl linearity. -/
theorem residualCurlLinearityDifferentiableAt_of_smooth
    {u : NSVelocityField} (hu : smoothSpaceTimeVelocity u)
    (t : NSTime) (x : NSSpace) :
    residualCurlLinearityDifferentiableAt u t x :=
  residualCurlLinearityDifferentiableAt_of_smooth_laplacian
    (u := u) (t := t) (x := x) hu
    (spatialLaplacianField_differentiableAt_of_smooth hu t x)

/-- Ordinary spatial differentiability of the three pressure-residual
components closes the curl-linearity defect at a point. -/
theorem residualCurlLinearityDefect_eq_zero_of_differentiableAt
    {ν : ℝ} {u : NSVelocityField} {t : NSTime} {x : NSSpace}
    (hDiff : residualCurlLinearityDifferentiableAt u t x) :
    residualCurlLinearityDefect ν u t x = 0 := by
  have hlap :
      DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x :=
    hDiff.1
  have htime :
      DifferentiableAt ℝ (fun y : NSSpace => timeVelocityDerivativeField u t y) x :=
    hDiff.2.1
  have hconv :
      DifferentiableAt ℝ (fun y : NSSpace => spatialConvectionField u t y) x :=
    hDiff.2.2
  have hsmul :
      DifferentiableAt ℝ
        (fun y : NSSpace => (ν • spatialLaplacianField u) t y) x := by
    change DifferentiableAt ℝ
      (ν • fun y : NSSpace => spatialLaplacianField u t y) x
    exact hlap.const_smul ν
  have hfirst :
      DifferentiableAt ℝ
        (fun y : NSSpace =>
          (ν • spatialLaplacianField u - timeVelocityDerivativeField u) t y) x := by
    change DifferentiableAt ℝ
      ((fun y : NSSpace => (ν • spatialLaplacianField u) t y) -
        fun y : NSSpace => timeVelocityDerivativeField u t y) x
    exact hsmul.sub htime
  have hres :
      spatialVorticity (momentumPressureResidual ν u) t x =
        spatialVorticity
          (ν • spatialLaplacianField u - timeVelocityDerivativeField u -
            spatialConvectionField u) t x := by
    refine spatialVorticity_congr_at ?_
    intro y
    simp [momentumPressureResidual, spatialLaplacianField,
      timeVelocityDerivativeField, spatialConvectionField]
  rw [residualCurlLinearityDefect, hres]
  rw [spatialVorticity_sub hfirst hconv]
  rw [spatialVorticity_sub hsmul htime]
  rw [spatialVorticity_const_smul]
  module

/-- Exact algebraic decomposition of the residual-curl expansion defect into
the four differential-identity defects above. -/
theorem residualCurlExpansionDefect_eq_differentialIdentityDefects
    (ν : ℝ) (u : NSVelocityField) (t : NSTime) (x : NSSpace) :
    residualCurlExpansionDefect ν u t x =
      residualCurlLinearityDefect ν u t x +
        ν • vorticityLaplacianCommutationDefect u t x -
          vorticityTimeCommutationDefect u t x -
            vorticityConvectionExpansionDefect u t x := by
  simp [residualCurlExpansionDefect, residualCurlLinearityDefect,
    vorticityLaplacianCommutationDefect, vorticityTimeCommutationDefect,
    vorticityConvectionExpansionDefect, vorticityEquationResidual,
    vorticityMaterialDiffusionRemainder]
  module

/-- Slabwise closure of the residual-curl linearity defect. -/
def residualCurlLinearityClosedOn
    (ν : ℝ) (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → residualCurlLinearityDefect ν u t x = 0

/-- Slabwise spatial differentiability sufficient for residual-curl
linearity. -/
def residualCurlLinearityDifferentiableOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → residualCurlLinearityDifferentiableAt u t x

/-- Slabwise differentiability of only the Laplacian field. Smoothness supplies
the time-derivative and convection differentiability pieces. -/
def residualCurlLinearityLaplacianDifferentiableOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T →
    DifferentiableAt ℝ (fun y : NSSpace => spatialLaplacianField u t y) x

/-- Smooth velocities reduce slabwise residual-curl linearity differentiability
to slabwise differentiability of the Laplacian field. -/
theorem residualCurlLinearityDifferentiableOn_of_smooth_laplacian
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityDifferentiableOn u T := by
  intro t x ht0 htT
  exact residualCurlLinearityDifferentiableAt_of_smooth_laplacian
    (u := u) (t := t) (x := x) hu (hLap t x ht0 htT)

/-- Smooth velocities give slabwise residual-curl linearity differentiability. -/
theorem residualCurlLinearityDifferentiableOn_of_smooth
    {T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u) :
    residualCurlLinearityDifferentiableOn u T := by
  intro t x _ht0 _htT
  exact residualCurlLinearityDifferentiableAt_of_smooth hu t x

/-- Slabwise differentiability of the three residual components closes the
slabwise curl-linearity defect. -/
theorem residualCurlLinearityClosedOn_of_differentiableOn
    {ν T : ℝ} {u : NSVelocityField}
    (hDiff : residualCurlLinearityDifferentiableOn u T) :
    residualCurlLinearityClosedOn ν u T := by
  intro t x ht0 htT
  exact residualCurlLinearityDefect_eq_zero_of_differentiableAt
    (ν := ν) (u := u) (t := t) (x := x) (hDiff t x ht0 htT)

/-- Smoothness plus Laplacian-field differentiability closes the slabwise
curl-linearity defect. -/
theorem residualCurlLinearityClosedOn_of_smooth_laplacian
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hLap : residualCurlLinearityLaplacianDifferentiableOn u T) :
    residualCurlLinearityClosedOn ν u T :=
  residualCurlLinearityClosedOn_of_differentiableOn
    (residualCurlLinearityDifferentiableOn_of_smooth_laplacian hu hLap)

/-- Smoothness closes the slabwise residual-curl linearity defect. -/
theorem residualCurlLinearityClosedOn_of_smooth
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u) :
    residualCurlLinearityClosedOn ν u T :=
  residualCurlLinearityClosedOn_of_differentiableOn
    (residualCurlLinearityDifferentiableOn_of_smooth hu)

/-- Slabwise closure of curl/time commutation. -/
def vorticityTimeCommutationClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → vorticityTimeCommutationDefect u t x = 0

/-- Smooth spacetime velocities close curl/time commutation on every slab. -/
theorem vorticityTimeCommutationClosedOn_of_smooth
    {u : NSVelocityField} {T : ℝ} (hu : smoothSpaceTimeVelocity u) :
    vorticityTimeCommutationClosedOn u T := by
  intro t x _ht0 _htT
  exact vorticityTimeCommutationDefect_eq_zero_of_smooth hu t x

/-- Slabwise closure of curl/Laplacian commutation. -/
def vorticityLaplacianCommutationClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → vorticityLaplacianCommutationDefect u t x = 0

/-- Smooth spacetime velocities close curl/Laplacian commutation on every
slab. -/
theorem vorticityLaplacianCommutationClosedOn_of_smooth
    {u : NSVelocityField} {T : ℝ} (hu : smoothSpaceTimeVelocity u) :
    vorticityLaplacianCommutationClosedOn u T := by
  intro t x _ht0 _htT
  exact vorticityLaplacianCommutationDefect_eq_zero_of_smooth hu t x

/-- Slabwise closure of the incompressible curl-convection identity. -/
def vorticityConvectionExpansionClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → vorticityConvectionExpansionDefect u t x = 0

/-- Smooth divergence-free velocity fields close the slabwise
curl-convection identity. -/
theorem vorticityConvectionExpansionClosedOn_of_smooth_divergence
    {u : NSVelocityField} {T : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hdiv : ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) :
    vorticityConvectionExpansionClosedOn u T := by
  intro t x ht0 htT
  exact vorticityConvectionExpansionDefect_eq_zero_of_smooth_divergence
    hu (hdiv t x ht0 htT)

/-- Bundled slabwise differential identities sufficient to close the
residual-curl expansion defect. -/
def residualCurlDifferentialIdentitiesClosedOn
    (ν : ℝ) (u : NSVelocityField) (T : ℝ) : Prop :=
  residualCurlLinearityClosedOn ν u T ∧
    vorticityTimeCommutationClosedOn u T ∧
      vorticityLaplacianCommutationClosedOn u T ∧
        vorticityConvectionExpansionClosedOn u T

/-- The three residual-curl identities still needed after smoothness closes
curl-linearity. -/
def residualCurlCommutationExpansionClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  vorticityTimeCommutationClosedOn u T ∧
    vorticityLaplacianCommutationClosedOn u T ∧
      vorticityConvectionExpansionClosedOn u T

/-- Once smoothness supplies curl/time and curl/Laplacian commutation, the
residual-curl commutation bundle reduces to the incompressible convection
identity. -/
theorem residualCurlCommutationExpansionClosedOn_of_smooth_convection
    {u : NSVelocityField} {T : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hConv : vorticityConvectionExpansionClosedOn u T) :
    residualCurlCommutationExpansionClosedOn u T :=
  ⟨vorticityTimeCommutationClosedOn_of_smooth hu,
    vorticityLaplacianCommutationClosedOn_of_smooth hu, hConv⟩

/-- Smooth divergence-free velocities close the slabwise residual-curl
commutation/expansion package. -/
theorem residualCurlCommutationExpansionClosedOn_of_smooth_divergence
    {u : NSVelocityField} {T : ℝ}
    (hu : smoothSpaceTimeVelocity u)
    (hdiv : ∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) :
    residualCurlCommutationExpansionClosedOn u T :=
  residualCurlCommutationExpansionClosedOn_of_smooth_convection hu
    (vorticityConvectionExpansionClosedOn_of_smooth_divergence hu hdiv)

/-- A differentiability proof for curl-linearity plus the remaining three
commutation/expansion identities supplies the bundled residual-curl
differential identities. -/
theorem residualCurlDifferentialIdentitiesClosedOn_of_linearityDifferentiableOn
    {ν T : ℝ} {u : NSVelocityField}
    (hLin : residualCurlLinearityDifferentiableOn u T)
    (hTime : vorticityTimeCommutationClosedOn u T)
    (hLap : vorticityLaplacianCommutationClosedOn u T)
    (hConv : vorticityConvectionExpansionClosedOn u T) :
    residualCurlDifferentialIdentitiesClosedOn ν u T :=
  ⟨residualCurlLinearityClosedOn_of_differentiableOn hLin,
    hTime, hLap, hConv⟩

/-- Smoothness supplies curl-linearity, so only the three commutation/expansion
identities are needed for the bundled residual-curl differential identities. -/
theorem residualCurlDifferentialIdentitiesClosedOn_of_smooth_commutationExpansion
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hComm : residualCurlCommutationExpansionClosedOn u T) :
    residualCurlDifferentialIdentitiesClosedOn ν u T :=
  ⟨residualCurlLinearityClosedOn_of_smooth hu,
    hComm.1, hComm.2.1, hComm.2.2⟩

/-- Smoothness plus the three remaining commutation/expansion identities closes
the residual-curl expansion defect on a slab. -/
theorem residualCurlExpansionClosedOn_of_smooth_commutationExpansion
    {ν T : ℝ} {u : NSVelocityField}
    (hu : smoothSpaceTimeVelocity u)
    (hComm : residualCurlCommutationExpansionClosedOn u T) :
    residualCurlExpansionClosedOn ν u T := by
  intro t x ht0 htT
  rw [residualCurlExpansionDefect_eq_differentialIdentityDefects]
  rw [residualCurlLinearityClosedOn_of_smooth (ν := ν) (u := u) hu t x ht0 htT,
    hComm.1 t x ht0 htT, hComm.2.1 t x ht0 htT, hComm.2.2 t x ht0 htT]
  simp

/-- The bundled differential identities force the residual-curl expansion
defect to vanish on the same slab. -/
theorem residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn
    {ν T : ℝ} {u : NSVelocityField}
    (hIds : residualCurlDifferentialIdentitiesClosedOn ν u T) :
    residualCurlExpansionClosedOn ν u T := by
  intro t x ht0 htT
  rw [residualCurlExpansionDefect_eq_differentialIdentityDefects]
  rw [hIds.1 t x ht0 htT, hIds.2.1 t x ht0 htT,
    hIds.2.2.1 t x ht0 htT, hIds.2.2.2 t x ht0 htT]
  simp

/-- Precise remaining vector-calculus target, decomposed into the four
differential identities above for smooth incompressible velocity fields. -/
def BKMResidualCurlDifferentialIdentitiesClosed : Prop :=
  ∀ (ν : ℝ) (u : NSVelocityField) (T : ℝ),
    smoothSpaceTimeVelocity u →
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) →
        residualCurlDifferentialIdentitiesClosedOn ν u T

/-- Global remaining residual-curl target after curl-linearity has been closed
from smoothness. -/
def BKMResidualCurlCommutationExpansionClosed : Prop :=
  ∀ (u : NSVelocityField) (T : ℝ),
    smoothSpaceTimeVelocity u →
      (∀ t x, 0 ≤ t → t ≤ T → spatialDivergence u t x = 0) →
        residualCurlCommutationExpansionClosedOn u T

/-- Closing the three remaining commutation/expansion identities closes the
bundled residual-curl differential identity target. -/
theorem BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion
    (hComm : BKMResidualCurlCommutationExpansionClosed) :
    BKMResidualCurlDifferentialIdentitiesClosed := by
  intro ν u T hu hdiv
  exact residualCurlDifferentialIdentitiesClosedOn_of_smooth_commutationExpansion
    (ν := ν) hu (hComm u T hu hdiv)

/-- The concrete divergence-form curl-convection identity closes the global
residual-curl commutation/expansion package. -/
theorem BKMResidualCurlCommutationExpansionClosed_proved :
    BKMResidualCurlCommutationExpansionClosed := by
  intro u T hu hdiv
  exact residualCurlCommutationExpansionClosedOn_of_smooth_divergence hu hdiv

/-- The decomposed residual-curl differential identities are closed for smooth
incompressible velocities. -/
theorem BKMResidualCurlDifferentialIdentitiesClosed_proved :
    BKMResidualCurlDifferentialIdentitiesClosed :=
  BKMResidualCurlDifferentialIdentitiesClosed_of_commutationExpansion
    BKMResidualCurlCommutationExpansionClosed_proved

/-- Closing the decomposed differential identities closes the previous
residual-curl expansion target. -/
theorem BKMResidualCurlDifferentialIdentitiesClosed.implies_residualCurlExpansionDefectVanishes
    (hIds : BKMResidualCurlDifferentialIdentitiesClosed) :
    BKMResidualCurlExpansionDefectVanishes := by
  intro ν u T hsmooth hdiv
  exact residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn
    (hIds ν u T hsmooth hdiv)

/-- The residual-curl expansion defect vanishes for every smooth
incompressible slab. -/
theorem BKMResidualCurlExpansionDefectVanishes_proved :
    BKMResidualCurlExpansionDefectVanishes :=
  BKMResidualCurlDifferentialIdentitiesClosed.implies_residualCurlExpansionDefectVanishes
    BKMResidualCurlDifferentialIdentitiesClosed_proved

/-- A componentized residual-curl route can feed the analytic BKM component
bundle by first closing `BKMResidualCurlExpansionDefectVanishes`. -/
theorem BKMAnalyticComponentsClosed_of_residualCurlDifferentialIdentities
    (hIds : BKMResidualCurlDifferentialIdentitiesClosed)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticComponentsClosed :=
  ⟨hIds.implies_residualCurlExpansionDefectVanishes, hLog, hHigh⟩

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia

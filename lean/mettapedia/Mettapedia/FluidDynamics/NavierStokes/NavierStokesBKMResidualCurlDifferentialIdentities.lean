import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation

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

/-- Slabwise closure of curl/Laplacian commutation. -/
def vorticityLaplacianCommutationClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → vorticityLaplacianCommutationDefect u t x = 0

/-- Slabwise closure of the incompressible curl-convection identity. -/
def vorticityConvectionExpansionClosedOn
    (u : NSVelocityField) (T : ℝ) : Prop :=
  ∀ t x, 0 ≤ t → t ≤ T → vorticityConvectionExpansionDefect u t x = 0

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

/-- Closing the decomposed differential identities closes the previous
residual-curl expansion target. -/
theorem BKMResidualCurlDifferentialIdentitiesClosed.implies_residualCurlExpansionDefectVanishes
    (hIds : BKMResidualCurlDifferentialIdentitiesClosed) :
    BKMResidualCurlExpansionDefectVanishes := by
  intro ν u T hsmooth hdiv
  exact residualCurlExpansionClosedOn_of_differentialIdentitiesClosedOn
    (hIds ν u T hsmooth hdiv)

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

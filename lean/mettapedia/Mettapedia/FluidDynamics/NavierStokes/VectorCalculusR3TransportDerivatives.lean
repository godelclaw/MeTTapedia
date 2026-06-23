import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles

/-!
# Vector Calculus R3: Transport Derivatives

This module contains spatial/time derivative, divergence, initial divergence,
and initial-value matching identities for transported heat-shear fields.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped Gradient
open scoped Laplacian
open scoped BigOperators
open scoped ContDiff

section VectorCalculusR3

/-- The transported heat-shear field has the expected spatial Fréchet
derivative in the first velocity component. -/
theorem spatialFDeriv_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  let A : ℝ := a * Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  have hcoord : HasFDerivAt (fun y : NSSpace => k * (y nsCoord1 - b * t))
      ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)) x := by
    simpa [smul_eq_mul, sub_eq_add_neg, mul_assoc] using
      (((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).hasFDerivAt.sub_const (b * t)).const_smul k)
  have hsin : HasFDerivAt (fun y : NSSpace => Real.sin (k * (y nsCoord1 - b * t)))
      (Real.cos (k * (x nsCoord1 - b * t)) •
        ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))) x := by
    simpa using hcoord.sin
  have hscalar : HasFDerivAt
      (fun y : NSSpace => A * Real.sin (k * (y nsCoord1 - b * t)))
      ((A : ℝ) •
        (Real.cos (k * (x nsCoord1 - b * t)) •
          ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ)))) x := by
    simpa [A, smul_eq_mul] using hsin.const_smul A
  have hvec : HasFDerivAt
      (fun y : NSSpace => coord0Embedding (A * Real.sin (k * (y nsCoord1 - b * t))))
      (coord0Embedding.comp
        ((A : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) x := by
    exact coord0Embedding.hasFDerivAt.comp x hscalar
  have hcore :
      spatialFDeriv
        (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
      coord0Embedding.comp
        (((a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
    unfold spatialFDeriv
    simpa [heatShearTransportScalar, A, mul_assoc] using hvec.fderiv
  have hdiff :
      DifferentiableAt ℝ (fun y : NSSpace => coord0Embedding (heatShearTransportScalar ν a k b t y)) x := by
    simpa [heatShearTransportScalar, A, mul_assoc] using hvec.differentiableAt
  rw [heatShearTransportVelocityField]
  rw [spatialFDeriv_add
    hdiff
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord1 b)) t x)]
  simp [hcore, spatialFDeriv_constantVelocityField]

/-- The spatial Fréchet derivative of transported arbitrary-amplitude shear is
the transported heat-shear slice formula with sampled amplitude `A t`. -/
theorem spatialFDeriv_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialFDeriv (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding.comp
        (((A t : ℝ) •
          (Real.cos (k * (x nsCoord1 - b * t)) •
            ((k : ℝ) • (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ))))) := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialFDeriv_congr_at hslice]
  simpa [heatShearTransportScalar]
    using spatialFDeriv_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported heat-shear field has the expected advection-diffusion time
derivative. -/
theorem timeVelocityDerivative_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportVelocityField ν a k b) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) -
          a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  let E : ℝ := Real.exp (-(ν * k ^ (2 : ℕ)) * t)
  let S : ℝ := Real.sin (k * (x nsCoord1 - b * t))
  let C : ℝ := Real.cos (k * (x nsCoord1 - b * t))
  have hexp : HasDerivAt
      (fun s : ℝ => Real.exp (-(ν * k ^ (2 : ℕ)) * s))
      (Real.exp (-(ν * k ^ (2 : ℕ)) * t) * (-(ν * k ^ (2 : ℕ)))) t := by
    simpa [smul_eq_mul, mul_assoc] using
      (((hasDerivAt_id' t).const_mul (-(ν * k ^ (2 : ℕ)))).exp)
  have hphase : HasDerivAt
      (fun s : ℝ => k * (x nsCoord1 - b * s))
      (-(b * k)) t := by
    have hbase : HasDerivAt (fun s : ℝ => x nsCoord1 - b * s) (-b) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id' t).const_mul b).const_sub (x nsCoord1))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul k
  have hsin : HasDerivAt
      (fun s : ℝ => Real.sin (k * (x nsCoord1 - b * s)))
      (Real.cos (k * (x nsCoord1 - b * t)) * (-(b * k))) t := by
    simpa using hphase.sin
  have hscalar : HasDerivAt
      (fun s : ℝ =>
        a * Real.exp (-(ν * k ^ (2 : ℕ)) * s) *
          Real.sin (k * (x nsCoord1 - b * s)))
      (-(ν * k ^ (2 : ℕ)) * (a * E * S) - a * E * (b * k * C)) t := by
    convert (hexp.mul hsin).const_mul a using 1
    · simp [mul_assoc]
    · simp [E, S, C, mul_assoc, mul_left_comm, mul_comm]
      ring
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  have hcore :
      timeVelocityDerivative
          (fun t x => coord0Embedding (heatShearTransportScalar ν a k b t x)) t x =
        coord0Embedding
          (-(ν * k ^ (2 : ℕ)) * (a * E * S) - a * E * (b * k * C)) := by
    simpa [timeVelocityDerivative, timeFDeriv, heatShearTransportScalar,
      E, S, C, ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly
  have htdiff :
      DifferentiableAt ℝ (fun s : ℝ => coord0Embedding (heatShearTransportScalar ν a k b s x)) t := by
    simpa [heatShearTransportScalar, mul_assoc] using hvec.differentiableAt
  rw [heatShearTransportVelocityField]
  rw [timeVelocityDerivative_add]
  · simpa [hcore, E, S, C] using timeVelocityDerivative_constantVelocityField
      (EuclideanSpace.single nsCoord1 b) t x
  · exact htdiff
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The time derivative of transported arbitrary-amplitude shear contains the
sampled amplitude derivative and the phase-transport term. -/
theorem timeVelocityDerivative_amplitudeShearTransportVelocityField
    {A : NSTime → ℝ} {A' : ℝ} {t : NSTime}
    (hA : HasDerivAt A A' t) (k b : ℝ) (x : NSSpace) :
    timeVelocityDerivative (amplitudeShearTransportVelocityField A k b) t x =
      coord0Embedding
        (A' * Real.sin (k * (x nsCoord1 - b * t)) -
          A t * (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  let S : ℝ := Real.sin (k * (x nsCoord1 - b * t))
  let C : ℝ := Real.cos (k * (x nsCoord1 - b * t))
  have hphase : HasDerivAt
      (fun s : ℝ => k * (x nsCoord1 - b * s))
      (-(b * k)) t := by
    have hbase : HasDerivAt (fun s : ℝ => x nsCoord1 - b * s) (-b) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (((hasDerivAt_id' t).const_mul b).const_sub (x nsCoord1))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul k
  have hsin : HasDerivAt
      (fun s : ℝ => Real.sin (k * (x nsCoord1 - b * s)))
      (C * (-(b * k))) t := by
    simpa [C] using hphase.sin
  have hscalar : HasDerivAt
      (fun s : ℝ => A s * Real.sin (k * (x nsCoord1 - b * s)))
      (A' * S - A t * (b * k * C)) t := by
    convert hA.mul hsin using 1
    simp [S, C, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hvec := coord0Embedding.hasFDerivAt.comp t hscalar.hasFDerivAt
  have happly :=
    congrArg (fun L : ℝ →L[ℝ] NSSpace => L (1 : ℝ)) hvec.fderiv
  have hcore :
      timeVelocityDerivative
          (fun t x => coord0Embedding
            (A t * Real.sin (k * (x nsCoord1 - b * t)))) t x =
        coord0Embedding (A' * S - A t * (b * k * C)) := by
    simpa [timeVelocityDerivative, timeFDeriv, S, C,
      ContinuousLinearMap.comp_apply, mul_assoc, mul_left_comm, mul_comm] using happly
  have htdiff :
      DifferentiableAt ℝ
        (fun s : ℝ => coord0Embedding (A s * Real.sin (k * (x nsCoord1 - b * s)))) t := by
    simpa using hvec.differentiableAt
  rw [amplitudeShearTransportVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [hcore, timeVelocityDerivative_constantVelocityField, S, C]
  · exact htdiff
  · dsimp [constantVelocityField]
    exact differentiableAt_const (EuclideanSpace.single nsCoord1 b : NSSpace)

/-- The transported full-drift heat-shear family has the same time derivative
as the transported branch without the additional constant drifts. -/
theorem timeVelocityDerivative_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    timeVelocityDerivative (heatShearTransportFullDriftVelocityField ν a k b d c) t x =
      coord0Embedding
        (-(ν * k ^ (2 : ℕ)) *
            (a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
              Real.sin (k * (x nsCoord1 - b * t))) -
          a * Real.exp (-(ν * k ^ (2 : ℕ)) * t) *
            (b * k * Real.cos (k * (x nsCoord1 - b * t)))) := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [timeVelocityDerivative_add]
  · simp [timeVelocityDerivative_heatShearTransportVelocityField,
      timeVelocityDerivative_constantVelocityField]
  · exact smoothSpaceTimeVelocity_differentiableAt_timeSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x
  · dsimp [constantVelocityField]
    exact differentiableAt_const
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c : NSSpace)

/-- The transported heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearTransportVelocityField
    (ν a k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearTransportVelocityField ν a k b) t x = 0 := by
  rw [spatialDivergence, spatialFDeriv_heatShearTransportVelocityField, Fin.sum_univ_three]
  simp [coord0Embedding_apply, nsCoord0, nsCoord1]

/-- Transported arbitrary-amplitude shear is divergence free on each time
slice. -/
theorem spatialDivergence_amplitudeShearTransportVelocityField
    (A : NSTime → ℝ) (k b : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (amplitudeShearTransportVelocityField A k b) t x = 0 := by
  have hslice :
      ∀ y : NSSpace,
        amplitudeShearTransportVelocityField A k b t y =
          heatShearTransportVelocityField 0 (A t) k b t y := by
    intro y
    simp [amplitudeShearTransportVelocityField, heatShearTransportVelocityField,
      heatShearTransportScalar, constantVelocityField]
  rw [spatialDivergence_congr_at hslice]
  simpa using spatialDivergence_heatShearTransportVelocityField 0 (A t) k b t x

/-- The transported heat-shear initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearTransportInitialVelocity
    (a k b : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearTransportInitialVelocity a k b) x = 0 := by
  rw [heatShearTransportInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearInitialVelocity a k).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord1 b)).contDiffAt (x := x)).differentiableAt (by simp)

/-- The transported full-drift heat-shear field is divergence free. -/
theorem spatialDivergence_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) (t : NSTime) (x : NSSpace) :
    spatialDivergence (heatShearTransportFullDriftVelocityField ν a k b d c) t x = 0 := by
  rw [heatShearTransportFullDriftVelocityField]
  rw [spatialDivergence_add
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_heatShearTransportVelocityField ν a k b) t x)
    (smoothSpaceTimeVelocity_differentiableAt_spatialSlice
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)) t x)]
  simp [spatialDivergence_heatShearTransportVelocityField,
    spatialDivergence_constantVelocityField]

/-- The transported full-drift heat-shear initial datum is divergence free. -/
theorem initialSpatialDivergence_heatShearTransportFullDriftInitialVelocity
    (a k b d c : ℝ) (x : NSSpace) :
    initialSpatialDivergence (heatShearTransportFullDriftInitialVelocity a k b d c) x = 0 := by
  rw [heatShearTransportFullDriftInitialVelocity]
  rw [initialSpatialDivergence_add]
  · simp [initialSpatialDivergence_heatShearTransportInitialVelocity,
      initialSpatialDivergence_constantInitialVelocity]
  · exact ((smoothInitialVelocityData_heatShearTransportInitialVelocity a k b).contDiffAt
      (x := x)).differentiableAt (by simp)
  · exact ((smoothInitialVelocityData_constantInitialVelocity
      (EuclideanSpace.single nsCoord0 d + EuclideanSpace.single nsCoord2 c)).contDiffAt
        (x := x)).differentiableAt (by simp)

/-- The transported heat-shear field matches its declared initial data at time
`0`. -/
theorem matchesInitialVelocity_heatShearTransportVelocityField
    (ν a k b : ℝ) :
    MatchesInitialVelocity
      (heatShearTransportInitialVelocity a k b)
      (heatShearTransportVelocityField ν a k b) := by
  intro x
  simp [heatShearTransportVelocityField, heatShearTransportInitialVelocity,
    heatShearTransportScalar, heatShearInitialVelocity, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord1, mul_assoc]

/-- The transported full-drift heat-shear field matches its declared initial
data at time `0`. -/
theorem matchesInitialVelocity_heatShearTransportFullDriftVelocityField
    (ν a k b d c : ℝ) :
    MatchesInitialVelocity
      (heatShearTransportFullDriftInitialVelocity a k b d c)
      (heatShearTransportFullDriftVelocityField ν a k b d c) := by
  intro x
  simp [heatShearTransportFullDriftVelocityField, heatShearTransportFullDriftInitialVelocity,
    heatShearTransportVelocityField, heatShearTransportInitialVelocity,
    heatShearTransportScalar, heatShearInitialVelocity, heatShearInitialScalar,
    constantVelocityField, constantInitialVelocity, nsCoord1, mul_assoc]

end VectorCalculusR3

end NavierStokes
end FluidDynamics
end Mettapedia

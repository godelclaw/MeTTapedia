import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMZeroOutput
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityRegularityTransfers
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityTargetZeroOutputTransfers

/-!
# Zero-data, affine-pressure, and finite-energy repair regression checks.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace ContinuationRegression

theorem zero_data_finiteInitialKineticEnergy_regression :
    finiteInitialKineticEnergy (0 : NSInitialVelocity) := by
  exact finiteInitialKineticEnergy_zero

theorem zero_data_repaired_regularity_regression
    {ν : ℝ} :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν

theorem zero_data_unrepaired_regularity_constantPressure_regression
    {ν : ℝ} (c : ℝ) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesRegularityClause_zero_constantPressure (ν := ν) c

theorem zero_data_unrepaired_regularity_timeOnlyPressure_regression
    {ν : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitConcreteNavierStokesRegularityClause_zero_timeOnlyPressure (ν := ν) π hπ

theorem zero_data_repaired_regularity_constantPressure_regression
    {ν : ℝ} (c : ℝ) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_constantPressure (ν := ν) c

theorem zero_data_repaired_regularity_timeOnlyPressure_regression
    {ν : ℝ} (π : NSTime → ℝ) (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_timeOnlyPressure
      (ν := ν) π hπ

theorem concrete_clause_zero_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  exact concreteNavierStokesGlobalRegularityClause_zero hν

theorem repaired_concrete_clause_zero_regression
    {ν : ℝ} (hν : 0 < ν) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  exact finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero hν

theorem concrete_clause_zero_add_zeroGradient_affinePressure_regression
    {ν : ℝ} (hν : 0 < ν)
    (a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      { viscosity := ν
        viscosity_pos := hν
        initialVelocity := (0 : NSInitialVelocity)
        smooth_initial := smoothInitialVelocityData_zero
        divergence_free_initial := by
          intro x
          simpa using (initialSpatialDivergence_zero x) } := by
  have hq_zero :
      ∀ t x,
        spatialPressureGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
    intro t x
    have hc :
        DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSTime => fun _ : NSSpace => c) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_const c) t x
    have hπx :
        DifferentiableAt ℝ (fun y : NSSpace => (fun s : NSTime => fun _ : NSSpace => π s) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_timeOnly hπ) t x
    rw [spatialPressureGradient_linearCombination
      (p := fun _ : NSTime => fun _ : NSSpace => c)
      (q := fun s : NSTime => fun _ : NSSpace => π s) a b hc hπx]
    rw [spatialPressureGradient_const, spatialPressureGradient_timeOnly]
    simp
  exact
    concreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
      hν
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      hq_zero

theorem repaired_concrete_clause_zero_add_zeroGradient_affinePressure_regression
    {ν : ℝ} (hν : 0 < ν)
    (a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    NavierStokesGlobalRegularityClause
      mkFullyConcreteNavierStokesSurface
      ({ viscosity := ν
         viscosity_pos := hν
         initialVelocity := (0 : NSInitialVelocity)
         smooth_initial := smoothInitialVelocityData_zero
         divergence_free_initial := by
           intro x
           simpa using (initialSpatialDivergence_zero x)
         finite_initial_energy := finiteInitialKineticEnergy_zero } :
        FiniteEnergyAdmissibleNavierStokesProblemData).toNavierStokesProblemData := by
  have hq_zero :
      ∀ t x,
        spatialPressureGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun s : NSTime => fun _ : NSSpace => π s)) t x = 0 := by
    intro t x
    have hc :
        DifferentiableAt ℝ (fun y : NSSpace => (fun _ : NSTime => fun _ : NSSpace => c) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_const c) t x
    have hπx :
        DifferentiableAt ℝ (fun y : NSSpace => (fun s : NSTime => fun _ : NSSpace => π s) t y) x :=
      smoothSpaceTimePressure_differentiableAt_spatialSlice
        (smoothSpaceTimePressure_timeOnly hπ) t x
    rw [spatialPressureGradient_linearCombination
      (p := fun _ : NSTime => fun _ : NSSpace => c)
      (q := fun s : NSTime => fun _ : NSSpace => π s) a b hc hπx]
    rw [spatialPressureGradient_const, spatialPressureGradient_timeOnly]
    simp
  exact
    finiteEnergyConcreteNavierStokesGlobalRegularityClause_zero_addPressureOfZeroSpatialGradient
      hν
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      hq_zero

theorem zero_data_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitUniformVorticityContinuationClause_zero ν T

theorem zero_data_uniform_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

theorem zero_data_uniform_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitUniformVorticityContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesRegularityClause_zero ν)) T

theorem zero_data_repaired_uniform_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_zero ν T

theorem zero_data_repaired_uniform_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

theorem zero_data_repaired_uniform_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyUniformVorticityContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)) T

theorem zero_data_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitBKMContinuationClause_zero ν T

theorem zero_data_BKM_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause
      (T := T) (ExplicitConcreteNavierStokesRegularityClause_zero ν)

theorem zero_data_BKM_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitConcreteNavierStokesRegularityClause_implies_ExplicitBKMContinuationClause_allHorizons
      (ExplicitConcreteNavierStokesRegularityClause_zero ν)) T

theorem zero_data_repaired_BKM_clause_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact ExplicitFiniteEnergyBKMContinuationClause_zero ν T

theorem zero_data_repaired_BKM_clause_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause
      (T := T) (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)

theorem zero_data_repaired_BKM_allHorizons_from_explicit_regularity_regression
    {ν T : ℝ} :
    ExplicitFiniteEnergyBKMContinuationClause ν (0 : NSInitialVelocity) T := by
  exact
    (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_implies_ExplicitFiniteEnergyBKMContinuationClause_allHorizons
      (ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero ν)) T

theorem smooth_velocity_linearCombination_regression
    (a b c : ℝ) :
    smoothSpaceTimeVelocity
      (a • constantVelocityField (EuclideanSpace.single nsCoord0 c) +
        b • linearShearVelocityField 1) := by
  exact
    smoothSpaceTimeVelocity_linearCombination a b
      (smoothSpaceTimeVelocity_constantVelocityField
        (EuclideanSpace.single nsCoord0 c))
      (smoothSpaceTimeVelocity_linearShearVelocityField 1)

theorem zero_globalOutput_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    (ExplicitConcreteNavierStokesGlobalOutput_zero ν).addPressureOfZeroSpatialGradient
      q hq hq_zero

theorem zero_witness_uniformBound_add_zeroGradient_affinePressure_regression
    (ν T a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ B : ℝ,
      uniformVorticityBoundUpTo
        ((zeroFiniteTimeRegularityWitness ν T).addPressureOfZeroSpatialGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun t : NSTime => fun _ : NSSpace => π t))
          (smoothSpaceTimePressure_linearCombination a b
            (smoothSpaceTimePressure_const c)
            (smoothSpaceTimePressure_timeOnly hπ))
          (spatialPressureGradient_affineConstantTimeOnly a b c π)).velocity
        T B := by
  refine ⟨0, ?_⟩
  have hω :
      uniformVorticityBoundUpTo (zeroFiniteTimeRegularityWitness ν T).velocity T 0 := by
    simpa [zeroFiniteTimeRegularityWitness] using uniformVorticityBoundUpTo_zero T
  exact
    (zeroFiniteTimeRegularityWitness ν T).uniformVorticityBound_addPressureOfZeroSpatialGradient
      hω
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      (spatialPressureGradient_affineConstantTimeOnly a b c π)

theorem zero_witness_BKMEnvelope_add_zeroGradient_affinePressure_regression
    (ν T a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ∃ Ω : NSTime → ℝ, ∃ B : ℝ,
      vorticityEnvelopeOn
        ((zeroFiniteTimeRegularityWitness ν T).addPressureOfZeroSpatialGradient
          (a • (fun _ : NSTime => fun _ : NSSpace => c) +
            b • (fun t : NSTime => fun _ : NSSpace => π t))
          (smoothSpaceTimePressure_linearCombination a b
            (smoothSpaceTimePressure_const c)
            (smoothSpaceTimePressure_timeOnly hπ))
          (spatialPressureGradient_affineConstantTimeOnly a b c π)).velocity
        T Ω ∧
      integrableVorticityEnvelopeOn Ω T B := by
  exact
    (zeroFiniteTimeRegularityWitness ν T).BKMEnvelope_addPressureOfZeroSpatialGradient
      (zeroFiniteTimeRegularityWitness_has_BKMEnvelope ν T)
      (a • (fun _ : NSTime => fun _ : NSSpace => c) +
        b • (fun t : NSTime => fun _ : NSSpace => π t))
      (smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ))
      (spatialPressureGradient_affineConstantTimeOnly a b c π)

theorem zero_uniform_clause_add_zeroGradient_affinePressure_regression
    (ν Tsmall Tlarge a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (hClause := ExplicitUniformVorticityContinuationClause_zero ν Tsmall)
      hν q hq hq_zero hT

theorem zero_repaired_BKM_clause_add_zeroGradient_affinePressure_regression
    (ν Tsmall Tlarge a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyBKMContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (hClause := ExplicitFiniteEnergyBKMContinuationClause_zero ν Tsmall)
      hν q hq hq_zero hT

theorem explicit_target_zero_add_zeroGradient_affinePressure_regression
    (h : ExplicitConcreteNavierStokesMillenniumTarget)
    (ν a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitConcreteNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν q hq hq_zero

theorem repaired_target_zero_add_zeroGradient_affinePressure_regression
    (h : ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget)
    (ν a b c : ℝ)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesMillenniumTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      h hν q hq hq_zero

theorem zero_unrepaired_regularity_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitConcreteNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitConcreteNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν q hq hq_zero

theorem zero_repaired_regularity_add_zeroGradient_affinePressure_regression
    (ν a b c : ℝ)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν (0 : NSInitialVelocity) := by
  let q : NSPressureField :=
    a • (fun _ : NSTime => fun _ : NSSpace => c) +
      b • (fun t : NSTime => fun _ : NSSpace => π t)
  have hq : smoothSpaceTimePressure q := by
    dsimp [q]
    exact
      smoothSpaceTimePressure_linearCombination a b
        (smoothSpaceTimePressure_const c)
        (smoothSpaceTimePressure_timeOnly hπ)
  have hq_zero : ∀ t x, spatialPressureGradient q t x = 0 := by
    intro t x
    dsimp [q]
    exact spatialPressureGradient_affineConstantTimeOnly a b c π t x
  exact
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_zero_addPressureOfZeroSpatialGradient
      ν q hq hq_zero

theorem explicit_regularity_implies_finiteEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (h : ExplicitConcreteNavierStokesRegularityClause ν u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ := by
  exact ExplicitConcreteNavierStokesRegularityClause_implies_finiteEnergy h

theorem repaired_regularity_iff_of_finiteInitialKineticEnergy_regression
    {ν : ℝ} {u₀ : NSInitialVelocity}
    (hfinite : finiteInitialKineticEnergy u₀) :
    ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause ν u₀ ↔
      ExplicitConcreteNavierStokesRegularityClause ν u₀ := by
  exact ExplicitFiniteEnergyAdmissibleNavierStokesRegularityClause_iff_of_finiteInitialKineticEnergy hfinite

end ContinuationRegression
end NavierStokes
end FluidDynamics
end Mettapedia

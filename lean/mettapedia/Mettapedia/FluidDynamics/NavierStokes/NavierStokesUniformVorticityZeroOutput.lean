import Mettapedia.FluidDynamics.NavierStokes.NavierStokesUniformVorticityZeroPressureGaugeWitnesses

/-!
# Uniform-vorticity zero-output consequences

Operational zero-data consequences for unrepaired and finite-energy
uniform-vorticity continuation clauses, plus the regression refuting the
unrepaired negative-horizon target shape.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section UniformVorticityContinuation

/-- The unrepaired uniform-vorticity continuation clause is directly
inhabitable at zero initial data: any finite-time witness on the zero datum may
be discarded in favor of the explicit global zero solution. -/
theorem ExplicitUniformVorticityContinuationClause_zero
    (ν T : ℝ) :
    ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  intro _hν _hsmooth _hdiv _W _hω
  exact ExplicitConcreteNavierStokesGlobalOutput_zero ν

/-- The repaired finite-energy uniform-vorticity continuation clause is
likewise directly inhabitable at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_zero
    (ν T : ℝ) :
    ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T := by
  intro _hν _hsmooth _hdiv _hfinite _W _hω
  exact ExplicitConcreteNavierStokesGlobalOutput_zero ν

/-- Clause-level operational consequence at zero initial data: applying one
uniform-vorticity continuation clause instance to the canonical zero slab
witness yields an explicit global output. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise ν T with
    ⟨W, hω⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 W hω

/-- Nontrivial operational pressure-gauge sanity check: a smaller-slab uniform
continuation clause can be applied to a larger zero witness after adding any
smooth time-only pressure gauge and restricting back down. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hω :
      ∃ B : ℝ,
        uniformVorticityBoundUpTo
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall B :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hω

/-- Time-only special case of the zero-data uniform clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the uniform clause-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- Operational consequence of the uniform-vorticity target: for positive
viscosity, applying the target to the canonical zero slab witness yields a
global explicit output for zero initial data. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T :=
    hTarget ν (0 : NSInitialVelocity) T
  exact ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level operational pressure-gauge sanity check on the unrepaired
uniform-vorticity layer: the target applies on any smaller zero slab after
adding a smooth time-only pressure gauge on a larger zero witness and
restricting back down. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause : ExplicitUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall :=
    hTarget ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the zero-data uniform target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hTarget hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the uniform target-level pressure-gauge
sanity check at zero initial data. -/
theorem ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hTarget : ExplicitUniformVorticityContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hTarget hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- If the horizon is negative, the slab conditions `0 ≤ t ≤ T` are empty, so
steady linear shear itself furnishes a formal finite-time witness. This
exposes the missing `0 ≤ T` hypothesis in the unrepaired continuation target.
-/
def explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
    {ν T a : ℝ}
    (hT : T < 0) :
    ExplicitFiniteTimeRegularityWitness ν (linearShearInitialVelocity a) T where
  velocity := linearShearVelocityField a
  pressure := 0
  smooth_velocity := smoothSpaceTimeVelocity_linearShearVelocityField a
  smooth_pressure := by
    simpa [smoothSpaceTimePressure, spaceTimePressureMap] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : NSSpacetime => (0 : ℝ)))
  momentum_equation_on := by
    intro t x ht0 htT'
    exfalso
    linarith
  incompressible_on := by
    intro t x ht0 htT'
    exfalso
    linarith
  initial_condition := matchesInitialVelocity_linearShearVelocityField a
  bounded_energy_on := by
    refine ⟨0, le_rfl, ?_⟩
    intro t ht0 htT'
    exfalso
    linarith

/-- The unrepaired uniform-vorticity continuation target is false as stated.
For a negative horizon, nonzero linear shear admits a formal finite-time witness
with uniform vorticity bound, while the required global bounded-energy output is
already impossible on `ℝ^3`. -/
theorem not_ExplicitUniformVorticityContinuationTarget :
    ¬ ExplicitUniformVorticityContinuationTarget := by
  intro hTarget
  have hν : 0 < (1 : ℝ) := by positivity
  have hdiv :
      ∀ x, initialSpatialDivergence (linearShearInitialVelocity 1) x = 0 := by
    intro x
    simpa using initialSpatialDivergence_linearShearInitialVelocity 1 x
  let W : ExplicitFiniteTimeRegularityWitness 1 (linearShearInitialVelocity 1) (-1) :=
    explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero
      (ν := 1) (T := -1) (a := 1) (by norm_num)
  have hω : ∃ B : ℝ, uniformVorticityBoundUpTo W.velocity (-1) B := by
    refine ⟨1, ?_⟩
    simpa [W, explicitFiniteTimeRegularityWitness_linearShearInitialVelocity_of_lt_zero] using
      (uniformVorticityBoundUpTo_linearShearVelocityField (a := (1 : ℝ)) (-1))
  exact
    not_ExplicitConcreteNavierStokesGlobalOutput_linearShearInitialVelocity one_ne_zero
      (hTarget 1 (linearShearInitialVelocity 1) (-1)
        hν
        (smoothInitialVelocityData_linearShearInitialVelocity 1)
        hdiv W hω)

/-- Clause-level operational consequence for the repaired finite-energy
uniform-vorticity layer: zero initial data satisfy the repaired input
hypothesis directly, so a repaired clause instance can be applied to the
canonical zero slab witness without vacuity. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  rcases zeroFiniteTimeRegularityWitness_exhibits_uniformContinuationPremise ν T with
    ⟨W, hω⟩
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero W hω

/-- Nontrivial operational pressure-gauge sanity check on the repaired
finite-energy uniform-vorticity layer: a smaller-slab repaired clause can be
applied to a larger zero witness after adding any smooth time-only pressure
gauge and restricting back down. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hdiv0 : ∀ x, initialSpatialDivergence (0 : NSInitialVelocity) x = 0 := by
    intro x
    simpa using (initialSpatialDivergence_zero x)
  have hω :
      ∃ B : ℝ,
        uniformVorticityBoundUpTo
          (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT).velocity
          Tsmall B :=
    zeroFiniteTimeRegularityWitness_addPressureOfZeroSpatialGradient_restrict_has_uniformVorticityBound
      ν Tsmall Tlarge q hq hq_zero hT
  exact hClause hν smoothInitialVelocityData_zero hdiv0 finiteInitialKineticEnergy_zero
    (((zeroFiniteTimeRegularityWitness ν Tlarge).addPressureOfZeroSpatialGradient q hq hq_zero).restrict hT) hω

/-- Time-only special case of the repaired zero-data uniform clause-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_timeOnlyPressure
    {ν Tsmall Tlarge : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) Tsmall)
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired uniform clause-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_constantPressure
    {ν T : ℝ}
    (hClause : ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T)
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hClause hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

/-- The repaired finite-energy uniform-vorticity continuation target is also
operational at zero initial data: the zero datum satisfies the repaired input
hypothesis directly, so the target applies to the canonical zero slab witness
without any vacuity. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ} (hν : 0 < ν) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause :
      ExplicitFiniteEnergyUniformVorticityContinuationClause ν (0 : NSInitialVelocity) T :=
    hTarget ν (0 : NSInitialVelocity) T
  exact ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput hClause hν

/-- Target-level repaired time-gauge sanity check: the repaired finite-energy
uniform-vorticity target applies on any smaller zero slab after adding a smooth
time-only pressure gauge on a larger zero witness and restricting back down. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (q : NSPressureField)
    (hq : smoothSpaceTimePressure q)
    (hq_zero : ∀ t x, spatialPressureGradient q t x = 0)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  have hClause :
      ExplicitFiniteEnergyUniformVorticityContinuationClause
        ν (0 : NSInitialVelocity) Tsmall :=
    hTarget ν (0 : NSInitialVelocity) Tsmall
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationClause_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hClause hν q hq hq_zero hT

/-- Time-only special case of the repaired zero-data uniform target-level
zero-spatial-gradient transport theorem. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_timeOnlyPressure
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν Tsmall Tlarge : ℝ}
    (hν : 0 < ν)
    (π : NSTime → ℝ)
    (hπ : ContDiff ℝ ∞ π)
    (hT : Tsmall ≤ Tlarge) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      hTarget hν
      (fun t : NSTime => fun _ : NSSpace => π t)
      (smoothSpaceTimePressure_timeOnly hπ)
      (fun t x => spatialPressureGradient_timeOnly π t x)
      hT

/-- Constant-pressure special case of the repaired uniform target-level
pressure-gauge sanity check at zero initial data. -/
theorem ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_constantPressure
    (hTarget : ExplicitFiniteEnergyUniformVorticityContinuationTarget)
    {ν T : ℝ}
    (hν : 0 < ν)
    (c : ℝ) :
    ExplicitConcreteNavierStokesGlobalOutput ν (0 : NSInitialVelocity) := by
  exact
    ExplicitFiniteEnergyUniformVorticityContinuationTarget_implies_zeroGlobalOutput_addPressureOfZeroSpatialGradient
      (Tsmall := T) (Tlarge := T) hTarget hν
      (fun _ : NSTime => fun _ : NSSpace => c)
      (smoothSpaceTimePressure_const c)
      (fun t x => spatialPressureGradient_const c t x)
      le_rfl

end UniformVorticityContinuation

end NavierStokes
end FluidDynamics
end Mettapedia

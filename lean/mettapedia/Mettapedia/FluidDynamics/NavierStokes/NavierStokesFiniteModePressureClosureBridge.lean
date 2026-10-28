import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeAffineQuadraticPressureModes

/-!
# Finite-mode pressure residual closure bridge.

This module contains reusable abstract bridges from finite pressure-gradient
range obligations to reconstructed Navier-Stokes momentum equations.
Concrete counterexamples and examples live in downstream modules.
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

/-- A finite-mode Helmholtz pressure closure is exactly a range condition for
the pressure-gradient synthesis map, time slice by time slice. -/
theorem finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈
          range (finiteModePressureGradientSynthesis pressureMode) := by
  constructor
  · rintro ⟨b, hres⟩ t ht
    refine ⟨b t, ?_⟩
    funext x
    have hzero := hres t ht x
    unfold finiteModeReconstructedMomentumResidualZeroAt at hzero
    unfold finiteModeReconstructedMomentumResidual at hzero
    rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
      (fun k => hpressureModeDiff k x)] at hzero
    change
      finiteModePressureGradientSynthesis pressureMode (b t) x =
        (-finiteModeNonPressureMomentumDefect ν mode C a t) x
    have hsum :
        finiteModePressureGradientSynthesis pressureMode (b t) x +
            finiteModeNonPressureMomentumDefect ν mode C a t x =
          0 := by
      simpa [finiteModePressureGradientSynthesis, finiteModeNonPressureMomentumDefect,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
    exact add_eq_zero_iff_eq_neg.mp hsum
  · intro hrange
    classical
    let b : ℝ → FiniteModeState κ :=
      fun t =>
        if ht : t ∈ I then
          Classical.choose (hrange t ht)
        else
          0
    refine ⟨b, ?_⟩
    intro t ht x
    unfold finiteModeReconstructedMomentumResidualZeroAt
    unfold finiteModeReconstructedMomentumResidual
    rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
      (fun k => hpressureModeDiff k x)]
    have hb :
        finiteModePressureGradientSynthesis pressureMode (b t) =
          -finiteModeNonPressureMomentumDefect ν mode C a t := by
      dsimp [b]
      simpa [ht] using Classical.choose_spec (hrange t ht)
    have hbx := congrFun hb x
    have hsum :
        finiteModePressureGradientSynthesis pressureMode (b t) x +
            finiteModeNonPressureMomentumDefect ν mode C a t x =
          0 := by
      rw [hbx]
      simp
    simpa [finiteModePressureGradientSynthesis, finiteModeNonPressureMomentumDefect,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- A finite pressure-primitive basis turns the Helmholtz range condition into
plain membership in the corresponding gradient subspace. -/
theorem finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    (∃ b : ℝ → FiniteModeState κ,
        finiteModeReconstructedMomentumResidualZeroOn
          I ν mode pressureMode C a b) ↔
      ∀ t ∈ I,
        -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V := by
  rw [finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
    I ν mode pressureMode C a hpressureModeDiff]
  constructor
  · intro hrange t ht
    change -finiteModeNonPressureMomentumDefect ν mode C a t ∈
      (V : Set (NSSpace → NSSpace))
    rw [← finiteModePressureGradientSynthesis_range_eq_submodule
      pressureMode V B hgradientBasis]
    exact hrange t ht
  · intro hV t ht
    rw [finiteModePressureGradientSynthesis_range_eq_submodule
      pressureMode V B hgradientBasis]
    exact hV t ht

/-- If the finite pressure-mode gradients exactly close the reconstructed
non-pressure residual, then the reconstructed pressure ansatz has zero
Navier-Stokes momentum residual on the time set.  This is the pressure closure
obligation in coefficient form. -/
theorem finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hbalance : ∀ t ∈ I, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ k : κ, b t k • gradient (pressureMode k) x) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    finiteModeReconstructedMomentumResidualZeroOn I ν mode pressureMode C a b := by
  intro t ht x
  unfold finiteModeReconstructedMomentumResidualZeroAt
  unfold finiteModeReconstructedMomentumResidual
  rw [finiteModeReconstructedPressure_spatialPressureGradient pressureMode b t x
    (fun k => hpressureModeDiff k x)]
  exact sub_eq_zero.mpr (hbalance t ht x)

/-- A coefficient derivative reconstructs pointwise into the time derivative of
the spatial finite-mode velocity field. -/
theorem finiteModeReconstructedVelocity_timeDerivative_at
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x =
      finiteModeReconstructedAcceleration mode C a t x := by
  unfold timeVelocityDerivative timeFDeriv
  have hDeriv :
      HasDerivAt
        (fun s : NSTime => finiteModeReconstructionCLM mode x (a s))
        (finiteModeReconstructionCLM mode x (finiteModeProjectedNSRHS C (a t))) t := by
    exact
      HasFDerivAt.comp_hasDerivAt
        (l := fun b : FiniteModeState ι => finiteModeReconstructionCLM mode x b)
        (l' := finiteModeReconstructionCLM mode x)
        (f := a)
        (x := t)
        (f' := finiteModeProjectedNSRHS C (a t))
        ((finiteModeReconstructionCLM mode x).hasFDerivAt (x := a t))
        ha
  change
    (fderiv ℝ (fun s : NSTime => finiteModeReconstructionCLM mode x (a s)) t) 1 =
      finiteModeReconstructionCLM mode x (finiteModeProjectedNSRHS C (a t))
  rw [hDeriv.hasFDerivAt.fderiv]
  simp

/-- Pressure/residual reconstruction at one point: once the coefficient curve
solves the finite projected ODE, zero residual is exactly the concrete
Navier-Stokes momentum equation for the reconstructed velocity and pressure. -/
theorem finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (x : NSSpace) :
    finiteModeReconstructedMomentumResidualZeroAt
        ν mode pressureMode C a b t x ↔
      timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            spatialPressureGradient
              (finiteModeReconstructedPressure pressureMode b) t x =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x := by
  constructor
  · intro hres
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x]
    exact sub_eq_zero.mp hres
  · intro hmom
    rw [finiteModeReconstructedVelocity_timeDerivative_at mode C a t ha x] at hmom
    exact sub_eq_zero.mpr hmom

/-- The forward direction of pressure/residual reconstruction at one point. -/
theorem finiteModeReconstructedVelocityPressure_momentumEquation_at_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime)
    (ha : HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      ∀ x : NSSpace,
        finiteModeReconstructedMomentumResidualZeroAt
          ν mode pressureMode C a b t x)
    (x : NSSpace) :
    timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
        spatialConvection (finiteModeReconstructedVelocity mode a) t x +
          spatialPressureGradient
            (finiteModeReconstructedPressure pressureMode b) t x =
      ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x :=
  (finiteModeReconstructedMomentumResidualZeroAt_iff_momentumEquation_at
    ν mode pressureMode C a b t ha x).mp (hres x)

/-- Pressure/residual reconstruction on a time set.  This is the local
finite-dimensional-to-PDE momentum step: no global target or continuation
hypothesis is used, only the coefficient ODE and the explicit residual closure
for the reconstructed pressure ansatz. -/
theorem finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ha : ∀ t ∈ I, HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      finiteModeReconstructedMomentumResidualZeroOn
        I ν mode pressureMode C a b) :
    ∀ t ∈ I, ∀ x : NSSpace,
      timeVelocityDerivative (finiteModeReconstructedVelocity mode a) t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            spatialPressureGradient
              (finiteModeReconstructedPressure pressureMode b) t x =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x := by
  intro t ht x
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_at_of_residual_zero
      ν mode pressureMode C a b t (ha t ht) (hres t ht) x

/-- Given a coefficient solution and a pressure coefficient curve whose
reconstructed residual vanishes on a local time interval, the reconstructed
`u,p` pair satisfies the concrete pointwise momentum equation on that interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hres :
      finiteModeReconstructedMomentumResidualZeroOn
        (Ioo (-ε) ε) ν mode pressureMode C a b) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  refine
    ⟨finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

/-- A coefficient ODE solution plus a finite pressure-mode gradient balance
constructs a concrete velocity-pressure pair satisfying the pointwise momentum
equation on the local interval. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureModeGradient_balance
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hbalance : ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
      finiteModeReconstructedAcceleration mode C a t x +
          spatialConvection (finiteModeReconstructedVelocity mode a) t x +
            (∑ k : κ, b t k • gradient (pressureMode k) x) =
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x) :
    ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  exact
    finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_residual_zero
      ν mode pressureMode C a b ε ha
      (finiteModeReconstructedMomentumResidualZeroOn_of_pressureModeGradient_balance
        (Ioo (-ε) ε) ν mode pressureMode C a b hpressureModeDiff hbalance)

/-- A local coefficient ODE solution plus the finite-dimensional Helmholtz
range condition constructs pressure coefficients and hence a concrete
velocity-pressure pair satisfying the pointwise momentum equation locally. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressureHelmholtzRange
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hrange : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈
        range (finiteModePressureGradientSynthesis pressureMode)) :
    ∃ b : ℝ → FiniteModeState κ, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  rcases
    (finiteModePressureHelmholtzRangeOn_iff_residualZeroOn
      (Ioo (-ε) ε) ν mode pressureMode C a hpressureModeDiff).mpr hrange with
    ⟨b, hres⟩
  refine
    ⟨b, finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, hres, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

/-- Local finite-mode momentum reconstruction from a finite-dimensional
pressure-primitive basis.  The remaining Helmholtz obligation is now the
mathematically sharp statement that each non-pressure defect slice lies in the
chosen gradient subspace; pressure coefficients are synthesized from the basis
coordinates. -/
theorem finiteModeProjectedNS_local_reconstructed_velocityPressure_momentum_of_pressurePrimitiveBasis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (ε : ℝ)
    (ha : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt a (finiteModeProjectedNSRHS C (a t)) t)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hpressureModeDiff : ∀ k x, DifferentiableAt ℝ (pressureMode k) x)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (hdefectV : ∀ t ∈ Ioo (-ε) ε,
      -finiteModeNonPressureMomentumDefect ν mode C a t ∈ V) :
    ∃ b : ℝ → FiniteModeState κ, ∃ u : NSVelocityField, ∃ p : NSPressureField,
      u = finiteModeReconstructedVelocity mode a ∧
        p = finiteModeReconstructedPressure pressureMode b ∧
          finiteModeReconstructedMomentumResidualZeroOn
            (Ioo (-ε) ε) ν mode pressureMode C a b ∧
          ∀ t ∈ Ioo (-ε) ε, ∀ x : NSSpace,
            timeVelocityDerivative u t x +
                spatialConvection u t x +
                  spatialPressureGradient p t x =
              ν • spatialLaplacian u t x := by
  rcases
    (finiteModePressurePrimitiveBasisOn_iff_residualZeroOn
      (Ioo (-ε) ε) ν mode pressureMode C a V B
      hpressureModeDiff hgradientBasis).mpr hdefectV with
    ⟨b, hres⟩
  refine
    ⟨b, finiteModeReconstructedVelocity mode a,
      finiteModeReconstructedPressure pressureMode b, rfl, rfl, hres, ?_⟩
  exact
    finiteModeReconstructedVelocityPressure_momentumEquation_on_of_residual_zero
      (Ioo (-ε) ε) ν mode pressureMode C a b ha hres

end NavierStokes
end FluidDynamics
end Mettapedia

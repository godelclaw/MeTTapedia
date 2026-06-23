import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModeGalerkinToy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationCore
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKits
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationProblemData
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationFiniteEnergy
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationComponentBridge
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationEquivalences
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEquationKitIff
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3LocalOperators
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Smoothness
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3FirstOrder
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3PressureObstructions
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Laplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Momentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Vorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportProfiles
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportDerivatives
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportLaplacian
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportMomentum
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3TransportVorticity
import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3VorticityNorms
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Finite-mode reconstruction core: velocity, pressure, residual predicates, pressure-gradient synthesis, and coordinate/diagonal pressure modes.
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

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- The continuous linear map sending a vector of mode coefficients to the
spatial finite-mode sum at a fixed point `x`. -/
def finiteModeReconstructionCLM
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (x : NSSpace) :
    FiniteModeState ι →L[ℝ] NSSpace :=
  ∑ i : ι, (ContinuousLinearMap.proj i).smulRight (mode i x)

@[simp]
theorem finiteModeReconstructionCLM_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (x : NSSpace)
    (a : FiniteModeState ι) :
    finiteModeReconstructionCLM mode x a =
      ∑ i : ι, a i • mode i x := by
  simp [finiteModeReconstructionCLM]

/-- Reconstruct a concrete velocity field from mode coefficients. -/
def finiteModeReconstructedVelocity
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  fun t x => finiteModeReconstructionCLM mode x (a t)

@[simp]
theorem finiteModeReconstructedVelocity_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity mode a t x =
      ∑ i : ι, a t i • mode i x := by
  simp [finiteModeReconstructedVelocity]

/-- The reconstructed initial velocity associated to a coefficient vector. -/
def finiteModeReconstructedInitialVelocity
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a₀ : FiniteModeState ι) :
    NSInitialVelocity :=
  fun x => finiteModeReconstructionCLM mode x a₀

@[simp]
theorem finiteModeReconstructedInitialVelocity_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a₀ : FiniteModeState ι)
    (x : NSSpace) :
    finiteModeReconstructedInitialVelocity mode a₀ x =
      ∑ i : ι, a₀ i • mode i x := by
  simp [finiteModeReconstructedInitialVelocity]

/-- Reconstruct the projected acceleration field from the coefficient RHS. -/
def finiteModeReconstructedAcceleration
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  finiteModeReconstructedVelocity mode (fun t => finiteModeProjectedNSRHS C (a t))

@[simp]
theorem finiteModeReconstructedAcceleration_apply
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedAcceleration mode C a t x =
      ∑ i : ι, finiteModeProjectedNSRHS C (a t) i • mode i x := by
  simp [finiteModeReconstructedAcceleration]

/-- Reconstruct a concrete pressure field from finite pressure-mode
coefficients. -/
def finiteModeReconstructedPressure
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ) :
    NSPressureField :=
  fun t x => ∑ k : κ, b t k * pressureMode k x

@[simp]
theorem finiteModeReconstructedPressure_apply
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedPressure pressureMode b t x =
      ∑ k : κ, b t k * pressureMode k x := by
  rfl

/-- The spatial pressure gradient of the reconstructed pressure is the finite
sum of modal pressure gradients weighted by the current pressure coefficients. -/
theorem finiteModeReconstructedPressure_spatialPressureGradient
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace)
    (hmode : ∀ k, DifferentiableAt ℝ (pressureMode k) x) :
    spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x =
      ∑ k : κ, b t k • gradient (pressureMode k) x := by
  unfold spatialPressureGradient gradient
  have hdiff :
      ∀ k ∈ (Finset.univ : Finset κ),
        DifferentiableAt ℝ (fun y : NSSpace => b t k * pressureMode k y) x := by
    intro k _hk
    simpa [smul_eq_mul] using (hmode k).const_smul (b t k)
  have hfderiv :
      fderiv ℝ (fun y : NSSpace => finiteModeReconstructedPressure pressureMode b t y) x =
        ∑ k : κ, fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x := by
    simpa [finiteModeReconstructedPressure] using fderiv_fun_sum hdiff
  rw [hfderiv]
  calc
    (InnerProductSpace.toDual ℝ NSSpace).symm
        (∑ k : κ, fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x) =
      ∑ k : κ,
        (InnerProductSpace.toDual ℝ NSSpace).symm
          (fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x) := by
        simp
    _ =
      ∑ k : κ, b t k •
        (InnerProductSpace.toDual ℝ NSSpace).symm
          (fderiv ℝ (pressureMode k) x) := by
        apply Finset.sum_congr rfl
        intro k _hk
        have hf :
            fderiv ℝ (fun y : NSSpace => b t k * pressureMode k y) x =
              b t k • fderiv ℝ (pressureMode k) x := by
          simpa [smul_eq_mul] using
            fderiv_fun_const_smul (hmode k) (b t k)
        rw [hf]
        simp

/-- Smooth coefficient curves and smooth spatial modes reconstruct to a smooth
space-time velocity field. -/
theorem finiteModeReconstructedVelocity_smoothSpaceTime
    {ι : Type*} [Fintype ι]
    (mode : ι → NSSpace → NSSpace) (a : ℝ → FiniteModeState ι)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t : NSTime => a t i))
    (hmode : ∀ i, ContDiff ℝ ∞ (mode i)) :
    smoothSpaceTimeVelocity (finiteModeReconstructedVelocity mode a) := by
  unfold smoothSpaceTimeVelocity spaceTimeVelocityMap
  unfold finiteModeReconstructedVelocity finiteModeReconstructionCLM
  simpa using
    (ContDiff.sum (s := (Finset.univ : Finset ι))
      (fun i _hi =>
        ((ha i).comp (contDiff_fst : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.1))).smul
          ((hmode i).comp
            (contDiff_snd : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2)))))

/-- Smooth pressure coefficient curves and smooth pressure modes reconstruct to
a smooth space-time pressure field. -/
theorem finiteModeReconstructedPressure_smoothSpaceTime
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) (b : ℝ → FiniteModeState κ)
    (hb : ∀ k, ContDiff ℝ ∞ (fun t : NSTime => b t k))
    (hmode : ∀ k, ContDiff ℝ ∞ (pressureMode k)) :
    smoothSpaceTimePressure (finiteModeReconstructedPressure pressureMode b) := by
  unfold smoothSpaceTimePressure spaceTimePressureMap finiteModeReconstructedPressure
  simpa using
    (ContDiff.sum (s := (Finset.univ : Finset κ))
      (fun k _hk =>
        ((hb k).comp (contDiff_fst : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.1))).mul
          ((hmode k).comp
            (contDiff_snd : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2)))))

/-- Coordinate-linear pressure modes on `ℝ^3`: the `j`th mode is
`x ↦ x_j`. -/
def finiteModeCoordinatePressureMode (j : Fin 3) : NSSpace → ℝ :=
  fun x => x j

/-- Coordinate-linear pressure modes are smooth. -/
theorem finiteModeCoordinatePressureMode_contDiff
    (j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeCoordinatePressureMode j) := by
  change ContDiff ℝ ∞
    (fun y : NSSpace => (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) y)
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff

/-- The coordinate-linear pressure modes are differentiable. -/
theorem finiteModeCoordinatePressureMode_differentiableAt
    (j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeCoordinatePressureMode j) x := by
  change
    DifferentiableAt ℝ
      (fun y : NSSpace => (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) y) x
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).differentiable.differentiableAt

/-- The gradient of the `j`th coordinate pressure mode is the `j`th coordinate
unit vector. -/
theorem finiteModeCoordinatePressureMode_gradient
    (j : Fin 3) (x : NSSpace) :
    gradient (finiteModeCoordinatePressureMode j) x =
      EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeCoordinatePressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (EuclideanSpace.single j (1 : ℝ)) =
        (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_left]
  rw [hdual]
  exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt

/-- The standard coordinate pressure gradients reconstruct any vector in
`ℝ^3`. -/
theorem finiteModeCoordinatePressureMode_gradient_sum
    (c : NSSpace) :
    (∑ j : Fin 3, c j • EuclideanSpace.single j (1 : ℝ)) = c := by
  ext j
  simp [Pi.single_apply]

/-- Coordinate pressure coefficients for a prescribed time-dependent constant
pressure gradient. -/
def finiteModeCoordinatePressureCoefficients
    (c : NSTime → NSSpace) : NSTime → FiniteModeState (Fin 3) :=
  fun t j => c t j

/-- The finite coordinate pressure ansatz has spatial gradient exactly `c(t)`. -/
theorem finiteModeCoordinatePressure_spatialPressureGradient
    (c : NSTime → NSSpace) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      c t := by
  calc
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeCoordinatePressureMode
          (finiteModeCoordinatePressureCoefficients c)) t x =
      ∑ j : Fin 3,
        finiteModeCoordinatePressureCoefficients c t j •
          gradient (finiteModeCoordinatePressureMode j) x := by
        rw [finiteModeReconstructedPressure_spatialPressureGradient]
        intro j
        exact finiteModeCoordinatePressureMode_differentiableAt j x
    _ = ∑ j : Fin 3, c t j • EuclideanSpace.single j (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [finiteModeCoordinatePressureMode_gradient]
        rfl
    _ = c t := finiteModeCoordinatePressureMode_gradient_sum (c t)

/-- Diagonal quadratic pressure modes on `ℝ^3`: the `j`th mode is
`x ↦ (1 / 2) * x_j^2`. Their gradients are nonconstant, linear-in-space
coordinate vector fields. -/
def finiteModeDiagonalQuadraticPressureMode (j : Fin 3) : NSSpace → ℝ :=
  fun x => (1 / 2 : ℝ) * (x j) ^ (2 : ℕ)

/-- Diagonal quadratic pressure modes are smooth. -/
theorem finiteModeDiagonalQuadraticPressureMode_contDiff
    (j : Fin 3) :
    ContDiff ℝ ∞ (finiteModeDiagonalQuadraticPressureMode j) := by
  unfold finiteModeDiagonalQuadraticPressureMode
  have hcoord : ContDiff ℝ ∞ (fun x : NSSpace => x j) := by
    simpa using (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).contDiff
  simpa using (contDiff_const.mul (hcoord.pow 2))

/-- The diagonal quadratic pressure modes are differentiable. -/
theorem finiteModeDiagonalQuadraticPressureMode_differentiableAt
    (j : Fin 3) (x : NSSpace) :
    DifferentiableAt ℝ (finiteModeDiagonalQuadraticPressureMode j) x := by
  unfold finiteModeDiagonalQuadraticPressureMode
  have hproj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hpow : HasFDerivAt (fun y : NSSpace => (y j) ^ (2 : ℕ))
      (((2 : ℝ) * x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)) x := by
    simpa using hproj.pow 2
  exact (hpow.const_mul (1 / 2 : ℝ)).differentiableAt

/-- The gradient of `x ↦ (1 / 2) * x_j^2` is `x_j e_j`. -/
theorem finiteModeDiagonalQuadraticPressureMode_gradient
    (j : Fin 3) (x : NSSpace) :
    gradient (finiteModeDiagonalQuadraticPressureMode j) x =
      x j • EuclideanSpace.single j (1 : ℝ) := by
  unfold finiteModeDiagonalQuadraticPressureMode gradient
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hdual :
      (InnerProductSpace.toDual ℝ NSSpace) (x j • EuclideanSpace.single j (1 : ℝ)) =
        (x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply]
    rw [inner_smul_left]
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [hdual]
  have hproj : HasFDerivAt (fun y : NSSpace => y j)
      (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ) x := by
    exact (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ).hasFDerivAt
  have hpow : HasFDerivAt (fun y : NSSpace => (y j) ^ (2 : ℕ))
      (((2 : ℝ) * x j) • (EuclideanSpace.proj j : NSSpace →L[ℝ] ℝ)) x := by
    simpa using hproj.pow 2
  have hconst := hpow.const_mul (1 / 2 : ℝ)
  convert hconst using 1
  · ext y
    simp [one_div, smul_smul]

/-- Coefficients for diagonal quadratic pressure modes. -/
def finiteModeDiagonalQuadraticPressureCoefficients
    (d : NSTime → FiniteModeState (Fin 3)) : NSTime → FiniteModeState (Fin 3) :=
  d

/-- The diagonal quadratic pressure ansatz has a nonconstant diagonal linear
spatial gradient. -/
theorem finiteModeDiagonalQuadraticPressure_spatialPressureGradient
    (d : NSTime → FiniteModeState (Fin 3)) (t : NSTime) (x : NSSpace) :
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
  calc
    spatialPressureGradient
        (finiteModeReconstructedPressure finiteModeDiagonalQuadraticPressureMode
          (finiteModeDiagonalQuadraticPressureCoefficients d)) t x =
      ∑ j : Fin 3,
        finiteModeDiagonalQuadraticPressureCoefficients d t j •
          gradient (finiteModeDiagonalQuadraticPressureMode j) x := by
        rw [finiteModeReconstructedPressure_spatialPressureGradient]
        intro j
        exact finiteModeDiagonalQuadraticPressureMode_differentiableAt j x
    _ = ∑ j : Fin 3, d t j • (x j • EuclideanSpace.single j (1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [finiteModeDiagonalQuadraticPressureMode_gradient]
        rfl

/-- The finite-mode momentum residual after reconstructing velocity and
pressure.  Its vanishing is exactly the pressure/residual closure condition
that turns a projected coefficient trajectory into a pointwise momentum
equation for the reconstructed fields. -/
def finiteModeReconstructedMomentumResidual
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ) :
    NSVelocityField :=
  fun t x =>
    finiteModeReconstructedAcceleration mode C a t x +
        spatialConvection (finiteModeReconstructedVelocity mode a) t x +
          spatialPressureGradient (finiteModeReconstructedPressure pressureMode b) t x -
      ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x

/-- Pointwise zero-residual condition for the reconstructed finite-mode
velocity-pressure ansatz. -/
def finiteModeReconstructedMomentumResidualZeroAt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ)
    (t : NSTime) (x : NSSpace) : Prop :=
  finiteModeReconstructedMomentumResidual ν mode pressureMode C a b t x = 0

/-- Zero-residual condition on a time set. -/
def finiteModeReconstructedMomentumResidualZeroOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : Set NSTime)
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (pressureMode : κ → NSSpace → ℝ)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι)
    (b : ℝ → FiniteModeState κ) : Prop :=
  ∀ t ∈ I, ∀ x : NSSpace,
    finiteModeReconstructedMomentumResidualZeroAt
      ν mode pressureMode C a b t x

/-- The non-pressure part of the reconstructed momentum residual. -/
def finiteModeNonPressureMomentumDefect
    {ι : Type*} [Fintype ι]
    (ν : ℝ)
    (mode : ι → NSSpace → NSSpace)
    (C : FiniteModeProjectedNSCoefficients ι)
    (a : ℝ → FiniteModeState ι) :
    NSVelocityField :=
  fun t x =>
    finiteModeReconstructedAcceleration mode C a t x +
      spatialConvection (finiteModeReconstructedVelocity mode a) t x -
        ν • spatialLaplacian (finiteModeReconstructedVelocity mode a) t x

/-- The finite pressure-gradient synthesis map determined by selected pressure
modes. -/
def finiteModePressureGradientSynthesis
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ) :
    FiniteModeState κ → NSSpace → NSSpace :=
  fun b x => ∑ k : κ, b k • gradient (pressureMode k) x

/-- Pointwise coercion of a finite linear combination in a subspace of vector
fields. -/
theorem finiteModeSubmodule_sum_apply
    {κ : Type*} [Fintype κ]
    (V : Submodule ℝ (NSSpace → NSSpace))
    (G : κ → V) (c : κ → ℝ) (x : NSSpace) :
    ((∑ k : κ, c k • G k : V) : NSSpace → NSSpace) x =
      ∑ k : κ, c k • ((G k : V) : NSSpace → NSSpace) x := by
  have hcoe :
      ((∑ k : κ, c k • G k : V) : NSSpace → NSSpace) =
        ∑ k : κ, ((c k • G k : V) : NSSpace → NSSpace) := by
    simp
  rw [hcoe]
  simp [Pi.smul_apply]

/-- If the modal pressure gradients are a basis for a finite-dimensional
subspace `V` of vector fields, the basis coordinates of any `F ∈ V` synthesize
exactly `F` as a pressure gradient. -/
theorem finiteModePressureGradientSynthesis_basis_repr
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (F : V) :
    finiteModePressureGradientSynthesis pressureMode
        (fun k => B.repr F k) =
      (F : NSSpace → NSSpace) := by
  have hsum : (∑ k : κ, (B.repr F k) • B k : V) = F := by
    exact B.sum_repr F
  have hfun :
      ((∑ k : κ, (B.repr F k) • B k : V) : NSSpace → NSSpace) =
        (F : NSSpace → NSSpace) :=
    congrArg (fun G : V => (G : NSSpace → NSSpace)) hsum
  have hgradientBasis_apply :
      ∀ k x, ((B k : V) : NSSpace → NSSpace) x =
        gradient (pressureMode k) x := by
    intro k x
    exact congrFun (hgradientBasis k) x
  funext x
  have hx := congrFun hfun x
  calc
    finiteModePressureGradientSynthesis pressureMode
        (fun k => B.repr F k) x =
      ∑ k : κ, (B.repr F k) • (((B k : V) : NSSpace → NSSpace) x) := by
        simp [finiteModePressureGradientSynthesis, hgradientBasis_apply]
    _ = ((∑ k : κ, (B.repr F k) • B k : V) : NSSpace → NSSpace) x := by
        exact (finiteModeSubmodule_sum_apply V B (fun k => B.repr F k) x).symm
    _ = (F : NSSpace → NSSpace) x := hx

/-- The pressure coefficients obtained from a gradient-subspace basis witness
membership in the pressure-gradient range. -/
theorem finiteModePressureGradientSynthesis_mem_range_of_basis
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x)
    (F : V) :
    (F : NSSpace → NSSpace) ∈
      range (finiteModePressureGradientSynthesis pressureMode) := by
  refine ⟨fun k => B.repr F k, ?_⟩
  exact finiteModePressureGradientSynthesis_basis_repr
    pressureMode V B hgradientBasis F

/-- A finite pressure basis realizes exactly its gradient subspace.  This is
the finite-dimensional Helmholtz algebra behind pressure reconstruction: once
the actual pressure primitives have been provided for a vector-field subspace,
pressure coefficients are just basis coordinates. -/
theorem finiteModePressureGradientSynthesis_range_eq_submodule
    {κ : Type*} [Fintype κ]
    (pressureMode : κ → NSSpace → ℝ)
    (V : Submodule ℝ (NSSpace → NSSpace))
    (B : Module.Basis κ ℝ V)
    (hgradientBasis : ∀ k,
      ((B k : V) : NSSpace → NSSpace) =
        fun x => gradient (pressureMode k) x) :
    range (finiteModePressureGradientSynthesis pressureMode) =
      (V : Set (NSSpace → NSSpace)) := by
  ext F
  constructor
  · rintro ⟨b, rfl⟩
    have hgradientBasis_apply :
        ∀ k x, ((B k : V) : NSSpace → NSSpace) x =
          gradient (pressureMode k) x := by
      intro k x
      exact congrFun (hgradientBasis k) x
    have hcoe :
        ((∑ k : κ, b k • B k : V) : NSSpace → NSSpace) =
          finiteModePressureGradientSynthesis pressureMode b := by
      funext x
      calc
        ((∑ k : κ, b k • B k : V) : NSSpace → NSSpace) x =
          ∑ k : κ, b k • (((B k : V) : NSSpace → NSSpace) x) := by
            exact finiteModeSubmodule_sum_apply V B b x
        _ = finiteModePressureGradientSynthesis pressureMode b x := by
            simp [finiteModePressureGradientSynthesis, hgradientBasis_apply]
    rw [← hcoe]
    exact (∑ k : κ, b k • B k : V).property
  · intro hF
    exact finiteModePressureGradientSynthesis_mem_range_of_basis
      pressureMode V B hgradientBasis ⟨F, hF⟩

end NavierStokes
end FluidDynamics
end Mettapedia

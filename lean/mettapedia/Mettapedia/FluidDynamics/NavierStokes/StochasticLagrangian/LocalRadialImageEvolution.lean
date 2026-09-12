import Mettapedia.Analysis.RadialRieszCoefficientEvolution
import Mettapedia.Analysis.UnitTorusMaterialLifts
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticitySeparation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityRadialPairing

/-!
# Full signed radial image dynamics for the actual local solution

Each Euclidean image is followed using real material lifts and a constant
shift. Kernel transport, common-strain amplitude growth, unequal-gradient
remainders and both viscous endpoints are retained. A fixed image shift
does not move with the common deformation: its velocity remainder includes
the negative gradient applied to that shift.

The identity is local at nonzero image separation. It does not interchange
an infinite image sum, a cutoff limit or a time integral with differentiation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRadialImageEvolution

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories PancakeLocalSpatialVelocity PancakeLocalGradientEquation
open PancakeLocalStrainEquation PancakeMatrixCurlAlgebra PancakeFilteredStrainDynamics
open PancakeLocalProjectedEquation PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakePeriodicComplexStretch PancakeInfiniteFourierDerivative
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open LocalVorticitySeparation
open LocalMeanAlignmentBalance (velocity)
open Mettapedia.Analysis
open EuclideanCrossProduct
open scoped RealInnerProductSpace

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "Lat" => UnitTorusLattice.LatticeSubmodule (ι := Fin 3)

def imageSeparation (z : R3) (x y : X3) : R3 := z + separation x y

def imageVelocityRemainder (z : R3) (u : FourierVelocity) (x y : X3) : R3 :=
  velocity u (torusPoint x) - velocity u (torusPoint y) -
    gradient u (torusPoint x) (imageSeparation z x y)

/-- The constant lattice image is not advected affinely. -/
theorem imageVelocityRemainder_eq (z : R3) (u : FourierVelocity) (x y : X3) :
    imageVelocityRemainder z u x y =
      velocityRemainder u x y - gradient u (torusPoint x) z := by
  simp only [imageVelocityRemainder, velocityRemainder, imageSeparation, map_add]
  abel

def coefficient (N : ℕ) (z : R3) (x y : X3) : ℝ :=
  RadialRieszRegularization.radialCoefficient N (EuclideanSpace.single 0 1) (imageSeparation z x y)

def coefficientRate (N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  RadialRieszRegularization.radialCoefficientSlope N (EuclideanSpace.single 0 1) (imageSeparation z x y) *
    ⟪imageSeparation z x y, velocity u (torusPoint x) - velocity u (torusPoint y)⟫

def sourceDensity (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  SignedRadialStretch.density (2 * (n + 1)) (coefficient N z x y)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)

def kernelTransport (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  coefficientRate N z u x y *
    tripleProduct (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y) *
    SignedRadialStretch.amplitudePair (2 * (n + 1)) (fullVorticity u (torusPoint x))
      (fullVorticity u (torusPoint y)) (imageSeparation z x y)

def commonDeformation (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  coefficient N z x y *
    tripleProduct (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y) *
    SignedRadialStretch.commonAmplitudeRate n (gradient u (torusPoint x))
      (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)

def nonviscousImageRate (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  SignedRadialStretch.residualRate n (coefficient N z x y)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    0 (gradientRemainder u (torusPoint x) (torusPoint y)) (imageVelocityRemainder z u x y)

def viscousImageRate (n N : ℕ) (z : R3) (u : FourierVelocity) (x y : X3) : ℝ :=
  SignedRadialStretch.residualRate n (coefficient N z x y)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    (fullVorticityLaplacian u (torusPoint x)) (fullVorticityLaplacian u (torusPoint y)) 0

def materialRate (n N : ℕ) (z : R3) (u : FourierVelocity) (nu : ℝ) (x y : X3) : ℝ :=
  kernelTransport n N z u x y + commonDeformation n N z u x y +
    nonviscousImageRate n N z u x y + nu * viscousImageRate n N z u x y

theorem materialRate_eq (n N : ℕ) (z : R3) (u : FourierVelocity) (nu : ℝ)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ k, modeDot k (u k) = 0) (x y : X3) :
    SignedRadialStretch.rate n (coefficient N z x y) (coefficientRate N z u x y)
      (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
      (fullStrainOperator u (torusPoint x) (fullVorticity u (torusPoint x)) +
        nu • fullVorticityLaplacian u (torusPoint x))
      (fullStrainOperator u (torusPoint y) (fullVorticity u (torusPoint y)) +
        nu • fullVorticityLaplacian u (torusPoint y))
      (velocity u (torusPoint x) - velocity u (torusPoint y)) = materialRate n N z u nu x y := by
  rw [← gradient_vorticity, ← gradient_vorticity]
  have h := SignedRadialStretch.rate_cancel_common n (coefficient N z x y) (coefficientRate N z u x y)
    (gradientMatrix u (torusPoint x)) (trace_gradientMatrix u hu hd _)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    (nu • fullVorticityLaplacian u (torusPoint x))
    (gradientRemainder u (torusPoint x) (torusPoint y) + nu • fullVorticityLaplacian u (torusPoint y))
    (imageVelocityRemainder z u x y)
  change SignedRadialStretch.rate _ _ _ _ _ _ (gradient u _ _ + _)
    (gradient u _ _ + _) (gradient u _ _ + _) = _ at h
  have hy : gradient u (torusPoint x) (fullVorticity u (torusPoint y)) +
      (gradientRemainder u (torusPoint x) (torusPoint y) + nu • fullVorticityLaplacian u (torusPoint y)) =
      gradient u (torusPoint y) (fullVorticity u (torusPoint y)) +
        nu • fullVorticityLaplacian u (torusPoint y) := by
    simp only [gradientRemainder, sub_apply]
    abel
  have hv : gradient u (torusPoint x) (imageSeparation z x y) + imageVelocityRemainder z u x y =
      velocity u (torusPoint x) - velocity u (torusPoint y) := by
    simp only [imageVelocityRemainder, add_sub_cancel]
  rw [hy, hv] at h
  rw [h]
  have hr := SignedRadialStretch.residualRate_add n (coefficient N z x y)
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    0 (gradientRemainder u (torusPoint x) (torusPoint y)) (imageVelocityRemainder z u x y)
    (nu • fullVorticityLaplacian u (torusPoint x)) (nu • fullVorticityLaplacian u (torusPoint y)) 0
  simp only [zero_add, add_zero] at hr
  rw [hr]
  have hv := SignedRadialStretch.residualRate_smul n (coefficient N z x y) nu
    (fullVorticity u (torusPoint x)) (fullVorticity u (torusPoint y)) (imageSeparation z x y)
    (fullVorticityLaplacian u (torusPoint x)) (fullVorticityLaplacian u (torusPoint y)) 0
  simp only [smul_zero] at hv
  rw [hv]
  exact (add_assoc _ _ _).symm

theorem hasDerivAt_sourceDensity_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (n N : ℕ) (z : R3) (hz : imageSeparation z (X t) (Y t) ≠ 0) :
    HasDerivAt (fun τ ↦ sourceDensity n N z (s.coefficients τ) (X τ) (Y τ))
      (materialRate n N z (s.coefficients t) nu (X t) (Y t)) t := by
  have hx := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI X t ht hX
  have hy := LocalVorticityTangency.hasDerivAt_fullVorticity_path s g hg hSum hu a b hab hI Y t ht hY
  let L := (WithLp.linearEquiv 2 ℝ X3).symm.toContinuousLinearEquiv
  have hh : HasDerivAt (fun τ ↦ imageSeparation z (X τ) (Y τ))
      (velocity (s.coefficients t) (torusPoint (X t)) -
        velocity (s.coefficients t) (torusPoint (Y t))) t :=
    (L.hasFDerivAt.comp_hasDerivAt t (hX.sub hY)).const_add z
  have h := RadialRieszRegularization.hasDerivAt_signedDensity N n (EuclideanSpace.single 0 1) hx hy hh hz
  change HasDerivAt (fun τ ↦ sourceDensity n N z (s.coefficients τ) (X τ) (Y τ))
    (SignedRadialStretch.rate n (coefficient N z (X t) (Y t))
      (coefficientRate N z (s.coefficients t) (X t) (Y t)) _ _ _ _ _ _) t at h
  have hm := summable_fourierMoment_of_le _ (by omega : 2 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
      (hu t (Set.Ioo_subset_Icc_self (hI (Set.Ioo_subset_Icc_self ht)))))
  rw [materialRate_eq _ _ _ _ nu hm (s.transverse t)] at h
  exact h

/-- Freeze the chosen image at one time; never differentiate a canonical
representative as if it were a smooth material curve. -/
def frozenImageShift (x y : X3) (z : Lat) : R3 :=
  UnitTorusSchwartzLattice.displacement (torusPoint x - torusPoint y) z - separation x y

theorem imageSeparation_frozenImageShift (x y : X3) (z : Lat) :
    imageSeparation (frozenImageShift x y z) x y =
      UnitTorusSchwartzLattice.displacement (torusPoint x - torusPoint y) z :=
  sub_add_cancel _ _

theorem frozenImageShift_mem_lattice (x y : X3) (z : Lat) :
    frozenImageShift x y z ∈ UnitTorusLattice.LatticeSubmodule (ι := Fin 3) := by
  apply UnitTorusLattice.sub_mem_lattice_of_projection_eq
  rw [UnitTorusSchwartzLattice.torusProjection_displacement]
  funext i
  exact (AddCircle.coe_sub (p := (1 : ℝ)) (x i) (y i)).symm

theorem sourceDensity_frozenImageShift (n N : ℕ) (u : FourierVelocity) (x y : X3) (z : Lat) :
    sourceDensity n N (frozenImageShift x y z) u x y =
      VorticityRadialPairing.imageDensity (2 * (n + 1)) N u (torusPoint x) (torusPoint y) z := by
  simp only [sourceDensity, coefficient, SignedRadialStretch.density, SignedRadialStretch.amplitudePair,
    imageSeparation_frozenImageShift, VorticityRadialPairing.imageDensity]

/-- The image is frozen at `t`; the endpoint vorticities and real lifts
continue to follow the actual local solution. -/
theorem hasDerivAt_frozenImage_path {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)
    (a b : ℝ) (hab : a ≤ b) (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (X Y : ℝ → X3) (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hX : HasDerivAt X (liftedVelocity s t (X t)) t)
    (hY : HasDerivAt Y (liftedVelocity s t (Y t)) t)
    (n N : ℕ) (z : Lat) (hxy : torusPoint (X t) ≠ torusPoint (Y t)) :
    HasDerivAt (fun τ ↦ sourceDensity n N (frozenImageShift (X t) (Y t) z)
      (s.coefficients τ) (X τ) (Y τ))
      (materialRate n N (frozenImageShift (X t) (Y t) z) (s.coefficients t) nu (X t) (Y t)) t := by
  apply hasDerivAt_sourceDensity_path s g hg hSum hu a b hab hI X Y t ht hX hY n N
  rw [imageSeparation_frozenImageShift]
  exact UnitTorusSchwartzLattice.displacement_ne_zero (sub_ne_zero.mpr hxy) z

end Mettapedia.FluidDynamics.NavierStokes.LocalRadialImageEvolution

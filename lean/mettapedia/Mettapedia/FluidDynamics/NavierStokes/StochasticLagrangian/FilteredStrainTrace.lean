import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StrainEigenvalueContinuity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierMaterialPaths

/-!
# Trace-free filtered strain and quantitative bottom-eigenvalue damping

Fourier incompressibility makes each reconstructed strain coefficient
trace-free. The real operator trace then equals the sum of its ordered
eigenvalues. Their ordering bounds the bottom eigenvalue by the bottom gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredStrainTrace

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFourierPressureStrain
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeStrainSpectralFrame
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralClusterDichotomy.SymmetricStrain StrainEigenvalueContinuity

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)

theorem trace_realMatrixOperator (A : MatrixCoefficient) :
    LinearMap.trace ℝ R3 (realMatrixOperator A).toLinearMap = A.trace.re := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [realMatrixOperator, Matrix.inner_toEuclideanCLM, EuclideanSpace.basisFun_apply,
    realMatrix, Matrix.mulVec, dotProduct, Matrix.trace]

theorem matrixReconstruction_strain_trace_zero (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ q, modeDot q (u q) = 0) (x : T3) :
    (matrixReconstruction modes (strainCoeff u) x).trace = 0 := by
  simp only [matrixReconstruction, Matrix.trace_sum, Matrix.trace_smul]
  apply Finset.sum_eq_zero
  intro q _
  rw [strainCoeff_trace_zero u q (hu q), smul_zero]

theorem trace_spatialStrain_eq_zero (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ q, modeDot q (u q) = 0) (x : T3) :
    LinearMap.trace ℝ R3 (spatialStrain modes u x).1.toLinearMap = 0 := by
  change LinearMap.trace ℝ R3 (realMatrixOperator (matrixReconstruction modes (strainCoeff u) x)).toLinearMap = 0
  rw [trace_realMatrixOperator, matrixReconstruction_strain_trace_zero modes u hu x, Complex.zero_re]

theorem trace_filteredStrain_eq_zero (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : ∀ q, modeDot q (u q) = 0) (x : T3) :
    LinearMap.trace ℝ R3 (spatialStrain modes (filteredVelocity chi u) x).1.toLinearMap = 0 := by
  apply trace_spatialStrain_eq_zero
  intro q
  exact filteredVelocity_transverse chi u q (hu q)

theorem thirdEigenvalue_le_neg_two_thirds_bottomGap (S : SymmetricStrain)
    (htrace : LinearMap.trace ℝ R3 S.1.toLinearMap = 0) :
    thirdEigenvalue S ≤ -(2 / 3 : ℝ) * bottomGap S := by
  rw [trace_eq_sum_orderedEigenvalues] at htrace
  have horder : secondEigenvalue S ≤ topEigenvalue S :=
    (orderedEigenframe S.1 S.2).antitone_eigenvalue (by decide)
  unfold bottomGap
  linarith

end Mettapedia.FluidDynamics.NavierStokes.FilteredStrainTrace

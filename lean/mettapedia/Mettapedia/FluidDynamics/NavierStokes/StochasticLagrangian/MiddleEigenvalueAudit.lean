import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueCriterion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueEvolution

/-! Checks for the middle-eigenvalue criterion: Betchov's identity for the actual periodic
field, the sheet-forming bound on enstrophy production, and the resulting equivalence with
periodic regularity. The equivalence reformulates the open problem; it proves no bound.
Also checked: the material evolution law of the middle eigenvalue and the restricted Euler
sheet, which shows that the local terms of that law do not bound it. -/

set_option autoImplicit false
noncomputable section

open Mettapedia.FluidDynamics.NavierStokes
open PeriodicFourierTriad PancakeCurlOutputTail LocalEnstrophyDiffusion
open MiddleEigenvalueAlgebra BetchovIdentity MiddleEigenvalueCriterion

example (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0) :
    stretching u ≤ middleSup u * meanEnstrophy u :=
  stretching_le_middleSup u hu hd

#print axioms MiddleEigenvalueAlgebra.trSq_eq
#print axioms MiddleEigenvalueAlgebra.trCube_eq
#print axioms MiddleEigenvalueAlgebra.neg_trCube_le
#print axioms MiddleEigenvalueAlgebra.sqFluxDiv_eq
#print axioms MiddleEigenvalueAlgebra.cubeFluxDiv_eq
#print axioms BetchovIdentity.integral_trSq_eq_zero
#print axioms BetchovIdentity.integral_trCube_eq_zero
#print axioms MiddleEigenvalueCriterion.toStrain_eq_fullSymmetricStrain
#print axioms MiddleEigenvalueCriterion.stretching_eq_trCube
#print axioms MiddleEigenvalueCriterion.integral_normSq_eq
#print axioms MiddleEigenvalueCriterion.stretching_le_middleSup
#print axioms MiddleEigenvalueCriterion.meanEnstrophy_le_of_middle
#print axioms MiddleEigenvalueCriterion.nonempty_globalSolution_iff_middleBound
#print axioms MiddleEigenvalueCriterion.periodicRegularity_iff_middleBound
#print axioms MiddleEigenvalueCriterion.periodicStatementB_of_middleBound
#print axioms MiddleEigenvalueAlgebra.sum_spin_sq
#print axioms MiddleEigenvalueEvolution.norm_spinAlong_sq
#print axioms MiddleEigenvalueEvolution.normSq_symm_gradAlong
#print axioms MiddleEigenvalueEvolution.inner_rate_eq
#print axioms MiddleEigenvalueEvolution.hasDerivAt_secondEigenvalueAlong
#print axioms MiddleEigenvalueEvolution.trace_pressureHessianAlong
#print axioms MiddleEigenvalueEvolution.hasDerivAt_secondEigenvalueAlong_anisotropic
#print axioms MiddleEigenvalueEvolution.restricted_sheet

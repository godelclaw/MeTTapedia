import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MiddleEigenvalueCriterion

/-! Checks for the middle-eigenvalue criterion: Betchov's identity for the actual periodic
field, the sheet-forming bound on enstrophy production, and the resulting equivalence with
periodic regularity. The equivalence reformulates the open problem; it proves no bound. -/

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

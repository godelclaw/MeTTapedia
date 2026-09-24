import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFluxHeat

/-!
# Contracted rational convolution for divergence and heat variation

Contract the output frequency and the velocity derivative before summing
input modes. This is an exact reassociation of the full convolution. A
zero third-slot component is tested first to avoid evaluating inactive
interactions in closed rational certificates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxContraction

open PeriodicFourierTriad PeriodicGradientFluxTriple
open RationalStretchingFlux RationalStretchingFluxHeat

def divergenceInteraction (a : RationalVelocity) (q : Wavevector) (p : TripleIndex)
    (i : Fin 3) : ℚ :=
  if a p.2.2 i = 0 then 0 else
    (∑ j, (q j : ℚ) * rationalCurl a p.1 j) *
      (∑ r, (p.2.2 r : ℚ) * rationalCurl a p.2.1 r) * a p.2.2 i

theorem divergenceInteraction_eq (a : RationalVelocity) (q : Wavevector) (p : TripleIndex)
    (i : Fin 3) :
    divergenceInteraction a q p i =
      (∑ j, (q j : ℚ) * rationalCurl a p.1 j) *
        (∑ r, (p.2.2 r : ℚ) * rationalCurl a p.2.1 r) * a p.2.2 i := by
  unfold divergenceInteraction
  split_ifs with h
  · simp [h]
  · rfl

theorem divergence_eq_double_sum (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) (i : Fin 3) :
    rationalDivergenceCoefficient s a q i =
      ∑ k ∈ s, ∑ l ∈ s, divergenceInteraction a q (k, (l, q - k - l)) i := by
  simp only [rationalDivergenceCoefficient, rationalFluxCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [rationalInteraction, divergenceInteraction_eq, Fin.sum_univ_three]
  ring

theorem heat_divergence_eq_double_sum (s : Finset Wavevector) (a : RationalVelocity)
    (q : Wavevector) (i : Fin 3) :
    rationalHeatDivergenceCoefficient s a q i =
      ∑ k ∈ s, ∑ l ∈ s, tripleHeatWeight (k, (l, q - k - l)) *
        divergenceInteraction a q (k, (l, q - k - l)) i := by
  simp only [rationalHeatDivergenceCoefficient, rationalHeatFluxCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [rationalInteraction, divergenceInteraction_eq, Fin.sum_univ_three]
  ring

end Mettapedia.FluidDynamics.NavierStokes.RationalStretchingFluxContraction

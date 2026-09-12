import Mettapedia.Analysis.PeriodicRieszSeparated
import Mettapedia.Analysis.SmoothAmplitudePairingBound

/-! Separated-kernel regressions retain uniformity in the number of annuli. -/

open Mettapedia.Analysis

example (r : ℝ) (hr : 0 < r) :
    ∃ C ≥ (0 : ℝ), ∀ N (q : UnitAddTorus (Fin 3)), r ≤ ‖q‖ →
      ‖PeriodicRieszOperator.kernel N q‖ ≤ C :=
  PeriodicRieszSeparated.exists_uniform_operator_bound r hr

example (N : ℕ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 4 * ‖AnnularRieszKernel.partialKernel (0 : Fin 3) 1 N x‖ ≤
      AnnularRieszKernel.decayBound (0 : Fin 3) 1 :=
  AnnularRieszKernel.pow_mul_norm_partialKernel_le 0 1 N x

#print axioms AnnularRieszKernel.pow_mul_norm_dyadicKernel_le
#print axioms AnnularRieszKernel.pow_mul_norm_partialKernel_le
#print axioms AnnularRieszKernel.norm_partialKernel_le
#print axioms UnitTorusSeparatedLattice.norm_representative_le
#print axioms UnitTorusSeparatedLattice.exists_uniform_inverse_power_majorant
#print axioms PeriodicRieszSeparated.exists_uniform_entry_bound
#print axioms PeriodicRieszSeparated.exists_uniform_operator_bound
#print axioms PeriodicRieszSeparated.exists_uniform_polynomial_bound
#print axioms SmoothAmplitudePairing.abs_retainedStretch_le_amplitudes
#print axioms SmoothAmplitudePairing.abs_half_integral_retained_le_of_bound

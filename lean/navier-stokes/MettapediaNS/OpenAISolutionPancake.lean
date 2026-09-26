import NavierStokes.R3.Theorem
import MettapediaNS.ForcedCandidatePancake

/-!
# Middle-eigenvalue budgets fail for OpenAI's constructed forced solutions

The actual solution supplied by OpenAI's Theorem 1.1 admits no uniform integral bound for
nonnegative continuous majorants of the middle strain eigenvalue on compact slabs exhausting
`[1/2, 1)`. This applies the energy argument to the imported construction without rebuilding it.
The force is smooth and compactly supported. A regularity argument that would give the same
middle-eigenvalue budget with such forcing therefore fails this test; the unforced problem
remains open.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake

open NavierStokesR3.ProblemStatement

/-- For every positive viscosity, the constructed forced solution violates the uniform
middle-eigenvalue budget used in the whole-space regularity criterion. -/
theorem openAI_solution_no_uniform_middle_majorants (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      ∃ hc : CandidateProperties ν u p f K,
        ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧ ¬ UniformMiddleMajorants hc := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, no_uniform_middle_majorants hc hν⟩

end Mettapedia.FluidDynamics.NavierStokes.ForcedCandidatePancake

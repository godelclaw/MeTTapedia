import NavierStokes.R3.Theorem
import MettapediaNS.ForcedCandidateVorticity

/-!
# The eighth vorticity moment of OpenAI's constructed solutions

OpenAI's Theorem 1.1 constructs, for every positive viscosity, a whole-space
Navier–Stokes solution driven by a smooth force compactly supported in
positive time, which starts from rest and breaks down at time one. Applying
`ForcedCandidateVorticity.candidate_eighthVorticityMoment_unbounded` to the
constructed fields shows that their eighth vorticity moment is unbounded
before time one. The imported construction is used as proved; nothing in it
is reimplemented.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ForcedCandidateVorticity

open EulerBlowup Ring3D
open NavierStokesR3.ProblemStatement

/-- For every positive viscosity, OpenAI's constructed forced solution has no
global finite-energy competitor and an unbounded eighth vorticity moment
before its singular time. -/
theorem openAI_solution_eighthVorticityMoment_unbounded (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ¬ BddAbove ((fun t ↦ ∫ x, ‖curl3 (fun y ↦ u (t, y)) x‖ ^ (8 : ℕ)) '' Set.Ioo 0 1) := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, candidate_eighthVorticityMoment_unbounded hc⟩

end Mettapedia.FluidDynamics.NavierStokes.ForcedCandidateVorticity

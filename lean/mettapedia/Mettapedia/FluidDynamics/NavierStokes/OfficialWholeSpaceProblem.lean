/-
SPDX-License-Identifier: Apache-2.0
Adapted from google-deepmind/formal-conjectures,
FormalConjectures/Millenium/NavierStokes.lean at revision
8bf45ed70d48b2b2a501de9c00b26bfa38c573ee, as retained in the comparator
reference of OpenAI's NavierStokesAndEuler development.
Modified by MeTTapedia contributors: specialized to three dimensions and to the
whole-space existence-and-smoothness alternative (A) with zero force; the
definitions are otherwise unchanged. See LICENSES/Apache-2.0.txt at the
repository root.
-/
import Mettapedia.FluidDynamics.NavierStokes.OfficialPeriodicProblem

/-!
# The official whole-space existence-and-smoothness statement

This module fixes the whole-space target: alternative (A) of the Clay problem as
formalized in Formal Conjectures, on `ℝ³` with zero external force. The initial velocity is
smooth, divergence-free, and all of its derivatives decay faster than every power of
`1 + |x|`. A solution is smooth on `ℝ³ × [0, ∞)`, square-integrable at every time, and has
uniformly bounded kinetic energy. The divergence, the smooth solution notion and the
Navier–Stokes equation are those of `OfficialPeriodicProblem`.

`WholeSpaceStatementA` is a proposition, not an axiom and not a proved theorem.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace Mettapedia.FluidDynamics.NavierStokes.OfficialWholeSpaceProblem

open OfficialPeriodicProblem

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Smooth, divergence-free initial velocity whose derivatives of every order decay faster
than every power of `1 + |x|`. -/
structure InitialVelocityConditionDecay (u₀ : ℝ³ → ℝ³) : Prop
    extends InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- A smooth solution on `ℝ³ × [0, ∞)` with finite, uniformly bounded kinetic energy. -/
structure NavierStokesExistenceAndSmoothnessRn
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- **OPEN (Clay (A), whole space, zero force).** For every positive viscosity, every
smooth, divergence-free, rapidly decaying initial velocity has a smooth solution with
bounded energy for all time. This is a definition, not an assumption. -/
def WholeSpaceStatementA : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ (fun _ _ ↦ 0) v p

end Mettapedia.FluidDynamics.NavierStokes.OfficialWholeSpaceProblem

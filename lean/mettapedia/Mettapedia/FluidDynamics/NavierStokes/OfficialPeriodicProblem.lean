/-
SPDX-License-Identifier: Apache-2.0
Adapted from google-deepmind/formal-conjectures,
FormalConjectures/Millenium/NavierStokes.lean at revision
8bf45ed70d48b2b2a501de9c00b26bfa38c573ee, as retained in the comparator
reference of OpenAI's NavierStokesAndEuler development.
Modified by MeTTapedia contributors: specialized to three dimensions and to the
periodic existence-and-smoothness alternative (B) with zero force; the
definitions are otherwise unchanged. See LICENSES/Apache-2.0.txt at the
repository root.
-/
import Mathlib

/-!
# The official periodic existence-and-smoothness statement

This module fixes the target of the periodic Navier–Stokes lane: alternative
(B) of the Clay problem as formalized in Formal Conjectures, for the unit
torus `ℝ³/ℤ³` and zero external force. The velocity is written `v x t`, with
position before time; the time derivative at `t ≥ 0` is taken within
`[0, ∞)`, and the velocity and pressure must be smooth on `ℝ³ × [0, ∞)` and
one-periodic in space.

`PeriodicStatementB` is a proposition, not an axiom and not a proved theorem.
-/

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace Mettapedia.FluidDynamics.NavierStokes.OfficialPeriodicProblem

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The divergence `∇ · v`, the trace of the Jacobian. -/
noncomputable def divergence (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ := (fderiv ℝ v x).trace ℝ ℝ³

/-- One-periodicity in each coordinate. -/
def IsOnePeriodic {α : Sort*} (f : ℝ³ → α) : Prop :=
  ∀ x i, f (x + EuclideanSpace.single i 1) = f x

/-- Smooth, divergence-free initial velocity. -/
structure InitialVelocityCondition (u₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, divergence u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Smooth, divergence-free, one-periodic initial velocity. -/
structure InitialVelocityConditionPeriodic (u₀ : ℝ³ → ℝ³) : Prop
    extends InitialVelocityCondition u₀ where
  isOnePeriodic : IsOnePeriodic u₀

/-- A smooth solution on `ℝ³ × [0, ∞)` of the Navier–Stokes equations with
viscosity `nu`, initial velocity `u₀` and force `f`. -/
structure NavierStokesExistenceAndSmoothness
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  navier_stokes : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      nu • Δ (v · t) x - gradient (p · t) x + f x t
  div_free : ∀ x, ∀ t ≥ 0, divergence (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (↿v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (↿p) (Set.univ ×ˢ Set.Ici 0)

/-- A smooth solution on the torus: velocity and pressure are one-periodic. -/
structure NavierStokesExistenceAndSmoothnessPeriodic
    (nu : ℝ) (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³)
    (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends NavierStokesExistenceAndSmoothness nu u₀ f v p where
  isOnePeriodic_velocity : ∀ t ≥ 0, IsOnePeriodic (v · t)
  isOnePeriodic_pressure : ∀ t ≥ 0, IsOnePeriodic (p · t)

/-- **OPEN (Clay (B), periodic, zero force).** For every positive viscosity,
every smooth, divergence-free, one-periodic initial velocity has a smooth
periodic solution for all time. This is a definition, not an assumption. -/
def PeriodicStatementB : Prop :=
  ∀ nu : ℝ, 0 < nu → ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p

end Mettapedia.FluidDynamics.NavierStokes.OfficialPeriodicProblem

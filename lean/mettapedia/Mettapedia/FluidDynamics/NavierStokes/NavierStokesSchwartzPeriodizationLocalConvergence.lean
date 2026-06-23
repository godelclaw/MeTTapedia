import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzPeriodizationLimit

/-!
# Navier-Stokes: Schwartz Periodization Local Convergence

Semantic layer split from `NavierStokesSchwartzPeriodizationConvergence`.
-/


set_option autoImplicit false

noncomputable section

open Filter

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open scoped BigOperators

/-- The centered spatial cube `Q_R = [-R, R]^3 ⊂ ℝ^3`. -/
def spatialCube (R : ℝ) : Set NSSpace :=
  { x | ∀ i : Fin 3, |x i| ≤ R }

/-- Membership in `Q_R` is the expected coordinatewise bound. -/
theorem mem_spatialCube_iff {R : ℝ} {x : NSSpace} :
    x ∈ spatialCube R ↔ ∀ i : Fin 3, |x i| ≤ R :=
  Iff.rfl

/-- Larger radii contain smaller centered cubes. -/
theorem spatialCube_mono {R S : ℝ} (hRS : R ≤ S) :
    spatialCube R ⊆ spatialCube S := by
  intro x hx
  rw [mem_spatialCube_iff] at hx ⊢
  intro i
  exact (hx i).trans hRS

/-- Local convergence of the boxed partial periodizations on a set `s`. -/
def BoxedPartialPeriodizationConvergesOn
    (s : Set NSSpace) (L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  ∀ x ∈ s, Tendsto (fun N => boxedPartialPeriodizedInitialVelocity N L u₀ x)
    Filter.atTop (nhds (u x))

/-- Local convergence of the boxed partial periodizations on the centered cube
`Q_R`. -/
def BoxedPartialPeriodizationConvergesOnCube
    (R L : ℝ) (u₀ u : NSInitialVelocity) : Prop :=
  BoxedPartialPeriodizationConvergesOn (spatialCube R) L u₀ u

/-- The boxed partial periodizations of Schwartz data converge pointwise on any
fixed set to the `tsum`-defined whole-space periodization candidate whenever
`L ≠ 0`. -/
theorem BoxedPartialPeriodizationConvergesOn_of_schwartz
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    BoxedPartialPeriodizationConvergesOn s L (u₀ : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀) := by
  intro x hx
  let f : NSLatticeIndex → NSSpace := fun n => u₀ (x + periodizationShift L n)
  have hsum : HasSum f (schwartzPeriodizedInitialVelocity L u₀ x) := by
    simpa [f, schwartzPeriodizedInitialVelocity] using
      hasSum_schwartzPeriodizedInitialVelocity hL u₀ x
  simpa [f, boxedPartialPeriodizedInitialVelocity, finitePartialPeriodizedInitialVelocity] using
    hsum.comp centeredLatticeBox_tendsto_atTop

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem. -/
theorem BoxedPartialPeriodizationConvergesOnCube_of_schwartz
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    BoxedPartialPeriodizationConvergesOnCube R L (u₀ : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartz (s := spatialCube R) hL u₀

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem on the manuscript's `Sσ(ℝ^3)` input class. -/
theorem BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    BoxedPartialPeriodizationConvergesOn s L (u₀.1 : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀.1) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartz (s := s) hL u₀.1

/-- Fixed-cube specialization of the Schwartz boxed-periodization convergence
theorem on the manuscript's `Sσ(ℝ^3)` input class. -/
theorem BoxedPartialPeriodizationConvergesOnCube_of_schwartzDivergenceFree
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    BoxedPartialPeriodizationConvergesOnCube R L (u₀.1 : NSInitialVelocity)
      (schwartzPeriodizedInitialVelocity L u₀.1) :=
  BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree
    (s := spatialCube R) hL u₀

/-- The shell contribution added when enlarging the boxed partial periodization
from radius `N` to radius `N + 1`. -/
def boxedPeriodizationShellInitialVelocity
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    NSInitialVelocity :=
  finitePartialPeriodizedInitialVelocity (centeredLatticeShell N) L u₀

/-- The shell contribution is exactly the one-step difference of boxed partial
periodizations. -/
theorem boxedPeriodizationShellInitialVelocity_eq_sub
    (N : ℕ) (L : ℝ) (u₀ : NSInitialVelocity) :
    boxedPeriodizationShellInitialVelocity N L u₀ =
      boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ -
        boxedPartialPeriodizedInitialVelocity N L u₀ := by
  funext x
  apply eq_sub_iff_add_eq.mpr
  simpa [boxedPeriodizationShellInitialVelocity, add_comm, add_left_comm, add_assoc] using
    (congrFun (boxedPartialPeriodizedInitialVelocity_succ N L u₀) x).symm

theorem BoxedPartialPeriodizationConvergesOn.mono
    {s t : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn t L u₀ u)
    (hst : s ⊆ t) :
    BoxedPartialPeriodizationConvergesOn s L u₀ u := by
  intro x hx
  exact hconv x (hst hx)

theorem BoxedPartialPeriodizationConvergesOnCube.mono
    {R S L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube S L u₀ u)
    (hRS : R ≤ S) :
    BoxedPartialPeriodizationConvergesOnCube R L u₀ u := by
  exact BoxedPartialPeriodizationConvergesOn.mono hconv (spatialCube_mono hRS)

/-- If the boxed partial periodizations converge locally, the added shell
contributions vanish locally. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
    {s : Set NSSpace} {L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOn s L u₀ u) :
    ∀ x ∈ s, Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
      Filter.atTop (nhds 0) := by
  intro x hx
  have hconv_x := hconv x hx
  have hsucc_x :
      Tendsto (fun N => boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x)
        Filter.atTop (nhds (u x)) := by
    exact hconv_x.comp (tendsto_add_atTop_nat 1)
  have hdiff :
      Tendsto
        (fun N =>
          boxedPartialPeriodizedInitialVelocity (N + 1) L u₀ x -
            boxedPartialPeriodizedInitialVelocity N L u₀ x)
        Filter.atTop (nhds (u x - u x)) :=
    hsucc_x.sub hconv_x
  simpa [boxedPeriodizationShellInitialVelocity_eq_sub] using hdiff

/-- Cube-local convergence implies vanishing shell increments on the same cube. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
    {R L : ℝ} {u₀ u : NSInitialVelocity}
    (hconv : BoxedPartialPeriodizationConvergesOnCube R L u₀ u) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L u₀ x)
        Filter.atTop (nhds 0) :=
  boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn hconv

/-- For Schwartz initial data and nonzero period parameter, the shell
increments of the boxed partial periodizations vanish pointwise on any fixed
set. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartz
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    ∀ x ∈ s,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀ : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
      (BoxedPartialPeriodizationConvergesOn_of_schwartz (s := s) hL u₀)

/-- Fixed-cube specialization of the direct shell-vanishing corollary for
Schwartz initial data. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_schwartz
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzInitialVelocity) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀ : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_convergesOnCube
      (BoxedPartialPeriodizationConvergesOnCube_of_schwartz (R := R) hL u₀)

/-- Fixed-cube shell increments also vanish for manuscript-style
`Sσ(ℝ^3)` initial data once the period parameter is nonzero. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartzDivergenceFree
    {s : Set NSSpace} {L : ℝ} (hL : L ≠ 0)
    (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    ∀ x ∈ s,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀.1 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_convergesOn
      (BoxedPartialPeriodizationConvergesOn_of_schwartzDivergenceFree (s := s) hL u₀)

/-- Fixed-cube shell increments also vanish for manuscript-style
`Sσ(ℝ^3)` initial data once the period parameter is nonzero. -/
theorem boxedPeriodizationShellInitialVelocity_tendsto_zero_onCube_of_schwartzDivergenceFree
    {R L : ℝ} (hL : L ≠ 0) (u₀ : NSSchwartzDivergenceFreeInitialVelocity) :
    ∀ x ∈ spatialCube R,
      Tendsto (fun N => boxedPeriodizationShellInitialVelocity N L (u₀.1 : NSInitialVelocity) x)
        Filter.atTop (nhds 0) := by
  exact
    boxedPeriodizationShellInitialVelocity_tendsto_zero_on_of_schwartzDivergenceFree
      (s := spatialCube R) hL u₀

end NavierStokes
end FluidDynamics
end Mettapedia

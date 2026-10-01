import Mettapedia.QuantumTheory.YangMills.WilsonBoundaryChanges

/-!
# Separated boundary changes of the Wilson partition function

The four boundary conditions are the original one, each of two changes, and
both changes together. Plaquette separation gives their exact multiplicative
relation. The resulting mixed logarithm has an exponential spatial bound,
uniform in the rest of the volume and in all fixed boundary values.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonPatchGeometry WilsonLocalResponse
open WilsonBoundaryChanges WilsonBlockElimination WilsonBoundaryResponse

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d n : ℕ}

export WilsonLocalResponse (extend)

/-- The actual boundary-change factor on its finite collar. -/
def localChange (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (base : E) (β : ℝ)
    (held S : Finset (Link d M.n)) (b new : Link d M.n → E) : C(collar S → E, ℝ) :=
  (changeFactor M hφ β held S b new).comp (extend base (collar S))

theorem localChange_reconstruct (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (base : E) (β : ℝ) (held S : Finset (Link d M.n)) (b new : Link d M.n → E) :
    localObservable (collar S) (localChange M hφ base β held S b new) =
      changeFactor M hφ β held S b new := by
  ext ω
  change changeFactor M hφ β held S b new
      (extendConfiguration base (collar S) (restrictTo (collar S) ω)) =
    changeFactor M hφ β held S b new ω
  apply changeFactor_local M hφ β held S b new
  intro l hl
  simp [extendConfiguration, restrictTo, hl]

/-- A change on a second, plaquette-disjoint patch leaves the first response
factor unchanged, including its normalization-independent pointwise value. -/
theorem changeFactor_other (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S T : Finset (Link d M.n)) (b a c : Link d M.n → E)
    (hST : Disjoint (incident S) (incident T)) :
    changeFactor M hφ β held S (replace T c b) a =
      changeFactor M hφ β held S b a := by
  ext ω
  apply congrArg (fun x => Real.exp (-β * x))
  apply sum_congr rfl
  intro p hp
  have hpT : p ∉ incident T := fun h => disjoint_left.mp hST hp h
  have htop : pinnedPotential M held (replace S a (replace T c b)) p ω =
      pinnedPotential M held (replace S a b) p ω := by
    apply pinnedPotential_eq_of_agree
    intro l hl
    have hlT : l ∉ T := fun h => hpT (mem_incident.mpr ⟨l, h, hl⟩)
    simp [replace, hlT]
  rw [htop, unchanged_off_incident M held T b c p hpT]

/-- Both modifications applied to the actual original density. -/
theorem density_changed_twice (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held S T : Finset (Link d M.n)) (b a c : Link d M.n → E)
    (hST : Disjoint (incident S) (incident T)) :
    realDensity (M.pinned held (replace T c (replace S a b)))
      (continuous_pinned M hφ held _) β =
      realDensity (M.pinned held b) (continuous_pinned M hφ held _) β *
        (changeFactor M hφ β held S b a * changeFactor M hφ β held T b c) := by
  rw [density_changed M hφ β held T (replace S a b) c,
    changeFactor_other M hφ β held T S b c a hST.symm,
    density_changed M hφ β held S b a, mul_assoc]

/-- Logarithm of the original fixed-boundary partition function, expressed
using independent dummy variables for held coordinates. -/
def boundaryLogPartition (ν₀ : Measure E) (M : Model d E)
    (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (held : Finset (Link d M.n))
    (b : Link d M.n → E) : ℝ :=
  logPartition (Measure.pi fun _ => ν₀)
    (realDensity (M.pinned held b) (continuous_pinned M hφ held b) β)

/-- The observable is the mixed change of four boundary partition functions. -/
def boundaryResponse (ν₀ : Measure E) (M : Model d E)
    (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (held S T : Finset (Link d M.n))
    (b a c : Link d M.n → E) : ℝ :=
  boundaryLogPartition ν₀ M hφ β held (replace T c (replace S a b)) +
    boundaryLogPartition ν₀ M hφ β held b -
      boundaryLogPartition ν₀ M hφ β held (replace S a b) -
        boundaryLogPartition ν₀ M hφ β held (replace T c b)

theorem boundaryResponse_eq_mixedResponse (ν₀ : Measure E) (M : Model d E)
    (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (held S T : Finset (Link d M.n))
    (b a c : Link d M.n → E) (hST : Disjoint (incident S) (incident T)) :
    boundaryResponse ν₀ M hφ β held S T b a c =
      mixedResponse (Measure.pi fun _ => ν₀)
        (realDensity (M.pinned held b) (continuous_pinned M hφ held b) β)
        (changeFactor M hφ β held S b a) (changeFactor M hφ β held T b c) := by
  unfold boundaryResponse boundaryLogPartition mixedResponse
  rw [density_changed_twice M hφ β held S T b a c hST,
    density_changed M hφ β held S b a, density_changed M hφ β held T b c]

/-- Exponential spatial decay for two actual boundary modifications. The
coupling range and decay rate are uniform over all pinning and all volumes. -/
theorem boundaryResponse_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
      (held S T : Finset (Link d M.n)) (b a c : Link d M.n → E),
      (collar S).Nonempty → Disjoint (incident S) (incident T) →
      |boundaryResponse ν₀ M hφ β held S T b a c| ≤
        (3 * Real.exp (2 * β * (incident S).card) * Real.exp (2 * β * (incident T).card) *
          Real.exp (3 * (collar S).card + 3 * (collar T).card) *
          Real.exp (-κ * polymerDist (collar S) (collar T))) /
          (Real.exp (-2 * β * (incident S).card) * Real.exp (-2 * β * (incident T).card)) := by
  obtain ⟨κ, hκ, hc⟩ := mixedResponse_clustering d ν₀ base hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro M hφ held S T b a c hS hST
  rw [boundaryResponse_eq_mixedResponse ν₀ M hφ β held S T b a c hST,
    ← localChange_reconstruct M hφ base β held S b a,
    ← localChange_reconstruct M hφ base β held T b c]
  exact hc (M.pinned held b) (continuous_pinned M hφ held b) (collar S) (collar T) hS
    (localChange M hφ base β held S b a) (localChange M hφ base β held T b c)
    _ _ _ _ (Real.exp_pos _) (Real.exp_pos _)
    (fun v => (changeFactor_bounds M hφ hβ held S b a _).1)
    (fun v => (changeFactor_bounds M hφ hβ held S b a _).2)
    (fun v => (changeFactor_bounds M hφ hβ held T b c _).1)
    (fun v => (changeFactor_bounds M hφ hβ held T b c _).2)

#print axioms density_changed_twice
#print axioms boundaryResponse_eq_mixedResponse
#print axioms boundaryResponse_clustering

end Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse

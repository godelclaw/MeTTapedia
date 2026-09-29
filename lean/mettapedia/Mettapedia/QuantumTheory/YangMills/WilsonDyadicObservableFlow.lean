import Mettapedia.QuantumTheory.YangMills.SU2WilsonAssemblyLocality

/-!
# Observable locality along arbitrary dyadic conditional projections

Each operator is the actual normalized Wilson integral with its specified
retained coordinates. Iterating these continuous operators derives the
support recurrence for the resulting marks. For the SU(2) assembly, the
first two operators are identified with its staged elimination route,
including the generated intermediate density.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills
namespace WilsonDyadicObservableFlow
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonPinnedIntegral WilsonDyadicLocality WilsonDyadicProjection WilsonProductLocality

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d n : ℕ}

def pinMap (held : Finset (Link d n)) : C((Link d n → E) × (Link d n → E), Link d n → E) :=
  ⟨fun p => pin held p.1 p.2, by
    apply continuous_pi
    intro l
    dsimp [pin]
    split_ifs <;> fun_prop⟩

/-- The actual conditional integral as a continuous boundary mark, lifted to
the original coordinate space by ignoring unretained coordinates. -/
def projectMap (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) : C(Link d M.n → E, ℝ) :=
  WilsonBlockElimination.project (Measure.pi fun _ : Link d M.n => ν₀)
    ((realDensity M hφ β).comp (pinMap held))
    (fun _ => realDensity_pos M hφ β _) (F.comp (pinMap held))

theorem projectMap_apply (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E) :
    projectMap ν₀ M hφ β held F b = WilsonConditionalProjection.project ν₀ M hφ β held F b := rfl

/-- Successive original-law conditional projections at doubled separator meshes. -/
def observableSequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (F : C(Link d M.n → E, ℝ)) : ℕ → C(Link d M.n → E, ℝ)
  | 0 => F
  | j + 1 => projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
      (observableSequence ν₀ M hφ β F j)

/-- The support recurrence is proved for these explicitly defined integral
operators at every stage, with no support-growth hypothesis on a black box. -/
theorem observableSequence_locality (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (hF : DependsOn S F) :
    ∀ j, DependsOn (supportSequence S j) (observableSequence ν₀ M hφ β F j) := by
  intro j
  induction j with
  | zero => exact hF
  | succ j ih =>
    intro b b' hb
    change projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
      (observableSequence ν₀ M hφ β F j) b =
      projectMap ν₀ M hφ β (retainedSet (2^(j+1)))
        (observableSequence ν₀ M hφ β F j) b'
    rw [projectMap_apply, projectMap_apply]
    exact project_dependsOn ν₀ base M hφ β (2^(j+1)) (supportSequence S j)
      (observableSequence ν₀ M hφ β F j) ih b b' hb

/-- Each actual projected mark has an explicit dependency set contained in a
uniform collar in the successively rescaled metric. -/
theorem observableSequence_uniform_collar (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (hF : DependsOn S F)
    (c : Link d M.n) (r : ℝ) (hS : ∀ l ∈ S, dist l c ≤ r) (j : ℕ) :
    DependsOn (supportSequence S j) (observableSequence ν₀ M hφ β F j) ∧
      ∀ l ∈ supportSequence S j, dist l c / (2 : ℝ)^j ≤ r / (2 : ℝ)^j + 4 :=
  ⟨observableSequence_locality ν₀ base M hφ β S F hF j,
    fun l hl => supportSequence_uniform_collar S c r hS j l hl⟩

end WilsonDyadicObservableFlow

namespace SU2WilsonAssemblyLocality
open SU2WilsonAssembly SU2WilsonBlockPilot WilsonDyadicObservableFlow WilsonDyadicProjection

/-- The first generic dyadic operator is the assembly's actual first mark. -/
theorem observableSequence_one (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) :
    observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 1 = firstLift N β F := by
  ext b
  change projectMap _ _ _ β (retainedSet (2^1)) F b = firstProjected N β F b
  rw [projectMap_apply, firstProjected_eq_conditional]
  rfl

/-- The second generic dyadic operator is the assembly's actual composed mark. -/
theorem observableSequence_two (N : ℕ) (β : ℝ) (F : C(FullField N, ℝ)) (b : FullField N) :
    observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 2 b = secondProjected N β F b := by
  change projectMap (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet (2^2))
    (observableSequence (volume : Measure SU2) (SU2BoundaryResponse.model (volumeIndex N) univ)
      (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β F 1) b = _
  rw [observableSequence_one, projectMap_apply]
  change WilsonConditionalProjection.project (volume : Measure SU2)
    (SU2BoundaryResponse.model (volumeIndex N) univ)
    (SU2BoundaryResponse.model_continuous (volumeIndex N) univ) β (retainedSet 4)
    (firstLift N β F) b = _
  rw [← secondProjected_eq_conditional, secondProjected_firstLift]

#print axioms WilsonDyadicObservableFlow.observableSequence_uniform_collar
#print axioms observableSequence_one
#print axioms observableSequence_two
end SU2WilsonAssemblyLocality
end Mettapedia.QuantumTheory.YangMills

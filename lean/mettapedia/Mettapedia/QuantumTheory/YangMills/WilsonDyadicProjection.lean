import Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection
import Mettapedia.QuantumTheory.YangMills.SupportGrowth

/-!
# Locality and the support recurrence of dyadic Wilson projection

The support-cover assumptions of conditional projection are discharged by
the actual plaquette/cell geometry. The resulting dependency boundary is
within `s+1` of the source at mesh `s`. Measured in successively doubled
lattice units, this gives the explicit recurrence `r' <= r/2 + 2` and a
uniform collar of four. The geometric constants are independent of volume
and coupling.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.WilsonDyadicProjection
open StrongCouplingCrossing WilsonDyadicGeometry WilsonDyadicLocality
open InhomogeneousWilsonCrossing WilsonProductLocality
variable {d n : ℕ}

/-- Exactly the retained links of the specified mesh. -/
def retainedSet (s : ℕ) : Finset (Link d n) := univ.filter (Retained s)

theorem dependency_subset_retained (s : ℕ) (S : Finset (Link d n)) :
    dependencyBoundary s S ⊆ retainedSet s := by
  intro l hl
  rcases mem_union.mp hl with h | h <;> exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩

theorem affected_disjoint_retained (s : ℕ) (S : Finset (Link d n)) :
    Disjoint (affectedInterior s S) (retainedSet s) := by
  apply disjoint_left.mpr
  intro l hl hr
  exact (mem_filter.mp hl).2.1 (mem_filter.mp hr).2

section Projection
variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Actual normalized Wilson integration is local on the explicitly constructed
boundary. All geometric side conditions are proved here. -/
theorem project_dependsOn (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (s : ℕ)
    (S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (hF : DependsOn S F) :
    DependsOn (dependencyBoundary s S)
      (WilsonConditionalProjection.project ν₀ M hφ β (retainedSet s) F) :=
  WilsonConditionalProjection.project_locality ν₀ base M hφ β (retainedSet s)
    (dependencyBoundary s S) (affectedInterior s S) S F
    (dependency_subset_retained s S) (affected_disjoint_retained s S)
    (source_covered s S) (incident_support_covered s S) hF

end Projection

/-- The radius recurrence is derived from the geometry in the new lattice
units, rather than assumed as a condition on the projection. -/
theorem radius_step {a : ℕ} (ha : 0 < a) (S : Finset (Link d n)) (c : Link d n)
    (r : ℝ) (hS : ∀ l ∈ S, dist l c ≤ (a : ℝ) * r) :
    ∀ l ∈ dependencyBoundary (2*a) S,
      dist l c ≤ ((2*a : ℕ) : ℝ) * (r / 2 + 2) := by
  intro l hl
  obtain ⟨k, hk, hdist⟩ := dependencyBoundary_radius (by omega : 0 < 2*a) S hl
  have hsrc := hS k hk
  have htri := dist_triangle l k c
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  push_cast at hdist ⊢
  nlinarith

/-- The actual finite boundary sets produced by repeated dyadic support
projection, on one fixed torus. -/
def supportSequence (S : Finset (Link d n)) : ℕ → Finset (Link d n)
  | 0 => S
  | j + 1 => dependencyBoundary (2^(j+1)) (supportSequence S j)

def radiusSequence (r : ℝ) : ℕ → ℝ
  | 0 => r
  | j + 1 => radiusSequence r j / 2 + 2

/-- Every stage of the support construction lies in its derived radius. -/
theorem supportSequence_radius (S : Finset (Link d n)) (c : Link d n) (r : ℝ)
    (hS : ∀ l ∈ S, dist l c ≤ r) :
    ∀ j, ∀ l ∈ supportSequence S j,
      dist l c ≤ (2 : ℝ)^j * radiusSequence r j := by
  intro j
  induction j with
  | zero => simpa [supportSequence, radiusSequence] using hS
  | succ j ih =>
    have h := radius_step (by positivity : 0 < 2^j) (supportSequence S j) c
      (radiusSequence r j) (by simpa using ih)
    simpa [supportSequence, radiusSequence, pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

/-- Coarsen-then-thicken gives a uniform collar of four in the rescaled metric,
independently of how many dependency-boundary steps are taken. -/
theorem supportSequence_uniform_collar (S : Finset (Link d n)) (c : Link d n) (r : ℝ)
    (hS : ∀ l ∈ S, dist l c ≤ r) (j : ℕ) (l : Link d n)
    (hl : l ∈ supportSequence S j) :
    dist l c / (2 : ℝ)^j ≤ r / (2 : ℝ)^j + 4 := by
  have hd := supportSequence_radius S c r hS j l hl
  have hr := good_support_recurrence_uniform_bound_two (r := radiusSequence r)
    (A := 2) (by norm_num) (fun _ => le_rfl) j
  have hpos : (0 : ℝ) < 2^j := by positivity
  have hdiv : dist l c / (2 : ℝ)^j ≤ radiusSequence r j := by
    apply (div_le_iff₀ hpos).mpr
    simpa only [mul_comm] using hd
  exact hdiv.trans (by norm_num [radiusSequence] at hr ⊢; exact hr)

#print axioms project_dependsOn
#print axioms radius_step
#print axioms supportSequence_uniform_collar
end Mettapedia.QuantumTheory.YangMills.WilsonDyadicProjection

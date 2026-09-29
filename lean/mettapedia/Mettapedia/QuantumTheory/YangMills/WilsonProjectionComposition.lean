import Mettapedia.QuantumTheory.YangMills.WilsonEliminationRoutes

/-!
# Composition of normalized Wilson projections

The intermediate marginal cancels against the normalization of the first
projected mark. Fubini then identifies successive projections with the
single projection integrating both interior groups. All generated weights
remain present in this identity.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Topology
namespace Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition
open WilsonBlockElimination

variable {B I J : Type*}
  [TopologicalSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  [TopologicalSpace I] [CompactSpace I] [MeasurableSpace I] [BorelSpace I]
  [SecondCountableTopology I]
  [TopologicalSpace J] [CompactSpace J] [MeasurableSpace J] [BorelSpace J]
  [SecondCountableTopology J]

omit [MeasurableSpace B] [BorelSpace B] in
/-- Exact tower identity for the actual normalized integral operators. -/
theorem project_staged (ν : Measure I) (ρ : Measure J)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (W : C((B × I) × J, ℝ)) (hW : ∀ p, 0 < W p)
    (F : C((B × I) × J, ℝ)) :
    project ν (marginal ρ W) (marginal_pos ρ W hW) (project ρ W hW F) =
      project (ν.prod ρ) (reassociate W) (fun _ => hW _) (reassociate F) := by
  have hmul : marginal ρ W * project ρ W hW F = marginal ρ (W * F) := by
    ext b
    change marginal ρ W b * (marginal ρ (W * F) b / marginal ρ W b) = _
    field_simp [(marginal_pos ρ W hW b).ne']
  ext b
  change marginal ν (marginal ρ W * project ρ W hW F) b /
    marginal ν (marginal ρ W) b = _
  rw [hmul, marginal_staged, marginal_staged]
  rfl

#print axioms project_staged
end Mettapedia.QuantumTheory.YangMills.WilsonProjectionComposition

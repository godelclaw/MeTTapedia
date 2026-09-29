import Mettapedia.QuantumTheory.YangMills.WilsonSeparator
import Mettapedia.QuantumTheory.YangMills.WilsonRectangleElimination

/-!
# Wilson separators on explicit plaquette complexes

Retaining the seam of a two-plaquette rectangle separates its two three-link
interiors. This gives exact two-observable transport for compact gauge groups
at every real coupling. The product-measure identification with the original
seven-link rectangle is explicit.

In contrast, a single mixed plaquette with gauge group `Z/2Z`, coupling `log 2`,
and two fixed identity boundary links has conditional covariance `3/5` between
its two interior link signs. Both one-marked projections are zero there.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Mettapedia.QuantumTheory.YangMills.WilsonSeparatorExamples

open WilsonBlockElimination WilsonSeparator CompactTransferGap

namespace RetainedSeam

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

abbrev ThreeLinks (E : Type*) := Fin 3 → E

/-- The retained seam followed by the left and right outer triples, reassembled
as the original six outer links and seam. No links are discarded or duplicated. -/
def reassemble (p : E × (ThreeLinks E × ThreeLinks E)) : Rectangle.Boundary E × E :=
  (Fin.append p.2.1 p.2.2, p.1)

omit [Group E] [IsTopologicalGroup E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem continuous_reassemble : Continuous (reassemble (E := E)) := by
  exact ((Fin.continuous_append 3 3).comp continuous_snd).prodMk continuous_fst

def pull (F : C(Rectangle.Boundary E × E, ℝ)) : C(E × (ThreeLinks E × ThreeLinks E), ℝ) :=
  ⟨fun p => F (reassemble p), F.continuous.comp continuous_reassemble⟩

def leftWeight (ψ : C(E, ℝ)) (β : ℝ) : C(E × ThreeLinks E, ℝ) :=
  ⟨fun p => Real.exp (-β * ψ (p.2 0 * p.1 * (p.2 1)⁻¹ * (p.2 2)⁻¹)), by fun_prop⟩

def rightWeight (ψ : C(E, ℝ)) (β : ℝ) : C(E × ThreeLinks E, ℝ) :=
  ⟨fun p => Real.exp (-β * ψ (p.2 0 * p.2 1 * (p.2 2)⁻¹ * p.1⁻¹)), by fun_prop⟩

omit [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem leftWeight_pos (ψ : C(E, ℝ)) (β : ℝ) (p : E × ThreeLinks E) :
    0 < leftWeight ψ β p := Real.exp_pos _

omit [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem rightWeight_pos (ψ : C(E, ℝ)) (β : ℝ) (p : E × ThreeLinks E) :
    0 < rightWeight ψ β p := Real.exp_pos _

omit [CompactSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- This is exactly the Wilson density of the original two plaquettes. -/
theorem separated_eq_rectangle (ψ : C(E, ℝ)) (β : ℝ) :
    separated (leftWeight ψ β) (rightWeight ψ β) =
      pull (Rectangle.density ψ ψ.continuous β) := by
  ext p
  rfl

variable (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

omit [Group E] [IsTopologicalGroup E] in
/-- The new coordinates carry precisely the original independent link law. -/
theorem integral_reassemble (F : C(Rectangle.Boundary E × E, ℝ)) :
    (∫ p, F (reassemble p)
      ∂ν₀.prod ((Measure.pi fun _ : Fin 3 => ν₀).prod (Measure.pi fun _ : Fin 3 => ν₀))) =
      ∫ p, F p ∂(Measure.pi fun _ : Fin 6 => ν₀).prod ν₀ := by
  calc
    _ = ∫ h, ∫ u : ThreeLinks E, ∫ v : ThreeLinks E, F (Fin.append u v, h)
        ∂Measure.pi (fun _ => ν₀) ∂Measure.pi (fun _ => ν₀) ∂ν₀ := by
      rw [integral_prod (fun p => F (reassemble p)) (IntegralKernel.integrable_continuous_fun _
        (show Continuous (fun p => F (reassemble p)) from F.continuous.comp continuous_reassemble))]
      apply integral_congr_ae
      exact ae_of_all ν₀ (fun h => integral_prod _
        (IntegralKernel.integrable_continuous_fun _
          (show Continuous (fun p : ThreeLinks E × ThreeLinks E => F (Fin.append p.1 p.2, h)) from
            F.continuous.comp ((Fin.continuous_append 3 3).prodMk continuous_const))))
    _ = ∫ h, ∫ b : Rectangle.Boundary E, F (b, h) ∂Measure.pi (fun _ => ν₀) ∂ν₀ := by
      apply integral_congr_ae
      exact ae_of_all ν₀ (fun h =>
        (ProductMeasure.integral_append ν₀ 3 3 (fun b => F (b, h)) (by fun_prop)).symm)
    _ = ∫ b : Rectangle.Boundary E, ∫ h, F (b, h) ∂ν₀ ∂Measure.pi (fun _ => ν₀) :=
      integral_integral_swap (IntegralKernel.integrable_continuous_fun _ (by fun_prop))
    _ = _ := (integral_prod _ (IntegralKernel.integrable_continuous_fun _ F.continuous)).symm

omit [Group E] [IsTopologicalGroup E] in
theorem expectation_reassemble (W F : C(Rectangle.Boundary E × E, ℝ)) :
    expectation
      (ν₀.prod ((Measure.pi fun _ : Fin 3 => ν₀).prod (Measure.pi fun _ : Fin 3 => ν₀)))
      (pull W) (pull F) =
      expectation ((Measure.pi fun _ : Fin 6 => ν₀).prod ν₀) W F := by
  unfold expectation
  change (∫ p, (W * F) (reassemble p) ∂_) / (∫ p, W (reassemble p) ∂_) = _
  rw [integral_reassemble, integral_reassemble]
  rfl

omit [Group E] [IsTopologicalGroup E] in
theorem covariance_reassemble (W F G : C(Rectangle.Boundary E × E, ℝ)) :
    covariance
      (ν₀.prod ((Measure.pi fun _ : Fin 3 => ν₀).prod (Measure.pi fun _ : Fin 3 => ν₀)))
      (pull W) (pull F) (pull G) =
      covariance ((Measure.pi fun _ : Fin 6 => ν₀).prod ν₀) W F G := by
  have hmul : pull F * pull G = pull (F * G) := rfl
  rw [covariance, hmul, expectation_reassemble, expectation_reassemble, expectation_reassemble]
  rfl

/-- A left observable in the original six-outer-links coordinates. -/
def originalLeft (F : C(E × ThreeLinks E, ℝ)) : C(Rectangle.Boundary E × E, ℝ) :=
  ⟨fun p => F (p.2, fun i => p.1 (Fin.castAdd 3 i)), by fun_prop⟩

def originalRight (G : C(E × ThreeLinks E, ℝ)) : C(Rectangle.Boundary E × E, ℝ) :=
  ⟨fun p => G (p.2, fun i => p.1 (Fin.natAdd 3 i)), by fun_prop⟩

omit [Group E] [IsTopologicalGroup E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem pull_originalLeft (F : C(E × ThreeLinks E, ℝ)) :
    pull (originalLeft F) = fromLeft F := by
  ext p
  simp [pull, originalLeft, reassemble, fromLeft]

omit [Group E] [IsTopologicalGroup E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
theorem pull_originalRight (G : C(E × ThreeLinks E, ℝ)) :
    pull (originalRight G) = fromRight G := by
  ext p
  simp only [pull, originalRight, reassemble, fromRight, ContinuousMap.coe_mk,
    Fin.append_right]

/-- The actual retained seam kills the conditional-covariance remainder for
all left/right observables, compact gauge groups, and real couplings. -/
theorem rectangle_fiberCovariance_zero (ψ : C(E, ℝ)) (β : ℝ)
    (F G : C(E × ThreeLinks E, ℝ)) :
    fiberCovariance
      ((Measure.pi fun _ : Fin 3 => ν₀).prod (Measure.pi fun _ : Fin 3 => ν₀))
      (separated (leftWeight ψ β) (rightWeight ψ β))
      (separated_pos _ _ (leftWeight_pos ψ β) (rightWeight_pos ψ β))
      (fromLeft F) (fromRight G) = 0 :=
  fiberCovariance_separated _ _ _ F _ G (leftWeight_pos ψ β) (rightWeight_pos ψ β)

/-- Exact two-marked transport, starting from the original seven-link Wilson
expectation and ending at the retained seam law. -/
theorem rectangle_covariance_transport (ψ : C(E, ℝ)) (β : ℝ)
    (F G : C(E × ThreeLinks E, ℝ)) :
    let ρ := (Measure.pi fun _ : Fin 3 => ν₀).prod (Measure.pi fun _ : Fin 3 => ν₀)
    let W := separated (leftWeight ψ β) (rightWeight ψ β)
    let hW := separated_pos _ _ (leftWeight_pos ψ β) (rightWeight_pos ψ β)
    covariance ((Measure.pi fun _ : Fin 6 => ν₀).prod ν₀)
      (Rectangle.density ψ ψ.continuous β) (originalLeft F) (originalRight G) =
      covariance ν₀ (marginal ρ W)
        (project ρ W hW (fromLeft F)) (project ρ W hW (fromRight G)) := by
  dsimp only
  rw [← covariance_reassemble, pull_originalLeft, pull_originalRight, ← separated_eq_rectangle]
  exact covariance_transport_exact _ _ _ _ F _ G (leftWeight_pos ψ β) (rightWeight_pos ψ β)

end RetainedSeam

namespace MixedPlaquette

open WilsonRectangleElimination (Gauge sign potential potential_continuous potential_bounds
  singleWeight singleWeight_eq_exp negative linkMeasure integral_link)

abbrev Boundary := Fin 2 → Gauge

/-- Two retained links and one eliminated link on each side. This plaquette
couples the two interiors even after its retained links are fixed. -/
def links : Fin 4 → C(Boundary × (Gauge × Gauge), Gauge) :=
  ![⟨fun p => p.2.1, continuous_of_discreteTopology⟩,
    ⟨fun p => p.2.2, continuous_of_discreteTopology⟩,
    ⟨fun p => p.1 0, continuous_of_discreteTopology⟩,
    ⟨fun p => p.1 1, continuous_of_discreteTopology⟩]

def ψ : C(Gauge, ℝ) := ⟨potential, potential_continuous⟩

def weight (β : ℝ) : C(Boundary × (Gauge × Gauge), ℝ) :=
  interaction (fun _ : Fin 1 => plaquettePotential ψ links) β

theorem weight_pos (β : ℝ) (p : Boundary × (Gauge × Gauge)) : 0 < weight β p :=
  interaction_pos _ β p

/-- The mixed factor is the actual four-link Wilson plaquette weight. -/
theorem weight_apply (β : ℝ) (p : Boundary × (Gauge × Gauge)) :
    weight β p = Real.exp (-β * potential
      (p.2.1 * p.2.2 * (p.1 0)⁻¹ * (p.1 1)⁻¹)) := by
  simp [weight, interaction, plaquettePotential, ψ, links, StrongCouplingTwist.holonomy]

theorem weight_log_two (p : Boundary × (Gauge × Gauge)) :
    weight (Real.log 2) p = singleWeight (p.2.1 * p.2.2 * (p.1 0)⁻¹ * (p.1 1)⁻¹) := by
  rw [weight_apply, singleWeight_eq_exp]

def mark : C(Boundary × Gauge, ℝ) :=
  ⟨fun p => sign p.2, continuous_of_discreteTopology⟩

theorem abs_mark_le (p : Boundary × Gauge) : |mark p| ≤ 1 := by
  change |if p.2 = 1 then (1 : ℝ) else -1| ≤ 1
  split_ifs <;> norm_num

def identityBoundary : Boundary := fun _ => 1

theorem integral_pair (f : Gauge × Gauge → ℝ) :
    (∫ p, f p ∂linkMeasure.prod linkMeasure) =
      (f (1, 1) + f (1, negative) + f (negative, 1) + f (negative, negative)) / 4 := by
  rw [integral_prod _ (.of_finite)]
  simp only [integral_link]
  ring

/-- At identity boundary the mixed plaquette creates an exact conditional
covariance of `3/5`; separate one-marked projections cannot discard it. -/
theorem fiberCovariance_at_identity :
    fiberCovariance (linkMeasure.prod linkMeasure) (weight (Real.log 2))
      (weight_pos _) (fromLeft mark) (fromRight mark) identityBoundary = 3 / 5 := by
  change covariance (linkMeasure.prod linkMeasure) ((weight (Real.log 2)).curry identityBoundary)
    ((fromLeft mark).curry identityBoundary) ((fromRight mark).curry identityBoundary) = _
  simp only [covariance, expectation, ContinuousMap.mul_apply, ContinuousMap.curry_apply]
  simp_rw [weight_log_two]
  norm_num [integral_pair, identityBoundary, fromLeft, fromRight, mark, singleWeight, sign]

theorem left_projection_at_identity :
    project (linkMeasure.prod linkMeasure) (weight (Real.log 2)) (weight_pos _)
      (fromLeft mark) identityBoundary = 0 := by
  rw [project_apply]
  simp only [expectation, ContinuousMap.curry_apply]
  simp_rw [weight_log_two]
  norm_num [integral_pair, identityBoundary, fromLeft, mark, singleWeight, sign]

theorem right_projection_at_identity :
    project (linkMeasure.prod linkMeasure) (weight (Real.log 2)) (weight_pos _)
      (fromRight mark) identityBoundary = 0 := by
  rw [project_apply]
  simp only [expectation, ContinuousMap.curry_apply]
  simp_rw [weight_log_two]
  norm_num [integral_pair, identityBoundary, fromRight, mark, singleWeight, sign]

/-- The general quantitative theorem applies to this one genuine mixed
plaquette, at every nonnegative coupling and every boundary configuration. -/
theorem remainder_bound {β : ℝ} (hβ : 0 ≤ β) (b : Boundary) :
    |fiberCovariance (linkMeasure.prod linkMeasure) (weight β) (weight_pos β)
      (fromLeft mark) (fromRight mark) b| ≤ 3 * (Real.exp (2 * β) - 1) := by
  have h := fiberCovariance_wilson_le linkMeasure linkMeasure
    (1 : C(Boundary × Gauge, ℝ)) mark (1 : C(Boundary × Gauge, ℝ)) mark
    (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    ψ potential_bounds (fun _ : Fin 1 => links) hβ
    (M := 1) (N := 1) zero_le_one zero_le_one abs_mark_le abs_mark_le b
  have hs : separated (1 : C(Boundary × Gauge, ℝ)) (1 : C(Boundary × Gauge, ℝ)) = 1 := by
    ext p
    simp [separated, fromLeft, fromRight]
  simpa only [weight, hs, one_mul, Nat.cast_one, mul_one] using h

/-- The boundary is fixed, while the two interior links have the independent
uniform reference law. This is a Wilson plaquette with fixed boundary data. -/
def fixedReference : Measure (Boundary × (Gauge × Gauge)) :=
  (Measure.dirac identityBoundary).prod (linkMeasure.prod linkMeasure)

instance : IsProbabilityMeasure fixedReference := by unfold fixedReference; infer_instance

theorem expectation_fixed (W F : C(Boundary × (Gauge × Gauge), ℝ)) :
    expectation fixedReference W F =
      expectation (linkMeasure.prod linkMeasure) (W.curry identityBoundary)
        (F.curry identityBoundary) := by
  simp only [expectation, fixedReference]
  rw [integral_prod _ (.of_finite), integral_prod _ (.of_finite)]
  simp

/-- For the actual fixed-boundary Wilson law, the full covariance is nonzero. -/
theorem fixed_covariance :
    covariance fixedReference (weight (Real.log 2)) (fromLeft mark) (fromRight mark) = 3 / 5 := by
  change expectation fixedReference (weight (Real.log 2)) (fromLeft mark * fromRight mark) -
    expectation fixedReference (weight (Real.log 2)) (fromLeft mark) *
      expectation fixedReference (weight (Real.log 2)) (fromRight mark) = _
  rw [expectation_fixed, expectation_fixed, expectation_fixed]
  exact fiberCovariance_at_identity

/-- Separate source projection loses this correlation under the fixed-boundary
law, whereas carrying the conditional covariance restores it exactly. -/
theorem fixed_transport_error :
    covariance fixedReference (weight (Real.log 2)) (fromLeft mark) (fromRight mark) -
      covariance (Measure.dirac identityBoundary)
        (marginal (linkMeasure.prod linkMeasure) (weight (Real.log 2)))
        (project (linkMeasure.prod linkMeasure) (weight (Real.log 2)) (weight_pos _) (fromLeft mark))
        (project (linkMeasure.prod linkMeasure) (weight (Real.log 2)) (weight_pos _) (fromRight mark)) =
      3 / 5 := by
  rw [fixed_covariance]
  simp [covariance, expectation, left_projection_at_identity, right_projection_at_identity]

end MixedPlaquette

#print axioms RetainedSeam.integral_reassemble
#print axioms RetainedSeam.separated_eq_rectangle
#print axioms RetainedSeam.rectangle_fiberCovariance_zero
#print axioms RetainedSeam.rectangle_covariance_transport
#print axioms MixedPlaquette.weight_apply
#print axioms MixedPlaquette.fiberCovariance_at_identity
#print axioms MixedPlaquette.left_projection_at_identity
#print axioms MixedPlaquette.right_projection_at_identity
#print axioms MixedPlaquette.remainder_bound
#print axioms MixedPlaquette.fixed_covariance
#print axioms MixedPlaquette.fixed_transport_error

end Mettapedia.QuantumTheory.YangMills.WilsonSeparatorExamples

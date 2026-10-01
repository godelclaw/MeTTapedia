import Mettapedia.QuantumTheory.YangMills.WilsonSeparatedBoundaryResponse

/-!
# Fixed-boundary integrals without dummy variables

Replacing held coordinates inside the plaquette potentials is exactly
integration over the complementary link variables. The unused held-coordinate
probability factors integrate to one. This identifies the boundary response
with the original interior-only partition function.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Topology Classical

namespace Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonSeparatedBoundaryResponse WilsonBoundaryResponse

variable {X E : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace E]

/-- Assemble prescribed boundary values with the remaining interior variables. -/
def fill (held : Finset X) (b : X → E) (i : {x // x ∉ held} → E) : X → E :=
  fun x => if h : x ∈ held then b x else i ⟨x, h⟩

def pin (held : Finset X) (b ω : X → E) : X → E :=
  fun x => if x ∈ held then b x else ω x

@[simp] theorem pin_pin (held : Finset X) (b ω : X → E) :
    pin held b (pin held b ω) = pin held b ω := by
  funext x
  by_cases hx : x ∈ held <;> simp [pin, hx]

/-- A smaller prescribed boundary can be imposed before or after selecting
the random coordinates of a larger boundary. -/
theorem pin_nested {S T : Finset X} (hTS : T ⊆ S) (b ω ω' : X → E) :
    pin S (pin T b ω) ω' = pin T b (pin S ω ω') := by
  funext x
  by_cases hx : x ∈ T
  · simp [pin, hx, hTS hx]
  · by_cases hs : x ∈ S <;> simp [pin, hx, hs]

/-- Selecting each coordinate from one of two independent product fields
preserves the product probability law. No group structure is needed. -/
theorem measurePreserving_pin (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (held : Finset X) :
    MeasurePreserving (fun p : (X → E) × (X → E) ↦ pin held p.1 p.2)
      ((Measure.pi fun _ : X ↦ ν₀).prod (Measure.pi fun _ : X ↦ ν₀))
      (Measure.pi fun _ : X ↦ ν₀) := by
  let f : X → E × E → E := fun x p ↦ if x ∈ held then p.1 else p.2
  have hf (x : X) : MeasurePreserving (f x) (ν₀.prod ν₀) ν₀ := by
    by_cases hx : x ∈ held
    · simpa only [f, hx, ↓reduceIte] using (measurePreserving_fst (μ := ν₀) (ν := ν₀))
    · simpa only [f, hx, ↓reduceIte] using (measurePreserving_snd (μ := ν₀) (ν := ν₀))
  have hp := measurePreserving_pi (fun _ : X ↦ ν₀.prod ν₀) (fun _ : X ↦ ν₀) hf
  exact hp.comp (measurePreserving_arrowProdEquivProdArrow E E X
    (fun _ ↦ ν₀) (fun _ ↦ ν₀)).symm

/-- Exact equality of the two integration conventions, for an arbitrary
integrand and any probability law on each link. -/
theorem integral_pin (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (held : Finset X) (b : X → E) (F : (X → E) → ℝ) :
    (∫ ω, F (pin held b ω) ∂Measure.pi (fun _ : X => ν₀)) =
      ∫ i, F (fill held b i) ∂Measure.pi (fun _ : {x // x ∉ held} => ν₀) := by
  letI : Fintype {x : X // x ∈ held} := Subtype.fintype (fun x => x ∈ held)
  have h := (measurePreserving_piEquivPiSubtypeProd (fun _ : X => ν₀)
    (fun x => x ∈ held)).symm.integral_comp' (fun ω => F (pin held b ω))
  rw [← h]
  have heq : (fun p : (held → E) × ({x // x ∉ held} → E) =>
      F (pin held b ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : X => E)
        (fun x => x ∈ held)).symm p))) = fun p => F (fill held b p.2) := by
    funext p
    apply congrArg F
    funext x
    by_cases hx : x ∈ held <;>
      simp [pin, fill, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd_symm_apply, hx]
  rw [heq]
  simpa using (integral_fun_snd
    (μ := Measure.pi (fun _ : {x : X // x ∈ held} => ν₀))
    (ν := Measure.pi (fun _ : {x // x ∉ held} => ν₀))
    (fun i => F (fill held b i)))

section Continuous
variable [TopologicalSpace E] [CompactSpace E] [BorelSpace E] [SecondCountableTopology E]
  {d : ℕ}

/-- The common continuous assembly map for arbitrary finite held sets. -/
def pinMap (held : Finset X) : C((X → E) × (X → E), X → E) :=
  ⟨fun p ↦ pin held p.1 p.2, by
    apply continuous_pi
    intro x
    dsimp [pin]
    split_ifs <;> fun_prop⟩

/-- The unnormalized partial integral, kept on the original coordinates.
Coordinates outside `held` in its argument are dummy coordinates. -/
def average (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (held : Finset X)
    (F : C(X → E, ℝ)) : C(X → E, ℝ) :=
  WilsonBlockElimination.marginal (Measure.pi fun _ : X ↦ ν₀) (F.comp (pinMap held))

@[simp] theorem average_apply (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (held : Finset X) (F : C(X → E, ℝ)) (b : X → E) :
    average ν₀ held F b = ∫ ω, F (pin held b ω) ∂Measure.pi (fun _ : X ↦ ν₀) := rfl

theorem average_pos (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (held : Finset X)
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) : ∀ b, 0 < average ν₀ held W b :=
  WilsonBlockElimination.marginal_pos _ _ (fun p ↦ hW _)

theorem average_local (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (held : Finset X)
    (F : C(X → E, ℝ)) : DependsOn held (average ν₀ held F) := by
  intro b b' hb
  apply integral_congr_ae
  filter_upwards [] with ω
  apply congrArg F
  funext x
  change pin held b ω x = pin held b' ω x
  by_cases hx : x ∈ held
  · simpa only [pin, hx, ↓reduceIte] using hb x hx
  · simp only [pin, hx, ↓reduceIte]

/-- Integrating the generated marginal gives the original normalization. -/
theorem integral_average (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (held : Finset X)
    (F : C(X → E, ℝ)) :
    (∫ b, average ν₀ held F b ∂Measure.pi (fun _ : X ↦ ν₀)) =
      ∫ ω, F ω ∂Measure.pi (fun _ : X ↦ ν₀) := by
  let μ := Measure.pi (fun _ : X ↦ ν₀)
  have hp := measurePreserving_pin ν₀ held
  have hi := integral_map_of_stronglyMeasurable (μ := μ.prod μ)
    hp.measurable F.continuous.stronglyMeasurable
  rw [hp.map_eq] at hi
  change (∫ b, ∫ ω, F (pin held b ω) ∂μ ∂μ) = _
  rw [← integral_prod (fun p : (X → E) × (X → E) ↦ F (pin held p.1 p.2))
    (CompactTransferGap.IntegralKernel.integrable_continuous_fun (μ.prod μ)
      (F.continuous.comp (pinMap held).continuous))]
  exact hi.symm

/-- Arbitrary nested held sets give an exact tower for unnormalized
integrals. The source density need not have Wilson form. -/
theorem average_nested (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {S T : Finset X} (hTS : T ⊆ S) (F : C(X → E, ℝ)) :
    average ν₀ T (average ν₀ S F) = average ν₀ T F := by
  ext b
  let G : C(X → E, ℝ) :=
    ⟨fun ω ↦ F (pin T b ω), F.continuous.comp ((pinMap T).continuous.comp
      (continuous_const.prodMk continuous_id))⟩
  have h := integral_average ν₀ S G
  change (∫ ω, ∫ ω', F (pin S (pin T b ω) ω') ∂Measure.pi (fun _ : X ↦ ν₀)
    ∂Measure.pi (fun _ : X ↦ ν₀)) = _
  simp_rw [pin_nested hTS]
  exact h

/-- Normalized integration against the actual supplied positive density. -/
def weightedProject (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X)
    (F : C(X → E, ℝ)) : C(X → E, ℝ) :=
  WilsonBlockElimination.project (Measure.pi fun _ : X ↦ ν₀)
    (W.comp (pinMap held)) (fun p ↦ hW _) (F.comp (pinMap held))

theorem weightedProject_congr_density (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    {W V : C(X → E, ℝ)} (hWV : W = V) (hW : ∀ ω, 0 < W ω) (hV : ∀ ω, 0 < V ω)
    (held : Finset X) (F : C(X → E, ℝ)) :
    weightedProject ν₀ W hW held F = weightedProject ν₀ V hV held F := by
  cases hWV
  rfl

def weightedProjectLinear (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X) :
    C(X → E, ℝ) →ₗ[ℝ] C(X → E, ℝ) where
  toFun := weightedProject ν₀ W hW held
  map_add' F G := by
    ext b
    exact WilsonBlockElimination.expectation_add (Measure.pi fun _ : X ↦ ν₀)
      ((W.comp (pinMap held)).curry b)
      ((F.comp (pinMap held)).curry b) ((G.comp (pinMap held)).curry b)
  map_smul' c F := by
    ext b
    exact WilsonBlockElimination.expectation_const_mul (Measure.pi fun _ : X ↦ ν₀)
      ((W.comp (pinMap held)).curry b) ((F.comp (pinMap held)).curry b) c

theorem abs_weightedProject_le (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X)
    (F : C(X → E, ℝ)) {B : ℝ} (hF : ∀ ω, |F ω| ≤ B) :
    ∀ b, |weightedProject ν₀ W hW held F b| ≤ B :=
  WilsonBlockElimination.abs_project_le _ _ _ _ (fun p ↦ hF _)

theorem weightedProject_local (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X)
    (F : C(X → E, ℝ)) : DependsOn held (weightedProject ν₀ W hW held F) := by
  intro b b' hb
  change average ν₀ held (W * F) b / average ν₀ held W b =
    average ν₀ held (W * F) b' / average ν₀ held W b'
  rw [average_local ν₀ held (W * F) b b' hb, average_local ν₀ held W b b' hb]

theorem average_mul_of_local (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (held : Finset X) (W F : C(X → E, ℝ)) (hF : DependsOn held F) :
    average ν₀ held (W * F) = average ν₀ held W * F := by
  ext b
  have hf (ω : X → E) : F (pin held b ω) = F b :=
    hF _ _ (by intro x hx; simp [pin, hx])
  simp only [average_apply, ContinuousMap.mul_apply, hf]
  exact integral_mul_const _ _

theorem average_mul_weightedProject (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X)
    (F : C(X → E, ℝ)) :
    average ν₀ held W * weightedProject ν₀ W hW held F = average ν₀ held (W * F) := by
  ext b
  change average ν₀ held W b * (average ν₀ held (W * F) b / average ν₀ held W b) = _
  exact mul_div_cancel₀ _ (average_pos ν₀ held W hW b).ne'

/-- Direct and staged weighted integration agree for any two nested
boundaries, with the intermediate generated density explicitly present. -/
theorem weightedProject_nested (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) {S T : Finset X} (hTS : T ⊆ S)
    (F : C(X → E, ℝ)) :
    weightedProject ν₀ (average ν₀ S W) (average_pos ν₀ S W hW) T
      (weightedProject ν₀ W hW S F) = weightedProject ν₀ W hW T F := by
  ext b
  change average ν₀ T (average ν₀ S W * weightedProject ν₀ W hW S F) b /
    average ν₀ T (average ν₀ S W) b = _
  rw [average_mul_weightedProject, average_nested ν₀ hTS, average_nested ν₀ hTS]
  rfl

/-- The same tower expressed as conditional expectations of the original
law. The generated-weight tower above supplies its exact interpretation. -/
theorem weightedProject_nested_original (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) {S T : Finset X} (hTS : T ⊆ S)
    (F : C(X → E, ℝ)) :
    weightedProject ν₀ W hW T (weightedProject ν₀ W hW S F) =
      weightedProject ν₀ W hW T F := by
  have hnum : average ν₀ T (W * weightedProject ν₀ W hW S F) = average ν₀ T (W * F) := by
    rw [← average_nested ν₀ hTS (W * weightedProject ν₀ W hW S F),
      average_mul_of_local ν₀ S W _ (weightedProject_local ν₀ W hW S F),
      average_mul_weightedProject, average_nested ν₀ hTS]
  ext b
  change average ν₀ T (W * weightedProject ν₀ W hW S F) b / average ν₀ T W b = _
  rw [hnum]
  rfl

theorem expectation_weightedProject (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : Finset X)
    (F : C(X → E, ℝ)) :
    WilsonBlockElimination.expectation (Measure.pi fun _ : X ↦ ν₀) (average ν₀ held W)
      (weightedProject ν₀ W hW held F) =
      WilsonBlockElimination.expectation (Measure.pi fun _ : X ↦ ν₀) W F := by
  unfold WilsonBlockElimination.expectation
  change (∫ b, (average ν₀ held W * weightedProject ν₀ W hW held F) b
    ∂Measure.pi (fun _ : X ↦ ν₀)) / (∫ b, average ν₀ held W b ∂Measure.pi (fun _ : X ↦ ν₀)) = _
  rw [average_mul_weightedProject, integral_average, integral_average]
  rfl

/-- Successive unnormalized integrations. Each term is the actual generated
density used in the following step. The sequence stays on one fixed lattice. -/
def densitySequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (held : ℕ → Finset X) : ℕ → C(X → E, ℝ)
  | 0 => W
  | j + 1 => average ν₀ (held j) (densitySequence ν₀ W held j)

theorem densitySequence_pos (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X) :
    ∀ j b, 0 < densitySequence ν₀ W held j b := by
  intro j
  induction j with
  | zero => exact hW
  | succ j ih => exact average_pos ν₀ (held j) _ ih

theorem densitySequence_eq_direct (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (held : ℕ → Finset X)
    (hnested : ∀ j, held (j + 1) ⊆ held j) :
    ∀ j, densitySequence ν₀ W held (j + 1) = average ν₀ (held j) W := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change average ν₀ (held (j + 1)) (densitySequence ν₀ W held (j + 1)) = _
    rw [ih, average_nested ν₀ (hnested j)]

/-- Mark transport under the successive generated densities, without
replacing an effective interaction by a Wilson-form approximation. -/
def markSequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (F : C(X → E, ℝ)) : ℕ → C(X → E, ℝ)
  | 0 => F
  | j + 1 => weightedProject ν₀ (densitySequence ν₀ W held j)
      (densitySequence_pos ν₀ W hW held j) (held j) (markSequence ν₀ W hW held F j)

/-- Every finite nested sequence equals the direct normalized integral.
This applies to every continuous mark, hence to products of any finite
number of original marks, without an assumption on higher cumulant bounds. -/
theorem markSequence_eq_direct (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (hnested : ∀ j, held (j + 1) ⊆ held j) (F : C(X → E, ℝ)) :
    ∀ j, markSequence ν₀ W hW held F (j + 1) = weightedProject ν₀ W hW (held j) F := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    change weightedProject ν₀ (densitySequence ν₀ W held (j + 1))
      (densitySequence_pos ν₀ W hW held (j + 1)) (held (j + 1))
      (markSequence ν₀ W hW held F (j + 1)) = _
    rw [ih]
    exact (weightedProject_congr_density ν₀ (densitySequence_eq_direct ν₀ W held hnested j)
      _ (average_pos ν₀ (held j) W hW) _ _).trans
      (weightedProject_nested ν₀ W hW (hnested j) F)

theorem expectation_markSequence (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (W : C(X → E, ℝ)) (hW : ∀ ω, 0 < W ω) (held : ℕ → Finset X)
    (F : C(X → E, ℝ)) :
    ∀ j, WilsonBlockElimination.expectation (Measure.pi fun _ : X ↦ ν₀)
      (densitySequence ν₀ W held j) (markSequence ν₀ W hW held F j) =
      WilsonBlockElimination.expectation (Measure.pi fun _ : X ↦ ν₀) W F := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    exact (expectation_weightedProject ν₀ _ (densitySequence_pos ν₀ W hW held j)
      (held j) _).trans ih

theorem realDensity_pinned_apply (M : Model d E) (hφ : ∀ p, Continuous (M.φ p))
    (β : ℝ) (held : Finset (Link d M.n)) (b ω : Link d M.n → E) :
    realDensity (M.pinned held b) (continuous_pinned M hφ held b) β ω =
      realDensity M hφ β (pin held b ω) := rfl

/-- The partition function used in the spatial response theorem is exactly
the partition function integrating only the unheld links. -/
theorem boundaryLogPartition_eq_interior (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E) :
    boundaryLogPartition ν₀ M hφ β held b =
      Real.log (∫ i, realDensity M hφ β (fill held b i)
        ∂Measure.pi (fun _ : {l : Link d M.n // l ∉ held} => ν₀)) := by
  unfold boundaryLogPartition logPartition
  simp_rw [realDensity_pinned_apply M hφ β held b]
  rw [integral_pin]

end Continuous
#print axioms integral_pin
#print axioms boundaryLogPartition_eq_interior
end Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral

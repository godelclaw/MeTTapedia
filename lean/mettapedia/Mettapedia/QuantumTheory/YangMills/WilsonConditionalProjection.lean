import Mettapedia.QuantumTheory.YangMills.WilsonProductLocality
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicLocality
import Mettapedia.Combinatorics.PolymerGas.PlaquetteSmallness

/-!
# Conditional Wilson projection depends only on the geometric boundary

At fixed retained coordinates, plaquettes incident to an affected interior
component form a local density. The complementary plaquettes involve no
variables in that component and cancel from the normalized expectation.
The dependence of the projected mark is then read from the original
plaquette supports, with no coupling restriction.

For ordered two-link blocking, the unweighted Haar projection of a local
interaction depends only on pairs fully contained in its support. Regrouping
by these retained supports gives a strict, volume-independent contraction in
the exponential support-cardinality norm. The full nonlinear logarithm is
controlled by connected conditional activities and an all-order polymer
majorant. At input radius at most `1/2`, exact vacuum extraction produces a
centered local family whose norm with weight `exp(8 |S|)` is at most
`4 exp(-2)` times the input radius. The constants are independent of volume.
The same contraction holds with an additional spatial tree-length weight
when the blocking chart admits a nonexpanding projection identifying each
link pair. These are uniform norms of interaction functions; derivative
seminorms require their own estimates.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonBoundaryChanges WilsonPinnedIntegral WilsonPatchGeometry
open WilsonProductLocality WilsonBlockElimination

section Pinned

variable {E : Type*} [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {d n : ℕ}

/-- A full mark with the prescribed boundary coordinates substituted. -/
def pinnedMark (held : Finset (Link d n)) (b : Link d n → E)
    (F : C(Link d n → E, ℝ)) : C(Link d n → E, ℝ) :=
  ⟨fun ω => F (pin held b ω), F.continuous.comp (by
    apply continuous_pi
    intro l
    dsimp [pin]
    split_ifs <;> fun_prop)⟩

/-- Fixing boundary coordinates preserves an observable's original support. -/
theorem pinnedMark_local (held S : Finset (Link d n)) (b : Link d n → E)
    (F : C(Link d n → E, ℝ)) (hF : DependsOn S F) :
    DependsOn S (pinnedMark held b F) := by
  intro ω ω' h
  apply hF
  intro l hl
  dsimp only [pin]
  split_ifs
  · rfl
  · exact h l hl

/-- The chosen subset of original plaquette factors at fixed boundary values. -/
def partialDensity (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E)
    (P : Finset (Plaquette d M.n)) : C(Link d M.n → E, ℝ) :=
  ⟨fun ω => Real.exp (-β * ∑ p ∈ P, pinnedPotential M held b p ω),
    (continuous_const.mul (continuous_finsetSum _ fun p _ =>
      continuous_pinnedPotential M hφ held b p)).rexp⟩

theorem partialDensity_pos (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E)
    (P : Finset (Plaquette d M.n)) (ω : Link d M.n → E) :
    0 < partialDensity M hφ β held b P ω := Real.exp_pos _

theorem density_factorization (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (b : Link d M.n → E) (P : Finset (Plaquette d M.n)) :
    realDensity (M.pinned held b) (continuous_pinned M hφ held b) β =
      partialDensity M hφ β held b P * partialDensity M hφ β held b Pᶜ := by
  ext ω
  rw [ContinuousMap.mul_apply, realDensity_pinned_eq_exp M hφ β held b ω]
  change Real.exp _ = Real.exp _ * Real.exp _
  rw [← Real.exp_add, ← mul_add, sum_add_sum_compl]

omit [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
/-- Agreement on the unheld part of a local support gives agreement after
pinning all its retained coordinates. -/
theorem pin_agree_of_cover (held B J S : Finset (Link d n))
    (hB : B ⊆ held) (hS : S ⊆ B ∪ J) (b ω ω' : Link d n → E)
    (h : ∀ l ∈ J, ω l = ω' l) : ∀ l ∈ S, pin held b ω l = pin held b ω' l := by
  intro l hl
  by_cases hheld : l ∈ held
  · simp [pin, hheld]
  · have hJ : l ∈ J := (mem_union.mp (hS hl)).resolve_left (fun hlB => hheld (hB hlB))
    simp [pin, hheld, h l hJ]

omit [TopologicalSpace E] [CompactSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] in
/-- Only the retained boundary part of a local component can affect its
integrand when its interior variables are held equal. -/
theorem pin_boundary_agree (held B J S : Finset (Link d n))
    (hJ : Disjoint J held) (hS : S ⊆ B ∪ J) (b b' ω : Link d n → E)
    (hb : ∀ l ∈ B, b l = b' l) : ∀ l ∈ S, pin held b ω l = pin held b' ω l := by
  intro l hl
  by_cases hheld : l ∈ held
  · have hlB : l ∈ B := (mem_union.mp (hS hl)).resolve_right
      (fun hlJ => disjoint_left.mp hJ hlJ hheld)
    simp [pin, hheld, hb l hlB]
  · simp [pin, hheld]

omit [TopologicalSpace E] [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem pinnedPotential_eq_pin (M : Model d E) (held : Finset (Link d M.n))
    (b ω : Link d M.n → E) (p : Plaquette d M.n) :
    pinnedPotential M held b p ω = potential (M.φ p) p (pin held b ω) := rfl

omit [TopologicalSpace E] [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem potential_agree (M : Model d E) (p : Plaquette d M.n)
    (ω ω' : Link d M.n → E) (h : ∀ l ∈ support p, ω l = ω' l) :
    potential (M.φ p) p ω = potential (M.φ p) p ω' := by
  apply congrArg (M.φ p)
  funext i
  exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

theorem partialDensity_depends (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held B J : Finset (Link d M.n)) (b : Link d M.n → E)
    (P : Finset (Plaquette d M.n)) (hB : B ⊆ held)
    (hP : ∀ p ∈ P, support p ⊆ B ∪ J) :
    DependsOn J (partialDensity M hφ β held b P) := by
  intro ω ω' h
  apply congrArg (fun x => Real.exp (-β * x))
  apply sum_congr rfl
  intro p hp
  rw [pinnedPotential_eq_pin, pinnedPotential_eq_pin]
  exact potential_agree M p _ _ (pin_agree_of_cover held B J _ hB (hP p hp) b ω ω' h)

theorem exteriorDensity_dependsOff (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held J : Finset (Link d M.n)) (b : Link d M.n → E) :
    DependsOff J (partialDensity M hφ β held b (incident J)ᶜ) := by
  intro ω ω' h
  apply congrArg (fun x => Real.exp (-β * x))
  apply sum_congr rfl
  intro p hp
  apply pinnedPotential_local
  intro l hl
  exact h l (fun hlJ => (mem_compl.mp hp) (mem_incident.mpr ⟨l, hlJ, hl⟩))

/-- The normalized actual conditional Wilson expectation. -/
def project (ν₀ : Measure E) (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E) : ℝ :=
  expectation (Measure.pi fun _ => ν₀)
    (realDensity (M.pinned held b) (continuous_pinned M hφ held b) β) (pinnedMark held b F)

/-- A mark already insensitive to held dummy coordinates needs no additional
pinning inside the original conditional expectation. -/
theorem project_eq_expectation_of_pinInvariant (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E)
    (hF : ∀ ω, F (pin held b ω) = F ω) :
    project ν₀ M hφ β held F b = expectation (Measure.pi fun _ ↦ ν₀)
      (realDensity (M.pinned held b) (continuous_pinned M hφ held b) β) F := by
  have hm : pinnedMark held b F = F := ContinuousMap.ext hF
  unfold project
  rw [hm]

theorem project_eq_ratio (ν₀ : Measure E) (M : Model d E)
    (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (held : Finset (Link d M.n))
    (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E) :
    project ν₀ M hφ β held F b =
      (∫ ω, (realDensity M hφ β * F) (pin held b ω) ∂Measure.pi (fun _ => ν₀)) /
        (∫ ω, realDensity M hφ β (pin held b ω) ∂Measure.pi (fun _ => ν₀)) := rfl

theorem logPartition_eq_pin (ν₀ : Measure E) (M : Model d E)
    (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ) (held : Finset (Link d M.n))
    (b : Link d M.n → E) :
    WilsonSeparatedBoundaryResponse.boundaryLogPartition ν₀ M hφ β held b =
      Real.log (∫ ω, realDensity M hφ β (pin held b ω) ∂Measure.pi (fun _ => ν₀)) := rfl

/-- The untouched cells cancel exactly, after the closure of the affected
interior is supplied by the explicit plaquette geometry. -/
theorem project_eq_local (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held B J S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ)) (b : Link d M.n → E)
    (hB : B ⊆ held) (hS : S ⊆ B ∪ J)
    (hP : ∀ p ∈ incident J, support p ⊆ B ∪ J) (hF : DependsOn S F) :
    project ν₀ M hφ β held F b = expectation (Measure.pi fun _ => ν₀)
      (partialDensity M hφ β held b (incident J)) (pinnedMark held b F) := by
  unfold project
  rw [density_factorization M hφ β held b (incident J)]
  apply expectation_cancel_exterior ν₀ base J
    _ _ _ (partialDensity_pos M hφ β held b _) (partialDensity_pos M hφ β held b _)
    (partialDensity_depends M hφ β held B J b _ hB hP)
    _ (exteriorDensity_dependsOff M hφ β held J b)
  intro ω ω' h
  exact hF _ _ (pin_agree_of_cover held B J S hB hS b ω ω' h)

/-- The projected observable depends only on the proved boundary set `B`.
No decay, factorization, or support recurrence is an additional assumption. -/
theorem project_locality (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (M : Model d E) (hφ : ∀ p, Continuous (M.φ p)) (β : ℝ)
    (held B J S : Finset (Link d M.n)) (F : C(Link d M.n → E, ℝ))
    (hB : B ⊆ held) (hJ : Disjoint J held) (hS : S ⊆ B ∪ J)
    (hP : ∀ p ∈ incident J, support p ⊆ B ∪ J) (hF : DependsOn S F) :
    DependsOn B (project ν₀ M hφ β held F) := by
  intro b b' hb
  rw [project_eq_local ν₀ base M hφ β held B J S F b hB hS hP hF,
    project_eq_local ν₀ base M hφ β held B J S F b' hB hS hP hF]
  have hU : partialDensity M hφ β held b (incident J) =
      partialDensity M hφ β held b' (incident J) := by
    ext ω
    apply congrArg (fun x => Real.exp (-β * x))
    apply sum_congr rfl
    intro p hp
    rw [pinnedPotential_eq_pin, pinnedPotential_eq_pin]
    exact potential_agree M p _ _ (pin_boundary_agree held B J _ hJ (hP p hp) b b' ω hb)
  have hmark : pinnedMark held b F = pinnedMark held b' F := by
    ext ω
    exact hF _ _ (pin_boundary_agree held B J S hJ hS b b' ω hb)
  rw [hU, hmark]

#print axioms density_factorization
#print axioms project_eq_local
#print axioms project_locality
end Pinned

/-! ## Haar cancellation and a strict linear gain for local interactions

Before inserting an interaction density, a projected local mark can retain a
coarse product only when both fine halves belong to its support. Regrouping
centered local interactions by these smaller supports preserves their sum
exactly and contracts the exponentially weighted support norm. This is the
linear Haar operator; no nonlinear logarithmic remainder is absorbed into
its gain. All functions remain on the original compact group.
-/

namespace PairedHaar
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
variable {X I J E : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]

/-- Coarse products fully contained in the fine support. -/
def retainedSupport (e : ((I ⊕ I) ⊕ J) ≃ X) (S : Finset X) : Finset I :=
  univ.filter (fun i ↦ e (.inl (.inl i)) ∈ S ∧ e (.inl (.inr i)) ∈ S)

omit [Fintype X] [Fintype J] in
@[simp] theorem mem_retainedSupport (e : ((I ⊕ I) ⊕ J) ≃ X) (S : Finset X) (i : I) :
    i ∈ retainedSupport e S ↔ e (.inl (.inl i)) ∈ S ∧ e (.inl (.inr i)) ∈ S := by
  simp [retainedSupport]

omit [Fintype X] [Fintype J] in
theorem twice_card_retainedSupport_le (e : ((I ⊕ I) ⊕ J) ≃ X) (S : Finset X) :
    2 * (retainedSupport e S).card ≤ S.card := by
  let T := retainedSupport e S
  have hl : Function.Injective (fun i : I ↦ e (.inl (.inl i))) := by
    intro i j h
    exact Sum.inl.inj (Sum.inl.inj (e.injective h))
  have hr : Function.Injective (fun i : I ↦ e (.inl (.inr i))) := by
    intro i j h
    exact Sum.inr.inj (Sum.inl.inj (e.injective h))
  have hd : Disjoint (T.image (fun i ↦ e (.inl (.inl i))))
      (T.image (fun i ↦ e (.inl (.inr i)))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    obtain ⟨j, _, hj⟩ := mem_image.mp hy
    have hbad := e.injective hj
    simp only [Sum.inl.injEq, Sum.inr_ne_inl] at hbad
  have hs : (T.image (fun i ↦ e (.inl (.inl i)))) ∪
      (T.image (fun i ↦ e (.inl (.inr i)))) ⊆ S := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact (mem_retainedSupport e S i |>.mp hi).1
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact (mem_retainedSupport e S i |>.mp hi).2
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd, card_image_of_injective _ hl,
    card_image_of_injective _ hr] at hc
  simpa only [two_mul] using hc

variable [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def boundaryShift (e : ((I ⊕ I) ⊕ J) ≃ X) (S : Finset X) (c c' : I → E)
    (f : (I → E) × (J → E)) : (I → E) × (J → E) :=
  (fun i ↦ if e (.inl (.inl i)) ∈ S then f.1 i else c' i * (c i)⁻¹ * f.1 i, f.2)

omit [Fintype X] in
theorem measurePreserving_boundaryShift (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (S : Finset X) (c c' : I → E) :
    MeasurePreserving (boundaryShift e S c c')
      ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))
      ((Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν)) := by
  have hm : MeasurePreserving
      (fun a : I → E ↦ fun i ↦ if e (.inl (.inl i)) ∈ S then a i else c' i * (c i)⁻¹ * a i)
      (Measure.pi fun _ : I ↦ ν) (Measure.pi fun _ : I ↦ ν) := by
    apply measurePreserving_pi (fun _ : I ↦ ν) (fun _ : I ↦ ν)
      (f := fun i x ↦ if e (.inl (.inl i)) ∈ S then x else c' i * (c i)⁻¹ * x)
    intro i
    by_cases hi : e (.inl (.inl i)) ∈ S
    · simp only [hi, ↓reduceIte]
      exact MeasurePreserving.id ν
    · simpa only [hi, ↓reduceIte] using measurePreserving_mul_left ν (c' i * (c i)⁻¹)
  exact hm.prod (MeasurePreserving.id _)

omit [CompactSpace E] [Fintype X] [Fintype J] in
theorem chart_agree_on_support (e : ((I ⊕ I) ⊕ J) ≃ X) (S : Finset X)
    (c c' : I → E) (hc : ∀ i ∈ retainedSupport e S, c i = c' i)
    (f : (I → E) × (J → E)) :
    ∀ x ∈ S, chart e (c', boundaryShift e S c c' f) x = chart e (c, f) x := by
  intro x hx
  obtain ⟨s, rfl⟩ := e.surjective x
  rcases s with (i | i) | j
  · simp only [chart_first, boundaryShift, hx, ↓reduceIte]
  · rw [chart_second, chart_second]
    by_cases hi : e (.inl (.inl i)) ∈ S
    · have hh := hc i ((mem_retainedSupport e S i).mpr ⟨hi, hx⟩)
      simp only [boundaryShift, hi, ↓reduceIte, hh]
    · simp only [boundaryShift, hi, ↓reduceIte]
      group
  · simp only [chart_unused, boundaryShift]

theorem blockedDensity_local (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (S : Finset X) (F : C(X → E, ℝ)) (hF : DependsOn S F) :
    DependsOn (retainedSupport e S) (blockedDensity ν e F) := by
  intro c c' hc
  let μ := (Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν)
  let H : C((I → E) × (J → E), ℝ) :=
    ⟨fun f ↦ F (chart e (c', f)), F.continuous.comp
      ((continuous_chart e).comp (continuous_const.prodMk continuous_id))⟩
  have hm := measurePreserving_boundaryShift ν e S c c'
  have hi := integral_map_of_stronglyMeasurable (μ := μ) hm.measurable H.continuous.stronglyMeasurable
  rw [hm.map_eq] at hi
  change (∫ f, F (chart e (c, f)) ∂μ) = ∫ f, H f ∂μ
  rw [hi]
  apply integral_congr_ae
  filter_upwards [] with f
  exact (hF _ _ (chart_agree_on_support e S c c' hc f)).symm

theorem blockedDensity_eq_zero (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (S : Finset X) (F : C(X → E, ℝ)) (hlocal : DependsOn S F)
    (hcenter : (∫ U, F U ∂Measure.pi (fun _ : X ↦ ν)) = 0)
    (hsupport : retainedSupport e S = ∅) : blockedDensity ν e F = 0 := by
  ext c
  have hl := blockedDensity_local ν e S F hlocal
  rw [hsupport] at hl
  have hc (c' : I → E) : blockedDensity ν e F c' = blockedDensity ν e F c := hl c' c (by simp)
  have hi := integral_blockedDensity ν e F
  simp_rw [hc] at hi
  simpa [hcenter] using hi

omit [Fintype X] [DecidableEq X] in
theorem abs_blockedDensity_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (F : C(X → E, ℝ)) {B : ℝ}
    (hF : ∀ U, |F U| ≤ B) (c : I → E) : |blockedDensity ν e F c| ≤ B := by
  change |∫ f, F (chart e (c, f)) ∂(Measure.pi fun _ : I ↦ ν).prod
    (Measure.pi fun _ : J ↦ ν)| ≤ B
  have h := norm_integral_le_of_norm_le_const
    (μ := (Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν))
    (f := fun f ↦ F (chart e (c, f))) (C := B) (by
      filter_upwards [] with f
      exact hF _)
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

omit [Fintype X] [DecidableEq X] in
theorem norm_blockedDensity_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (F : C(X → E, ℝ)) : ‖blockedDensity ν e F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).mpr
  intro c
  exact abs_blockedDensity_le ν e F (fun U ↦ F.norm_coe_le_norm U) c

section WeightedNorms
omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Y : Type*} [Fintype Y] [DecidableEq Y]

def weightedInteractionRow (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S) (i : Y) :
    Seminorm ℝ (Finset Y → C(Y → E, ℝ)) :=
  Seminorm.of (fun Φ ↦ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S), w S * ‖Φ S‖)
    (fun Φ Ψ ↦ by
      calc
        _ ≤ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S), w S * (‖Φ S‖ + ‖Ψ S‖) :=
          Finset.sum_le_sum (fun S _ ↦ mul_le_mul_of_nonneg_left (norm_add_le _ _) (hw S))
        _ = _ := by simp only [mul_add, Finset.sum_add_distrib])
    (fun c Φ ↦ by
      simp only [Pi.smul_apply, norm_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring)

@[simp] theorem weightedInteractionRow_apply (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S) (i : Y)
    (Φ : Finset Y → C(Y → E, ℝ)) :
    weightedInteractionRow w hw i Φ = ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S), w S * ‖Φ S‖ := rfl

def weightedInteractionNorm (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S) :
    Seminorm ℝ (Finset Y → C(Y → E, ℝ)) := Finset.univ.sup (weightedInteractionRow w hw)

theorem weightedInteractionRow_le (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S) (i : Y)
    (Φ : Finset Y → C(Y → E, ℝ)) :
    weightedInteractionRow w hw i Φ ≤ weightedInteractionNorm w hw Φ :=
  Seminorm.le_finset_sup_apply (Finset.mem_univ i)

theorem weightedInteractionNorm_le (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S)
    (Φ : Finset Y → C(Y → E, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, weightedInteractionRow w hw i Φ ≤ C) : weightedInteractionNorm w hw Φ ≤ C :=
  Seminorm.finset_sup_apply_le hC (fun i _ ↦ h i)

end WeightedNorms

def interactionRow {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ) (i : Y) :
    Seminorm ℝ (Finset Y → C(Y → E, ℝ)) :=
  weightedInteractionRow (fun S ↦ Real.exp (a * S.card)) (fun _ ↦ (Real.exp_pos _).le) i

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
@[simp] theorem interactionRow_apply {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ) (i : Y)
    (Φ : Finset Y → C(Y → E, ℝ)) :
    interactionRow a i Φ = ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
      Real.exp (a * S.card) * ‖Φ S‖ := rfl

/-- Maximum per-link total interaction size, with exponential support-cardinality
weight. The empty-support constant is invisible and is controlled separately. -/
def interactionNorm {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ) :
    Seminorm ℝ (Finset Y → C(Y → E, ℝ)) := Finset.univ.sup (interactionRow a)

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem interactionRow_le {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ) (i : Y)
    (Φ : Finset Y → C(Y → E, ℝ)) : interactionRow a i Φ ≤ interactionNorm a Φ :=
  Seminorm.le_finset_sup_apply (Finset.mem_univ i)

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem interactionNorm_le {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ)
    (Φ : Finset Y → C(Y → E, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, interactionRow a i Φ ≤ C) : interactionNorm a Φ ≤ C :=
  Seminorm.finset_sup_apply_le hC (fun i _ ↦ h i)

section SpatialNorms
open Mettapedia.Combinatorics.PolymerGas
omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Y : Type*} [Fintype Y] [DecidableEq Y]
variable [PseudoMetricSpace Y]

def spatialInteractionRow (a η : ℝ) (i : Y) : Seminorm ℝ (Finset Y → C(Y → E, ℝ)) :=
  weightedInteractionRow (fun S => Real.exp (a*S.card + η*treeLength S)) (fun _ => (Real.exp_pos _).le) i

def spatialInteractionNorm (a η : ℝ) : Seminorm ℝ (Finset Y → C(Y → E, ℝ)) :=
  weightedInteractionNorm (fun S => Real.exp (a*S.card + η*treeLength S)) (fun _ => (Real.exp_pos _).le)

@[simp] theorem spatialInteractionRow_apply (a η : ℝ) (i : Y) (Φ : Finset Y → C(Y → E, ℝ)) :
    spatialInteractionRow a η i Φ =
      ∑ S ∈ univ.filter (fun S : Finset Y => i ∈ S), Real.exp (a*S.card + η*treeLength S) * ‖Φ S‖ := rfl

theorem spatialInteractionRow_le (a η : ℝ) (i : Y) (Φ : Finset Y → C(Y → E, ℝ)) :
    spatialInteractionRow a η i Φ ≤ spatialInteractionNorm a η Φ := weightedInteractionRow_le _ _ _ _

theorem spatialInteractionNorm_le (a η : ℝ) (Φ : Finset Y → C(Y → E, ℝ))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, spatialInteractionRow a η i Φ ≤ C) :
    spatialInteractionNorm a η Φ ≤ C := weightedInteractionNorm_le _ _ _ hC h

theorem interactionNorm_le_spatial (a : ℝ) {η : ℝ} (hη : 0 ≤ η) (Φ : Finset Y → C(Y → E, ℝ)) :
    interactionNorm a Φ ≤ spatialInteractionNorm a η Φ := by
  apply interactionNorm_le _ _ (by positivity)
  intro i
  apply le_trans (b := spatialInteractionRow a η i Φ) ?_ (spatialInteractionRow_le _ _ _ _)
  apply sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg hη (treeLength_nonneg S)
  linarith

end SpatialNorms

section Regroup
variable {Y P : Type*} [Fintype Y] [DecidableEq Y] [Fintype P]

def regroupInteraction (support : P → Finset Y) (F : P → C(Y → E, ℝ))
    (S : Finset Y) : C(Y → E, ℝ) := ∑ p ∈ univ.filter (fun p ↦ support p = S), F p

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompactSpace E] in
theorem sum_regroupInteraction (support : P → Finset Y) (F : P → C(Y → E, ℝ)) :
    ∑ S, regroupInteraction support F S = ∑ p, F p := by
  unfold regroupInteraction
  rw [Finset.sum_fiberwise_of_maps_to (fun p _ ↦ mem_univ (support p))]

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Fintype Y] [CompactSpace E] in
theorem regroupInteraction_local (support : P → Finset Y) (F : P → C(Y → E, ℝ))
    (hF : ∀ p, DependsOn (support p) (F p)) (S : Finset Y) :
    DependsOn S (regroupInteraction support F S) := by
  intro U V h
  simp only [regroupInteraction, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  exact hF p U V ((mem_filter.mp hp).2 ▸ h)

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem weightedInteractionRow_regroup_le (support : P → Finset Y) (F : P → C(Y → E, ℝ))
    (w : Finset Y → ℝ) (hw : ∀ S, 0 ≤ w S) (i : Y) :
    weightedInteractionRow w hw i (regroupInteraction support F) ≤
      ∑ p ∈ univ.filter (fun p ↦ i ∈ support p), w (support p) * ‖F p‖ := by
  calc
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
        ∑ p ∈ univ.filter (fun p ↦ support p = S), w S * ‖F p‖ := by
      apply Finset.sum_le_sum
      intro S _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw S)
    _ = ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
        ∑ p ∈ univ.filter (fun p ↦ support p = S), w (support p) * ‖F p‖ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := by
      simpa only [mem_filter, mem_univ, true_and] using
        Finset.sum_fiberwise_eq_sum_filter (univ : Finset P)
          (univ.filter (fun S : Finset Y ↦ i ∈ S)) support
          (fun p ↦ w (support p) * ‖F p‖)

omit [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem interactionRow_regroup_le (support : P → Finset Y) (F : P → C(Y → E, ℝ))
    (a : ℝ) (i : Y) :
    interactionRow a i (regroupInteraction support F) ≤
      ∑ p ∈ univ.filter (fun p ↦ i ∈ support p), Real.exp (a * (support p).card) * ‖F p‖ :=
  weightedInteractionRow_regroup_le support F _ _ i

end Regroup

def blockedInteraction (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ)) (T : Finset I) : C(I → E, ℝ) :=
  regroupInteraction (retainedSupport e) (fun S ↦ blockedDensity ν e (Φ S)) T

theorem blockedInteraction_local (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (Φ : Finset X → C(X → E, ℝ)) (hΦ : ∀ S, DependsOn S (Φ S)) (T : Finset I) :
    DependsOn T (blockedInteraction ν e Φ T) := by
  intro c c' hc
  simp only [blockedInteraction, regroupInteraction, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro S hS
  have he := (mem_filter.mp hS).2
  exact blockedDensity_local ν e S (Φ S) (hΦ S) c c' (he ▸ hc)

theorem blockedInteraction_norm_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ)) (T : Finset I) :
    ‖blockedInteraction ν e Φ T‖ ≤
      ∑ S ∈ univ.filter (fun S : Finset X ↦ retainedSupport e S = T), ‖Φ S‖ := by
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun S _ ↦ norm_blockedDensity_le ν e (Φ S))

theorem interactionRow_blocked_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ)) (a : ℝ) (ha : 0 ≤ a) (i : I) :
    interactionRow a i (blockedInteraction ν e Φ) ≤
      Real.exp (-a) * interactionRow a (e (.inl (.inl i))) Φ := by
  have he (S : Finset X) (hi : i ∈ retainedSupport e S) :
      Real.exp (a * (retainedSupport e S).card) ≤ Real.exp (-a) * Real.exp (a * S.card) := by
    have hcard := twice_card_retainedSupport_le e S
    have hpos := card_pos.mpr (show (retainedSupport e S).Nonempty from ⟨i, hi⟩)
    have hle : (retainedSupport e S).card + 1 ≤ S.card := by omega
    have hle' : ((retainedSupport e S).card : ℝ) + 1 ≤ S.card := by exact_mod_cast hle
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ ∑ T ∈ univ.filter (fun T : Finset I ↦ i ∈ T),
        ∑ S ∈ univ.filter (fun S : Finset X ↦ retainedSupport e S = T),
          Real.exp (a * T.card) * ‖Φ S‖ := by
      apply Finset.sum_le_sum
      intro T _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (blockedInteraction_norm_le ν e Φ T) (Real.exp_pos _).le
    _ = ∑ T ∈ univ.filter (fun T : Finset I ↦ i ∈ T),
        ∑ S ∈ univ.filter (fun S : Finset X ↦ retainedSupport e S = T),
          Real.exp (a * (retainedSupport e S).card) * ‖Φ S‖ := by
      apply Finset.sum_congr rfl
      intro T _
      apply Finset.sum_congr rfl
      intro S hS
      rw [(mem_filter.mp hS).2]
    _ = ∑ S ∈ univ.filter (fun S : Finset X ↦ i ∈ retainedSupport e S),
        Real.exp (a * (retainedSupport e S).card) * ‖Φ S‖ := by
      simpa only [mem_filter, mem_univ, true_and] using
        Finset.sum_fiberwise_eq_sum_filter (univ : Finset (Finset X))
          (univ.filter (fun T : Finset I ↦ i ∈ T)) (retainedSupport e)
          (fun S ↦ Real.exp (a * (retainedSupport e S).card) * ‖Φ S‖)
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset X ↦ i ∈ retainedSupport e S),
        Real.exp (-a) * (Real.exp (a * S.card) * ‖Φ S‖) := by
      apply Finset.sum_le_sum
      intro S hS
      exact (mul_le_mul_of_nonneg_right (he S (mem_filter.mp hS).2) (norm_nonneg _)).trans_eq
        (mul_assoc _ _ _)
    _ = Real.exp (-a) * ∑ S ∈ univ.filter (fun S : Finset X ↦ i ∈ retainedSupport e S),
        Real.exp (a * S.card) * ‖Φ S‖ := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-a) * interactionRow a (e (.inl (.inl i))) Φ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        exact mem_filter.mpr ⟨mem_univ _, ((mem_retainedSupport e S i).mp (mem_filter.mp hS).2).1⟩
      · intro S _ _
        positivity

theorem interactionNorm_blocked_le (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ)) (a : ℝ) (ha : 0 ≤ a) :
    interactionNorm a (blockedInteraction ν e Φ) ≤ Real.exp (-a) * interactionNorm a Φ := by
  apply interactionNorm_le _ _ (by positivity)
  intro i
  exact (interactionRow_blocked_le ν e Φ a ha i).trans
    (mul_le_mul_of_nonneg_left (interactionRow_le a (e (.inl (.inl i))) Φ) (Real.exp_pos _).le)

theorem blockedInteraction_centered (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (Φ : Finset X → C(X → E, ℝ))
    (hΦ : ∀ S, (∫ U, Φ S U ∂Measure.pi (fun _ : X ↦ ν)) = 0) (T : Finset I) :
    (∫ c, blockedInteraction ν e Φ T c ∂Measure.pi (fun _ : I ↦ ν)) = 0 := by
  simp only [blockedInteraction, regroupInteraction, ContinuousMap.sum_apply]
  rw [integral_finsetSum _ (fun S _ ↦ CompactTransferGap.IntegralKernel.integrable_continuous_fun
    (Measure.pi fun _ : I ↦ ν) (blockedDensity ν e (Φ S)).continuous)]
  simp only [integral_blockedDensity, hΦ, Finset.sum_const_zero]

theorem blockedInteraction_empty_eq_zero (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (Φ : Finset X → C(X → E, ℝ)) (hlocal : ∀ S, DependsOn S (Φ S))
    (hcenter : ∀ S, (∫ U, Φ S U ∂Measure.pi (fun _ : X ↦ ν)) = 0) :
    blockedInteraction ν e Φ ∅ = 0 := by
  ext c
  have hc (c' : I → E) : blockedInteraction ν e Φ ∅ c' = blockedInteraction ν e Φ ∅ c :=
    blockedInteraction_local ν e Φ hlocal ∅ c' c (by simp)
  have hi := blockedInteraction_centered ν e Φ hcenter ∅
  simp_rw [hc] at hi
  simpa using hi

def blockedDensityLinear (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) : C(X → E, ℝ) →ₗ[ℝ] C(I → E, ℝ) where
  toFun := blockedDensity ν e
  map_add' F G := by
    ext c
    change (∫ f, F (chart e (c, f)) + G (chart e (c, f))
      ∂(Measure.pi fun _ : I ↦ ν).prod (Measure.pi fun _ : J ↦ ν)) = _
    exact integral_add
      (CompactTransferGap.IntegralKernel.integrable_continuous_fun _
        (F.continuous.comp ((continuous_chart e).comp (continuous_const.prodMk continuous_id))))
      (CompactTransferGap.IntegralKernel.integrable_continuous_fun _
        (G.continuous.comp ((continuous_chart e).comp (continuous_const.prodMk continuous_id))))
  map_smul' a F := by
    ext c
    exact integral_const_mul a _

theorem sum_blockedInteraction (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ)) :
    ∑ T, blockedInteraction ν e Φ T = blockedDensity ν e (∑ S, Φ S) := by
  unfold blockedInteraction regroupInteraction
  rw [Finset.sum_fiberwise_of_maps_to (fun S _ ↦ mem_univ (retainedSupport e S))]
  exact (map_sum (blockedDensityLinear ν e) Φ univ).symm

/-- On actual centered local interactions the regrouped Haar operator preserves
locality, centering and the full averaged action, while its norm decreases by
`exp(-a) < 1`. There is no dependence on the number of fine links. -/
theorem strict_linear_gain (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (Φ : Finset X → C(X → E, ℝ)) (hlocal : ∀ S, DependsOn S (Φ S))
    (hcenter : ∀ S, (∫ U, Φ S U ∂Measure.pi (fun _ : X ↦ ν)) = 0)
    (a : ℝ) (ha : 0 < a) :
    0 < Real.exp (-a) ∧ Real.exp (-a) < 1 ∧
    (∀ T, DependsOn T (blockedInteraction ν e Φ T)) ∧
    (∀ T, (∫ c, blockedInteraction ν e Φ T c ∂Measure.pi (fun _ : I ↦ ν)) = 0) ∧
    blockedInteraction ν e Φ ∅ = 0 ∧
    (∑ T, blockedInteraction ν e Φ T) = blockedDensity ν e (∑ S, Φ S) ∧
    interactionNorm a (blockedInteraction ν e Φ) ≤ Real.exp (-a) * interactionNorm a Φ :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith),
    blockedInteraction_local ν e Φ hlocal, blockedInteraction_centered ν e Φ hcenter,
    blockedInteraction_empty_eq_zero ν e Φ hlocal hcenter,
    sum_blockedInteraction ν e Φ, interactionNorm_blocked_le ν e Φ a ha.le⟩

end PairedHaar

/-! ## Uniform connected-family budgets for the block chart -/

namespace PairedHaar
open WilsonBlockElimination.PairedLinks
open Mettapedia.Combinatorics.PolymerGas
variable {X I J P : Type*} [Fintype X] [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq X] [DecidableEq I] [DecidableEq J] [DecidableEq P]
variable (e : ((I ⊕ I) ⊕ J) ≃ X) (supp : P → Finset X) (v : P → ℝ)

def clusterMajorant (C : Finset P) : ℝ :=
  if C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)) then
    ∏ p ∈ C, v p * Real.exp (4 * (supp p).card) else 0

theorem clusterMajorant_nonneg (hv : ∀ p, 0 ≤ v p) (C : Finset P) :
    0 ≤ clusterMajorant e supp v C := by
  unfold clusterMajorant
  split_ifs
  · exact prod_nonneg fun p _ ↦ mul_nonneg (hv p) (Real.exp_pos _).le
  · rfl

theorem exp_card_fluctuationUnion_le (C : Finset P) :
    Real.exp ((plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card : ℝ) ≤
      ∏ p ∈ C, Real.exp ((supp p).card : ℝ) := by
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hc : (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card ≤
      ∑ p ∈ C, (supp p).card :=
    (card_biUnion_le).trans (sum_le_sum (fun p _ ↦ card_fluctuationSupport_le e (supp p)))
  exact_mod_cast hc

theorem clusterMajorant_dressed_le (hv : ∀ p, 0 ≤ v p) (C : Finset P) :
    clusterMajorant e supp v C *
      Real.exp ((plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card : ℝ) ≤
    if C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)) then
      ∏ p ∈ C, v p * Real.exp (5 * (supp p).card) else 0 := by
  unfold clusterMajorant
  split_ifs
  · calc
      _ ≤ (∏ p ∈ C, v p * Real.exp (4 * (supp p).card)) *
          ∏ p ∈ C, Real.exp ((supp p).card : ℝ) :=
        mul_le_mul_of_nonneg_left (exp_card_fluctuationUnion_le e supp C)
          (prod_nonneg fun p _ ↦ mul_nonneg (hv p) (Real.exp_pos _).le)
      _ = _ := by
        rw [← prod_mul_distrib]
        apply prod_congr rfl
        intro p hp
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  · simp

/-- Two units of the input cardinality weight pay for the exponential
connected-family reserve. This inequality is independent of the lattice size. -/
theorem weighted_root_budget (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) (x : X) :
    ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      (v p * Real.exp (5 * (supp p).card)) * Real.exp ((fluctuationSupport e (supp p)).card : ℝ) ≤
      Real.exp (-2) * r := by
  calc
    _ ≤ ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p), Real.exp (6 * (supp p).card) * v p := by
      apply sum_le_sum
      intro p hp
      have hc : ((fluctuationSupport e (supp p)).card : ℝ) ≤ (supp p).card := by
        exact_mod_cast card_fluctuationSupport_le e (supp p)
      rw [mul_assoc, ← Real.exp_add, mul_comm (Real.exp _) (v p)]
      apply mul_le_mul_of_nonneg_left _ (hv p)
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (-2) * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
        Real.exp (8 * (supp p).card) * v p := by
      simpa only [show (6 : ℝ)-8 = -2 by norm_num] using
        sum_card_weight_reserve_le supp hne hv (show (6 : ℝ) ≤ 8 by norm_num) x
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow x) (Real.exp_pos _).le

theorem exp_reserve_lt_one : 4 * Real.exp (-2) < 1 := by
  have h1 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  have h2 : 4 < Real.exp 2 := by
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos 2)).mpr h2


theorem weighted_fluctuation_budget (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) (y : I ⊕ J) :
    ∑ p ∈ univ.filter (fun p ↦ y ∈ fluctuationSupport e (supp p)),
      (v p * Real.exp (5 * (supp p).card)) * Real.exp ((fluctuationSupport e (supp p)).card : ℝ) ≤
      2 * (Real.exp (-2) * r) :=
  sum_incident_fluctuationSupport_le e supp
    (fun p ↦ mul_nonneg (mul_nonneg (hv p) (Real.exp_pos _).le) (Real.exp_pos _).le)
    (mul_nonneg (Real.exp_pos _).le hr) (weighted_root_budget e supp v hne hv hrow) y

theorem connected_majorant_smallness (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) (y : I ⊕ J) :
    ∑ p ∈ univ.filter (fun p ↦ y ∈ fluctuationSupport e (supp p)),
      (v p * Real.exp (5 * (supp p).card)) * Real.exp (1 * (fluctuationSupport e (supp p)).card : ℝ) ≤ 1 := by
  simp only [one_mul]
  refine (weighted_fluctuation_budget e supp v hne hv hr hrow y).trans ?_
  have he := exp_reserve_lt_one
  have hm := mul_le_mul_of_nonneg_left hr1 (Real.exp_pos (-2)).le
  nlinarith [Real.exp_pos (-2)]

theorem clusterMajorant_site_budget (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) (y : I ⊕ J) :
    ∑ C ∈ univ.filter (fun C ↦ y ∈ plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C),
      clusterMajorant e supp v C *
        Real.exp ((plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card : ℝ) ≤
      2 * (Real.exp (-2) * r) := by
  let ds : P → Finset (I ⊕ J) := fun p ↦ fluctuationSupport e (supp p)
  let w : P → ℝ := fun p ↦ v p * Real.exp (5 * (supp p).card)
  calc
    _ ≤ ∑ C ∈ univ.filter (fun C ↦ y ∈ plaquetteSupport ds C),
        if C ∈ connectedPlaquettes ds then ∏ p ∈ C, w p else 0 :=
      sum_le_sum (fun C _ ↦ clusterMajorant_dressed_le e supp v hv C)
    _ = ∑ C ∈ (connectedPlaquettes ds).filter (fun C ↦ y ∈ plaquetteSupport ds C),
        ∏ p ∈ C, w p := by
      rw [← sum_filter]
      congr 1
      ext C
      simp [and_comm]
    _ ≤ ∑ p ∈ univ.filter (fun p ↦ y ∈ ds p), w p * Real.exp (1 * (ds p).card) :=
      sum_connected_weight_through_site_le ds (fun p ↦ mul_nonneg (hv p) (Real.exp_pos _).le)
        (connected_majorant_smallness e supp v hne hv hr hr1 hrow) y
    _ ≤ _ := by
      simpa only [one_mul] using weighted_fluctuation_budget e supp v hne hv hr hrow y

theorem clusterMajorant_through_fine_site (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) (x : X) :
    ∑ C ∈ univ.filter (fun C ↦ x ∈ plaquetteSupport supp C),
      clusterMajorant e supp v C *
        Real.exp ((plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card : ℝ) ≤
      Real.exp (-2) * r := by
  let ds : P → Finset (I ⊕ J) := fun p ↦ fluctuationSupport e (supp p)
  let w : P → ℝ := fun p ↦ v p * Real.exp (5 * (supp p).card)
  let incident : Finset P := univ.filter (fun p ↦ x ∈ supp p)
  have he (C : Finset P) : x ∈ plaquetteSupport supp C ↔ ¬ Disjoint C incident := by
    simp only [plaquetteSupport, mem_biUnion, not_disjoint_iff, incident, mem_filter,
      mem_univ, true_and]
  calc
    _ ≤ ∑ C ∈ univ.filter (fun C ↦ x ∈ plaquetteSupport supp C),
        if C ∈ connectedPlaquettes ds then ∏ p ∈ C, w p else 0 :=
      sum_le_sum (fun C _ ↦ clusterMajorant_dressed_le e supp v hv C)
    _ = ∑ C ∈ (connectedPlaquettes ds).filter (fun C ↦ ¬ Disjoint C incident),
        ∏ p ∈ C, w p := by
      rw [← sum_filter]
      congr 1
      ext C
      simp [he, and_comm]
    _ ≤ ∑ p ∈ incident, w p * Real.exp (1 * (ds p).card) :=
      sum_connected_weight_meeting_labels_le ds (fun p ↦ mul_nonneg (hv p) (Real.exp_pos _).le)
        (connected_majorant_smallness e supp v hne hv hr hr1 hrow) incident
    _ ≤ _ := by simpa only [one_mul] using weighted_root_budget e supp v hne hv hrow x

theorem clusterMajorant_koteckyPreiss (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) :
    KoteckyPreissCondition (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ ((-clusterMajorant e supp v C : ℝ) : ℂ))
      (fun C ↦ (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card) := by
  apply koteckyPreissCondition_of_supported_site_sum
  · intro C hC
    by_cases hc : C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p))
    · have hn := plaquetteSupport_nonempty (fun p ↦ fluctuationSupport e (supp p))
        (fun p ↦ fluctuationSupport_nonempty e (hne p)) (mem_filter.mp hc).2
      exact (hn.ne_empty hC).elim
    · simp [clusterMajorant, hc]
  · intro y
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (clusterMajorant_nonneg e supp v hv _)]
    refine (clusterMajorant_site_budget e supp v hne hv hr hr1 hrow y).trans ?_
    have he := exp_reserve_lt_one
    have hm := mul_le_mul_of_nonneg_left hr1 (Real.exp_pos (-2)).le
    nlinarith [Real.exp_pos (-2)]

end PairedHaar

/-! ## Actual conditional activities and their exact partition -/

namespace PairedHaar
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {X I J P E : Type*}
  [Fintype X] [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq X] [DecidableEq I] [DecidableEq J] [DecidableEq P]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def interactionFactor (F : C(X → E, ℝ)) : C(X → E, ℝ) :=
  ⟨fun U ↦ Real.exp (F U) - 1, (Real.continuous_exp.comp F.continuous).sub continuous_const⟩

theorem interactionFactor_norm_le (F : C(X → E, ℝ)) (hF : ‖F‖ ≤ 1) :
    ‖interactionFactor F‖ ≤ 2 * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro U
  have hb : |F U| ≤ ‖F‖ := F.norm_coe_le_norm U
  exact (Real.abs_exp_sub_one_le (hb.trans hF)).trans (by linarith)

theorem interactionFactor_local (S : Finset X) (F : C(X → E, ℝ)) (hF : DependsOn S F) :
    DependsOn S (interactionFactor F) := by
  intro U V huv
  change Real.exp (F U) - 1 = Real.exp (F V) - 1
  rw [hF U V huv]

variable (ν : Measure E) [IsProbabilityMeasure ν]
  (e : ((I ⊕ I) ⊕ J) ≃ X) (supp : P → Finset X) (Φ : P → C(X → E, ℝ))

def clusterActivity (C : Finset P) : C(I → E, ℝ) :=
  if C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)) then
    blockedDensity ν e (∏ p ∈ C, interactionFactor (Φ p)) else 0

theorem clusterActivity_local [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ p, DependsOn (supp p) (Φ p)) (C : Finset P) :
    DependsOn (retainedSupport e (plaquetteSupport supp C)) (clusterActivity ν e supp Φ C) := by
  unfold clusterActivity
  split_ifs
  · apply blockedDensity_local
    intro U V huv
    simp only [ContinuousMap.prod_apply]
    apply prod_congr rfl
    intro p hp
    exact interactionFactor_local (supp p) (Φ p) (hΦ p) U V
      (fun x hx ↦ huv x (mem_biUnion.mpr ⟨p, hp, hx⟩))
  · intro U V huv
    rfl

theorem clusterActivity_norm_le (hΦ : ∀ p, ‖Φ p‖ ≤ 1) (C : Finset P) :
    ‖clusterActivity ν e supp Φ C‖ ≤
      if C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)) then
        ∏ p ∈ C, 2 * ‖Φ p‖ else 0 := by
  unfold clusterActivity
  split_ifs
  · exact (norm_blockedDensity_le ν e _).trans ((Finset.norm_prod_le _ _).trans
      (prod_le_prod (fun p _ ↦ norm_nonneg _) (fun p _ ↦ interactionFactor_norm_le (Φ p) (hΦ p))))
  · simp


def interactionDensity : C(X → E, ℝ) :=
  ⟨fun U ↦ Real.exp (∑ p, Φ p U), by fun_prop⟩

theorem interactionDensity_pos (U : X → E) : 0 < interactionDensity Φ U := Real.exp_pos _

theorem clusterActivity_partitionFunction
    (hne : ∀ p, (supp p).Nonempty) (hΦ : ∀ p, DependsOn (supp p) (Φ p)) :
    blockedDensity ν e (interactionDensity Φ) =
      partitionFunction (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
        (clusterActivity ν e supp Φ) (connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p))) := by
  ext c
  rw [partitionFunction_continuous_apply]
  let ds : P → Finset (I ⊕ J) := fun p ↦ fluctuationSupport e (supp p)
  let f : P → (I ⊕ J → E) → ℝ := fun p u ↦ interactionFactor (Φ p) (fluctuationChart e c u)
  have hfc p : Continuous (f p) := (interactionFactor (Φ p)).continuous.comp
    (continuous_fluctuationChart e c)
  have hfl p U V (huv : ∀ y ∈ ds p, U y = V y) : f p U = f p V :=
    interactionFactor_local (supp p) (Φ p) (hΦ p) _ _ (fluctuationChart_agree e c huv)
  have hi := integral_prod_one_add_eq_labelledPartition ν (1 : E) ds
    (fun p ↦ fluctuationSupport_nonempty e (hne p)) f (fun p ↦ (hfc p).measurable) hfl
    (fun Γ ↦ CompactTransferGap.IntegralKernel.integrable_continuous_fun
      (Measure.pi fun _ : I ⊕ J ↦ ν) (by
        apply continuous_finset_prod
        intro C hC
        exact continuous_finset_prod _ (fun p _ ↦ hfc p)))
  rw [← integral_fluctuationChart ν e c (interactionDensity Φ)]
  calc
    _ = ∫ u, ∏ p, (1 + f p u) ∂Measure.pi (fun _ : I ⊕ J ↦ ν) := by
      apply integral_congr_ae
      filter_upwards [] with u
      change Real.exp (∑ p, Φ p (fluctuationChart e c u)) = _
      rw [Real.exp_sum]
      apply prod_congr rfl
      intro p hp
      dsimp [f, interactionFactor]
      ring
    _ = _ := by
      rw [hi]
      apply partitionFunction_congr
      intro C hC
      change C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)) at hC
      have hh := integral_fluctuationChart ν e c (∏ p ∈ C, interactionFactor (Φ p))
      simpa only [ContinuousMap.prod_apply, clusterActivity, if_pos hC, f] using hh

end PairedHaar

/-! ## Exact centering and vacuum extraction -/

namespace PairedHaar
open WilsonBlockElimination WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {V X E : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem coefficient_local (supp : V → Finset X) (F : Finset V → C(X → E, ℝ))
    (hF : ∀ S, DependsOn (S.biUnion supp) (F S)) (S : Finset V) :
    DependsOn (S.biUnion supp) (coefficient (A := C(X → E, ℝ)) F S) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro U W huw
    rw [coefficient]
    simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply]
    rw [hF S U W huw]
    congr 1
    apply sum_congr rfl
    intro T hT
    have hsub : T.val ⊆ S := mem_powerset.mp (mem_erase.mp T.property).2
    have hstrict : T.val ⊂ S := (ssubset_iff_subset_ne).mpr ⟨hsub, (mem_erase.mp T.property).1⟩
    exact ih T.val hstrict U W (fun x hx ↦ huw x (biUnion_subset_biUnion_of_subset_left supp hsub hx))

theorem haarCentered_local (ν : Measure E) [IsProbabilityMeasure ν]
    (S : Finset X) (F : C(X → E, ℝ)) (hF : DependsOn S F) :
    DependsOn S (centered (Measure.pi fun _ : X ↦ ν) 1 F) := by
  intro U W huw
  simp only [centered, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply]
  rw [hF U W huw]

theorem norm_haarCentered_le (ν : Measure E) [IsProbabilityMeasure ν] (F : C(X → E, ℝ)) :
    ‖centered (Measure.pi fun _ : X ↦ ν) 1 F‖ ≤ 2 * ‖F‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro U
  exact abs_centered_le _ 1 F (fun _ ↦ by norm_num) (fun U ↦ F.norm_coe_le_norm U) U

theorem integral_haarCentered_zero (ν : Measure E) [IsProbabilityMeasure ν] (F : C(X → E, ℝ)) :
    (∫ U, centered (Measure.pi fun _ : X ↦ ν) 1 F U ∂Measure.pi (fun _ : X ↦ ν)) = 0 := by
  have h := expectation_centered (Measure.pi fun _ : X ↦ ν) 1 F (fun _ ↦ by norm_num)
  simpa [WilsonBlockElimination.expectation] using h

variable (ν : Measure E) [IsProbabilityMeasure ν]
  (supp : V → Finset X) (F : Finset V → C(X → E, ℝ))

def extractedInteraction : Finset X → C(X → E, ℝ) :=
  regroupInteraction (fun S ↦ S.biUnion supp)
    (fun S ↦ centered (Measure.pi fun _ : X ↦ ν) 1 (coefficient F S))

def extractedVacuum : ℝ :=
  ∑ S : Finset V, expectation (Measure.pi fun _ : X ↦ ν) 1 (coefficient F S)

theorem extractedInteraction_local (hF : ∀ S, DependsOn (S.biUnion supp) (F S)) (T : Finset X) :
    DependsOn T (extractedInteraction ν supp F T) :=
  regroupInteraction_local _ _ (fun S ↦ haarCentered_local ν _ _ (coefficient_local supp F hF S)) T

theorem extractedInteraction_centered (T : Finset X) :
    (∫ U, extractedInteraction ν supp F T U ∂Measure.pi (fun _ : X ↦ ν)) = 0 := by
  simp only [extractedInteraction, regroupInteraction, ContinuousMap.sum_apply]
  rw [integral_finsetSum _ (fun S _ ↦ CompactTransferGap.IntegralKernel.integrable_continuous_fun _
    (centered (Measure.pi fun _ : X ↦ ν) 1 (coefficient F S)).continuous)]
  simp only [integral_haarCentered_zero, sum_const_zero]

theorem extractedInteraction_empty_eq_zero (hF : ∀ S, DependsOn (S.biUnion supp) (F S)) :
    extractedInteraction ν supp F ∅ = 0 := by
  ext U
  have he (W : X → E) : extractedInteraction ν supp F ∅ W = extractedInteraction ν supp F ∅ U :=
    extractedInteraction_local ν supp F hF ∅ W U (by simp)
  have hi := extractedInteraction_centered ν supp F ∅
  simp_rw [he] at hi
  simpa using hi

theorem extractedInteraction_reconstruct :
    (∑ T, extractedInteraction ν supp F T) + extractedVacuum ν F • 1 = F univ := by
  rw [extractedInteraction, sum_regroupInteraction]
  simp only [centered, sum_sub_distrib]
  rw [← Finset.sum_smul]
  have he : ∑ S : Finset V, coefficient F S = F univ := by
    simpa only [zeta, powerset_univ] using zeta_coefficient F univ
  rw [he]
  simp only [extractedVacuum, sub_add_cancel]

theorem extractedInteraction_weighted_row_le (w : Finset X → ℝ) (hw : ∀ S, 0 ≤ w S) {c : V → ℝ}
    (hbudget : ∀ p, ∑ S ∈ univ.filter (fun S : Finset V ↦ p ∈ S),
      w (S.biUnion supp) * ‖coefficient F S‖ ≤ c p) (x : X) :
    weightedInteractionRow w hw x (extractedInteraction ν supp F) ≤
      2 * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p), c p := by
  calc
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset V ↦ x ∈ S.biUnion supp),
        w (S.biUnion supp) *
          ‖centered (Measure.pi fun _ : X ↦ ν) 1 (coefficient F S)‖ :=
      weightedInteractionRow_regroup_le _ _ w hw x
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset V ↦ x ∈ S.biUnion supp),
        2 * (w (S.biUnion supp) * ‖coefficient F S‖) := by
      apply sum_le_sum
      intro S hS
      nlinarith [mul_le_mul_of_nonneg_left (norm_haarCentered_le ν (coefficient F S)) (hw (S.biUnion supp))]
    _ = 2 * ∑ S ∈ univ.filter (fun S : Finset V ↦ x ∈ S.biUnion supp),
        w (S.biUnion supp) * ‖coefficient F S‖ := by rw [mul_sum]
    _ ≤ 2 * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
        ∑ S ∈ univ.filter (fun S : Finset V ↦ p ∈ S),
          w (S.biUnion supp) * ‖coefficient F S‖ :=
      mul_le_mul_of_nonneg_left (sum_union_support_incident_le supp (fun S ↦ mul_nonneg (hw _) (norm_nonneg _)) x) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum (fun p _ ↦ hbudget p)) (by norm_num)

theorem extractedInteraction_row_le (a : ℝ) {c : V → ℝ}
    (hbudget : ∀ p, ∑ S ∈ univ.filter (fun S : Finset V ↦ p ∈ S),
      Real.exp (a * (S.biUnion supp).card) * ‖coefficient F S‖ ≤ c p) (x : X) :
    interactionRow a x (extractedInteraction ν supp F) ≤
      2 * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p), c p :=
  extractedInteraction_weighted_row_le ν supp F _ (fun _ ↦ (Real.exp_pos _).le) hbudget x

end PairedHaar

/-! ## A nonlinear contraction for the full generated interaction -/

namespace PairedHaar
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {X I J P E : Type*}
  [Fintype X] [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq X] [DecidableEq I] [DecidableEq J] [DecidableEq P]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (ν : Measure E) [IsProbabilityMeasure ν]
  (e : ((I ⊕ I) ⊕ J) ≃ X) (supp : P → Finset X) (Φ : P → C(X → E, ℝ))

def clusterRetainedSupport (C : Finset P) : Finset I := retainedSupport e (plaquetteSupport supp C)

def clusterRemovalWeight (v : P → ℝ) (C : Finset P) : ℝ :=
  Real.log (1 + clusterMajorant e supp v C *
    Real.exp ((plaquetteSupport (fun p ↦ fluctuationSupport e (supp p)) C).card : ℝ))

theorem clusterMajorant_dobrushin {v : P → ℝ}
    (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ r) :
    DobrushinCondition (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ ((-clusterMajorant e supp v C : ℝ) : ℂ)) (clusterRemovalWeight e supp v) := by
  have h := dobrushinCondition_of_koteckyPreiss (clusterMajorant_koteckyPreiss e supp v hne hv hr hr1 hrow)
  unfold clusterRemovalWeight
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (clusterMajorant_nonneg e supp v hv _)] using h

theorem weighted_clusterActivity_norm_le (hΦ : ∀ p, ‖Φ p‖ ≤ 1) (C : Finset P) :
    Real.exp (8 * (clusterRetainedSupport e supp C).card) * ‖clusterActivity ν e supp Φ C‖ ≤
      clusterMajorant e supp (fun p ↦ 2 * ‖Φ p‖) C := by
  by_cases hc : C ∈ connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p))
  · have hn := clusterActivity_norm_le ν e supp Φ hΦ C
    rw [if_pos hc] at hn
    have hb : 2 * (clusterRetainedSupport e supp C).card ≤ ∑ p ∈ C, (supp p).card :=
      (twice_card_retainedSupport_le e _).trans card_biUnion_le
    have he : Real.exp (8 * (clusterRetainedSupport e supp C).card) ≤
        ∏ p ∈ C, Real.exp (4 * (supp p).card) := by
      rw [← Real.exp_sum, ← mul_sum]
      apply Real.exp_le_exp.mpr
      have hb' : (2 : ℝ) * (clusterRetainedSupport e supp C).card ≤ ∑ p ∈ C, ((supp p).card : ℝ) := by
        exact_mod_cast hb
      linarith
    calc
      _ ≤ (∏ p ∈ C, Real.exp (4 * (supp p).card)) * (∏ p ∈ C, 2 * ‖Φ p‖) :=
        mul_le_mul he hn (norm_nonneg _) (prod_nonneg (fun _ _ ↦ (Real.exp_pos _).le))
      _ = _ := by
        simp only [clusterMajorant, if_pos hc, prod_mul_distrib]
        ring
  · simp [clusterActivity, clusterMajorant, hc]

theorem component_norm_le_of_row (hne : ∀ p, (supp p).Nonempty) {R : ℝ}
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) (p : P) : ‖Φ p‖ ≤ R := by
  obtain ⟨x, hx⟩ := hne p
  have hp : p ∈ univ.filter (fun p ↦ x ∈ supp p) := mem_filter.mpr ⟨mem_univ _, hx⟩
  calc
    _ ≤ Real.exp (8 * (supp p).card) * ‖Φ p‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
    _ ≤ ∑ q ∈ univ.filter (fun q ↦ x ∈ supp q), Real.exp (8 * (supp q).card) * ‖Φ q‖ :=
      single_le_sum (s := univ.filter (fun q : P ↦ x ∈ supp q))
        (f := fun q ↦ Real.exp (8 * (supp q).card) * ‖Φ q‖) (fun q _ ↦ by positivity) hp
    _ ≤ R := hrow x

theorem clusterActivity_shadow_dobrushin (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) :
    DobrushinCondition (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ ((-clusterMajorant e supp (fun p ↦ 2 * ‖Φ p‖) C : ℝ) : ℂ))
      (clusterRemovalWeight e supp (fun p ↦ 2 * ‖Φ p‖)) := by
  apply clusterMajorant_dobrushin e supp hne (fun p ↦ by positivity)
    (r := 2*R) (by positivity) (by linarith)
  intro x
  calc
    _ = 2 * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p), Real.exp (8 * (supp p).card) * ‖Φ p‖ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow x) (by norm_num)

theorem clusterActivity_partition_pos (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R)
    (Λ : Finset (Finset P)) (c : I → E) :
    0 < partitionFunction (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ clusterActivity ν e supp Φ C c) Λ := by
  apply partitionFunction_pos_of_dobrushin
  apply (clusterActivity_shadow_dobrushin e supp Φ hne hR hR1 hrow).mono_activity
  intro C
  have hρ := clusterMajorant_nonneg e supp (fun p ↦ 2 * ‖Φ p‖) (fun p ↦ by positivity) C
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hρ]
  have hn : ∀ p, ‖Φ p‖ ≤ 1 := fun p ↦
    (component_norm_le_of_row supp Φ hne hrow p).trans (by linarith)
  calc
    _ ≤ ‖clusterActivity ν e supp Φ C‖ := (clusterActivity ν e supp Φ C).norm_coe_le_norm c
    _ ≤ Real.exp (8 * (clusterRetainedSupport e supp C).card) * ‖clusterActivity ν e supp Φ C‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
    _ ≤ _ := weighted_clusterActivity_norm_le ν e supp Φ hn C

def clusterLogFamily
    (hpos : ∀ Λ c, 0 < partitionFunction
      (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ clusterActivity ν e supp Φ C c) Λ) (A : Finset (Finset P)) : C(I → E, ℝ) :=
  let Z : C(I → E, ℝ) := partitionFunction
    (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
    (clusterActivity ν e supp Φ) ((connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p))) ∩ A)
  ⟨fun c ↦ Real.log (Z c), Z.continuous.log (fun c ↦ by
    rw [partitionFunction_continuous_apply]
    exact (hpos _ c).ne')⟩

theorem clusterLogFamily_local [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ p, DependsOn (supp p) (Φ p))
    (hpos : ∀ Λ c, 0 < partitionFunction
      (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
      (fun C ↦ clusterActivity ν e supp Φ C c) Λ) (A : Finset (Finset P)) :
    DependsOn (A.biUnion (clusterRetainedSupport e supp)) (clusterLogFamily ν e supp Φ hpos A) := by
  intro U W huw
  simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply]
  apply congrArg Real.log
  apply partitionFunction_congr
  intro C hC
  exact clusterActivity_local ν e supp Φ hΦ C U W
    (fun x hx ↦ huw x (mem_biUnion.mpr ⟨C, (mem_inter.mp hC).2, hx⟩))


variable (hpos : ∀ Λ c, 0 < partitionFunction
  (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
  (fun C ↦ clusterActivity ν e supp Φ C c) Λ)

theorem clusterLogFamily_root_budget (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) (C : Finset P) :
    ∑ A ∈ univ.filter (fun A : Finset (Finset P) ↦ C ∈ A),
      Real.exp (8 * (A.biUnion (clusterRetainedSupport e supp)).card) *
        ‖coefficient (clusterLogFamily ν e supp Φ hpos) A‖ ≤
      clusterRemovalWeight e supp (fun p ↦ 2 * ‖Φ p‖) C := by
  let w := supportCardinalityWeight (clusterRetainedSupport e supp) 8 (by norm_num)
  apply sum_weighted_norm_log_coefficients_le
    (Λ := connectedPlaquettes (fun p ↦ fluctuationSupport e (supp p)))
    _ w (clusterActivity ν e supp Φ)
    (fun C ↦ clusterMajorant_nonneg e supp _ (fun p ↦ by positivity) C)
    (clusterActivity_shadow_dobrushin e supp Φ hne hR hR1 hrow)
  · intro D c
    have hn : ∀ p, ‖Φ p‖ ≤ 1 := fun p ↦
      (component_norm_le_of_row supp Φ hne hrow p).trans (by linarith)
    have hb := weighted_clusterActivity_norm_le ν e supp Φ hn D
    have hc := mul_le_mul_of_nonneg_left ((clusterActivity ν e supp Φ D).norm_coe_le_norm c)
      (Real.exp_pos (8 * (clusterRetainedSupport e supp D).card)).le
    simpa [w, supportCardinalityWeight] using hc.trans hb
  · intro A c
    simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply,
      activatedLogPartition]

theorem sum_clusterRemoval_retained_le_of_row (v : P → ℝ)
    (hne : ∀ p, (supp p).Nonempty) (hv : ∀ p, 0 ≤ v p)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p => x ∈ supp p), Real.exp (8 * (supp p).card) * v p ≤ r)
    (i : I) :
    ∑ C ∈ univ.filter (fun C => i ∈ clusterRetainedSupport e supp C),
      clusterRemovalWeight e supp v C ≤ Real.exp (-2) * r := by
  calc
    _ ≤ ∑ C ∈ univ.filter (fun C => i ∈ clusterRetainedSupport e supp C),
        clusterMajorant e supp v C *
          Real.exp ((plaquetteSupport (fun p => fluctuationSupport e (supp p)) C).card : ℝ) := by
      apply sum_le_sum
      intro C hC
      have hn := mul_nonneg (clusterMajorant_nonneg e supp v hv C)
        (Real.exp_pos ((plaquetteSupport (fun p => fluctuationSupport e (supp p)) C).card : ℝ)).le
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 + clusterMajorant e supp v C *
        Real.exp ((plaquetteSupport (fun p => fluctuationSupport e (supp p)) C).card : ℝ) by linarith)
      exact (show Real.log _ ≤ _ from h).trans_eq (by ring)
    _ ≤ ∑ C ∈ univ.filter (fun C => e (.inl (.inl i)) ∈ plaquetteSupport supp C),
        clusterMajorant e supp v C *
          Real.exp ((plaquetteSupport (fun p => fluctuationSupport e (supp p)) C).card : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro C hC
        exact mem_filter.mpr ⟨mem_univ _, ((mem_retainedSupport e _ i).mp (mem_filter.mp hC).2).1⟩
      · intro C hC hnot
        exact mul_nonneg (clusterMajorant_nonneg e supp v hv C) (Real.exp_pos _).le
    _ ≤ _ := clusterMajorant_through_fine_site e supp v hne hv hr hr1 hrow (e (.inl (.inl i)))


theorem sum_clusterRemoval_retained_le (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) (i : I) :
    ∑ C ∈ univ.filter (fun C ↦ i ∈ clusterRetainedSupport e supp C),
      clusterRemovalWeight e supp (fun p ↦ 2 * ‖Φ p‖) C ≤ 2 * Real.exp (-2) * R := by
  let v : P → ℝ := fun p ↦ 2 * ‖Φ p‖
  have hv p : 0 ≤ v p := by dsimp [v]; positivity
  have hr : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * v p ≤ 2*R := by
    intro x
    calc
      _ = 2 * ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p), Real.exp (8 * (supp p).card) * ‖Φ p‖ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        dsimp [v]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrow x) (by norm_num)
  calc
    _ ≤ Real.exp (-2) * (2*R) :=
      sum_clusterRemoval_retained_le_of_row e supp v hne hv (by positivity) (by linarith) hr i
    _ = _ := by ring

def nonlinearInteraction : Finset I → C(I → E, ℝ) :=
  extractedInteraction ν (clusterRetainedSupport e supp) (clusterLogFamily ν e supp Φ hpos)

def nonlinearVacuum : ℝ := extractedVacuum ν (clusterLogFamily ν e supp Φ hpos)

theorem nonlinearInteraction_norm_le (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) :
    interactionNorm 8 (nonlinearInteraction ν e supp Φ hpos) ≤ (4 * Real.exp (-2)) * R := by
  apply interactionNorm_le _ _ (by positivity)
  intro i
  calc
    _ ≤ 2 * ∑ C ∈ univ.filter (fun C ↦ i ∈ clusterRetainedSupport e supp C),
        clusterRemovalWeight e supp (fun p ↦ 2 * ‖Φ p‖) C :=
      extractedInteraction_row_le ν _ _ 8 (clusterLogFamily_root_budget ν e supp Φ hpos hne hR hR1 hrow) i
    _ ≤ 2 * (2 * Real.exp (-2) * R) :=
      mul_le_mul_of_nonneg_left (sum_clusterRemoval_retained_le e supp Φ hne hR hR1 hrow i) (by norm_num)
    _ = _ := by ring

theorem nonlinearInteraction_local [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ p, DependsOn (supp p) (Φ p)) (T : Finset I) :
    DependsOn T (nonlinearInteraction ν e supp Φ hpos T) :=
  extractedInteraction_local ν _ _ (clusterLogFamily_local ν e supp Φ hΦ hpos) T

theorem nonlinearInteraction_centered (T : Finset I) :
    (∫ U, nonlinearInteraction ν e supp Φ hpos T U ∂Measure.pi (fun _ : I ↦ ν)) = 0 :=
  extractedInteraction_centered ν _ _ T

theorem nonlinearInteraction_empty_eq_zero [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ p, DependsOn (supp p) (Φ p)) : nonlinearInteraction ν e supp Φ hpos ∅ = 0 :=
  extractedInteraction_empty_eq_zero ν _ _ (clusterLogFamily_local ν e supp Φ hΦ hpos)

theorem nonlinearInteraction_reconstruct
    (hne : ∀ p, (supp p).Nonempty) (hΦ : ∀ p, DependsOn (supp p) (Φ p)) (c : I → E) :
    blockedDensity ν e (interactionDensity Φ) c =
      Real.exp (nonlinearVacuum ν e supp Φ hpos + ∑ T, nonlinearInteraction ν e supp Φ hpos T c) := by
  have h := congrArg (fun F : C(I → E, ℝ) ↦ F c)
    (extractedInteraction_reconstruct ν (clusterRetainedSupport e supp) (clusterLogFamily ν e supp Φ hpos))
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one] at h
  have hlog : clusterLogFamily ν e supp Φ hpos univ c =
      Real.log (blockedDensity ν e (interactionDensity Φ) c) := by
    simp only [clusterLogFamily, inter_univ, ContinuousMap.coe_mk]
    rw [← clusterActivity_partitionFunction ν e supp Φ hne hΦ]
  rw [hlog] at h
  have he : nonlinearVacuum ν e supp Φ hpos + ∑ T, nonlinearInteraction ν e supp Φ hpos T c =
      Real.log (blockedDensity ν e (interactionDensity Φ) c) := by
    change extractedVacuum ν _ + ∑ T, extractedInteraction ν _ _ T c = _
    linarith
  rw [he, Real.exp_log (blockedDensity_pos ν e _ (interactionDensity_pos Φ) c)]

/-- The nonlinear block map includes the full connected logarithm. Vacuum
extraction and centering retain the complete density, with a strict gain in
one fixed support-cardinality norm. -/
theorem nonlinear_block_contraction [Measure.IsMulLeftInvariant ν]
    (hne : ∀ p, (supp p).Nonempty) (hΦ : ∀ p, DependsOn (supp p) (Φ p))
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p ↦ x ∈ supp p),
      Real.exp (8 * (supp p).card) * ‖Φ p‖ ≤ R) :
    ∃ (Ψ : Finset I → C(I → E, ℝ)) (vacuum : ℝ),
      (∀ T, DependsOn T (Ψ T)) ∧ (∀ T, (∫ c, Ψ T c ∂Measure.pi (fun _ : I ↦ ν)) = 0) ∧
      Ψ ∅ = 0 ∧
      (∀ c, blockedDensity ν e (interactionDensity Φ) c = Real.exp (vacuum + ∑ T, Ψ T c)) ∧
      interactionNorm 8 Ψ ≤ (4 * Real.exp (-2)) * R := by
  let hp := clusterActivity_partition_pos ν e supp Φ hne hR hR1 hrow
  exact ⟨nonlinearInteraction ν e supp Φ hp, nonlinearVacuum ν e supp Φ hp,
    nonlinearInteraction_local ν e supp Φ hp hΦ,
    nonlinearInteraction_centered ν e supp Φ hp,
    nonlinearInteraction_empty_eq_zero ν e supp Φ hp hΦ,
    nonlinearInteraction_reconstruct ν e supp Φ hp hne hΦ,
    nonlinearInteraction_norm_le ν e supp Φ hp hne hR hR1 hrow⟩

end PairedHaar

/-! ## Canonical extraction for support-indexed interactions -/

namespace PairedHaar
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
variable {X I J E A : Type*} [Fintype X] [Fintype I] [Fintype J]
  [DecidableEq X] [DecidableEq I] [DecidableEq J]

theorem sum_nonemptySupports [AddCommMonoid A] (f : Finset X → A) (hf : f ∅ = 0) :
    (∑ S : {S : Finset X // S.Nonempty}, f S.val) = ∑ S, f S := by
  rw [← Finset.sum_subtype (univ.filter (fun S : Finset X ↦ S.Nonempty)) (by simp) f]
  apply sum_subset (subset_univ _)
  intro S hS hn
  have he : S = ∅ := by simpa using hn
  simpa only [he] using hf

variable [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem interactionRow_nonempty (a : ℝ) (Φ : Finset X → C(X → E, ℝ)) (x : X) :
    (∑ S ∈ univ.filter (fun S : {S : Finset X // S.Nonempty} ↦ x ∈ S.val),
      Real.exp (a * S.val.card) * ‖Φ S.val‖) = interactionRow a x Φ := by
  simp only [sum_filter, interactionRow_apply]
  exact sum_nonemptySupports (fun S ↦ if x ∈ S then Real.exp (a * S.card) * ‖Φ S‖ else 0) (by simp)

theorem interactionDensity_nonempty (Φ : Finset X → C(X → E, ℝ)) (hzero : Φ ∅ = 0) :
    interactionDensity (fun S : {S : Finset X // S.Nonempty} ↦ Φ S.val) = interactionDensity Φ := by
  ext U
  apply congrArg Real.exp
  exact sum_nonemptySupports (fun S ↦ Φ S U) (by simp only [hzero, ContinuousMap.zero_apply])

theorem nonlinear_block_contraction_of_norm (ν : Measure E) [IsProbabilityMeasure ν]
    [Measure.IsMulLeftInvariant ν] (e : ((I ⊕ I) ⊕ J) ≃ X)
    (Φ : Finset X → C(X → E, ℝ)) (hΦ : ∀ S, DependsOn S (Φ S)) (hzero : Φ ∅ = 0)
    (hsmall : interactionNorm 8 Φ ≤ 1/2) :
    ∃ (Ψ : Finset I → C(I → E, ℝ)) (vacuum : ℝ),
      (∀ T, DependsOn T (Ψ T)) ∧ (∀ T, (∫ c, Ψ T c ∂Measure.pi (fun _ : I ↦ ν)) = 0) ∧
      Ψ ∅ = 0 ∧
      (∀ c, blockedDensity ν e (interactionDensity Φ) c = Real.exp (vacuum + ∑ T, Ψ T c)) ∧
      interactionNorm 8 Ψ ≤ (4 * Real.exp (-2)) * interactionNorm 8 Φ := by
  obtain ⟨Ψ, vacuum, hl, hc, hz, he, hn⟩ := nonlinear_block_contraction ν e
    (fun S : {S : Finset X // S.Nonempty} ↦ S.val) (fun S ↦ Φ S.val)
    (fun S ↦ S.property) (fun S ↦ hΦ S.val)
    (R := interactionNorm 8 Φ) (by positivity) hsmall (fun x ↦ by
      rw [interactionRow_nonempty]
      exact interactionRow_le 8 x Φ)
  refine ⟨Ψ, vacuum, hl, hc, hz, ?_, hn⟩
  simpa only [interactionDensity_nonempty Φ hzero] using he


variable (ν : Measure E) [IsProbabilityMeasure ν]
  (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ))
  (hsmall : interactionNorm 8 Φ ≤ 1/2)

include hsmall in
theorem nonempty_partition_pos : ∀ Λ c, 0 < Mettapedia.Combinatorics.PolymerGas.partitionFunction
    (Mettapedia.Combinatorics.PolymerGas.plaquetteGraph
      (Mettapedia.Combinatorics.PolymerGas.plaquetteSupport
        (fun S : {S : Finset X // S.Nonempty} ↦ fluctuationSupport e S.val)))
    (fun C ↦ clusterActivity ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
      (fun S ↦ Φ S.val) C c) Λ :=
  clusterActivity_partition_pos ν e _ _ (fun S ↦ S.property)
    (R := interactionNorm 8 Φ) (by positivity) hsmall (fun x ↦ by
      rw [interactionRow_nonempty]
      exact interactionRow_le 8 x Φ)

/-- The full logarithm, regrouped by retained coarse support and Haar-centered. -/
def effectiveInteraction : Finset I → C(I → E, ℝ) :=
  nonlinearInteraction ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (nonempty_partition_pos ν e Φ hsmall)

def effectiveVacuum : ℝ :=
  nonlinearVacuum ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (nonempty_partition_pos ν e Φ hsmall)

theorem effectiveInteraction_norm_le :
    interactionNorm 8 (effectiveInteraction ν e Φ hsmall) ≤
      (4 * Real.exp (-2)) * interactionNorm 8 Φ :=
  nonlinearInteraction_norm_le ν e _ _ _ (fun S ↦ S.property)
    (R := interactionNorm 8 Φ) (by positivity) hsmall (fun x ↦ by
      rw [interactionRow_nonempty]
      exact interactionRow_le 8 x Φ)

theorem effectiveInteraction_local [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ S, DependsOn S (Φ S)) (T : Finset I) :
    DependsOn T (effectiveInteraction ν e Φ hsmall T) :=
  nonlinearInteraction_local ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (nonempty_partition_pos ν e Φ hsmall) (fun S ↦ hΦ S.val) T

theorem effectiveInteraction_centered (T : Finset I) :
    (∫ c, effectiveInteraction ν e Φ hsmall T c ∂Measure.pi (fun _ : I ↦ ν)) = 0 :=
  nonlinearInteraction_centered ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (nonempty_partition_pos ν e Φ hsmall) T

theorem effectiveInteraction_empty_eq_zero [Measure.IsMulLeftInvariant ν]
    (hΦ : ∀ S, DependsOn S (Φ S)) : effectiveInteraction ν e Φ hsmall ∅ = 0 :=
  nonlinearInteraction_empty_eq_zero ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
    (fun S ↦ Φ S.val) (nonempty_partition_pos ν e Φ hsmall) (fun S ↦ hΦ S.val)

theorem effectiveInteraction_reconstruct
    (hΦ : ∀ S, DependsOn S (Φ S)) (hzero : Φ ∅ = 0) (c : I → E) :
    blockedDensity ν e (interactionDensity Φ) c =
      Real.exp (effectiveVacuum ν e Φ hsmall + ∑ T, effectiveInteraction ν e Φ hsmall T c) := by
  have h := nonlinearInteraction_reconstruct ν e
    (fun S : {S : Finset X // S.Nonempty} ↦ S.val) (fun S ↦ Φ S.val)
    (nonempty_partition_pos ν e Φ hsmall) (fun S ↦ S.property) (fun S ↦ hΦ S.val) c
  simpa only [effectiveInteraction, effectiveVacuum, interactionDensity_nonempty Φ hzero] using h

end PairedHaar

/-! ## Symmetry of the extracted interaction -/

namespace PairedHaar
open WilsonBlockElimination WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {V X E : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem coefficient_eval_eq (F : Finset V → C(X → E, ℝ)) (U W : X → E)
    (hF : ∀ S, F S U = F S W) (S : Finset V) : coefficient F S U = coefficient F S W := by
  let ev (U : X → E) : C(X → E, ℝ) →+ ℝ :=
    { toFun := fun F ↦ F U, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have h := congrFun (coefficient_map (ev U) F) S
  have h' := congrFun (coefficient_map (ev W) F) S
  change _ = coefficient F S U at h
  change _ = coefficient F S W at h'
  rw [← h, ← h']
  congr 1
  exact funext hF

theorem extractedInteraction_eval_eq (ν : Measure E) [IsProbabilityMeasure ν]
    (supp : V → Finset X) (F : Finset V → C(X → E, ℝ)) (U W : X → E)
    (hF : ∀ S, F S U = F S W) (T : Finset X) :
    extractedInteraction ν supp F T U = extractedInteraction ν supp F T W := by
  simp only [extractedInteraction, regroupInteraction, ContinuousMap.sum_apply,
    centered, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply]
  apply sum_congr rfl
  intro S hS
  rw [coefficient_eval_eq F U W hF S]


variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem effectiveInteraction_eval_eq (ν : Measure E) [IsProbabilityMeasure ν]
    (e : ((I ⊕ I) ⊕ J) ≃ X) (Φ : Finset X → C(X → E, ℝ))
    (hsmall : interactionNorm 8 Φ ≤ 1/2) (U W : I → E)
    (hA : ∀ C, clusterActivity ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
      (fun S ↦ Φ S.val) C U = clusterActivity ν e (fun S : {S : Finset X // S.Nonempty} ↦ S.val)
      (fun S ↦ Φ S.val) C W) (T : Finset I) :
    effectiveInteraction ν e Φ hsmall T U = effectiveInteraction ν e Φ hsmall T W := by
  unfold effectiveInteraction nonlinearInteraction
  apply extractedInteraction_eval_eq
  intro A
  simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply]
  apply congrArg Real.log
  apply partitionFunction_congr
  intro C hC
  exact hA C

end PairedHaar

end Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection

/-! ## Spatial contraction of the complete generated interaction -/

namespace Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection.PairedHaar
open WilsonBlockElimination WilsonBlockElimination.PairedLinks WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas Mettapedia.Combinatorics.PolymerGas.SubsetExpansion
variable {X I J P : Type*} [Fintype X] [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq X] [DecidableEq I] [DecidableEq J] [DecidableEq P]
  [PseudoMetricSpace X] [PseudoMetricSpace I]
variable (e : ((I ⊕ I) ⊕ J) ≃ X) (π : X → I)
  (hπ₁ : ∀ i, π (e (.inl (.inl i))) = i)
  (hπ₂ : ∀ i, π (e (.inl (.inr i))) = i)
  (hπd : ∀ x y, dist (π x) (π y) ≤ dist x y)

include hπ₁ in
theorem retainedSupport_subset_image (S : Finset X) : retainedSupport e S ⊆ S.image π := by
  intro i hi
  exact mem_image.mpr ⟨_, ((mem_retainedSupport e S i).mp hi).1, hπ₁ i⟩

include hπ₁ hπ₂ in
theorem projectedSupport_meet {S T : Finset X}
    (hm : ¬Disjoint (fluctuationSupport e S) (fluctuationSupport e T)) :
    ¬Disjoint (S.image π) (T.image π) := by
  obtain ⟨y, hyS, hyT⟩ := not_disjoint_iff.mp hm
  rcases y with i | j
  · have hi (U : Finset X) (hU : Sum.inl i ∈ fluctuationSupport e U) : i ∈ U.image π := by
      rcases (mem_fluctuationSupport_inl e U i).mp hU with h | h
      · exact mem_image.mpr ⟨_, h, hπ₁ i⟩
      · exact mem_image.mpr ⟨_, h, hπ₂ i⟩
    exact not_disjoint_iff.mpr ⟨i, hi S hyS, hi T hyT⟩
  · exact not_disjoint_iff.mpr ⟨π (e (.inr j)),
      mem_image_of_mem π ((mem_fluctuationSupport_inr e S j).mp hyS),
      mem_image_of_mem π ((mem_fluctuationSupport_inr e T j).mp hyT)⟩

theorem fluctuationSupport_biUnion (supp : P → Finset X) (C : Finset P) :
    fluctuationSupport e (plaquetteSupport supp C) =
      plaquetteSupport (fun p => fluctuationSupport e (supp p)) C := by
  ext y
  simp only [fluctuationSupport, plaquetteSupport, biUnion_image, mem_biUnion, mem_image]

include hπ₁ hπ₂ hπd in
theorem projectedCluster_treeLength_le (supp : P → Finset X) (C : Finset P)
    (hC : C ∈ connectedPlaquettes (fun p => fluctuationSupport e (supp p))) :
    treeLength ((plaquetteSupport supp C).image π) ≤ ∑ p ∈ C, treeLength (supp p) := by
  have hc := (mem_filter.mp hC).2
  calc
    _ = treeLength (C.biUnion (fun p => (supp p).image π)) := by
      simp only [plaquetteSupport, biUnion_image]
    _ ≤ ∑ p ∈ C, treeLength ((supp p).image π) :=
      treeLength_biUnion_le_of_connected (plaquetteGraph (fun p => fluctuationSupport e (supp p)))
        _ (fun p q hpq => projectedSupport_meet e π hπ₁ hπ₂ hpq.2) C hc
    _ ≤ _ := sum_le_sum (fun p _ => treeLength_image_le π hπd (supp p))

include hπ₁ hπ₂ hπd in
theorem retainedFamily_treeLength_le (supp : P → Finset X) (A : Finset (Finset P))
    (ha : A ⊆ connectedPlaquettes (fun p => fluctuationSupport e (supp p)))
    (hc : ((plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p)))).induce
      (A : Set (Finset P))).Connected) :
    treeLength (A.biUnion (clusterRetainedSupport e supp)) ≤
      ∑ C ∈ A, ∑ p ∈ C, treeLength (supp p) := by
  calc
    _ ≤ treeLength (A.biUnion (fun C => (plaquetteSupport supp C).image π)) :=
      treeLength_mono (biUnion_mono (fun C _ => retainedSupport_subset_image e π hπ₁ _))
    _ ≤ ∑ C ∈ A, treeLength ((plaquetteSupport supp C).image π) := by
      apply treeLength_biUnion_le_of_connected _ _ _ A hc
      intro C D hCD
      apply projectedSupport_meet e π hπ₁ hπ₂
      simpa only [fluctuationSupport_biUnion] using hCD.2
    _ ≤ _ := sum_le_sum (fun C hC => projectedCluster_treeLength_le e π hπ₁ hπ₂ hπd supp C (ha hC))

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (ν : Measure E) [IsProbabilityMeasure ν]
  (supp : P → Finset X) (Φ : P → C(X → E, ℝ))
  (hpos : ∀ Λ c, 0 < partitionFunction
    (plaquetteGraph (plaquetteSupport (fun p ↦ fluctuationSupport e (supp p))))
    (fun C ↦ clusterActivity ν e supp Φ C c) Λ)

theorem clusterLogFamily_coefficient_zero_of_not_connected (A : Finset (Finset P))
    (hA : ¬((plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p)))).induce
      (A : Set (Finset P))).Connected) :
    coefficient (clusterLogFamily ν e supp Φ hpos) A = 0 := by
  ext c
  rw [coefficient_continuous_apply]
  have he : (fun B => clusterLogFamily ν e supp Φ hpos B c) =
      activatedLogPartition (plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p))))
        (fun C => clusterActivity ν e supp Φ C c)
        (connectedPlaquettes (fun p => fluctuationSupport e (supp p))) := by
    funext B
    simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply,
      activatedLogPartition]
  rw [he]
  exact coefficient_activatedLogPartition_eq_zero_of_not_connected _ _ (fun T => hpos T c) _ A hA

theorem clusterLogFamily_coefficient_zero_of_not_active (A : Finset (Finset P))
    (hA : ¬A ⊆ connectedPlaquettes (fun p => fluctuationSupport e (supp p))) :
    coefficient (clusterLogFamily ν e supp Φ hpos) A = 0 := by
  ext c
  rw [coefficient_continuous_apply]
  have he : (fun B => clusterLogFamily ν e supp Φ hpos B c) =
      (fun B => Real.log (partitionFunction
        (plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p))))
        (fun C => clusterActivity ν e supp Φ C c)
        (B ∩ connectedPlaquettes (fun p => fluctuationSupport e (supp p))))) := by
    funext B
    simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply, inter_comm]
  rw [he, coefficient_restrict (fun T => Real.log (partitionFunction
    (plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p))))
    (fun C => clusterActivity ν e supp Φ C c) T))]
  simp only [hA, ↓reduceIte, ContinuousMap.zero_apply]

def spatialClusterWeight (η : ℝ) (hη : 0 ≤ η) : UnionWeight (Finset P) :=
  supportCardinalityCostWeight (clusterRetainedSupport e supp) 8 (by norm_num)
    (fun C => η * ∑ p ∈ C, treeLength (supp p))
    (fun C => mul_nonneg hη (sum_nonneg (fun p _ => treeLength_nonneg _)))

include hπ₁ hπ₂ hπd in
theorem spatialClusterWeight_controls_coefficient {η : ℝ} (hη : 0 ≤ η)
    (A : Finset (Finset P)) :
    Real.exp (8 * (A.biUnion (clusterRetainedSupport e supp)).card +
      η * treeLength (A.biUnion (clusterRetainedSupport e supp))) *
        ‖coefficient (clusterLogFamily ν e supp Φ hpos) A‖ ≤
      spatialClusterWeight e supp η hη A * ‖coefficient (clusterLogFamily ν e supp Φ hpos) A‖ := by
  by_cases ha : A ⊆ connectedPlaquettes (fun p => fluctuationSupport e (supp p))
  · by_cases hc : ((plaquetteGraph (plaquetteSupport (fun p => fluctuationSupport e (supp p)))).induce
        (A : Set (Finset P))).Connected
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      dsimp only [spatialClusterWeight, supportCardinalityCostWeight]
      rw [← mul_sum]
      have h := mul_le_mul_of_nonneg_left
        (retainedFamily_treeLength_le e π hπ₁ hπ₂ hπd supp A ha hc) hη
      linarith
    · rw [clusterLogFamily_coefficient_zero_of_not_connected e ν supp Φ hpos A hc]
      simp
  · rw [clusterLogFamily_coefficient_zero_of_not_active e ν supp Φ hpos A ha]
    simp

theorem clusterMajorant_exp_mul (cost v : P → ℝ) (C : Finset P) :
    clusterMajorant e supp (fun p => Real.exp (cost p) * v p) C =
      Real.exp (∑ p ∈ C, cost p) * clusterMajorant e supp v C := by
  unfold clusterMajorant
  split_ifs
  · rw [Real.exp_sum, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    ring
  · simp

theorem spatial_clusterActivity_norm_le {η : ℝ} (hη : 0 ≤ η)
    (hn : ∀ p, ‖Φ p‖ ≤ 1) (C : Finset P) :
    spatialClusterWeight e supp η hη {C} * ‖clusterActivity ν e supp Φ C‖ ≤
      clusterMajorant e supp (fun p => Real.exp (η * treeLength (supp p)) * (2 * ‖Φ p‖)) C := by
  rw [clusterMajorant_exp_mul]
  simp only [spatialClusterWeight, supportCardinalityCostWeight, singleton_biUnion, sum_singleton]
  rw [← mul_sum, Real.exp_add]
  calc
    _ = Real.exp (η * ∑ p ∈ C, treeLength (supp p)) *
        (Real.exp (8 * (clusterRetainedSupport e supp C).card) * ‖clusterActivity ν e supp Φ C‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_clusterActivity_norm_le ν e supp Φ hn C) (Real.exp_pos _).le

theorem cardinality_row_le_spatial_row {η : ℝ} (hη : 0 ≤ η) (x : X) :
    (∑ p ∈ univ.filter (fun p => x ∈ supp p), Real.exp (8 * (supp p).card) * ‖Φ p‖) ≤
      ∑ p ∈ univ.filter (fun p => x ∈ supp p),
        Real.exp (8 * (supp p).card + η * treeLength (supp p)) * ‖Φ p‖ := by
  apply sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr (le_add_of_nonneg_right (mul_nonneg hη (treeLength_nonneg _)))

theorem spatial_inflated_row_le {η R : ℝ}
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p => x ∈ supp p),
      Real.exp (8 * (supp p).card + η * treeLength (supp p)) * ‖Φ p‖ ≤ R) (x : X) :
    (∑ p ∈ univ.filter (fun p => x ∈ supp p), Real.exp (8 * (supp p).card) *
      (Real.exp (η * treeLength (supp p)) * (2 * ‖Φ p‖))) ≤ 2 * R := by
  calc
    _ = 2 * ∑ p ∈ univ.filter (fun p => x ∈ supp p),
        Real.exp (8 * (supp p).card + η * treeLength (supp p)) * ‖Φ p‖ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hrow x) (by norm_num)

include hπ₁ hπ₂ hπd in
theorem clusterLogFamily_spatial_root_budget {η : ℝ} (hη : 0 ≤ η)
    (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p => x ∈ supp p),
      Real.exp (8 * (supp p).card + η * treeLength (supp p)) * ‖Φ p‖ ≤ R) (C : Finset P) :
    ∑ A ∈ univ.filter (fun A : Finset (Finset P) => C ∈ A),
      Real.exp (8 * (A.biUnion (clusterRetainedSupport e supp)).card +
        η * treeLength (A.biUnion (clusterRetainedSupport e supp))) *
        ‖coefficient (clusterLogFamily ν e supp Φ hpos) A‖ ≤
      clusterRemovalWeight e supp (fun p => Real.exp (η * treeLength (supp p)) * (2 * ‖Φ p‖)) C := by
  apply le_trans (sum_le_sum (fun A _ => spatialClusterWeight_controls_coefficient e π hπ₁ hπ₂ hπd ν supp Φ hpos hη A))
  apply sum_weighted_norm_log_coefficients_le
    (Λ := connectedPlaquettes (fun p => fluctuationSupport e (supp p)))
    _ (spatialClusterWeight e supp η hη) (clusterActivity ν e supp Φ)
    (fun C => clusterMajorant_nonneg e supp _ (fun p => by positivity) C)
    (clusterMajorant_dobrushin e supp hne (fun p => by positivity)
      (by positivity : 0 ≤ 2*R) (by linarith) (spatial_inflated_row_le supp Φ hrow))
  · intro D c
    have hn : ∀ p, ‖Φ p‖ ≤ 1 := fun p =>
      (component_norm_le_of_row supp Φ hne
        (fun x => (cardinality_row_le_spatial_row supp Φ hη x).trans (hrow x)) p).trans (by linarith)
    exact (mul_le_mul_of_nonneg_left ((clusterActivity ν e supp Φ D).norm_coe_le_norm c)
      (le_trans zero_le_one ((spatialClusterWeight e supp η hη).one_le _))).trans
        (spatial_clusterActivity_norm_le e ν supp Φ hη hn D)
  · intro A c
    simp only [clusterLogFamily, ContinuousMap.coe_mk, partitionFunction_continuous_apply, activatedLogPartition]

include hπ₁ hπ₂ hπd in
theorem nonlinearInteraction_spatial_norm_le {η : ℝ} (hη : 0 ≤ η)
    (hne : ∀ p, (supp p).Nonempty)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hrow : ∀ x, ∑ p ∈ univ.filter (fun p => x ∈ supp p),
      Real.exp (8 * (supp p).card + η * treeLength (supp p)) * ‖Φ p‖ ≤ R) :
    spatialInteractionNorm 8 η (nonlinearInteraction ν e supp Φ hpos) ≤ (4 * Real.exp (-2)) * R := by
  apply spatialInteractionNorm_le _ _ _ (by positivity)
  intro i
  calc
    _ ≤ 2 * ∑ C ∈ univ.filter (fun C => i ∈ clusterRetainedSupport e supp C),
        clusterRemovalWeight e supp (fun p => Real.exp (η * treeLength (supp p)) * (2 * ‖Φ p‖)) C :=
      extractedInteraction_weighted_row_le ν _ _ _ (fun _ => (Real.exp_pos _).le)
        (clusterLogFamily_spatial_root_budget e π hπ₁ hπ₂ hπd ν supp Φ hpos hη hne hR hR1 hrow) i
    _ ≤ 2 * (Real.exp (-2) * (2*R)) :=
      mul_le_mul_of_nonneg_left (sum_clusterRemoval_retained_le_of_row e supp _ hne
        (fun p => by positivity) (by positivity : 0 ≤ 2*R) (by linarith)
        (spatial_inflated_row_le supp Φ hrow) i) (by norm_num)
    _ = _ := by ring

theorem spatialInteractionRow_nonempty (a η : ℝ) (Ψ : Finset X → C(X → E, ℝ)) (x : X) :
    (∑ S ∈ univ.filter (fun S : {S : Finset X // S.Nonempty} => x ∈ S.val),
      Real.exp (a * S.val.card + η * treeLength S.val) * ‖Ψ S.val‖) = spatialInteractionRow a η x Ψ := by
  simp only [sum_filter, spatialInteractionRow_apply]
  exact sum_nonemptySupports (fun S => if x ∈ S then
    Real.exp (a * S.card + η * treeLength S) * ‖Ψ S‖ else 0) (by simp)

include hπ₁ hπ₂ hπd in
theorem effectiveInteraction_spatial_norm_le {η : ℝ} (hη : 0 ≤ η)
    (Ψ : Finset X → C(X → E, ℝ)) (hsmall : interactionNorm 8 Ψ ≤ 1/2)
    (hspatial : spatialInteractionNorm 8 η Ψ ≤ 1/2) :
    spatialInteractionNorm 8 η (effectiveInteraction ν e Ψ hsmall) ≤
      (4 * Real.exp (-2)) * spatialInteractionNorm 8 η Ψ :=
  nonlinearInteraction_spatial_norm_le e π hπ₁ hπ₂ hπd ν _ _ _ hη (fun S => S.property)
    (R := spatialInteractionNorm 8 η Ψ) (by positivity) hspatial (fun x => by
      rw [spatialInteractionRow_nonempty]
      exact spatialInteractionRow_le 8 η x Ψ)

end Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection.PairedHaar

/-! ## Exact polymer representation and spatial clustering of generated laws -/

namespace Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection.PairedHaar
open WilsonBlockElimination WilsonLocalResponse
open Mettapedia.Combinatorics.PolymerGas
variable {X E : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
  [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (Ψ : Finset X → C(X → E, ℝ))

def interactionActivity (S : Finset X) : (S → E) → ℂ :=
  plaquetteActivity (fun T : {S : Finset X // S.Nonempty} => T.val) (1 : E)
    (fun T ω => ((interactionFactor (Ψ T.val) ω : ℝ) : ℂ)) S

def interactionMajorant (S : Finset X) : ℝ :=
  weightedPlaquetteMajorant (fun T : {S : Finset X // S.Nonempty} => T.val)
    (fun T => 2 * ‖Ψ T.val‖) S

theorem measurable_interactionActivity (S : Finset X) : Measurable (interactionActivity Ψ S) := by
  unfold interactionActivity
  apply measurable_plaquetteActivity
  intro T
  exact Complex.measurable_ofReal.comp (interactionFactor (Ψ T.val)).continuous.measurable

theorem interactionMajorant_empty : interactionMajorant Ψ ∅ = 0 :=
  weightedPlaquetteMajorant_empty _ (fun T => T.property) _

theorem interactionActivity_bound (hsmall : interactionNorm 8 Ψ ≤ 1/2) (S : Finset X) (u : S → E) :
    ‖interactionActivity Ψ S u‖ ≤ interactionMajorant Ψ S := by
  apply norm_plaquetteActivity_le_weighted
  intro T ω
  have hn : ‖Ψ T.val‖ ≤ 1 := by
    have h := component_norm_le_of_row (fun T : {S : Finset X // S.Nonempty} => T.val)
      (fun T => Ψ T.val) (fun T => T.property) (R := (1:ℝ)/2) (fun x => by
        rw [interactionRow_nonempty]
        exact (interactionRow_le 8 x Ψ).trans hsmall) T
    linarith
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    ((interactionFactor (Ψ T.val)).norm_coe_le_norm ω).trans (interactionFactor_norm_le _ hn)

theorem interactionActivity_small {η : ℝ} (hη : 0 ≤ η)
    (hsmall : spatialInteractionNorm 8 η Ψ ≤ 1/2) :
    ActivitySmall (interactionMajorant Ψ) η (Real.exp (-3)) := by
  unfold interactionMajorant
  have hrow (x : X) :
      (∑ T ∈ univ.filter (fun T : {S : Finset X // S.Nonempty} => x ∈ T.val),
        Real.exp (8 * T.val.card + η * treeLength T.val) * (2 * ‖Ψ T.val‖)) ≤ 1 := by
    calc
      _ = 2 * spatialInteractionRow 8 η x Ψ := by
        rw [← spatialInteractionRow_nonempty, mul_sum]
        apply sum_congr rfl
        intro T _
        ring
      _ ≤ 1 := by have h := (spatialInteractionRow_le 8 η x Ψ).trans hsmall; linarith
  simpa only [mul_one, interactionMajorant] using activitySmall_weightedPlaquetteMajorant
    (fun T : {S : Finset X // S.Nonempty} => T.val) (fun T => T.property)
    (fun T => by positivity : ∀ T : {S : Finset X // S.Nonempty}, 0 ≤ 2 * ‖Ψ T.val‖)
    hη (by norm_num : (0:ℝ) ≤ 1) (by norm_num) hrow

theorem interactionDensity_eq_polymerDensity
    (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0) (ω : X → E) :
    ((interactionDensity Ψ ω : ℝ) : ℂ) = polymerDensity (interactionActivity Ψ) univ ω := by
  have h := prod_one_add_eq_polymerDensity
    (fun T : {S : Finset X // S.Nonempty} => T.val) (fun T => T.property) (1 : E)
    (fun T ω => ((interactionFactor (Ψ T.val) ω : ℝ) : ℂ))
    (fun T U V hUV => congrArg Complex.ofReal (interactionFactor_local _ _ (hΨ T.val) U V hUV)) ω
  unfold interactionActivity
  rw [← h]
  change ((Real.exp (∑ S, Ψ S ω) : ℝ) : ℂ) = _
  rw [← sum_nonemptySupports (fun S => Ψ S ω) (by simp [hzero]), Real.exp_sum, Complex.ofReal_prod]
  apply prod_congr rfl
  intro T _
  simp only [interactionFactor, ContinuousMap.coe_mk, Complex.ofReal_sub, Complex.ofReal_one]
  ring

variable (ν : Measure E) [IsProbabilityMeasure ν]

theorem polymer_expectation_eq_realExpectation
    (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0)
    (hsmall : interactionNorm 8 Ψ ≤ 1/2) (F : C(X → E, ℝ)) :
    Mettapedia.Combinatorics.PolymerGas.expectation ν (fun ω => (F ω : ℂ)) (interactionActivity Ψ) univ =
      (WilsonBlockElimination.expectation (Measure.pi fun _ : X => ν) (interactionDensity Ψ) F : ℂ) := by
  unfold Mettapedia.Combinatorics.PolymerGas.expectation
  rw [← integral_polymerDensity ν (interactionActivity Ψ) (measurable_interactionActivity Ψ)
    (interactionMajorant Ψ) (interactionActivity_bound Ψ hsmall)]
  simp_rw [← interactionDensity_eq_polymerDensity Ψ hΨ hzero]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_div,
    WilsonBlockElimination.expectation]
  congr 2
  congr 1
  funext ω
  ring

theorem covariance_interactionDensity_le {η : ℝ} (hη : 0 ≤ η)
    (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0)
    (hsmall : spatialInteractionNorm 8 η Ψ ≤ 1/2)
    (S T : Finset X) (hS : S.Nonempty) (F G : C(X → E, ℝ))
    (hF : DependsOn S F) (hG : DependsOn T G) (B C : ℝ)
    (hB : ∀ ω, |F ω| ≤ B) (hC : ∀ ω, |G ω| ≤ C) :
    |covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) F G| ≤
      3 * B * C * Real.exp (3 * S.card + 3 * T.card) * Real.exp (-η * polymerDist S T) := by
  have h0 := (interactionNorm_le_spatial 8 hη Ψ).trans hsmall
  let f : (S → E) → ℂ := fun u => (F (extendConfiguration (1 : E) S u) : ℂ)
  let g : (T → E) → ℂ := fun u => (G (extendConfiguration (1 : E) T u) : ℂ)
  have hf : Measurable f := Complex.measurable_ofReal.comp
    (F.continuous.measurable.comp (measurable_extendConfiguration _ _))
  have hg : Measurable g := Complex.measurable_ofReal.comp
    (G.continuous.measurable.comp (measurable_extendConfiguration _ _))
  have he : Real.exp (-3) * Real.exp 1 ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have h := norm_truncated_le_exp ν (interactionActivity Ψ) (measurable_interactionActivity Ψ)
    (interactionMajorant Ψ) (interactionActivity_bound Ψ h0) (interactionMajorant_empty Ψ)
    hη (Real.exp_pos (-3)).le he (interactionActivity_small Ψ hη hsmall)
    S T hS f hf B (fun u => by simpa only [f, Complex.norm_real, Real.norm_eq_abs] using hB _)
    g hg C (fun u => by simpa only [g, Complex.norm_real, Real.norm_eq_abs] using hC _) univ
  have hf' (ω : X → E) : f (restrictTo S ω) = (F ω : ℂ) := by
    apply congrArg Complex.ofReal
    apply hF
    intro x hx
    simp [extendConfiguration, restrictTo, hx]
  have hg' (ω : X → E) : g (restrictTo T ω) = (G ω : ℂ) := by
    apply congrArg Complex.ofReal
    apply hG
    intro x hx
    simp [extendConfiguration, restrictTo, hx]
  simp_rw [hf', hg', ← Complex.ofReal_mul] at h
  have hfg : (fun ω => ((F ω * G ω : ℝ) : ℂ)) = (fun ω => (((F*G) ω : ℝ) : ℂ)) := rfl
  rw [hfg, polymer_expectation_eq_realExpectation Ψ ν hΨ hzero h0,
    polymer_expectation_eq_realExpectation Ψ ν hΨ hzero h0,
    polymer_expectation_eq_realExpectation Ψ ν hΨ hzero h0,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem crossingInput_of_spatial_norm {ι : Type*} (Blocks : ι → Type*)
    [∀ L, Fintype (Blocks L)] [∀ L, DecidableEq (Blocks L)] [∀ L, PseudoMetricSpace (Blocks L)]
    (Φ : ∀ L, Finset (Blocks L) → C(Blocks L → E, ℝ)) {η : ℝ} (hη : 0 < η)
    (hsmall : ∀ L, spatialInteractionNorm 8 η (Φ L) ≤ 1/2) :
    CrossingInput.CrossingInput Blocks E (fun L => interactionActivity (Φ L)) := by
  refine ⟨fun L => measurable_interactionActivity (Φ L),
    ⟨fun L => interactionMajorant (Φ L), η, Real.exp (-3), hη, (Real.exp_pos _).le,
      (by rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by norm_num)),
      fun L => interactionActivity_bound (Φ L) ((interactionNorm_le_spatial 8 hη.le _).trans (hsmall L)),
      fun L => interactionMajorant_empty (Φ L), fun L => interactionActivity_small (Φ L) hη.le (hsmall L)⟩⟩

/-! ### Spatial budgets for decomposed observables -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A local decomposition may have arbitrarily many supports. Their
cardinality and distance from an anchor are charged in one absolute budget. -/
def anchoredObservableBudget (η : ℝ) (x : X) (supp : ι → Finset X) (F : ι → C(X → E, ℝ)) : ℝ :=
  ∑ i, Real.exp (3 * (supp i).card + η * treeLength (insert x (supp i))) * ‖F i‖

theorem covariance_anchored_le (Ψ : Finset X → C(X → E, ℝ)) (ν : Measure E) [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 ≤ η) (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0)
    (hsmall : spatialInteractionNorm 8 η Ψ ≤ 1/2) (x y : X)
    (S T : Finset X) (hS : S.Nonempty) (hT : T.Nonempty)
    (F G : C(X → E, ℝ)) (hF : DependsOn S F) (hG : DependsOn T G) :
    |covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) F G| ≤
      3 * (Real.exp (3*S.card + η*treeLength (insert x S)) * ‖F‖) *
        (Real.exp (3*T.card + η*treeLength (insert y T)) * ‖G‖) * Real.exp (-η * dist x y) := by
  apply (covariance_interactionDensity_le Ψ ν hη hΨ hzero hsmall S T hS F G hF hG ‖F‖ ‖G‖
    (fun U => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm U)
    (fun U => by simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm U)).trans
  have hd := polymerDist_ge_dist_sub_treeLength x y S T hS hT
  have he : Real.exp (-η*polymerDist S T) ≤
      Real.exp (η*treeLength (insert x S)+η*treeLength (insert y T)) * Real.exp (-η*dist x y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hd hη
    nlinarith
  calc
    _ ≤ 3*‖F‖*‖G‖*Real.exp (3*S.card+3*T.card)*
        (Real.exp (η*treeLength (insert x S)+η*treeLength (insert y T))*Real.exp (-η*dist x y)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by simp only [Real.exp_add]; ring

theorem covariance_sum_spatial_le (Ψ : Finset X → C(X → E, ℝ)) (ν : Measure E) [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 ≤ η) (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0)
    (hsmall : spatialInteractionNorm 8 η Ψ ≤ 1/2) (x y : X)
    (suppF : ι → Finset X) (suppG : κ → Finset X)
    (hSF : ∀ i, (suppF i).Nonempty) (hSG : ∀ j, (suppG j).Nonempty)
    (F : ι → C(X → E, ℝ)) (G : κ → C(X → E, ℝ))
    (hF : ∀ i, DependsOn (suppF i) (F i)) (hG : ∀ j, DependsOn (suppG j) (G j)) :
    |covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) (∑ i, F i) (∑ j, G j)| ≤
      3 * anchoredObservableBudget η x suppF F * anchoredObservableBudget η y suppG G *
        Real.exp (-η * dist x y) := by
  rw [covariance_sum]
  calc
    _ ≤ ∑ i, |∑ j, covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) (F i) (G j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) (F i) (G j)| :=
      sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, 3 * (Real.exp (3*(suppF i).card + η*treeLength (insert x (suppF i))) * ‖F i‖) *
        (Real.exp (3*(suppG j).card + η*treeLength (insert y (suppG j))) * ‖G j‖) * Real.exp (-η*dist x y) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ =>
        covariance_anchored_le Ψ ν hη hΨ hzero hsmall x y _ _ (hSF i) (hSG j) _ _ (hF i) (hG j)))
    _ = _ := by
      unfold anchoredObservableBudget
      simp only [sum_mul, mul_sum]
      exact sum_comm


omit [Fintype X] [Group E] [IsTopologicalGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
theorem anchoredObservableBudget_nonneg (η : ℝ) (x : X) (supp : ι → Finset X)
    (F : ι → C(X → E, ℝ)) : 0 ≤ anchoredObservableBudget η x supp F := by
  unfold anchoredObservableBudget
  exact sum_nonneg (fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))

/-- An exact decomposition into local pieces, with a uniform budget charging
support cardinality and tree distance from the observable's anchor. -/
def AnchoredObservableBound (η : ℝ) (x : X) (B : ℝ) (F : C(X → E, ℝ)) : Prop :=
  ∃ f : {S : Finset X // S.Nonempty} → C(X → E, ℝ),
    (∀ S, DependsOn S.val (f S)) ∧ F = ∑ S, f S ∧
      anchoredObservableBudget η x (fun S => S.val) f ≤ B

theorem AnchoredObservableBound.nonneg {η : ℝ} {x : X} {B : ℝ} {F : C(X → E, ℝ)}
    (hF : AnchoredObservableBound η x B F) : 0 ≤ B := by
  obtain ⟨f, _, _, hf⟩ := hF
  exact (anchoredObservableBudget_nonneg _ _ _ _).trans hf

theorem AnchoredObservableBound.of_local (η : ℝ) (x : X) (S : Finset X) (hS : S.Nonempty)
    (F : C(X → E, ℝ)) (hF : DependsOn S F) :
    AnchoredObservableBound η x (Real.exp (3*S.card + η*treeLength (insert x S)) * ‖F‖) F := by
  let s : {S : Finset X // S.Nonempty} := ⟨S, hS⟩
  let f : {S : Finset X // S.Nonempty} → C(X → E, ℝ) := fun T => if T=s then F else 0
  refine ⟨f, ?_, ?_, ?_⟩
  · intro T U V hUV
    by_cases hT : T=s
    · subst T; simpa [f, s] using hF U V hUV
    · simp [f, hT]
  · simp [f]
  · simp only [anchoredObservableBudget, f, apply_ite norm, norm_zero, mul_ite, mul_zero]
    simp [s]

theorem covariance_of_anchoredBounds (Ψ : Finset X → C(X → E, ℝ)) (ν : Measure E) [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 ≤ η) (hΨ : ∀ S, DependsOn S (Ψ S)) (hzero : Ψ ∅ = 0)
    (hsmall : spatialInteractionNorm 8 η Ψ ≤ 1/2) (x y : X) {B C : ℝ}
    (F G : C(X → E, ℝ)) (hF : AnchoredObservableBound η x B F) (hG : AnchoredObservableBound η y C G) :
    |covariance (Measure.pi fun _ : X => ν) (interactionDensity Ψ) F G| ≤
      3 * B * C * Real.exp (-η * dist x y) := by
  have hB := hF.nonneg
  have hC := hG.nonneg
  obtain ⟨f, hf, rfl, hfB⟩ := hF
  obtain ⟨g, hg, rfl, hgC⟩ := hG
  apply (covariance_sum_spatial_le Ψ ν hη hΨ hzero hsmall x y
    (fun S : {S : Finset X // S.Nonempty} => S.val)
    (fun S : {S : Finset X // S.Nonempty} => S.val)
    (fun S => S.property) (fun S => S.property) f g hf hg).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfB (by norm_num)) hgC
    (anchoredObservableBudget_nonneg _ _ _ _) (by positivity)


end Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection.PairedHaar

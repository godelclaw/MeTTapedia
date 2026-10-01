import Mettapedia.QuantumTheory.YangMills.WilsonProductLocality
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicLocality

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
the exponential support-cardinality norm. This linear statement does not
assert a nonlinear bound for the logarithm of the generated density.
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

def interactionRow {Y : Type*} [Fintype Y] [DecidableEq Y] (a : ℝ) (i : Y) :
    Seminorm ℝ (Finset Y → C(Y → E, ℝ)) :=
  Seminorm.of (fun Φ ↦ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
      Real.exp (a * S.card) * ‖Φ S‖)
    (fun Φ Ψ ↦ by
      calc
        _ ≤ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
            Real.exp (a * S.card) * (‖Φ S‖ + ‖Ψ S‖) :=
          Finset.sum_le_sum (fun S _ ↦
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le)
        _ = _ := by simp only [mul_add, Finset.sum_add_distrib])
    (fun c Φ ↦ by
      simp only [Pi.smul_apply, norm_smul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring)

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
theorem interactionRow_regroup_le (support : P → Finset Y) (F : P → C(Y → E, ℝ))
    (a : ℝ) (i : Y) :
    interactionRow a i (regroupInteraction support F) ≤
      ∑ p ∈ univ.filter (fun p ↦ i ∈ support p), Real.exp (a * (support p).card) * ‖F p‖ := by
  calc
    _ ≤ ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
        ∑ p ∈ univ.filter (fun p ↦ support p = S), Real.exp (a * S.card) * ‖F p‖ := by
      apply Finset.sum_le_sum
      intro S _
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ = ∑ S ∈ univ.filter (fun S : Finset Y ↦ i ∈ S),
        ∑ p ∈ univ.filter (fun p ↦ support p = S), Real.exp (a * (support p).card) * ‖F p‖ := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ = _ := by
      simpa only [mem_filter, mem_univ, true_and] using
        Finset.sum_fiberwise_eq_sum_filter (univ : Finset P)
          (univ.filter (fun S : Finset Y ↦ i ∈ S)) support
          (fun p ↦ Real.exp (a * (support p).card) * ‖F p‖)

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

end Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection

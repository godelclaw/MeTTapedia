import Mettapedia.QuantumTheory.YangMills.WilsonProductLocality
import Mettapedia.QuantumTheory.YangMills.WilsonDyadicLocality

/-!
# Conditional Wilson projection depends only on the geometric boundary

At fixed retained coordinates, plaquettes incident to an affected interior
component form a local density. The complementary plaquettes involve no
variables in that component and cancel from the normalized expectation.
The dependence of the projected mark is then read from the original
plaquette supports, with no coupling restriction.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
namespace Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection
open StrongCouplingCrossing InhomogeneousWilsonCrossing WilsonLocalResponse
open WilsonBoundaryChanges WilsonPinnedIntegral WilsonPatchGeometry
open WilsonProductLocality WilsonBlockElimination

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
end Mettapedia.QuantumTheory.YangMills.WilsonConditionalProjection

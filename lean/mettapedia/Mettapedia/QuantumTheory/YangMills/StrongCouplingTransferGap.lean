import Mettapedia.QuantumTheory.YangMills.WilsonReflectionPositivity
import Mettapedia.QuantumTheory.YangMills.TransferGapClustering
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Strong-coupling transfer bounds on finite-group lattices

For a finite gauge group, the Wilson transfer matrix acts on functions of all
spatial links in one time slice. Its kernel is obtained by summing the temporal
link variables between adjacent slices, with half of the spatial action assigned
to each side. For a conjugation-invariant, inversion-even potential in `[0, 2]`,
`WilsonFinite.uniform_transfer_gap` proves a positive simple leading eigenvalue
and a uniform absolute bound on every other normalized eigenvalue at strong
coupling. The bound holds on the full spatial state space.

Here `d` is the spatial dimension. Rectangular tori have temporal extent `T + 3`
and spatial extent `L + 3`. The threshold is the earlier strong-coupling threshold
in total dimension `d + 1`; the decay rate is independent of both extents.

The proof identifies Wilson expectations exactly with cyclic matrix products,
uses time-slice clustering to bound the excess of squared traces over traces of
squares, and applies the finite-dimensional spectral theorem. The exponential
rate survives the limit in time, while the spatial-volume prefactor drops out.
The one-step kernel is symmetric and entrywise positive, but its spectrum need
not be nonnegative for these general potentials. Squaring the kernel handles
both signs; positivity of odd power traces identifies the leading sign.
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory Filter Topology
open Mettapedia.Combinatorics.PolymerGas

namespace Mettapedia.QuantumTheory.YangMills.StrongCouplingTransferGap

namespace Rectangular

/-- One time coordinate and a spatial torus. Both periods are at least three. -/
abbrev Site (d T L : ℕ) := ZMod (T + 3) × StrongCouplingCrossing.Site d L
abbrev Link (d T L : ℕ) := Site d T L × Fin (d + 1)
abbrev Plaquette (d T L : ℕ) := Site d T L × StrongCouplingCrossing.Plane (d + 1)

/-- Direction zero is time; successor directions are spatial. -/
def step {d T L : ℕ} : Fin (d + 1) → Site d T L :=
  Fin.cases (1, 0) (fun i => (0, StrongCouplingCrossing.step i))

@[simp] theorem step_zero {d T L : ℕ} : step (d := d) (T := T) (L := L) 0 = (1, 0) := rfl
@[simp] theorem step_succ {d T L : ℕ} (i : Fin d) :
    step (T := T) (L := L) i.succ = (0, StrongCouplingCrossing.step i) := rfl

def linkAt {d T L : ℕ} (p : Plaquette d T L) : Fin 4 → Link d T L :=
  ![(p.1, p.2.1.1), (p.1 + step p.2.1.1, p.2.1.2),
    (p.1 + step p.2.1.2, p.2.1.1), (p.1, p.2.1.2)]

def support {d T L : ℕ} (p : Plaquette d T L) : Finset (Link d T L) := univ.image (linkAt p)

theorem support_nonempty {d T L : ℕ} (p : Plaquette d T L) : (support p).Nonempty :=
  ⟨linkAt p 0, mem_image.mpr ⟨0, mem_univ _, rfl⟩⟩

theorem card_support_le {d T L : ℕ} (p : Plaquette d T L) : (support p).card ≤ 4 := by
  simpa [support] using (card_image_le (s := (univ : Finset (Fin 4))) (f := linkAt p))

/-- Only temporal separation enters this pseudometric. -/
def timePosition {d T L : ℕ} (l : Link d T L) : AddCircle (T + 3 : ℝ) :=
  StrongCouplingCrossing.coordinateCircle T l.1.1

instance linkPseudoMetricSpace (d T L : ℕ) : PseudoMetricSpace (Link d T L) :=
  PseudoMetricSpace.induced timePosition inferInstance

@[simp] theorem dist_link_eq {d T L : ℕ} (l m : Link d T L) :
    dist l m = dist (timePosition l) (timePosition m) := rfl

theorem step_time {d T L : ℕ} (μ : Fin (d + 1)) :
    (step (T := T) (L := L) μ).1 = 0 ∨ (step (T := T) (L := L) μ).1 = 1 := by
  refine Fin.cases ?_ (fun i => ?_) μ <;> simp

theorem linkAt_time {d T L : ℕ} (p : Plaquette d T L) (i : Fin 4) :
    (linkAt p i).1.1 = p.1.1 ∨ (linkAt p i).1.1 = p.1.1 + 1 := by
  fin_cases i
  · simp [linkAt]
  · rcases step_time (T := T) (L := L) p.2.1.1 with h | h <;> simp [linkAt, h]
  · rcases step_time (T := T) (L := L) p.2.1.2 with h | h <;> simp [linkAt, h]
  · simp [linkAt]

theorem diam_support_le {d T L : ℕ} (p : Plaquette d T L) : polymerDiam (support p) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le (by norm_num)
  intro l hl m hm
  obtain ⟨i, _, rfl⟩ := mem_image.mp hl
  obtain ⟨j, _, rfl⟩ := mem_image.mp hm
  exact StrongCouplingCrossing.dist_coordinateCircle_le_one (linkAt_time p i) (linkAt_time p j)

/-- For fixed directions and a fixed boundary position, the link determines
the base point of a plaquette. -/
theorem linkAt_base_injective {d T L : ℕ} (a : StrongCouplingCrossing.Plane (d + 1)) (i : Fin 4) :
    Function.Injective (fun x : Site d T L => linkAt (x, a) i) := by
  fin_cases i <;> intro x y h <;>
    simpa [linkAt] using congrArg Prod.fst h

theorem plaquette_eq_of_plane_linkAt_eq {d T L : ℕ} {p q : Plaquette d T L} {i : Fin 4}
    (ha : p.2 = q.2) (hl : linkAt p i = linkAt q i) : p = q := by
  rcases p with ⟨x, a⟩
  rcases q with ⟨y, b⟩
  change a = b at ha
  subst b
  exact Prod.ext (linkAt_base_injective a i hl) rfl

/-- A fixed boundary position contributes at most `(d + 1)²` plaquettes through a link. -/
theorem card_linkAt_fiber_le {d T L : ℕ} (l : Link d T L) (i : Fin 4) :
    ((univ : Finset (Plaquette d T L)).filter (fun p => linkAt p i = l)).card ≤ (d + 1) * (d + 1) := by
  have h := card_le_card_of_injOn (s := univ.filter (fun p : Plaquette d T L => linkAt p i = l))
    (t := (univ : Finset (Fin (d + 1) × Fin (d + 1)))) (fun p => p.2.1)
    (fun _ _ => mem_univ _) (fun p hp q hq heq =>
      plaquette_eq_of_plane_linkAt_eq (Subtype.ext heq)
        ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))
  simpa using h

/-- A volume-independent incidence bound. -/
theorem card_incident_le (d T L : ℕ) (l : Link d T L) :
    ((univ : Finset (Plaquette d T L)).filter (fun p => l ∈ support p)).card ≤ 4 * ((d + 1) * (d + 1)) := by
  have hsub : (univ.filter (fun p : Plaquette d T L => l ∈ support p)) ⊆
      (univ : Finset (Fin 4)).biUnion
        (fun i => univ.filter (fun p : Plaquette d T L => linkAt p i = l)) := by
    intro p hp
    obtain ⟨i, _, hi⟩ := mem_image.mp (mem_filter.mp hp).2
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  refine (card_le_card hsub).trans ?_
  simpa using card_biUnion_le_card_mul (univ : Finset (Fin 4))
    (fun i => univ.filter (fun p : Plaquette d T L => linkAt p i = l)) ((d + 1) * (d + 1))
    (fun i _ => card_linkAt_fiber_le l i)

open scoped Classical in
/-- The plaquette overlap graph has degree at most `16 (d + 1)²`, uniformly in volume. -/
theorem degree_plaquetteGraph_le (d T L : ℕ) (p : Plaquette d T L) :
    (plaquetteGraph (support (d := d) (T := T) (L := L))).degree p ≤ 16 * ((d + 1) * (d + 1)) := by
  have hsub : (plaquetteGraph (support (d := d) (T := T) (L := L))).neighborFinset p ⊆
      (support p).biUnion (fun l => univ.filter (fun q : Plaquette d T L => l ∈ support q)) := by
    intro q hq
    have hq' := ((plaquetteGraph (support (d := d) (T := T) (L := L))).mem_neighborFinset p q).mp hq
    obtain ⟨l, hlp, hlq⟩ := not_disjoint_iff.mp hq'.2
    exact mem_biUnion.mpr ⟨l, hlp, mem_filter.mpr ⟨mem_univ _, hlq⟩⟩
  calc
    _ ≤ ((support p).biUnion
        (fun l => univ.filter (fun q : Plaquette d T L => l ∈ support q))).card := card_le_card hsub
    _ ≤ (support p).card * (4 * ((d + 1) * (d + 1))) :=
      card_biUnion_le_card_mul _ _ _ (fun l _ => card_incident_le d T L l)
    _ ≤ 4 * (4 * ((d + 1) * (d + 1))) := Nat.mul_le_mul_right _ (card_support_le p)
    _ = _ := by omega

section Potential

variable {E : Type*} [MeasurableSpace E]

/-- Evaluate the four-link potential in boundary order. -/
def potential {d : ℕ} {v : ℕ × ℕ} (φ : (Fin 4 → E) → ℝ) (p : Plaquette d v.1 v.2)
    (ω : Link d v.1 v.2 → E) : ℝ := φ (fun i => ω (linkAt p i))

/-- The local perturbation relative to the product reference measure. -/
def perturbation {d : ℕ} {v : ℕ × ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) (p : Plaquette d v.1 v.2)
    (ω : Link d v.1 v.2 → E) : ℂ := (Real.exp (-β * potential φ p ω) : ℂ) - 1

/-- The finite Wilson-type Boltzmann density. -/
def wilsonDensity {d : ℕ} {v : ℕ × ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) (ω : Link d v.1 v.2 → E) : ℂ :=
  ∏ p : Plaquette d v.1 v.2, (Real.exp (-β * potential φ p ω) : ℂ)

/-- Connected plaquette activities as functions of their link variables. -/
def activity (d : ℕ) (base : E) (φ : (Fin 4 → E) → ℝ) (β : ℝ)
    (v : ℕ × ℕ) (S : Finset (Link d v.1 v.2)) : (S → E) → ℂ :=
  plaquetteActivity support base (perturbation φ β) S

omit [MeasurableSpace E] in
theorem perturbation_local {d : ℕ} {v : ℕ × ℕ} (φ : (Fin 4 → E) → ℝ) (β : ℝ) :
    PlaquetteLocal (support (d := d) (T := v.1) (L := v.2)) (perturbation φ β) := by
  intro p ω ω' h
  have hp : potential φ p ω = potential φ p ω' := by
    apply congrArg φ
    funext i
    exact h _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  simp only [perturbation, hp]

theorem measurable_potential {d : ℕ} {v : ℕ × ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (p : Plaquette d v.1 v.2) : Measurable (potential φ p) :=
  hφ.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)

theorem measurable_perturbation {d : ℕ} {v : ℕ × ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (β : ℝ) (p : Plaquette d v.1 v.2) : Measurable (perturbation φ β p) := by
  exact (Complex.measurable_ofReal.comp
    ((measurable_const.mul (measurable_potential hφ p)).exp)).sub measurable_const

omit [MeasurableSpace E] in
/-- The perturbation is bounded by twice the coupling for a potential in `[0,2]`. -/
theorem norm_perturbation_le {d : ℕ} {v : ℕ × ℕ} {φ : (Fin 4 → E) → ℝ}
    (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2) {β : ℝ} (hβ : 0 ≤ β)
    (p : Plaquette d v.1 v.2) (ω : Link d v.1 v.2 → E) : ‖perturbation φ β p ω‖ ≤ 2 * β := by
  have hp0 : 0 ≤ potential φ p ω := hφ0 _
  have hp2 : potential φ p ω ≤ 2 := hφ2 _
  have he : Real.exp (-β * potential φ p ω) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  unfold perturbation
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have := Real.add_one_le_exp (-β * potential φ p ω)
  nlinarith

omit [MeasurableSpace E] in
/-- The exact Wilson density is the density of the connected polymer gas. -/
theorem wilsonDensity_eq_polymerDensity (d : ℕ) (v : ℕ × ℕ) (base : E)
    (φ : (Fin 4 → E) → ℝ) (β : ℝ) (ω : Link d v.1 v.2 → E) :
    wilsonDensity φ β ω = polymerDensity (activity d base φ β v) univ ω := by
  unfold activity
  convert prod_one_add_eq_polymerDensity support support_nonempty base
    (perturbation φ β) (perturbation_local φ β) ω using 1
  simp [wilsonDensity, perturbation]

/-- The same threshold as for the isotropic lattice, in total dimension `d + 1`. -/
abbrev beta0 (d : ℕ) : ℝ := StrongCouplingCrossing.beta0 (d + 1)

theorem beta0_pos (d : ℕ) : 0 < beta0 d := StrongCouplingCrossing.beta0_pos (d + 1)

/-- The connected plaquette activities satisfy the crossing input at strong
coupling, with decay rate one and smallness `exp (-1)` at every volume. -/
theorem crossingInput (d : ℕ) (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    CrossingInput.CrossingInput (fun v : ℕ × ℕ => Link d v.1 v.2) E (activity d base φ β) := by
  have : Nonempty E := ⟨base⟩
  refine ⟨fun v S => measurable_plaquetteActivity support base (perturbation φ β)
    (measurable_perturbation hφ β) S, ?_⟩
  refine ⟨fun v => plaquetteMajorant (support (d := d) (T := v.1) (L := v.2)) (2 * β),
    1, Real.exp (-1), by norm_num, (Real.exp_pos _).le, ?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add]
    norm_num
  · intro v S v
    exact norm_plaquetteActivity_le support base (perturbation φ β)
      (norm_perturbation_le hφ0 hφ2 hβ) S v
  · intro v
    exact plaquetteMajorant_empty support support_nonempty _
  · intro v
    apply activitySmall_plaquetteMajorant support
      (δ := 2 * β) (κ := 1) (r := 1) (ε := Real.exp (-1))
      (s := 4) (Δ := 16 * ((d + 1) * (d + 1))) (D := 4 * ((d + 1) * (d + 1)))
      (by positivity) (by norm_num) (by norm_num) (Real.exp_pos _).le
    · rw [← Real.exp_add]
      norm_num
    · exact card_support_le
    · exact diam_support_le
    · intro p
      convert degree_plaquetteGraph_le d v.1 v.2 p using 1
      congr 1
      exact Subsingleton.elim _ _
    · exact card_incident_le d v.1 v.2
    · unfold beta0 StrongCouplingCrossing.beta0 at hβ0
      linarith

/-- Expectation against the finite Wilson density over the product reference law. -/
def wilsonExpectation {d : ℕ} {v : ℕ × ℕ} (ν₀ : Measure E) (φ : (Fin 4 → E) → ℝ) (β : ℝ)
    (F : (Link d v.1 v.2 → E) → ℂ) : ℂ :=
  (∫ ω, F ω * wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d v.1 v.2 => ν₀)) /
    (∫ ω, wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d v.1 v.2 => ν₀))

/-- The ratio of Wilson integrals agrees with the polymer expectation. -/
theorem wilsonExpectation_eq_expectation {d : ℕ} {v : ℕ × ℕ} (ν₀ : Measure E)
    [IsProbabilityMeasure ν₀] (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (F : (Link d v.1 v.2 → E) → ℂ) :
    wilsonExpectation ν₀ φ β F = expectation ν₀ F (activity d base φ β v) univ := by
  have : Nonempty E := ⟨base⟩
  unfold wilsonExpectation expectation
  simp_rw [wilsonDensity_eq_polymerDensity d v base]
  rw [integral_polymerDensity ν₀ (activity d base φ β v)
    (fun S => measurable_plaquetteActivity support base (perturbation φ β)
      (measurable_perturbation hφ β) S)
    (plaquetteMajorant support (2 * β))
    (norm_plaquetteActivity_le support base (perturbation φ β)
      (norm_perturbation_le hφ0 hφ2 hβ))]

/-- The Wilson normalizing integral is nonzero throughout the stated regime. -/
theorem integral_wilsonDensity_ne_zero (d : ℕ) (v : ℕ × ℕ) (ν₀ : Measure E)
    [IsProbabilityMeasure ν₀] (base : E) {φ : (Fin 4 → E) → ℝ}
    (hφ : Measurable φ) (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    (∫ ω, wilsonDensity φ β ω ∂(Measure.pi fun _ : Link d v.1 v.2 => ν₀)) ≠ 0 := by
  have : Nonempty E := ⟨base⟩
  have hc := crossingInput d base hφ hφ0 hφ2 hβ hβ0
  obtain ⟨bound, rate, ε, hr, he0, he, hbound, hempty, hsmall⟩ := hc.exists_bounds
  simp_rw [wilsonDensity_eq_polymerDensity d v base]
  rw [integral_polymerDensity ν₀ (activity d base φ β v)
    (hc.measurable_activity v) (bound v) (hbound v)]
  exact (removalBound_of_dobrushin
    (dobrushin_of_activitySmall ν₀ (activity d base φ β v) (bound v)
      (hbound v) (hempty v) hr.le he0 he (hsmall v)) univ).1

/-- Uniform exponential clustering of the Wilson expectations at strong coupling. -/
theorem wilson_clustering (d : ℕ) (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    {φ : (Fin 4 → E) → ℝ} (hφ : Measurable φ)
    (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (v : ℕ × ℕ) (S₁ S₂ : Finset (Link d v.1 v.2)), S₁.Nonempty →
      ∀ (F₁ : (S₁ → E) → ℂ) (F₂ : (S₂ → E) → ℂ) (C₁ C₂ : ℝ),
      Measurable F₁ → Measurable F₂ → (∀ v, ‖F₁ v‖ ≤ C₁) → (∀ v, ‖F₂ v‖ ≤ C₂) →
      ‖wilsonExpectation ν₀ φ β (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) -
        wilsonExpectation ν₀ φ β (fun ω => F₁ (restrictTo S₁ ω)) *
          wilsonExpectation ν₀ φ β (fun ω => F₂ (restrictTo S₂ ω))‖ ≤
        3 * C₁ * C₂ * Real.exp (3 * S₁.card + 3 * S₂.card) *
          Real.exp (-κ * polymerDist S₁ S₂) := by
  have : Nonempty E := ⟨base⟩
  obtain ⟨κ, hκ, hc⟩ := CrossingInput.clustering (ν₀ := ν₀)
    (crossingInput d base hφ hφ0 hφ2 hβ hβ0)
  refine ⟨κ, hκ, ?_⟩
  intro v S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂
  simp_rw [wilsonExpectation_eq_expectation ν₀ base hφ hφ0 hφ2 hβ]
  exact hc v univ S₁ S₂ hS₁ F₁ F₂ C₁ C₂ hF₁ hF₂ hb₁ hb₂

end Potential

/-- Links based at a fixed time, including the outgoing temporal links. -/
def sliceSupport {d T L : ℕ} (t : ZMod (T + 3)) : Finset (Link d T L) :=
  univ.image (fun l : StrongCouplingCrossing.Site d L × Fin (d + 1) => ((t, l.1), l.2))

@[simp] theorem mem_sliceSupport {d T L : ℕ} (t : ZMod (T + 3)) (l : Link d T L) :
    l ∈ sliceSupport (d := d) (L := L) t ↔ l.1.1 = t := by
  constructor
  · intro h
    obtain ⟨x, _, hx⟩ := mem_image.mp h
    exact (congrArg (fun l : Link d T L => l.1.1) hx).symm
  · intro h
    exact mem_image.mpr ⟨(l.1.2, l.2), mem_univ _, by cases l; cases ‹Site d T L›; simp_all⟩

theorem sliceSupport_nonempty {d T L : ℕ} (t : ZMod (T + 3)) :
    (sliceSupport (d := d) (L := L) t).Nonempty :=
  ⟨((t, 0), 0), (mem_sliceSupport _ _).mpr rfl⟩

theorem card_sliceSupport {d T L : ℕ} (t : ZMod (T + 3)) :
    (sliceSupport (d := d) (L := L) t).card = (L + 3) ^ d * (d + 1) := by
  rw [sliceSupport, card_image_of_injective]
  · simp [StrongCouplingCrossing.Site]
  · intro x y h
    exact Prod.ext (congrArg (fun l : Link d T L => l.1.2) h) (congrArg (fun l : Link d T L => l.2) h)

theorem time_dist_le_slice_dist {d T L : ℕ} (t s : ZMod (T + 3)) :
    dist (StrongCouplingCrossing.coordinateCircle T t)
      (StrongCouplingCrossing.coordinateCircle T s) ≤
        polymerDist (sliceSupport (d := d) (L := L) t) (sliceSupport s) := by
  rw [polymerDist, dite_eq_left (sliceSupport_nonempty s)]
  apply le_inf'
  intro l hl
  apply (Metric.le_infDist (sliceSupport_nonempty t)).mpr
  intro m hm
  have hl' := (mem_sliceSupport s l).mp hl
  have hm' := (mem_sliceSupport t m).mp hm
  simp only [dist_link_eq, timePosition, hl', hm']
  exact (dist_comm _ _).le

theorem coordinate_dist_nat {T k : ℕ} (hk : 2 * k ≤ T + 3) :
    dist (StrongCouplingCrossing.coordinateCircle T 0)
      (StrongCouplingCrossing.coordinateCircle T (k : ZMod (T + 3))) = k := by
  have hlt : k < T + 3 := by omega
  have hle : (2 : ℝ) * k ≤ (T + 3 : ℝ) := by exact_mod_cast hk
  rw [map_zero, dist_zero_left, StrongCouplingCrossing.coordinateCircle_apply,
    ZMod.val_cast_of_lt hlt]
  rw [(AddCircle.norm_coe_eq_abs_iff (T + 3 : ℝ) (by positivity : (T + 3 : ℝ) ≠ 0)).mpr]
  · exact abs_of_nonneg (Nat.cast_nonneg _)
  · rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (by positivity : (0 : ℝ) < T + 3)]
    linarith

/-- Read the spatial links of one time slice. -/
def sliceConfiguration {E : Type*} {d T L : ℕ} (t : ZMod (T + 3))
    (ω : Link d T L → E) : StrongCouplingCrossing.Link d L → E :=
  fun l => ω ((t, l.1), l.2.succ)

def sliceObservable {E : Type*} {d T L : ℕ} (t : ZMod (T + 3))
    (F : (StrongCouplingCrossing.Link d L → E) → ℂ) :
    (sliceSupport (d := d) (L := L) t → E) → ℂ :=
  fun v => F (fun l => v ⟨((t, l.1), l.2.succ), (mem_sliceSupport _ _).mpr rfl⟩)

@[simp] theorem sliceObservable_restrict {E : Type*} {d T L : ℕ} (t : ZMod (T + 3))
    (F : (StrongCouplingCrossing.Link d L → E) → ℂ) (ω : Link d T L → E) :
    sliceObservable t F (restrictTo (sliceSupport t) ω) = F (sliceConfiguration t ω) := rfl

theorem measurable_sliceObservable {E : Type*} [MeasurableSpace E] {d T L : ℕ}
    (t : ZMod (T + 3)) {F : (StrongCouplingCrossing.Link d L → E) → ℂ} (hF : Measurable F) :
    Measurable (sliceObservable t F) :=
  hF.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)

/-- The decay rate is uniform in both extents; the prefactor depends only on the
spatial extent and the bounds of the two slice observables. -/
theorem slice_clustering {E : Type*} [MeasurableSpace E] (d : ℕ)
    (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    {φ : (Fin 4 → E) → ℝ} (hφ : Measurable φ)
    (hφ0 : ∀ v, 0 ≤ φ v) (hφ2 : ∀ v, φ v ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ beta0 d) :
    ∃ κ > 0, ∀ (T L k : ℕ), 2 * k ≤ T + 3 →
      ∀ (F G : (StrongCouplingCrossing.Link d L → E) → ℂ) (C D : ℝ),
      Measurable F → Measurable G → (∀ v, ‖F v‖ ≤ C) → (∀ v, ‖G v‖ ≤ D) →
      ‖wilsonExpectation (v := (T, L)) ν₀ φ β
          (fun ω => F (sliceConfiguration 0 ω) * G (sliceConfiguration (k : ZMod (T + 3)) ω)) -
        wilsonExpectation (v := (T, L)) ν₀ φ β (fun ω => F (sliceConfiguration 0 ω)) *
          wilsonExpectation (v := (T, L)) ν₀ φ β (fun ω => G (sliceConfiguration (k : ZMod (T + 3)) ω))‖ ≤
        3 * C * D * Real.exp (6 * ((L + 3) ^ d * (d + 1) : ℕ)) * Real.exp (-κ * k) := by
  obtain ⟨κ, hκ, hc⟩ := wilson_clustering d ν₀ base hφ hφ0 hφ2 hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro T L k hk F G C D hF hG hFb hGb
  have hb := hc (T, L) (sliceSupport 0) (sliceSupport (k : ZMod (T + 3)))
    (sliceSupport_nonempty 0) (sliceObservable 0 F) (sliceObservable _ G) C D
    (measurable_sliceObservable _ hF) (measurable_sliceObservable _ hG)
    (fun _ => hFb _) (fun _ => hGb _)
  simp only [sliceObservable_restrict, card_sliceSupport] at hb
  have hC : 0 ≤ C := (norm_nonneg (F fun _ => base)).trans (hFb _)
  have hD : 0 ≤ D := (norm_nonneg (G fun _ => base)).trans (hGb _)
  have hd := time_dist_le_slice_dist (d := d) (L := L) 0 (k : ZMod (T + 3))
  rw [coordinate_dist_nat hk] at hd
  refine hb.trans ?_
  have he : (3 : ℝ) * ((L + 3) ^ d * (d + 1) : ℕ) +
      3 * ((L + 3) ^ d * (d + 1) : ℕ) = 6 * ((L + 3) ^ d * (d + 1) : ℕ) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

end Rectangular

namespace WilsonFinite

open StrongCouplingTwist (holonomy)

variable {E : Type*} [Group E] [Fintype E] {d L : ℕ}

def planeJoin {d : ℕ} : Fin d ⊕ StrongCouplingCrossing.Plane d →
    StrongCouplingCrossing.Plane (d + 1)
  | .inl i => ⟨(0, i.succ), by simp⟩
  | .inr a => ⟨(a.1.1.succ, a.1.2.succ), by
      have := a.2
      simpa only [Fin.lt_def, Fin.val_succ, Nat.add_lt_add_iff_right] using this⟩

theorem planeJoin_bijective (d : ℕ) : Function.Bijective (planeJoin (d := d)) := by
  constructor
  · intro a b h
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        apply congrArg Sum.inl
        exact Fin.succ_injective d (congrArg (fun p : StrongCouplingCrossing.Plane (d + 1) => p.1.2) h)
      | inr b =>
        have he := congrArg (fun p : StrongCouplingCrossing.Plane (d + 1) => p.1.1) h
        exact False.elim ((Fin.succ_ne_zero b.1.1) he.symm)
    | inr a =>
      cases b with
      | inl j =>
        have he := congrArg (fun p : StrongCouplingCrossing.Plane (d + 1) => p.1.1) h
        simp [planeJoin] at he
      | inr b =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact Prod.ext (Fin.succ_injective d (congrArg (fun p : StrongCouplingCrossing.Plane (d + 1) => p.1.1) h))
          (Fin.succ_injective d (congrArg (fun p : StrongCouplingCrossing.Plane (d + 1) => p.1.2) h))
  · rintro ⟨⟨μ, ν⟩, hlt⟩
    cases μ using Fin.cases with
    | zero =>
      cases ν using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hlt)
      | succ ν => exact ⟨.inl ν, rfl⟩
    | succ μ =>
      cases ν using Fin.cases with
      | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hlt)
      | succ ν =>
        exact ⟨.inr ⟨(μ, ν), by simpa only [Fin.succ_lt_succ_iff] using hlt⟩, rfl⟩

def planeEquiv (d : ℕ) : Fin d ⊕ StrongCouplingCrossing.Plane d ≃
    StrongCouplingCrossing.Plane (d + 1) := Equiv.ofBijective planeJoin (planeJoin_bijective d)

/-- Spatial link variables on one time slice. -/
abbrev State (E : Type*) (d L : ℕ) := StrongCouplingCrossing.Link d L → E

/-- Temporal link variables between two successive slices. -/
abbrev Temporal (E : Type*) (d L : ℕ) := StrongCouplingCrossing.Site d L → E

def assemble {T : ℕ} (U : ZMod (T + 3) → State E d L)
    (h : ZMod (T + 3) → Temporal E d L) : Rectangular.Link d T L → E :=
  fun l => Fin.cases (h l.1.1 l.1.2) (fun i => U l.1.1 (l.1.2, i)) l.2

def configurationEquiv (d T L : ℕ) :
    (ZMod (T + 3) → State E d L) × (ZMod (T + 3) → Temporal E d L) ≃
      (Rectangular.Link d T L → E) where
  toFun x := assemble x.1 x.2
  invFun ω := (fun t => Rectangular.sliceConfiguration t ω, fun t x => ω ((t, x), 0))
  left_inv x := by
    apply Prod.ext
    · funext t l
      rfl
    · funext t x
      rfl
  right_inv ω := by
    funext l
    rcases l with ⟨⟨t, x⟩, μ⟩
    cases μ using Fin.cases <;> rfl

omit [Fintype E] in
theorem holonomy_spatial {T : ℕ} (U : ZMod (T + 3) → State E d L)
    (h : ZMod (T + 3) → Temporal E d L) (t : ZMod (T + 3))
    (p : StrongCouplingCrossing.Plaquette d L) :
    holonomy (fun i => assemble U h (Rectangular.linkAt ((t, p.1), planeJoin (.inr p.2)) i)) =
      holonomy (fun i => U t (StrongCouplingCrossing.linkAt p i)) := by
  simp [holonomy, assemble, planeJoin, Rectangular.linkAt, Rectangular.step,
    StrongCouplingCrossing.linkAt]

omit [Fintype E] in
theorem holonomy_temporal {T : ℕ} (U : ZMod (T + 3) → State E d L)
    (h : ZMod (T + 3) → Temporal E d L) (t : ZMod (T + 3))
    (l : StrongCouplingCrossing.Link d L) :
    holonomy (fun i => assemble U h (Rectangular.linkAt ((t, l.1), planeJoin (.inl l.2)) i)) =
      h t l.1 * U (t + 1) l * (h t (l.1 + StrongCouplingCrossing.step l.2))⁻¹ * (U t l)⁻¹ := by
  simp [holonomy, assemble, planeJoin, Rectangular.linkAt, Rectangular.step]

def spatialAction (ψ : E → ℝ) (U : State E d L) : ℝ :=
  ∑ p : StrongCouplingCrossing.Plaquette d L,
    ψ (holonomy (fun i => U (StrongCouplingCrossing.linkAt p i)))

def temporalAction (ψ : E → ℝ) (h : Temporal E d L) (U V : State E d L) : ℝ :=
  ∑ l : StrongCouplingCrossing.Link d L,
    ψ (h l.1 * V l * (h (l.1 + StrongCouplingCrossing.step l.2))⁻¹ * (U l)⁻¹)

/-- Half of each spatial action is assigned to either adjoining time step. -/
def edgeWeight (ψ : E → ℝ) (β : ℝ) (U V : State E d L) (h : Temporal E d L) : ℝ :=
  Real.exp (-β * (spatialAction ψ U / 2 + spatialAction ψ V / 2 + temporalAction ψ h U V))

/-- The transfer matrix after summing temporal link variables. Counting and
uniform reference measures differ by a scalar, which cancels in eigenvalue ratios. -/
def kernel (ψ : E → ℝ) (β : ℝ) : Matrix (State E d L) (State E d L) ℝ :=
  fun U V => ∑ h : Temporal E d L, edgeWeight ψ β U V h

omit [Fintype E] in
/-- Decomposition into spatial plaquettes and plaquettes crossing one time step. -/
theorem action_assemble {T : ℕ} (ψ : E → ℝ)
    (U : ZMod (T + 3) → State E d L) (h : ZMod (T + 3) → Temporal E d L) :
    (∑ p : Rectangular.Plaquette d T L,
      Rectangular.potential (v := (T, L)) (ψ ∘ holonomy) p (assemble U h)) =
      ∑ t, (spatialAction ψ (U t) + temporalAction ψ (h t) (U t) (U (t + 1))) := by
  classical
  simp only [Rectangular.Plaquette, Rectangular.Site, Fintype.sum_prod_type]
  rw [sum_comm]
  simp only [Rectangular.potential, Function.comp_apply]
  -- First group plaquettes by their time coordinate.
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  have hp (x : StrongCouplingCrossing.Site d L) :=
    Equiv.sum_comp (planeEquiv d)
      (fun a => ψ (holonomy (fun i => assemble U h (Rectangular.linkAt ((t, x), a) i))))
  simp only [Fintype.sum_sum_type, planeEquiv, Equiv.ofBijective_apply] at hp
  simp_rw [← hp]
  simp only [sum_add_distrib]
  rw [add_comm]
  simp only [spatialAction, temporalAction, StrongCouplingCrossing.Plaquette,
    StrongCouplingCrossing.Link, Fintype.sum_prod_type]
  congr 1
  · apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro a _
    exact congrArg ψ (holonomy_spatial U h t (x, a))
  · apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro i _
    exact congrArg ψ (holonomy_temporal U h t (x, i))

/-- Periodicity makes the two half spatial actions add to one full action. -/
theorem sum_shift {T : ℕ} (f : ZMod (T + 3) → ℝ) :
    (∑ t, f (t + 1)) = ∑ t, f t := by
  exact Equiv.sum_comp
    (⟨fun t => t + 1, fun t => t - 1, by intro t; simp, by intro t; simp⟩ :
      ZMod (T + 3) ≃ ZMod (T + 3)) f

omit [Fintype E] in
theorem density_assemble {T : ℕ} (ψ : E → ℝ) (β : ℝ)
    (U : ZMod (T + 3) → State E d L) (h : ZMod (T + 3) → Temporal E d L) :
    Rectangular.wilsonDensity (v := (T, L)) (ψ ∘ holonomy) β (assemble U h) =
      ((∏ t, edgeWeight ψ β (U t) (U (t + 1)) (h t) : ℝ) : ℂ) := by
  simp only [Rectangular.wilsonDensity, edgeWeight, ← Complex.ofReal_prod,
    ← Real.exp_sum, ← mul_sum]
  congr 2
  rw [action_assemble]
  simp only [sum_add_distrib, ← sum_div]
  rw [sum_shift (fun t => spatialAction ψ (U t))]
  ring

theorem sum_temporal_weights {T : ℕ} (ψ : E → ℝ) (β : ℝ)
    (U : ZMod (T + 3) → State E d L) :
    (∑ h : ZMod (T + 3) → Temporal E d L,
      ∏ t, edgeWeight ψ β (U t) (U (t + 1)) (h t)) =
      ∏ t, kernel ψ β (U t) (U (t + 1)) := by
  classical
  exact (Fintype.prod_sum (fun t h => edgeWeight ψ β (U t) (U (t + 1)) h)).symm

omit [Fintype E] in
theorem temporalAction_inv (ψ : E → ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (h : Temporal E d L) (U V : State E d L) :
    temporalAction ψ (fun x => (h x)⁻¹) V U = temporalAction ψ h U V := by
  apply sum_congr rfl
  intro l _
  have he : (h l.1)⁻¹ * U l * ((h (l.1 + StrongCouplingCrossing.step l.2))⁻¹)⁻¹ * (V l)⁻¹ =
      (h l.1)⁻¹ *
        (h l.1 * V l * (h (l.1 + StrongCouplingCrossing.step l.2))⁻¹ * (U l)⁻¹)⁻¹ *
        ((h l.1)⁻¹)⁻¹ := by group
  exact (congrArg ψ he).trans ((hclass _ _).trans (hinv _))

omit [Fintype E] in
theorem edgeWeight_inv (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (h : Temporal E d L) (U V : State E d L) :
    edgeWeight ψ β V U (fun x => (h x)⁻¹) = edgeWeight ψ β U V h := by
  rw [edgeWeight, edgeWeight, temporalAction_inv ψ hclass hinv]
  congr 2
  ring

theorem kernel_symmetric (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (U V : State E d L) : kernel ψ β U V = kernel ψ β V U := by
  have he := Equiv.sum_comp (Equiv.inv (Temporal E d L)) (fun h => edgeWeight ψ β V U h)
  change (∑ h : Temporal E d L, edgeWeight ψ β V U (fun x => (h x)⁻¹)) =
    ∑ h : Temporal E d L, edgeWeight ψ β V U h at he
  simpa only [kernel, edgeWeight_inv ψ β hclass hinv] using he

theorem kernel_pos (ψ : E → ℝ) (β : ℝ) (U V : State E d L) : 0 < kernel ψ β U V := by
  apply sum_pos'
  · intro h _
    exact (Real.exp_pos _).le
  · exact ⟨fun _ => 1, mem_univ _, Real.exp_pos _⟩

theorem kernel_isHermitian (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g) :
    (kernel (d := d) (L := L) ψ β).IsHermitian := by
  ext U V
  exact kernel_symmetric ψ β hclass hinv V U

/-- Two time steps give a positive semidefinite transfer operator even when the
one-step operator has negative eigenvalues. -/
def twoStep (ψ : E → ℝ) (β : ℝ) : Matrix (State E d L) (State E d L) ℝ :=
  kernel ψ β * kernel ψ β

theorem twoStep_posSemidef (ψ : E → ℝ) (β : ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g) :
    (twoStep (d := d) (L := L) ψ β).PosSemidef := by
  have hk := kernel_isHermitian (d := d) (L := L) ψ β hclass hinv
  have hh := Matrix.posSemidef_conjTranspose_mul_self (kernel (d := d) (L := L) ψ β)
  rw [hk.eq] at hh
  exact hh

theorem twoStep_pos (ψ : E → ℝ) (β : ℝ) (U V : State E d L) :
    0 < twoStep ψ β U V := by
  apply sum_pos'
  · intro W _
    exact (mul_pos (kernel_pos ψ β U W) (kernel_pos ψ β W V)).le
  · exact ⟨fun _ => 1, mem_univ _, mul_pos (kernel_pos ψ β U _) (kernel_pos ψ β _ V)⟩

section Uniform

variable [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Uniform single-link reference probability. -/
def uniformReference (E : Type*) [MeasurableSpace E] [Fintype E] [Nonempty E] : Measure E :=
  (PMF.uniformOfFintype E).toMeasure

instance : IsProbabilityMeasure (uniformReference E) := by
  unfold uniformReference
  infer_instance

theorem integral_uniform_product {I : Type*} [Fintype I] [DecidableEq I] (f : (I → E) → ℂ) :
    (∫ ω, f ω ∂(Measure.pi fun _ : I => uniformReference E)) =
      (((Fintype.card E : ℝ)⁻¹ ^ Fintype.card I : ℝ) : ℂ) * ∑ ω, f ω := by
  classical
  rw [integral_fintype (.of_finite)]
  simp only [Measure.real, Measure.pi_singleton, uniformReference,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply,
    prod_const, card_univ, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, ← mul_sum]

theorem wilsonExpectation_eq_counting {T : ℕ} (ψ : E → ℝ) (β : ℝ)
    (F : (Rectangular.Link d T L → E) → ℂ) :
    Rectangular.wilsonExpectation (v := (T, L)) (uniformReference E) (ψ ∘ holonomy) β F =
      (∑ ω, F ω * Rectangular.wilsonDensity (v := (T, L)) (ψ ∘ holonomy) β ω) /
        (∑ ω, Rectangular.wilsonDensity (d := d) (v := (T, L)) (ψ ∘ holonomy) β ω) := by
  unfold Rectangular.wilsonExpectation
  rw [integral_uniform_product, integral_uniform_product]
  apply mul_div_mul_left
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero (by exact_mod_cast
    (Fintype.card_ne_zero (α := E)))))

/-- Integrating temporal links gives the cyclic product of transfer kernels. -/
theorem wilsonExpectation_eq_cycle {T : ℕ} (ψ : E → ℝ) (β : ℝ)
    (F : (ZMod (T + 3) → State E d L) → ℂ) :
    Rectangular.wilsonExpectation (v := (T, L)) (uniformReference E) (ψ ∘ holonomy) β
      (fun ω => F (fun t => Rectangular.sliceConfiguration t ω)) =
      (∑ U, F U * ((∏ t, kernel ψ β (U t) (U (t + 1)) : ℝ) : ℂ)) /
        ((∑ U : ZMod (T + 3) → State E d L,
          ∏ t, kernel ψ β (U t) (U (t + 1)) : ℝ) : ℂ) := by
  classical
  rw [wilsonExpectation_eq_counting]
  have hs (G : (ZMod (T + 3) → State E d L) → ℂ) :
      (∑ ω, G (fun t => Rectangular.sliceConfiguration t ω) *
        Rectangular.wilsonDensity (v := (T, L)) (ψ ∘ holonomy) β ω) =
      ∑ U, G U * ((∏ t, kernel ψ β (U t) (U (t + 1)) : ℝ) : ℂ) := by
    rw [← Equiv.sum_comp (configurationEquiv d T L)]
    simp only [Fintype.sum_prod_type, configurationEquiv, Equiv.coe_fn_mk]
    change (∑ U, ∑ h, G U * Rectangular.wilsonDensity (v := (T, L))
      (ψ ∘ holonomy) β (assemble U h)) = _
    simp_rw [density_assemble, ← mul_sum, ← Complex.ofReal_sum, sum_temporal_weights]
  rw [hs]
  have hz := hs (fun _ => 1)
  simp only [one_mul, ← Complex.ofReal_sum] at hz
  rw [hz]

end Uniform

end WilsonFinite

namespace CyclicMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A chain whose last endpoint is supplied separately. -/
def segment (K : Matrix ι ι ℝ) {n : ℕ} (u : Fin n → ι) (y : ι) : ℝ :=
  ∏ i : Fin n, K (u i) (Fin.snoc (α := fun _ => ι) u y i.succ)

omit [Fintype ι] [DecidableEq ι] in
theorem segment_cons (K : Matrix ι ι ℝ) {n : ℕ} (x : ι) (u : Fin n → ι) (y : ι) :
    segment K (Fin.cons x u) y = K x (Fin.snoc (α := fun _ => ι) u y 0) * segment K u y := by
  unfold segment
  rw [Fin.prod_univ_succ]
  simp only [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

theorem sum_segment (K : Matrix ι ι ℝ) (n : ℕ) (x y : ι) :
    (∑ u : Fin n → ι, segment K (Fin.cons x u) y) = (K ^ (n + 1)) x y := by
  induction n generalizing x with
  | zero =>
    simp only [Fintype.sum_unique, Nat.zero_add, pow_one]
    unfold segment
    rw [Fin.prod_univ_one]
    rfl
  | succ n ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι)),
      Fintype.sum_prod_type]
    change (∑ z : ι, ∑ u : Fin n → ι, segment K (Fin.cons x (Fin.cons z u)) y) = _
    simp only [segment_cons, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero]
    simp_rw [← mul_sum]
    have hi (z : ι) : (∑ u : Fin n → ι,
        K z (Fin.snoc (α := fun _ => ι) u y 0) * segment K u y) = (K ^ (n + 1)) z y := by
      simpa only [segment_cons] using ih z
    simp_rw [hi]
    conv_rhs => rw [pow_succ', Matrix.mul_apply]

/-- Cutting the cycle at two specified slices leaves two independent chains. -/
theorem sum_two_segments (K : Matrix ι ι ℝ) (n : ℕ) (F : ι → ι → ℝ) :
    (∑ u : Fin (n + 1) → ι, ∑ v : Fin (n + 1) → ι,
      F (u 0) (v 0) * segment K u (v 0) * segment K v (u 0)) =
      ∑ x, ∑ y, F x y * (K ^ (n + 1)) x y * (K ^ (n + 1)) y x := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι)),
    Fintype.sum_prod_type]
  change (∑ x : ι, ∑ u : Fin n → ι, ∑ v : Fin (n + 1) → ι,
    F x (v 0) * segment K (Fin.cons x u) (v 0) * segment K v x) = _
  apply sum_congr rfl
  intro x _
  simp_rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ι)),
    Fintype.sum_prod_type]
  change (∑ u : Fin n → ι, ∑ y : ι, ∑ v : Fin n → ι,
    F x y * segment K (Fin.cons x u) y * segment K (Fin.cons y v) x) = _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp_rw [← mul_sum, sum_segment, ← sum_mul, ← mul_sum, sum_segment]

/-- Residues represented by the integers in the standard period. -/
def residueEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i.val : ZMod N)
  invFun t := ⟨t.val, ZMod.val_lt t⟩
  left_inv i := Fin.ext (ZMod.val_natCast_of_lt i.isLt)
  right_inv t := ZMod.natCast_zmod_val t

/-- Cutting the time coordinates into two consecutive intervals. -/
def cutEquiv (n : ℕ) : (ZMod ((n + 1) + (n + 1)) → ι) ≃
    (Fin (n + 1) → ι) × (Fin (n + 1) → ι) :=
  (Equiv.arrowCongr (residueEquiv ((n + 1) + (n + 1))).symm (Equiv.refl ι)).trans
    (Fin.appendEquiv (n + 1) (n + 1)).symm

omit [Fintype ι] [DecidableEq ι] in
theorem segment_sample (K : Matrix ι ι ℝ) {N n : ℕ} (U : ZMod N → ι) (a : ℕ) :
    segment K (fun i : Fin n => U ((a + i.val : ℕ) : ZMod N)) (U ((a + n : ℕ) : ZMod N)) =
      ∏ i : Fin n, K (U ((a + i.val : ℕ) : ZMod N))
        (U ((a + i.val + 1 : ℕ) : ZMod N)) := by
  unfold segment
  apply prod_congr rfl
  intro i _
  congr 1
  by_cases h : i.val + 1 < n
  · have he : i.succ = (⟨i.val + 1, h⟩ : Fin n).castSucc := rfl
    rw [he, Fin.snoc_castSucc]
    simp only [Nat.add_assoc]
  · have hv : i.val + 1 = n := by omega
    have he : i.succ = Fin.last n := Fin.ext hv
    rw [he, Fin.snoc_last]
    congr 2
    omega

omit [Fintype ι] [DecidableEq ι] in
theorem cycle_split (K : Matrix ι ι ℝ) (n : ℕ)
    (U : ZMod ((n + 1) + (n + 1)) → ι) :
    (∏ t, K (U t) (U (t + 1))) =
      segment K (fun i : Fin (n + 1) => U (i.val : ZMod _)) (U (n + 1)) *
      segment K (fun i : Fin (n + 1) => U ((n + 1 + i.val : ℕ) : ZMod _)) (U 0) := by
  rw [← Equiv.prod_comp (residueEquiv ((n + 1) + (n + 1))), Fin.prod_univ_add]
  have h₁ := segment_sample K (n := n + 1) U 0
  have h₂ := segment_sample K (n := n + 1) U (n + 1)
  simp only [Nat.zero_add] at h₁
  simp only [ZMod.natCast_self] at h₂
  simp only [Nat.cast_add, Nat.cast_one] at h₁ h₂
  simp only [residueEquiv, Equiv.coe_fn_mk, Fin.val_castAdd, Fin.val_natAdd,
    Nat.cast_add, Nat.cast_one]
  rw [h₁, h₂]

theorem sum_cycle (K : Matrix ι ι ℝ) (n : ℕ) (F : ι → ι → ℝ) :
    (∑ U : ZMod ((n + 1) + (n + 1)) → ι,
      F (U 0) (U (n + 1)) * ∏ t, K (U t) (U (t + 1))) =
      ∑ x, ∑ y, F x y * (K ^ (n + 1)) x y * (K ^ (n + 1)) y x := by
  have hh (U : ZMod ((n + 1) + (n + 1)) → ι) :
      F (U 0) (U (n + 1)) * (∏ t, K (U t) (U (t + 1))) =
      (fun uv : (Fin (n + 1) → ι) × (Fin (n + 1) → ι) =>
        F (uv.1 0) (uv.2 0) * segment K uv.1 (uv.2 0) * segment K uv.2 (uv.1 0))
          (cutEquiv n U) := by
    rw [cycle_split]
    simp only [cutEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply,
      Fin.appendEquiv_symm_apply, residueEquiv, Equiv.symm_symm,
      Function.comp_apply, Equiv.refl_apply, Equiv.coe_fn_mk, Fin.val_zero, add_zero, Nat.cast_zero,
      Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add, Nat.cast_one]
    exact (mul_assoc (F (U 0) (U (n + 1))) _ _).symm
  simp_rw [hh]
  rw [Equiv.sum_comp (cutEquiv n)
    (fun uv => F (uv.1 0) (uv.2 0) * segment K uv.1 (uv.2 0) * segment K uv.2 (uv.1 0)),
    Fintype.sum_prod_type]
  exact sum_two_segments K n F

theorem sum_cycle_length (K : Matrix ι ι ℝ) {N : ℕ} [NeZero N] (n : ℕ)
    (hN : N = (n + 1) + (n + 1)) (F : ι → ι → ℝ) :
    (∑ U : ZMod N → ι, F (U 0) (U (n + 1)) * ∏ t, K (U t) (U (t + 1))) =
      ∑ x, ∑ y, F x y * (K ^ (n + 1)) x y * (K ^ (n + 1)) y x := by
  subst N
  exact sum_cycle K n F

theorem sum_cycle_partition (K : Matrix ι ι ℝ) {N : ℕ} [NeZero N] (n : ℕ)
    (hN : N = (n + 1) + (n + 1)) :
    (∑ U : ZMod N → ι, ∏ t, K (U t) (U (t + 1))) = Matrix.trace (K ^ N) := by
  have he := sum_cycle_length K n hN (fun _ _ => 1)
  simp only [one_mul] at he
  rw [he]
  conv_rhs => rw [hN, pow_add]
  rfl

theorem sum_cycle_both (K : Matrix ι ι ℝ) {N : ℕ} [NeZero N] (n : ℕ)
    (hN : N = (n + 1) + (n + 1)) (x : ι) :
    (∑ U : ZMod N → ι, (if U 0 = x then (1 : ℝ) else 0) *
      (if U (n + 1) = x then (1 : ℝ) else 0) * ∏ t, K (U t) (U (t + 1))) =
      (K ^ (n + 1)) x x ^ 2 := by
  rw [sum_cycle_length K n hN
    (fun a b => (if a = x then 1 else 0) * (if b = x then 1 else 0))]
  simp [ite_mul, mul_ite, sq]

theorem sum_cycle_left (K : Matrix ι ι ℝ) {N : ℕ} [NeZero N] (n : ℕ)
    (hN : N = (n + 1) + (n + 1)) (x : ι) :
    (∑ U : ZMod N → ι, (if U 0 = x then (1 : ℝ) else 0) *
      ∏ t, K (U t) (U (t + 1))) = (K ^ N) x x := by
  rw [sum_cycle_length K n hN (fun a _ => if a = x then 1 else 0)]
  conv_rhs => rw [hN, pow_add, Matrix.mul_apply]
  simp [ite_mul, sum_ite_irrel]

theorem sum_cycle_right (K : Matrix ι ι ℝ) {N : ℕ} [NeZero N] (n : ℕ)
    (hN : N = (n + 1) + (n + 1)) (x : ι) :
    (∑ U : ZMod N → ι, (if U (n + 1) = x then (1 : ℝ) else 0) *
      ∏ t, K (U t) (U (t + 1))) = (K ^ N) x x := by
  rw [sum_cycle_length K n hN (fun _ a => if a = x then 1 else 0)]
  conv_rhs => rw [hN, pow_add, Matrix.mul_apply]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
  apply sum_congr rfl
  intro y _
  exact mul_comm _ _

end CyclicMatrix

namespace Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Diagonal slice correlations control the normalized trace. -/
theorem sum_le_of_diagonal_correlation (a p : ι → ℝ)
    (_ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hc : ∀ i, |a i ^ 2 - p i ^ 2| ≤ δ ^ 2) :
    (∑ i, a i) ≤ 1 + Fintype.card ι * δ := by
  have he (i : ι) : a i ≤ p i + δ := by
    have := (abs_le.mp (hc i)).2
    nlinarith [hp i, mul_nonneg (hp i) hδ]
  calc
    _ ≤ ∑ i, (p i + δ) := sum_le_sum fun i _ => he i
    _ = _ := by simp [sum_add_distrib, hs]

omit [DecidableEq ι] in
theorem trace_excess_le_of_diagonal_correlation (a p : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {q C : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (n : ℕ)
    (hc : ∀ i, |a i ^ 2 - p i ^ 2| ≤ C * q ^ (2 * n)) :
    (∑ i, a i) ^ 2 - 1 ≤
      (2 * Fintype.card ι * Real.sqrt C + (Fintype.card ι : ℝ) ^ 2 * C) * q ^ n := by
  have he : (Real.sqrt C * q ^ n) ^ 2 = C * q ^ (2 * n) := by
    rw [mul_pow, Real.sq_sqrt hC, ← pow_mul]
    congr 2
    omega
  have hb := sum_le_of_diagonal_correlation a p ha hp hs
    (mul_nonneg (Real.sqrt_nonneg C) (pow_nonneg hq n)) (fun i => by simpa [he] using hc i)
  have hsum := sum_nonneg (fun i (_ : i ∈ (univ : Finset ι)) => ha i)
  have hpow := pow_le_one₀ hq hq1 (n := n)
  have hn := pow_nonneg hq n
  have hsqrt := Real.sq_sqrt hC
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hs : (∑ i, a i) ^ 2 ≤ (1 + Fintype.card ι * (Real.sqrt C * q ^ n)) ^ 2 :=
    pow_le_pow_left₀ hsum hb 2
  have hsmall : (q ^ n) ^ 2 ≤ q ^ n := by nlinarith
  have hcsmall := mul_le_mul_of_nonneg_left hsmall
    (mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) hC)
  have hexpand : (1 + Fintype.card ι * (Real.sqrt C * q ^ n)) ^ 2 =
      1 + 2 * Fintype.card ι * Real.sqrt C * q ^ n +
        (Fintype.card ι : ℝ) ^ 2 * C * (q ^ n) ^ 2 := by
    rw [add_sq, mul_pow, mul_pow, Real.sq_sqrt hC]
    ring
  rw [hexpand] at hs
  nlinarith only [hs, hcsmall]

/-- Spectral moments of a real symmetric matrix. -/
theorem trace_pow_eq_sum (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (n : ℕ) :
    Matrix.trace (A ^ n) = ∑ i, hA.eigenvalues i ^ n := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  simp [Matrix.diagonal_pow]

/-- Two distinct nonnegative summands contribute their cross term to the square
of a sum, over and above the sum of the squares. -/
theorem cross_term_le (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) {i j : ι} (hij : i ≠ j) :
    (∑ k, v k ^ 2) + 2 * v i * v j ≤ (∑ k, v k) ^ 2 := by
  let row := fun k => ∑ l : ι, if k = l then 0 else v k * v l
  have hterm (k l : ι) : 0 ≤ (if k = l then 0 else v k * v l) := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hv k) (hv l)
  have hr (k : ι) : 0 ≤ row k := sum_nonneg fun l _ => hterm k l
  have hi : v i * v j ≤ row i := by
    simpa only [row, hij, ↓reduceIte] using
      (single_le_sum (f := fun l => if i = l then 0 else v i * v l)
        (fun l _ => hterm i l) (mem_univ j))
  have hj : v j * v i ≤ row j := by
    simpa only [row, Ne.symm hij, ↓reduceIte] using
      (single_le_sum (f := fun l => if j = l then 0 else v j * v l)
        (fun l _ => hterm j l) (mem_univ i))
  have hp : row i + row j ≤ ∑ k, row k := by
    have h := sum_le_sum_of_subset_of_nonneg (f := row)
      (show ({i, j} : Finset ι) ⊆ univ from subset_univ _)
      (fun k _ _ => hr k)
    simpa only [sum_pair hij] using h
  have he : (∑ k, v k) ^ 2 = (∑ k, v k ^ 2) + ∑ k, row k := by
    rw [pow_two, sum_mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    calc
      _ = ∑ l : ι, ((if k = l then v k ^ 2 else 0) +
          (if k = l then 0 else v k * v l)) := by
        apply sum_congr rfl
        intro l _
        by_cases h : k = l <;> simp [h, pow_two]
      _ = (∑ l : ι, if k = l then v k ^ 2 else 0) + row k := by
        rw [sum_add_distrib]
      _ = _ := by simp
  nlinarith

theorem le_of_power_bound {a b C : ℝ} (hb : 0 < b)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * b ^ n) : a ≤ b := by
  by_contra hab
  have hab : b < a := lt_of_not_ge hab
  have hr : 1 < a / b := (one_lt_div hb).mpr hab
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (max C 1) hr
  have hn0 : 0 < n := by
    by_contra hn0
    have : n = 0 := by omega
    simp only [this, pow_zero] at hn
    exact (not_lt_of_ge (le_max_right C 1)) hn
  have hp : (a / b) ^ n ≤ C := by
    rw [div_pow, div_le_iff₀ (pow_pos hb n)]
    exact h n hn0
  exact (not_lt_of_ge (hp.trans (le_max_left C 1))) hn

/-- Exponential decay of the normalized trace excess forces a gap in a finite
nonnegative spectrum. The prefactor may depend on the size of the spectrum. -/
theorem eigenvalue_le_of_trace_excess (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (i₀ : ι) (h₀ : 0 < a i₀) (hmax : ∀ i, a i ≤ a i₀)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (htrace : ∀ n : ℕ, 0 < n →
      (∑ i, a i ^ n) ^ 2 - (∑ i, a i ^ (2 * n)) ≤
        C * q ^ n * (∑ i, a i ^ (2 * n))) :
    ∀ j, j ≠ i₀ → a j ≤ q * a i₀ := by
  intro j hj
  apply le_of_power_bound (mul_pos hq h₀)
    (C := C * Fintype.card ι / 2)
  intro n hn
  have hc := cross_term_le (fun i => a i ^ n) (fun i => pow_nonneg (ha i) n) (Ne.symm hj)
  have hz : (∑ i, a i ^ (2 * n)) ≤ Fintype.card ι * (a i₀) ^ (2 * n) := by
    calc
      _ ≤ ∑ _ : ι, (a i₀) ^ (2 * n) := sum_le_sum fun i _ => pow_le_pow_left₀ (ha i) (hmax i) _
      _ = _ := by simp
  have ht := (htrace n hn).trans (mul_le_mul_of_nonneg_left hz (by positivity))
  have hp : 0 < a i₀ ^ n := pow_pos h₀ n
  have he (i : ι) : (a i ^ n) ^ 2 = a i ^ (2 * n) := by rw [← pow_mul]; congr 1; omega
  simp only [he] at hc
  rw [mul_pow]
  apply (mul_le_mul_iff_left₀ hp).mp
  have hpow : a i₀ ^ (2 * n) = (a i₀ ^ n) ^ 2 := (he i₀).symm
  rw [hpow] at ht
  nlinarith

/-- Positive entries remain positive after any positive number of time steps. -/
theorem pow_entry_pos (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 < A i j)
    {n : ℕ} (hn : 0 < n) (i j : ι) : 0 < (A ^ n) i j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction n with
  | zero => simpa using hA i j
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply sum_pos'
    · intro k _
      exact mul_nonneg (Matrix.pow_apply_nonneg (fun i j => (hA i j).le) _ _ _) (hA k j).le
    · exact ⟨j, mem_univ _, mul_pos ih (hA j j)⟩

theorem trace_pow_pos [Nonempty ι] (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 < A i j)
    {n : ℕ} (hn : 0 < n) : 0 < Matrix.trace (A ^ n) :=
  sum_pos (fun i _ => pow_entry_pos A hA hn i i) univ_nonempty

/-- Equal-state slice covariances control the excess of the squared trace. -/
theorem matrix_trace_excess (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (n : ℕ) {q C : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hZ : 0 < Matrix.trace (A ^ (2 * n)))
    (hc : ∀ i, |(A ^ n) i i ^ 2 / Matrix.trace (A ^ (2 * n)) -
      ((A ^ (2 * n)) i i / Matrix.trace (A ^ (2 * n))) ^ 2| ≤ C * q ^ (2 * n)) :
    Matrix.trace (A ^ n) ^ 2 - Matrix.trace (A ^ (2 * n)) ≤
      (2 * Fintype.card ι * Real.sqrt C + (Fintype.card ι : ℝ) ^ 2 * C) *
        q ^ n * Matrix.trace (A ^ (2 * n)) := by
  let Z := Matrix.trace (A ^ (2 * n))
  let a (i : ι) := (A ^ n) i i / Real.sqrt Z
  let p (i : ι) := (A ^ (2 * n)) i i / Z
  have hZn : 0 < Z := hZ
  have ha : ∀ i, 0 ≤ a i := fun i => div_nonneg (Matrix.pow_apply_nonneg hA _ _ _) (Real.sqrt_nonneg _)
  have hp : ∀ i, 0 ≤ p i := fun i => div_nonneg (Matrix.pow_apply_nonneg hA _ _ _) hZn.le
  have hs : ∑ i, p i = 1 := by
    dsimp [p]
    rw [← sum_div]
    exact div_self hZn.ne'
  have hcorr : ∀ i, |a i ^ 2 - p i ^ 2| ≤ C * q ^ (2 * n) := by
    intro i
    simpa only [a, p, div_pow, Real.sq_sqrt hZn.le] using hc i
  have ht := trace_excess_le_of_diagonal_correlation a p ha hp hs hq hq1 hC n hcorr
  have hs' : ∑ i, a i = Matrix.trace (A ^ n) / Real.sqrt Z := by
    simp only [a, ← sum_div, Matrix.trace, Matrix.diag_apply]
  rw [hs', div_pow, Real.sq_sqrt hZn.le] at ht
  have ht' : Matrix.trace (A ^ n) ^ 2 / Z ≤
      (2 * Fintype.card ι * Real.sqrt C + (Fintype.card ι : ℝ) ^ 2 * C) * q ^ n + 1 := by
    linarith
  have hmul := (div_le_iff₀ hZn).mp ht'
  dsimp [Z] at hmul
  nlinarith only [hmul]

/-- A finite-dimensional spectral gap obtained solely from diagonal correlations.
The correlation prefactor is unrestricted and may grow with the state space. -/
theorem gap_of_diagonal_correlations [Nonempty ι] (A : Matrix ι ι ℝ)
    (hA : A.PosSemidef) (hpos : ∀ i j, 0 < A i j) {q C : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, 0 < n → ∀ i,
      |(A ^ n) i i ^ 2 / Matrix.trace (A ^ (2 * n)) -
        ((A ^ (2 * n)) i i / Matrix.trace (A ^ (2 * n))) ^ 2| ≤ C * q ^ (2 * n)) :
    ∃ i₀ : ι, 0 < hA.isHermitian.eigenvalues i₀ ∧
      (∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues i₀) ∧
      ∀ j, j ≠ i₀ → hA.isHermitian.eigenvalues j ≤ q * hA.isHermitian.eigenvalues i₀ := by
  obtain ⟨i₀, _, hmax⟩ := exists_max_image univ hA.isHermitian.eigenvalues univ_nonempty
  have hm : ∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues i₀ :=
    fun i => hmax i (mem_univ _)
  have h₀ : 0 < hA.isHermitian.eigenvalues i₀ := by
    by_contra hh
    have hz : ∑ i, hA.isHermitian.eigenvalues i = 0 :=
      sum_eq_zero fun i _ => le_antisymm ((hm i).trans (le_of_not_gt hh)) (hA.eigenvalues_nonneg i)
    have ht := trace_pow_pos A hpos (show 0 < 1 by omega)
    rw [trace_pow_eq_sum A hA.isHermitian 1] at ht
    simp only [pow_one, hz] at ht
    exact (lt_irrefl 0) ht
  refine ⟨i₀, h₀, hm, eigenvalue_le_of_trace_excess hA.isHermitian.eigenvalues
    (C := 2 * Fintype.card ι * Real.sqrt C + (Fintype.card ι : ℝ) ^ 2 * C)
    hA.eigenvalues_nonneg i₀ h₀ hm hq (by positivity) ?_⟩
  intro n hn
  have ht := matrix_trace_excess A (fun i j => (hpos i j).le) n hq.le hq1.le hC
    (trace_pow_pos A hpos (by omega)) (hc n hn)
  simpa only [trace_pow_eq_sum A hA.isHermitian] using ht

/-- A unique dominant real eigenvalue is positive if all odd power traces are
positive. This avoids any sign assumption on the remaining spectrum. -/
theorem dominant_pos_of_odd_traces (a : ι → ℝ) (i₀ : ι) (ha : 0 < |a i₀|)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ j, j ≠ i₀ → |a j| ≤ r * |a i₀|)
    (ht : ∀ n : ℕ, 0 < ∑ i, a i ^ (2 * n + 1)) : 0 < a i₀ := by
  by_contra hneg
  have hn : a i₀ ≤ 0 := le_of_not_gt hneg
  obtain ⟨n, hsmall⟩ := exists_pow_lt_of_lt_one
    (show 0 < 1 / ((Fintype.card ι : ℝ) + 1) by positivity) hr1
  have hpow := (pow_le_pow_of_le_one hr0 hr1.le (show n ≤ 2 * n + 1 by omega)).trans_lt hsmall
  have hN : (Fintype.card ι : ℝ) * r ^ (2 * n + 1) < 1 := by
    have hp := (lt_div_iff₀ (show 0 < (Fintype.card ι : ℝ) + 1 by positivity)).mp hpow
    have hp0 := pow_nonneg hr0 (2 * n + 1)
    nlinarith
  have hb : (∑ i ∈ (univ : Finset ι).erase i₀, a i ^ (2 * n + 1)) ≤
      Fintype.card ι * (r * |a i₀|) ^ (2 * n + 1) := by
    calc
      _ ≤ ∑ i ∈ (univ : Finset ι).erase i₀, (r * |a i₀|) ^ (2 * n + 1) := by
        apply sum_le_sum
        intro j hj
        exact (le_abs_self _).trans ((abs_pow _ _).le.trans
          (pow_le_pow_left₀ (abs_nonneg _) (hg j (mem_erase.mp hj).1) _))
      _ ≤ ∑ _ : ι, (r * |a i₀|) ^ (2 * n + 1) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (by intro i _ _; positivity)
      _ = _ := by simp
  have he : a i₀ ^ (2 * n + 1) = -|a i₀| ^ (2 * n + 1) := by
    rw [abs_of_nonpos hn, (odd_two_mul_add_one n).neg_pow, neg_neg]
  have hs := ht n
  rw [← sum_erase_add _ _ (mem_univ i₀), he] at hs
  rw [mul_pow] at hb
  have hm := mul_lt_mul_of_pos_right hN (pow_pos ha (2 * n + 1))
  nlinarith

/-- Diagonal correlations for the squared transfer matrix yield an absolute
one-step gap around its positive leading eigenvalue. -/
theorem absolute_gap_of_squared_correlations [Nonempty ι] (K : Matrix ι ι ℝ)
    (hK : K.IsHermitian) (hpos : ∀ i j, 0 < K i j) {r C : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, 0 < n → ∀ i,
      |(K ^ (2 * n)) i i ^ 2 / Matrix.trace (K ^ (2 * (2 * n))) -
        ((K ^ (2 * (2 * n))) i i / Matrix.trace (K ^ (2 * (2 * n)))) ^ 2| ≤
          C * (r ^ 2) ^ (2 * n)) :
    ∃ i₀ : ι, 0 < hK.eigenvalues i₀ ∧
      (∀ i, |hK.eigenvalues i| ≤ hK.eigenvalues i₀) ∧
      ∀ j, j ≠ i₀ → |hK.eigenvalues j| ≤ r * hK.eigenvalues i₀ := by
  let a := hK.eigenvalues
  have ha (n : ℕ) : Matrix.trace (K ^ (2 * n)) = ∑ i, (a i ^ 2) ^ n := by
    rw [trace_pow_eq_sum K hK]
    simp only [← pow_mul, a]
  have hsq : ∀ i j, 0 < (K ^ 2) i j := pow_entry_pos K hpos (by omega)
  have ht (n : ℕ) (hn : 0 < n) :
      (∑ i, (a i ^ 2) ^ n) ^ 2 - ∑ i, (a i ^ 2) ^ (2 * n) ≤
        (2 * Fintype.card ι * Real.sqrt C + (Fintype.card ι : ℝ) ^ 2 * C) *
          (r ^ 2) ^ n * ∑ i, (a i ^ 2) ^ (2 * n) := by
    have he := matrix_trace_excess (K ^ 2) (fun i j => (hsq i j).le) n
      (sq_nonneg r) (by nlinarith) hC
      (trace_pow_pos (K ^ 2) hsq (by omega)) (by simpa only [← pow_mul] using hc n hn)
    simpa only [← pow_mul, ha] using he
  obtain ⟨i₀, _, hm⟩ := exists_max_image univ (fun i => a i ^ 2) univ_nonempty
  have hmax : ∀ i, a i ^ 2 ≤ a i₀ ^ 2 := fun i => hm i (mem_univ _)
  have h₀ : 0 < a i₀ ^ 2 := by
    by_contra hh
    have hz : ∑ i, a i ^ 2 = 0 := sum_eq_zero fun i _ =>
      le_antisymm ((hmax i).trans (le_of_not_gt hh)) (sq_nonneg _)
    have hp := trace_pow_pos K hpos (show 0 < 2 * 1 by omega)
    rw [ha 1] at hp
    simp only [pow_one, hz] at hp
    exact (lt_irrefl 0) hp
  have hg := eigenvalue_le_of_trace_excess (fun i => a i ^ 2) (fun i => sq_nonneg _)
    i₀ h₀ hmax (pow_pos hr 2) (by positivity) ht
  have habs : 0 < |a i₀| := abs_pos.mpr (by intro hz; simp [hz] at h₀)
  have hg' (j : ι) (hj : j ≠ i₀) : |a j| ≤ r * |a i₀| := by
    have hj' := hg j hj
    have hn : 0 ≤ r * |a i₀| := mul_nonneg hr.le (abs_nonneg _)
    nlinarith [sq_abs (a j), sq_abs (a i₀)]
  have hlead : 0 < a i₀ := dominant_pos_of_odd_traces a i₀ habs hr.le hr1 hg' (by
    intro n
    simpa only [a, trace_pow_eq_sum K hK] using trace_pow_pos K hpos (show 0 < 2 * n + 1 by omega))
  refine ⟨i₀, hlead, ?_, ?_⟩
  · intro i
    have hi := hmax i
    nlinarith [sq_abs (a i), abs_nonneg (a i)]
  · simpa only [abs_of_pos hlead] using hg'

end Spectral

namespace WilsonFinite

variable {E : Type*} [Group E] [Fintype E] [DecidableEq E] {d L : ℕ}

/-- Matrix powers count twice as many elementary time steps. -/
theorem twoStep_pow (ψ : E → ℝ) (β : ℝ) (n : ℕ) :
    (twoStep (d := d) (L := L) ψ β) ^ n = (kernel ψ β) ^ (2 * n) := by
  rw [twoStep, ← sq, ← pow_mul]

section Correlations

variable [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Two-slice Wilson expectations are finite-dimensional transfer traces. -/
theorem expectation_pair_eq {T : ℕ} (ψ : E → ℝ) (β : ℝ) (n : ℕ)
    (hT : T + 3 = (n + 1) + (n + 1)) (F : State E d L → State E d L → ℝ) :
    Rectangular.wilsonExpectation (v := (T, L)) (uniformReference E)
      (ψ ∘ StrongCouplingTwist.holonomy) β
      (fun ω => ((F (Rectangular.sliceConfiguration 0 ω)
        (Rectangular.sliceConfiguration (n + 1 : ZMod (T + 3)) ω) : ℝ) : ℂ)) =
      (((∑ x, ∑ y, F x y * (kernel ψ β ^ (n + 1)) x y *
        (kernel ψ β ^ (n + 1)) y x) / Matrix.trace (kernel (d := d) (L := L) ψ β ^ (T + 3)) : ℝ) : ℂ) := by
  rw [wilsonExpectation_eq_cycle ψ β
    (fun U => ((F (U 0) (U (n + 1)) : ℝ) : ℂ))]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_div]
  rw [CyclicMatrix.sum_cycle_length (kernel ψ β) n hT F,
    CyclicMatrix.sum_cycle_partition (kernel ψ β) n hT]

/-- State indicators are bounded observables of a single spatial slice. -/
def stateIndicator (x U : State E d L) : ℝ := if U = x then 1 else 0

omit [Group E] [Fintype E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem norm_stateIndicator (x U : State E d L) : ‖(stateIndicator x U : ℂ)‖ ≤ 1 := by
  unfold stateIndicator
  split <;> norm_num

/-- The exponential rate is independent of the spatial extent. The prefactor
may depend on that extent and disappears in the spectral limit. -/
theorem diagonal_correlations (d : ℕ) (ψ : E → ℝ)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ Rectangular.beta0 d) :
    ∃ κ > 0, ∀ L n : ℕ, 0 < n → ∀ x : State E d L,
      |(twoStep ψ β ^ n) x x ^ 2 / Matrix.trace (twoStep (d := d) (L := L) ψ β ^ (2 * n)) -
        ((twoStep ψ β ^ (2 * n)) x x / Matrix.trace (twoStep (d := d) (L := L) ψ β ^ (2 * n))) ^ 2| ≤
        (3 * Real.exp (6 * ((L + 3) ^ d * (d + 1) : ℕ))) * (Real.exp (-κ)) ^ (2 * n) := by
  obtain ⟨κ, hκ, hc⟩ := Rectangular.slice_clustering d (uniformReference E) (1 : E)
    (φ := ψ ∘ StrongCouplingTwist.holonomy) (measurable_of_countable _)
    (fun v => hψ0 _) (fun v => hψ2 _) hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro L n hn x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let T := 4 * k + 1
  let m := 2 * k + 1
  have hT : T + 3 = (m + 1) + (m + 1) := by dsimp [T, m]; omega
  let f : State E d L → ℂ := fun U => (stateIndicator x U : ℂ)
  have hb := hc T L (m + 1) (by omega) f f 1 1
    (measurable_of_countable _) (measurable_of_countable _)
    (norm_stateIndicator x) (norm_stateIndicator x)
  have hbcast :
      (fun ω : Rectangular.Link d T L → E =>
        f (Rectangular.sliceConfiguration 0 ω) *
          f (Rectangular.sliceConfiguration ((m + 1 : ℕ) : ZMod (T + 3)) ω)) =
      (fun ω => ((stateIndicator x (Rectangular.sliceConfiguration 0 ω) *
        stateIndicator x (Rectangular.sliceConfiguration (m + 1 : ZMod (T + 3)) ω) : ℝ) : ℂ)) := by
    funext ω
    simp [f]
  rw [hbcast, expectation_pair_eq ψ β m hT
    (fun U V => stateIndicator x U * stateIndicator x V)] at hb
  have hl := expectation_pair_eq ψ β m hT (fun U _ => stateIndicator x U)
  have hr := expectation_pair_eq ψ β m hT (fun _ V => stateIndicator x V)
  dsimp only [f] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rw [hl, hr] at hb
  have hd : (∑ U, ∑ V, stateIndicator x U * stateIndicator x V *
      (kernel ψ β ^ (m + 1)) U V * (kernel ψ β ^ (m + 1)) V U) =
        (kernel ψ β ^ (m + 1)) x x ^ 2 := by
    simp [stateIndicator, ite_mul, mul_ite, sq]
  have hleft : (∑ U, ∑ V, stateIndicator x U *
      (kernel ψ β ^ (m + 1)) U V * (kernel ψ β ^ (m + 1)) V U) =
        (kernel ψ β ^ (T + 3)) x x := by
    conv_rhs => rw [hT, pow_add, Matrix.mul_apply]
    simp [stateIndicator, ite_mul, sum_ite_irrel]
  have hright : (∑ U, ∑ V, stateIndicator x V *
      (kernel ψ β ^ (m + 1)) U V * (kernel ψ β ^ (m + 1)) V U) =
        (kernel ψ β ^ (T + 3)) x x := by
    conv_rhs => rw [hT, pow_add, Matrix.mul_apply]
    simp only [stateIndicator, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    apply sum_congr rfl
    intro U _
    exact mul_comm _ _
  rw [hd, hleft, hright] at hb
  simp only [← sq, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, mul_one] at hb
  have hm : m + 1 = 2 * (k + 1) := by dsimp [m]; omega
  have ht : T + 3 = 2 * (2 * (k + 1)) := by dsimp [T]; omega
  rw [hm, ht] at hb
  simp only [twoStep_pow]
  convert hb using 1
  rw [← Real.exp_nat_mul]
  congr 2
  dsimp [m]
  push_cast
  ring

end Correlations

/-- The two-step Wilson transfer matrix has a unique largest eigenvalue and a
uniform bound on every other normalized eigenvalue, on the full spatial state
space. Its time step is two lattice units. No positivity assumption on the
one-step spectrum is needed. -/
theorem uniform_twoStep_gap (d : ℕ) (ψ : E → ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ Rectangular.beta0 d) :
    ∃ κ > 0, ∀ L : ℕ,
      let hA := twoStep_posSemidef (d := d) (L := L) ψ β hclass hinv
      ∃ i₀ : State E d L, 0 < hA.isHermitian.eigenvalues i₀ ∧
        (∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues i₀) ∧
        ∀ j, j ≠ i₀ →
          0 ≤ hA.isHermitian.eigenvalues j / hA.isHermitian.eigenvalues i₀ ∧
          hA.isHermitian.eigenvalues j / hA.isHermitian.eigenvalues i₀ ≤ Real.exp (-κ) := by
  let : MeasurableSpace E := ⊤
  obtain ⟨κ, hκ, hc⟩ := diagonal_correlations d ψ hψ0 hψ2 hβ hβ0
  refine ⟨κ, hκ, ?_⟩
  intro L
  let hA := twoStep_posSemidef (d := d) (L := L) ψ β hclass hinv
  have hq : Real.exp (-κ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨i₀, h₀, hm, hg⟩ := Spectral.gap_of_diagonal_correlations
    (twoStep (d := d) (L := L) ψ β) hA (twoStep_pos ψ β)
    (Real.exp_pos _) hq (show 0 ≤ 3 * Real.exp (6 * ((L + 3) ^ d * (d + 1) : ℕ)) by positivity)
    (hc L)
  refine ⟨i₀, h₀, hm, ?_⟩
  intro j hj
  exact ⟨div_nonneg (hA.eigenvalues_nonneg j) h₀.le, (div_le_iff₀ h₀).mpr (hg j hj)⟩

/-- Uniform strong-coupling gap for the one-step transfer matrix. The leading
Perron eigenvalue is positive and simple. Every other eigenvalue, including any
negative ones, has normalized absolute value at most `exp (-mass)`, where
`mass > 0` is independent of the spatial volume. -/
theorem uniform_transfer_gap (d : ℕ) (ψ : E → ℝ)
    (hclass : ∀ g h, ψ (g * h * g⁻¹) = ψ h) (hinv : ∀ g, ψ g⁻¹ = ψ g)
    (hψ0 : ∀ g, 0 ≤ ψ g) (hψ2 : ∀ g, ψ g ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β) (hβ0 : β ≤ Rectangular.beta0 d) :
    ∃ mass > 0, ∀ L : ℕ,
      let hK := kernel_isHermitian (d := d) (L := L) ψ β hclass hinv
      ∃ i₀ : State E d L, 0 < hK.eigenvalues i₀ ∧
        (∀ i, |hK.eigenvalues i| ≤ hK.eigenvalues i₀) ∧
        ∀ j, j ≠ i₀ → |hK.eigenvalues j / hK.eigenvalues i₀| ≤ Real.exp (-mass) := by
  let : MeasurableSpace E := ⊤
  obtain ⟨κ, hκ, hc⟩ := diagonal_correlations d ψ hψ0 hψ2 hβ hβ0
  refine ⟨κ / 2, by positivity, ?_⟩
  intro L
  have hq : Real.exp (-(κ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : Real.exp (-(κ / 2)) ^ 2 = Real.exp (-κ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hcorr := hc L
  simp only [twoStep_pow] at hcorr
  obtain ⟨i₀, h₀, hm, hg⟩ := Spectral.absolute_gap_of_squared_correlations
    (kernel (d := d) (L := L) ψ β) (kernel_isHermitian ψ β hclass hinv) (kernel_pos ψ β)
    (Real.exp_pos _) hq (show 0 ≤ 3 * Real.exp (6 * ((L + 3) ^ d * (d + 1) : ℕ)) by positivity)
    (by simpa only [hs] using hcorr)
  refine ⟨i₀, h₀, hm, ?_⟩
  intro j hj
  rw [abs_div, abs_of_pos h₀]
  exact (div_le_iff₀ h₀).mpr (hg j hj)

end WilsonFinite

#print axioms Rectangular.crossingInput
#print axioms Rectangular.slice_clustering
#print axioms WilsonFinite.kernel_isHermitian
#print axioms WilsonFinite.wilsonExpectation_eq_cycle
#print axioms CyclicMatrix.sum_cycle
#print axioms WilsonFinite.expectation_pair_eq
#print axioms WilsonFinite.diagonal_correlations
#print axioms Spectral.absolute_gap_of_squared_correlations
#print axioms WilsonFinite.uniform_twoStep_gap
#print axioms WilsonFinite.uniform_transfer_gap

end Mettapedia.QuantumTheory.YangMills.StrongCouplingTransferGap

import Mettapedia.Combinatorics.PolymerGas.ConnectedDecomposition
import Mettapedia.Combinatorics.PolymerGas.SupportRegrouping

/-!
# The connected plaquette expansion

Local perturbations with nonempty finite supports are collected into activities
indexed by their union of links. The product of the local factors is exactly
the hard-core polymer density of these activities.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {X Pl E : Type*} [Fintype X] [DecidableEq X] [Fintype Pl] [DecidableEq Pl]

/-- Plaquettes are adjacent if they are distinct and their link supports meet. -/
def plaquetteGraph (supp : Pl → Finset X) : SimpleGraph Pl where
  Adj p q := p ≠ q ∧ ¬ Disjoint (supp p) (supp q)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (supp : Pl → Finset X) : DecidableRel (plaquetteGraph supp).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ ¬ Disjoint _ _))

omit [Fintype X] [Fintype Pl] [DecidableEq Pl] in
/-- Distinct labelled supports are compatible exactly when they are
pairwise disjoint. Labels with equal supports remain distinct polymers. -/
theorem isCompatible_plaquetteGraph_iff (supp : Pl → Finset X) (Γ : Finset Pl) :
    IsCompatible (plaquetteGraph supp) Γ ↔ (Γ : Set Pl).PairwiseDisjoint supp := by
  constructor
  · intro h p hp q hq hpq
    by_contra hd
    exact h p hp q hq ⟨hpq, hd⟩
  · intro h p hp q hq hadj
    exact hadj.2 (h hp hq hadj.1)

omit [Fintype X] in
/-- Support size and site incidence bound the overlap degree. -/
theorem degree_plaquetteGraph_le_of_incidence (supp : Pl → Finset X) {s D : ℕ}
    (hs : ∀ p, (supp p).card ≤ s)
    (hD : ∀ x, ((univ : Finset Pl).filter (fun p ↦ x ∈ supp p)).card ≤ D) (p : Pl) :
    (plaquetteGraph supp).degree p ≤ s * D := by
  have hsub : (plaquetteGraph supp).neighborFinset p ⊆
      (supp p).biUnion (fun x ↦ univ.filter (fun q : Pl ↦ x ∈ supp q)) := by
    intro q hq
    obtain ⟨x, hxp, hxq⟩ := not_disjoint_iff.mp (((plaquetteGraph supp).mem_neighborFinset p q).mp hq).2
    exact mem_biUnion.mpr ⟨x, hxp, mem_filter.mpr ⟨mem_univ _, hxq⟩⟩
  exact (card_le_card hsub).trans ((card_biUnion_le_card_mul _ _ _
    (fun x _ ↦ hD x)).trans (Nat.mul_le_mul_right D (hs p)))

/-- The links used by a plaquette set. -/
def plaquetteSupport (supp : Pl → Finset X) (C : Finset Pl) : Finset X := C.biUnion supp

/-- All nonempty connected sets of plaquettes. -/
def connectedPlaquettes (supp : Pl → Finset X) : Finset (Finset Pl) :=
  univ.filter fun C : Finset Pl => ((plaquetteGraph supp).induce (C : Set Pl)).Connected

variable (supp : Pl → Finset X) (hne : ∀ p, (supp p).Nonempty)

include hne in
theorem plaquetteSupport_nonempty {C : Finset Pl}
    (hC : ((plaquetteGraph supp).induce (C : Set Pl)).Connected) :
    (plaquetteSupport supp C).Nonempty := by
  obtain ⟨p⟩ := hC.nonempty
  obtain ⟨x, hx⟩ := hne p.1
  exact ⟨x, mem_biUnion.mpr ⟨p.1, p.2, hx⟩⟩

include hne in
theorem isComponentFamily_plaquette_iff (Γ : Finset (Finset Pl)) :
    IsComponentFamily (plaquetteGraph supp) Γ ↔
      Γ ⊆ connectedPlaquettes supp ∧
        (Γ : Set (Finset Pl)).PairwiseDisjoint (plaquetteSupport supp) := by
  constructor
  · intro hΓ
    refine ⟨fun C hC => mem_filter.mpr ⟨mem_univ _, hΓ.1 C hC⟩, ?_⟩
    intro C hC D hD hCD
    apply disjoint_left.mpr
    intro x hxC hxD
    obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hxC
    obtain ⟨q, hq, hxq⟩ := mem_biUnion.mp hxD
    have hpq : p ≠ q := fun heq => disjoint_left.mp (hΓ.2.1 hC hD hCD) hp (heq ▸ hq)
    exact hΓ.2.2 C hC D hD hCD p hp q hq
      ⟨hpq, fun hd => disjoint_left.mp hd hxp hxq⟩
  · rintro ⟨hconn, hdisj⟩
    refine ⟨fun C hC => (mem_filter.mp (hconn hC)).2, ?_, ?_⟩
    · intro C hC D hD hCD
      apply disjoint_left.mpr
      intro p hpC hpD
      obtain ⟨x, hx⟩ := hne p
      exact disjoint_left.mp (hdisj hC hD hCD)
        (mem_biUnion.mpr ⟨p, hpC, hx⟩) (mem_biUnion.mpr ⟨p, hpD, hx⟩)
    · intro C hC D hD hCD p hp q hq hpq
      apply hpq.2
      apply disjoint_left.mpr
      intro x hxp hxq
      exact disjoint_left.mp (hdisj hC hD hCD)
        (mem_biUnion.mpr ⟨p, hp, hxp⟩) (mem_biUnion.mpr ⟨q, hq, hxq⟩)

include hne in
theorem support_injective_compatible_iff {Γ : Finset (Finset Pl)}
    (hconn : Γ ⊆ connectedPlaquettes supp) :
    (Set.InjOn (plaquetteSupport supp) (Γ : Set (Finset Pl)) ∧
      IsCompatible (overlapGraph X) (Γ.image (plaquetteSupport supp))) ↔
    IsComponentFamily (plaquetteGraph supp) Γ := by
  rw [isComponentFamily_plaquette_iff supp hne Γ]
  constructor
  · rintro ⟨hinj, hc⟩
    refine ⟨hconn, fun C hC D hD hCD => ?_⟩
    by_contra hd
    exact hc _ (mem_image_of_mem _ hC) _ (mem_image_of_mem _ hD)
      ⟨fun heq => hCD (hinj hC hD heq), hd⟩
  · rintro ⟨_, hdisj⟩
    constructor
    · intro C hC D hD heq
      by_contra hCD
      have hd : Disjoint (plaquetteSupport supp C) (plaquetteSupport supp D) := hdisj hC hD hCD
      rw [heq, disjoint_self] at hd
      exact (plaquetteSupport_nonempty supp hne (mem_filter.mp (hconn hD)).2).ne_empty hd
    · intro S hS T hT hadj
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hS
      obtain ⟨D, hD, rfl⟩ := mem_image.mp hT
      exact hadj.2 (hdisj hC hD (fun heq => hadj.1 (congrArg _ heq)))

/-- The activity at a link set, before restricting its configuration argument. -/
def plaquetteWeight (w : Pl → ℂ) (S : Finset X) : ℂ :=
  ∑ C ∈ (connectedPlaquettes supp).filter (fun C => plaquetteSupport supp C = S),
    ∏ p ∈ C, w p

include hne in
/-- The exact finite plaquette expansion, regrouped by link support. -/
theorem prod_one_add_eq_partitionFunction (w : Pl → ℂ) :
    (∏ p, (1 + w p)) = partitionFunction (overlapGraph X) (plaquetteWeight supp w) univ := by
  classical
  have hreg : partitionFunction (overlapGraph X) (plaquetteWeight supp w) univ =
      ∑ Γ ∈ (connectedPlaquettes supp).powerset,
        if Set.InjOn (plaquetteSupport supp) (Γ : Set (Finset Pl)) ∧
          IsCompatible (overlapGraph X) (Γ.image (plaquetteSupport supp)) then
            ∏ C ∈ Γ, ∏ p ∈ C, w p else 0 := by
    unfold partitionFunction plaquetteWeight
    rw [powerset_univ]
    convert sum_prod_fiberSums (connectedPlaquettes supp) (plaquetteSupport supp)
      (fun C => ∏ p ∈ C, w p) (IsCompatible (overlapGraph X)) using 1
    all_goals
      apply sum_congr rfl
      intro I hI
      split_ifs <;> rfl
  rw [hreg]
  rw [← sum_componentFamilies (G := plaquetteGraph supp) w]
  symm
  calc
    _ = ∑ Γ ∈ (connectedPlaquettes supp).powerset,
        if IsComponentFamily (plaquetteGraph supp) Γ then
          ∏ C ∈ Γ, ∏ p ∈ C, w p else 0 := by
      apply sum_congr rfl
      intro Γ hΓ
      simp only [support_injective_compatible_iff supp hne (mem_powerset.mp hΓ)]
    _ = ∑ Γ : Finset (Finset Pl),
        if IsComponentFamily (plaquetteGraph supp) Γ then
          ∏ C ∈ Γ, ∏ p ∈ C, w p else 0 := by
      apply sum_subset (subset_univ _)
      intro Γ _ hΓ
      have hnot : ¬ IsComponentFamily (plaquetteGraph supp) Γ := by
        intro hc
        exact hΓ (mem_powerset.mpr ((isComponentFamily_plaquette_iff supp hne Γ).mp hc).1)
      simp [hnot]
    _ = _ := by rw [componentFamilies, sum_filter]

/-- The same exact expansion with connected label sets kept as polymer
indices. This retains more support information than regrouping by their union. -/
theorem prod_one_add_eq_labelled_partitionFunction {R : Type*} [CommSemiring R]
    (supp : Pl → Finset X) (hne : ∀ p, (supp p).Nonempty) (w : Pl → R) :
    (∏ p, (1 + w p)) = partitionFunction (plaquetteGraph (plaquetteSupport supp))
      (fun C ↦ ∏ p ∈ C, w p) (connectedPlaquettes supp) := by
  rw [← sum_componentFamilies (G := plaquetteGraph supp) w]
  symm
  unfold partitionFunction
  calc
    _ = ∑ Γ ∈ (connectedPlaquettes supp).powerset,
        if IsComponentFamily (plaquetteGraph supp) Γ then
          ∏ C ∈ Γ, ∏ p ∈ C, w p else 0 := by
      apply sum_congr rfl
      intro Γ hΓ
      have hc : Γ ⊆ connectedPlaquettes supp := mem_powerset.mp hΓ
      simp only [isCompatible_plaquetteGraph_iff, isComponentFamily_plaquette_iff supp hne, and_iff_right hc]
    _ = ∑ Γ : Finset (Finset Pl),
        if IsComponentFamily (plaquetteGraph supp) Γ then
          ∏ C ∈ Γ, ∏ p ∈ C, w p else 0 := by
      apply sum_subset (subset_univ _)
      intro Γ _ hΓ
      have hnot : ¬ IsComponentFamily (plaquetteGraph supp) Γ := by
        intro hc
        exact hΓ (mem_powerset.mpr ((isComponentFamily_plaquette_iff supp hne Γ).mp hc).1)
      simp [hnot]
    _ = _ := by rw [componentFamilies, sum_filter]

/-- Extend a configuration by a fixed reference value outside its support. -/
def extendConfiguration (base : E) (S : Finset X) (v : S → E) : X → E :=
  fun x => if h : x ∈ S then v ⟨x, h⟩ else base

/-- A perturbation depends only on the variables in its plaquette support. -/
def PlaquetteLocal (f : Pl → (X → E) → ℂ) : Prop :=
  ∀ p ω ω', (∀ x ∈ supp p, ω x = ω' x) → f p ω = f p ω'

/-- The connected activity, as a function of the configuration on its link set. -/
def plaquetteActivity (base : E) (f : Pl → (X → E) → ℂ)
    (S : Finset X) (v : S → E) : ℂ :=
  plaquetteWeight supp (fun p => f p (extendConfiguration base S v)) S

theorem plaquetteActivity_restrictTo (base : E) (f : Pl → (X → E) → ℂ)
    (hloc : PlaquetteLocal supp f) (S : Finset X) (ω : X → E) :
    plaquetteActivity supp base f S (restrictTo S ω) =
      plaquetteWeight supp (fun p => f p ω) S := by
  apply sum_congr rfl
  intro C hC
  obtain ⟨_, hCS⟩ := mem_filter.mp hC
  apply prod_congr rfl
  intro p hp
  apply hloc
  intro x hx
  have hxS : x ∈ S := hCS ▸ mem_biUnion.mpr ⟨p, hp, hx⟩
  simp [extendConfiguration, hxS, restrictTo]

include hne in
/-- The local product is exactly the polymer density on all link sets. -/
theorem prod_one_add_eq_polymerDensity (base : E) (f : Pl → (X → E) → ℂ)
    (hloc : PlaquetteLocal supp f) (ω : X → E) :
    (∏ p, (1 + f p ω)) = polymerDensity (plaquetteActivity supp base f) univ ω := by
  unfold polymerDensity
  simp_rw [plaquetteActivity_restrictTo supp base f hloc]
  exact prod_one_add_eq_partitionFunction supp hne (fun p => f p ω)

include hne in
theorem plaquetteWeight_empty (w : Pl → ℂ) : plaquetteWeight supp w ∅ = 0 := by
  apply sum_eq_zero
  intro C hC
  obtain ⟨hC, hCS⟩ := mem_filter.mp hC
  exact ((plaquetteSupport_nonempty supp hne (mem_filter.mp hC).2).ne_empty hCS).elim

include hne in
@[simp] theorem plaquetteActivity_empty (base : E) (f : Pl → (X → E) → ℂ)
    (v : (∅ : Finset X) → E) : plaquetteActivity supp base f ∅ v = 0 :=
  plaquetteWeight_empty supp hne _

/-- The scalar majorant obtained by replacing every local factor by `δ`. -/
def plaquetteMajorant (δ : ℝ) (S : Finset X) : ℝ :=
  ∑ C ∈ (connectedPlaquettes supp).filter (fun C => plaquetteSupport supp C = S),
    δ ^ C.card

include hne in
@[simp] theorem plaquetteMajorant_empty (δ : ℝ) : plaquetteMajorant supp δ ∅ = 0 := by
  apply sum_eq_zero
  intro C hC
  obtain ⟨hC, hCS⟩ := mem_filter.mp hC
  exact ((plaquetteSupport_nonempty supp hne (mem_filter.mp hC).2).ne_empty hCS).elim

theorem plaquetteMajorant_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (S : Finset X) :
    0 ≤ plaquetteMajorant supp δ S := sum_nonneg fun _ _ => pow_nonneg hδ _

theorem norm_plaquetteActivity_le (base : E) (f : Pl → (X → E) → ℂ)
    {δ : ℝ} (hf : ∀ p ω, ‖f p ω‖ ≤ δ) (S : Finset X) (v : S → E) :
    ‖plaquetteActivity supp base f S v‖ ≤ plaquetteMajorant supp δ S := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun C _ => ?_)
  rw [norm_prod]
  calc
    (∏ p ∈ C, ‖f p (extendConfiguration base S v)‖) ≤ ∏ _p ∈ C, δ :=
      prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hf p _)
    _ = δ ^ C.card := by simp

section Measurability

variable [MeasurableSpace E]

omit [Fintype X] [Fintype Pl] [DecidableEq Pl] in
theorem measurable_extendConfiguration (base : E) (S : Finset X) :
    Measurable (extendConfiguration base S) := by
  apply measurable_pi_lambda
  intro x
  by_cases hx : x ∈ S
  · simpa only [extendConfiguration, hx, ↓reduceDIte] using
      (measurable_pi_apply (⟨x, hx⟩ : S))
  · simpa only [extendConfiguration, hx, ↓reduceDIte] using
      (measurable_const (a := base) : Measurable (fun _ : (S → E) => base))

theorem measurable_plaquetteActivity (base : E) (f : Pl → (X → E) → ℂ)
    (hf : ∀ p, Measurable (f p)) (S : Finset X) :
    Measurable (plaquetteActivity supp base f S) := by
  apply Finset.measurable_sum
  intro C _
  apply Finset.measurable_prod
  intro p _
  exact (hf p).comp (measurable_extendConfiguration base S)

end Measurability

section Integration
variable [MeasurableSpace E]
variable (ν₀ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure ν₀]
open MeasureTheory

/-- Independent labelled local functions factor under the product law.
The full-configuration formulation keeps labels distinct from supports. -/
theorem integral_prod_of_disjoint_supports {P 𝕜 : Type*} [DecidableEq P] [RCLike 𝕜]
    (base : E) (supp : P → Finset X) (f : P → (X → E) → 𝕜)
    (hf : ∀ p, Measurable (f p))
    (hlocal : ∀ p U V, (∀ x ∈ supp p, U x = V x) → f p U = f p V)
    (I : Finset P) (hI : (I : Set P).PairwiseDisjoint supp) :
    (∫ U, ∏ p ∈ I, f p U ∂Measure.pi (fun _ : X ↦ ν₀)) =
      ∏ p ∈ I, ∫ U, f p U ∂Measure.pi (fun _ : X ↦ ν₀) := by
  let g : ∀ p, (supp p → E) → 𝕜 := fun p v ↦ f p (extendConfiguration base (supp p) v)
  have hg p : Measurable (g p) := (hf p).comp (measurable_extendConfiguration base (supp p))
  have he p U : g p (restrictTo (supp p) U) = f p U := by
    apply hlocal
    intro x hx
    simp [extendConfiguration, restrictTo, hx]
  have h := integral_prod_supported_eq_prod ν₀ supp g hg I hI
  simpa only [he] using h

/-- Integrating the exact connected-family expansion factors precisely the
families with disjoint dependency supports. Integrability is explicit. -/
theorem integral_prod_one_add_eq_labelledPartition (base : E)
    (supp : Pl → Finset X) (hne : ∀ p, (supp p).Nonempty)
    (f : Pl → (X → E) → ℝ) (hf : ∀ p, Measurable (f p))
    (hlocal : ∀ p U V, (∀ x ∈ supp p, U x = V x) → f p U = f p V)
    (hint : ∀ Γ : Finset (Finset Pl), Integrable (fun U ↦ ∏ C ∈ Γ, ∏ p ∈ C, f p U)
      (Measure.pi fun _ : X ↦ ν₀)) :
    (∫ U, ∏ p, (1 + f p U) ∂Measure.pi (fun _ : X ↦ ν₀)) =
      partitionFunction (plaquetteGraph (plaquetteSupport supp))
        (fun C ↦ ∫ U, ∏ p ∈ C, f p U ∂Measure.pi (fun _ : X ↦ ν₀))
        (connectedPlaquettes supp) := by
  have he U := prod_one_add_eq_labelled_partitionFunction supp hne (fun p ↦ f p U)
  simp_rw [he]
  unfold partitionFunction
  rw [integral_finsetSum _ (fun Γ _ ↦ by
    by_cases hΓ : IsCompatible (plaquetteGraph (plaquetteSupport supp)) Γ
    · simpa only [if_pos hΓ] using hint Γ
    · simp only [if_neg hΓ]
      exact integrable_zero (X → E) ℝ (Measure.pi fun _ : X ↦ ν₀))]
  apply sum_congr rfl
  intro Γ hΓ
  by_cases hc : IsCompatible (plaquetteGraph (plaquetteSupport supp)) Γ
  · simp only [if_pos hc]
    apply integral_prod_of_disjoint_supports ν₀ base (plaquetteSupport supp)
      (fun C U ↦ ∏ p ∈ C, f p U)
    · intro C
      exact Finset.measurable_prod _ (fun p _ ↦ hf p)
    · intro C U V huv
      apply prod_congr rfl
      intro p hp
      exact hlocal p U V (fun x hx ↦ huv x (mem_biUnion.mpr ⟨p, hp, hx⟩))
    · exact (isCompatible_plaquetteGraph_iff _ Γ).mp hc
  · simp only [if_neg hc, integral_zero]

end Integration


#print axioms prod_one_add_eq_partitionFunction
#print axioms prod_one_add_eq_polymerDensity
#print axioms plaquetteActivity_empty
#print axioms norm_plaquetteActivity_le
#print axioms measurable_plaquetteActivity

end Mettapedia.Combinatorics.PolymerGas

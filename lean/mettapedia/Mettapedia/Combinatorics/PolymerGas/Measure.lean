import Mettapedia.Combinatorics.PolymerGas.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Polymer representations of measures on block configurations

Let `X` be a finite set of blocks, `E` a measurable space of block states and
`ν₀` a probability measure on `E`.  The reference measure is the product
`ν = ⊗_{x ∈ X} ν₀` on configurations `ω : X → E`.  A polymer is a finite set of
blocks; two distinct polymers are incompatible when they overlap
(`overlapGraph`).  An activity assigns to each polymer `S` a function `K S` of
the configuration on `S`, and the polymer density

`ρ(ω) = ∑_{Γ compatible} ∏_{γ ∈ Γ} K γ (ω|_γ)`

is the partition function of `Λ` with the configuration-dependent activities
`K γ (ω|_γ)` (`polymerDensity`).

Because the reference measure is a product, the integral of a product of
functions of pairwise disjoint blocks is the product of their integrals
(`integral_prod_restrictTo_eq_prod`), and a function of the configuration on `Y`
is independent of any function of the configuration outside `Y`
(`integral_mul_of_dependsOutside`).  Hence `∫ ρ dν` is the partition function of
the integrated polymer gas with activities `∫ K γ (ω|_γ) dν(ω)`
(`integral_polymerDensity`).  Every compatible family splits into the polymers
meeting a block set `S` and a compatible family of polymers disjoint from `S`
and from them (`polymerDensity_eq_sum_meeting`), so the integral of an
observable `F` of the configuration on `S` against `ρ` is a sum over the
compatible families `Γ` of polymers meeting `S` of the integral of `F` times
their activities, weighted by the partition function of the polymers disjoint
from `S ∪ ⋃ Γ` (`integral_mul_polymerDensity`).
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace Mettapedia.Combinatorics.PolymerGas

/-! ## Polymers as sets of blocks -/

/-- Two distinct polymers are incompatible when they overlap. -/
def overlapGraph (X : Type*) : SimpleGraph (Finset X) where
  Adj S T := S ≠ T ∧ ¬ Disjoint S T
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {X : Type*} [DecidableEq X]

instance : DecidableRel (overlapGraph X).Adj := fun S T => by
  unfold overlapGraph
  infer_instance

theorem isCompatible_overlapGraph_iff {I : Finset (Finset X)} :
    IsCompatible (overlapGraph X) I ↔ (I : Set (Finset X)).PairwiseDisjoint id := by
  constructor
  · intro h S hS T hT hST
    by_contra hd
    exact h S hS T hT ⟨hST, hd⟩
  · intro h S hS T hT hadj
    exact hadj.2 (h hS hT hadj.1)

/-- A sum over the subsets of `Λ` splits along a subset `M ⊆ Λ`. -/
theorem sum_powerset_eq_sum_sum {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {Λ M : Finset α} (hM : M ⊆ Λ) (f : Finset α → β) :
    ∑ I ∈ Λ.powerset, f I = ∑ Γ ∈ M.powerset, ∑ I' ∈ (Λ \ M).powerset, f (Γ ∪ I') := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun I => (I ∩ M, I \ M))
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    simp only [mem_powerset]
    exact union_subset (hp.1.trans hM) (hp.2.trans sdiff_subset)
  · intro I hI
    simp only [mem_powerset] at hI
    simp only [mem_product, mem_powerset]
    exact ⟨inter_subset_right, sdiff_subset_sdiff hI subset_rfl⟩
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have h1 : (p.1 ∪ p.2) ∩ M = p.1 := by
      ext u
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hu | hu, huM⟩
        · exact hu
        · exact absurd huM (mem_sdiff.mp (hp.2 hu)).2
      · intro hu
        exact ⟨Or.inl hu, hp.1 hu⟩
    have h2 : (p.1 ∪ p.2) \ M = p.2 := by
      ext u
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hu | hu, huM⟩
        · exact absurd (hp.1 hu) huM
        · exact hu
      · intro hu
        exact ⟨Or.inr hu, (mem_sdiff.mp (hp.2 hu)).2⟩
    ext <;> simp [h1, h2]
  · intro I _
    ext u
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  · intro p _
    rfl

/-! ## Configurations and the product reference measure -/

variable {E : Type*} [MeasurableSpace E]

/-- The restriction of a configuration to a set of blocks. -/
def restrictTo (S : Finset X) (ω : X → E) : S → E := fun i => ω i

omit [DecidableEq X] in
theorem measurable_restrictTo (S : Finset X) : Measurable (restrictTo (E := E) S) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : X)

variable [Fintype X] (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

/-- **Block independence.**  Under the product reference measure, the integral of
a product of functions of pairwise disjoint blocks is the product of their
integrals. -/
theorem integral_prod_supported_eq_prod {P 𝕜 : Type*} [DecidableEq P] [RCLike 𝕜]
    (supp : P → Finset X) (f : ∀ p, (supp p → E) → 𝕜)
    (hf : ∀ p, Measurable (f p)) :
    ∀ I : Finset P, (I : Set P).PairwiseDisjoint supp →
      ∫ ω, ∏ S ∈ I, f S (restrictTo (supp S) ω) ∂(Measure.pi fun _ : X => ν₀) =
        ∏ S ∈ I, ∫ ω, f S (restrictTo (supp S) ω) ∂(Measure.pi fun _ : X => ν₀) := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert S₀ I hS₀ ih =>
    intro hI
    have hI' : (I : Set P).PairwiseDisjoint supp :=
      hI.subset (by rw [coe_insert]; exact Set.subset_insert _ _)
    have hdisj : ∀ S ∈ I, Disjoint (supp S₀) (supp S) := fun S hS =>
      hI (mem_insert_self S₀ I) (mem_insert_of_mem hS) fun h => hS₀ (h ▸ hS)
    set T : Finset X := I.biUnion supp with hTdef
    have hS₀T : Disjoint (supp S₀) T := by
      rw [hTdef, Finset.disjoint_biUnion_right]
      exact fun S hS => hdisj S hS
    let g : (T → E) → 𝕜 := fun v =>
      ∏ S ∈ I.attach, f S.1 fun i => v ⟨i.1, mem_biUnion.mpr ⟨S.1, S.2, i.2⟩⟩
    have hg : Measurable g :=
      Finset.measurable_prod _ fun S _ =>
        (hf S.1).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
    have hgI : ∀ ω : X → E, ∏ S ∈ I, f S (restrictTo (supp S) ω) = g (restrictTo T ω) := by
      intro ω
      rw [← Finset.prod_attach I]
      rfl
    have hcoord : iIndepFun (fun (i : X) (ω : X → E) => ω i) (Measure.pi fun _ : X => ν₀) :=
      iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
    have hind : IndepFun (fun ω => f S₀ (restrictTo (supp S₀) ω)) (fun ω => g (restrictTo T ω))
        (Measure.pi fun _ : X => ν₀) :=
      (hcoord.indepFun_finset (supp S₀) T hS₀T fun i => measurable_pi_apply i).comp (hf S₀) hg
    simp only [prod_insert hS₀]
    rw [← ih hI']
    simp_rw [hgI]
    exact hind.integral_fun_mul_eq_mul_integral
      ((hf S₀).comp (measurable_restrictTo (supp S₀))).aestronglyMeasurable
      (hg.comp (measurable_restrictTo T)).aestronglyMeasurable


/-- The support-labelled block independence theorem specialized to labels
that are themselves finite supports. -/
theorem integral_prod_restrictTo_eq_prod (f : ∀ S : Finset X, (S → E) → ℂ)
    (hf : ∀ S, Measurable (f S)) :
    ∀ I : Finset (Finset X), (I : Set (Finset X)).PairwiseDisjoint id →
      ∫ ω, ∏ S ∈ I, f S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀) =
        ∏ S ∈ I, ∫ ω, f S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀) :=
  integral_prod_supported_eq_prod ν₀ id f hf

/-- An extra block `Y` disjoint from pairwise disjoint blocks factors out. -/
theorem integral_mul_prod_restrictTo (Y : Finset X) (H : (Y → E) → ℂ) (hH : Measurable H)
    (f : ∀ S : Finset X, (S → E) → ℂ) (hf : ∀ S, Measurable (f S))
    (I : Finset (Finset X)) (hI : (I : Set (Finset X)).PairwiseDisjoint id)
    (hY : ∀ S ∈ I, Disjoint Y S) :
    ∫ ω, H (restrictTo Y ω) * ∏ S ∈ I, f S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀) =
      (∫ ω, H (restrictTo Y ω) ∂(Measure.pi fun _ : X => ν₀)) *
        ∏ S ∈ I, ∫ ω, f S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀) := by
  set T : Finset X := I.biUnion id with hTdef
  have hYT : Disjoint Y T := by
    rw [hTdef, Finset.disjoint_biUnion_right]
    exact fun S hS => hY S hS
  let g : (T → E) → ℂ := fun v =>
    ∏ S ∈ I.attach, f S.1 fun i => v ⟨i.1, mem_biUnion.mpr ⟨S.1, S.2, i.2⟩⟩
  have hg : Measurable g :=
    Finset.measurable_prod _ fun S _ =>
      (hf S.1).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hgI : ∀ ω : X → E, ∏ S ∈ I, f S (restrictTo S ω) = g (restrictTo T ω) := by
    intro ω
    rw [← Finset.prod_attach I]
    rfl
  have hcoord : iIndepFun (fun (i : X) (ω : X → E) => ω i) (Measure.pi fun _ : X => ν₀) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hind : IndepFun (fun ω => H (restrictTo Y ω)) (fun ω => g (restrictTo T ω))
      (Measure.pi fun _ : X => ν₀) :=
    (hcoord.indepFun_finset Y T hYT fun i => measurable_pi_apply i).comp hH hg
  rw [← integral_prod_restrictTo_eq_prod ν₀ f hf I hI]
  simp_rw [hgI]
  exact hind.integral_fun_mul_eq_mul_integral
    (hH.comp (measurable_restrictTo Y)).aestronglyMeasurable
    (hg.comp (measurable_restrictTo T)).aestronglyMeasurable

/-! ## Polymer densities -/

/-- The polymer density: the partition function of `Λ` with the
configuration-dependent activities `K γ (ω|_γ)`. -/
def polymerDensity (K : ∀ S : Finset X, (S → E) → ℂ) (Λ : Finset (Finset X))
    (ω : X → E) : ℂ :=
  partitionFunction (overlapGraph X) (fun S => K S (restrictTo S ω)) Λ

/-- The activities of the integrated polymer gas. -/
def integratedActivity (K : ∀ S : Finset X, (S → E) → ℂ) (S : Finset X) : ℂ :=
  ∫ ω, K S (restrictTo S ω) ∂(Measure.pi fun _ : X => ν₀)

omit [DecidableEq X] in
theorem integrable_prod_restrictTo (K : ∀ S : Finset X, (S → E) → ℂ)
    (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S)
    (I : Finset (Finset X)) :
    Integrable (fun ω => ∏ S ∈ I, K S (restrictTo S ω)) (Measure.pi fun _ : X => ν₀) := by
  refine Integrable.of_bound
    (Finset.measurable_prod _ fun S _ =>
      (hK S).comp (measurable_restrictTo S)).aestronglyMeasurable
    (∏ S ∈ I, k S) (ae_of_all _ fun ω => ?_)
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun S _ => hk S _

/-- The integral of the polymer density is the partition function of the
integrated polymer gas. -/
theorem integral_polymerDensity (K : ∀ S : Finset X, (S → E) → ℂ)
    (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S)
    (Λ : Finset (Finset X)) :
    ∫ ω, polymerDensity K Λ ω ∂(Measure.pi fun _ : X => ν₀) =
      partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ := by
  unfold polymerDensity partitionFunction
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro I _
    split_ifs with hc
    · exact integral_prod_restrictTo_eq_prod ν₀ K hK I (isCompatible_overlapGraph_iff.mp hc)
    · simp
  · intro I _
    split_ifs
    · exact integrable_prod_restrictTo ν₀ K hK k hk I
    · exact integrable_zero _ _ _


/-! ## Functions of the configuration outside a block set -/

/-- `G` depends only on the configuration outside `Y`. -/
def DependsOutside (Y : Finset X) (G : (X → E) → ℂ) : Prop :=
  ∀ ω ω' : X → E, (∀ i, i ∉ Y → ω i = ω' i) → G ω = G ω'

/-- **Factorization across a block set.**  A function of the configuration on `Y`
and a function of the configuration outside `Y` are independent under the product
reference measure. -/
theorem integral_mul_of_dependsOutside [Nonempty E] (Y : Finset X) (H : (Y → E) → ℂ)
    (hH : Measurable H) (G : (X → E) → ℂ) (hG : Measurable G) (hGY : DependsOutside Y G) :
    ∫ ω, H (restrictTo Y ω) * G ω ∂(Measure.pi fun _ : X => ν₀) =
      (∫ ω, H (restrictTo Y ω) ∂(Measure.pi fun _ : X => ν₀)) *
        ∫ ω, G ω ∂(Measure.pi fun _ : X => ν₀) := by
  classical
  obtain ⟨e₀⟩ := ‹Nonempty E›
  set Yc : Finset X := Finset.univ \ Y with hYc
  let ext : (Yc → E) → (X → E) := fun v i => if h : i ∈ Yc then v ⟨i, h⟩ else e₀
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i ∈ Yc
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_pi_apply _
    · simp only [ext, h, ↓reduceDIte]
      exact measurable_const
  let G' : (Yc → E) → ℂ := fun v => G (ext v)
  have hG' : Measurable G' := hG.comp hext
  have hGG' : ∀ ω, G ω = G' (restrictTo Yc ω) := by
    intro ω
    apply hGY
    intro i hi
    have hiYc : i ∈ Yc := by simp [hYc, hi]
    simp [ext, restrictTo, hiYc]
  have hYYc : Disjoint Y Yc := by
    rw [hYc]
    exact disjoint_sdiff
  have hcoord : iIndepFun (fun (i : X) (ω : X → E) => ω i) (Measure.pi fun _ : X => ν₀) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hind : IndepFun (fun ω => H (restrictTo Y ω)) (fun ω => G' (restrictTo Yc ω))
      (Measure.pi fun _ : X => ν₀) :=
    (hcoord.indepFun_finset Y Yc hYYc fun i => measurable_pi_apply i).comp hH hG'
  simp_rw [hGG']
  exact hind.integral_fun_mul_eq_mul_integral
    (hH.comp (measurable_restrictTo Y)).aestronglyMeasurable
    (hG'.comp (measurable_restrictTo Yc)).aestronglyMeasurable

omit [Fintype X] in
theorem measurable_polymerDensity (K : ∀ S : Finset X, (S → E) → ℂ)
    (hK : ∀ S, Measurable (K S)) (Λ : Finset (Finset X)) :
    Measurable (polymerDensity K Λ) := by
  unfold polymerDensity partitionFunction
  refine Finset.measurable_sum _ fun I _ => ?_
  split_ifs
  · exact Finset.measurable_prod _ fun S _ => (hK S).comp (measurable_restrictTo S)
  · exact measurable_const

/-! ## Conditioning on a block set -/

/-- The polymers of `Λ` meeting `S`. -/
def meeting (Λ : Finset (Finset X)) (S : Finset X) : Finset (Finset X) :=
  Λ.filter fun γ => ¬ Disjoint γ S

/-- The polymers of `Λ` disjoint from `Y`. -/
def avoiding (Λ : Finset (Finset X)) (Y : Finset X) : Finset (Finset X) :=
  Λ.filter fun γ => Disjoint γ Y

omit [Fintype X] in
theorem meeting_subset (Λ : Finset (Finset X)) (S : Finset X) : meeting Λ S ⊆ Λ :=
  filter_subset _ _

omit [MeasurableSpace E] [Fintype X] in
theorem dependsOutside_polymerDensity_avoiding (K : ∀ S : Finset X, (S → E) → ℂ)
    (Λ : Finset (Finset X)) (Y : Finset X) :
    DependsOutside Y (polymerDensity K (avoiding Λ Y)) := by
  intro ω ω' h
  unfold polymerDensity partitionFunction
  apply sum_congr rfl
  intro I hI
  split_ifs
  · apply prod_congr rfl
    intro γ hγ
    have hγY : Disjoint γ Y := (mem_filter.mp (mem_powerset.mp hI hγ)).2
    show K γ (restrictTo γ ω) = K γ (restrictTo γ ω')
    congr 1
    funext i
    exact h i fun hiY => Finset.disjoint_left.mp hγY i.2 hiY
  · rfl

omit [Fintype X] in
theorem isCompatible_union_iff {Γ I : Finset (Finset X)} :
    IsCompatible (overlapGraph X) (Γ ∪ I) ↔
      IsCompatible (overlapGraph X) Γ ∧ IsCompatible (overlapGraph X) I ∧
        ∀ γ ∈ Γ, ∀ γ' ∈ I, ¬ (overlapGraph X).Adj γ γ' := by
  constructor
  · intro h
    exact ⟨fun u hu v hv => h u (mem_union_left _ hu) v (mem_union_left _ hv),
      fun u hu v hv => h u (mem_union_right _ hu) v (mem_union_right _ hv),
      fun u hu v hv => h u (mem_union_left _ hu) v (mem_union_right _ hv)⟩
  · rintro ⟨h1, h2, h3⟩ u hu v hv
    rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
    · exact h1 u hu v hv
    · exact h3 u hu v hv
    · exact fun hadj => h3 v hv u hu hadj.symm
    · exact h2 u hu v hv

omit [Fintype X] in
/-- For polymers disjoint from `S`, compatibility with a family `Γ` of polymers
meeting `S` means avoiding `S ∪ ⋃ Γ`. -/
theorem subset_avoiding_iff {Λ Γ I : Finset (Finset X)} {S : Finset X}
    (hΓ : Γ ⊆ meeting Λ S) (hI : I ⊆ Λ \ meeting Λ S) :
    (∀ γ ∈ Γ, ∀ γ' ∈ I, ¬ (overlapGraph X).Adj γ γ') ↔
      I ⊆ avoiding Λ (S ∪ Γ.biUnion id) := by
  constructor
  · intro h γ' hγ'
    have hγ'Λ := mem_sdiff.mp (hI hγ')
    have hS : Disjoint γ' S := by
      by_contra hnd
      exact hγ'Λ.2 (mem_filter.mpr ⟨hγ'Λ.1, hnd⟩)
    refine mem_filter.mpr ⟨hγ'Λ.1, disjoint_union_right.mpr ⟨hS, ?_⟩⟩
    rw [Finset.disjoint_biUnion_right]
    intro γ hγ
    have hne : γ ≠ γ' := by
      intro heq
      have hγS := (mem_filter.mp (hΓ hγ)).2
      exact hγS (heq ▸ hS)
    by_contra hnd
    exact h γ hγ γ' hγ' ⟨hne, fun hd => hnd hd.symm⟩
  · intro h γ hγ γ' hγ' hadj
    have hav := (mem_filter.mp (h hγ')).2
    rw [disjoint_union_right, Finset.disjoint_biUnion_right] at hav
    exact hadj.2 (hav.2 γ hγ).symm

omit [Fintype X] [MeasurableSpace E] in
/-- **Decomposition of the polymer density along a block set.**  Every compatible
family splits into the polymers meeting `S` and a compatible family of polymers
disjoint from `S` and from them. -/
theorem polymerDensity_eq_sum_meeting (K : ∀ S : Finset X, (S → E) → ℂ)
    (Λ : Finset (Finset X)) (S : Finset X) (ω : X → E) :
    polymerDensity K Λ ω = ∑ Γ ∈ (meeting Λ S).powerset,
      if IsCompatible (overlapGraph X) Γ then
        (∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
          polymerDensity K (avoiding Λ (S ∪ Γ.biUnion id)) ω
      else 0 := by
  set M := meeting Λ S with hMdef
  unfold polymerDensity partitionFunction
  rw [sum_powerset_eq_sum_sum (meeting_subset Λ S)]
  apply sum_congr rfl
  intro Γ hΓ
  have hΓM : Γ ⊆ M := mem_powerset.mp hΓ
  split_ifs with hcΓ
  · set Y : Finset X := S ∪ Γ.biUnion id with hYdef
    have hAsub : avoiding Λ Y ⊆ Λ \ M := by
      intro γ hγ
      have h := mem_filter.mp hγ
      refine mem_sdiff.mpr ⟨h.1, fun hM => ?_⟩
      exact (mem_filter.mp hM).2 (disjoint_of_subset_right subset_union_left h.2)
    have hterm : ∀ I ∈ (Λ \ M).powerset,
        (if IsCompatible (overlapGraph X) (Γ ∪ I) then
          ∏ γ ∈ Γ ∪ I, K γ (restrictTo γ ω) else 0) =
        if I ⊆ avoiding Λ Y then
          (∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
            (if IsCompatible (overlapGraph X) I then ∏ γ ∈ I, K γ (restrictTo γ ω) else 0)
        else 0 := by
      intro I hI
      have hIsub : I ⊆ Λ \ M := mem_powerset.mp hI
      have hiff := subset_avoiding_iff hΓM hIsub
      have hdisj : Disjoint Γ I :=
        disjoint_of_subset_left hΓM (disjoint_of_subset_right hIsub disjoint_sdiff)
      by_cases hIA : I ⊆ avoiding Λ Y
      · by_cases hcI : IsCompatible (overlapGraph X) I
        · have hcU : IsCompatible (overlapGraph X) (Γ ∪ I) :=
            isCompatible_union_iff.mpr ⟨hcΓ, hcI, hiff.mpr hIA⟩
          simp only [hcU, hIA, hcI, ↓reduceIte]
          rw [prod_union hdisj]
        · have hcU : ¬ IsCompatible (overlapGraph X) (Γ ∪ I) := fun h =>
            hcI (isCompatible_union_iff.mp h).2.1
          simp only [hcU, hIA, hcI, ↓reduceIte, mul_zero]
      · have hcU : ¬ IsCompatible (overlapGraph X) (Γ ∪ I) := fun h =>
          hIA (hiff.mp (isCompatible_union_iff.mp h).2.2)
        simp only [hcU, hIA, ↓reduceIte]
    rw [sum_congr rfl hterm, ← sum_filter]
    have hfilter : (Λ \ M).powerset.filter (· ⊆ avoiding Λ Y) =
        (avoiding Λ Y).powerset := by
      ext I
      simp only [mem_filter, mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨h.trans hAsub, h⟩⟩
    rw [hfilter, ← mul_sum]
  · apply sum_eq_zero
    intro I _
    have hcU : ¬ IsCompatible (overlapGraph X) (Γ ∪ I) := fun h =>
      hcΓ (isCompatible_union_iff.mp h).1
    simp only [hcU, ↓reduceIte]

omit [DecidableEq X] [MeasurableSpace E] [Fintype X] in
theorem activityBound_nonneg [Nonempty E] {K : ∀ S : Finset X, (S → E) → ℂ} {k : Finset X → ℝ}
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (S : Finset X) : 0 ≤ k S := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  exact (norm_nonneg _).trans (hk S fun _ => e₀)

omit [Fintype X] in
theorem norm_polymerDensity_le [Nonempty E] (K : ∀ S : Finset X, (S → E) → ℂ)
    (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S) (Λ : Finset (Finset X)) (ω : X → E) :
    ‖polymerDensity K Λ ω‖ ≤ ∑ I ∈ Λ.powerset, ∏ γ ∈ I, k γ := by
  unfold polymerDensity partitionFunction
  refine (norm_sum_le _ _).trans (sum_le_sum fun I _ => ?_)
  split_ifs
  · rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun γ _ => hk γ _
  · rw [norm_zero]
    exact Finset.prod_nonneg fun γ _ => activityBound_nonneg hk γ

/-- **Conditioning on a block set.**  For an observable `F` of the configuration
on `S`, the integral of `F` against the polymer density is a sum over the
compatible families `Γ` of polymers meeting `S` of the integral of `F` times
their activities, weighted by the partition function of the integrated gas of
polymers disjoint from `S ∪ ⋃ Γ`. -/
theorem integral_mul_polymerDensity [Nonempty E] (S : Finset X) (F : (S → E) → ℂ)
    (hF : Measurable F) (CF : ℝ) (hFb : ∀ v, ‖F v‖ ≤ CF)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (Λ : Finset (Finset X)) :
    ∫ ω, F (restrictTo S ω) * polymerDensity K Λ ω ∂(Measure.pi fun _ : X => ν₀) =
      ∑ Γ ∈ (meeting Λ S).powerset,
        if IsCompatible (overlapGraph X) Γ then
          (∫ ω, F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω)
              ∂(Measure.pi fun _ : X => ν₀)) *
            partitionFunction (overlapGraph X) (integratedActivity ν₀ K)
              (avoiding Λ (S ∪ Γ.biUnion id))
        else 0 := by
  have hCF : 0 ≤ CF := by
    obtain ⟨e₀⟩ := ‹Nonempty E›
    exact (norm_nonneg _).trans (hFb fun _ => e₀)
  simp_rw [polymerDensity_eq_sum_meeting K Λ S, mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro Γ _
    split_ifs with hcΓ
    · set Y : Finset X := S ∪ Γ.biUnion id with hYdef
      let H : (Y → E) → ℂ := fun v =>
        F (fun i => v ⟨i.1, mem_union_left _ i.2⟩) *
          ∏ γ ∈ Γ.attach, K γ.1 fun i =>
            v ⟨i.1, mem_union_right _ (mem_biUnion.mpr ⟨γ.1, γ.2, i.2⟩)⟩
      have hH : Measurable H :=
        (hF.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).mul
          (Finset.measurable_prod _ fun γ _ =>
            (hK γ.1).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _))
      have hHY : ∀ ω, H (restrictTo Y ω) =
          F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω) := by
        intro ω
        simp only [H]
        rw [← Finset.prod_attach Γ]
        rfl
      have hfun : (fun ω => F (restrictTo S ω) * ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
          polymerDensity K (avoiding Λ Y) ω)) =
          fun ω => H (restrictTo Y ω) * polymerDensity K (avoiding Λ Y) ω := by
        funext ω
        rw [hHY, mul_assoc]
      rw [hfun, integral_mul_of_dependsOutside ν₀ Y H hH _ (measurable_polymerDensity K hK _)
        (dependsOutside_polymerDensity_avoiding K Λ Y), integral_polymerDensity ν₀ K hK k hk]
      simp_rw [hHY]
    · simp
  · intro Γ _
    split_ifs
    · refine Integrable.of_bound
        ((hF.comp (measurable_restrictTo S)).mul
          ((Finset.measurable_prod _ fun γ _ => (hK γ).comp (measurable_restrictTo γ)).mul
            (measurable_polymerDensity K hK _))).aestronglyMeasurable
        (CF * ((∏ γ ∈ Γ, k γ) * ∑ I ∈ (avoiding Λ (S ∪ Γ.biUnion id)).powerset,
          ∏ γ ∈ I, k γ)) (ae_of_all _ fun ω => ?_)
      rw [norm_mul, norm_mul, norm_prod]
      have hkn : ∀ γ, 0 ≤ k γ := activityBound_nonneg hk
      refine mul_le_mul (hFb _) (mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun γ _ => hk γ _) (norm_polymerDensity_le K k hk _ ω) (norm_nonneg _)
        (Finset.prod_nonneg fun γ _ => hkn γ)) (by positivity) hCF
    · simp

#print axioms integral_prod_restrictTo_eq_prod
#print axioms integral_mul_of_dependsOutside
#print axioms integral_polymerDensity
#print axioms integral_mul_polymerDensity

end Mettapedia.Combinatorics.PolymerGas

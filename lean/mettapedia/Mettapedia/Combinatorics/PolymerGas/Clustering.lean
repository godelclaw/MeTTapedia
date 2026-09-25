import Mettapedia.Combinatorics.PolymerGas.Measure
import Mettapedia.Combinatorics.PolymerGas.Decay

/-!
# Polymer gases: expectations and the truncated two-point function

For a polymer representation over a product reference measure
(`PolymerGas.Measure`), the expectation of a function of the configuration is its
integral against the polymer density divided by the partition function of the
integrated gas (`expectation`).  The expectation of an observable `F` on a block
set `S` expands over the compatible families `Γ` of polymers meeting `S`: each
contributes its weight `∫ F · ∏_{γ ∈ Γ} K γ` times `Z(Λ ∖ B)/Z(Λ)`, where `B` is the
set of polymers meeting `S ∪ ⋃ Γ` (`expectation_eq_sum`).

Under Dobrushin's criterion for the integrated gas, removing a set `A` of
polymers changes the expectation of `F` by at most a sum over such families, in
which families avoiding `A` contribute the influence weights of the polymers
meeting `S ∪ ⋃ Γ` for any supersolution of the influence recursion for removing
`A` (`norm_expectation_sdiff_sub_le`).  The truncated two-point function
`E[F₁ F₂] - E[F₁] E[F₂]` of observables on `S₁` and `S₂` expands over the families
`Γ` meeting `S₁`: a family whose union with `S₁` misses `S₂` contributes its weight
times `Z(Λ ∖ B)/Z(Λ)` times the change of `E[F₂]` when the polymers `B` meeting
`S₁ ∪ ⋃ Γ` are removed, and the remaining families contribute a bridging term
(`truncated_eq_sum`), which is bounded explicitly (`norm_bridgeTerm_le`).
-/

set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace Mettapedia.Combinatorics.PolymerGas

variable {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [MeasurableSpace E] [Nonempty E]
variable (ν₀ : Measure E) [IsProbabilityMeasure ν₀]

omit [Fintype X] [Nonempty E] in
theorem avoiding_eq_sdiff_meeting (Λ : Finset (Finset X)) (Y : Finset X) :
    avoiding Λ Y = Λ \ meeting Λ Y := by
  ext γ
  simp only [avoiding, meeting, mem_filter, mem_sdiff, not_and, not_not]
  tauto

omit [Fintype X] [Nonempty E] in
theorem meeting_sdiff (Λ A : Finset (Finset X)) (S : Finset X) :
    meeting (Λ \ A) S = meeting Λ S \ A := by
  ext γ
  simp only [meeting, mem_filter, mem_sdiff]
  tauto

omit [Fintype X] [Nonempty E] in
theorem sdiff_sdiff_meeting (Λ A : Finset (Finset X)) (Y : Finset X) :
    (Λ \ A) \ meeting (Λ \ A) Y = (Λ \ A) \ meeting Λ Y := by
  ext γ
  simp only [meeting, mem_filter, mem_sdiff]
  tauto

/-- The expectation of a function of the configuration in the polymer measure of
`Λ`: the integral against the polymer density, normalized by its integral. -/
def expectation (G : (X → E) → ℂ) (K : ∀ S : Finset X, (S → E) → ℂ)
    (Λ : Finset (Finset X)) : ℂ :=
  (∫ ω, G ω * polymerDensity K Λ ω ∂(Measure.pi fun _ : X => ν₀)) /
    partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ

/-- The weight of a family `Γ` of polymers in the expansion of the expectation of
an observable `F` of the configuration on `S`. -/
def familyWeight (S : Finset X) (F : (S → E) → ℂ) (K : ∀ S : Finset X, (S → E) → ℂ)
    (Γ : Finset (Finset X)) : ℂ :=
  ∫ ω, F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω) ∂(Measure.pi fun _ : X => ν₀)

omit [Nonempty E] in
theorem norm_familyWeight_le (S : Finset X) (F : (S → E) → ℂ) (CF : ℝ)
    (hFb : ∀ v, ‖F v‖ ≤ CF) (hCF : 0 ≤ CF) (K : ∀ S : Finset X, (S → E) → ℂ)
    (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S) (hkn : ∀ S, 0 ≤ k S)
    (Γ : Finset (Finset X)) :
    ‖familyWeight ν₀ S F K Γ‖ ≤ CF * ∏ γ ∈ Γ, k γ := by
  unfold familyWeight
  have hbound : ∀ ω : X → E,
      ‖F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω)‖ ≤ CF * ∏ γ ∈ Γ, k γ := by
    intro ω
    rw [norm_mul, norm_prod]
    exact mul_le_mul (hFb _) (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      fun γ _ => hk γ _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hCF
  calc ‖∫ ω, F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω) ∂(Measure.pi fun _ : X => ν₀)‖
      ≤ (CF * ∏ γ ∈ Γ, k γ) * (Measure.pi fun _ : X => ν₀).real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ hbound)
    _ = CF * ∏ γ ∈ Γ, k γ := by simp

/-- **Expansion of an expectation.**  If the integrated partition function of `Λ`
is nonzero, the expectation of an observable `F` of the configuration on `S` is a
sum over compatible families `Γ` of polymers meeting `S` of their weights times
`Z(Λ ∖ B)/Z(Λ)`, where `B` is the set of polymers meeting `S ∪ ⋃ Γ`. -/
theorem expectation_eq_sum (S : Finset X) (F : (S → E) → ℂ) (hF : Measurable F)
    (CF : ℝ) (hFb : ∀ v, ‖F v‖ ≤ CF)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (Λ : Finset (Finset X)) :
    expectation ν₀ (fun ω => F (restrictTo S ω)) K Λ = ∑ Γ ∈ (meeting Λ S).powerset,
      if IsCompatible (overlapGraph X) Γ then
        familyWeight ν₀ S F K Γ *
          sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ
            (meeting Λ (S ∪ Γ.biUnion id))
      else 0 := by
  unfold expectation
  rw [integral_mul_polymerDensity ν₀ S F hF CF hFb K hK k hk Λ, sum_div]
  apply sum_congr rfl
  intro Γ _
  split_ifs
  · rw [sdiffRatio, avoiding_eq_sdiff_meeting, familyWeight, mul_div_assoc]
  · simp

/-- **Removing polymers changes an expectation by a controlled amount.**  Under
Dobrushin's criterion for the integrated gas, if `Φ` is a supersolution of the
influence recursion for removing `A`, the expectation of an observable `F` on `S`
changes by at most a sum over families `Γ` of polymers meeting `S`: families
avoiding `A` contribute the influence weights of the polymers meeting
`S ∪ ⋃ Γ`, families meeting `A` contribute fully. -/
theorem norm_expectation_sdiff_sub_le (S : Finset X) (F : (S → E) → ℂ) (hF : Measurable F)
    (CF : ℝ) (hFb : ∀ v, ‖F v‖ ≤ CF)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) {c : Finset X → ℝ}
    (hD : DobrushinCondition (overlapGraph X) (integratedActivity ν₀ K) c)
    (A : Finset (Finset X)) {Φ : Finset X → ℝ}
    (hΦ : IsInfluenceSupersolution (G := overlapGraph X) (c := c) A Φ)
    (Λ : Finset (Finset X)) :
    ‖expectation ν₀ (fun ω => F (restrictTo S ω)) K (Λ \ A) -
        expectation ν₀ (fun ω => F (restrictTo S ω)) K Λ‖ ≤
      ∑ Γ ∈ (meeting Λ S).powerset,
        CF * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ meeting Λ (S ∪ Γ.biUnion id), c b) *
          (if Disjoint Γ A then
            ∑ b ∈ meeting Λ (S ∪ Γ.biUnion id), influenceWeight A c Φ b else 1) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hCF : 0 ≤ CF := (norm_nonneg _).trans (hFb fun _ => e₀)
  have hkn : ∀ S, 0 ≤ k S := activityBound_nonneg hk
  set M := meeting Λ S with hMdef
  set w := integratedActivity ν₀ K
  rw [expectation_eq_sum ν₀ S F hF CF hFb K hK k hk (Λ \ A),
    expectation_eq_sum ν₀ S F hF CF hFb K hK k hk Λ, meeting_sdiff]
  have hext : ∑ Γ ∈ (M \ A).powerset, (if IsCompatible (overlapGraph X) Γ then
        familyWeight ν₀ S F K Γ *
          sdiffRatio (overlapGraph X) w (Λ \ A) (meeting (Λ \ A) (S ∪ Γ.biUnion id))
        else 0) =
      ∑ Γ ∈ M.powerset, if Disjoint Γ A then (if IsCompatible (overlapGraph X) Γ then
        familyWeight ν₀ S F K Γ *
          sdiffRatio (overlapGraph X) w (Λ \ A) (meeting Λ (S ∪ Γ.biUnion id))
        else 0) else 0 := by
    rw [← Finset.sum_filter (p := fun Γ => Disjoint Γ A)]
    have hfilt : M.powerset.filter (fun Γ => Disjoint Γ A) = (M \ A).powerset := by
      ext Γ
      simp only [mem_filter, mem_powerset, subset_sdiff]
    rw [hfilt]
    apply sum_congr rfl
    intro Γ _
    unfold sdiffRatio
    rw [sdiff_sdiff_meeting]
  rw [hext, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun Γ _ => ?_)
  set B := meeting Λ (S ∪ Γ.biUnion id)
  have hbnd_nonneg : 0 ≤ CF * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ B, c b) *
      (if Disjoint Γ A then ∑ b ∈ B, influenceWeight A c Φ b else 1) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hCF (Finset.prod_nonneg fun γ _ => hkn γ))
      (Real.exp_pos _).le) ?_
    split_ifs
    · exact sum_nonneg fun b _ => influenceWeight_nonneg hD.nonneg hΦ.1 b
    · norm_num
  have ha := norm_familyWeight_le ν₀ S F CF hFb hCF K k hk hkn Γ
  have hs := norm_sdiffRatio_le hD Λ B
  by_cases hc : IsCompatible (overlapGraph X) Γ
  · by_cases hdA : Disjoint Γ A
    · simp only [hc, hdA, ↓reduceIte]
      have hinf : ∀ T' ⊆ Λ, ∀ s, s ∉ A →
          ‖removalRatio (overlapGraph X) w T' s - removalRatio (overlapGraph X) w (T' \ A) s‖ ≤
            Φ s :=
        fun T' _ s hs => norm_removalRatio_sub_le_of_supersolution hD hΦ T' s hs
      have hdiff := norm_sdiffRatio_sub_le hD hΦ.1 hinf B
      rw [← mul_sub, norm_mul, norm_sub_rev]
      calc ‖familyWeight ν₀ S F K Γ‖ *
            ‖sdiffRatio (overlapGraph X) w Λ B - sdiffRatio (overlapGraph X) w (Λ \ A) B‖
          ≤ (CF * ∏ γ ∈ Γ, k γ) *
              (Real.exp (∑ u ∈ B, c u) * ∑ b ∈ B, influenceWeight A c Φ b) :=
            mul_le_mul ha hdiff (norm_nonneg _)
              (mul_nonneg hCF (Finset.prod_nonneg fun γ _ => hkn γ))
        _ = CF * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ B, c b) *
              ∑ b ∈ B, influenceWeight A c Φ b := by ring
    · simp only [hc, hdA, ↓reduceIte, zero_sub, norm_neg, mul_one]
      rw [norm_mul]
      calc ‖familyWeight ν₀ S F K Γ‖ * ‖sdiffRatio (overlapGraph X) w Λ B‖
          ≤ (CF * ∏ γ ∈ Γ, k γ) * Real.exp (∑ u ∈ B, c u) :=
            mul_le_mul ha hs (norm_nonneg _)
              (mul_nonneg hCF (Finset.prod_nonneg fun γ _ => hkn γ))
        _ = CF * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ B, c b) := by ring
  · simp only [hc, ↓reduceIte, ite_self, sub_self, norm_zero]
    exact hbnd_nonneg

/-! ## The truncated two-point function -/

/-- Integrating the decomposition of the density along `S` against any bounded
measurable observable. -/
theorem integral_mul_polymerDensity_eq_sum_meeting (G : (X → E) → ℂ) (hG : Measurable G)
    (CG : ℝ) (hGb : ∀ ω, ‖G ω‖ ≤ CG)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (Λ : Finset (Finset X)) (S : Finset X) :
    ∫ ω, G ω * polymerDensity K Λ ω ∂(Measure.pi fun _ : X => ν₀) =
      ∑ Γ ∈ (meeting Λ S).powerset,
        if IsCompatible (overlapGraph X) Γ then
          ∫ ω, G ω * ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
            polymerDensity K (avoiding Λ (S ∪ Γ.biUnion id)) ω) ∂(Measure.pi fun _ : X => ν₀)
        else 0 := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hCG : 0 ≤ CG := (norm_nonneg _).trans (hGb fun _ => e₀)
  have hkn : ∀ S, 0 ≤ k S := activityBound_nonneg hk
  simp_rw [polymerDensity_eq_sum_meeting K Λ S, mul_sum]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro Γ _
    split_ifs <;> simp
  · intro Γ _
    split_ifs
    · refine Integrable.of_bound
        (hG.mul ((Finset.measurable_prod _ fun γ _ =>
          (hK γ).comp (measurable_restrictTo γ)).mul
            (measurable_polymerDensity K hK _))).aestronglyMeasurable
        (CG * ((∏ γ ∈ Γ, k γ) * ∑ I ∈ (avoiding Λ (S ∪ Γ.biUnion id)).powerset,
          ∏ γ ∈ I, k γ)) (ae_of_all _ fun ω => ?_)
      rw [norm_mul, norm_mul, norm_prod]
      exact mul_le_mul (hGb _) (mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        fun γ _ => hk γ _) (norm_polymerDensity_le K k hk _ ω) (norm_nonneg _)
        (Finset.prod_nonneg fun γ _ => hkn γ)) (by positivity) hCG
    · simp

/-- The function of the configuration on `S ∪ ⋃ Γ` given by an observable on `S`
times the activities of the polymers of `Γ`. -/
def familyObservable (S : Finset X) (F : (S → E) → ℂ) (K : ∀ S : Finset X, (S → E) → ℂ)
    (Γ : Finset (Finset X)) : ((S ∪ Γ.biUnion id : Finset X) → E) → ℂ := fun v =>
  F (fun i => v ⟨i.1, mem_union_left _ i.2⟩) *
    ∏ γ ∈ Γ.attach, K γ.1 fun i =>
      v ⟨i.1, mem_union_right _ (mem_biUnion.mpr ⟨γ.1, γ.2, i.2⟩)⟩

omit [Fintype X] [Nonempty E] in
theorem familyObservable_restrictTo (S : Finset X) (F : (S → E) → ℂ)
    (K : ∀ S : Finset X, (S → E) → ℂ) (Γ : Finset (Finset X)) (ω : X → E) :
    familyObservable S F K Γ (restrictTo (S ∪ Γ.biUnion id) ω) =
      F (restrictTo S ω) * ∏ γ ∈ Γ, K γ (restrictTo γ ω) := by
  unfold familyObservable
  rw [← Finset.prod_attach Γ]
  rfl

omit [Fintype X] [Nonempty E] in
theorem measurable_familyObservable (S : Finset X) (F : (S → E) → ℂ) (hF : Measurable F)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S))
    (Γ : Finset (Finset X)) : Measurable (familyObservable S F K Γ) :=
  (hF.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).mul
    (Finset.measurable_prod _ fun γ _ =>
      (hK γ.1).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _))

omit [Fintype X] [Nonempty E] [MeasurableSpace E] in
theorem norm_familyObservable_le (S : Finset X) (F : (S → E) → ℂ) (CF : ℝ)
    (hFb : ∀ v, ‖F v‖ ≤ CF) (hCF : 0 ≤ CF) (K : ∀ S : Finset X, (S → E) → ℂ)
    (k : Finset X → ℝ) (hk : ∀ S v, ‖K S v‖ ≤ k S) (Γ : Finset (Finset X))
    (v : (S ∪ Γ.biUnion id : Finset X) → E) :
    ‖familyObservable S F K Γ v‖ ≤ CF * ∏ γ ∈ Γ, k γ := by
  unfold familyObservable
  rw [norm_mul, norm_prod, ← Finset.prod_attach Γ k]
  exact mul_le_mul (hFb _) (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    fun γ _ => hk γ.1 _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hCF

/-- For a family `Γ` of polymers meeting `S₁` whose union with `S₁` misses `S₂`,
the family's contribution to the joint integral factors into its weight times
the integral of `F₂` against the density of the polymers avoiding it. -/
theorem integral_joint_family_of_disjoint (S₁ S₂ : Finset X) (F₁ : (S₁ → E) → ℂ)
    (hF₁ : Measurable F₁) (F₂ : (S₂ → E) → ℂ) (hF₂ : Measurable F₂)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S))
    (Λ Γ : Finset (Finset X)) (hdisj : Disjoint (S₁ ∪ Γ.biUnion id) S₂) :
    ∫ ω, (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) *
        ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
          polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω) ∂(Measure.pi fun _ : X => ν₀) =
      familyWeight ν₀ S₁ F₁ K Γ *
        ∫ ω, F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω
          ∂(Measure.pi fun _ : X => ν₀) := by
  have hfun : (fun ω => (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) *
      ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω)) =
      fun ω => familyObservable S₁ F₁ K Γ (restrictTo (S₁ ∪ Γ.biUnion id) ω) *
        (F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω) := by
    funext ω
    rw [familyObservable_restrictTo]
    ring
  have hdep : DependsOutside (S₁ ∪ Γ.biUnion id)
      (fun ω => F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω) := by
    intro ω ω' h
    have h2 : restrictTo S₂ ω = restrictTo S₂ ω' := by
      funext i
      exact h i fun hiY => Finset.disjoint_left.mp hdisj hiY i.2
    show F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω =
      F₂ (restrictTo S₂ ω') * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω'
    rw [h2, dependsOutside_polymerDensity_avoiding K Λ _ ω ω' h]
  have hGmeas : Measurable
      (fun ω => F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω) :=
    (hF₂.comp (measurable_restrictTo S₂)).mul (measurable_polymerDensity K hK _)
  rw [hfun, integral_mul_of_dependsOutside ν₀ (S₁ ∪ Γ.biUnion id) _
    (measurable_familyObservable S₁ F₁ hF₁ K hK Γ) _ hGmeas hdep]
  simp_rw [familyObservable_restrictTo]
  rfl

/-- **Decomposition of the truncated two-point function.**  Expanding both
`E[F₁ F₂]` and `E[F₁]` over the compatible families `Γ` of polymers meeting `S₁`,
a family whose union with `S₁` misses `S₂` contributes its weight times
`Z(Λ ∖ B)/Z(Λ)` times the change of `E[F₂]` when the polymers `B` meeting
`S₁ ∪ ⋃ Γ` are removed; the remaining families reach `S₂` and contribute
`bridgeTerm`. -/
def bridgeTerm (S₁ S₂ : Finset X) (F₁ : (S₁ → E) → ℂ) (F₂ : (S₂ → E) → ℂ)
    (K : ∀ S : Finset X, (S → E) → ℂ) (Λ Γ : Finset (Finset X)) : ℂ :=
  (∫ ω, (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) *
      ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) *
        polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω) ∂(Measure.pi fun _ : X => ν₀)) /
      partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ -
    familyWeight ν₀ S₁ F₁ K Γ *
      sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ (meeting Λ (S₁ ∪ Γ.biUnion id)) *
      expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ

theorem truncated_eq_sum (S₁ S₂ : Finset X) (F₁ : (S₁ → E) → ℂ) (hF₁ : Measurable F₁)
    (C₁ : ℝ) (hF₁b : ∀ v, ‖F₁ v‖ ≤ C₁) (F₂ : (S₂ → E) → ℂ) (hF₂ : Measurable F₂)
    (C₂ : ℝ) (hF₂b : ∀ v, ‖F₂ v‖ ≤ C₂)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) (Λ : Finset (Finset X))
    (hZ : ∀ Λ' : Finset (Finset X),
      partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ' ≠ 0) :
    expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) K Λ -
        expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω)) K Λ *
          expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ =
      ∑ Γ ∈ (meeting Λ S₁).powerset,
        if IsCompatible (overlapGraph X) Γ then
          (if Disjoint (S₁ ∪ Γ.biUnion id) S₂ then
            familyWeight ν₀ S₁ F₁ K Γ *
              sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ
                (meeting Λ (S₁ ∪ Γ.biUnion id)) *
              (expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K
                  (Λ \ meeting Λ (S₁ ∪ Γ.biUnion id)) -
                expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ)
          else bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ)
        else 0 := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hF₁b fun _ => e₀)
  have hZΛ := hZ Λ
  have hG12b : ∀ ω : X → E, ‖F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)‖ ≤ C₁ * C₂ := by
    intro ω
    rw [norm_mul]
    exact mul_le_mul (hF₁b _) (hF₂b _) (norm_nonneg _) hC₁
  have hG12m : Measurable fun ω : X → E => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω) :=
    (hF₁.comp (measurable_restrictTo S₁)).mul (hF₂.comp (measurable_restrictTo S₂))
  have hjoint := integral_mul_polymerDensity_eq_sum_meeting ν₀
    (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) hG12m (C₁ * C₂) hG12b
    K hK k hk Λ S₁
  have hone := integral_mul_polymerDensity ν₀ S₁ F₁ hF₁ C₁ hF₁b K hK k hk Λ
  generalize hE₂ : expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ = E₂
  have hLHS : expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) K Λ -
      expectation ν₀ (fun ω => F₁ (restrictTo S₁ ω)) K Λ * E₂ =
      (∫ ω, (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) * polymerDensity K Λ ω
          ∂(Measure.pi fun _ : X => ν₀) -
        (∫ ω, F₁ (restrictTo S₁ ω) * polymerDensity K Λ ω ∂(Measure.pi fun _ : X => ν₀)) *
          E₂) / partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ := by
    unfold expectation
    field_simp
  rw [hLHS, hjoint, hone, sum_mul, ← sum_sub_distrib, sum_div]
  apply sum_congr rfl
  intro Γ _
  split_ifs with hc hdisj
  · have hZY := hZ (avoiding Λ (S₁ ∪ Γ.biUnion id))
    rw [integral_joint_family_of_disjoint ν₀ S₁ S₂ F₁ hF₁ F₂ hF₂ K hK Λ Γ hdisj]
    have hE : ∫ ω, F₂ (restrictTo S₂ ω) * polymerDensity K (avoiding Λ (S₁ ∪ Γ.biUnion id)) ω
        ∂(Measure.pi fun _ : X => ν₀) =
        partitionFunction (overlapGraph X) (integratedActivity ν₀ K)
            (avoiding Λ (S₁ ∪ Γ.biUnion id)) *
          expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K (avoiding Λ (S₁ ∪ Γ.biUnion id)) := by
      unfold expectation
      field_simp
    rw [hE, sdiffRatio, ← avoiding_eq_sdiff_meeting]
    unfold familyWeight
    field_simp
  · unfold bridgeTerm
    rw [sdiffRatio, ← avoiding_eq_sdiff_meeting, hE₂]
    unfold familyWeight
    field_simp
  · simp

/-! ## Bounds on the pieces of the truncated two-point function -/

omit [Fintype X] [Nonempty E] in
theorem avoiding_avoiding_of_subset (Λ : Finset (Finset X)) {Y V : Finset X} (hYV : Y ⊆ V) :
    avoiding (avoiding Λ Y) V = avoiding Λ V := by
  ext γ
  simp only [avoiding, mem_filter]
  constructor
  · rintro ⟨⟨hγ, _⟩, hV⟩
    exact ⟨hγ, hV⟩
  · rintro ⟨hγ, hV⟩
    exact ⟨⟨hγ, disjoint_of_subset_right hYV hV⟩, hV⟩

omit [Fintype X] [Nonempty E] in
theorem meeting_avoiding_subset (Λ : Finset (Finset X)) (Y W : Finset X) :
    meeting (avoiding Λ Y) W ⊆ meeting Λ W := by
  intro γ hγ
  simp only [meeting, avoiding, mem_filter] at hγ ⊢
  exact ⟨hγ.1.1, hγ.2⟩

/-- Under Dobrushin's criterion, the expectation of an observable on `S` is bounded
by a sum over families of polymers meeting `S`. -/
theorem norm_expectation_le (S : Finset X) (F : (S → E) → ℂ) (hF : Measurable F)
    (CF : ℝ) (hFb : ∀ v, ‖F v‖ ≤ CF)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) {c : Finset X → ℝ}
    (hD : DobrushinCondition (overlapGraph X) (integratedActivity ν₀ K) c)
    (Λ : Finset (Finset X)) :
    ‖expectation ν₀ (fun ω => F (restrictTo S ω)) K Λ‖ ≤
      ∑ Γ ∈ (meeting Λ S).powerset,
        CF * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ meeting Λ (S ∪ Γ.biUnion id), c b) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hCF : 0 ≤ CF := (norm_nonneg _).trans (hFb fun _ => e₀)
  have hkn : ∀ S, 0 ≤ k S := activityBound_nonneg hk
  rw [expectation_eq_sum ν₀ S F hF CF hFb K hK k hk Λ]
  refine (norm_sum_le _ _).trans (sum_le_sum fun Γ _ => ?_)
  split_ifs
  · rw [norm_mul]
    exact mul_le_mul (norm_familyWeight_le ν₀ S F CF hFb hCF K k hk hkn Γ)
      (norm_sdiffRatio_le hD Λ _) (norm_nonneg _)
      (mul_nonneg hCF (Finset.prod_nonneg fun γ _ => hkn γ))
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg hCF (Finset.prod_nonneg fun γ _ => hkn γ))
      (Real.exp_pos _).le

/-- **The bridging term is bounded** by sums over families of polymers meeting
`S₁ ∪ S₂ ∪ ⋃ Γ` and `S₂`, times the activity product of `Γ`. -/
theorem norm_bridgeTerm_le (S₁ S₂ : Finset X) (F₁ : (S₁ → E) → ℂ) (hF₁ : Measurable F₁)
    (C₁ : ℝ) (hF₁b : ∀ v, ‖F₁ v‖ ≤ C₁) (F₂ : (S₂ → E) → ℂ) (hF₂ : Measurable F₂)
    (C₂ : ℝ) (hF₂b : ∀ v, ‖F₂ v‖ ≤ C₂)
    (K : ∀ S : Finset X, (S → E) → ℂ) (hK : ∀ S, Measurable (K S)) (k : Finset X → ℝ)
    (hk : ∀ S v, ‖K S v‖ ≤ k S) {c : Finset X → ℝ}
    (hD : DobrushinCondition (overlapGraph X) (integratedActivity ν₀ K) c)
    (Λ Γ : Finset (Finset X)) :
    ‖bridgeTerm ν₀ S₁ S₂ F₁ F₂ K Λ Γ‖ ≤
      C₁ * C₂ * (∏ γ ∈ Γ, k γ) *
        (∑ Γ' ∈ (meeting Λ ((S₁ ∪ S₂) ∪ Γ.biUnion id)).powerset, (∏ γ ∈ Γ', k γ) *
          Real.exp (∑ b ∈ meeting Λ (((S₁ ∪ S₂) ∪ Γ.biUnion id) ∪ Γ'.biUnion id), c b)) +
      C₁ * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ meeting Λ (S₁ ∪ Γ.biUnion id), c b) *
        ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
          C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b) := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hF₁b fun _ => e₀)
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hF₂b fun _ => e₀)
  have hkn : ∀ S, 0 ≤ k S := activityBound_nonneg hk
  have hZΛ := partitionFunction_ne_zero hD Λ
  set Y : Finset X := S₁ ∪ Γ.biUnion id with hYdef
  set W : Finset X := (S₁ ∪ S₂) ∪ Γ.biUnion id with hWdef
  have hYW : Y ⊆ W := by
    intro i hi
    simp only [hYdef, hWdef, mem_union] at hi ⊢
    tauto
  -- the joint observable on `S₁ ∪ S₂` and its family observable on `W`
  let F₁₂ : ((S₁ ∪ S₂ : Finset X) → E) → ℂ := fun v =>
    F₁ (fun i => v ⟨i.1, mem_union_left _ i.2⟩) * F₂ (fun i => v ⟨i.1, mem_union_right _ i.2⟩)
  have hF₁₂ : Measurable F₁₂ :=
    (hF₁.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).mul
      (hF₂.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _))
  have hF₁₂b : ∀ v, ‖F₁₂ v‖ ≤ C₁ * C₂ := fun v => by
    simp only [F₁₂, norm_mul]
    exact mul_le_mul (hF₁b _) (hF₂b _) (norm_nonneg _) hC₁
  let H := familyObservable (S₁ ∪ S₂) F₁₂ K Γ
  have hH : Measurable H := measurable_familyObservable (S₁ ∪ S₂) F₁₂ hF₁₂ K hK Γ
  have hHb : ∀ v, ‖H v‖ ≤ C₁ * C₂ * ∏ γ ∈ Γ, k γ := fun v =>
    norm_familyObservable_le (S₁ ∪ S₂) F₁₂ (C₁ * C₂) hF₁₂b (mul_nonneg hC₁ hC₂) K k hk Γ v
  have hHW : ∀ ω, H (restrictTo W ω) =
      (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) * ∏ γ ∈ Γ, K γ (restrictTo γ ω) := by
    intro ω
    exact familyObservable_restrictTo (S₁ ∪ S₂) F₁₂ K Γ ω
  -- first piece: condition the joint integral on `W` in the gas avoiding `Y`
  have hI : ∫ ω, (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) *
      ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) * polymerDensity K (avoiding Λ Y) ω)
        ∂(Measure.pi fun _ : X => ν₀) =
      ∫ ω, H (restrictTo W ω) * polymerDensity K (avoiding Λ Y) ω
        ∂(Measure.pi fun _ : X => ν₀) := by
    congr 1
    funext ω
    rw [hHW]
    ring
  have hexp := integral_mul_polymerDensity ν₀ W H hH (C₁ * C₂ * ∏ γ ∈ Γ, k γ) hHb K hK k hk
    (avoiding Λ Y)
  have hpiece1 : ‖(∫ ω, (F₁ (restrictTo S₁ ω) * F₂ (restrictTo S₂ ω)) *
      ((∏ γ ∈ Γ, K γ (restrictTo γ ω)) * polymerDensity K (avoiding Λ Y) ω)
        ∂(Measure.pi fun _ : X => ν₀)) /
      partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ‖ ≤
      C₁ * C₂ * (∏ γ ∈ Γ, k γ) *
        ∑ Γ' ∈ (meeting Λ W).powerset, (∏ γ ∈ Γ', k γ) *
          Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b) := by
    rw [hI, hexp, norm_div, div_le_iff₀ (norm_pos_iff.mpr hZΛ), mul_sum, sum_mul]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ Γ' : Finset (Finset X),
        ‖(if IsCompatible (overlapGraph X) Γ' then
            (∫ ω, H (restrictTo W ω) * ∏ γ ∈ Γ', K γ (restrictTo γ ω)
                ∂(Measure.pi fun _ : X => ν₀)) *
              partitionFunction (overlapGraph X) (integratedActivity ν₀ K)
                (avoiding (avoiding Λ Y) (W ∪ Γ'.biUnion id))
          else 0)‖ ≤
        C₁ * C₂ * (∏ γ ∈ Γ, k γ) * ((∏ γ ∈ Γ', k γ) *
          Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b)) *
          ‖partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ‖ := by
      intro Γ'
      have hbnd : 0 ≤ C₁ * C₂ * (∏ γ ∈ Γ, k γ) * ((∏ γ ∈ Γ', k γ) *
          Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b)) *
          ‖partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ‖ := by
        have := Finset.prod_nonneg fun γ (_ : γ ∈ Γ) => hkn γ
        have := Finset.prod_nonneg fun γ (_ : γ ∈ Γ') => hkn γ
        positivity
      split_ifs
      · rw [norm_mul, avoiding_avoiding_of_subset Λ (hYW.trans subset_union_left),
          avoiding_eq_sdiff_meeting]
        have hw := norm_familyWeight_le ν₀ W H (C₁ * C₂ * ∏ γ ∈ Γ, k γ) hHb
          (mul_nonneg (mul_nonneg hC₁ hC₂) (Finset.prod_nonneg fun γ _ => hkn γ)) K k hk hkn Γ'
        have hz := norm_partitionFunction_sdiff_le_of_dobrushin hD Λ
          (meeting Λ (W ∪ Γ'.biUnion id))
        unfold familyWeight at hw
        calc _ ≤ (C₁ * C₂ * (∏ γ ∈ Γ, k γ) * ∏ γ ∈ Γ', k γ) *
              (Real.exp (∑ b ∈ meeting Λ (W ∪ Γ'.biUnion id), c b) *
                ‖partitionFunction (overlapGraph X) (integratedActivity ν₀ K) Λ‖) :=
              mul_le_mul hw hz (norm_nonneg _)
                (mul_nonneg (mul_nonneg (mul_nonneg hC₁ hC₂)
                  (Finset.prod_nonneg fun γ _ => hkn γ)) (Finset.prod_nonneg fun γ _ => hkn γ))
          _ = _ := by ring
      · rw [norm_zero]
        exact hbnd
    refine (sum_le_sum fun Γ' _ => hterm Γ').trans ?_
    refine sum_le_sum_of_subset_of_nonneg (powerset_mono.mpr
      (meeting_avoiding_subset Λ Y W)) fun Γ' _ _ => ?_
    have := Finset.prod_nonneg fun γ (_ : γ ∈ Γ) => hkn γ
    have := Finset.prod_nonneg fun γ (_ : γ ∈ Γ') => hkn γ
    positivity
  -- second piece
  have hpiece2 : ‖familyWeight ν₀ S₁ F₁ K Γ *
      sdiffRatio (overlapGraph X) (integratedActivity ν₀ K) Λ (meeting Λ Y) *
      expectation ν₀ (fun ω => F₂ (restrictTo S₂ ω)) K Λ‖ ≤
      C₁ * (∏ γ ∈ Γ, k γ) * Real.exp (∑ b ∈ meeting Λ Y, c b) *
        ∑ Γ₂ ∈ (meeting Λ S₂).powerset,
          C₂ * (∏ γ ∈ Γ₂, k γ) * Real.exp (∑ b ∈ meeting Λ (S₂ ∪ Γ₂.biUnion id), c b) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (norm_familyWeight_le ν₀ S₁ F₁ C₁ hF₁b hC₁ K k hk hkn Γ)
      (norm_sdiffRatio_le hD Λ _) (norm_nonneg _)
      (mul_nonneg hC₁ (Finset.prod_nonneg fun γ _ => hkn γ)))
      (norm_expectation_le ν₀ S₂ F₂ hF₂ C₂ hF₂b K hK k hk hD Λ) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC₁ (Finset.prod_nonneg fun γ _ => hkn γ)) (Real.exp_pos _).le)
  unfold bridgeTerm
  exact (norm_sub_le _ _).trans (add_le_add hpiece1 hpiece2)

#print axioms expectation_eq_sum
#print axioms norm_expectation_sdiff_sub_le
#print axioms truncated_eq_sum
#print axioms norm_bridgeTerm_le

end Mettapedia.Combinatorics.PolymerGas

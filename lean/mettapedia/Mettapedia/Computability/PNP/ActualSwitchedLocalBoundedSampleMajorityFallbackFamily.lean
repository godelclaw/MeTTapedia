import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces

/-!
# PNP bounded sample-majority fallback-family interfaces

Structured fallback-family interfaces, radius-cover characterizations, and the generic fallback-code lower bound.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with a fallback chosen from a structured fallback family. -/
noncomputable def boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
    (FallbackIndex : Type v)
    (Z : Type v) (k sampleBound : ℕ)
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback (fallback index.1) index.2.1 u
  output := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback (fallback index.1) index.2.1 u
  output_eq_local := by
    intro index u
    rfl

/-- The structured fallback-family endpoint with the fallback family indexed by
`fallbackBits` Boolean bits.  The internal index is universe-lifted so the
construction remains available for arbitrary finite hidden alphabets `Z`. -/
noncomputable def boundedSamplePluginMajorityWithBitFallbackFamilyActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound fallbackBits : ℕ)
    (fallback : BitCode fallbackBits → ExactVisibleRule Z k) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackFamilyIndex
        (ULift.{v} (BitCode fallbackBits))
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) :=
  boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
    (ULift.{v} (BitCode fallbackBits)) Z k sampleBound
    (fun code => fallback code.down)

/-- For a structured fallback family, bounded samples can only change the
chosen fallback rule on sampled exact-visible inputs. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (index :
      BoundedSampleFallbackFamilyIndex
        FallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.disagreementSupport (fallback index.1)
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u)).card ≤
        sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.disagreementSupport_predictWithFallback_card_le_bound
      (fallback index.1) (sample := index.2)

/-- If the structured fallback family selects a rule and the bounded sample is
empty, the plug-in predictor is exactly that fallback rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) (code : FallbackIndex) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict
        (code, ⟨[], by simp⟩) =
      fallback code := by
  classical
  funext u
  simp [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- A bounded-sample structured fallback endpoint is already full-rule
expressive whenever the fallback family itself is full-rule expressive.  The
sample bound is irrelevant: the empty sample leaves the selected fallback
unchanged. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj : Function.Surjective fallback) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  intro rule
  rcases hsurj rule with ⟨code, hcode⟩
  refine ⟨(code, ⟨[], by simp⟩), ?_⟩
  simpa [hcode] using
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback code

/-- With zero sampled overrides, a structured fallback endpoint is full-rule
expressive exactly when the fallback family itself is full-rule expressive. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_zeroSample_surjective_iff_fallback_surjective
    {FallbackIndex : Type v} {Z : Type v} {k : ℕ}
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k 0 fallback).predictorFamily.predict ↔
      Function.Surjective fallback := by
  classical
  constructor
  · intro hsurj rule
    rcases hsurj rule with ⟨index, hindex⟩
    refine ⟨index.1, ?_⟩
    have hsample : index.2.1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      exact Nat.eq_zero_of_le_zero index.2.2
    funext u
    have hu := congrFun hindex u
    simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily, hsample] using hu
  · intro hfallback
    exact
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_fallback_surjective
        (Z := Z) (k := k) (sampleBound := 0) fallback hfallback

/-- Thus a structured fallback family can realize a target rule only if some
fallback code is within `sampleBound` point changes of that target. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hcard :
      ∀ code : FallbackIndex,
        sampleBound <
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card) :
    ¬ ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule := by
  classical
  rintro ⟨index, hindex⟩
  have hle :=
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
  have hsupport :
      PluginSampleMajority.disagreementSupport (fallback index.1)
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
              FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u) =
        PluginSampleMajority.disagreementSupport (fallback index.1) rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k sampleBound fallback).localRule index u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hindex u
    simp [PluginSampleMajority.disagreementSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) (hcard index.1)

/-- Every rule in the fallback-family radius cover is realized by sampling
exactly the points where it differs from the chosen fallback rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_of_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k)
    (hmem :
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound) :
    ∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule := by
  classical
  rcases
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).1 hmem with
    ⟨code, hcard⟩
  let support :=
    PluginSampleMajority.disagreementSupport (fallback code) rule
  let sample := PluginSampleMajority.supportSample support rule
  have hlen : sample.length ≤ sampleBound := by
    simpa [sample, support] using hcard
  refine ⟨⟨code, ⟨sample, hlen⟩⟩, ?_⟩
  have hoff : ∀ u : ExactVisiblePostSwitchSurface Z k,
      u ∉ support → fallback code u = rule u := by
    intro u hu
    have hnot : ¬ rule u ≠ fallback code u := by
      simpa [support] using
        mt
          ((PluginSampleMajority.mem_disagreementSupport
            (reference := fallback code) (rule := rule) (u := u)).2) hu
    exact (not_not.mp hnot).symm
  have hpredict :
      PluginSampleMajority.predictWithFallback (fallback code) sample = rule := by
    simpa [sample] using
      PluginSampleMajority.predictWithFallback_supportSample_eq_of_eq_off_support
        (fallback code) rule support hoff
  funext u
  simpa [boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using congrFun hpredict u

/-- A structured fallback family plus bounded samples realizes precisely the
finite Hamming-radius cover around its fallback codes. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (rule : ExactVisibleRule Z k) :
    (∃ index,
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict index =
        rule) ↔
      rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
  classical
  constructor
  · rintro ⟨index, hindex⟩
    have hle :=
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
    have hsupport :
        PluginSampleMajority.disagreementSupport (fallback index.1)
            (fun u : ExactVisiblePostSwitchSurface Z k =>
              (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
                FallbackIndex Z k sampleBound fallback).predictorFamily.predict index u) =
          PluginSampleMajority.disagreementSupport (fallback index.1) rule := by
      ext u
      have hu :
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
              FallbackIndex Z k sampleBound fallback).localRule index u =
            rule u := by
        simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hindex u
      simp [PluginSampleMajority.disagreementSupport, hu]
    rw [hsupport] at hle
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).2
        ⟨index.1, hle⟩
  · intro hmem
    exact
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_of_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound)
        fallback rule hmem

/-- A structured fallback family plus bounded samples is surjective precisely
when its finite Hamming-radius cover is the full exact-visible rule space. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound =
        (Finset.univ : Finset (ExactVisibleRule Z k)) := by
  classical
  constructor
  · intro hsurj
    apply Finset.eq_univ_iff_forall.mpr
    intro rule
    rcases hsurj rule with ⟨index, hindex⟩
    exact
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).1
        ⟨index, hindex⟩
  · intro hcover rule
    have hmem :
        rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
      simp [hcover]
    exact
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).2
        hmem

/-- Once the sample radius reaches the exact-visible alphabet size, any
nonempty structured fallback family becomes full-rule expressive.  This is the
sharp full-radius repair side of the bounded-sample Hamming-cover boundary. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_of_nonempty_of_surfaceCard_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Nonempty FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  intro rule
  exact
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_realizes_rule_iff_mem_fallbackFamilyRadiusCover
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback rule).2
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover_of_nonempty_of_card_le_radius
        (fallback := fallback) hbound rule)

/-- Pointwise form of the exact repair condition: surjectivity requires and is
required by every exact-visible rule lying within `sampleBound` of some
fallback code. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_forall_exists_disagreementSupport_card_le_sampleBound
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict ↔
      ∀ rule : ExactVisibleRule Z k,
        ∃ code : FallbackIndex,
          (PluginSampleMajority.disagreementSupport (fallback code) rule).card ≤
            sampleBound := by
  classical
  rw [
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback]
  constructor
  · intro hcover rule
    have hmem :
        rule ∈ PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound := by
      simp [hcover]
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).1 hmem
  · intro hforall
    apply Finset.eq_univ_iff_forall.mpr
    intro rule
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound) (rule := rule)).2
        (hforall rule)

/-- A structured fallback family plus bounded samples has an explicit finite
predictor-image cover: one radius-`sampleBound` Hamming ball around each
fallback code. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_finitePredictorCover
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.FinitePredictorCover
      (Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card) := by
  classical
  refine
    ⟨PluginSampleMajority.fallbackFamilyRadiusCover fallback sampleBound, ?_, ?_⟩
  · intro index
    have hle :=
      boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_disagreementSupport_card_le_sampleBound
        (Z := Z) (k := k) (sampleBound := sampleBound) fallback index
    exact
      (PluginSampleMajority.mem_fallbackFamilyRadiusCover
        (fallback := fallback) (radius := sampleBound)
        (rule :=
          (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
            FallbackIndex Z k sampleBound fallback).predictorFamily.predict index)).2
        ⟨index.1, hle⟩
  · exact PluginSampleMajority.fallbackFamilyRadiusCover_card_le
      fallback sampleBound

/-- If the fallback-code count times the number of possible sparse override
supports is below the full Boolean truth-table space, then the structured
fallback-family endpoint cannot realize every exact-visible rule. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_surjective_of_code_mul_smallSubsets_card_lt_boolClassifierSpace
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hcard :
      Fintype.card FallbackIndex *
          (PluginSampleMajority.smallSubsets
            (ExactVisiblePostSwitchSurface Z k) sampleBound).card <
        2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
        FallbackIndex Z k sampleBound fallback).predictorFamily.predict := by
  classical
  rcases
      PluginSampleMajority.exists_rule_forall_radius_lt_disagreementSupport_card_of_code_mul_smallSubsets_card_lt
        (U := ExactVisiblePostSwitchSurface Z k)
        fallback hcard with
    ⟨rule, hfar⟩
  intro hsurj
  rcases hsurj rule with ⟨index, hindex⟩
  exact
    boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_not_realizes_rule_of_forall_sampleBound_lt_disagreementSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound)
      fallback rule hfar ⟨index, hindex⟩

/-- Direct quantitative repair burden: if the structured fallback-family
endpoint is full-rule expressive, then fallback codes times sparse override
supports must be at least the full exact-visible Boolean truth-table count. -/
theorem boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_surjective
    {FallbackIndex : Type v} {Z : Type v} {k sampleBound : ℕ}
    [Fintype FallbackIndex] [Fintype Z]
    (fallback : FallbackIndex → ExactVisibleRule Z k)
    (hsurj :
      Function.Surjective
        (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface
          FallbackIndex Z k sampleBound fallback).predictorFamily.predict) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      Fintype.card FallbackIndex *
        (PluginSampleMajority.smallSubsets
          (ExactVisiblePostSwitchSurface Z k) sampleBound).card := by
  classical
  have hcover :=
    (boundedSamplePluginMajorityWithFallbackFamilyActualSwitchedLocalInterface_surjective_iff_fallbackFamilyRadiusCover_eq_univ
      (Z := Z) (k := k) (sampleBound := sampleBound) fallback).1 hsurj
  exact
    PluginSampleMajority.boolClassifierSpace_card_le_code_mul_smallSubsets_card_of_radiusCover_eq_univ
      (fallback := fallback) (radius := sampleBound) hcover

end Mettapedia.Computability.PNP

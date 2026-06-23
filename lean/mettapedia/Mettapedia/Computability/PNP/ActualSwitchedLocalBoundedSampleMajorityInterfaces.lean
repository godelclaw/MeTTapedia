import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics

/-!
# PNP bounded sample-majority interfaces

Actual switched-local interfaces for bounded samples, explicit defaults, and unrestricted input-dependent fallbacks.
-/

namespace Mettapedia.Computability.PNP

universe v

/-- The actual switched-local interface induced by sample-level plug-in
majority, with indices restricted to samples of length at most `sampleBound`. -/
noncomputable def boundedSamplePluginMajorityActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample.1 u
  output := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predict sample.1 u
  output_eq_local := by
    intro sample u
    rfl

/-- If the sample bound reaches the alphabet size, every Boolean lookup table
is still realized by the graph sample of that lookup table. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (rule : ExactVisibleRule Z k) :
    ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  classical
  refine ⟨⟨PluginSampleMajority.graphSample rule, ?_⟩, ?_⟩
  · rw [PluginSampleMajority.length_graphSample]
    exact hbound
  · funext u
    simp [boundedSamplePluginMajorityActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily]

/-- Bounded sample-level plug-in majority remains surjective once the bound is
at least the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) hbound rule

/-- If the sample bound is below the exact-visible alphabet size, bounded
sample-level plug-in majority is not surjective: every bounded sample omits an
input, where the tie-breaking majority predicts `true`, so the all-false rule is
not realizable. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict := by
  classical
  intro hsurj
  let allFalse : ExactVisibleRule Z k := fun _ => false
  rcases hsurj allFalse with ⟨sample, hsample⟩
  have hlen : sample.1.length < Fintype.card (ExactVisiblePostSwitchSurface Z k) :=
    lt_of_le_of_lt sample.2 hbound
  rcases PluginSampleMajority.exists_true_prediction_of_length_lt_card
      (sample := sample.1) hlen with ⟨u, hu⟩
  have hfalse :
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u = false := by
    simpa [allFalse] using congrFun hsample u
  rw [boundedSamplePluginMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] at hfalse
  simp [hu] at hfalse

/-- Exact surjectivity dichotomy for bounded sample-level plug-in majority: it
is full-rule expressive exactly when the sample bound reaches the exact-visible
alphabet size. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective_iff
    (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  constructor
  · intro hsurj
    by_contra hnot
    exact
      boundedSamplePluginMajorityActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        (Nat.lt_of_not_ge hnot) hsurj
  · intro hbound
    exact boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
      Z k sampleBound hbound

/-- Any predictor selected by bounded sample-level plug-in majority is false on
at most `sampleBound` exact-visible inputs. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.falseSupport
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample u)).card ≤ sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.falseSupport_predict_card_le_bound
      (sample := sample)

/-- Consequently, any target rule whose false-support is larger than the sample
bound is not realized by the bounded sample-level plug-in majority endpoint. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_falseSupport_card
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.falseSupport rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
          sample =
        rule := by
  classical
  rintro ⟨sample, hsample⟩
  have hle :=
    boundedSamplePluginMajorityActualSwitchedLocalInterface_falseSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) sample
  have hsupport :
      PluginSampleMajority.falseSupport
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).predictorFamily.predict
              sample u) =
        PluginSampleMajority.falseSupport rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound).localRule
            sample u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hsample u
    simp [PluginSampleMajority.falseSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) hcard

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with an explicit tie-breaking default. -/
noncomputable def boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithDefault default sample.1 u
  output := fun sample u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithDefault default sample.1 u
  output_eq_local := by
    intro sample u
    rfl

/-- If the sample bound reaches the alphabet size, explicit-default bounded
sample-level plug-in majority realizes every Boolean lookup table. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (rule : ExactVisibleRule Z k) :
    ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  classical
  refine ⟨⟨PluginSampleMajority.graphSample rule, ?_⟩, ?_⟩
  · rw [PluginSampleMajority.length_graphSample]
    exact hbound
  · funext u
    simp [boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.predictorFamily]

/-- Explicit-default bounded sample-level plug-in majority is surjective once
the sample bound reaches the exact-visible alphabet size. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z]
    (hbound : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) default hbound rule

/-- Any predictor selected by explicit-default bounded sample-level plug-in
majority differs from the default on at most `sampleBound` exact-visible inputs. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (sample :
      BoundedSampleIndex (ExactVisiblePostSwitchSurface Z k) sampleBound) :
    (PluginSampleMajority.nondefaultSupport default
      (fun u : ExactVisiblePostSwitchSurface Z k =>
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample u)).card ≤ sampleBound := by
  classical
  simpa [boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily] using
    PluginSampleMajority.nondefaultSupport_predictWithDefault_card_le_bound
      default (sample := sample)

/-- Consequently, any target rule whose nondefault support is larger than the
sample bound is not realized by the explicit-default bounded sample-level
plug-in majority endpoint. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool) (rule : ExactVisibleRule Z k)
    (hcard : sampleBound < (PluginSampleMajority.nondefaultSupport default rule).card) :
    ¬ ∃ sample,
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict sample =
        rule := by
  classical
  rintro ⟨sample, hsample⟩
  have hle :=
    boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_nondefaultSupport_card_le_sampleBound
      (Z := Z) (k := k) (sampleBound := sampleBound) default sample
  have hsupport :
      PluginSampleMajority.nondefaultSupport default
          (fun u : ExactVisiblePostSwitchSurface Z k =>
            (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
              default Z k sampleBound).predictorFamily.predict sample u) =
        PluginSampleMajority.nondefaultSupport default rule := by
    ext u
    have hu :
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
            default Z k sampleBound).localRule sample u =
          rule u := by
      simpa [ActualSwitchedLocalInterface.predictorFamily_predict] using congrFun hsample u
    simp [PluginSampleMajority.nondefaultSupport, hu]
  rw [hsupport] at hle
  exact (not_lt_of_ge hle) hcard

/-- Below the exact-visible alphabet size, no explicit-default bounded sample
endpoint is surjective: the rule constantly opposite to the default has
nondefault support equal to the whole surface. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
    {Z : Type v} {k sampleBound : ℕ} [Fintype Z]
    (default : Bool)
    (hbound : sampleBound < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
      (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
        default Z k sampleBound).predictorFamily.predict := by
  classical
  intro hsurj
  let antiDefault : ExactVisibleRule Z k := fun _ => !default
  have hcard :
      sampleBound < (PluginSampleMajority.nondefaultSupport default antiDefault).card := by
    simpa [antiDefault, PluginSampleMajority.nondefaultSupport_const_not_card] using hbound
  exact
    (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_realizes_rule_of_sampleBound_lt_nondefaultSupport_card
      (Z := Z) (k := k) (sampleBound := sampleBound) default antiDefault hcard)
      (hsurj antiDefault)

/-- Exact surjectivity dichotomy for explicit-default bounded sample-level
plug-in majority: the tie-breaking convention does not change the threshold. -/
theorem boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective_iff
    (default : Bool) (Z : Type v) (k sampleBound : ℕ) [Fintype Z] :
    Function.Surjective
        (boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface
          default Z k sampleBound).predictorFamily.predict ↔
      Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound := by
  constructor
  · intro hsurj
    by_contra hnot
    exact
      boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_not_surjective_of_sampleBound_lt_surfaceCard
        (Z := Z) (k := k) (sampleBound := sampleBound)
        default (Nat.lt_of_not_ge hnot) hsurj
  · intro hbound
    exact boundedSamplePluginMajorityWithDefaultActualSwitchedLocalInterface_surjective
      default Z k sampleBound hbound

/-- The actual switched-local interface induced by bounded sample-level
plug-in majority with an input-dependent fallback for ties.  The index carries a
fallback function over the whole exact-visible surface. -/
noncomputable def boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
    (Z : Type v) (k sampleBound : ℕ) :
    ActualSwitchedLocalInterface
      Z k
      (BoundedSampleFallbackIndex (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (ExactVisiblePostSwitchSurface Z k) where
  zOf := fun u => u.z
  aOf := fun _ u => u.a
  bOf := fun u => u.b
  localRule := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback index.1 index.2.1 u
  output := fun index u =>
    letI := Classical.decEq (ExactVisiblePostSwitchSurface Z k)
    PluginSampleMajority.predictWithFallback index.1 index.2.1 u
  output_eq_local := by
    intro index u
    rfl

/-- With an input-dependent fallback, the empty sample already realizes the
fallback rule exactly. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
    {Z : Type v} {k sampleBound : ℕ}
    (fallback : ExactVisibleRule Z k) :
    (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict
        (fallback, ⟨[], by simp⟩) =
      fallback := by
  classical
  funext u
  simp [boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface,
    ActualSwitchedLocalInterface.predictorFamily]

/-- Therefore an input-dependent fallback is already full-rule expressive for
every sample bound, including zero. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_realizes_every_lookupTable
    {Z : Type v} {k sampleBound : ℕ}
    (rule : ExactVisibleRule Z k) :
    ∃ index,
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily.predict index =
        rule := by
  exact ⟨(rule, ⟨[], by simp⟩),
    boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_emptySample_predict
      (Z := Z) (k := k) (sampleBound := sampleBound) rule⟩

/-- Bounded sample-level plug-in majority with an input-dependent fallback is
surjective onto all exact-visible Boolean rules independently of the sample
bound. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
    (Z : Type v) (k sampleBound : ℕ) :
    Function.Surjective
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.predict := by
  intro rule
  exact
    boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_realizes_every_lookupTable
      (Z := Z) (k := k) (sampleBound := sampleBound) rule

/-- Consequently the fallback-rule endpoint has no small finite predictor
cover below the exact visible truth-table budget.  The obstruction no longer
depends on the sample bound, because the fallback is already a full rule. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_finitePredictorCover_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily.FinitePredictorCover (2 ^ s) := by
  intro hcover
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)).2
      hcover
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
        Z k sampleBound)) hsmall

/-- The same side-channel endpoint cannot supply the clocked finite-learning
payload below the exact visible truth-table budget. -/
theorem boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    {Z : Type v} {k s sampleBound clock : ℕ} [Fintype Z]
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s clock := by
  intro hpayload
  have hsmall :
      ExactVisibleCompressionTarget
        (Z := Z) (k := k)
        (Index := BoundedSampleFallbackIndex
          (ExactVisiblePostSwitchSurface Z k) sampleBound)
        (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
          Z k sampleBound).predictorFamily s :=
    exactVisibleCompressionTarget_of_clockedKpolyFiniteLearningPayload
      (Z := Z) (k := k) (s := s) (clock := clock)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      hpayload
  exact
    (not_exactVisibleCompressionTarget_of_surjective_predict
      (Z := Z) (k := k) (s := s)
      (Index := BoundedSampleFallbackIndex
        (ExactVisiblePostSwitchSurface Z k) sampleBound)
      (G := (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface
        Z k sampleBound).predictorFamily)
      hs
      (boundedSamplePluginMajorityWithFallbackActualSwitchedLocalInterface_surjective
        Z k sampleBound)) hsmall

end Mettapedia.Computability.PNP

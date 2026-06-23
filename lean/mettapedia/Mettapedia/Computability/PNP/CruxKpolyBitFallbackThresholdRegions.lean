import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdVisibleWidth

/-!
# PNP `Kpoly` agreement and region-mass threshold anchors

This module isolates the agreement-mass, lightest-point, and heavy-region
obstructions for manuscript-facing sparse-threshold recovery packets on
actual-local endpoints.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on any actual-local endpoint, any two distinct
realized predictors in a manuscript-facing sparse-threshold recovery packet
already have agreement mass at most `q`. -/
theorem kpolyCoverage_anchor_actualLocal_agreementMass_le_of_nonempty_recovery_of_predict_ne
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q))
    (i j : Index)
    (hij : T.predictorFamily.predict j ≠ T.predictorFamily.predict i) :
    agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j) ≤ q := by
  rcases h with ⟨h⟩
  exact h.agreementMass_le_of_predict_ne i j hij

/-- Route-coverage anchor: therefore if one distinct realized predictor pair
already has agreement mass above `q`, no extractor at all can support the
manuscript-facing sparse-threshold recovery packet on that actual-local
endpoint. -/
theorem kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_agreementMass_of_predict_ne
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (i j : Index)
    (hij : T.predictorFamily.predict j ≠ T.predictorFamily.predict i)
    (hgap : q < agreementMass μ (T.predictorFamily.predict i) (T.predictorFamily.predict j)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_agreementMass_of_predict_ne
      (μ := μ)
      (T := T)
      (r := r)
      (zfeat := zfeat)
      (q := q)
      i
      j
      hij
      hgap
      hdata

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
manuscript-facing sparse-threshold recovery packet already forces the intrinsic
lightest-point threshold.  The fallback-side repairs are only concrete
specializations of this surjective actual-local barrier. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_one_sub_apply_lightestPoint_le_of_nonempty_recovery
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    1 - μ (PMF.lightestPoint μ) ≤ q := by
  rcases h with ⟨h⟩
  exact h.one_sub_apply_lightestPoint_le_of_surjective_predict hsurj

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
manuscript-facing sparse-threshold recovery packet already forces every proper
finite visible region to have total mass at most `q`.  This strengthens the
single-lightest-point barrier to arbitrary proper regions. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_regionMass_le_of_nonempty_recovery_of_exists_not_mem
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region) :
    region.sum (fun x => μ x) ≤ q := by
  rcases h with ⟨h⟩
  exact h.regionMass_le_of_surjective_predict_of_exists_not_mem hsurj region hout

/-- Route-coverage anchor: once some proper finite visible region already has
mass above `q`, no extractor at all can support the manuscript-facing sparse-
threshold recovery packet on a surjective actual-local endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_exists_not_mem_of_lt_regionMass
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hout : ∃ x₀ : ExactVisiblePostSwitchSurface Z k, x₀ ∉ region)
    (hmass : q < region.sum (fun x => μ x)) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  exact
    ActualSwitchedLocalInterface.not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_surjective_predict_of_exists_not_mem_of_lt_regionMass
      (μ := μ)
      (T := T)
      (r := r)
      hsurj
      region
      hout
      hmass

/-- Route-coverage anchor: once one finite visible region already carries mass
above `q`, any injectively indexed actual-local endpoint supporting the
manuscript-facing sparse-threshold recovery packet must fit inside the Boolean
trace space on that region. -/
theorem kpolyCoverage_anchor_actualLocal_predictorCard_le_two_pow_regionCard_of_nonempty_recovery_of_injective_predict_of_lt_regionMass
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Fintype Index]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q))
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hmass : q < region.sum (fun x => μ x))
    (hinj : Function.Injective T.predictorFamily.predict) :
    Fintype.card Index ≤ 2 ^ region.card := by
  rcases h with ⟨h⟩
  exact
    h.card_le_two_pow_regionCard_of_injective_predict_of_lt_regionMass
      region
      hmass
      hinj

/-- Route-coverage anchor: the same heavy-region trace-space obstruction also
removes the extractor choice itself on any injectively indexed actual-local
endpoint. -/
theorem kpolyCoverage_anchor_actualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Fintype Index]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (region : Finset (ExactVisiblePostSwitchSurface Z k))
    (hinj : Function.Injective T.predictorFamily.predict)
    (hmass : q < region.sum (fun x => μ x))
    (hcard : 2 ^ region.card < Fintype.card Index) :
    ¬ ∃ zfeat : Z → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ T zfeat q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_regionCard_of_injective_predict_of_lt_regionMass
      (μ := μ)
      (T := T)
      (r := r)
      (zfeat := zfeat)
      region
      hinj
      hmass
      hcard
      hdata
end Mettapedia.Computability.PNP

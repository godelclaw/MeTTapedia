import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryCardinalityObstruction
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMRecoveryInjectiveConcentrationObstruction
import Mettapedia.Computability.PNP.CruxKpolyBitFallbackThresholdFallback

/-!
# PNP `Kpoly` actual-local threshold anchors

This module lifts the bit-fallback endpoint barriers to generic actual-local
interfaces: surjective actual-local endpoints, injective extractors, full-rule
endpoints, and explicit uniform-complement thresholds.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal BigOperators

universe u v w z

/-- Route-coverage anchor: on any finite surjective actual-local endpoint, the
manuscript-facing sparse-threshold recovery packet already forces the
unconditional half-width ceiling.  The fallback-side visible-width repairs are
only concrete specializations of this surjective actual-local barrier. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_recovery
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface (BitVec n) k)]
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict hsurj

/-- Route-coverage anchor: on any finite nonempty surjective actual-local
endpoint, the manuscript-facing sparse-threshold recovery packet already
forces `q` above the uniform-complement threshold `1 - |surface|⁻¹`. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_one_sub_inv_card_le_of_nonempty_recovery
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
    1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact h.one_sub_inv_card_le_of_surjective_predict hsurj

/-- Route-coverage anchor: even without surjectivity, any manuscript-facing
recovery packet on an actual-local endpoint with an injective extractor of
positive combined width already forces `q` above the same uniform-complement
threshold `1 - |surface|⁻¹`. -/
theorem kpolyCoverage_anchor_actualLocal_one_sub_inv_card_le_of_nonempty_recovery_of_injective_zfeat
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (zfeat : Z → BitVec r)
    (i : Index)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact h.one_sub_inv_card_le_of_injective_zfeat hinj hwidth i

/-- Route-coverage anchor: below the uniform-complement threshold, no
injective extractor of positive combined width can support the manuscript-
facing sparse-threshold recovery packet on that actual-local endpoint. -/
theorem kpolyCoverage_anchor_actualLocal_not_exists_injective_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_inv_card
    {Z : Type v} [Fintype Z] {k r : ℕ} {Index : Type u} {Block : Type w}
    [Nonempty (ExactVisiblePostSwitchSurface Z k)]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (T : ActualSwitchedLocalInterface Z k Index Block)
    (q : ℝ≥0∞)
    (i : Index)
    (hwidth : 0 < r + (k + k))
    (hq_lt :
      q < 1 - (Fintype.card (ExactVisiblePostSwitchSurface Z k) : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : Z → BitVec r,
        Function.Injective zfeat ∧
          Nonempty
            (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
              μ T zfeat q) := by
  rintro ⟨zfeat, hinj, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_inv_card
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hinj
      hwidth
      i
      hq_lt
      hdata

/-- Route-coverage anchor: even the weaker shared sparse-threshold ERM packet
already forces the same unconditional half-width ceiling on any surjective
actual-local `BitVec n` endpoint. -/
theorem kpolyCoverage_anchor_surjectiveActualLocal_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (hsurj : Function.Surjective T.predictorFamily.predict)
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMData
          T zfeat)) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases h with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      hsurj

/-- Route-coverage anchor: on the full-rule `BitVec n` endpoint, the
manuscript-facing recovery packet already forces the explicit threshold
`q ≥ 1 - 2^-(n + 2*k)`. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_one_sub_pow_inv_le_of_nonempty_recovery
    {n k r : ℕ}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (zfeat : BitVec n → BitVec r)
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ
          (fullRuleActualSwitchedLocalInterface (BitVec n) k)
          zfeat
          q)) :
    1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.one_sub_pow_inv_le_of_nonempty_fullRuleActualSwitchedLocalInterface_sharedExactZABSparseThresholdERMRecoveryData
      (μ := μ)
      (k := k)
      (zfeat := zfeat)
      h

/-- Route-coverage anchor: on any actual-local `BitVec n` endpoint, an
injective extractor of positive combined width already forces the explicit
threshold `q ≥ 1 - 2^-(n + 2*k)`. -/
theorem kpolyCoverage_anchor_actualLocal_one_sub_pow_inv_le_of_nonempty_recovery_of_injective_zfeat
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)} {q : ℝ≥0∞}
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (zfeat : BitVec n → BitVec r)
    (i : Index)
    (hinj : Function.Injective zfeat)
    (hwidth : 0 < r + (k + k))
    (h :
      Nonempty
        (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
          μ T zfeat q)) :
    1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹ ≤ q := by
  rcases h with ⟨h⟩
  exact
    ActualSwitchedLocalInterface.one_sub_pow_inv_le_of_injective_zfeat
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      h
      hinj
      hwidth
      i

/-- Route-coverage anchor: below the explicit `BitVec n` threshold, no
injective extractor of positive combined width can support the manuscript-
facing sparse-threshold recovery packet on that actual-local endpoint. -/
theorem kpolyCoverage_anchor_actualLocal_not_exists_injective_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {n k r : ℕ} {Index : Type u} {Block : Type w}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (T : ActualSwitchedLocalInterface (BitVec n) k Index Block)
    (q : ℝ≥0∞)
    (i : Index)
    (hwidth : 0 < r + (k + k))
    (hq_lt : q < 1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Function.Injective zfeat ∧
          Nonempty
            (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
              μ T zfeat q) := by
  rintro ⟨zfeat, hinj, hdata⟩
  exact
    ActualSwitchedLocalInterface.not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_injective_zfeat_of_lt_one_sub_pow_inv
      (μ := μ)
      (T := T)
      (zfeat := zfeat)
      hinj
      hwidth
      i
      hq_lt
      hdata

/-- Route-coverage anchor: below that explicit `BitVec n` threshold, no
extractor at all can support the full-rule manuscript-facing recovery packet. -/
theorem kpolyCoverage_anchor_fullRuleActualLocal_not_exists_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
    {n k r : ℕ}
    (μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k))
    (q : ℝ≥0∞)
    (hq_lt : q < 1 - (2 ^ (n + 2 * k) : ℝ≥0∞)⁻¹) :
    ¬ ∃ zfeat : BitVec n → BitVec r,
        Nonempty
          (ActualSwitchedLocalInterface.SharedExactZABSparseThresholdERMRecoveryData
            μ
            (fullRuleActualSwitchedLocalInterface (BitVec n) k)
            zfeat
            q) := by
  rintro ⟨zfeat, hdata⟩
  exact
    ActualSwitchedLocalInterface.fullRuleActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMRecoveryData_of_lt_one_sub_pow_inv
      (μ := μ)
      (k := k)
      (r := r)
      (zfeat := zfeat)
      hq_lt
      hdata
end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterfaceData

/-!
# P vs NP grassroots: shared exact ZAB sparse-threshold ERM interface

This module derives the manuscript-facing sparse-threshold ERM target,
compression, finite-cover, non-surjectivity, and recovery consequences.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

section

variable [Fintype Z]

def SharedExactZABSparseThresholdERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABSparseThresholdAffineERMTargetData
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABSparseThresholdERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := Index) G (2 * p) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABSparseThresholdAffineERMCompressionTarget
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABSparseThresholdERMRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (2 * p)) := by
  exact (h.targetData).finitePredictorCover

theorem SharedExactZABSparseThresholdERMRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (2 * p)) := by
  exact (h.targetData).finiteIndexRepresentativeCover

theorem SharedExactZABSparseThresholdERMRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (2 * p)) := by
  exact (h.targetData).finitePredictorQuotient

theorem SharedExactZABSparseThresholdERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABSparseThresholdERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : 2 * p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABSparseThresholdERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABSparseThresholdAffineERMRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    μ zfeat features samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP

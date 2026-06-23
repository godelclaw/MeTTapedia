import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterfaceData

/-!
# P vs NP grassroots: shared exact ZAB affine-feature ERM interface

This module derives the manuscript-facing affine-feature ERM target,
compression, finite-cover, non-surjectivity, and recovery consequences.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

section

variable [Fintype Z]

def SharedExactZABAffineFeatureERMRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineFeatureERMTargetData
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABAffineFeatureERMRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
        (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineFeatureERMCompressionTarget
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    zfeat features samples

theorem SharedExactZABAffineFeatureERMRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorCover (2 ^ (2 ^ p)) := by
  exact (h.targetData).finitePredictorCover

theorem SharedExactZABAffineFeatureERMRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (2 ^ p)) := by
  exact (h.targetData).finiteIndexRepresentativeCover

theorem SharedExactZABAffineFeatureERMRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    G.FinitePredictorQuotient (2 ^ (2 ^ p)) := by
  exact (h.targetData).finitePredictorQuotient

theorem SharedExactZABAffineFeatureERMRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABAffineFeatureERMRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h with ⟨features, samples, rfl, agreement_le⟩
  exact sharedExactZABAffineFeatureERMRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
    μ zfeat features samples q agreement_le i m

end

end

end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionList

/-!
# P vs NP grassroots: shared exact ZAB decision-list recovery interface

This module packages the recovery wrapper for the shared exact ZAB
decision-list route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

structure SharedExactZABDecisionListRecoveryData
    [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  realized :
    RealizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) zfeat features G
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactZABAffineDecisionListBitFamily Z zfeat features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactZABAffineDecisionListBitFamily Z zfeat features).decode c.1) ≤ q

section

variable [Fintype Z]

theorem SharedExactZABDecisionListRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    SharedExactZABDecisionListTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABDecisionListRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (p + 1) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABDecisionListRecoveryData.finitePredictorCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FinitePredictorCover (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorCover

theorem SharedExactZABDecisionListRecoveryData.finiteIndexRepresentativeCover
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FiniteIndexRepresentativeCover (2 ^ (p + 1)) := by
  exact (h.targetData).finiteIndexRepresentativeCover

theorem SharedExactZABDecisionListRecoveryData.finitePredictorQuotient
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q) :
    G.FinitePredictorQuotient (2 ^ (p + 1)) := by
  exact (h.targetData).finitePredictorQuotient

theorem SharedExactZABDecisionListRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ p + 1 := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hs : p + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABDecisionListRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (p + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineDecisionListBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  exact sharedExactZABAffineDecisionListRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat features
    (μ := μ)
    (target := G.predict i)
    (m := m)
    (h.realized i)
    (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP

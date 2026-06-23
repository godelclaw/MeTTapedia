import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceData

/-!
# P vs NP grassroots: shared exact ZAB affine-feature recovery interface

This module derives compression, surface-cardinality, and weighted recovery
consequences from affine-feature recovery data on the shared-basis exact
`(zfeat(z), a, b)` route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

section

variable [Fintype Z]

def SharedExactZABAffineFeatureRecoveryData.targetData
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    SharedExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat h.features G := by
  exact ⟨h.realized⟩

theorem SharedExactZABAffineFeatureRecoveryData.compressionTarget
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  exact (h.targetData).compressionTarget

theorem SharedExactZABAffineFeatureRecoveryData.surfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact (h.targetData).surfaceCard_le_of_surjective_predict hsurj

theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_lt_surfaceCard
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_lt_surfaceCard hs

theorem SharedExactZABAffineFeatureRecoveryData.recoveryLowerBound
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat h.features).bitExactRecoverySampleMass
        μ (G.predict i) m := by
  rcases h.realized i with ⟨code, hcode⟩
  exact sharedExactZABAffineFeatureRecoveryLowerBound
    (Z := Z) (p := p) (r := r) (k := k) zfeat h.features
    (μ := μ) (target := G.predict i) (m := m)
    ⟨code, hcode⟩ (h.agreement_le i)

end

end

end Mettapedia.Computability.PNP

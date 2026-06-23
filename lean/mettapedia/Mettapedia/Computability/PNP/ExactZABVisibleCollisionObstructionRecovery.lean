import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionTargets

/-!
# P vs NP crux: exact ZAB visible collision recovery wrappers

This module lifts the noninjective-`zfeat` collision obstruction from target
records to exact and shared exact ZAB recovery-data records.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section Route

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

section Recovery

variable [Fintype Z]

theorem ExactZABAffineFeatureRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem ExactZABSparseThresholdRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem ExactZABAffineDecisionListRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABSparseThresholdRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

theorem SharedExactZABDecisionListRecoveryData.not_surjective_predict_of_not_injective_zfeat
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABDecisionListRecoveryData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
        μ zfeat features G q)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact (h.targetData).not_surjective_predict_of_not_injective_zfeat hni

end Recovery

end Route

end Mettapedia.Computability.PNP

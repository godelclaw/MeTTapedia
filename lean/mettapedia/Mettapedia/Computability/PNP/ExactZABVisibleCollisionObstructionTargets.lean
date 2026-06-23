import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionCore

/-!
# P vs NP crux: exact ZAB visible collision target wrappers

This module lifts the noninjective-`zfeat` collision obstruction from route
realization predicates to exact and shared exact ZAB target-data records.
-/

namespace Mettapedia.Computability.PNP
section Route

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

theorem ExactZABAffineFeatureTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABAffineFeatureFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem ExactZABSparseThresholdTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABSparseThresholdAffineFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem ExactZABAffineDecisionListTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      ExactZABAffineDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedByExactZABAffineDecisionListFamily
      (p := p) (Z := Z) (r := r) (k := k) h.realized hni

theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineFeatureFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

theorem SharedExactZABSparseThresholdTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABSparseThresholdAffineFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

theorem SharedExactZABDecisionListTargetData.not_surjective_predict_of_not_injective_zfeat
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABDecisionListTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineDecisionListFamily
      (Z := Z) (p := p) (r := r) (k := k) h.realized hni

end Route

end Mettapedia.Computability.PNP

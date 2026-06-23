import Mettapedia.Computability.PNP.ExactZABVisibleCollisionObstructionTargets
import Mettapedia.Computability.PNP.ExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteFamilies
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteTargets
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteRecovery
import Mettapedia.Computability.PNP.SharedExactZABERMRoute

/-!
# P vs NP crux: exact ZAB visible collision ERM wrappers

This module applies the noninjective-`zfeat` collision obstruction to the exact
and shared exact ZAB ERM family constructors.
-/

namespace Mettapedia.Computability.PNP
section Route

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

theorem exactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem exactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    (exactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_not_injective_zfeat
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineDecisionListERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features samples).not_surjective_predict_of_not_injective_zfeat
      hni

end Route

end Mettapedia.Computability.PNP

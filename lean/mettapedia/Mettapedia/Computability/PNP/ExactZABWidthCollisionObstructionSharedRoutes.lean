import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionExactRoutes

/-!
# Exact ZAB width-collision obstruction: shared-basis exact routes

This module lifts width-compressing extractor noninjectivity to the shared-basis
exact ZAB route surfaces.
-/

namespace Mettapedia.Computability.PNP
section SharedRoutes

variable {n p r k : ℕ} {Index : Type*}

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem sharedExactZABAffineDecisionListERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (sharedExactZABAffineDecisionListERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    sharedExactZABAffineDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

end SharedRoutes

end Mettapedia.Computability.PNP

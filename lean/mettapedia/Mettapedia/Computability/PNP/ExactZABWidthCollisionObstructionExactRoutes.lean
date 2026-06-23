import Mettapedia.Computability.PNP.ExactZABWidthCollisionObstructionCore

/-!
# Exact ZAB width-collision obstruction: non-shared exact routes

This module lifts width-compressing extractor noninjectivity to the non-shared
exact ZAB route surfaces.
-/

namespace Mettapedia.Computability.PNP
section ExactRoutes

variable {n p r k : ℕ} {Index : Type*}

theorem exactZABDecisionListERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABDecisionListERMFamily
          (Z := BitVec n) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABDecisionListERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem exactZABAffineFeatureERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABAffineFeatureERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

theorem exactZABSparseThresholdAffineERMFamily_not_surjective_of_width_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hwidth : r < n) :
    ¬ Function.Surjective
        (exactZABSparseThresholdAffineERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict := by
  exact
    exactZABSparseThresholdAffineERMFamily_not_surjective_of_not_injective_zfeat
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
      zfeat samples
      (not_injective_bitVecExtractor_of_width_lt zfeat hwidth)

end ExactRoutes

end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteFamilies

/-!
# P vs NP grassroots: shared exact ZAB feature ERM targets

This module proves that the shared-basis exact `(zfeat(z), a, b)` ERM families
land in the corresponding affine-feature and sparse-threshold compression
targets.
-/

namespace Mettapedia.Computability.PNP
section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

theorem sharedExactZABAffineFeatureERMTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedExactZABAffineFeatureTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) := by
  refine ⟨?_⟩
  intro i
  let table : BitCode (2 ^ p) :=
    (sharedExactZABAffineFeatureBitFamily Z zfeat features).empiricalRiskCode (samples i)
  refine ⟨table, ?_⟩
  funext u
  simp [sharedExactZABAffineFeatureERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    table,
    sharedExactZABAffineFeatureBitFamily]

theorem sharedExactZABSparseThresholdAffineERMTargetData
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedExactZABSparseThresholdTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) := by
  refine ⟨?_⟩
  intro i
  let code : SharedSparseThresholdCode p :=
    (sharedSparseThresholdCodeEquivBitCode p).symm
      ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext u
  simp [sharedExactZABSparseThresholdAffineERMFamily,
    BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
    BitEncodedClassifierFamily.empiricalRiskPredictor,
    code,
    sharedExactZABSparseThresholdAffineBitFamily,
    sharedSparseThresholdCodeEquivBitCode]

theorem sharedExactZABAffineFeatureERMCompressionTarget
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples)
      (2 ^ p) := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).compressionTarget

theorem sharedExactZABSparseThresholdAffineERMCompressionTarget
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples)
      (2 * p) := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).compressionTarget

theorem sharedExactZABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).surfaceCard_le_of_surjective_predict hsurj

theorem sharedExactZABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * p := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).surfaceCard_le_of_surjective_predict hsurj

theorem sharedExactZABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).not_surjective_predict_of_lt_surfaceCard hs

theorem sharedExactZABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Fintype Z]
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 * p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict := by
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).not_surjective_predict_of_lt_surfaceCard hs

end

end Mettapedia.Computability.PNP

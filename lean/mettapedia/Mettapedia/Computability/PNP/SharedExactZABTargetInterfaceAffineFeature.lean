import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceData
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# P vs NP grassroots: shared exact ZAB affine-feature target interface

This module packages the affine-feature target data and finite-image
consequences for the shared-basis `(zfeat(z), a, b)` route.
-/

namespace Mettapedia.Computability.PNP
section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

theorem SharedExactZABAffineFeatureTargetData.compressionTarget
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ p) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactZABAffineFeatureFamily
    (Z := Z) (p := p) (r := r) (k := k) zfeat features h.realized

theorem SharedExactZABAffineFeatureTargetData.finitePredictorCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorCover (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.finiteIndexRepresentativeCover
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FiniteIndexRepresentativeCover (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.finitePredictorQuotient
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G) :
    G.FinitePredictorQuotient (2 ^ (2 ^ p)) := by
  exact
    (exactVisibleCompressionTarget_iff_finitePredictorQuotient
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) (G := G)).mp
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ p := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 ^ p) (Index := Index) hsurj
      h.compressionTarget

theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := Z) (p := p) (r := r) (k := k) (Index := Index) zfeat features G)
    (hs : 2 ^ p < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

end Mettapedia.Computability.PNP

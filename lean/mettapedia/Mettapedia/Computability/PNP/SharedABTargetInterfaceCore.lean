import Mettapedia.Computability.PNP.SharedABFeatureRoutesExactPullback
import Mettapedia.Computability.PNP.ExactVisibleCompressionObstruction

/-!
# Shared raw `(a,b)` target interfaces

This module packages the generic target data for the shared affine-feature,
sparse-threshold, and decision-list routes and derives their compression and
surjectivity bounds.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- Target data for the shared raw `(a, b)` affine-feature route. -/
structure SharedABAffineFeatureTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` sparse-threshold route. -/
structure SharedABSparseThresholdTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

/-- Target data for the shared raw `(a, b)` decision-list route. -/
structure SharedABDecisionListTargetData
    [Inhabited Z]
    (G : ExactVisibleSwitchedFamily Z k Index) where
  features : Fin r → AffineColumnCode (k + k)
  invariant : ABVisibleInvariant (Z := Z) (k := k) G
  realized :
    RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
      (liftToABVisibleFamily (Z := Z) (k := k) G)

section

variable [Inhabited Z]

theorem SharedABAffineFeatureTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABAffineFeatureTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 ^ r) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABAffineFeatureTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedABSparseThresholdTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABSparseThresholdTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := 2 * r) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABSparseThresholdTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABSparseThresholdTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

theorem SharedABDecisionListTargetData.compressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    (Z := Z) (r := r) (k := k) h.invariant h.realized

theorem SharedABDecisionListTargetData.surfaceCard_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact
    exactVisibleCompressionTarget_surfaceCard_le_of_surjective_predict
      (Z := Z) (k := k) (s := r + 1) (Index := Index) hsurj
      h.compressionTarget

theorem SharedABDecisionListTargetData.not_surjective_predict_of_lt_surfaceCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : SharedABDecisionListTargetData (Z := Z) (r := r) (k := k) (Index := Index) G)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hs (h.surfaceCard_le_of_surjective_predict hsurj)

end

end

end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverProbePullback

/-!
# PNP `Kpoly` exact-visible finite-cover obstruction anchors

This module contains the final exact-visible surjectivity and finite-probe
obstructions for compression, clocked realization, and clocked finite-learning
payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
predictor-image cover below the full exact visible Boolean classifier space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finitePredictorCover_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N :=
  not_exactVisible_finitePredictorCover_of_surjective_predict hN hsurj

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
representative-index cover below the full exact visible Boolean classifier
space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict hN hsurj

/-- Route-coverage anchor: a fully expressive exact visible family has no finite
quotient-code presentation below the full exact visible Boolean classifier
space. -/
theorem kpolyCoverage_anchor_not_exactVisible_finitePredictorQuotient_of_surjective_predict
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N :=
  not_exactVisible_finitePredictorQuotient_of_surjective_predict hN hsurj

/-- Route-coverage anchor: the clocked exact-visible realization target is
impossible below the full predictor-image cardinality for a fully expressive
exact visible family. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_surjective_predict_of_lt_predictorCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    hs hsurj

/-- Route-coverage anchor: the same surjectivity obstruction refutes the full
clocked finite-learning payload below the full predictor-image cardinality. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_surjective_predict_of_lt_predictorCard
    hs hsurj

/-- Route-coverage anchor: exact visible compression is impossible below the
size of any injectively indexed finite probe family already realized by the
switched predictors. -/
theorem kpolyCoverage_anchor_not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    target hinj hreal hs

/-- Route-coverage anchor: the same finite-probe lower bound refutes clocked
exact-visible realization below the probe cardinality. -/
theorem kpolyCoverage_anchor_not_clockedRealization_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F :=
  not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
    target hinj hreal hs

/-- Route-coverage anchor: finite-probe lower bounds also refute the bundled
clocked finite-learning payload below the probe cardinality. -/
theorem kpolyCoverage_anchor_not_clockedFiniteLearningPayload_of_injective_realization_of_lt_card
    {Probe Z : Type*} [Fintype Probe] [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ClockedKpolyFiniteLearningPayload G s clock :=
  not_clockedKpolyFiniteLearningPayload_of_injective_realization_of_lt_card
    target hinj hreal hs
end Mettapedia.Computability.PNP

import Mettapedia.Computability.PNP.SharedABFeatureObstructionReducedFiniteProbe

/-!
# Shared `(a,b)` feature obstructions: exact pullback layer

This module lifts reduced `(a,b)` image lower bounds across exact visible
families that factor through the raw `(a,b)` surface.
-/

namespace Mettapedia.Computability.PNP

section ExactPullback

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared affine-feature exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ 2 ^ r := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 ^ r) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared affine-feature exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared affine features. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared sparse-threshold exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * r := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := 2 * r) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared sparse-threshold exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared sparse-threshold
features. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- If an exact family factors through a fully expressive raw `(a,b)` family,
then a shared decision-list exact realization forces the reduced truth-table
lower bound. -/
theorem abVisible_surfaceCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card (ABVisibleSurface k) ≤ r + 1 := by
  exact
    abVisible_surfaceCard_le_of_exactVisibleCompressionTarget_of_factorsThrough
      (Z := Z) (k := k) (s := r + 1) hfactor hsurj
      (exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) (Index := Index) features hreal)

/-- Shared decision-list exact realization is impossible below the reduced
truth-table threshold when the reduced family is fully expressive. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < Fintype.card (ABVisibleSurface k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hsurj hreal

/-- Formula form of the exact-pullback obstruction for shared decision-list
features. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_cardFormula
    [Inhabited Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < 2 ^ (2 * k))
    (hfactor : G.FactorsThrough abVisibleData H)
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  exact
    not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_surjective_predict_of_lt_surfaceCard
      (Z := Z) (r := r) (k := k)
      (by simpa [card_abVisibleSurface (k := k)] using hs)
      hfactor hsurj

/-- Exact-pullback partial-image form for shared affine features: any
injectively indexed finite probe family already realized on the reduced
`(a,b)` view must fit inside the shared truth-table predictor image. -/
theorem probeCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (2 ^ r) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (2 ^ r)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 ^ r) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact affine-feature realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

/-- Exact-pullback partial-image form for shared sparse-threshold features. -/
theorem probeCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (2 * r) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (2 * r)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := 2 * r) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact sparse-threshold realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

/-- Exact-pullback partial-image form for shared decision-list features. -/
theorem probeCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) features G) :
    Fintype.card Probe ≤ 2 ^ (r + 1) := by
  have htarget :
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) :=
    exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
      (Z := Z) (r := r) (k := k) (Index := Index) features hreal
  have hcover : G.FinitePredictorCover (2 ^ (r + 1)) :=
    (exactVisibleCompressionTarget_iff_finitePredictorCover
      (Z := Z) (k := k) (s := r + 1) (Index := Index) (G := G)).mp htarget
  exact
    abVisible_finitePredictorCover_card_le_of_factorsThrough_of_injective_realization
      (Z := Z) (k := k) (Index := Index)
      target hinj hprobe hfactor hcover

/-- Shared exact decision-list realization is impossible when a larger
injective probe family is already realized on the reduced `(a,b)` view. -/
theorem not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    [Inhabited Z] {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe
      (Z := Z) (r := r) (k := k) target hinj hprobe hfactor hreal

end ExactPullback

end Mettapedia.Computability.PNP

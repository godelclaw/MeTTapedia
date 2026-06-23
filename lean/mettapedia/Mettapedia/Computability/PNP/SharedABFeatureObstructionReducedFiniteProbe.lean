import Mettapedia.Computability.PNP.SharedABFeatureObstructionReducedFullRules

/-!
# Shared `(a,b)` feature obstructions: reduced finite-probe image bounds

This module packages injective-probe lower bounds for shared raw `(a,b)`
feature routes before exact-surface pullback.
-/

namespace Mettapedia.Computability.PNP

section ReducedFiniteProbe

variable {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}

/-- Partial-image form for shared affine features on the raw `(a,b)` surface:
realizing an injectively indexed probe family forces the probe count to fit
inside the finite predictor image of the shared truth-table combiner. -/
theorem probeCard_le_of_realizedBySharedABAffineFeatureFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (2 ^ r) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := 2 ^ r)
      (abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
        (r := r) (k := k) hreal))

/-- Shared affine features cannot realize an injective probe family larger than
their finite predictor image. -/
theorem not_realizedBySharedABAffineFeatureFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABAffineFeatureFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

/-- Partial-image form for shared sparse-threshold features on the raw
`(a,b)` surface. -/
theorem probeCard_le_of_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (2 * r) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := 2 * r)
      (abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
        (r := r) (k := k) hreal))

/-- Shared sparse-threshold features cannot realize an injective probe family
larger than their finite predictor image. -/
theorem not_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

/-- Partial-image form for shared decision-list features on the raw `(a,b)`
surface. -/
theorem probeCard_le_of_realizedBySharedABAffineDecisionListFamily_of_injective_probe
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    Fintype.card Probe ≤ 2 ^ (r + 1) :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    (G := H) target hinj hprobe
    (IndexedPredictorFamily.finitePredictorCover_of_hasBitBudget
      (G := H) (s := r + 1)
      (abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
        (r := r) (k := k) hreal))

/-- Shared decision-list features cannot realize an injective probe family
larger than their finite predictor image. -/
theorem not_realizedBySharedABAffineDecisionListFamily_of_injective_probe_of_lt_budgetImageCard
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hcard <|
    probeCard_le_of_realizedBySharedABAffineDecisionListFamily_of_injective_probe
      (r := r) (k := k) target hinj hprobe hreal

end ReducedFiniteProbe

end Mettapedia.Computability.PNP

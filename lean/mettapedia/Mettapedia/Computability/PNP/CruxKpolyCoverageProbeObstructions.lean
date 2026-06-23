import Mettapedia.Computability.PNP.SharedABFeatureObstructionFullExactPullback

/-!
# PNP `Kpoly` coverage anchors: finite-probe image obstructions

Finite-probe image cardinality obstructions and their exact-visible pullbacks through raw `(a,b)` factors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: shared affine-feature families cannot realize a
finite probe image larger than their truth-table combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABAffineFeature_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H :=
  not_realizedBySharedABAffineFeatureFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: shared sparse-threshold families cannot realize a
finite probe image larger than their combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABSparseThreshold_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H :=
  not_realizedBySharedABSparseThresholdAffineFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: shared decision-list families cannot realize a
finite probe image larger than their combiner image. -/
theorem kpolyCoverage_anchor_not_sharedABDecisionList_of_injective_probe_of_lt_budgetImageCard
    {Probe : Type*} [Fintype Probe] {r k : ℕ} {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H :=
  not_realizedBySharedABAffineDecisionListFamily_of_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard

/-- Route-coverage anchor: the shared affine-feature finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABAffineFeature_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 ^ r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineFeatureFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor

/-- Route-coverage anchor: the shared sparse-threshold finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABSparseThreshold_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (2 * r) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABSparseThresholdAffineFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor

/-- Route-coverage anchor: the shared decision-list finite-probe obstruction
lifts through exact visible pullback along `abVisibleData`. -/
theorem kpolyCoverage_anchor_not_sharedExactABDecisionList_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    {Z Probe : Type*} [Inhabited Z] [Fintype Probe]
    {r k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (target : Probe → ABVisibleSurface k → Bool)
    (hinj : Function.Injective target)
    (hprobe : ∀ p, ∃ i, H.predict i = target p)
    (hcard : 2 ^ (r + 1) < Fintype.card Probe)
    (hfactor : G.FactorsThrough abVisibleData H) :
    ¬ RealizedBySharedExactABAffineDecisionListFamily
        (Z := Z) (r := r) (k := k) features G :=
  not_realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab_and_injective_probe_of_lt_budgetImageCard
    target hinj hprobe hcard hfactor


end Mettapedia.Computability.PNP

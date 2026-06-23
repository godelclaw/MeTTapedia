import Mettapedia.Computability.PNP.ExactZABExtractorCollisionObstruction
import Mettapedia.Computability.PNP.ExactZABFeatureERMRoute
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteFamilies
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteTargets
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteRecovery

/-!
# P vs NP crux: exact ZAB visible collision core

This module proves the route-independent collision principle: if every
predictor in a family is invariant on the fibers of `zfeat`, then a
noninjective `zfeat` prevents surjectivity onto the full exact visible rule
class. It also records the invariance consequences for exact and shared exact
ZAB realization predicates.
-/

namespace Mettapedia.Computability.PNP
section Core

variable {Z : Type*} {p r k : ℕ}

theorem not_surjective_predict_of_all_exactZABFiberInvariant
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv :
      ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i))
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  classical
  rcases exists_exactZABFiberSeparatingRule_of_not_injective
      (Z := Z) (r := r) (k := k) zfeat hni with ⟨rule, hsep⟩
  intro hsurj
  rcases hsurj rule with ⟨i, hi⟩
  have hrule :
      ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat rule := by
    simpa [hi] using hinv i
  exact
    (not_exactZABFiberSeparatingRule_of_exactZABFiberInvariantRule
      (Z := Z) (r := r) (k := k) hrule) hsep

theorem all_exactZABFiberInvariant_of_realizedByExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = affineFeaturePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedByExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = sparseThresholdAffinePredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedByExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u = affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat u) := by
          simp [hcode]
    _ = affineDecisionListPredict code
        (exactZABVisibleData (Z := Z) (r := r) (k := k) zfeat v) := by
          rw [huv]
    _ = G.predict i v := by
          simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨table, htable⟩
  calc
    G.predict i u =
        sharedExactZABAffineFeaturePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features table u := by
            simp [htable]
    _ =
        sharedExactZABAffineFeaturePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features table v := by
            simp [sharedExactZABAffineFeaturePredict, exactZABAffineFeatureSummary, huv]
    _ = G.predict i v := by
            simp [htable]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code u := by
            simp [hcode]
    _ =
        sharedExactZABSparseThresholdAffinePredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code v := by
            simp [sharedExactZABSparseThresholdAffinePredict, huv]
    _ = G.predict i v := by
            simp [hcode]

theorem all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G) :
    ∀ i, ExactZABFiberInvariantRule (Z := Z) (r := r) (k := k) zfeat (G.predict i) := by
  intro i u v huv
  rcases hreal i with ⟨code, hcode⟩
  calc
    G.predict i u =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code u := by
            simp [hcode]
    _ =
        sharedExactZABAffineDecisionListPredict
          (Z := Z) (p := p) (r := r) (k := k) zfeat features code v := by
            simp [sharedExactZABAffineDecisionListPredict, exactZABAffineFeatureSummary, huv]
    _ = G.predict i v := by
            simp [hcode]

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABAffineFeatureFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABSparseThresholdAffineFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedByExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) (Index := Index) zfeat G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedByExactZABAffineDecisionListFamily
        (p := p) (Z := Z) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineFeatureFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineFeatureFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABSparseThresholdAffineFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABSparseThresholdAffineFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

theorem not_surjective_predict_of_not_injective_of_realizedBySharedExactZABAffineDecisionListFamily
    {Index : Type*}
    {zfeat : Z → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hreal :
      RealizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features G)
    (hni : ¬ Function.Injective zfeat) :
    ¬ Function.Surjective G.predict := by
  exact
    not_surjective_predict_of_all_exactZABFiberInvariant
      (Z := Z) (r := r) (k := k)
      (all_exactZABFiberInvariant_of_realizedBySharedExactZABAffineDecisionListFamily
        (Z := Z) (p := p) (r := r) (k := k) hreal)
      hni

end Core

end Mettapedia.Computability.PNP

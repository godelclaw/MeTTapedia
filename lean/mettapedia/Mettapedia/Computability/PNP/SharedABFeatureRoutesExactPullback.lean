import Mettapedia.Computability.PNP.SharedABFeatureRoutesFamilies

/-!
# Shared `(a,b)` feature route exact pullbacks

This module lifts reduced shared-AB feature realizations across exact visible
families that factor through `abVisibleData`, including the invariant-family
specialization.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ}

theorem realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineFeatureFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table u := by
          symm
          exact congrFun
            (sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features table) u

theorem realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABSparseThresholdAffineFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    RealizedBySharedExactABAffineDecisionListFamily (Z := Z) (r := r) (k := k) features G := by
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨code, ?_⟩
  funext u
  calc
    G.predict i u = H.predict i (abVisibleData u) := hfactor i u
    _ = sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
          exact congrFun hi (abVisibleData u)
    _ = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u := by
          symm
          exact congrFun
            (sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code) u

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineFeatureFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineFeatureFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABSparseThresholdAffineFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABSparseThresholdAffineFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

theorem exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hfactor : G.FactorsThrough abVisibleData H)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_realizedBySharedExactABAffineDecisionListFamily
    (Z := Z) (r := r) (k := k) features
    (realizedBySharedExactABAffineDecisionListFamily_of_factorsThrough_ab
      (Z := Z) (r := r) (k := k) hfactor hreal)

section Lift

variable [Inhabited Z]

theorem exactVisibleCompressionTarget_of_invariant_and_sharedAffineFeature
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 ^ r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedAffineFeature
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedSparseThreshold
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (2 * r) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedSparseThreshold
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

theorem exactVisibleCompressionTarget_of_invariant_and_sharedDecisionList
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    (hreal :
      RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features
        (liftToABVisibleFamily (Z := Z) (k := k) G)) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G (r + 1) := by
  exact exactVisibleCompressionTarget_of_factorsThrough_ab_and_sharedDecisionList
    (Z := Z) (r := r) (k := k)
    (factorsThrough_abVisibleData_of_invariant (Z := Z) (k := k) hinv)
    hreal

end Lift

end

end Mettapedia.Computability.PNP

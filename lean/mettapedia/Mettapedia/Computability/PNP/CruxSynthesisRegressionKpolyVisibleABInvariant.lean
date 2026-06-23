import Mettapedia.Computability.PNP.CruxKpolyCoverageInvariantMass

/-!
# CruxSynthesisRegressionKpolyVisibleABInvariant

AB-visible invariant mass and non-surjectivity regressions for visible Kpoly anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_not_exists_predict_eq_of_abVisibleInvariant_separating_rule_regression
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {rule : ExactVisiblePostSwitchSurface Z k → Bool}
    (hsep : ABFiberSeparatingRule (Z := Z) (k := k) rule) :
    ¬ ∃ i, G.predict i = rule := by
  exact
    kpolyCoverage_anchor_not_exists_predict_eq_of_abVisibleInvariant_of_abFiberSeparatingRule
      hinv hsep

theorem kpoly_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G) :
    ¬ ∃ i, G.predict i = boolZProjectionRule (k := k) := by
  exact
    kpolyCoverage_anchor_not_exists_predict_eq_boolZProjectionRule_of_abVisibleInvariant
      hinv

theorem kpoly_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_regression
    {Z : Type*} {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x := by
  exact
    kpolyCoverage_anchor_exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      hinv (μ := μ) (target := target) i hab hsep huμ hvμ

theorem kpoly_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    kpolyCoverage_anchor_exists_pos_mass_disagreement_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) i hfalse htrue

theorem kpoly_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 := by
  exact
    kpolyCoverage_anchor_agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
      hinv (μ := μ) (target := target) i hab hsep huμ hvμ

theorem kpoly_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    kpolyCoverage_anchor_agreementMass_lt_one_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) i hfalse htrue

theorem kpoly_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_regression
    {Z : Type*} [Fintype Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  exact
    kpolyCoverage_anchor_not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
      hinv (μ := μ) (target := target) hab hsep huμ hvμ

theorem kpoly_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant_regression
    {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  exact
    kpolyCoverage_anchor_not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      hinv (μ := μ) hfalse htrue

theorem kpoly_anchor_not_surjective_predict_of_abVisibleInvariant_nontrivial_regression
    {Z : Type*} [Nontrivial Z] {k : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G) :
    ¬ Function.Surjective G.predict := by
  exact
    kpolyCoverage_anchor_not_surjective_predict_of_abVisibleInvariant_of_nontrivial
      hinv

end Mettapedia.Computability.PNP.CruxSynthesisRegression

import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionCore

/-!
# P vs NP crux: support-level AB-fiber separation consequences

This module upgrades raw AB-fiber separation into positive-mass disagreement and
agreement-mass obstructions.
-/

namespace Mettapedia.Computability.PNP
section Core

variable {Z : Type*} {k : ℕ}

/-- An invariant predictor cannot agree with a target on both sides of a
same-`(a,b)` fiber that the target separates. -/
theorem exists_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
    {target predict : ExactVisiblePostSwitchSurface Z k → Bool}
    (hpredict : ABFiberInvariantRule (Z := Z) (k := k) predict)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v) :
    predict u ≠ target u ∨ predict v ≠ target v := by
  by_cases hu : predict u = target u
  · right
    intro hv
    have hp : predict u = predict v := hpredict u v hab
    exact hsep (hu.symm.trans (hp.trans hv))
  · exact Or.inl hu

/-- Support-level form: if a distribution puts positive mass on both sides of a
same-`(a,b)` fiber separated by the target, an invariant predictor has a
positive-mass disagreement point. -/
theorem exists_pos_mass_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target predict : ExactVisiblePostSwitchSurface Z k → Bool}
    (hpredict : ABFiberInvariantRule (Z := Z) (k := k) predict)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ predict x ≠ target x := by
  rcases
      exists_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
        (Z := Z) (k := k) (target := target) (predict := predict)
        hpredict hab hsep with hbad | hbad
  · exact ⟨u, huμ, hbad⟩
  · exact ⟨v, hvμ, hbad⟩

/-- Indexed-family support-level form for raw `(a,b)`-invariant exact visible
families. -/
theorem exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
    {Index : Type*}
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
    exists_pos_mass_disagreement_of_abFiberInvariantRule_of_abFiberSeparation
      (Z := Z) (k := k) (μ := μ) (target := target) (predict := G.predict i)
      (fun u v hab => hinv i u v hab) hab hsep huμ hvμ

/-- Factor-through form of the support-level obstruction. -/
theorem exists_pos_mass_disagreement_of_factorsThrough_abVisibleData_predict_of_abFiberSeparation
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ target x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) i hab hsep huμ hvμ

/-- Agreement-mass form: on any positive-mass same-`(a,b)` separating fiber,
an invariant predictor has agreement mass strictly below one. -/
theorem agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
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
  rcases
      exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
        (Z := Z) (k := k) hinv (μ := μ) (target := target) i
        hab hsep huμ hvμ with ⟨x, hxμ, hxdis⟩
  exact agreementMass_lt_one_of_pos_mass_disagreement
    (μ := μ) (target := target) (predict := G.predict i) hxμ hxdis

/-- Factor-through agreement-mass form of the same support obstruction. -/
theorem agreementMass_lt_one_of_factorsThrough_abVisibleData_predict_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    (i : Index)
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    agreementMass μ target (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) i hab hsep huμ hvμ

/-- Family-level agreement-mass form: no raw `(a,b)`-invariant exact family can
contain a predictor with perfect agreement mass against a target that separates
two positive-mass points in one same-`(a,b)` fiber. -/
theorem not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hinv : ABVisibleInvariant (Z := Z) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  rintro ⟨i, hi⟩
  exact
    (ne_of_lt
      (agreementMass_lt_one_of_abVisibleInvariant_predict_of_abFiberSeparation
        (Z := Z) (k := k) hinv (μ := μ) (target := target) i
        hab hsep huμ hvμ))
      hi

/-- Factor-through family-level agreement-mass obstruction. -/
theorem not_exists_agreementMass_eq_one_of_factorsThrough_abVisibleData_of_abFiberSeparation
    [Fintype Z]
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Z k)}
    {target : ExactVisiblePostSwitchSurface Z k → Bool}
    {u v : ExactVisiblePostSwitchSurface Z k}
    (hab : abVisibleData u = abVisibleData v)
    (hsep : target u ≠ target v)
    (huμ : μ u ≠ 0) (hvμ : μ v ≠ 0) :
    ¬ ∃ i, agreementMass μ target (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_of_abVisibleInvariant_of_abFiberSeparation
      (Z := Z) (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Z) (k := k) hfactor)
      (μ := μ) (target := target) hab hsep huμ hvμ

end Core

end Mettapedia.Computability.PNP

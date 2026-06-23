import Mettapedia.Computability.PNP.ABVisibleInvariantSurjectivityObstructionSupport

/-!
# P vs NP crux: concrete hidden-`z` AB-invariance obstruction

This module specializes the support/agreement-mass obstruction to the hidden
`z` projection target over `Bool`.
-/

namespace Mettapedia.Computability.PNP
section Core

variable {k : ℕ}

/-- Concrete hidden-`z` readout support obstruction: any raw `(a,b)`-invariant
predictor disagrees with the hidden-bit projection on positive mass whenever the
measure gives positive mass to the two hidden-bit points with the same default
raw `(a,b)` data. -/
theorem exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  let u : ExactVisiblePostSwitchSurface Bool k := ⟨false, default, default⟩
  let v : ExactVisiblePostSwitchSurface Bool k := ⟨true, default, default⟩
  refine
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_of_abFiberSeparation
      (Z := Bool) (k := k) (G := G) hinv
      (μ := μ) (target := boolZProjectionRule (k := k)) i
      (u := u) (v := v) ?_ ?_ ?_ ?_
  · rfl
  · simp [boolZProjectionRule, u, v]
  · simpa [u] using hfalse
  · simpa [v] using htrue

/-- Factor-through concrete hidden-`z` readout support obstruction. -/
theorem exists_pos_mass_disagreement_of_factorsThrough_abVisibleData_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ∃ x, μ x ≠ 0 ∧ G.predict i x ≠ boolZProjectionRule (k := k) x := by
  exact
    exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) i hfalse htrue

/-- Concrete agreement-mass form for the hidden-`z` readout target. -/
theorem agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  rcases
      exists_pos_mass_disagreement_of_abVisibleInvariant_predict_boolZProjectionRule
        (k := k) hinv (μ := μ) i hfalse htrue with ⟨x, hxμ, hxdis⟩
  exact agreementMass_lt_one_of_pos_mass_disagreement
    (μ := μ) (target := boolZProjectionRule (k := k)) (predict := G.predict i)
    hxμ hxdis

/-- Factor-through concrete agreement-mass form for the hidden-`z` readout
target. -/
theorem agreementMass_lt_one_of_factorsThrough_abVisibleData_predict_boolZProjectionRule
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (i : Index)
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) < 1 := by
  exact
    agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) i hfalse htrue

/-- Family-level concrete agreement-mass obstruction for the hidden-`z`
readout target. -/
theorem not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    (hinv : ABVisibleInvariant (Z := Bool) (k := k) G)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k)) (G.predict i) = 1 := by
  rintro ⟨i, hi⟩
  exact
    (ne_of_lt
      (agreementMass_lt_one_of_abVisibleInvariant_predict_boolZProjectionRule
        (k := k) hinv (μ := μ) i hfalse htrue))
      hi

/-- Factor-through family-level concrete agreement-mass obstruction for the
hidden-`z` readout target. -/
theorem not_exists_agreementMass_eq_one_boolZProjectionRule_of_factorsThrough_abVisibleData
    {Index : Type*}
    {G : ExactVisibleSwitchedFamily Bool k Index}
    {H : ABVisibleSwitchedFamily k Index}
    (hfactor : G.FactorsThrough abVisibleData H)
    {μ : PMF (ExactVisiblePostSwitchSurface Bool k)}
    (hfalse : μ ⟨false, default, default⟩ ≠ 0)
    (htrue : μ ⟨true, default, default⟩ ≠ 0) :
    ¬ ∃ i, agreementMass μ (boolZProjectionRule (k := k))
      (G.predict i) = 1 := by
  exact
    not_exists_agreementMass_eq_one_boolZProjectionRule_of_abVisibleInvariant
      (k := k)
      (abVisibleInvariant_of_factorsThrough_abVisibleData
        (Z := Bool) (k := k) hfactor)
      (μ := μ) hfalse htrue

end Core

end Mettapedia.Computability.PNP

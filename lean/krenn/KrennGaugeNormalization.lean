import KrennOfficialGauge

/-!
# Integral gauge normalization

This file supplies the generic algebra behind the gauge-normalization step.
Fifteen independent unit parameters determine a product-one vertex-colour
gauge: the factors at vertices `0,...,4` are the parameters, and the factor
at vertex `5` is their inverse product in each colour.

The second half proves that a checked integer right inverse of a finite
exponent table constructs simultaneous inverse monomials.  This is the
root-free normalization mechanism needed to connect the finite normalized
case tables to the official equations.
-/

namespace Krenn.GaugeNormalization

open MonochromaticQuantumGraph
open scoped BigOperators

/-- The product-one unit gauge determined by the fifteen free parameters at
vertices `0,...,4`. -/
def parameterUnitGauge (x : Fin 5 → Fin 3 → ℂˣ)
    (v : Fin 6) (c : Fin 3) : ℂˣ :=
  Fin.lastCases ((∏ u, x u c)⁻¹) (fun u => x u c) v

/-- The complex-valued gauge obtained by coercing `parameterUnitGauge`. -/
def parameterGauge (x : Fin 5 → Fin 3 → ℂˣ)
    (v : Fin 6) (c : Fin 3) : ℂ :=
  parameterUnitGauge x v c

theorem parameterGauge_productOne (x : Fin 5 → Fin 3 → ℂˣ) (c : Fin 3) :
    ∏ v, parameterGauge x v c = 1 := by
  rw [Fin.prod_univ_castSucc]
  simp only [parameterGauge, parameterUnitGauge, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  have hcoe : (↑(∏ u, x u c) : ℂ) = ∏ u, (x u c : ℂ) := by
    exact Units.coe_prod (fun u : Fin 5 => x u c) Finset.univ
  rw [← hcoe]
  exact Units.mul_inv (∏ u, x u c)

theorem parameterGauge_nonzero (x : Fin 5 → Fin 3 → ℂˣ)
    (v : Fin 6) (c : Fin 3) : parameterGauge x v c ≠ 0 := by
  exact Units.ne_zero _

/-- Applying a parameter gauge preserves the complete official equation
system. -/
theorem eqSystemN_parameterGauge (x : Fin 5 → Fin 3 → ℂˣ)
    (W : WeightsN 6 3 ℂ) (hW : EqSystemN 6 3 W) :
    EqSystemN 6 3 (Krenn.OfficialGauge.gauge (parameterGauge x) W) := by
  exact Krenn.OfficialGauge.eqSystemN_gauge (parameterGauge x) W
    (parameterGauge_productOne x) hW

theorem parameterGauge_entry_eq_zero_iff (x : Fin 5 → Fin 3 → ℂˣ)
    (W : WeightsN 6 3 ℂ) (edge : EdgeN 6 3) :
    Krenn.OfficialGauge.gauge (parameterGauge x) W edge = 0 ↔ W edge = 0 := by
  exact Krenn.OfficialGauge.gauge_entry_eq_zero_iff
    (parameterGauge x) W (parameterGauge_nonzero x) edge

/-- A finite multiplicative monomial with integer exponents. -/
def monomial {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : ι → G) (exponent : ι → ℤ) : G :=
  ∏ i, a i ^ exponent i

private theorem zpow_sum_finset {G ι : Type*} [CommGroup G]
    (a : G) (exponent : ι → ℤ) (s : Finset ι) :
    a ^ (∑ i ∈ s, exponent i) = ∏ i ∈ s, a ^ exponent i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add]

private theorem zpow_sum_univ {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : G) (exponent : ι → ℤ) :
    a ^ (∑ i, exponent i) = ∏ i, a ^ exponent i := by
  simpa using zpow_sum_finset a exponent Finset.univ

/-- Substitution of finite monomials composes their integer exponent tables. -/
theorem monomial_monomial {G ι κ : Type*} [CommGroup G]
    [Fintype ι] [Fintype κ]
    (a : κ → G) (table : ι → κ → ℤ) (row : ι → ℤ) :
    monomial (fun i => monomial a (table i)) row =
      monomial a (fun k => ∑ i, row i * table i k) := by
  classical
  simp only [monomial]
  calc
    (∏ i, (∏ k, a k ^ table i k) ^ row i) =
        ∏ i, ∏ k, (a k ^ table i k) ^ row i := by
          apply Finset.prod_congr rfl
          intro i _
          exact (Finset.prod_zpow
            (fun k => a k ^ table i k) Finset.univ (row i)).symm
    _ = ∏ k, ∏ i, (a k ^ table i k) ^ row i := Finset.prod_comm
    _ = ∏ k, a k ^ (∑ i, row i * table i k) := by
          apply Finset.prod_congr rfl
          intro k _
          rw [zpow_sum_univ]
          apply Finset.prod_congr rfl
          intro i _
          rw [mul_comm, zpow_mul]

theorem monomial_add {G ι : Type*} [CommGroup G] [Fintype ι]
    (a : ι → G) (left right : ι → ℤ) :
    monomial a (fun i => left i + right i) =
      monomial a left * monomial a right := by
  classical
  simp [monomial, zpow_add, Finset.prod_mul_distrib]

/-- If `rightInverse` is an integer right inverse for the exponent rows, then
the monomials with its negated columns scale every selected value by exactly
its inverse.  No roots or divisibility assumptions enter the construction. -/
theorem monomial_of_neg_rightInverse {G ι κ : Type*} [CommGroup G]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (a : κ → G) (rightInverse : ι → κ → ℤ) (row : κ → ι → ℤ)
    (hRight : ∀ k l,
      ∑ i, row k i * rightInverse i l = if k = l then 1 else 0)
    (k : κ) :
    monomial
        (fun i => monomial a (fun l => -rightInverse i l))
        (row k) = (a k)⁻¹ := by
  rw [monomial_monomial]
  unfold monomial
  have hexponent : ∀ l, (∑ i, row k i * -rightInverse i l) =
      if l = k then -1 else 0 := by
    intro l
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, hRight]
    by_cases h : k = l
    · subst l
      simp
    · simp [h, Ne.symm h]
  simp_rw [hexponent]
  simp [zpow_neg]

/-- The fifteen free gauge parameters: five vertices by three colours. -/
abbrev GaugeParameter := Fin 5 × Fin 3

def unitParameters (x : Fin 5 → Fin 3 → ℂˣ)
    (parameter : GaugeParameter) : ℂˣ :=
  x parameter.1 parameter.2

/-- Integer exponent of one free parameter in one vertex-colour gauge
factor.  At vertex five every same-colour parameter has exponent `-1`; at
vertices zero through four exactly one parameter has exponent `1`. -/
def vertexExponent (v : Fin 6) (c : Fin 3)
    (parameter : GaugeParameter) : ℤ :=
  Fin.lastCases (if parameter.2 = c then -1 else 0)
    (fun u => if parameter = (u, c) then 1 else 0) v

/-- Integer exponent row for the gauge factor of one physical channel. -/
def channelExponent (edge : EdgeN 6 3) (parameter : GaugeParameter) : ℤ :=
  vertexExponent edge.u edge.i parameter +
    vertexExponent edge.v edge.j parameter

/-- Finite proof object licensing simultaneous normalization of five selected
channels.  The final field is kernel-checkable integer arithmetic. -/
structure NormalizationDatum where
  caseIndex : Nat
  selected : Fin 5 → EdgeN 6 3
  rightInverse : GaugeParameter → Fin 5 → ℤ
  rightInverse_ok : ∀ k l,
    ∑ parameter,
      channelExponent (selected k) parameter * rightInverse parameter l =
        if k = l then 1 else 0

theorem parameterUnitGauge_eq_monomial (x : Fin 5 → Fin 3 → ℂˣ)
    (v : Fin 6) (c : Fin 3) :
    parameterUnitGauge x v c =
      monomial (unitParameters x) (vertexExponent v c) := by
  refine Fin.lastCases ?_ (fun u => ?_) v
  · rw [parameterUnitGauge, Fin.lastCases_last]
    unfold monomial vertexExponent unitParameters
    rw [Fintype.prod_prod_type]
    simp only [Fin.lastCases_last]
    simp [zpow_neg]
  · simp [parameterUnitGauge, monomial, vertexExponent, unitParameters]

theorem parameterUnitGauge_mul_eq_monomial
    (x : Fin 5 → Fin 3 → ℂˣ) (edge : EdgeN 6 3) :
    parameterUnitGauge x edge.u edge.i *
        parameterUnitGauge x edge.v edge.j =
      monomial (unitParameters x) (channelExponent edge) := by
  rw [parameterUnitGauge_eq_monomial, parameterUnitGauge_eq_monomial]
  exact (monomial_add _ _ _).symm

/-- The parameter assignment obtained from negating an integer right inverse
of the selected-channel exponent table. -/
def normalizationParameters {κ : Type*} [Fintype κ]
    (selectedValues : κ → ℂˣ)
    (rightInverse : GaugeParameter → κ → ℤ)
    (u : Fin 5) (c : Fin 3) : ℂˣ :=
  monomial selectedValues (fun k => -rightInverse (u, c) k)

theorem normalized_parameter_factor {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (selected : κ → EdgeN 6 3)
    (selectedValues : κ → ℂˣ)
    (rightInverse : GaugeParameter → κ → ℤ)
    (hRight : ∀ k l,
      ∑ parameter,
        channelExponent (selected k) parameter * rightInverse parameter l =
          if k = l then 1 else 0)
    (k : κ) :
    parameterUnitGauge
        (normalizationParameters selectedValues rightInverse)
        (selected k).u (selected k).i *
      parameterUnitGauge
        (normalizationParameters selectedValues rightInverse)
        (selected k).v (selected k).j = (selectedValues k)⁻¹ := by
  rw [parameterUnitGauge_mul_eq_monomial]
  exact monomial_of_neg_rightInverse selectedValues rightInverse
    (fun l => channelExponent (selected l)) hRight k

/-- A checked integer right inverse therefore constructs a product-one gauge
which sends all supplied nonzero selected channels to one simultaneously. -/
theorem normalized_gauge_entry {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (W : WeightsN 6 3 ℂ) (selected : κ → EdgeN 6 3)
    (selectedValues : κ → ℂˣ)
    (rightInverse : GaugeParameter → κ → ℤ)
    (hValues : ∀ k, (selectedValues k : ℂ) = W (selected k))
    (hRight : ∀ k l,
      ∑ parameter,
        channelExponent (selected k) parameter * rightInverse parameter l =
          if k = l then 1 else 0)
    (k : κ) :
    Krenn.OfficialGauge.gauge
        (parameterGauge
          (normalizationParameters selectedValues rightInverse)) W
        (selected k) = 1 := by
  have hfactor := normalized_parameter_factor
    selected selectedValues rightInverse hRight k
  have hfactorCoe :
      (parameterUnitGauge
          (normalizationParameters selectedValues rightInverse)
          (selected k).u (selected k).i : ℂ) *
        (parameterUnitGauge
          (normalizationParameters selectedValues rightInverse)
          (selected k).v (selected k).j : ℂ) =
        ((selectedValues k)⁻¹ : ℂ) := by
    exact_mod_cast hfactor
  rw [Krenn.OfficialGauge.gauge, ← hValues k]
  change
    (parameterUnitGauge
        (normalizationParameters selectedValues rightInverse)
        (selected k).u (selected k).i : ℂ) *
      (parameterUnitGauge
        (normalizationParameters selectedValues rightInverse)
        (selected k).v (selected k).j : ℂ) *
      (selectedValues k : ℂ) = 1
  rw [hfactorCoe]
  simpa using Units.inv_mul (selectedValues k)

/-- Any official witness with the five datum channels live can be transported
to a witness in which those channels are all exactly one, without changing
the zero/nonzero support of any channel. -/
theorem exists_normalized_witness (datum : NormalizationDatum)
    (W : WeightsN 6 3 ℂ) (hW : EqSystemN 6 3 W)
    (live : ∀ k, W (datum.selected k) ≠ 0) :
    ∃ normalized : WeightsN 6 3 ℂ,
      EqSystemN 6 3 normalized ∧
      (∀ edge, normalized edge = 0 ↔ W edge = 0) ∧
      (∀ k, normalized (datum.selected k) = 1) := by
  let selectedValues : Fin 5 → ℂˣ := fun k => Units.mk0 _ (live k)
  let parameters := normalizationParameters selectedValues datum.rightInverse
  let normalized := Krenn.OfficialGauge.gauge (parameterGauge parameters) W
  refine ⟨normalized, eqSystemN_parameterGauge parameters W hW, ?_, ?_⟩
  · intro edge
    exact parameterGauge_entry_eq_zero_iff parameters W edge
  · intro k
    exact normalized_gauge_entry W datum.selected selectedValues
      datum.rightInverse (fun _ => rfl) datum.rightInverse_ok k

#print axioms Krenn.GaugeNormalization.eqSystemN_parameterGauge
#print axioms Krenn.GaugeNormalization.monomial_of_neg_rightInverse
#print axioms Krenn.GaugeNormalization.normalized_gauge_entry
#print axioms Krenn.GaugeNormalization.exists_normalized_witness

end Krenn.GaugeNormalization

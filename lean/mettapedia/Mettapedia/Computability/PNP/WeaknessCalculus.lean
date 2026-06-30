import Mettapedia.Computability.PNP.NoThreadingLemma

/-!
# Finite weakness calculus

This file records the reusable finite core behind the PNP steelman repair.
There is no measure theory here: a task is a finite list of predictors, each
with a finite budget and a natural-number value.  The spectrum is the best
listed value available below a budget.  The gap is the poly-budget spectrum
minus the local-budget spectrum.

The open SW/domination input is represented as an explicit structure.  No
unconditional P versus NP separation is asserted.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-- Finite budget lattice with levels `0, ..., budgetTop`. -/
abbrev WeaknessBudget (budgetTop : Nat) :=
  Fin (budgetTop + 1)

/-- A predictor has a finite budget cost and a finite success/value score. -/
structure WeaknessPredictor (budgetTop : Nat) where
  cost : WeaknessBudget budgetTop
  value : Nat
deriving DecidableEq, Repr

/-- A finite weakness task with local and poly budget cuts. -/
structure WeaknessTask (budgetTop : Nat) where
  predictors : List (WeaknessPredictor budgetTop)
  localBudget : WeaknessBudget budgetTop
  polyBudget : WeaknessBudget budgetTop
deriving Repr

/-- Best listed value achievable below a budget. -/
def spectrumList {budgetTop : Nat} :
    List (WeaknessPredictor budgetTop) -> WeaknessBudget budgetTop -> Nat
  | [], _ => 0
  | p :: ps, b =>
      if p.cost ≤ b then
        max p.value (spectrumList ps b)
      else
        spectrumList ps b

theorem value_le_spectrumList_of_mem
    {budgetTop : Nat} {ps : List (WeaknessPredictor budgetTop)}
    {p : WeaknessPredictor budgetTop} {b : WeaknessBudget budgetTop}
    (hmem : p ∈ ps) (hcost : p.cost ≤ b) :
    p.value ≤ spectrumList ps b := by
  induction ps with
  | nil =>
      cases hmem
  | cons q qs ih =>
      cases hmem with
      | head =>
          simp [spectrumList, hcost]
      | tail _ htail =>
          by_cases hq : q.cost ≤ b
          · exact
              le_trans (ih htail)
                (by
                  simp [spectrumList, hq])
          · simpa [spectrumList, hq] using ih htail

theorem spectrumList_mono
    {budgetTop : Nat} {ps : List (WeaknessPredictor budgetTop)}
    {b b' : WeaknessBudget budgetTop} (hbb : b ≤ b') :
    spectrumList ps b ≤ spectrumList ps b' := by
  induction ps with
  | nil =>
      simp [spectrumList]
  | cons p ps ih =>
      by_cases hp : p.cost ≤ b
      · have hp' : p.cost ≤ b' := le_trans hp hbb
        simpa [spectrumList, hp, hp'] using
          max_le_max (le_rfl : p.value ≤ p.value) ih
      · by_cases hp' : p.cost ≤ b'
        · simpa [spectrumList, hp, hp'] using
            le_trans ih (le_max_right p.value (spectrumList ps b'))
        · simpa [spectrumList, hp, hp'] using ih

namespace WeaknessTask

/-- The finite weakness spectrum of a task. -/
def spectrum {budgetTop : Nat} (T : WeaknessTask budgetTop)
    (b : WeaknessBudget budgetTop) : Nat :=
  spectrumList T.predictors b

/-- The local-budget end of the spectrum. -/
def localSpectrum {budgetTop : Nat} (T : WeaknessTask budgetTop) : Nat :=
  T.spectrum T.localBudget

/-- The poly-budget end of the spectrum. -/
def polySpectrum {budgetTop : Nat} (T : WeaknessTask budgetTop) : Nat :=
  T.spectrum T.polyBudget

/-- Spectrum gap `Delta_T = spectrum_poly T - spectrum_local T`. -/
def spectrumGap {budgetTop : Nat} (T : WeaknessTask budgetTop) : Nat :=
  T.polySpectrum - T.localSpectrum

theorem spectrum_mono {budgetTop : Nat} (T : WeaknessTask budgetTop)
    {b b' : WeaknessBudget budgetTop} (hbb : b ≤ b') :
    T.spectrum b ≤ T.spectrum b' :=
  spectrumList_mono hbb

end WeaknessTask

/-- The local budget is below the poly budget. -/
def BudgetOrdered {budgetTop : Nat} (T : WeaknessTask budgetTop) : Prop :=
  T.localBudget ≤ T.polyBudget

/-- Domination means the poly spectrum gives no more value than the local one. -/
def SpectrumDomination {budgetTop : Nat} (T : WeaknessTask budgetTop) : Prop :=
  T.polySpectrum ≤ T.localSpectrum

theorem localSpectrum_le_polySpectrum_of_budgetOrdered
    {budgetTop : Nat} {T : WeaknessTask budgetTop}
    (hBudget : BudgetOrdered T) :
    T.localSpectrum ≤ T.polySpectrum :=
  T.spectrum_mono hBudget

theorem spectrumGap_nonneg {budgetTop : Nat}
    (T : WeaknessTask budgetTop) :
    0 ≤ T.spectrumGap :=
  Nat.zero_le _

theorem spectrumGap_eq_zero_iff_domination {budgetTop : Nat}
    (T : WeaknessTask budgetTop) :
    T.spectrumGap = 0 ↔ SpectrumDomination T := by
  unfold WeaknessTask.spectrumGap SpectrumDomination
  exact Nat.sub_eq_zero_iff_le

theorem spectrumGap_eq_zero_iff_flat {budgetTop : Nat}
    {T : WeaknessTask budgetTop} (hBudget : BudgetOrdered T) :
    T.spectrumGap = 0 ↔ T.localSpectrum = T.polySpectrum := by
  constructor
  · intro hgap
    have hdom : SpectrumDomination T :=
      (spectrumGap_eq_zero_iff_domination T).mp hgap
    exact le_antisymm
      (localSpectrum_le_polySpectrum_of_budgetOrdered hBudget) hdom
  · intro hflat
    exact
      (spectrumGap_eq_zero_iff_domination T).mpr
        (by simp [SpectrumDomination, hflat])

/-- Change only the poly-budget cut. -/
def WeaknessTask.withPolyBudget {budgetTop : Nat}
    (T : WeaknessTask budgetTop) (b : WeaknessBudget budgetTop) :
    WeaknessTask budgetTop :=
  { T with polyBudget := b }

theorem spectrumGap_mono_polyBudget {budgetTop : Nat}
    (T : WeaknessTask budgetTop) {b b' : WeaknessBudget budgetTop}
    (hbb : b ≤ b') :
    (T.withPolyBudget b).spectrumGap ≤
      (T.withPolyBudget b').spectrumGap := by
  dsimp [WeaknessTask.withPolyBudget, WeaknessTask.spectrumGap,
    WeaknessTask.polySpectrum, WeaknessTask.localSpectrum,
    WeaknessTask.spectrum]
  exact Nat.sub_le_sub_right (spectrumList_mono hbb) _

/--
Data-processing relation: every target predictor is obtained from some source
predictor with no larger source cost and no smaller source value.
-/
def DataProcessing {budgetTop : Nat}
    (source target : WeaknessTask budgetTop) : Prop :=
  ∀ q, q ∈ target.predictors ->
    ∃ p, p ∈ source.predictors ∧ p.cost ≤ q.cost ∧ q.value ≤ p.value

theorem spectrumList_dataProcessing
    {budgetTop : Nat}
    {source target : List (WeaknessPredictor budgetTop)}
    (h : ∀ q, q ∈ target ->
      ∃ p, p ∈ source ∧ p.cost ≤ q.cost ∧ q.value ≤ p.value)
    (b : WeaknessBudget budgetTop) :
    spectrumList target b ≤ spectrumList source b := by
  induction target with
  | nil =>
      simp [spectrumList]
  | cons q qs ih =>
      have htail :
          spectrumList qs b ≤ spectrumList source b := by
        exact ih (fun r hr => h r (List.Mem.tail q hr))
      by_cases hq : q.cost ≤ b
      · rcases h q (List.Mem.head qs) with ⟨p, hpMem, hpCost, hval⟩
        have hpBudget : p.cost ≤ b := le_trans hpCost hq
        have hpSpec :
            p.value ≤ spectrumList source b :=
          value_le_spectrumList_of_mem hpMem hpBudget
        have hqSpec : q.value ≤ spectrumList source b :=
          le_trans hval hpSpec
        simpa [spectrumList, hq] using max_le hqSpec htail
      · simpa [spectrumList, hq] using htail

theorem spectrum_dataProcessing {budgetTop : Nat}
    {source target : WeaknessTask budgetTop}
    (h : DataProcessing source target)
    (b : WeaknessBudget budgetTop) :
    target.spectrum b ≤ source.spectrum b :=
  spectrumList_dataProcessing h b

/-- General no-threading form reused by the weakness calculus. -/
theorem noThreading_general
    {Phi U : Type*} [Fintype Phi] [DecidableEq U]
    {u : Phi -> U} {x : Phi -> Bool}
    (hNontrivial : NontrivialWitnessBit x) :
    ¬ (Neutral u x ∧ Sufficient u x) :=
  noThreading_neutral_sufficient_blocks_nontrivial_bit hNontrivial

/--
No-threading gap witness: if equality of local and poly spectra would make a
local statistic both neutral and sufficient for a nontrivial deterministic bit,
then equality is impossible.
-/
structure NoThreadingGapWitness
    {budgetTop : Nat} {Phi U : Type*}
    [Fintype Phi] [DecidableEq U]
    (T : WeaknessTask budgetTop) (u : Phi -> U) (x : Phi -> Bool) where
  nontrivialBit : NontrivialWitnessBit x
  budgetOrdered : BudgetOrdered T
  equalityWouldThread :
    T.localSpectrum = T.polySpectrum -> Neutral u x ∧ Sufficient u x

theorem localSpectrum_ne_polySpectrum_of_noThreading
    {budgetTop : Nat} {Phi U : Type*}
    [Fintype Phi] [DecidableEq U]
    {T : WeaknessTask budgetTop} {u : Phi -> U} {x : Phi -> Bool}
    (h : NoThreadingGapWitness T u x) :
    T.localSpectrum ≠ T.polySpectrum := by
  intro hflat
  exact noThreading_general h.nontrivialBit (h.equalityWouldThread hflat)

theorem spectrumGap_pos_of_noThreading
    {budgetTop : Nat} {Phi U : Type*}
    [Fintype Phi] [DecidableEq U]
    {T : WeaknessTask budgetTop} {u : Phi -> U} {x : Phi -> Bool}
    (h : NoThreadingGapWitness T u x) :
    0 < T.spectrumGap := by
  have hle : T.localSpectrum ≤ T.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered h.budgetOrdered
  have hne : T.localSpectrum ≠ T.polySpectrum :=
    localSpectrum_ne_polySpectrum_of_noThreading h
  have hlt : T.localSpectrum < T.polySpectrum :=
    lt_of_le_of_ne hle hne
  exact Nat.sub_pos_of_lt hlt

theorem spectrumGap_pos_of_poly_value_gt_local
    {budgetTop : Nat} {T : WeaknessTask budgetTop}
    {p : WeaknessPredictor budgetTop}
    (hmem : p ∈ T.predictors) (hbudget : p.cost ≤ T.polyBudget)
    (hlocal : T.localSpectrum < p.value) :
    0 < T.spectrumGap := by
  have hpSpec : p.value ≤ T.polySpectrum :=
    value_le_spectrumList_of_mem hmem hbudget
  exact Nat.sub_pos_of_lt (lt_of_lt_of_le hlocal hpSpec)

/--
The explicit open domination input.  In the steelman route this is the
average-case witness-bit hardness/short-predictor domination principle; it is a
hypothesis, not a theorem.
-/
structure StarSWDominationHypothesis {budgetTop : Nat}
    (T : WeaknessTask budgetTop) where
  budgetOrdered : BudgetOrdered T
  domination : SpectrumDomination T

theorem spectrumGap_zero_of_starSWDomination
    {budgetTop : Nat} {T : WeaknessTask budgetTop}
    (h : StarSWDominationHypothesis T) :
    T.spectrumGap = 0 :=
  (spectrumGap_eq_zero_iff_domination T).mpr h.domination

/-! ## Two-point toy inhabitant -/

def toyWeaknessLocalPredictor : WeaknessPredictor 1 where
  cost := ⟨0, by norm_num⟩
  value := 1

def toyWeaknessGlobalPredictor : WeaknessPredictor 1 where
  cost := ⟨1, by norm_num⟩
  value := 2

def toyWeaknessTask : WeaknessTask 1 where
  predictors := [toyWeaknessLocalPredictor, toyWeaknessGlobalPredictor]
  localBudget := ⟨0, by norm_num⟩
  polyBudget := ⟨1, by norm_num⟩

def toyWeaknessPostProcessedTask : WeaknessTask 1 where
  predictors := [
    { cost := toyWeaknessLocalPredictor.cost, value := 0 },
    { cost := toyWeaknessGlobalPredictor.cost, value := 1 }
  ]
  localBudget := toyWeaknessTask.localBudget
  polyBudget := toyWeaknessTask.polyBudget

theorem toyWeaknessTask_budgetOrdered :
    BudgetOrdered toyWeaknessTask := by
  norm_num [BudgetOrdered, toyWeaknessTask]

theorem toyWeaknessTask_localSpectrum :
    toyWeaknessTask.localSpectrum = 1 := by
  norm_num [WeaknessTask.localSpectrum, WeaknessTask.spectrum,
    toyWeaknessTask, toyWeaknessLocalPredictor, toyWeaknessGlobalPredictor,
    spectrumList]

theorem toyWeaknessTask_polySpectrum :
    toyWeaknessTask.polySpectrum = 2 := by
  norm_num [WeaknessTask.polySpectrum, WeaknessTask.spectrum,
    toyWeaknessTask, toyWeaknessLocalPredictor, toyWeaknessGlobalPredictor,
    spectrumList]

theorem toyWeaknessTask_spectrumGap :
    toyWeaknessTask.spectrumGap = 1 := by
  norm_num [WeaknessTask.spectrumGap, toyWeaknessTask_localSpectrum,
    toyWeaknessTask_polySpectrum]

theorem toyWeaknessTask_spectrumGap_pos :
    0 < toyWeaknessTask.spectrumGap := by
  norm_num [toyWeaknessTask_spectrumGap]

theorem toyWeakness_globalPredictor_beats_local :
    0 < toyWeaknessTask.spectrumGap :=
  spectrumGap_pos_of_poly_value_gt_local
    (T := toyWeaknessTask) (p := toyWeaknessGlobalPredictor)
    (by simp [toyWeaknessTask])
    (by norm_num [toyWeaknessTask, toyWeaknessGlobalPredictor])
    (by
      rw [toyWeaknessTask_localSpectrum]
      norm_num [toyWeaknessGlobalPredictor])

def toyWeaknessNoThreadingGapWitness :
    NoThreadingGapWitness toyWeaknessTask
      noThreadingToyStatistic noThreadingToyWitness where
  nontrivialBit := noThreadingToyWitness_nontrivial
  budgetOrdered := toyWeaknessTask_budgetOrdered
  equalityWouldThread := by
    intro hflat
    simp [toyWeaknessTask_localSpectrum, toyWeaknessTask_polySpectrum] at hflat

theorem toyWeakness_noThreading_forces_gap :
    0 < toyWeaknessTask.spectrumGap :=
  spectrumGap_pos_of_noThreading toyWeaknessNoThreadingGapWitness

theorem toyWeakness_dataProcessing :
    DataProcessing toyWeaknessTask toyWeaknessPostProcessedTask := by
  intro q hq
  simp [toyWeaknessPostProcessedTask] at hq
  rcases hq with hq | hq
  · subst q
    refine ⟨toyWeaknessLocalPredictor, ?_, ?_, ?_⟩
    · simp [toyWeaknessTask]
    · exact le_rfl
    · norm_num [toyWeaknessLocalPredictor]
  · subst q
    refine ⟨toyWeaknessGlobalPredictor, ?_, ?_, ?_⟩
    · simp [toyWeaknessTask]
    · exact le_rfl
    · norm_num [toyWeaknessGlobalPredictor]

theorem toyWeakness_dataProcessing_local :
    toyWeaknessPostProcessedTask.localSpectrum ≤ toyWeaknessTask.localSpectrum :=
  spectrum_dataProcessing toyWeakness_dataProcessing toyWeaknessTask.localBudget

theorem toyWeakness_starSW_domination_gap_zero
    (h : StarSWDominationHypothesis toyWeaknessTask) :
    toyWeaknessTask.spectrumGap = 0 :=
  spectrumGap_zero_of_starSWDomination h

end Mettapedia.Computability.PNP

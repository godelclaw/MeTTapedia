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

/-! ## Budget-compositional finite laws -/

/--
Independent tensor spectrum over split budgets.  The product may spend `b` on
the left block and `c` on the right block, and values are added in this finite
score model.
-/
def tensorSpectrumList {leftTop rightTop : Nat} :
    List (WeaknessPredictor leftTop) ->
      List (WeaknessPredictor rightTop) ->
        WeaknessBudget leftTop -> WeaknessBudget rightTop -> Nat
  | [], qs, _b, c => spectrumList qs c
  | p :: ps, qs, b, c =>
      if p.cost ≤ b then
        max (p.value + spectrumList qs c) (tensorSpectrumList ps qs b c)
      else
        tensorSpectrumList ps qs b c

/-- Block additivity for the concrete split-budget tensor spectrum. -/
theorem tensorSpectrumList_additive
    {leftTop rightTop : Nat}
    {ps : List (WeaknessPredictor leftTop)}
    {qs : List (WeaknessPredictor rightTop)}
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) :
    tensorSpectrumList ps qs b c =
      spectrumList ps b + spectrumList qs c := by
  induction ps with
  | nil =>
      simp [tensorSpectrumList, spectrumList]
  | cons p ps ih =>
      by_cases hp : p.cost ≤ b
      · simp [tensorSpectrumList, spectrumList, hp, ih,
          max_add_add_right]
      · simp [tensorSpectrumList, spectrumList, hp, ih]

namespace WeaknessTask

/-- Concrete tensor spectrum of two finite tasks under split budgets. -/
def tensorSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) : Nat :=
  tensorSpectrumList T.predictors U.predictors b c

theorem tensorSpectrum_additive {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) :
    T.tensorSpectrum U b c = T.spectrum b + U.spectrum c :=
  tensorSpectrumList_additive b c

end WeaknessTask

/-- Local end of the tensor spectrum. -/
def tensorLocalSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  T.tensorSpectrum U T.localBudget U.localBudget

/-- Poly end of the tensor spectrum. -/
def tensorPolySpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  T.tensorSpectrum U T.polyBudget U.polyBudget

/-- Tensor gap between the split poly and split local budgets. -/
def tensorSpectrumGap {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  tensorPolySpectrum T U - tensorLocalSpectrum T U

theorem tensorLocalSpectrum_eq_add {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) :
    tensorLocalSpectrum T U = T.localSpectrum + U.localSpectrum :=
  T.tensorSpectrum_additive U T.localBudget U.localBudget

theorem tensorPolySpectrum_eq_add {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) :
    tensorPolySpectrum T U = T.polySpectrum + U.polySpectrum :=
  T.tensorSpectrum_additive U T.polyBudget U.polyBudget

theorem tensorSpectrumGap_eq_add {leftTop rightTop : Nat}
    {T : WeaknessTask leftTop} {U : WeaknessTask rightTop}
    (hT : BudgetOrdered T) (hU : BudgetOrdered U) :
    tensorSpectrumGap T U = T.spectrumGap + U.spectrumGap := by
  have hTle : T.localSpectrum ≤ T.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hT
  have hUle : U.localSpectrum ≤ U.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hU
  unfold tensorSpectrumGap tensorPolySpectrum tensorLocalSpectrum
    WeaknessTask.spectrumGap
  rw [WeaknessTask.tensorSpectrum_additive,
    WeaknessTask.tensorSpectrum_additive]
  simp only [WeaknessTask.localSpectrum, WeaknessTask.polySpectrum] at hTle hUle ⊢
  omega

/--
Independent value tensor over split budgets.  This is the finite L9 side:
independent success/value scores multiply, while the additive tensor above
records the corresponding surprisal/cost accounting.
-/
def tensorValueSpectrumList {leftTop rightTop : Nat} :
    List (WeaknessPredictor leftTop) ->
      List (WeaknessPredictor rightTop) ->
        WeaknessBudget leftTop -> WeaknessBudget rightTop -> Nat
  | [], _qs, _b, _c => 0
  | p :: ps, qs, b, c =>
      if p.cost ≤ b then
        max (p.value * spectrumList qs c)
          (tensorValueSpectrumList ps qs b c)
      else
        tensorValueSpectrumList ps qs b c

/-- Tensor-multiplicativity for the concrete split-budget value spectrum. -/
theorem tensorValueSpectrumList_multiplicative
    {leftTop rightTop : Nat}
    {ps : List (WeaknessPredictor leftTop)}
    {qs : List (WeaknessPredictor rightTop)}
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) :
    tensorValueSpectrumList ps qs b c =
      spectrumList ps b * spectrumList qs c := by
  induction ps with
  | nil =>
      simp [tensorValueSpectrumList, spectrumList]
  | cons p ps ih =>
      by_cases hp : p.cost ≤ b
      · have hmax :
          max (p.value * spectrumList qs c)
              (spectrumList ps b * spectrumList qs c) =
            max p.value (spectrumList ps b) * spectrumList qs c :=
          (max_mul p.value (spectrumList ps b) (spectrumList qs c)).symm
        simp [tensorValueSpectrumList, spectrumList, hp, ih, hmax]
      · simp [tensorValueSpectrumList, spectrumList, hp, ih]

namespace WeaknessTask

/-- Concrete independent-value tensor spectrum of two finite tasks. -/
def tensorValueSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) : Nat :=
  tensorValueSpectrumList T.predictors U.predictors b c

theorem tensorValueSpectrum_multiplicative {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) :
    T.tensorValueSpectrum U b c = T.spectrum b * U.spectrum c :=
  tensorValueSpectrumList_multiplicative b c

end WeaknessTask

/-- Local end of the independent-value tensor spectrum. -/
def tensorValueLocalSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  T.tensorValueSpectrum U T.localBudget U.localBudget

/-- Poly end of the independent-value tensor spectrum. -/
def tensorValuePolySpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  T.tensorValueSpectrum U T.polyBudget U.polyBudget

/-- Independent-value tensor gap between the split poly and local budgets. -/
def tensorValueSpectrumGap {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  tensorValuePolySpectrum T U - tensorValueLocalSpectrum T U

theorem tensorValueLocalSpectrum_eq_mul {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) :
    tensorValueLocalSpectrum T U = T.localSpectrum * U.localSpectrum :=
  T.tensorValueSpectrum_multiplicative U T.localBudget U.localBudget

theorem tensorValuePolySpectrum_eq_mul {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) :
    tensorValuePolySpectrum T U = T.polySpectrum * U.polySpectrum :=
  T.tensorValueSpectrum_multiplicative U T.polyBudget U.polyBudget

/-- Product-gap arithmetic for finite independent values. -/
theorem nat_productGap_eq_crossTerms {A B C D : Nat}
    (hBA : B ≤ A) (hDC : D ≤ C) :
    A * C - B * D = (A - B) * C + B * (C - D) := by
  have hA : A * C = (A - B) * C + B * C := by
    calc
      A * C = ((A - B) + B) * C := by
        rw [Nat.sub_add_cancel hBA]
      _ = (A - B) * C + B * C := by ring
  have hC : B * C = B * (C - D) + B * D := by
    calc
      B * C = B * ((C - D) + D) := by
        rw [Nat.sub_add_cancel hDC]
      _ = B * (C - D) + B * D := by ring
  omega

/--
Independent-value tensor gap in factor terms.  The gap is not simply additive
before taking surprisal; it is the usual product cross-term decomposition.
-/
theorem tensorValueSpectrumGap_eq_crossTerms {leftTop rightTop : Nat}
    {T : WeaknessTask leftTop} {U : WeaknessTask rightTop}
    (hT : BudgetOrdered T) (hU : BudgetOrdered U) :
    tensorValueSpectrumGap T U =
      T.spectrumGap * U.polySpectrum +
        T.localSpectrum * U.spectrumGap := by
  have hTle : T.localSpectrum ≤ T.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hT
  have hUle : U.localSpectrum ≤ U.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hU
  unfold tensorValueSpectrumGap tensorValuePolySpectrum
    tensorValueLocalSpectrum WeaknessTask.spectrumGap
  rw [WeaknessTask.tensorValueSpectrum_multiplicative,
    WeaknessTask.tensorValueSpectrum_multiplicative]
  exact nat_productGap_eq_crossTerms hTle hUle

/-- Nat-budgeted predictor used for sequential composition with overhead. -/
structure NatBudgetPredictor where
  cost : Nat
  value : Nat
deriving DecidableEq, Repr

/-- Best listed value achievable under a Nat budget. -/
def natSpectrumList : List NatBudgetPredictor -> Nat -> Nat
  | [], _ => 0
  | p :: ps, b =>
      if p.cost ≤ b then
        max p.value (natSpectrumList ps b)
      else
        natSpectrumList ps b

theorem value_le_natSpectrumList_of_mem
    {ps : List NatBudgetPredictor} {p : NatBudgetPredictor} {b : Nat}
    (hmem : p ∈ ps) (hcost : p.cost ≤ b) :
    p.value ≤ natSpectrumList ps b := by
  induction ps with
  | nil =>
      cases hmem
  | cons q qs ih =>
      cases hmem with
      | head =>
          simp [natSpectrumList, hcost]
      | tail _ htail =>
          by_cases hq : q.cost ≤ b
          · exact
              le_trans (ih htail)
                (by
                  simp [natSpectrumList, hq])
          · simpa [natSpectrumList, hq] using ih htail

/-- Zero predictor used to make every finite spectrum witnessable. -/
def zeroWeaknessPredictor (budgetTop : Nat) :
    WeaknessPredictor budgetTop where
  cost := ⟨0, Nat.succ_pos _⟩
  value := 0

/-- Add the zero predictor without changing the intended spectrum. -/
def withZeroPredictor {budgetTop : Nat}
    (ps : List (WeaknessPredictor budgetTop)) :
    List (WeaknessPredictor budgetTop) :=
  zeroWeaknessPredictor budgetTop :: ps

theorem exists_spectrumList_witness
    {budgetTop : Nat} (ps : List (WeaknessPredictor budgetTop))
    (b : WeaknessBudget budgetTop) :
    ∃ p, p ∈ withZeroPredictor ps ∧ p.cost ≤ b ∧
      p.value = spectrumList ps b := by
  induction ps with
  | nil =>
      refine ⟨zeroWeaknessPredictor budgetTop, ?_, ?_, ?_⟩
      · simp [withZeroPredictor]
      · simp [zeroWeaknessPredictor]
      · simp [spectrumList, zeroWeaknessPredictor]
  | cons p ps ih =>
      by_cases hp : p.cost ≤ b
      · by_cases hmax : p.value ≤ spectrumList ps b
        · rcases ih with ⟨q, hqMem, hqCost, hqValue⟩
          refine ⟨q, ?_, hqCost, ?_⟩
          · simp [withZeroPredictor] at hqMem ⊢
            rcases hqMem with hzero | htail
            · exact Or.inl hzero
            · exact Or.inr (Or.inr htail)
          · simp [spectrumList, hp, hqValue, max_eq_right hmax]
        · refine ⟨p, ?_, hp, ?_⟩
          · simp [withZeroPredictor]
          · have hle : spectrumList ps b ≤ p.value :=
              le_of_lt (lt_of_not_ge hmax)
            simp [spectrumList, hp, max_eq_left hle]
      · rcases ih with ⟨q, hqMem, hqCost, hqValue⟩
        refine ⟨q, ?_, hqCost, ?_⟩
        · simp [withZeroPredictor] at hqMem ⊢
          rcases hqMem with hzero | htail
          · exact Or.inl hzero
          · exact Or.inr (Or.inr htail)
        · simp [spectrumList, hp, hqValue]

/--
One sequentially composed predictor: run a left predictor, then a right
predictor, paying a finite wrapper/scheduling defect.
-/
def sequentialPredictor {leftTop rightTop : Nat} (defect : Nat)
    (p : WeaknessPredictor leftTop) (q : WeaknessPredictor rightTop) :
    NatBudgetPredictor where
  cost := p.cost.val + q.cost.val + defect
  value := p.value + q.value

/-- Finite list of all baseline-closed sequential predictor pairs. -/
def sequentialPredictors {leftTop rightTop : Nat}
    (ps : List (WeaknessPredictor leftTop))
    (qs : List (WeaknessPredictor rightTop))
    (defect : Nat) : List NatBudgetPredictor :=
  (withZeroPredictor ps).flatMap fun p =>
    (withZeroPredictor qs).map fun q => sequentialPredictor defect p q

theorem sequentialPredictor_mem {leftTop rightTop : Nat}
    {ps : List (WeaknessPredictor leftTop)}
    {qs : List (WeaknessPredictor rightTop)}
    {defect : Nat} {p : WeaknessPredictor leftTop}
    {q : WeaknessPredictor rightTop}
    (hp : p ∈ withZeroPredictor ps)
    (hq : q ∈ withZeroPredictor qs) :
    sequentialPredictor defect p q ∈ sequentialPredictors ps qs defect := by
  simp [sequentialPredictors]
  exact ⟨p, hp, q, hq, rfl⟩

/-- Sequential composition spectrum under one Nat budget and a fixed defect. -/
def sequentialSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (defect budget : Nat) : Nat :=
  natSpectrumList (sequentialPredictors T.predictors U.predictors defect)
    budget

/-- Split sequential spectrum: the value promised by a chosen split budget. -/
def sequentialSplitSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop) : Nat :=
  T.spectrum b + U.spectrum c

/-- Split sequential budget with the explicit lax defect. -/
def sequentialSplitBudget {leftTop rightTop : Nat}
    (b : WeaknessBudget leftTop) (c : WeaknessBudget rightTop)
    (defect : Nat) : Nat :=
  b.val + c.val + defect

/--
Chain-rule lower bound: the split plan with budgets `b` and `c` is available in
the sequential composite after paying the finite defect.
-/
theorem sequential_chainRule_subadditive {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (defect : Nat) (b : WeaknessBudget leftTop)
    (c : WeaknessBudget rightTop) :
    sequentialSplitSpectrum T U b c ≤
      sequentialSpectrum T U defect (sequentialSplitBudget b c defect) := by
  rcases exists_spectrumList_witness T.predictors b with
    ⟨p, hpMem, hpCost, hpValue⟩
  rcases exists_spectrumList_witness U.predictors c with
    ⟨q, hqMem, hqCost, hqValue⟩
  let r := sequentialPredictor defect p q
  have hrMem :
      r ∈ sequentialPredictors T.predictors U.predictors defect := by
    exact sequentialPredictor_mem hpMem hqMem
  have hpNat : p.cost.val ≤ b.val := by
    simpa using hpCost
  have hqNat : q.cost.val ≤ c.val := by
    simpa using hqCost
  have hrCost : r.cost ≤ sequentialSplitBudget b c defect := by
    dsimp [r, sequentialPredictor, sequentialSplitBudget]
    omega
  have hvalue :
      r.value ≤ sequentialSpectrum T U defect
        (sequentialSplitBudget b c defect) :=
    value_le_natSpectrumList_of_mem hrMem hrCost
  dsimp [r, sequentialPredictor, sequentialSplitSpectrum] at hvalue
  rw [hpValue, hqValue] at hvalue
  exact hvalue

/-- Local value under split sequential accounting. -/
def sequentialSplitLocalSpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  sequentialSplitSpectrum T U T.localBudget U.localBudget

/-- Poly value under split sequential accounting. -/
def sequentialSplitPolySpectrum {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  sequentialSplitSpectrum T U T.polyBudget U.polyBudget

/-- Gap under split sequential accounting. -/
def sequentialSplitSpectrumGap {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop) : Nat :=
  sequentialSplitPolySpectrum T U - sequentialSplitLocalSpectrum T U

theorem sequentialSplitSpectrumGap_eq_add {leftTop rightTop : Nat}
    {T : WeaknessTask leftTop} {U : WeaknessTask rightTop}
    (hT : BudgetOrdered T) (hU : BudgetOrdered U) :
    sequentialSplitSpectrumGap T U = T.spectrumGap + U.spectrumGap := by
  have hTle : T.localSpectrum ≤ T.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hT
  have hUle : U.localSpectrum ≤ U.polySpectrum :=
    localSpectrum_le_polySpectrum_of_budgetOrdered hU
  unfold sequentialSplitSpectrumGap sequentialSplitPolySpectrum
    sequentialSplitLocalSpectrum sequentialSplitSpectrum
    WeaknessTask.spectrumGap WeaknessTask.localSpectrum
    WeaknessTask.polySpectrum
  simp only [WeaknessTask.localSpectrum, WeaknessTask.polySpectrum] at hTle hUle
  omega

theorem sequential_chainRule_local {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (defect : Nat) :
    sequentialSplitLocalSpectrum T U ≤
      sequentialSpectrum T U defect
        (sequentialSplitBudget T.localBudget U.localBudget defect) :=
  sequential_chainRule_subadditive T U defect T.localBudget U.localBudget

theorem sequential_chainRule_poly {leftTop rightTop : Nat}
    (T : WeaknessTask leftTop) (U : WeaknessTask rightTop)
    (defect : Nat) :
    sequentialSplitPolySpectrum T U ≤
      sequentialSpectrum T U defect
        (sequentialSplitBudget T.polyBudget U.polyBudget defect) :=
  sequential_chainRule_subadditive T U defect T.polyBudget U.polyBudget

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

theorem toyWeakness_tensor_localSpectrum :
    tensorLocalSpectrum toyWeaknessTask toyWeaknessTask = 2 := by
  norm_num [tensorLocalSpectrum_eq_add, toyWeaknessTask_localSpectrum]

theorem toyWeakness_tensor_polySpectrum :
    tensorPolySpectrum toyWeaknessTask toyWeaknessTask = 4 := by
  norm_num [tensorPolySpectrum_eq_add, toyWeaknessTask_polySpectrum]

theorem toyWeakness_tensor_spectrumGap :
    tensorSpectrumGap toyWeaknessTask toyWeaknessTask = 2 := by
  rw [tensorSpectrumGap_eq_add toyWeaknessTask_budgetOrdered
    toyWeaknessTask_budgetOrdered]
  norm_num [toyWeaknessTask_spectrumGap]

theorem toyWeakness_tensor_blockAdditivity :
  toyWeaknessTask.tensorSpectrum toyWeaknessTask
        toyWeaknessTask.polyBudget toyWeaknessTask.polyBudget = 4 := by
  rw [WeaknessTask.tensorSpectrum_additive]
  change toyWeaknessTask.polySpectrum + toyWeaknessTask.polySpectrum = 4
  norm_num [toyWeaknessTask_polySpectrum]

theorem toyWeakness_tensorValue_multiplicative :
  toyWeaknessTask.tensorValueSpectrum toyWeaknessTask
        toyWeaknessTask.polyBudget toyWeaknessTask.polyBudget = 4 := by
  rw [WeaknessTask.tensorValueSpectrum_multiplicative]
  change toyWeaknessTask.polySpectrum * toyWeaknessTask.polySpectrum = 4
  norm_num [toyWeaknessTask_polySpectrum]

theorem toyWeakness_tensorValue_spectrumGap :
    tensorValueSpectrumGap toyWeaknessTask toyWeaknessTask = 3 := by
  rw [tensorValueSpectrumGap_eq_crossTerms toyWeaknessTask_budgetOrdered
    toyWeaknessTask_budgetOrdered]
  norm_num [toyWeaknessTask_spectrumGap, toyWeaknessTask_polySpectrum,
    toyWeaknessTask_localSpectrum]

def toySequentialDefect : Nat := 1

theorem toyWeakness_sequential_local_chainRule :
    sequentialSplitLocalSpectrum toyWeaknessTask toyWeaknessTask ≤
      sequentialSpectrum toyWeaknessTask toyWeaknessTask toySequentialDefect
        (sequentialSplitBudget toyWeaknessTask.localBudget
          toyWeaknessTask.localBudget toySequentialDefect) :=
  sequential_chainRule_local toyWeaknessTask toyWeaknessTask toySequentialDefect

theorem toyWeakness_sequential_poly_chainRule :
    sequentialSplitPolySpectrum toyWeaknessTask toyWeaknessTask ≤
      sequentialSpectrum toyWeaknessTask toyWeaknessTask toySequentialDefect
        (sequentialSplitBudget toyWeaknessTask.polyBudget
          toyWeaknessTask.polyBudget toySequentialDefect) :=
  sequential_chainRule_poly toyWeaknessTask toyWeaknessTask toySequentialDefect

theorem toyWeakness_sequential_splitGap :
    sequentialSplitSpectrumGap toyWeaknessTask toyWeaknessTask = 2 := by
  rw [sequentialSplitSpectrumGap_eq_add toyWeaknessTask_budgetOrdered
    toyWeaknessTask_budgetOrdered]
  norm_num [toyWeaknessTask_spectrumGap]

end Mettapedia.Computability.PNP

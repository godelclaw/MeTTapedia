import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!+# Real-valued three-horizon attention

Ideal mathematical specification of the native `lib-cetta.metta` attention
library in `godelclaw/metta-attention`. STI, MTI and LTI have independently
balanced reserves. Reserves may be negative: conservation is accounting, not
an admission rule. Adjacent consolidation smooths MTI toward STI, then LTI
toward the updated MTI; it does not exchange different attention currencies.

Retention is `(1/2)^(elapsed / halfLife)`; the zero half-life sentinel disables
decay. The model establishes conservation, time composition, calibration and
the mathematical parameter domains over real numbers. Native `pow`/`log` and
arithmetic use floating point. These proofs do not certify those C functions,
their roundoff, serialization, relevance quality, or the MeTTa interpreter.
-/

noncomputable section

namespace Mettapedia.CogArch.Attention.ThreeTimescale

inductive Horizon where
  | sti | mti | lti
  deriving DecidableEq

abbrev Value := Horizon → ℝ

structure Bank (ι : Type*) where
  values : ι → Value
  reserve : Value

theorem bank_ext {ι : Type*} {a b : Bank ι}
    (hv : a.values = b.values) (hr : a.reserve = b.reserve) : a = b := by
  cases a
  cases b
  simp_all

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def total (b : Bank ι) (h : Horizon) : ℝ :=
  b.reserve h + ∑ i, b.values i h

/-- The native identity-targeted replacement, including its reserve adjustment. -/
def replace (b : Bank ι) (i : ι) (v : Value) : Bank ι where
  values := Function.update b.values i v
  reserve h := b.reserve h + (b.values i h - v h)

omit [Fintype ι] in
theorem replace_preserves_other (b : Bank ι) (i j : ι) (v : Value) (hne : j ≠ i) :
    (replace b i v).values j = b.values j := by
  simp [replace, Function.update_of_ne hne]

theorem replace_total (b : Bank ι) (i : ι) (v : Value) (h : Horizon) :
    total (replace b i v) h = total b h := by
  classical
  unfold total replace
  simp only
  have hv : (fun j => Function.update b.values i v j h) =
      Function.update (fun j => b.values j h) i (v h) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [hv, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have old := Finset.sum_update_of_mem (s := Finset.univ)
    (f := fun j => b.values j h) (b := b.values i h) (Finset.mem_univ i)
  simp only [Function.update_eq_self] at old
  linarith

/-- A full sweep accumulates the old-minus-new difference for each horizon. -/
def sweep (b : Bank ι) (r : Value) : Bank ι where
  values i h := b.values i h * r h
  reserve h := b.reserve h + ∑ i, (b.values i h - b.values i h * r h)

omit [DecidableEq ι] in
theorem sweep_total (b : Bank ι) (r : Value) (h : Horizon) :
    total (sweep b r) h = total b h := by
  simp only [total, sweep, Finset.sum_sub_distrib]
  ring

def retention (elapsed halfLife : ℝ) : ℝ :=
  if halfLife = 0 then 1 else (1 / 2 : ℝ) ^ (elapsed / halfLife)

@[simp] theorem retention_disabled (t : ℝ) : retention t 0 = 1 := by
  simp [retention]

@[simp] theorem retention_zero_time (h : ℝ) : retention 0 h = 1 := by
  by_cases hh : h = 0 <;> simp [retention, hh]

theorem retention_positive (t h : ℝ) : 0 < retention t h := by
  by_cases hh : h = 0
  · simp [retention, hh]
  · simp only [retention, hh, if_false]
    exact Real.rpow_pos_of_pos (by norm_num) _

theorem retention_le_one (t h : ℝ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    retention t h ≤ 1 := by
  by_cases hz : h = 0
  · simp [retention, hz]
  · simp only [retention, hz, if_false]
    exact Real.rpow_le_one (by norm_num) (by norm_num) (div_nonneg ht hh)

theorem retention_compose (s t h : ℝ) :
    retention (s + t) h = retention s h * retention t h := by
  by_cases hz : h = 0
  · simp [retention, hz]
  · simp only [retention, hz, if_false, add_div]
    exact Real.rpow_add (by norm_num) _ _

def advance (b : Bank ι) (halfLife : Value) (elapsed : ℝ) : Bank ι :=
  sweep b (fun h => retention elapsed (halfLife h))

omit [DecidableEq ι] in
theorem advance_total (b : Bank ι) (halfLife : Value) (t : ℝ) (h : Horizon) :
    total (advance b halfLife t) h = total b h := sweep_total _ _ _

omit [DecidableEq ι] in
theorem advance_values_compose (b : Bank ι) (halfLife : Value) (s t : ℝ) (i : ι)
    (h : Horizon) :
    (advance (advance b halfLife s) halfLife t).values i h =
      (advance b halfLife (s + t)).values i h := by
  simp only [advance, sweep, retention_compose]
  ring

omit [DecidableEq ι] in
theorem advance_compose (b : Bank ι) (halfLife : Value) (s t : ℝ) :
    advance (advance b halfLife s) halfLife t = advance b halfLife (s + t) := by
  have hv : (advance (advance b halfLife s) halfLife t).values =
      (advance b halfLife (s + t)).values := by
    funext i h
    exact advance_values_compose b halfLife s t i h
  have hr : (advance (advance b halfLife s) halfLife t).reserve =
      (advance b halfLife (s + t)).reserve := by
    funext h
    have ha := advance_total (advance b halfLife s) halfLife t h
    have hb := advance_total b halfLife s h
    have hc := advance_total b halfLife (s + t) h
    simp only [total, hv] at ha hb hc
    linarith
  exact bank_ext hv hr

def consolidate (stiMti mtiLti : ℝ) (v : Value) : Value :=
  let m := v .mti + stiMti * (v .sti - v .mti)
  let l := v .lti + mtiLti * (m - v .lti)
  fun h => match h with | .sti => v .sti | .mti => m | .lti => l

@[simp] theorem consolidate_sti (a b : ℝ) (v : Value) :
    consolidate a b v .sti = v .sti := rfl

theorem consolidate_lti_uses_new_mti (a b : ℝ) (v : Value) :
    consolidate a b v .lti = v .lti + b * (consolidate a b v .mti - v .lti) := rfl

@[simp] theorem consolidation_disabled (v : Value) : consolidate 0 0 v = v := by
  funext h
  cases h <;> simp [consolidate]

theorem consolidate_total (bank : Bank ι) (i : ι) (a b : ℝ) (h : Horizon) :
    total (replace bank i (consolidate a b (bank.values i))) h = total bank h :=
  replace_total _ _ _ _

theorem smoothing_between (x y r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    min x y ≤ x + r * (y - x) ∧ x + r * (y - x) ≤ max x y := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, max_eq_right hxy]
    constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hxy),
      mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hxy)]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx, max_eq_left hyx]
    constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hyx),
      mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hyx)]

def halfLifeFor (t fraction : ℝ) : ℝ :=
  if fraction = 1 then 0 else -(t / (Real.log fraction / Real.log 2))

@[simp] theorem calibration_disabled (t : ℝ) : halfLifeFor t 1 = 0 := by
  simp [halfLifeFor]

theorem calibrated_half_life_positive (t f : ℝ) (ht : 0 < t) (hf0 : 0 < f)
    (hf1 : f < 1) : 0 < halfLifeFor t f := by
  have hl : Real.log f < 0 := Real.log_neg hf0 hf1
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  unfold halfLifeFor
  rw [if_neg (ne_of_lt hf1)]
  exact neg_pos.mpr (div_neg_of_pos_of_neg ht (div_neg_of_neg_of_pos hl htwo))

theorem calibration_roundtrip (t f : ℝ) (ht : 0 < t) (hf0 : 0 < f) (hf1 : f < 1) :
    retention t (halfLifeFor t f) = f := by
  have hhalf : halfLifeFor t f ≠ 0 := ne_of_gt (calibrated_half_life_positive t f ht hf0 hf1)
  have hf : f ≠ 1 := ne_of_lt hf1
  have hl : Real.log f ≠ 0 := ne_of_lt (Real.log_neg hf0 hf1)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have htwo : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [retention, if_neg hhalf, Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log (1 / 2 : ℝ) * (t / halfLifeFor t f) = Real.log f := by
    rw [hlog, halfLifeFor, if_neg hf]
    field_simp
  rw [he, Real.exp_log hf0]


end Mettapedia.CogArch.Attention.ThreeTimescale

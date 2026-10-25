import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Ordered divisibility scans

Each occurrence removes its divisor at most once. Order and multiplicity
matter in general. A product-divisibility certificate permits forgetting
order at the endpoint; it does not identify intermediate candidates.
The arithmetic includes zero divisors, unlike partial integer evaluators.
-/

namespace Mettapedia.Algorithms.DivisibilityScan

set_option autoImplicit false

/-- Divide by `divisor` once when it divides `candidate`. -/
def removeIfDivides (candidate divisor : Nat) : Nat :=
  if candidate % divisor = 0 then candidate / divisor else candidate

/-- Consume divisor occurrences from left to right. -/
def scan : List Nat → Nat → Nat
  | [], candidate => candidate
  | divisor :: divisors, candidate =>
      scan divisors (removeIfDivides candidate divisor)

@[simp] theorem scan_nil (candidate : Nat) : scan [] candidate = candidate := rfl

@[simp] theorem scan_cons (divisor : Nat) (divisors : List Nat) (candidate : Nat) :
    scan (divisor :: divisors) candidate =
      scan divisors (removeIfDivides candidate divisor) := rfl

@[simp] theorem removeIfDivides_zero_divisor (candidate : Nat) :
    removeIfDivides candidate 0 = candidate := by
  by_cases h : candidate = 0 <;> simp [removeIfDivides, h]

@[simp] theorem scan_zero (divisors : List Nat) : scan divisors 0 = 0 := by
  induction divisors with
  | nil => rfl
  | cons divisor divisors ih => simpa [scan, removeIfDivides] using ih

theorem scan_eq_foldl (divisors : List Nat) (candidate : Nat) :
    scan divisors candidate = divisors.foldl removeIfDivides candidate := by
  induction divisors generalizing candidate <;> simp_all [scan]

theorem scan_append (first second : List Nat) (candidate : Nat) :
    scan (first ++ second) candidate = scan second (scan first candidate) := by
  simp only [scan_eq_foldl, List.foldl_append]

theorem removeIfDivides_pos {candidate divisor : Nat}
    (candidatePositive : 0 < candidate) : 0 < removeIfDivides candidate divisor := by
  unfold removeIfDivides
  split
  · next divides =>
      have hd := Nat.dvd_of_mod_eq_zero divides
      exact Nat.div_pos (Nat.le_of_dvd candidatePositive hd)
        (Nat.pos_of_dvd_of_pos hd candidatePositive)
  · exact candidatePositive

theorem scan_pos {divisors : List Nat} {candidate : Nat}
    (candidatePositive : 0 < candidate) : 0 < scan divisors candidate := by
  induction divisors generalizing candidate with
  | nil => exact candidatePositive
  | cons divisor divisors ih => exact ih (removeIfDivides_pos candidatePositive)

/-- Nondivisibility at the initial candidate is exactly persistence through
all residuals dividing it; it is not an additional scan invariant. -/
theorem not_dvd_iff_persistent (divisor candidate : Nat) :
    (¬divisor ∣ candidate) ↔
      ∀ residual, residual ∣ candidate → ¬divisor ∣ residual :=
  ⟨fun h _ hr hd => h (dvd_trans hd hr), fun h => h candidate (dvd_refl _)⟩

/-- Selected occurrences divide out exactly; unselected values cannot become
divisors later. No decidable equality or positivity assumption is needed. -/
theorem scan_map_eq_div_filter_prod
    {α : Type*} (items : List α) (value : α → Nat) (selected : α → Prop)
    [DecidablePred selected] (candidate : Nat)
    (selectedProductDivides : ((items.filter selected).map value).prod ∣ candidate)
    (unselectedDoesNotDivide :
      ∀ item ∈ items, ¬selected item → ¬value item ∣ candidate) :
    scan (items.map value) candidate =
      candidate / ((items.filter selected).map value).prod := by
  induction items generalizing candidate with
  | nil => simp
  | cons item items ih =>
      by_cases hs : selected item
      · have hd : value item ∣ candidate :=
          dvd_trans (dvd_mul_right _ _) (by simpa [hs] using selectedProductDivides)
        have ht : ((items.filter selected).map value).prod ∣ candidate / value item := by
          rw [Nat.dvd_div_iff_mul_dvd hd]
          simpa [hs] using selectedProductDivides
        have hn : ∀ other ∈ items, ¬selected other → ¬value other ∣ candidate / value item :=
          fun other hm ho hv => unselectedDoesNotDivide other (by simp [hm]) ho
            (dvd_trans hv (Nat.div_dvd_of_dvd hd))
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_pos (Nat.dvd_iff_mod_eq_zero.mp hd), ih _ ht hn, Nat.div_div_eq_div_mul]
        simp [hs]
      · have hd := unselectedDoesNotDivide item (by simp) hs
        rw [List.map_cons, scan_cons, removeIfDivides,
          if_neg (Nat.dvd_iff_mod_eq_zero.not.mp hd), ih candidate]
        · simp [hs]
        · simpa [hs] using selectedProductDivides
        · exact fun other hm ho => unselectedDoesNotDivide other (by simp [hm]) ho

/-- A certificate for the entire product permits exact division. -/
theorem scan_eq_div_prod_of_prod_dvd (divisors : List Nat) (candidate : Nat)
    (productDivides : divisors.prod ∣ candidate) :
    scan divisors candidate = candidate / divisors.prod := by
  simpa using scan_map_eq_div_filter_prod divisors id (fun _ => True) candidate
    (by simpa using productDivides) (by simp)

/-- A list of nondivisors leaves the candidate unchanged. -/
theorem scan_eq_self_of_forall_not_dvd (divisors : List Nat) (candidate : Nat)
    (noneDivides : ∀ divisor ∈ divisors, ¬divisor ∣ candidate) :
    scan divisors candidate = candidate := by
  simpa using scan_map_eq_div_filter_prod divisors id (fun _ => False) candidate
    (by simp) (by simpa using noneDivides)

theorem removeIfDivides_dvd_candidate (candidate divisor : Nat) :
    removeIfDivides candidate divisor ∣ candidate := by
  unfold removeIfDivides
  split <;> rename_i h
  · exact Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h)
  · exact dvd_refl _

theorem scan_dvd_candidate (divisors : List Nat) (candidate : Nat) :
    scan divisors candidate ∣ candidate := by
  induction divisors generalizing candidate with
  | nil => exact dvd_refl _
  | cons divisor divisors ih =>
      exact dvd_trans (ih _) (removeIfDivides_dvd_candidate candidate divisor)

/-- Certified endpoints depend only on the product, not the supplied ordering. -/
theorem scan_factorsThrough_prod (candidate : Nat) :
    Function.FactorsThrough
      (fun ds : {ds : List Nat // ds.prod ∣ candidate} => scan ds.val candidate)
      (fun ds => ds.val.prod) := by
  intro first second same
  change scan first.val candidate = scan second.val candidate
  change first.val.prod = second.val.prod at same
  rw [scan_eq_div_prod_of_prod_dvd _ _ first.property,
    scan_eq_div_prod_of_prod_dvd _ _ second.property, same]

theorem scan_perm_of_prod_dvd {first second : List Nat} (h : first.Perm second)
    (candidate : Nat) (productDivides : first.prod ∣ candidate) :
    scan first candidate = scan second candidate :=
  scan_factorsThrough_prod candidate (a := ⟨first, productDivides⟩)
    (b := ⟨second, h.prod_eq ▸ productDivides⟩) h.prod_eq

/-- Unselected occurrences also may move when the selected product divides. -/
theorem scan_map_perm_of_filter_prod_dvd {α : Type*} {first second : List α}
    (h : first.Perm second) (value : α → Nat) (selected : α → Prop)
    [DecidablePred selected] (candidate : Nat)
    (productDivides : ((first.filter selected).map value).prod ∣ candidate)
    (nondivisors : ∀ item ∈ first, ¬selected item → ¬value item ∣ candidate) :
    scan (first.map value) candidate = scan (second.map value) candidate := by
  have same := ((h.filter selected).map value).prod_eq
  rw [scan_map_eq_div_filter_prod first value selected candidate productDivides nondivisors,
    scan_map_eq_div_filter_prod second value selected candidate (same ▸ productDivides)
      (fun item hm => nondivisors item (h.mem_iff.mpr hm)), same]

theorem removeIfDivides_comm_of_mul_dvd (first second candidate : Nat)
    (productDivides : first * second ∣ candidate) :
    removeIfDivides (removeIfDivides candidate first) second =
      removeIfDivides (removeIfDivides candidate second) first := by
  simpa using scan_perm_of_prod_dvd (List.Perm.swap second first []) candidate
    (by simpa using productDivides)

/-- Without a product certificate, even permutations can change the endpoint. -/
theorem scan_order_sensitive : scan [4, 6] 12 ≠ scan [6, 4] 12 := by decide

/-- Equal endpoints need not imply equal intermediate observations. -/
theorem scan_endpoint_forgets_prefix :
    scan [2, 3] 12 = scan [3, 2] 12 ∧ scan [2] 12 ≠ scan [3] 12 := by decide

/-- Duplicate occurrences remain observable even though order can be forgotten. -/
theorem scan_occurrence_sensitive : scan [2, 2] 8 ≠ scan [2] 8 := by decide

end Mettapedia.Algorithms.DivisibilityScan

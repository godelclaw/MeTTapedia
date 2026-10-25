import Mettapedia.Algebra.SupportTensorRounding
import Mettapedia.Algorithms.Retrieval.ScreeningCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

/-!
Ordered dot-product screening under a local relative-plus-absolute rounding
model. The trace assumptions describe the actual multiplication and addition
steps, not arbitrary operations on unbounded inputs. Native floating-point
and owner conformance are separate obligations. Missing sparse coordinates
are not introduced as extra floating operations by this model.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensorScreening

open scoped BigOperators

/-! Independent row accumulators may share a column traversal. Selecting row
occurrences first changes neither a row's operation schedule nor duplicates. -/

def interleavedRows {I C R V : Type*} (step : R → V → R) (sample : I → C → V)
    (columns : List C) (initial : I → R) : I → R :=
  columns.foldl (fun state column row => step (state row) (sample row column)) initial

theorem interleavedRows_at {I C R V : Type*} (step : R → V → R) (sample : I → C → V)
    (columns : List C) (initial : I → R) (row : I) :
    interleavedRows step sample columns initial row =
      columns.foldl (fun accumulator column => step accumulator (sample row column)) (initial row) := by
  induction columns generalizing initial with
  | nil => rfl
  | cons column rest ih =>
      simpa [interleavedRows] using
        ih (initial := fun row => step (initial row) (sample row column))

theorem interleavedRows_select {I O C R V : Type*} (step : R → V → R)
    (sample : I → C → V) (selected : O → I) (columns : List C) (initial : I → R) :
    interleavedRows step (fun output column => sample (selected output) column)
        columns (fun output => initial (selected output)) =
      fun output => interleavedRows step sample columns initial (selected output) := by
  funext output
  rw [interleavedRows_at, interleavedRows_at]

theorem one_step_error (u eta magnitude : ℝ) (processed : Nat)
    (exactValue accumulator product roundedProduct next : ℝ)
    (u_nonneg : 0 ≤ u) (u_le_one : u ≤ 1)
    (eta_nonneg : 0 ≤ eta) (magnitude_nonneg : 0 ≤ magnitude)
    (processed_small : 4 * (processed : ℝ) * u ≤ 1)
    (exact_budget : |exactValue| + |product| ≤ magnitude)
    (previous_error : |accumulator - exactValue| ≤
      4 * (processed : ℝ) * (u * magnitude + eta))
    (product_error : |roundedProduct - product| ≤ u * |product| + eta)
    (addition_error : |next - (accumulator + roundedProduct)| ≤
      u * |accumulator + roundedProduct| + eta) :
    |next - (exactValue + product)| ≤
      4 * ((processed : ℝ) + 1) * (u * magnitude + eta) := by
  let budget := u * magnitude + eta
  have budget_nonneg : 0 ≤ budget := add_nonneg (mul_nonneg u_nonneg magnitude_nonneg) eta_nonneg
  have product_le : |product| ≤ magnitude := by linarith [abs_nonneg exactValue]
  have rounded_product_error : |roundedProduct - product| ≤ budget :=
    product_error.trans (add_le_add (mul_le_mul_of_nonneg_left product_le u_nonneg) (le_refl eta))
  have exact_sum_le : |exactValue + product| ≤ magnitude :=
    (abs_add_le exactValue product).trans exact_budget
  have difference_le : |(accumulator + roundedProduct) - (exactValue + product)| ≤
      4 * (processed : ℝ) * budget + budget := by
    calc
      _ = |(accumulator - exactValue) + (roundedProduct - product)| := by congr 1; ring
      _ ≤ |accumulator - exactValue| + |roundedProduct - product| := abs_add_le _ _
      _ ≤ _ := add_le_add previous_error rounded_product_error
  have add_argument_le : |accumulator + roundedProduct| ≤
      magnitude + 4 * (processed : ℝ) * budget + budget := by
    have := abs_sub_le (accumulator + roundedProduct) (exactValue + product) 0
    simp only [sub_zero] at this
    linarith
  have growth_le : (4 * (processed : ℝ) * u) * budget ≤ budget := by
    simpa using mul_le_mul_of_nonneg_right processed_small budget_nonneg
  have unit_le : u * budget ≤ budget := by
    simpa using mul_le_mul_of_nonneg_right u_le_one budget_nonneg
  have next_rounding_le : |next - (accumulator + roundedProduct)| ≤ 3 * budget := by
    calc
      _ ≤ u * |accumulator + roundedProduct| + eta := addition_error
      _ ≤ u * (magnitude + 4 * (processed : ℝ) * budget + budget) + eta :=
        add_le_add (mul_le_mul_of_nonneg_left add_argument_le u_nonneg) (le_refl eta)
      _ = budget + (4 * (processed : ℝ) * u) * budget + u * budget := by dsimp [budget]; ring
      _ ≤ _ := by linarith
  have final_triangle := abs_sub_le next (accumulator + roundedProduct) (exactValue + product)
  calc
    |next - (exactValue + product)| ≤ 3 * budget +
        (4 * (processed : ℝ) * budget + budget) := by linarith
    _ = _ := by dsimp [budget]; ring

def roundedSum (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ) : ℝ → List ℝ → ℝ
  | accumulator, [] => accumulator
  | accumulator, product :: rest => roundedSum multiply add (add accumulator (multiply product)) rest

def Admitted (u eta : ℝ) (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ) :
    ℝ → List ℝ → Prop
  | _, [] => True
  | accumulator, product :: rest =>
      |multiply product - product| ≤ u * |product| + eta ∧
      |add accumulator (multiply product) - (accumulator + multiply product)| ≤
        u * |accumulator + multiply product| + eta ∧
      Admitted u eta multiply add (add accumulator (multiply product)) rest

theorem roundedSum_error_from (u eta magnitude : ℝ)
    (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ)
    (u_nonneg : 0 ≤ u) (u_le_one : u ≤ 1)
    (eta_nonneg : 0 ≤ eta) (magnitude_nonneg : 0 ≤ magnitude)
    (products : List ℝ) (processed : Nat) (accumulator exactValue : ℝ)
    (admitted : Admitted u eta multiply add accumulator products)
    (exact_budget : |exactValue| + (products.map abs).sum ≤ magnitude)
    (count_small : ((processed + products.length : Nat) : ℝ) * u ≤ 1 / 4)
    (previous_error : |accumulator - exactValue| ≤
      4 * (processed : ℝ) * (u * magnitude + eta)) :
    |roundedSum multiply add accumulator products - (exactValue + products.sum)| ≤
      4 * ((processed + products.length : Nat) : ℝ) * (u * magnitude + eta) := by
  induction products generalizing processed accumulator exactValue with
  | nil => simpa [roundedSum] using previous_error
  | cons product rest ih =>
      rcases admitted with ⟨product_error, addition_error, tail_admitted⟩
      have tail_nonneg : 0 ≤ (rest.map abs).sum :=
        List.sum_nonneg fun value member => by
          rcases List.mem_map.mp member with ⟨item, _, rfl⟩
          exact abs_nonneg item
      have step_budget : |exactValue| + |product| ≤ magnitude := by
        simp only [List.map_cons, List.sum_cons] at exact_budget
        linarith
      have tail_budget : |exactValue + product| + (rest.map abs).sum ≤ magnitude := by
        have := abs_add_le exactValue product
        simp only [List.map_cons, List.sum_cons] at exact_budget
        linarith
      have processed_le : (processed : ℝ) * u ≤ 1 / 4 :=
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.le_add_right processed (product :: rest).length) u_nonneg).trans count_small
      have next_error := one_step_error u eta magnitude processed exactValue accumulator
        product (multiply product) (add accumulator (multiply product))
        u_nonneg u_le_one eta_nonneg magnitude_nonneg (by linarith)
        step_budget previous_error product_error addition_error
      have tail_count : ((processed + 1 + rest.length : Nat) : ℝ) * u ≤ 1 / 4 := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using count_small
      have continued := ih (processed + 1) (add accumulator (multiply product))
        (exactValue + product) tail_admitted tail_budget tail_count
        (by simpa using next_error)
      simpa only [roundedSum, List.sum_cons, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc] using continued

theorem roundedSum_error (u eta magnitude : ℝ)
    (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ)
    (u_nonneg : 0 ≤ u) (u_le_one : u ≤ 1)
    (eta_nonneg : 0 ≤ eta) (magnitude_nonneg : 0 ≤ magnitude)
    (products : List ℝ) (admitted : Admitted u eta multiply add 0 products)
    (exact_budget : (products.map abs).sum ≤ magnitude)
    (count_small : (products.length : ℝ) * u ≤ 1 / 4) :
    |roundedSum multiply add 0 products - products.sum| ≤
      4 * (products.length : ℝ) * (u * magnitude + eta) := by
  simpa using roundedSum_error_from u eta magnitude multiply add u_nonneg u_le_one
    eta_nonneg magnitude_nonneg products 0 0 0 admitted
    (by simpa using exact_budget) (by simpa using count_small) (by simp)

def roundedDot {n : Nat} (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ)
    (source query : Fin n → ℝ) : ℝ :=
  roundedSum multiply add 0 (List.ofFn fun col => source col * query col)

theorem product_magnitude_le {n : Nat} (source query : Fin n → ℝ) (qmax : ℝ)
    (query_bound : ∀ col, |query col| ≤ qmax) :
    ((List.ofFn fun col => source col * query col).map abs).sum ≤
      (∑ col, |source col|) * qmax := by
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  calc
    (∑ col, |source col * query col|) = ∑ col, |source col| * |query col| := by
      simp only [abs_mul]
    _ ≤ ∑ col, |source col| * qmax := Finset.sum_le_sum fun col _ =>
      mul_le_mul_of_nonneg_left (query_bound col) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem roundedDot_error {n : Nat} (u eta qmax : ℝ)
    (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ) (source query : Fin n → ℝ)
    (u_nonneg : 0 ≤ u) (u_le_one : u ≤ 1) (eta_nonneg : 0 ≤ eta)
    (qmax_nonneg : 0 ≤ qmax) (query_bound : ∀ col, |query col| ≤ qmax)
    (count_small : (n : ℝ) * u ≤ 1 / 4)
    (admitted : Admitted u eta multiply add 0
      (List.ofFn fun col => source col * query col)) :
    |roundedDot multiply add source query - ∑ col, source col * query col| ≤
      4 * (n : ℝ) * (u * ((∑ col, |source col|) * qmax) + eta) := by
  have magnitude_nonneg : 0 ≤ (∑ col, |source col|) * qmax :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) qmax_nonneg
  simpa [roundedDot, List.sum_ofFn] using roundedSum_error u eta ((∑ col, |source col|) * qmax)
    multiply add u_nonneg u_le_one eta_nonneg magnitude_nonneg
    (List.ofFn fun col => source col * query col) admitted
    (product_magnitude_le source query qmax query_bound) (by simpa using count_small)

theorem quantized_dot_error {n : Nat} (source compact query : Fin n → ℝ) (qmax : ℝ)
    (query_bound : ∀ col, |query col| ≤ qmax) :
    |(∑ col, source col * query col) - ∑ col, compact col * query col| ≤
      (∑ col, |source col - compact col|) * qmax := by
  calc
    _ = |∑ col, (source col - compact col) * query col| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro col _
      ring
    _ ≤ ∑ col, |(source col - compact col) * query col| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ col, |source col - compact col| * qmax := Finset.sum_le_sum fun col _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (query_bound col) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

theorem screening_radius {n : Nat} (u eta qmax difference magnitude : ℝ)
    (multiply : ℝ → ℝ) (add : ℝ → ℝ → ℝ) (source compact query : Fin n → ℝ)
    (u_nonneg : 0 ≤ u) (u_le_one : u ≤ 1) (eta_nonneg : 0 ≤ eta)
    (qmax_nonneg : 0 ≤ qmax) (query_bound : ∀ col, |query col| ≤ qmax)
    (count_small : (n : ℝ) * u ≤ 1 / 4)
    (difference_bound : (∑ col, |source col - compact col|) ≤ difference)
    (magnitude_bound : (∑ col, |source col|) + (∑ col, |compact col|) ≤ magnitude)
    (source_admitted : Admitted u eta multiply add 0
      (List.ofFn fun col => source col * query col))
    (compact_admitted : Admitted u eta multiply add 0
      (List.ofFn fun col => compact col * query col)) :
    |roundedDot multiply add source query - roundedDot multiply add compact query| ≤
      qmax * difference + (4 * (n : ℝ) * u) * (qmax * magnitude) + 8 * (n : ℝ) * eta := by
  have source_error := roundedDot_error u eta qmax multiply add source query
    u_nonneg u_le_one eta_nonneg qmax_nonneg query_bound count_small source_admitted
  have compact_error := roundedDot_error u eta qmax multiply add compact query
    u_nonneg u_le_one eta_nonneg qmax_nonneg query_bound count_small compact_admitted
  have quantized_error := quantized_dot_error source compact query qmax query_bound
  have triangle₁ := abs_sub_le (roundedDot multiply add source query)
    (∑ col, source col * query col) (roundedDot multiply add compact query)
  have triangle₂ := abs_sub_le (∑ col, source col * query col)
    (∑ col, compact col * query col) (roundedDot multiply add compact query)
  rw [abs_sub_comm (∑ col, compact col * query col)] at triangle₂
  have coefficient_nonneg : 0 ≤ 4 * (n : ℝ) * u * qmax := by positivity
  have magnitude_error := mul_le_mul_of_nonneg_left magnitude_bound coefficient_nonneg
  have discrepancy_error := mul_le_mul_of_nonneg_right difference_bound qmax_nonneg
  nlinarith

theorem interval_contains {approximate exactScore radius : ℝ}
    (error : |exactScore - approximate| ≤ radius) :
    approximate - radius ≤ exactScore ∧ exactScore ≤ approximate + radius := by
  rcases abs_le.mp error with ⟨low, high⟩
  constructor <;> linarith

/-! Stable row identities lift the numerical bounds to an injective ranking
key. The inclusive real threshold then preserves boundary ties as well. -/

abbrev RankedScore := ℝ ×ₗ WithBot Int

def ranked (score : ℝ) (ordinal : Nat) : RankedScore :=
  toLex (score, ((-(ordinal : Int) : Int) : WithBot Int))

def thresholdKey (threshold : ℝ) : RankedScore := toLex (threshold, ⊥)

theorem ranked_mono {lower upper : ℝ} (ordinal : Nat) (bound : lower ≤ upper) :
    ranked lower ordinal ≤ ranked upper ordinal := by
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases lt_or_eq_of_le bound with strict | same
  · exact Or.inl strict
  · exact Or.inr ⟨same, le_rfl⟩

theorem threshold_le_ranked (threshold score : ℝ) (ordinal : Nat) :
    thresholdKey threshold ≤ ranked score ordinal ↔ threshold ≤ score := by
  rw [thresholdKey, ranked, Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (strict | ⟨same, _⟩)
    · exact le_of_lt strict
    · exact le_of_eq same
  · intro bound
    rcases lt_or_eq_of_le bound with strict | same
    · exact Or.inl strict
    · exact Or.inr ⟨same, bot_le⟩

theorem ranked_injective {I : Type*} (score : I → ℝ) (ordinal : I → Nat)
    (distinct : Function.Injective ordinal) :
    Function.Injective (fun row => ranked (score row) (ordinal row)) := by
  intro left right same
  apply distinct
  have second := congrArg (fun value : RankedScore => (ofLex value).2) same
  simpa [ranked] using second

theorem unique_topK {I Score : Type*} [DecidableEq I] [LinearOrder Score]
    (score : I → Score) (distinct : Function.Injective score)
    {k : Nat} {source original result : Finset I}
    (original_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK score k source original)
    (result_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK score k source result) :
    result = original := by
  rcases original_top with ⟨original_in, original_card, original_order⟩
  rcases result_top with ⟨result_in, result_card, result_order⟩
  apply Finset.eq_of_subset_of_card_le
  · intro row in_result
    by_contra not_original
    have not_subset : ¬ original ⊆ result := by
      intro included
      have same := Finset.eq_of_subset_of_card_le included (by omega : result.card ≤ original.card)
      exact not_original (same.symm ▸ in_result)
    obtain ⟨other, in_original, not_result⟩ := Finset.not_subset.mp not_subset
    have first := original_order other in_original row (result_in in_result) not_original
    have second := result_order row in_result other (original_in in_original) not_result
    have same := distinct (le_antisymm first second)
    exact not_original (same ▸ in_original)
  · omega

theorem stable_screened_rerank_exact {I : Type*} [DecidableEq I]
    (score lower upper : I → ℝ) (ordinal : I → Nat) (distinct : Function.Injective ordinal)
    (threshold : ℝ) {k : Nat} {source witnesses original result : Finset I}
    (original_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k source original)
    (witnesses_in : witnesses ⊆ source) (enough : min k source.card ≤ witnesses.card)
    (lower_bound : ∀ row ∈ source, lower row ≤ score row)
    (upper_bound : ∀ row ∈ source, score row ≤ upper row)
    (threshold_reached : ∀ row ∈ witnesses, threshold ≤ lower row)
    (result_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k
      (Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper threshold source) result) :
    result = original := by
  let lifted := fun (values : I → ℝ) (row : I) => ranked (values row) (ordinal row)
  have same_screen : Mettapedia.Algorithms.Retrieval.RetrievalContract.screen
      (lifted upper) (thresholdKey threshold) source =
      Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper threshold source := by
    ext row
    simp [Mettapedia.Algorithms.Retrieval.RetrievalContract.screen, lifted, threshold_le_ranked]
  have exact_result := Mettapedia.Algorithms.Retrieval.RetrievalContract.screened_rerank_exact
    (lifted score) (lifted lower) (lifted upper) (thresholdKey threshold)
    original_top witnesses_in enough
    (fun row member => ranked_mono (ordinal row) (lower_bound row member))
    (fun row member => ranked_mono (ordinal row) (upper_bound row member))
    (fun row member => (threshold_le_ranked _ _ _).mpr (threshold_reached row member))
    (by simpa only [same_screen] using result_top)
  exact unique_topK _ (ranked_injective score ordinal distinct) original_top exact_result

/-! Eligibility is support-aware: only a present true entry enables a row.
The lower-bound witnesses and their threshold are chosen inside this domain,
not from an unfiltered top-k that might contain excluded rows. -/

def eligible {I : Type*} (source : Finset I) (mask : I → Option Bool) : Finset I :=
  source.filter (fun row => mask row = some true)

theorem mem_eligible {I : Type*} (source : Finset I) (mask : I → Option Bool) (row : I) :
    row ∈ eligible source mask ↔ row ∈ source ∧ mask row = some true := by
  simp [eligible]

theorem screen_eligible {I : Type*} (source : Finset I) (mask : I → Option Bool)
    (upper : I → ℝ) (threshold : ℝ) :
    Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper threshold (eligible source mask) =
      eligible (Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper threshold source) mask := by
  ext row
  simp only [Mettapedia.Algorithms.Retrieval.RetrievalContract.screen, eligible,
    Finset.mem_filter]
  tauto

noncomputable def lowerThreshold {I : Type*} (lower : I → ℝ) (witnesses : Finset I)
    (nonempty : witnesses.Nonempty) : ℝ :=
  (witnesses.image lower).min' (nonempty.image lower)

def storedEligible {I : Type*} [DecidableEq I] (source stored : Finset I)
    (mask : I → Option Bool) : Finset I :=
  (source ∩ stored).filter (fun row => mask row = some true)

theorem storedEligible_eq {I : Type*} [DecidableEq I] (source stored : Finset I)
    (mask : I → Option Bool)
    (exact_support : ∀ row, row ∈ stored ↔ (mask row).isSome = true) :
    storedEligible source stored mask = eligible source mask := by
  ext row
  simp only [storedEligible, eligible, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨member, _⟩, enabled⟩
    exact ⟨member, enabled⟩
  · rintro ⟨member, enabled⟩
    refine ⟨⟨member, (exact_support row).mpr ?_⟩, enabled⟩
    simp [enabled]

theorem storedEligible_card_le {I : Type*} [DecidableEq I] (source stored : Finset I)
    (mask : I → Option Bool) : (storedEligible source stored mask).card ≤ stored.card := by
  exact (Finset.card_filter_le _ _).trans (Finset.card_le_card Finset.inter_subset_right)

theorem lowerThreshold_le {I : Type*} (lower : I → ℝ) (witnesses : Finset I)
    (nonempty : witnesses.Nonempty) {row : I} (member : row ∈ witnesses) :
    lowerThreshold lower witnesses nonempty ≤ lower row := by
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem lower member)

theorem stable_masked_screened_rerank_exact {I : Type*} [DecidableEq I]
    (score lower upper : I → ℝ) (ordinal : I → Nat) (distinct : Function.Injective ordinal)
    (mask : I → Option Bool) {k : Nat} {source witnesses original result : Finset I}
    (nonempty : witnesses.Nonempty)
    (original_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k (eligible source mask) original)
    (lower_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      lower k (eligible source mask) witnesses)
    (lower_bound : ∀ row ∈ eligible source mask, lower row ≤ score row)
    (upper_bound : ∀ row ∈ eligible source mask, score row ≤ upper row)
    (result_top : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row => ranked (score row) (ordinal row)) k
      (Mettapedia.Algorithms.Retrieval.RetrievalContract.screen upper
        (lowerThreshold lower witnesses nonempty) (eligible source mask)) result) :
    result = original := by
  exact stable_screened_rerank_exact score lower upper ordinal distinct
    (lowerThreshold lower witnesses nonempty) original_top lower_top.1
    (le_of_eq lower_top.2.1.symm) lower_bound upper_bound
    (fun _ member => lowerThreshold_le lower witnesses nonempty member) result_top

noncomputable def binary64Unit : ℝ := 1 / (2 : ℝ) ^ 53
noncomputable def binary64Underflow : ℝ := 1 / (2 : ℝ) ^ 1074

theorem binary64_unit_range : 0 ≤ binary64Unit ∧ binary64Unit ≤ 1 := by
  norm_num [binary64Unit]

theorem binary64_underflow_nonneg : 0 ≤ binary64Underflow := by
  unfold binary64Underflow
  positivity

theorem binary64_count_small (columns : Nat) (admitted : columns ≤ 2 ^ 51) :
    (columns : ℝ) * binary64Unit ≤ 1 / 4 := by
  have bound : (columns : ℝ) ≤ 2251799813685248 := by exact_mod_cast admitted
  calc
    (columns : ℝ) * binary64Unit ≤ 2251799813685248 * binary64Unit :=
      mul_le_mul_of_nonneg_right bound binary64_unit_range.1
    _ = 1 / 4 := by norm_num [binary64Unit]

example : roundedSum id (· + ·) 0 [10, -3, 2] = 9 := by
  norm_num [roundedSum]

example : interleavedRows (fun (accumulator : Nat) value => 10 * accumulator + value)
    (fun (row : Bool) column => (if row then 4 else 1) + column)
    [0, 1, 2] (fun _ => 0) true = 456 := by
  decide +kernel

example : Admitted 0 (1 / 100) (fun product => product + 1 / 100)
    (fun accumulator product => accumulator + product + 1 / 100) 0 [2, -1] := by
  norm_num [Admitted]

example : ¬ Admitted 0 0 (fun product => product + 1 / 100)
    (· + ·) 0 [2] := by
  norm_num [Admitted]

example : roundedSum id
    (fun accumulator product => accumulator + product +
      (if accumulator < 0 then -(1 / 100) else 1 / 100)) 0 [2, -3, 2] ≠
    roundedSum id
    (fun accumulator product => accumulator + product +
      (if accumulator < 0 then -(1 / 100) else 1 / 100)) 0 [2, 2, -3] := by
  norm_num [roundedSum]

example : ranked 5 1 < ranked 5 0 := by
  norm_num [ranked, Prod.Lex.toLex_lt_toLex]

example : thresholdKey 5 ≤ ranked 5 100 :=
  (threshold_le_ranked 5 5 100).mpr le_rfl

example : ¬ thresholdKey 6 ≤ ranked 5 0 := by
  rw [threshold_le_ranked]
  norm_num

#print axioms one_step_error
#print axioms roundedSum_error
#print axioms screening_radius
#print axioms stable_screened_rerank_exact
#print axioms binary64_count_small
#print axioms interleavedRows_select
#print axioms stable_masked_screened_rerank_exact
#print axioms storedEligible_eq

example : eligible ({false, true} : Finset Bool)
    (fun row => if row then some true else none) = {true} := by decide +kernel

example : eligible ({false, true} : Finset Bool)
    (fun row => if row then some true else some false) = {true} := by decide +kernel

example : Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
    (fun row : Bool => if row then (1 : ℝ) else 100) 1 {false, true} {false} ∧
    eligible ({false} : Finset Bool) (fun row => some row) = ∅ ∧
    Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK
      (fun row : Bool => if row then (1 : ℝ) else 100) 1
      (eligible {false, true} (fun row => some row)) {true} := by
  norm_num [Mettapedia.Algorithms.Retrieval.RetrievalContract.IsTopK, eligible,
    Finset.subset_iff]
  exact ⟨true, by simp⟩

end Mettapedia.Algebra.SupportTensorScreening

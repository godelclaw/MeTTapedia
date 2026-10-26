import Mettapedia.ProbabilityTheory.FreeProbability.Cumulants
import Mettapedia.GSLT.Dynamics.OrderedListFold
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Free probability: algebraic models, separating examples, and diagram execution

`NoncrossingPartitions` supplies canonical ordered partitions; `Cumulants` constructs
all joint cumulants and proves the moment equation, uniqueness, transport, scaling,
and additivity under mixed-cumulant freeness. This module assembles those interfaces
with examples and the finite diagram-summation machine.

The word-algebra model has two free generators with semicircular cumulant profiles.
This is an algebraic statement: no measure identification, positivity, free central
limit theorem, or random-matrix convergence is asserted by the density functions below.
-/

namespace Mettapedia.ProbabilityTheory.FreeProbability
open Finset

/-- The semicircle density function on `[-2,2]`. -/
noncomputable def semicircleDensity (x : ℝ) : ℝ :=
  if |x| ≤ 2 then (1 / (2 * Real.pi)) * Real.sqrt (4 - x ^ 2) else 0

theorem semicircleDensity_nonneg (x : ℝ) : 0 ≤ semicircleDensity x := by
  unfold semicircleDensity
  split_ifs
  · exact mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num) Real.pi_nonneg))
      (Real.sqrt_nonneg _)
  · rfl

/-- Continuous Marchenko–Pastur density in the parameter range `0 < γ ≤ 1`. -/
noncomputable def marchenkoPasturDensity (γ x : ℝ) : ℝ :=
  let lo := (1 - Real.sqrt γ) ^ 2
  let hi := (1 + Real.sqrt γ) ^ 2
  if lo ≤ x ∧ x ≤ hi ∧ 0 < γ ∧ γ ≤ 1 then
    (1 / (2 * Real.pi * γ * x)) * Real.sqrt ((hi - x) * (x - lo)) else 0

/-- Alternating Catalan coefficients; no general Möbius-inversion theorem is assumed. -/
def mobiusNC : ℕ → ℤ
  | 0 => 1
  | n + 1 => (-1 : ℤ) ^ n * (catalanNumber n : ℤ)

/-- Numerical Catalan moment profile, separate from any analytic measure theorem. -/
def semicircleMoment (n : ℕ) : ℕ :=
  if n % 2 = 0 then catalanNumber (n / 2) else 0

theorem semicircleMoment_small :
    semicircleMoment 0 = 1 ∧ semicircleMoment 1 = 0 ∧ semicircleMoment 2 = 1 ∧
    semicircleMoment 4 = 2 ∧ semicircleMoment 6 = 5 := by decide +kernel

section DiagramExecution
variable {R A : Type} [CommRing R] [Ring A] [Algebra R A]

/-- Each entry contributes its independently computed diagram value. -/
def diagramAdd (φ : AlgebraicState R A) {n : ℕ} (a : Fin n → A)
    (accumulator : R) (P : Partition n) : R :=
  accumulator + partitionEvaluation (fun m => jointCumulant φ m) P a

/-- A complete, duplicate-free listing computes the moment in any diagram order. -/
theorem diagram_fold (φ : AlgebraicState R A) {n : ℕ} (a : Fin n → A)
    (listing : List (Partition n)) (hn : listing.Nodup)
    (hc : listing.toFinset = noncrossingPartitions n) :
    listing.foldl (diagramAdd φ a) 0 = wordMoment φ n a := by
  rw [moment_cumulant φ n a, ← hc, List.sum_toFinset _ hn]
  change listing.foldl (fun acc P => acc + partitionEvaluation (fun m => jointCumulant φ m) P a) 0 = _
  simpa only [List.foldl_map] using
    (List.sum_eq_foldl (xs := listing.map
      (fun P => partitionEvaluation (fun m => jointCumulant φ m) P a))).symm

/-- This counts diagram entry visits and finalization, excluding recursive evaluation costs. -/
theorem diagram_execution (φ : AlgebraicState R A) {n : ℕ} (a : Fin n → A)
    (listing : List (Partition n)) (hn : listing.Nodup)
    (hc : listing.toFinset = noncrossingPartitions n) (result : R)
    (path : (Mettapedia.GSLT.Dynamics.OrderedListFold.theory (diagramAdd φ a)).RewritePath
      (.active listing 0) (.done result)) :
    result = wordMoment φ n a ∧ path.length = listing.length + 1 := by
  obtain ⟨hr, hl⟩ := Mettapedia.GSLT.Dynamics.OrderedListFold.complete_path
    (diagramAdd φ a) listing 0 result path
  exact ⟨hr.trans (diagram_fold φ a listing hn hc), hl⟩

/-- Permuting diagram summands preserves the fold; permuting word positions is a different claim. -/
theorem diagram_fold_perm (φ : AlgebraicState R A) {n : ℕ} (a : Fin n → A)
    {xs ys : List (Partition n)} (h : xs.Perm ys) :
    xs.foldl (diagramAdd φ a) 0 = ys.foldl (diagramAdd φ a) 0 := by
  have hs := (h.map (fun P => partitionEvaluation (fun m => jointCumulant φ m) P a)).sum_eq
  change xs.foldl (fun acc P => acc + partitionEvaluation (fun m => jointCumulant φ m) P a) 0 =
    ys.foldl (fun acc P => acc + partitionEvaluation (fun m => jointCumulant φ m) P a) 0
  simpa only [List.sum_eq_foldl, List.foldl_map] using hs

end DiagramExecution

namespace Examples

/-- Normalized matrix trace: tracial, but not invariant under arbitrary word permutations. -/
def traceTwo : AlgebraicState ℚ (Matrix (Fin 2) (Fin 2) ℚ) where
  toLinearMap := (1 / 2 : ℚ) • Matrix.traceLinearMap (Fin 2) ℚ ℚ
  map_one := by norm_num [Matrix.trace, Fin.sum_univ_two]

theorem traceTwo_tracial (X Y : Matrix (Fin 2) (Fin 2) ℚ) :
    traceTwo (X * Y) = traceTwo (Y * X) := by
  change (1 / 2 : ℚ) * Matrix.trace (X * Y) = (1 / 2 : ℚ) * Matrix.trace (Y * X)
  rw [Matrix.trace_mul_comm]

def signMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]
def swapMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]

set_option maxRecDepth 10000 in
/-- The same letters and multiplicities can have different joint cumulants, even for a trace. -/
theorem interleaving_matters :
    jointCumulant traceTwo 4 ![signMatrix, signMatrix, swapMatrix, swapMatrix] = 0 ∧
    jointCumulant traceTwo 4 ![signMatrix, swapMatrix, signMatrix, swapMatrix] = -1 := by
  rw [← cumulantTable_eq traceTwo 4 4 (by decide),
    ← cumulantTable_eq traceTwo 4 4 (by decide)]
  decide +kernel

theorem matrices_not_free : ¬FreelyIndependent traceTwo signMatrix swapMatrix := by
  intro h
  have hh := h 4 {0, 2} (by decide) (by decide)
  have he : (fun i : Fin 4 => if i ∈ ({0, 2} : Finset (Fin 4)) then signMatrix else swapMatrix) =
      ![signMatrix, swapMatrix, signMatrix, swapMatrix] := by
    funext i
    fin_cases i <;> rfl
  rw [he, interleaving_matters.2] at hh
  norm_num at hh

/-- Symmetric Bernoulli moments, independent of the cumulant computation. -/
theorem sign_moments :
    moment traceTwo signMatrix 1 = 0 ∧ moment traceTwo signMatrix 2 = 1 ∧
    moment traceTwo signMatrix 3 = 0 ∧ moment traceTwo signMatrix 4 = 1 ∧
    moment traceTwo signMatrix 5 = 0 ∧ moment traceTwo signMatrix 6 = 1 := by
  decide +kernel

/-- Higher cumulants are computed, rather than cut off at a fixed order. -/
theorem bernoulli_six : freeCumulant traceTwo signMatrix 6 = 2 := by
  rw [freeCumulant_rec _ _ (by decide), proper_sum_by_shapes, properShapes_small.2.2.2.2.2]
  simp [freeCumulant_one, freeCumulant_two_variance, freeCumulant_three,
    freeCumulant_four, freeCumulant_five, sign_moments.1, sign_moments.2.1,
    sign_moments.2.2.1, sign_moments.2.2.2.1, sign_moments.2.2.2.2.1,
    sign_moments.2.2.2.2.2]
  norm_num

/-- A constant unit has fifth cumulant zero; normalization is not optional. -/
theorem unit_fifth (φ : AlgebraicState ℚ ℚ) : freeCumulant φ 1 5 = 0 := by
  norm_num [freeCumulant_five, moment]

/-- A repeated diagram contributes twice; duplicate elimination is a semantic condition. -/
theorem duplicate_diagrams_overcount :
    let φ : AlgebraicState ℚ ℚ := ⟨LinearMap.id, rfl⟩
    [⊥, ⊥].foldl (diagramAdd φ (fun _ : Fin 2 => 1)) 0 = 2 ∧ wordMoment φ 2 (fun _ => 1) = 1 := by
  simp [diagramAdd, Finpartition.parts_bot, freeCumulant_one, moment, wordMoment]
  norm_num

/-- A joint semicircular profile on an alphabet; only monochromatic pairs contribute. -/
def semicircularProfile (n : ℕ) (a : Fin n → Bool) : ℚ :=
  if n = 2 ∧ ∀ i j, a i = a j then 1 else 0

noncomputable def semicircularState := cumulantWordState semicircularProfile

/-- Both generators have nonzero variance at every-order semicircular profiles. -/
theorem semicircular_generator (b : Bool) :
    HasSemicircularCumulants semicircularState (letter b) 1 := by
  intro n
  change freeCumulant (cumulantWordState semicircularProfile) (letter b) n = _
  rw [freeCumulant, cumulantWordState_cumulant _ (by simp [semicircularProfile])]
  simp [semicircularProfile]

/-- Mixed words vanish in every ordering, with no bounded-order assumption. -/
theorem semicircular_generators_free :
    FreelyIndependent semicircularState (letter false) (letter true) := by
  intro n s hs hne
  have hex : ∃ j : Fin n, j ∉ s := by
    by_contra! h
    exact hne (eq_univ_of_forall h)
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := hex
  have hn : ¬∀ i j : Fin n, (if i ∈ s then false else true) = (if j ∈ s then false else true) := by
    intro h
    simpa only [if_pos hi, if_neg hj, Bool.false_eq_true] using h i j
  have he : (fun i : Fin n => if i ∈ s then letter (R := ℚ) false else letter true) =
      (fun i => letter (R := ℚ) (if i ∈ s then false else true)) := by
    funext i
    split_ifs <;> rfl
  rw [he]
  change jointCumulant (cumulantWordState semicircularProfile) n _ = _
  rw [cumulantWordState_cumulant _ (by simp [semicircularProfile])]
  unfold semicircularProfile
  exact if_neg (fun h => hn h.2)

theorem semicircular_generator_nonzero (b : Bool) : letter (R := ℚ) b ≠ 0 := by
  intro h
  have hc := semicircular_generator b 2
  simp [freeCumulant, h] at hc
  exact zero_ne_one (((jointCumulant semicircularState 2).map_coord_zero
    (m := fun _ => 0) 0 rfl).symm.trans hc)

theorem semicircular_generators_distinct : letter (R := ℚ) false ≠ letter (R := ℚ) true := by
  intro h
  have hz := semicircular_generators_free 2 {0} (by decide) (by decide)
  have he : (fun i : Fin 2 => if i ∈ ({0} : Finset (Fin 2)) then letter (R := ℚ) false
      else letter true) = (fun _ => letter true) := by
    funext i
    simp only [h, ite_self]
  rw [he] at hz
  have ho := semicircular_generator true 2
  change freeCumulant semicircularState (letter true) 2 = 0 at hz
  norm_num [hz] at ho

/-- Free addition is witnessed by a nontrivial algebraic model. -/
theorem semicircular_sum :
    HasSemicircularCumulants semicircularState (letter false + letter true) 2 := by
  convert (semicircular_generator false).add semicircularState (semicircular_generator true)
    semicircular_generators_free using 1
  norm_num

/-- Ordered word moments distinguish crossing from noncrossing pairings. -/
theorem semicircular_word_moments :
    semicircularState ([false, false, true, true].map (letter (R := ℚ))).prod = 1 ∧
    semicircularState ([false, true, false, true].map (letter (R := ℚ))).prod = 0 := by
  change cumulantWordState semicircularProfile _ = _ ∧ cumulantWordState semicircularProfile _ = _
  rw [cumulantWordState_word, cumulantWordState_word]
  decide +kernel

end Examples
end Mettapedia.ProbabilityTheory.FreeProbability

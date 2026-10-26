import Mettapedia.ProbabilityTheory.Moments.HausdorffMoment
import Mettapedia.GSLT.Dynamics.OrderedListFold

/-!
# Ordered execution of finite Bernstein observations

A degree-`n` observation visits `n + 1` weighted samples, including samples with
zero weight. Its small-step execution uses the existing ordered-list fold and
has one additional finalization transition. Coefficients may be arbitrary real
numbers; the probability interpretation requires complete monotonicity and
normalization separately.

These are exact real-arithmetic semantics. Transition counts exclude constructing
the coefficients and evaluating the supplied continuous function.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.Moments.BernsteinObservation

open scoped unitInterval
open Mettapedia.ProbabilityTheory.Moments.HausdorffMoment
open Mettapedia.ProbabilityTheory.Moments.MomentSequences
open Mettapedia.GSLT.Dynamics.OrderedListFold

/-- Samples retain their degree-indexed occurrences, even when their weights vanish. -/
noncomputable def rows (m : ℕ → ℝ) (n : ℕ) : List (ℝ × I) :=
  List.ofFn (fun j : Fin (n + 1) => (bernsteinWeight m n j, bernstein.z j))

@[simp] theorem rows_length (m : ℕ → ℝ) (n : ℕ) : (rows m n).length = n + 1 :=
  List.length_ofFn

def accumulate (f : I → ℝ) (total : ℝ) (entry : ℝ × I) : ℝ :=
  total + entry.1 * f entry.2

/-- The independent list evaluator exposes the weighted sum without any probability premise. -/
theorem fold_eq (entries : List (ℝ × I)) (f : I → ℝ) (initial : ℝ) :
    entries.foldl (accumulate f) initial =
      initial + (entries.map (fun entry => entry.1 * f entry.2)).sum := by
  induction entries generalizing initial with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, accumulate]
      ring

theorem rows_fold (m : ℕ → ℝ) (n : ℕ) (f : C(I, ℝ)) (initial : ℝ) :
    (rows m n).foldl (accumulate f) initial = initial + bernsteinFunctional m n f := by
  rw [fold_eq]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_apply, bernsteinFunctional]

/-- Every supplied complete path has the specified observation and exact transition count. -/
theorem complete_execution (m : ℕ → ℝ) (n : ℕ) (f : C(I, ℝ)) (initial result : ℝ)
    (path : (theory (accumulate f)).RewritePath (.active (rows m n) initial) (.done result)) :
    result = initial + bernsteinFunctional m n f ∧ path.length = n + 2 := by
  obtain ⟨value, length⟩ := complete_path (accumulate f) (rows m n) initial result path
  exact ⟨value.trans (rows_fold m n f initial), by simpa [Nat.add_assoc] using length⟩

/-- The step relation supplies a terminating execution; its result is not a transition premise. -/
theorem execution_exists (m : ℕ → ℝ) (n : ℕ) (f : C(I, ℝ)) (initial : ℝ) :
    Nonempty ((theory (accumulate f)).RewritePath
      (.active (rows m n) initial) (.done (initial + bernsteinFunctional m n f))) := by
  rw [← rows_fold]
  exact ⟨runPath (accumulate f) (rows m n) initial⟩

theorem rows_nonnegative (m : ℕ → ℝ) (n : ℕ) (hcm : CompletelyMonotone m)
    (entry : ℝ × I) (occurs : entry ∈ rows m n) : 0 ≤ entry.1 := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp occurs
  exact bernsteinWeight_nonneg m hcm n j

theorem rows_mass (m : ℕ → ℝ) (n : ℕ) :
    ((rows m n).map Prod.fst).sum = m 0 := by
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range, bernsteinWeight_sum, momentFunctional_one]

namespace Controls

theorem degree_zero (m : ℕ → ℝ) : rows m 0 = [(m 0, 0)] := by
  simp [rows, List.ofFn_succ, bernsteinWeight, fwdDiffIter, bernstein.z]

/-- Zero-valued work is still visited: erasing it preserves the result but changes the path. -/
theorem zero_entry_retained (f : I → ℝ) (x : I) (initial : ℝ) :
    ([(0, x)] : List (ℝ × I)).foldl (accumulate f) initial = initial ∧
      (runPath (accumulate f) [(0, x)] initial).length = 2 := by
  constructor
  · simp [accumulate]
  · exact (complete_path (accumulate f) [(0, x)] initial _
      (runPath (accumulate f) [(0, x)] initial)).2

/-- Repeated rows contribute twice and retain two visits. -/
theorem repeated_entry (f : I → ℝ) (entry : ℝ × I) :
    [entry, entry].foldl (accumulate f) 0 = 2 * (entry.1 * f entry.2) ∧
      (runPath (accumulate f) [entry, entry] 0).length = 3 := by
  constructor
  · simp [accumulate]; ring
  · exact (complete_path (accumulate f) [entry, entry] 0 _
      (runPath (accumulate f) [entry, entry] 0)).2

end Controls

end Mettapedia.ProbabilityTheory.Moments.BernsteinObservation

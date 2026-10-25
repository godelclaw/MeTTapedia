import Mettapedia.GSLT.Distinction.Probabilistic.FiniteSubprediction
import Mettapedia.GraphTheory.Representation.SparseBackendChoice

/-!
# Array realization and resource account for finite prediction rows

The symbolic weighted-traversal module names transition coefficients and
prior values separately. The existing sparse backend compiles the coefficient
dependencies to an immutable array and reads current prior values in one
indexed fold. This file instantiates that realization for normalized kernels
and subdistribution kernels.

Theorems account for entry reads, accumulator updates and cursor advances.
They do not assert C instruction counts, allocation behavior, floating-point
rounding or wall-clock speed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionArray

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.Distinction.Probabilistic.FinitePrediction
open Mettapedia.GSLT.Distinction.Probabilistic.FiniteSubprediction
open Mettapedia.GraphTheory.Representation
open Mettapedia.GraphTheory.Representation.SparseBackendChoice
open Mettapedia.GraphTheory.Representation.SparseTraversalModule
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

variable {n m : Nat} {S T : Type*} [Fintype S] [Fintype T]

/-- Environment for one normalized prediction coordinate. -/
def probabilityEnvironment (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) : Nat → ℝ :=
  rowEnvironment (fun index => (kernel (enumeration index)).1 target)
    (fun index => prior.1 (enumeration index))

/-- Actual fused array execution of one prediction coordinate. -/
def arrayPredictionRow (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) : ℝ :=
  fused (probabilityEnvironment enumeration prior kernel target)
    (references (List.finRange n)) .zero

/-- The fused array result is the independently defined stochastic bind. -/
theorem arrayPredictionRow_eq_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    arrayPredictionRow enumeration prior kernel target = (bind prior kernel).1 target := by
  rw [arrayPredictionRow, fused_eq_source]
  change (rowExpression (List.finRange n)).eval
    (probabilityEnvironment enumeration prior kernel target) = _
  exact predictionRow_eq_bind enumeration prior kernel target

/-- The counted target loop reads exactly one compiled cell per input state. -/
theorem arrayPredictionRow_counted (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    ArrayFold.runCounted
        (fun total entry => total + entry.2 *
          probabilityEnvironment enumeration prior kernel target entry.1)
        (StackSlice.ofArray
          (compileRow (probabilityEnvironment enumeration prior kernel target)
            (references (List.finRange n)))) 0 =
      ((bind prior kernel).1 target, n) := by
  calc
    _ = (fused (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange n)) .zero,
        (references (List.finRange n)).length) := by
      simpa only [SparseTraversalModule.Expr.eval] using
        fused_entry_account (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange n)) .zero
    _ = ((bind prior kernel).1 target, n) := by
      change (arrayPredictionRow enumeration prior kernel target,
        (references (List.finRange n)).length) = _
      rw [arrayPredictionRow_eq_bind]
      simp [references]

/-- Array-fold target steps have the existing two-sided correspondence with
the interpreted ordered fold; arbitrary target steps cannot invent entries. -/
def rowOperationalCorrespondence (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :=
  ArrayFold.correspondence
    (fun (total : ℝ) (entry : Nat × ℝ) => total + entry.2 *
      probabilityEnvironment enumeration prior kernel target entry.1)

/-- Compilation starts in the relation used by the generic path laws. -/
theorem compiled_row_related (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    (rowOperationalCorrespondence enumeration prior kernel target).related
      (.active
        (interpretedEntries (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange n))) 0)
      (ArrayFold.compile (.active
        (interpretedEntries (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange n))) 0)) :=
  ArrayFold.compiled_related _ _

/-- The array-computed coordinate function forms the same probability law. -/
noncomputable def interpretedArrayPrediction (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) : Prob T :=
  ⟨arrayPredictionRow enumeration prior kernel,
    (fun target => by rw [arrayPredictionRow_eq_bind]; exact (bind prior kernel).2.1 target),
    by simp_rw [arrayPredictionRow_eq_bind]; exact (bind prior kernel).2.2⟩

theorem interpretedArrayPrediction_eq_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) :
    interpretedArrayPrediction enumeration prior kernel = bind prior kernel := by
  apply Subtype.ext
  funext target
  exact arrayPredictionRow_eq_bind enumeration prior kernel target

/-- Evaluate all output coordinates into an actual immutable array. -/
noncomputable def predictionArray (inputEnumeration : Fin n ≃ S)
    (outputEnumeration : Fin m ≃ T) (prior : Prob S) (kernel : S → Prob T) : Array ℝ :=
  Array.ofFn (fun output =>
    arrayPredictionRow inputEnumeration prior kernel (outputEnumeration output))

@[simp] theorem predictionArray_size (inputEnumeration : Fin n ≃ S)
    (outputEnumeration : Fin m ≃ T) (prior : Prob S) (kernel : S → Prob T) :
    (predictionArray inputEnumeration outputEnumeration prior kernel).size = m := by
  simp [predictionArray]

@[simp] theorem predictionArray_get (inputEnumeration : Fin n ≃ S)
    (outputEnumeration : Fin m ≃ T) (prior : Prob S) (kernel : S → Prob T)
    (output : Fin m) :
    (predictionArray inputEnumeration outputEnumeration prior kernel)[output.val]'(by simp) =
      (bind prior kernel).1 (outputEnumeration output) := by
  simp [predictionArray, arrayPredictionRow_eq_bind]

/-- The selected source-or-array backend has the same probability coordinate
for every price profile and expected reuse count. -/
def selectedPredictionRow (prices : Prices) (queries : Nat)
    (enumeration : Fin n ≃ S) (prior : Prob S) (kernel : S → Prob T) (target : T) : ℝ :=
  selected prices queries (probabilityEnvironment enumeration prior kernel target)
    (references (List.finRange n)) .zero

theorem selectedPredictionRow_eq_bind (prices : Prices) (queries : Nat)
    (enumeration : Fin n ≃ S) (prior : Prob S) (kernel : S → Prob T) (target : T) :
    selectedPredictionRow prices queries enumeration prior kernel target =
      (bind prior kernel).1 target := by
  rw [selectedPredictionRow, selected_eq_source]
  change (rowExpression (List.finRange n)).eval
    (probabilityEnvironment enumeration prior kernel target) = _
  exact predictionRow_eq_bind enumeration prior kernel target

/-! ## Subdistribution rows -/

def subdistributionEnvironment (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) : Nat → ℝ :=
  rowEnvironment (fun index => (kernel (enumeration index)).weight target)
    (fun index => prior.1 (enumeration index))

def arraySubpredictionRow (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) : ℝ :=
  fused (subdistributionEnvironment enumeration prior kernel target)
    (references (List.finRange n)) .zero

theorem arraySubpredictionRow_eq (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) (target : T) :
    arraySubpredictionRow enumeration prior kernel target =
      (subBind prior kernel).weight target := by
  rw [arraySubpredictionRow, fused_eq_source]
  change (rowExpression (List.finRange n)).eval
    (subdistributionEnvironment enumeration prior kernel target) = _
  exact subpredictionRow_eq enumeration prior kernel target

noncomputable def subdistributionTotalEnvironment (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) : Nat → ℝ :=
  rowEnvironment (fun index => (kernel (enumeration index)).total)
    (fun index => prior.1 (enumeration index))

noncomputable def arraySubpredictionTotal (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) : ℝ :=
  fused (subdistributionTotalEnvironment enumeration prior kernel)
    (references (List.finRange n)) .zero

theorem arraySubpredictionTotal_eq (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    arraySubpredictionTotal enumeration prior kernel = (subBind prior kernel).total := by
  rw [arraySubpredictionTotal, fused_eq_source]
  change (rowExpression (List.finRange n)).eval
    (subdistributionTotalEnvironment enumeration prior kernel) = _
  exact subpredictionTotal_eq enumeration prior kernel

/-- Refusal is reconstructed from the separately retained enabled-mass row. -/
theorem arraySubprediction_refusal (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → SubDistribution T) :
    1 - arraySubpredictionTotal enumeration prior kernel = refusal (subBind prior kernel) := by
  rw [arraySubpredictionTotal_eq]
  rfl

/-! ## Declared operation accounts -/

/-- Arithmetic-loop resources for one dense prediction row. -/
def rowArithmeticResources (inputs : Nat) : Resources := ArrayFold.account inputs

/-- Arithmetic-loop resources for every output row, excluding compilation,
outer-array construction and physical allocation costs. -/
def distributionArithmeticResources (inputs outputs : Nat) : Resources :=
  Resources.replicate outputs (rowArithmeticResources inputs)

theorem counted_row_resources (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    ArrayFold.account
      (ArrayFold.runCounted
        (fun total entry => total + entry.2 *
          probabilityEnvironment enumeration prior kernel target entry.1)
        (StackSlice.ofArray
          (compileRow (probabilityEnvironment enumeration prior kernel target)
            (references (List.finRange n)))) 0).2 = rowArithmeticResources n := by
  rw [arrayPredictionRow_counted]
  rfl

theorem distributionArithmeticResources_coordinates (inputs outputs : Nat) :
    (distributionArithmeticResources inputs outputs).reads = outputs * inputs ∧
    (distributionArithmeticResources inputs outputs).writes = outputs * inputs ∧
    (distributionArithmeticResources inputs outputs).time = outputs * (3 * inputs + 1) ∧
    (distributionArithmeticResources inputs outputs).allocated = 0 ∧
    (distributionArithmeticResources inputs outputs).peakTemporary = 0 := by
  simp [distributionArithmeticResources, rowArithmeticResources,
    Resources.replicate, ArrayFold.account]

/-- Source execution includes a finalization transition; the fused target
counts the `n` actual entry reads separately. Both have the same endpoint. -/
theorem source_target_account_boundary (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    (rowPath (List.finRange n)).length = n + 1 ∧
    (ArrayFold.runCounted
      (fun total entry => total + entry.2 *
        probabilityEnvironment enumeration prior kernel target entry.1)
      (StackSlice.ofArray
        (compileRow (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange n)))) 0).2 = n ∧
    arrayPredictionRow enumeration prior kernel target = (bind prior kernel).1 target := by
  exact ⟨by simp [rowPath_length], by rw [arrayPredictionRow_counted],
    arrayPredictionRow_eq_bind enumeration prior kernel target⟩

namespace Controls

noncomputable def nativeFixturePrior : Prob (Fin 2) :=
  ⟨![1 / 4, 3 / 4], by
    constructor
    · intro state
      fin_cases state <;> norm_num
    · norm_num [Fin.sum_univ_two]⟩

noncomputable def nativeFixtureFirstRow : Prob (Fin 2) :=
  ⟨![3 / 4, 1 / 4], by
    constructor
    · intro state
      fin_cases state <;> norm_num
    · norm_num [Fin.sum_univ_two]⟩

noncomputable def nativeFixtureSecondRow : Prob (Fin 2) :=
  ⟨![1 / 8, 7 / 8], by
    constructor
    · intro state
      fin_cases state <;> norm_num
    · norm_num [Fin.sum_univ_two]⟩

noncomputable def nativeFixtureKernel (state : Fin 2) : Prob (Fin 2) :=
  if state = 0 then nativeFixtureFirstRow else nativeFixtureSecondRow

/-- Kernel-checked counterpart of the native provider's primary 2×2 fixture. -/
theorem native_fixture_coordinates :
    arrayPredictionRow (Equiv.refl (Fin 2)) nativeFixturePrior nativeFixtureKernel 0 = 9 / 32 ∧
      arrayPredictionRow (Equiv.refl (Fin 2)) nativeFixturePrior nativeFixtureKernel 1 = 23 / 32 := by
  constructor <;>
    rw [arrayPredictionRow_eq_bind] <;>
    norm_num [bind_apply, nativeFixturePrior, nativeFixtureKernel,
      nativeFixtureFirstRow, nativeFixtureSecondRow, Fin.sum_univ_two]

/-- The declared price model may choose different implementations at different
reuse counts while the probability answer remains fixed. -/
theorem route_selection_can_change :
    profitable SparseBackendChoice.Controls.prices 2 1 = false ∧
      profitable SparseBackendChoice.Controls.prices 2 10 = true :=
  SparseBackendChoice.Controls.compilation_needs_reuse

/-- A one-input, two-output law performs one entry read for each requested
coordinate; the resource model must not report an empty execution. -/
theorem one_input_row_is_not_free (enumeration : Fin 1 ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (target : T) :
    (ArrayFold.runCounted
      (fun total entry => total + entry.2 *
        probabilityEnvironment enumeration prior kernel target entry.1)
      (StackSlice.ofArray
        (compileRow (probabilityEnvironment enumeration prior kernel target)
          (references (List.finRange 1)))) 0).2 = 1 ∧
      (rowArithmeticResources 1).reads = 1 := by
  constructor
  · rw [arrayPredictionRow_counted]
  · rfl

end Controls

end Mettapedia.GSLT.Distinction.Probabilistic.FinitePredictionArray

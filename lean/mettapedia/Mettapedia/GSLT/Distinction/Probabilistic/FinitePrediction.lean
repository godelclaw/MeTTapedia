import Mettapedia.ProbabilityTheory.FiniteLumpability
import Mettapedia.GraphTheory.Representation.SparseTraversalModule
import Mettapedia.GSLT.Distinction.Probabilistic.FiniteChains

/-!
# Finite stochastic prediction through the weighted traversal module

An output coordinate of a finite kernel prediction is an ordered sum of
transition contributions. The existing `SparseTraversal` presentation builds
that sum as an expression, retaining one occurrence per supplied input state.
Its independent interpretation is finite stochastic `Prob.bind`.

Coefficient and input-value names occupy disjoint even and odd slots. An
explicit equivalence enumerates a general finite input carrier. Complete
enumerations preserve the probability law; repeated or missing contributions
are not silently normalized. The arithmetic execution constructs a law and
is distinct from sampling a successor under that law.

The probabilistic GSLT adapter retains complete transition weights, while
the execution bridge retains the symbolic construction path and its length.
Exact observation squares transport the computed law, not those paths.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic.FinitePrediction

open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.Prob
open Mettapedia.ProbabilityTheory.FiniteLumpability
open Mettapedia.GraphTheory.Representation.SparseTraversalModule
open Mettapedia.GSLT.Dynamics
open scoped BigOperators

variable {n : Nat}

def coefficientKey (index : Fin n) : Nat := 2 * index.val

def inputKey (index : Fin n) : Nat := 2 * index.val + 1

theorem coefficientKey_ne_inputKey (first second : Fin n) :
    coefficientKey first ≠ inputKey second := by
  simp only [coefficientKey, inputKey]
  omega

/-- An input occurrence contributes its transition coefficient times its
current prior weight. Names retain the distinction between these two roles. -/
def references (inputs : List (Fin n)) : List Entry :=
  inputs.map (fun index => (coefficientKey index, inputKey index))

/-- A bounded name interpretation; unused names evaluate to zero. -/
def rowEnvironment {R : Type*} [Zero R] (weights values : Fin n → R) (key : Nat) : R :=
  if h : key / 2 < n then
    if key % 2 = 0 then weights ⟨key / 2, h⟩ else values ⟨key / 2, h⟩
  else 0

@[simp] theorem environment_coefficient {R : Type*} [Zero R]
    (weights values : Fin n → R) (index : Fin n) :
    rowEnvironment weights values (coefficientKey index) = weights index := by
  have quotient : 2 * index.val / 2 = index.val := by omega
  have remainder : (2 * index.val) % 2 = 0 := by omega
  simp [rowEnvironment, coefficientKey, quotient, remainder, index.isLt]

@[simp] theorem environment_input {R : Type*} [Zero R]
    (weights values : Fin n → R) (index : Fin n) :
    rowEnvironment weights values (inputKey index) = values index := by
  have quotient : (2 * index.val + 1) / 2 = index.val := by omega
  have remainder : (2 * index.val + 1) % 2 = 1 := by omega
  simp [rowEnvironment, inputKey, quotient, remainder, index.isLt]

/-- The actual symbolic output of the existing traversal presentation. -/
def rowExpression (inputs : List (Fin n)) : Expr :=
  (references inputs).foldl update .zero

def rowValue {R : Type*} [Semiring R] (weights values : Fin n → R)
    (inputs : List (Fin n)) : R :=
  (rowExpression inputs).eval (rowEnvironment weights values)

/-- Interpreting the ordered construction sums exactly its supplied occurrences. -/
theorem rowValue_eq_sum {R : Type*} [Semiring R] (weights values : Fin n → R)
    (inputs : List (Fin n)) :
    rowValue weights values inputs = (inputs.map (fun i => weights i * values i)).sum := by
  rw [rowValue, rowExpression, completed_expression_eval, Mettapedia.Algebra.SparseLinearMap.rowRun_eq]
  simp [interpretedEntries, references, Expr.eval, List.map_map, Function.comp_def]

/-- Removing only zero contributions preserves the arithmetic observer.
The retained occurrences, expression and transition count may change. -/
theorem rowValue_filter {R : Type*} [Semiring R] (weights values : Fin n → R)
    (keep : Fin n → Bool) (discarded : ∀ i, keep i = false → weights i * values i = 0)
    (inputs : List (Fin n)) :
    rowValue weights values (inputs.filter keep) = rowValue weights values inputs := by
  simp only [rowValue_eq_sum]
  induction inputs with
  | nil => rfl
  | cons first rest ih =>
      cases h : keep first with
      | false => simp [h, discarded first h, ih]
      | true => simp [h, ih]

/-- A construction path in the authored language, reusing its existing compiler. -/
def rowPath (inputs : List (Fin n)) :
    (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLT language).RewritePath
      (statePattern (.active (references inputs) .zero))
      (statePattern (.done (rowExpression inputs))) :=
  constructionPath (references inputs) .zero

theorem rowPath_length (inputs : List (Fin n)) :
    (rowPath inputs).length = inputs.length + 1 := by
  change (constructionPath (references inputs) .zero).length = inputs.length + 1
  rw [constructionPath_length]
  simp [references]

/-- Every complete source-fold execution has the same interpreted result and
the same entry count; the initial expression has not been replaced by an oracle. -/
theorem complete_row_path {R : Type} [Semiring R] (weights values : Fin n → R)
    (inputs : List (Fin n)) (result : Expr)
    (path : (OrderedListFold.theory update).RewritePath
      (.active (references inputs) .zero) (.done result)) :
    result.eval (rowEnvironment weights values) =
        (inputs.map (fun i => weights i * values i)).sum ∧
      path.length = inputs.length + 1 := by
  obtain ⟨same, length⟩ := OrderedListFold.complete_path update (references inputs) .zero result path
  constructor
  · rw [same]
    exact rowValue_eq_sum weights values inputs
  · simpa [references] using length

section Prediction

variable {S T C D : Type*} [Fintype S] [Fintype T]

/-- A finite input representation is supplied explicitly. No fixed ordering
of the abstract carrier is assumed. -/
noncomputable def predictionRow (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (outcome : T) : ℝ :=
  rowValue (fun i => (kernel (enumeration i)).1 outcome)
    (fun i => prior.1 (enumeration i)) (List.finRange n)

/-- The independently interpreted module output is the requested prediction coordinate. -/
theorem predictionRow_eq_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (outcome : T) :
    predictionRow enumeration prior kernel outcome = (bind prior kernel).1 outcome := by
  rw [predictionRow, rowValue_eq_sum, ← Fin.sum_univ_def, bind_apply]
  rw [enumeration.sum_comp (fun s => (kernel s).1 outcome * prior.1 s)]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-- A sparse traversal is exact when each discarded coordinate contributes
zero. No renormalization or independence assumption is needed. -/
theorem sparse_predictionRow_eq_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (outcome : T) (keep : Fin n → Bool)
    (discarded : ∀ i, keep i = false →
      (kernel (enumeration i)).1 outcome * prior.1 (enumeration i) = 0) :
    rowValue (fun i => (kernel (enumeration i)).1 outcome)
      (fun i => prior.1 (enumeration i)) ((List.finRange n).filter keep) =
        (bind prior kernel).1 outcome := by
  rw [rowValue_filter _ _ keep discarded]
  exact predictionRow_eq_bind enumeration prior kernel outcome

/-- The operational path has one transition per input occurrence and one
finalization; its arithmetic observer is the kernel prediction. -/
theorem prediction_execution (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) (outcome : T) :
    (rowPath (List.finRange n)).length = n + 1 ∧
      (rowExpression (List.finRange n)).eval
        (rowEnvironment (fun i => (kernel (enumeration i)).1 outcome)
          (fun i => prior.1 (enumeration i))) = (bind prior kernel).1 outcome := by
  exact ⟨by simp [rowPath_length], predictionRow_eq_bind enumeration prior kernel outcome⟩

/-- Changing the enumeration may change the construction history but preserves
the complete probability law. -/
theorem predictionRow_enumeration_independent {m : Nat}
    (first : Fin n ≃ S) (second : Fin m ≃ S) (prior : Prob S)
    (kernel : S → Prob T) :
    predictionRow first prior kernel = predictionRow second prior kernel := by
  funext outcome
  rw [predictionRow_eq_bind, predictionRow_eq_bind]

/-- The output is computed by the module's arithmetic interpretation;
normalization follows from its correspondence with stochastic prediction. -/
noncomputable def interpretedPrediction (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) : Prob T :=
  ⟨predictionRow enumeration prior kernel,
    (fun t => by rw [predictionRow_eq_bind]; exact (bind prior kernel).2.1 t), by
      simp_rw [predictionRow_eq_bind]
      exact (bind prior kernel).2.2⟩

theorem interpretedPrediction_eq_bind (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : S → Prob T) : interpretedPrediction enumeration prior kernel = bind prior kernel := by
  apply Subtype.ext
  funext outcome
  exact predictionRow_eq_bind enumeration prior kernel outcome

/-- Observing the constructed distribution commutes with prediction by the
supplied coarse kernel exactly under the row compatibility contract. -/
theorem observed_prediction [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
    (enumeration : Fin n ≃ S) (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D)
    (rows : ∀ s, coarsen (fine s) targetView = coarse (sourceView s)) (prior : Prob S) :
    coarsen (interpretedPrediction enumeration prior fine) targetView =
      bind (coarsen prior sourceView) coarse := by
  rw [interpretedPrediction_eq_bind]
  exact coarsen_bind_of_rows sourceView targetView fine coarse rows prior

/-- Both sides of an exact observation square may use their own finite
enumerations and the same operational presentation. -/
theorem observed_interpretedPrediction {m : Nat}
    [Fintype C] [Fintype D] [DecidableEq C] [DecidableEq D]
    (fineEnumeration : Fin n ≃ S) (coarseEnumeration : Fin m ≃ C)
    (sourceView : S → C) (targetView : T → D)
    (fine : S → Prob T) (coarse : C → Prob D)
    (rows : ∀ s, coarsen (fine s) targetView = coarse (sourceView s)) (prior : Prob S) :
    coarsen (interpretedPrediction fineEnumeration prior fine) targetView =
      interpretedPrediction coarseEnumeration (coarsen prior sourceView) coarse := by
  simpa only [interpretedPrediction_eq_bind] using
    observed_prediction fineEnumeration sourceView targetView fine coarse rows prior

end Prediction

section ProbabilisticSystem

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S : Type*} [Fintype S]

/-- Finite probability kernels supply the existing chain semantics, with an
explicit family of observables. No support erasure is performed. -/
def asChain (kernel : A → S → Prob S) (observe : Atom → S → ℝ) :
    LabelledMarkovChain ℝ A Atom S where
  trans action source := (kernel action source).1
  isDistribution action source :=
    ⟨(kernel action source).2.1, (kernel action source).2.2⟩
  observe := observe

open Classical in
/-- A predicate's probability under the computed output is the prior-weighted
probabilistic GSLT observation of that predicate after one labelled step. -/
theorem prediction_predicate_mass (enumeration : Fin n ≃ S) (prior : Prob S)
    (kernel : A → S → Prob S) (observe : Atom → S → ℝ)
    (action : A) (held : S → Prop) :
    (∑ target, if held target then
        (interpretedPrediction enumeration prior (kernel action)).1 target else 0) =
      ∑ source, prior.1 source *
        (chainSystem (asChain kernel observe)).prob action source held := by
  rw [interpretedPrediction_eq_bind]
  simpa only [prob_eq_sum, asChain, mul_ite, mul_one, mul_zero] using
    expectation_bind prior (kernel action) (fun target => if held target then (1 : ℝ) else 0)

end ProbabilisticSystem

namespace Controls

/-- Exact rational arithmetic exercises both parameter roles. -/
theorem rational_prediction_coordinate :
    rowValue (fun i : Fin 2 => if i = 0 then (1 / 4 : ℚ) else 3 / 4)
      (fun _ => (1 / 2 : ℚ)) [0, 1] = 1 / 2 := by
  rw [rowValue_eq_sum]
  norm_num

/-- Each occurrence contributes: duplicating an input doubles this unit row. -/
theorem duplicate_contribution :
    rowValue (fun _ : Fin 1 => (1 : ℚ)) (fun _ => 1) [0] = 1 ∧
      rowValue (fun _ : Fin 1 => (1 : ℚ)) (fun _ => 1) [0, 0] = 2 := by
  norm_num [rowValue_eq_sum]

/-- Omitting an input with positive mass changes the result; it is not a
normalized probability law. The empty traversal still has a finalization. -/
theorem omitted_contribution :
    rowValue (fun _ : Fin 1 => (1 : ℚ)) (fun _ => 1) [] = 0 ∧
      (rowPath ([] : List (Fin 1))).length = 1 := by
  simp [rowValue_eq_sum, rowPath_length]

/-- A valid zero-elimination lowers the entry count while preserving the
arithmetic answer. Preserving that answer does not require equal paths. -/
theorem zero_elimination_shortens_execution :
    rowValue (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 0)
      (fun _ => 1) [0, 1] =
        rowValue (fun i : Fin 2 => if i = 0 then (1 : ℚ) else 0) (fun _ => 1) [0] ∧
    (rowPath ([0, 1] : List (Fin 2))).length = 3 ∧
    (rowPath ([0] : List (Fin 2))).length = 2 := by
  norm_num [rowValue_eq_sum, rowPath_length]

/-- Equal arithmetic answers can have different occurrence histories. An
endpoint observer alone cannot justify preserving the symbolic output. -/
theorem reordering_preserves_value_not_expression :
    rowValue (fun i : Fin 2 => (i.val + 1 : ℚ)) (fun _ => 1) [0, 1] =
      rowValue (fun i : Fin 2 => (i.val + 1 : ℚ)) (fun _ => 1) [1, 0] ∧
      rowExpression ([0, 1] : List (Fin 2)) ≠ rowExpression ([1, 0] : List (Fin 2)) := by
  constructor
  · norm_num [rowValue_eq_sum]
  · decide

/-- A source program finishing at a fabricated zero result is not licensed
by the declared root strategy, even though a forward simulation alone could
not exclude extra target transitions. -/
theorem spurious_finish_rejected :
    statePattern (.done .zero) ∉
      rootSuccessors (statePattern (.active (references ([0] : List (Fin 1))) .zero)) := by
  rw [root_step_iff]
  simp [step?, OrderedListFold.step?, references, statePattern]

end Controls

end Mettapedia.GSLT.Distinction.Probabilistic.FinitePrediction

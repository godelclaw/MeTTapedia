import Mettapedia.GraphTheory.Representation.ArraySparseFrontier
import Mettapedia.GraphTheory.Representation.SparseTraversalModule

/-!
# Observation- and cost-qualified sparse backend choice

The source language builds arithmetic expressions; the fused target performs
arithmetic while traversing a compiled array. Their endpoints agree for every
environment and every initial expression. Fusing need not retain expression
allocation or intermediate constructor observations.

Backend selection uses the established conversion-amortization equations.
The supplied operation prices are a declared cost profile, not measurements
or a proof about a particular CeTTa release. Profitability never substitutes
for the independent semantic correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.SparseBackendChoice

open Mettapedia.Algebra
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.LanguageDef.CArray0SequenceHosting

variable {R : Type} [Zero R] [Add R] [Mul R]

/-- Compile symbolic weighted references to their coefficient payload.
Input values remain a separate current environment, not cached in the plan. -/
def compileRow (environment : Nat → R) (entries : List SparseTraversalModule.Entry) :
    Array (Nat × R) := (SparseTraversalModule.interpretedEntries environment entries).toArray

def fused (environment : Nat → R) (entries : List SparseTraversalModule.Entry)
    (initial : SparseTraversalModule.Expr) : R :=
  ArraySparseFrontier.weightedRow (compileRow environment entries) environment
    (initial.eval environment)

/-- The fused array loop is a separately implemented target. Its endpoint
is the semantic interpretation of the actual source expression construction. -/
theorem fused_eq_source (environment : Nat → R) (entries : List SparseTraversalModule.Entry)
    (initial : SparseTraversalModule.Expr) :
    fused environment entries initial =
      (entries.foldl SparseTraversalModule.update initial).eval environment := by
  rw [fused, ArraySparseFrontier.weightedRow_eq]
  simp only [compileRow, List.toList_toArray]
  exact (SparseTraversalModule.completed_expression_eval environment entries initial).symm

omit [Zero R] [Add R] [Mul R] in
/-- Cached code may be reused under new inputs when all coefficient
dependencies still agree. Unused environment coordinates need not agree. -/
theorem compileRow_congr (first second : Nat → R)
    (entries : List SparseTraversalModule.Entry)
    (same : ∀ entry ∈ entries, first entry.1 = second entry.1) :
    compileRow first entries = compileRow second entries := by
  unfold compileRow SparseTraversalModule.interpretedEntries
  apply congrArg List.toArray
  apply List.map_congr_left
  intro entry member
  rw [same entry member]

theorem cached_row_current (cached current : Nat → R)
    (entries : List SparseTraversalModule.Entry) (initial : SparseTraversalModule.Expr)
    (same : ∀ entry ∈ entries, cached entry.1 = current entry.1) :
    ArraySparseFrontier.weightedRow (compileRow cached entries) current (initial.eval current) =
      (entries.foldl SparseTraversalModule.update initial).eval current := by
  rw [compileRow_congr cached current entries same]
  exact fused_eq_source current entries initial

/-- The target loop visits exactly one compiled entry per source occurrence. -/
theorem fused_entry_account (environment : Nat → R) (entries : List SparseTraversalModule.Entry)
    (initial : SparseTraversalModule.Expr) :
    ArrayFold.runCounted (fun total entry => total + entry.2 * environment entry.1)
        (StackSlice.ofArray (compileRow environment entries)) (initial.eval environment) =
      (fused environment entries initial, entries.length) := by
  rw [ArrayFold.runCounted_exact]
  change (fused environment entries initial, (compileRow environment entries).size) = _
  simp only [compileRow, List.size_toArray, SparseTraversalModule.interpretedEntries,
    List.length_map]

structure Prices where
  compilation : Nat
  sourcePerEntry : Nat
  sourceFinish : Nat
  targetPerEntry : Nat
  targetFinish : Nat
deriving DecidableEq, Repr

def sourceWork (prices : Prices) (entries : Nat) : Nat :=
  entries * prices.sourcePerEntry + prices.sourceFinish

def targetWork (prices : Prices) (entries : Nat) : Nat :=
  entries * prices.targetPerEntry + prices.targetFinish

def profitable (prices : Prices) (entries queries : Nat) : Bool :=
  decide (migrateTime prices.compilation queries (targetWork prices entries) <
    stayTime queries (sourceWork prices entries))

def selected (prices : Prices) (queries : Nat) (environment : Nat → R)
    (entries : List SparseTraversalModule.Entry) (initial : SparseTraversalModule.Expr) : R :=
  if profitable prices entries.length queries then fused environment entries initial
  else (entries.foldl SparseTraversalModule.update initial).eval environment

theorem selected_eq_source (prices : Prices) (queries : Nat) (environment : Nat → R)
    (entries : List SparseTraversalModule.Entry) (initial : SparseTraversalModule.Expr) :
    selected prices queries environment entries initial =
      (entries.foldl SparseTraversalModule.update initial).eval environment := by
  unfold selected
  split_ifs
  · exact fused_eq_source environment entries initial
  · rfl

/-- Current input and coefficient environment is part of each request.
It is never hidden inside a reusable implementation-selection certificate. -/
structure Request (R : Type) where
  environment : Nat → R
  entries : List SparseTraversalModule.Entry
  initial : SparseTraversalModule.Expr

/-- Expose the independently proved lowering through the existing shared
realization API. Its observation is the arithmetic endpoint only; clients
requiring expression history must select the operational source route. -/
def realization (prices : Prices) (queries : Nat) :
    Mettapedia.GSLT.SimpleRealization (Request R) R R where
  compile _ request := selected prices queries request.environment request.entries request.initial
  observeSource _ request :=
    (request.entries.foldl SparseTraversalModule.update request.initial).eval request.environment
  observeArtifact _ value := value
  adequate _ request := selected_eq_source prices queries request.environment request.entries request.initial

/-- Any positive saving is judged against the one-time compilation cost,
using the existing representation economics theorem. -/
theorem profitable_iff_breakEven (prices : Prices) (entries queries saving : Nat)
    (difference : sourceWork prices entries = targetWork prices entries + saving) :
    profitable prices entries queries = true ↔ prices.compilation < queries * saving := by
  simp only [profitable, decide_eq_true_eq, difference]
  exact migrate_faster_iff_breakEven _ _ _ _

namespace Controls

structure OrderedDigits where
  value : Nat
deriving DecidableEq, Repr

instance : Zero OrderedDigits := ⟨⟨0⟩⟩
instance : Add OrderedDigits := ⟨fun a b => ⟨10 * a.value + b.value⟩⟩
instance : Mul OrderedDigits := ⟨fun a b => ⟨a.value * b.value⟩⟩

/-- Ordered lowering does not assume associativity. This carrier has no
semiring instance, so matrix reassociation cannot be invoked on it. -/
theorem fusion_preserves_nonassociative_arithmetic :
    (fused (fun key => (⟨key + 1⟩ : OrderedDigits)) [(0, 1), (2, 3)] .zero).value = 32 ∧
      (((⟨1⟩ : OrderedDigits) + ⟨2⟩) + ⟨3⟩).value ≠
        ((⟨1⟩ : OrderedDigits) + (⟨2⟩ + ⟨3⟩)).value := by
  rw [fused_eq_source]
  constructor <;> decide

def prices : Prices := ⟨100, 10, 1, 3, 1⟩

/-- The same program can justify compilation after reuse but not for one query. -/
theorem compilation_needs_reuse :
    profitable prices 2 1 = false ∧ profitable prices 2 10 = true := by decide

/-- A zero-cost readout cannot prove that execution is empty. -/
theorem zero_prices_do_not_erase_work :
    profitable ⟨0, 0, 0, 0, 0⟩ 2 10 = false ∧
      (SparseTraversalModule.constructionPath [(0, 1), (0, 1)] .zero).length = 3 := by
  constructor
  · decide
  · exact SparseTraversalModule.constructionPath_length _ _

/-- Caching a coefficient without checking its dependency changes the answer.
The input coordinate is unchanged in this counterexample. -/
theorem stale_coefficient_changes_result :
    ArraySparseFrontier.weightedRow
        (compileRow (fun key => if key = 0 then (2 : Nat) else 3) [(0, 1)])
        (fun key => if key = 0 then (4 : Nat) else 3) 0 = 6 ∧
      ([(0, 1)].foldl SparseTraversalModule.update .zero).eval
        (fun key => if key = 0 then (4 : Nat) else 3) = 12 := by
  rw [ArraySparseFrontier.weightedRow_eq]
  constructor <;> decide

end Controls

end Mettapedia.GraphTheory.Representation.SparseBackendChoice

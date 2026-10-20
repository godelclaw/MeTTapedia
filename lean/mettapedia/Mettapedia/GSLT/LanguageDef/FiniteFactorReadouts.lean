import Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
import Mettapedia.GSLT.LanguageDef.Cost.LiteralSignatureCommitment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Finite factor tables in the polynomial readout calculus

The compiler emits the existing `Read`, `Product`, `One`, `Sum` and `Zero`
constructors. Primitive table requests retain both indices using the checked
structural natural-number codec. These indices are local to the supplied table;
linking independently compiled tables needs a namespace or renaming bridge.
Execution is proved against a finite sum of
products, with ordered requests and separate arithmetic counts.

A supplied world list is occurrence-sensitive. Only the complete canonical
enumeration licenses the finite query-mass theorem. Repeating a world repeats
its contribution. The operation account belongs to this reference tree
evaluator and does not measure a native backend's time or allocation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts

open Mettapedia.OSLF.MeTTaIL.Syntax
open PolynomialReadoutCalculus PolynomialReadoutEvaluation
open Cost.LiteralSignatureCommitment

variable {Value : Type*} [CommSemiring Value] {worldCount factorCount : ℕ}

/-- A collision-free primitive request retaining world and factor indices. -/
def entry (world factor : ℕ) : Pattern :=
  .apply "FactorEntry" [encodeNat world, encodeNat factor]

/-- Literal requests retain both origin indices without a hash or collision premise. -/
theorem entry_equal_iff (world factor otherWorld otherFactor : ℕ) :
    entry world factor = entry otherWorld otherFactor ↔ world = otherWorld ∧ factor = otherFactor := by
  constructor
  · intro same
    have coordinates : encodeNat world = encodeNat otherWorld ∧ encodeNat factor = encodeNat otherFactor := by
      simpa [entry] using same
    exact ⟨encodeNat_injective coordinates.1, encodeNat_injective coordinates.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Decode a primitive request into the supplied finite table; other requests read zero. -/
def values (table : Fin worldCount → Fin factorCount → Value) : Pattern → Value
  | .apply "FactorEntry" [world, factor] =>
      match decodeNat? world, decodeNat? factor with
      | some w, some f => if hw : w < worldCount then
          if hf : f < factorCount then table ⟨w,hw⟩ ⟨f,hf⟩ else 0 else 0
      | _, _ => 0
  | _ => 0

/-- Every generated request decodes to exactly its source table entry. -/
theorem values_entry (table : Fin worldCount → Fin factorCount → Value)
    (world : Fin worldCount) (factor : Fin factorCount) :
    values table (entry world.val factor.val) = table world factor := by
  simp [values, entry, world.isLt, factor.isLt]

/-- An ordered product with an explicit unit terminator. -/
def productTree : List Pattern → Pattern
  | [] => one
  | request :: rest => mul (read request) (productTree rest)

/-- An ordered sum of row products with an explicit zero terminator. -/
def sumProducts : List (List Pattern) → Pattern
  | [] => zero
  | requests :: rest => add (productTree requests) (sumProducts rest)

/-- Product execution retains request order and counts every multiplication. -/
theorem run_productTree (query : Pattern → Value) (requests : List Pattern) :
    run query (productTree requests) =
      ⟨(requests.map query).prod, ⟨requests, 0, requests.length⟩⟩ := by
  induction requests with
  | nil => simp [productTree, one, FirstOrderCalculus.app, run]
  | cons request rest ih =>
      simp [productTree, run, PolynomialReadoutCalculus.read, mul, FirstOrderCalculus.app, ih]

/-- Sum-product execution has the declared value, request trace and arithmetic account. -/
theorem run_sumProducts (query : Pattern → Value) (rows : List (List Pattern)) :
    run query (sumProducts rows) =
      ⟨(rows.map fun requests => (requests.map query).prod).sum,
        ⟨rows.flatten, rows.length, (rows.map List.length).sum⟩⟩ := by
  induction rows with
  | nil => simp [sumProducts, zero, FirstOrderCalculus.app, run]
  | cons requests rest ih =>
      simp [sumProducts, run, add, FirstOrderCalculus.app, run_productTree, ih]

/-- Selected worlds retain their order and multiplicity, each with all factor requests. -/
def rows (worlds : List (Fin worldCount)) (query : Fin worldCount → Bool) (factors : ℕ) :
    List (List Pattern) :=
  (worlds.filter query).map fun world => (List.finRange factors).map fun factor => entry world.val factor.val

/-- Reference finite sum-product compilation into the existing polynomial calculus. -/
def compile (worlds : List (Fin worldCount)) (query : Fin worldCount → Bool) (factors : ℕ) : Pattern :=
  sumProducts (rows worlds query factors)

/-- Execution is the independently specified sum of products over selected occurrences. -/
theorem compile_value (table : Fin worldCount → Fin factorCount → Value)
    (worlds : List (Fin worldCount)) (query : Fin worldCount → Bool) :
    (run (values table) (compile worlds query factorCount)).value =
      ((worlds.filter query).map fun world => ∏ factor, table world factor).sum := by
  rw [compile, run_sumProducts]
  simp [rows, List.map_map, Function.comp_def, values_entry, ← Fin.prod_univ_def]

/-- The reference evaluator performs one request and multiplication per selected entry. -/
theorem compile_profile (table : Fin worldCount → Fin factorCount → Value)
    (worlds : List (Fin worldCount)) (query : Fin worldCount → Bool) :
    (run (values table) (compile worlds query factorCount)).profile =
      ⟨(rows worlds query factorCount).flatten, (worlds.filter query).length,
        (worlds.filter query).length * factorCount⟩ := by
  rw [compile, run_sumProducts]
  simp [rows, List.map_map, Function.comp_def, List.length_finRange, List.sum_replicate, Nat.mul_comm]

/-- A complete canonical world enumeration computes the finite query mass. -/
theorem complete_compile_value (table : Fin worldCount → Fin factorCount → Value)
    (query : Fin worldCount → Bool) :
    (run (values table) (compile (List.finRange worldCount) query factorCount)).value =
      ∑ world, if query world then ∏ factor, table world factor else 0 := by
  rw [compile_value, Fin.sum_univ_def]
  induction (List.finRange worldCount) with
  | nil => rfl
  | cons world rest ih =>
      cases h : query world <;> simp [h, ih]

open CertificateGSLT

/-- An accepted polynomial equality certificate preserves the compiled finite query mass. -/
theorem checked_replacement (table : Fin worldCount → Fin factorCount → Value)
    (query : Fin worldCount → Bool) (target : Pattern) (proof : RawOpenProof)
    (checked : checkOpenRaw validated []
      (equal target (compile (List.finRange worldCount) query factorCount)) proof = true) :
    (run (values table) target).value =
      ∑ world, if query world then ∏ factor, table world factor else 0 := by
  have identity := checked_polynomial_equal [] target
    (compile (List.finRange worldCount) query factorCount) proof checked (by simp)
  calc
    _ = (run (values table) (compile (List.finRange worldCount) query factorCount)).value := by
      rw [run_value, run_value, identity]
    _ = _ := complete_compile_value table query

namespace Controls

def table : Fin 4 → Fin 2 → ℚ := fun _ _ => 1/2
def anyTrue (world : Fin 4) : Bool := decide (world.val ≠ 0)
def noisyOr : Pattern := compile (List.finRange 4) anyTrue 2

theorem noisy_or_executes :
    (run (values table) noisyOr).value = 3/4 ∧
      (run (values table) noisyOr).profile.requests.length = 6 ∧
      (run (values table) noisyOr).profile.additions = 3 ∧
      (run (values table) noisyOr).profile.multiplications = 6 := by
  decide +kernel

theorem summing_explanations_overcounts :
    (1/2 + 1/2 : ℚ) = 1 ∧ (run (values table) noisyOr).value = 3/4 := by
  decide +kernel

theorem repeating_worlds_overcounts :
    (run (values table) (compile (worldCount := 4) [1,1] (fun _ => true) 2)).value = 1/2 ∧
      (run (values table) (compile (worldCount := 4) [1] (fun _ => true) 2)).value = 1/4 := by
  decide +kernel

def firstRow : Pattern := productTree [entry 1 0, entry 1 1]
def remainingRows : Pattern := sumProducts [[entry 2 0, entry 2 1], [entry 3 0, entry 3 1]]
def reordered : Pattern := add remainingRows firstRow

def reorderProof : RawOpenProof :=
  .node ⟨⟨"sum-comm"⟩, [remainingRows, firstRow]⟩ []

/-- A nontrivial authored module rule accepts the actual compiled readout. -/
theorem compiled_reorder_checks :
    checkOpenRaw validated [] (equal reordered noisyOr) reorderProof = true := by
  decide +kernel

/-- The checked module equality preserves the finite-table query value. Its
request order is a separate observable and changes in this example. -/
theorem certified_reordering_value :
    (run (values table) reordered).value = (run (values table) noisyOr).value := by
  have replacement := checked_replacement table anyTrue reordered reorderProof compiled_reorder_checks
  exact replacement.trans (complete_compile_value table anyTrue).symm

theorem certified_reordering_changes_requests :
    (run (values table) reordered).profile.requests ≠
      (run (values table) noisyOr).profile.requests := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts

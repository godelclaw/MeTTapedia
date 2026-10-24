import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic

/-!
An ordered keyed fold may update a table once per occurrence instead of
filtering the entire input separately for every key. The accumulator step is
arbitrary: neither associativity nor commutativity is assumed. Consequently
the law also applies to an explicitly scheduled, non-associative accumulator.
This is an algorithmic law, not a proof of a native hash-table implementation.
-/

namespace Mettapedia.Algorithms.Retrieval.GroupedFold

variable {K V R : Type*} [DecidableEq K]

def grouped (step : R → V → R) (initial : K → R) (entries : List (K × V)) : K → R :=
  entries.foldl (fun table row => Function.update table row.1 (step (table row.1) row.2)) initial

theorem observe_grouped (step : R → V → R) (initial : K → R)
    (entries : List (K × V)) (key : K) :
    grouped step initial entries key =
      entries.foldl (fun acc row => if row.1 = key then step acc row.2 else acc) (initial key) := by
  induction entries generalizing initial with
  | nil => rfl
  | cons row rest ih =>
    change grouped step (Function.update initial row.1 (step (initial row.1) row.2)) rest key = _
    rw [ih]
    simp only [List.foldl_cons]
    congr 1
    by_cases h : row.1 = key
    · simp [h]
    · simp [h, Ne.symm h]

private theorem fold_filter (entries : List V) (keep : V → Bool)
    (step : R → V → R) (initial : R) :
    (entries.filter keep).foldl step initial =
      entries.foldl (fun acc row => if keep row then step acc row else acc) initial := by
  induction entries generalizing initial with
  | nil => rfl
  | cons row rest ih =>
    cases h : keep row <;> simp [h, ih]

theorem observe_grouped_eq_filtered (step : R → V → R) (initial : K → R)
    (entries : List (K × V)) (key : K) :
    grouped step initial entries key =
      (entries.filter (fun row => decide (row.1 = key))).foldl
        (fun acc row => step acc row.2) (initial key) := by
  rw [observe_grouped, fold_filter]
  simp

theorem distinct_key_update_is_unobserved (step : R → V → R)
    (table : K → R) (key other : K) (value : V) (different : key ≠ other) :
    Function.update table other (step (table other) value) key = table key :=
  Function.update_of_ne different _ _

def groupedBlocks (step : R → V → R) (initial : K → R)
    (blocks : List (List (K × V))) : K → R :=
  blocks.foldl (fun table block => grouped step table block) initial

theorem groupedBlocks_eq_flatten (step : R → V → R) (initial : K → R)
    (blocks : List (List (K × V))) :
    groupedBlocks step initial blocks = grouped step initial blocks.flatten := by
  induction blocks generalizing initial with
  | nil => rfl
  | cons block rest ih =>
    simpa [groupedBlocks, grouped, List.foldl_append] using
      ih (initial := grouped step initial block)

example : grouped (fun xs (v : Nat) => xs ++ [v]) (fun (_ : Bool) => [])
    [(true, 2), (false, 8), (true, 5)] true = [2, 5] := by decide +kernel

example : grouped (fun xs (v : Nat) => xs ++ [v]) (fun (_ : Bool) => [])
    [(true, 2), (true, 5)] true ≠
      grouped (fun xs (v : Nat) => xs ++ [v]) (fun (_ : Bool) => [])
        [(true, 5), (true, 2)] true := by decide +kernel

#print axioms observe_grouped_eq_filtered

end Mettapedia.Algorithms.Retrieval.GroupedFold

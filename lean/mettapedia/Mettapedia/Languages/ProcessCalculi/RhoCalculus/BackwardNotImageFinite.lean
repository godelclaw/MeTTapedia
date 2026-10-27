import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic

/-!
# The ρ-calculus is not backward image-finite

The Hennessy–Milner characterization of bisimilarity by native types with past modalities asks that every process
have finitely many predecessors (`theorem1_substitutability_imageFinite`, hypothesis `hPredFinite`). The ρ-calculus
fails it, and not only syntactically: a process can have infinitely many predecessors that are pairwise not
structurally congruent.

- **Outputs are counted** (`outputCount`): the number of output constructors in a pattern. Every law of structural
  congruence keeps it (`outputCount_congruent`): permutations and flattening of parallel components, units, singletons,
  quote–drop, and congruence through every former.
- **One process, infinitely many predecessors** (`predecessor_reduces`): `@0!(q) | for(<- @0){0}` steps to the
  process `{0}` for every `q`, since the continuation does not use the received name.
- With `q` carrying `k` outputs (`nestedOutputs`), these predecessors have `k + 1` outputs each, so no finite set of
  processes covers them up to structural congruence (`not_predecessorFinite_modulo`), and the predecessor set of `{0}`
  is infinite (`not_predecessorFinite`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.BackwardNotImageFinite

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Counting outputs -/

mutual
/-- **The number of output constructors** in a pattern. -/
def outputCount : Pattern → ℕ
  | .bvar _ => 0
  | .fvar _ => 0
  | .apply head arguments => (if head = "POutput" then 1 else 0) + outputCountList arguments
  | .lambda _ body => outputCount body
  | .multiLambda _ _ body => outputCount body
  | .subst body replacement => outputCount body + outputCount replacement
  | .collection _ elements _ => outputCountList elements

/-- The number of output constructors in a list of patterns. -/
def outputCountList : List Pattern → ℕ
  | [] => 0
  | pattern :: patterns => outputCount pattern + outputCountList patterns
end

theorem outputCountList_append (first second : List Pattern) :
    outputCountList (first ++ second) = outputCountList first + outputCountList second := by
  induction first with
  | nil => simp [outputCountList]
  | cons head tail ih => simp only [List.cons_append, outputCountList, ih]; omega

theorem outputCountList_perm {first second : List Pattern} (perm : first.Perm second) :
    outputCountList first = outputCountList second := by
  induction perm with
  | nil => rfl
  | cons head _ ih => simp only [outputCountList, ih]
  | swap a b rest => simp only [outputCountList]; omega
  | trans _ _ first second => exact first.trans second

/-- Lists of the same length with the same counts position by position have the same count. -/
theorem outputCountList_pointwise : ∀ {first second : List Pattern} (_length : first.length = second.length),
    (∀ index (inFirst : index < first.length) (inSecond : index < second.length),
      outputCount (first.get ⟨index, inFirst⟩) = outputCount (second.get ⟨index, inSecond⟩)) →
      outputCountList first = outputCountList second
  | [], [], _, _ => rfl
  | [], _ :: _, length, _ => absurd length (by simp)
  | _ :: _, [], length, _ => absurd length (by simp)
  | head :: tail, head' :: tail', length, same => by
    simp only [outputCountList]
    have first := same 0 (by simp) (by simp)
    simp only [List.get_eq_getElem, List.getElem_cons_zero] at first
    have rest := outputCountList_pointwise (first := tail) (second := tail') (by simpa using length)
      fun index inFirst inSecond => by
        have := same (index + 1) (by simpa using inFirst) (by simpa using inSecond)
        simpa using this
    omega

/-- **Structural congruence keeps the number of outputs.** -/
theorem outputCount_congruent {first second : Pattern} (congruent : StructuralCongruence first second) :
    outputCount first = outputCount second := by
  induction congruent with
  | alpha _ _ equal => rw [equal]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second
  | par_singleton => simp [outputCount, outputCountList]
  | par_nil_left => simp [outputCount, outputCountList]
  | par_nil_right => simp [outputCount, outputCountList]
  | par_comm => simp only [outputCount, outputCountList]; omega
  | par_assoc => simp only [outputCount, outputCountList]; omega
  | par_cong _ _ length _ ih => exact outputCountList_pointwise length ih
  | par_flatten ps qs =>
    simp only [outputCount, outputCountList_append, outputCountList]
    omega
  | par_perm _ _ perm => exact outputCountList_perm perm
  | set_perm _ _ perm => exact outputCountList_perm perm
  | set_cong _ _ length _ ih => exact outputCountList_pointwise length ih
  | lambda_cong _ _ _ _ ih => exact ih
  | apply_cong _ _ _ length _ ih =>
    simp only [outputCount]
    rw [outputCountList_pointwise length ih]
  | collection_general_cong _ _ _ _ length _ ih => exact outputCountList_pointwise length ih
  | multiLambda_cong _ _ _ _ _ ih => exact ih
  | subst_cong _ _ _ _ _ _ ihBody ihReplacement =>
    simp only [outputCount]
    omega
  | quote_drop => simp [outputCount, outputCountList]
  | par_empty => simp [outputCount, outputCountList]

/-! ## Infinitely many predecessors -/

/-- The name `@0`. -/
def zeroName : Pattern := .apply "NQuote" [.apply "PZero" []]

/-- `@0!(q) | for(<- @0){0}`. -/
def predecessor (q : Pattern) : Pattern :=
  .collection .hashBag [.apply "POutput" [zeroName, q], .apply "PInput" [zeroName, .lambda none (.apply "PZero" [])]] none

/-- The process `{0}`. -/
def target : Pattern := .collection .hashBag [.apply "PZero" []] none

/-- **Every `@0!(q) | for(<- @0){0}` steps to `{0}`**: the continuation does not use the received name. -/
def predecessor_reduces (q : Pattern) : Reduces (predecessor q) target := by
  have step := Reduces.comm (n := zeroName) (q := q) (p := .apply "PZero" []) (rest := [])
  simp only [List.append_nil] at step
  have closed : semanticCommSubst (.apply "PZero" []) q = .apply "PZero" [] := by
    simp [semanticCommSubst, semanticSubstProc]
  rw [closed] at step
  exact step

/-- `k` nested outputs on `@0`. -/
def nestedOutputs : ℕ → Pattern
  | 0 => .apply "PZero" []
  | k + 1 => .apply "POutput" [zeroName, nestedOutputs k]

theorem outputCount_nestedOutputs : ∀ k, outputCount (nestedOutputs k) = k
  | 0 => by simp [nestedOutputs, outputCount, outputCountList]
  | k + 1 => by
    simp only [nestedOutputs, outputCount, outputCountList, outputCount_nestedOutputs k]
    simp [zeroName, outputCount, outputCountList]
    omega

theorem outputCount_predecessor (q : Pattern) : outputCount (predecessor q) = outputCount q + 1 := by
  simp [predecessor, zeroName, outputCount, outputCountList]
  omega

/-- **No finite set of processes covers the predecessors of `{0}` up to structural congruence.** -/
theorem not_predecessorFinite_modulo :
    ¬ ∃ covering : Finset Pattern, ∀ source, Nonempty (Reduces source target) →
      ∃ representative ∈ covering, StructuralCongruence source representative := by
  rintro ⟨covering, covers⟩
  let bound := covering.sup outputCount
  obtain ⟨representative, found, congruent⟩ :=
    covers (predecessor (nestedOutputs bound)) ⟨predecessor_reduces _⟩
  have counted := outputCount_congruent congruent
  rw [outputCount_predecessor, outputCount_nestedOutputs] at counted
  have below : outputCount representative ≤ bound := Finset.le_sup (f := outputCount) found
  omega

/-- **The predecessors of `{0}` are infinitely many**, so the ρ-calculus does not satisfy the backward
image-finiteness hypothesis of the Hennessy–Milner characterization. -/
theorem not_predecessorFinite : ¬ ∀ process : Pattern, Set.Finite {source | Nonempty (Reduces source process)} := by
  intro finite
  have injective : Function.Injective fun k => predecessor (nestedOutputs k) := by
    intro first second equal
    have := congrArg outputCount equal
    simp only [outputCount_predecessor, outputCount_nestedOutputs] at this
    omega
  have inside : ∀ k, predecessor (nestedOutputs k) ∈ {source | Nonempty (Reduces source target)} :=
    fun k => ⟨predecessor_reduces (nestedOutputs k)⟩
  exact Set.infinite_of_injective_forall_mem injective inside (finite target)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.BackwardNotImageFinite

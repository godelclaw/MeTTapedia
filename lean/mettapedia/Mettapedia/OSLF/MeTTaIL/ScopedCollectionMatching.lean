import Mettapedia.OSLF.MeTTaIL.CollectionMatching
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-!
# Collection decomposition with authored scoped captures

The collection operation uses the existing scoped argument matcher and rest
capture. Its independent judgment combines collection equality with the
existing ordered argument judgment. All source positions and assignment flow
are retained.

This theorem covers the outer collection decomposition. Element matching has
exactly the meaning of `GeneralScopedMatch.Arguments`; nested set decomposition
is not silently granted a stronger meaning.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching

open Syntax RuleBinding ScopedRuleMatching CanonicalBags CollectionSelection

def finish (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (rest : Option String) (kind : CollType) (initial : Assignment)
    (targets : List Pattern) : List Assignment :=
  match rest with
  | none => if targets.isEmpty then [initial] else []
  | some name =>
      (captureRest? rule spec ambient depth site (path ++ [index])
        initial name kind targets).toList

inductive Finished (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (kind : CollType) : Option String → Assignment → List Pattern → Assignment → Prop where
  | empty {initial} : Finished rule spec ambient site path depth index kind none initial [] initial
  | captured {name initial targets final} :
      captureRest? rule spec ambient depth site (path ++ [index])
        initial name kind targets = some final →
      Finished rule spec ambient site path depth index kind (some name) initial targets final

theorem finish_exact (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (rest : Option String) (kind : CollType) (initial final : Assignment)
    (targets : List Pattern) :
    final ∈ finish rule spec ambient site path depth index rest kind initial targets ↔
      Finished rule spec ambient site path depth index kind rest initial targets final := by
  cases rest with
  | none =>
      constructor
      · intro member
        simp only [finish] at member
        split at member
        next empty =>
          have same := List.isEmpty_iff.mp empty
          subst targets
          have equal : final = initial := by simpa using member
          subst final
          exact .empty
        next => simp at member
      · intro finished
        cases finished
        simp [finish]
  | some name =>
      constructor
      · intro member
        exact .captured (by simpa [finish] using member)
      · intro finished
        cases finished with
        | captured receipt => simpa [finish] using receipt

theorem rows_iff_arguments (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial final : Assignment) (schemas targets : List Pattern) :
    CollectionMatching.Rows
      (fun i before schema target after =>
        GeneralScopedMatch.Matches rule spec ambient site (path ++ [i]) depth
          before schema target after)
      index initial schemas targets final ↔
      GeneralScopedMatch.Arguments rule spec ambient site path depth initial index
        schemas targets final := by
  constructor
  · intro rows
    induction rows with
    | nil => exact .nil
    | cons head _ ih => exact .cons head ih
  · induction schemas generalizing index initial targets with
    | nil =>
        intro arguments
        cases arguments
        exact .nil
    | cons schema schemas ih =>
        intro arguments
        cases arguments with
        | cons head tail => exact .cons head (ih _ _ _ tail)

theorem matchRows_eq_arguments (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial : Assignment) (schemas targets : List Pattern) :
    CollectionMatching.matchRows
      (fun i before schema target =>
        matchAt rule spec ambient site (path ++ [i]) depth before schema target)
      index initial schemas targets =
      matchArgsAt rule spec ambient site path depth initial index schemas targets := by
  induction schemas generalizing index initial targets with
  | nil =>
      cases targets <;>
        simp only [CollectionMatching.matchRows, matchArgsAt, matchArgsAtWith]
  | cons schema schemas ih =>
      cases targets with
      | nil => simp only [CollectionMatching.matchRows, matchArgsAt, matchArgsAtWith]
      | cons target targets =>
          simp only [CollectionMatching.matchRows, matchArgsAt, matchArgsAtWith]
          apply List.flatMap_congr
          intro middle _
          exact ih (index + 1) middle targets

/-- The shared scoped matcher checks the selected rows; only collection
decomposition is supplied by the new equational allocator. -/
def run (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial : Assignment) (schemas : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern) : List Assignment :=
  (kindAllocations kind schemas.length targets).flatMap fun (selected, residual) =>
    (matchArgsAt rule spec ambient site path depth initial index schemas selected).flatMap
      fun middle => finish rule spec ambient site path depth (index + schemas.length)
        rest kind middle (arrange kind residual)

/-- The source judgment uses arbitrary residual presentations, including
overlap with selected set members. No enumeration occurs in this definition. -/
def Matches (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial : Assignment) (schemas : List Pattern) (rest : Option String)
    (kind : CollType) (targets : List Pattern) (final : Assignment) : Prop :=
  ∃ selected residual middle,
    Presents kind targets (selected ++ residual) ∧
    GeneralScopedMatch.Arguments rule spec ambient site path depth initial index
      schemas selected middle ∧
    Finished rule spec ambient site path depth (index + schemas.length)
      kind rest middle (arrange kind residual) final

theorem run_exact (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth index : Nat)
    (initial final : Assignment) (schemas : List Pattern) (rest : Option String)
    {kind : CollType} (unordered : kind ≠ .vec) {targets : List Pattern}
    (distinct : kind = .hashSet → targets.Nodup) :
    final ∈ run rule spec ambient site path depth index initial schemas rest kind targets ↔
      Matches rule spec ambient site path depth index initial schemas rest kind targets final := by
  have exactness := CollectionMatching.matchCollection_exact
    (element := fun i before schema target =>
      matchAt rule spec ambient site (path ++ [i]) depth before schema target)
    (Element := fun i before schema target after =>
      GeneralScopedMatch.Matches rule spec ambient site (path ++ [i]) depth
        before schema target after)
    (finish := finish rule spec ambient site path depth (index + schemas.length) rest kind)
    (Finish := Finished rule spec ambient site path depth (index + schemas.length) kind rest)
    (fun _ _ _ _ _ => GeneralScopedMatch.matchAt_iff)
    (fun _ _ _ => finish_exact ..) unordered distinct index initial final schemas
  simpa only [CollectionMatching.matchCollection, matchRows_eq_arguments,
    CollectionMatching.Matches, rows_iff_arguments, run, Matches] using exactness

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatching

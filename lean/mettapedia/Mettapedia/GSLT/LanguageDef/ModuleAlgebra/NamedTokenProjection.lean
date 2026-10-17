import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.BindingDeclarationElaboration

/-!
# The named-token projection's scope interpretation

Names are resolved in category-indexed namespaces. Environments are ordered
from the nearest binder outward; every binder contributes a de Bruijn level,
including binders of other categories. This is one explicit interpretation,
not a universal convention imposed on every language definition.

The executable lookup agrees with an independently stated nearest-binding
relation, yields the existing core's typed object variables, and commutes
with injective renaming of source names. BindingDeclarationElaboration supplies
the constructor-body wrapping law. These results do not prove the native AST
slot decoder or the preceding lexical and parser implementation adequate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedTokenProjection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A binder's exact source spelling and declared category. -/
abbrev Environment := List (String × String)

def resolve? : Environment → String → String → Option Nat
  | [], _, _ => none
  | (name, sort) :: outer, query, category =>
      if name = query ∧ sort = category then some 0
      else (resolve? outer query category).map Nat.succ

/-- The nearest matching source binder; intervening differently named or
sorted binders still contribute to the target index. -/
inductive Resolves : Environment → String → String → Nat → Prop
  | here (outer : Environment) (name sort : String) :
      Resolves ((name, sort) :: outer) name sort 0
  | there {outer : Environment} {name sort query category : String} {index : Nat}
      (different : ¬ (name = query ∧ sort = category))
      (tail : Resolves outer query category index) :
      Resolves ((name, sort) :: outer) query category (index + 1)

theorem resolves_iff (environment : Environment) (name sort : String) (index : Nat) :
    resolve? environment name sort = some index ↔ Resolves environment name sort index := by
  induction environment generalizing index with
  | nil =>
      constructor
      · simp [resolve?]
      · intro impossible; cases impossible
  | cons entry outer ih =>
      obtain ⟨boundName, boundSort⟩ := entry
      by_cases same : boundName = name ∧ boundSort = sort
      · obtain ⟨rfl, rfl⟩ := same
        constructor
        · intro found
          have zero : index = 0 := by simpa [resolve?] using found.symm
          subst index
          exact .here _ _ _
        · intro found
          cases found with
          | here => simp [resolve?]
          | there different _ => exact False.elim (different ⟨rfl, rfl⟩)
      · constructor
        · intro found
          simp only [resolve?, if_neg same, Option.map_eq_some_iff] at found
          obtain ⟨previous, found, rfl⟩ := found
          exact .there same ((ih previous).mp found)
        · intro found
          cases found with
          | here => exact False.elim (same ⟨rfl, rfl⟩)
          | there _ tail => simp [resolve?, same, (ih _).mpr tail]

def boundTypes (environment : Environment) : List TypeExpr :=
  environment.map fun entry => .base entry.2

theorem Resolves.lookup {environment : Environment} {name sort : String} {index : Nat}
    (resolved : Resolves environment name sort index) :
    (boundTypes environment)[index]? = some (.base sort) := by
  induction resolved with
  | here => rfl
  | there _ _ ih => simpa [boundTypes] using ih

theorem Resolves.in_scope {environment : Environment} {name sort : String} {index : Nat}
    (resolved : Resolves environment name sort index) : index < environment.length := by
  induction resolved with
  | here => simp
  | there _ _ ih => simpa using Nat.succ_lt_succ ih

theorem resolved_object (language : LanguageDef) (free : FreeTypeContext)
    {environment : Environment} {name sort : String} {index : Nat}
    (resolved : resolve? environment name sort = some index) :
    OpenPatternWellSorted language free (boundTypes environment) (.base sort) (.bvar index) := by
  have relation := (resolves_iff _ _ _ _).mp resolved
  refine ⟨.bvar relation.lookup, rfl, rfl, ?_⟩
  simpa [ScopeSafeAt, Pattern.isWellScopedAt, boundTypes] using relation.in_scope

/-- Renaming all source names coherently preserves their binding occurrence.
Injectivity is needed only for the names actually being identified by this
uniform map; a non-injective map can introduce capture. -/
theorem resolve_rename (rename : String → String) (injective : Function.Injective rename)
    (environment : Environment) (name sort : String) :
    resolve? (environment.map fun entry => (rename entry.1, entry.2)) (rename name) sort =
      resolve? environment name sort := by
  induction environment with
  | nil => rfl
  | cons entry outer ih =>
      obtain ⟨boundName, boundSort⟩ := entry
      simpa [resolve?, injective.eq_iff] using congrArg (fun value =>
        if boundName = name ∧ boundSort = sort then some 0 else value.map Nat.succ) ih

theorem shadowing_control : resolve? [("x", "Name"), ("x", "Name")] "x" "Name" = some 0 := by decide
theorem outer_reference_control : resolve? [("y", "Name"), ("x", "Name")] "x" "Name" = some 1 := by decide
theorem sorted_namespace_control : resolve? [("x", "TypeName"), ("x", "Name")] "x" "Name" = some 1 := by decide
theorem no_invented_binding_control : resolve? [("x", "Name")] "y" "Name" = none := by decide

/-- Identifying two spellings can capture the older occurrence: preservation
under arbitrary source renaming is false, even though both indices are typed. -/
theorem noninjective_renaming_captures :
    resolve? [("y", "Name"), ("x", "Name")] "x" "Name" = some 1 ∧
    resolve? ([("y", "Name"), ("x", "Name")].map fun entry => ("z", entry.2)) "z" "Name" = some 0 := by decide

#print axioms resolves_iff
#print axioms resolved_object
#print axioms resolve_rename
#print axioms noninjective_renaming_captures

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NamedTokenProjection

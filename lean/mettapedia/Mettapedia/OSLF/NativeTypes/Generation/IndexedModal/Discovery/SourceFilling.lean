import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

/-!
# Scoped contextual filling depends only on its exposed inputs

The selected hole is supplied directly. Variables hidden inside that hole
are never read by source reconstruction. Display metadata is erased only
after reconstructing the authored enclosing tree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.SourceFilling

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching DerivedContexts
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.NativeTypes.Modal Instantiation NativeBindingMatchInstantiation

mutual
theorem instantiate_congr (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (first second : ScopedRuleMatching.Assignment) (pattern : Pattern)
    (shape : treeSchema pattern = true)
    (agree : ∀ name ∈ fvarNames pattern, lookup first name = lookup second name) :
    instantiateWith? operation rule spec ambient site path depth first pattern =
      instantiateWith? operation rule spec ambient site path depth second pattern := by
  cases pattern with
  | fvar name => simp only [instantiateWith?, agree name (List.mem_singleton_self _)]
  | bvar index => simp only [instantiateWith?]
  | apply constructor arguments =>
      simp only [instantiateWith?, instantiateArgs_congr operation rule spec ambient site
        path depth first second 0 arguments shape agree]
  | lambda display body =>
      simp only [instantiateWith?, instantiate_congr operation rule spec ambient site
        (path ++ [0]) (depth + 1) first second body shape agree]
  | multiLambda arity display body =>
      simp only [instantiateWith?, instantiate_congr operation rule spec ambient site
        (path ++ [0]) (depth + arity) first second body shape agree]
  | subst | collection => cases shape
termination_by sizeOf pattern

theorem instantiateArgs_congr (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (first second : ScopedRuleMatching.Assignment) (offset : Nat) (patterns : List Pattern)
    (shape : treeSchemas patterns = true)
    (agree : ∀ name ∈ fvarNamesList patterns, lookup first name = lookup second name) :
    instantiateArgsWith? operation rule spec ambient site path depth first offset patterns =
      instantiateArgsWith? operation rule spec ambient site path depth second offset patterns := by
  cases patterns with
  | nil => simp only [instantiateArgsWith?]
  | cons pattern patterns =>
      have shapes := Bool.and_eq_true_iff.mp shape
      have headAgree : ∀ name ∈ fvarNames pattern, lookup first name = lookup second name :=
        fun name member => agree name (List.mem_append_left _ member)
      have tailAgree : ∀ name ∈ fvarNamesList patterns, lookup first name = lookup second name :=
        fun name member => agree name (List.mem_append_right _ member)
      simp only [instantiateArgsWith?,
        instantiate_congr operation rule spec ambient site (path ++ [offset]) depth
          first second pattern shapes.1 headAgree,
        instantiateArgs_congr operation rule spec ambient site path depth first second
          (offset + 1) patterns shapes.2 tailAgree]
termination_by sizeOf patterns
end

theorem fillArgs_split (operation : Pattern → Pattern → Pattern)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (assignment : ScopedRuleMatching.Assignment) (hole : Pattern) (rest : Position)
    (before : List Pattern) (selected : Pattern) (after : List Pattern) (offset : Nat) :
    fillArgs? operation rule spec ambient site path depth assignment hole before.length rest offset
      (before ++ selected :: after) = (do
        let leading ← instantiateArgsWith? operation rule spec ambient site path depth assignment offset before
        let inner ← fill? operation rule spec ambient site (path ++ [offset + before.length])
          depth assignment hole selected rest
        let suffix ← instantiateArgsWith? operation rule spec ambient site path depth assignment
          (offset + before.length + 1) after
        some (leading ++ inner :: suffix)) := by
  induction before generalizing offset with
  | nil => simp [fillArgs?, instantiateArgsWith?]
  | cons head tail ih =>
      simp only [List.cons_append, List.length_cons, fillArgs?, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_one_sub_one, ih, instantiateArgsWith?]
      simp only [Nat.add_assoc, Nat.add_comm 1 tail.length]
      cases instantiateWith? operation rule spec ambient site (path ++ [offset]) depth assignment head <;>
        try simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some]
      cases instantiateArgsWith? operation rule spec ambient site path depth assignment (offset + 1) tail <;>
        try simp only [Option.bind_none, Option.bind_some]
      cases fill? operation rule spec ambient site (path ++ [offset + (tail.length + 1)]) depth
        assignment hole selected rest <;> try simp only [Option.bind_none, Option.bind_some]
      cases instantiateArgsWith? operation rule spec ambient site path depth assignment
        (offset + (tail.length + 1) + 1) after <;> rfl

theorem names_append (before after : List Pattern) :
    fvarNamesList (before ++ after) = fvarNamesList before ++ fvarNamesList after := by
  induction before with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, fvarNamesList, ih, List.append_assoc]

theorem shapes_append (before after : List Pattern) :
    treeSchemas (before ++ after) = (treeSchemas before && treeSchemas after) := by
  induction before with
  | nil => rfl
  | cons head tail ih => simp only [List.cons_append, treeSchemas, ih, Bool.and_assoc]

/-- Replacing the hole and exposed captures by alpha-equal data preserves
the reconstructed source. No values for hidden focus variables are needed. -/
theorem fill_congr {needle host : Pattern} {context : OneHoleContext}
    (selected : Selects needle context host) (shape : treeSchema host = true)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient : Nat)
    (site : RulePatternSite) (path : List Nat) (depth : Nat)
    (first second : ScopedRuleMatching.Assignment) (left right : Pattern)
    (holes : left.eraseBinderMetadata = right.eraseBinderMetadata)
    (agree : ∀ name ∈ Occurrences.contextNames context,
      lookup first name = lookup second name) :
    (fill? Substitution.instantiateBVar rule spec ambient site path depth first left host
      (contextAddress context)).map Pattern.eraseBinderMetadata =
    (fill? Substitution.instantiateBVar rule spec ambient site path depth second right host
      (contextAddress context)).map Pattern.eraseBinderMetadata := by
  induction selected generalizing path depth with
  | here => simpa only [contextAddress, fill?, Option.map_some] using congrArg some holes
  | @apply host context constructor before after selected ih =>
      have shapes : treeSchemas before = true ∧ treeSchema host = true ∧ treeSchemas after = true := by
        simpa only [treeSchema, shapes_append, treeSchemas, Bool.and_eq_true, and_assoc] using shape
      have names : ∀ name ∈ fvarNamesList before ++ Occurrences.contextNames context ++ fvarNamesList after,
          lookup first name = lookup second name := by
        simpa only [Occurrences.contextNames, OneHoleContext.fill, fvarNames, names_append,
          fvarNamesList, List.append_assoc] using agree
      have leading := instantiateArgs_congr Substitution.instantiateBVar rule spec ambient site path depth
        first second 0 before shapes.1 (fun name member => names name (by simp [member]))
      have suffix := instantiateArgs_congr Substitution.instantiateBVar rule spec ambient site path depth
        first second (before.length + 1) after shapes.2.2 (fun name member => names name (by simp [member]))
      have inner := ih shapes.2.1 (path ++ [before.length]) depth
        (fun name member => names name (by simp [member]))
      simp only [contextAddress, fill?, fillArgs_split, Nat.zero_add, leading, suffix]
      cases instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth second 0 before <;>
        try simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some, Option.map_none]
      cases instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth second
        (before.length + 1) after <;>
        try simp only [Option.bind_none, Option.bind_some]
      all_goals
        cases firstFill : fill? Substitution.instantiateBVar rule spec ambient site
          (path ++ [before.length]) depth first left host (contextAddress context) <;>
          cases secondFill : fill? Substitution.instantiateBVar rule spec ambient site
            (path ++ [before.length]) depth second right host (contextAddress context) <;>
          simp only [firstFill, secondFill, Option.map_none, Option.map_some, Option.some.injEq,
            reduceCtorEq] at inner ⊢
      all_goals simp_all [Pattern.eraseBinderMetadata]
  | @lambda context body binder selected ih =>
      have inner := ih shape (path ++ [0]) (depth + 1) agree
      cases firstFill : fill? Substitution.instantiateBVar rule spec ambient site
        (path ++ [0]) (depth + 1) first left body (contextAddress context) <;>
        cases secondFill : fill? Substitution.instantiateBVar rule spec ambient site
          (path ++ [0]) (depth + 1) second right body (contextAddress context) <;>
        simp_all [contextAddress, fill?, Option.bind_eq_bind, Pattern.eraseBinderMetadata]
  | @multiLambda context body arity display selected ih =>
      have inner := ih shape (path ++ [0]) (depth + arity) agree
      cases firstFill : fill? Substitution.instantiateBVar rule spec ambient site
        (path ++ [0]) (depth + arity) first left body (contextAddress context) <;>
        cases secondFill : fill? Substitution.instantiateBVar rule spec ambient site
          (path ++ [0]) (depth + arity) second right body (contextAddress context) <;>
        simp_all [contextAddress, fill?, Option.bind_eq_bind, Pattern.eraseBinderMetadata]
  | substBody | substReplacement | collection => cases shape

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Discovery.SourceFilling

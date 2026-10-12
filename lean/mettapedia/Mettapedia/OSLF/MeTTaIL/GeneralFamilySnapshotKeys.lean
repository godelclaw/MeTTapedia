import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-!
# Executable equality for complete authored snapshots

The keys retain every source field, including display metadata, declaration
order, grammar syntax, binding spines, premise syntax and duplicate provider
rows. Injectivity proves that a successful comparison identifies the actual
snapshot rather than merely its name or selected declaration labels.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFamilySnapshotKeys

open Syntax GeneralExecutionAdmission

structure RuleKey where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  bindings : Option RuleBindingSpec
  deriving DecidableEq

def rule (source : RewriteRule) : RuleKey :=
  ⟨source.name, source.typeContext, source.premises, source.left, source.right, source.bindings⟩

theorem rule_injective : Function.Injective rule := by
  intro first second same
  cases first
  cases second
  simp only [rule, RuleKey.mk.injEq] at same
  rcases same with ⟨name, types, premises, left, right, bindings⟩
  subst_vars
  rfl

structure EquationKey where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
  bindings : Option RuleBindingSpec
  deriving DecidableEq

def equation (source : Equation) : EquationKey :=
  ⟨source.name, source.typeContext, source.premises, source.left, source.right, source.bindings⟩

theorem equation_injective : Function.Injective equation := by
  intro first second same
  cases first
  cases second
  simp only [equation, EquationKey.mk.injEq] at same
  rcases same with ⟨name, types, premises, left, right, bindings⟩
  subst_vars
  rfl

structure LanguageKey where
  name : String
  types : List TypeDecl
  terms : List GrammarRule
  equations : List EquationKey
  rewrites : List RuleKey
  deriving DecidableEq

def language (source : LanguageDef) : LanguageKey :=
  ⟨source.name, source.types, source.terms, source.equations.map equation, source.rewrites.map rule⟩

theorem language_injective : Function.Injective language := by
  intro first second same
  cases first
  cases second
  simp only [language, LanguageKey.mk.injEq] at same
  rcases same with ⟨name, types, terms, equations, rewrites⟩
  have equationsSame := (List.map_injective_iff.mpr equation_injective) equations
  have rewritesSame := (List.map_injective_iff.mpr rule_injective) rewrites
  subst_vars
  rfl

structure SnapshotKey where
  language : LanguageKey
  freeTypes : List (String × TypeExpr)
  provider : GeneralPremise.ProviderSnapshot
  deriving DecidableEq

def snapshot (source : Snapshot) : SnapshotKey :=
  ⟨language source.language, source.freeTypes, source.provider⟩

theorem snapshot_injective : Function.Injective snapshot := by
  intro first second same
  cases first
  cases second
  simp only [snapshot, SnapshotKey.mk.injEq] at same
  rcases same with ⟨language, freeTypes, provider⟩
  have languageSame := language_injective language
  subst_vars
  rfl

def checkSnapshot (first second : Snapshot) : Bool := decide (snapshot first = snapshot second)

theorem checkSnapshot_iff (first second : Snapshot) :
    checkSnapshot first second = true ↔ first = second := by
  simp only [checkSnapshot, decide_eq_true_eq]
  exact ⟨fun same => snapshot_injective same, congrArg snapshot⟩

def checkProfile (firstSnapshot secondSnapshot : Snapshot) (firstPermissions secondPermissions : Permissions) : Bool :=
  checkSnapshot firstSnapshot secondSnapshot && decide (firstPermissions = secondPermissions)

theorem checkProfile_iff (firstSnapshot secondSnapshot : Snapshot) (firstPermissions secondPermissions : Permissions) :
    checkProfile firstSnapshot secondSnapshot firstPermissions secondPermissions = true ↔
      firstSnapshot = secondSnapshot ∧ firstPermissions = secondPermissions := by
  simp only [checkProfile, Bool.and_eq_true, checkSnapshot_iff, decide_eq_true_eq]

#print axioms snapshot_injective
#print axioms checkProfile_iff

end Mettapedia.OSLF.MeTTaIL.GeneralFamilySnapshotKeys

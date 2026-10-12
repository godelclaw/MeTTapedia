import Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement

/-!
# Conditional execution at licensed typed occurrence sites

An occurrence uses the existing zipper and typing descent. Its permission is
an explicit finite operational profile, separate from structural occurrence
selection. Root rules execute in the complete context at the selected hole;
the surrounding context is filled only after the independently typed root
operation finishes. Whole-source and whole-target readouts retain all binder
frames, selected declaration positions and atomic query histories.

The site interface is proof-carrying. It is not a claim that every structural
slot is reduction-active, nor a complete site generator for every language.
Concrete admitted profiles construct their finite site families and earn
coverage separately.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.TypedContextualEquationExecution

open Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Exact typed descent at an operationally permitted zipper. The typing
derivation identifies binder sorts and the authored constructor parameters. -/
structure Site (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern) where
  context : OneHoleContext
  focus : Pattern
  focusBound : List TypeExpr
  focusType : TypeExpr
  permitted : context ∈ permissions
  source_eq : context.fill focus = source
  typed : TypedAt language free focus context bound expected focusBound focusType

namespace Site

variable {language : LanguageDef} {free : FreeTypeContext}
  {bound : List TypeExpr} {expected : TypeExpr}
  {permissions : List OneHoleContext} {source : Pattern}

theorem source_typed (site : Site language free bound expected permissions source) :
    HasType language free bound source expected :=
  site.source_eq ▸ site.typed.source_typed

theorem focus_typed (site : Site language free bound expected permissions source) :
    HasType language free site.focusBound site.focus site.focusType :=
  site.typed.focus_typed

theorem ambient_retained (site : Site language free bound expected permissions source) :
    ∃ binderPrefix, site.focusBound = binderPrefix ++ bound := site.typed.ambient_suffix

def root (typed : HasType language free bound source expected)
    (permitted : OneHoleContext.hole ∈ permissions) :
    Site language free bound expected permissions source where
  context := .hole
  focus := source
  focusBound := bound
  focusType := expected
  permitted := permitted
  source_eq := rfl
  typed := .here typed

end Site

/-- Context and declaration origin remain outside the complete atomic receipt. -/
structure Receipt where
  contextIndex : Nat
  context : OneHoleContext
  focusBound : List TypeExpr
  focusType : TypeExpr
  ruleIndex : Nat
  atomic : ConditionalEquationExecution.Receipt
  target : Pattern
  deriving DecidableEq, Repr

structure Pending where
  contextIndex : Nat
  context : OneHoleContext
  ruleIndex : Nat
  reason : ConditionalEquationExecution.Pending
  deriving DecidableEq, Repr

structure Outcome where
  receipts : List Receipt
  pending : List Pending
  deriving DecidableEq, Repr

/-- An actual local firing is plugged back into its original typed context.
The final check rejects representation or sorting changes in the surroundings. -/
def fillReceipt? (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (contextIndex ruleIndex : Nat)
    (context : OneHoleContext) (focusBound : List TypeExpr) (focusType : TypeExpr)
    (atomic : ConditionalEquationExecution.Receipt) : Option Receipt :=
  let target := context.fill atomic.target
  if target.isWellScopedAt bound.length && checkHasType language free bound target expected then
    some ⟨contextIndex, context, focusBound, focusType, ruleIndex, atomic, target⟩
  else none

def applyAt (relEnv : Engine.RelationEnv) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (permissions : List OneHoleContext)
    (source : Pattern) (contextIndex ruleIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source) : Outcome :=
  let localResult := ConditionalEquationExecution.applyRuleAtOutcome relEnv language free
    site.focusBound site.focusType rule site.focus
  { receipts := localResult.receipts.filterMap
      (fillReceipt? language free bound expected contextIndex ruleIndex
        site.context site.focusBound site.focusType)
    pending := localResult.pending.map fun reason =>
      ⟨contextIndex, site.context, ruleIndex, reason⟩ }

/-- Enumerate actual authored rule positions at every supplied licensed site. -/
def executeSites (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (sites : List (Site language free bound expected permissions source)) : Outcome :=
  let results := sites.zipIdx.flatMap fun (site, contextIndex) =>
    language.rewrites.zipIdx.map fun (rule, ruleIndex) =>
      applyAt relEnv language free bound expected permissions source
        contextIndex ruleIndex rule site
  { receipts := results.flatMap Outcome.receipts
    pending := results.flatMap Outcome.pending }

theorem fillReceipt?_readout (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (contextIndex ruleIndex : Nat)
    (context : OneHoleContext) (focusBound : List TypeExpr) (focusType : TypeExpr)
    (atomic : ConditionalEquationExecution.Receipt) (receipt : Receipt)
    (finished : fillReceipt? language free bound expected contextIndex ruleIndex
      context focusBound focusType atomic = some receipt) :
    receipt.contextIndex = contextIndex ∧ receipt.context = context ∧
      receipt.focusBound = focusBound ∧ receipt.focusType = focusType ∧
      receipt.ruleIndex = ruleIndex ∧ receipt.atomic = atomic ∧
      receipt.target = context.fill atomic.target ∧
      receipt.target.isWellScopedAt bound.length = true ∧
      HasType language free bound receipt.target expected := by
  unfold fillReceipt? at finished
  dsimp only at finished
  split at finished
  · rename_i accepted
    cases Option.some.inj finished
    simp only [Bool.and_eq_true] at accepted
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, accepted.1,
      checkHasType_sound accepted.2⟩
  · contradiction

/-- A returned contextual firing retains its exact atomic occurrence and
reconstructs the target by the same zipper that selected its source. -/
theorem applyAt_readout (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (contextIndex ruleIndex : Nat) (rule : RewriteRule)
    (site : Site language free bound expected permissions source) (receipt : Receipt)
    (present : receipt ∈ (applyAt relEnv language free bound expected permissions source
      contextIndex ruleIndex rule site).receipts) :
    ∃ atomic ∈ (ConditionalEquationExecution.applyRuleAtOutcome relEnv language free
      site.focusBound site.focusType rule site.focus).receipts,
      receipt.contextIndex = contextIndex ∧ receipt.context = site.context ∧
        receipt.focusBound = site.focusBound ∧ receipt.focusType = site.focusType ∧
        receipt.ruleIndex = ruleIndex ∧ receipt.atomic = atomic ∧
        receipt.target = site.context.fill atomic.target ∧
        receipt.target.isWellScopedAt bound.length = true ∧
        HasType language free bound receipt.target expected := by
  obtain ⟨atomic, member, finished⟩ := List.mem_filterMap.mp present
  exact ⟨atomic, member, fillReceipt?_readout language free bound expected
    contextIndex ruleIndex site.context site.focusBound site.focusType atomic receipt finished⟩

theorem executeSites_readout (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (permissions : List OneHoleContext) (source : Pattern)
    (sites : List (Site language free bound expected permissions source)) (receipt : Receipt)
    (present : receipt ∈ (executeSites relEnv language free bound expected permissions
      source sites).receipts) :
    ∃ site contextIndex rule ruleIndex,
      (site, contextIndex) ∈ sites.zipIdx ∧
      (rule, ruleIndex) ∈ language.rewrites.zipIdx ∧
      receipt ∈ (applyAt relEnv language free bound expected permissions source
        contextIndex ruleIndex rule site).receipts := by
  simp only [executeSites, List.mem_flatMap, List.mem_map] at present
  obtain ⟨result, ⟨⟨site, contextIndex⟩, siteMember, ⟨rule, ruleIndex⟩,
    ruleMember, represented⟩, receiptMember⟩ := present
  cases represented
  exact ⟨site, contextIndex, rule, ruleIndex, siteMember, ruleMember, receiptMember⟩

end Mettapedia.OSLF.MeTTaIL.TypedContextualEquationExecution

import Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution
import Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

/-!
# Authored typed conditional equations in the resumable occurrence search

The fixed language and provider snapshot supply the actual scoped matcher,
ordered query interpreter and typing gates. Every authored equation position
is tried in both orientations; every authored directed rule position is kept
separate. Their pending obligations enter the search state unchanged.

This root provider can be composed with licensed contextual providers. Its
exhaustiveness is earned on admitted presentations, not inferred from empty
runtime lists. The queue explores equation representatives, while primitive
receipts retain distinct authored declaration and query occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSearch

open Syntax Engine
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open ScopedEquationExecution (Orientation)
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier (Batch Model)

structure RuleOrigin extends ConditionalEquationExecution.Receipt where
  ruleIndex : Nat
  deriving DecidableEq, Repr

inductive Obligation where
  | equation (equationIndex : Nat) (orientation : Orientation)
      (reason : ConditionalEquationExecution.Pending)
  | rule (ruleIndex : Nat) (reason : ConditionalEquationExecution.Pending)
  deriving DecidableEq, Repr

def orientations : List Orientation := [.forward, .reverse]

def equationCases (language : LanguageDef) : List (Equation × Nat × Orientation) :=
  language.equations.zipIdx.flatMap fun (equation, index) =>
    orientations.map fun orientation => (equation, index, orientation)

theorem equationCases_spec (language : LanguageDef) (equation : Equation)
    (index : Nat) (orientation : Orientation) :
    (equation, index, orientation) ∈ equationCases language ↔
      (equation, index) ∈ language.equations.zipIdx := by
  cases orientation <;>
    simp [equationCases, orientations, List.mem_flatMap, Prod.mk.injEq]

def equationBatch (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : Batch (ConditionalEquationExecution.EquationReceipt × Pattern) Obligation :=
  let cases := equationCases language
  { answers := cases.flatMap fun (equation, index, orientation) =>
      (ConditionalEquationExecution.applyAt relEnv language free bound expected
        index equation orientation source).receipts.map fun receipt => (receipt, receipt.target)
    unresolved := cases.flatMap fun (equation, index, orientation) =>
      (ConditionalEquationExecution.applyAt relEnv language free bound expected
        index equation orientation source).pending.map (.equation index orientation) }

def firingBatch (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) : Batch (RuleOrigin × Pattern) Obligation :=
  { answers := language.rewrites.zipIdx.flatMap fun (rule, index) =>
      (ConditionalEquationExecution.applyRuleAtOutcome relEnv language free bound expected
        rule source).receipts.map fun receipt =>
          (⟨receipt, index⟩, receipt.target)
    unresolved := language.rewrites.zipIdx.flatMap fun (rule, index) =>
      (ConditionalEquationExecution.applyRuleAtOutcome relEnv language free bound expected
        rule source).pending.map (.rule index) }

def model (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr) :
    Model Pattern ConditionalEquationExecution.EquationReceipt RuleOrigin Obligation where
  equations := equationBatch relEnv language free bound expected
  firings := firingBatch relEnv language free bound expected

theorem equationBatch_readout (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) (receipt : ConditionalEquationExecution.EquationReceipt)
    (present : (receipt, target) ∈ (equationBatch relEnv language free bound expected source).answers) :
    ∃ equation index orientation,
      (equation, index) ∈ language.equations.zipIdx ∧
      receipt ∈ (ConditionalEquationExecution.applyAt relEnv language free bound expected
        index equation orientation source).receipts ∧ target = receipt.target := by
  simp only [equationBatch, List.mem_flatMap, List.mem_map] at present
  obtain ⟨⟨equation, index, orientation⟩, declared, actual, actualMember, same⟩ := present
  cases same
  exact ⟨equation, index, orientation,
    (equationCases_spec language equation index orientation).mp declared, actualMember, rfl⟩

theorem firingBatch_readout (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source target : Pattern) (origin : RuleOrigin)
    (present : (origin, target) ∈ (firingBatch relEnv language free bound expected source).answers) :
    ∃ rule index receipt,
      (rule, index) ∈ language.rewrites.zipIdx ∧
      receipt ∈ (ConditionalEquationExecution.applyRuleAtOutcome relEnv language free bound expected
        rule source).receipts ∧ origin.toReceipt = receipt ∧
          origin.ruleIndex = index ∧ target = receipt.target := by
  simp only [firingBatch, List.mem_flatMap, List.mem_map] at present
  obtain ⟨⟨rule, index⟩, declared, receipt, receiptMember, same⟩ := present
  cases same
  exact ⟨rule, index, receipt, declared, receiptMember, rfl, rfl, rfl⟩

/-- Unsupported equation premises retain their declaration and orientation. -/
theorem equationPending_retained (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (equation : Equation) (index : Nat) (orientation : Orientation)
    (reason : ConditionalEquationExecution.Pending)
    (declared : (equation, index) ∈ language.equations.zipIdx)
    (unfinished : reason ∈ (ConditionalEquationExecution.applyAt relEnv language free bound expected
      index equation orientation source).pending) :
    Obligation.equation index orientation reason ∈
      (equationBatch relEnv language free bound expected source).unresolved := by
  apply List.mem_flatMap.mpr
  exact ⟨(equation, index, orientation),
    (equationCases_spec language equation index orientation).mpr declared,
    List.mem_map.mpr ⟨reason, unfinished, rfl⟩⟩

theorem rulePending_retained (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (rule : RewriteRule) (index : Nat)
    (reason : ConditionalEquationExecution.Pending)
    (declared : (rule, index) ∈ language.rewrites.zipIdx)
    (unfinished : reason ∈ (ConditionalEquationExecution.applyRuleAtOutcome relEnv language free
      bound expected rule source).pending) :
    Obligation.rule index reason ∈ (firingBatch relEnv language free bound expected source).unresolved := by
  exact List.mem_flatMap.mpr ⟨(rule, index), declared, List.mem_map.mpr ⟨reason, unfinished, rfl⟩⟩

end Mettapedia.OSLF.MeTTaIL.AuthoredEquationOccurrenceSearch

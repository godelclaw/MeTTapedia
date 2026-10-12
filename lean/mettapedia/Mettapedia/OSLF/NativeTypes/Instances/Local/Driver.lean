import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Instances.Local.Backend
import Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated

open Mettapedia.OSLF.Framework

/-!
# Generating a native decision driver from an authored local profile

The admission function inspects the actual compiled language and provider.
Every admitted equation-free profile uses the same occurrence jobs, source
decoder, generated structural predicates and public checker. Finite quotient
and proper-child recursive adapters can supply their separately proved
coverage without weakening these local admission checks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Local.Driver

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Runtime.Description

structure Leaf (generated : Generated) (expected : TypeExpr) where
  index : Fin generated.snapshot.language.terms.length
  carrier : .base (structuralDeclaration generated index).category = expected
  accepts : Fin (structuralDeclaration generated index).params.length → Pattern → Bool

def leaves (generated : Generated) (expected : TypeExpr) : List (Leaf generated expected) :=
  (List.finRange generated.snapshot.language.terms.length).filterMap fun index =>
    if carrier : .base (structuralDeclaration generated index).category = expected then
      some ⟨index, carrier, fun _ _ => true⟩
    else none

def lookup (generated : Generated) (expected : TypeExpr) (label : String) :
    Option (Leaf generated expected) :=
  (leaves generated expected).find? fun leaf => (structuralDeclaration generated leaf.index).label == label

def tests (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (equationFree : generated.plan.equations = [])
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (leaf : Leaf generated expected) :
    Test (GeneralOccurrenceSemantics.gslt generated.plan bound expected)
      (Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan bound expected) :=
  let actual := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localTest generated equationFree mask
    bound leaf.index leaf.accepts
  {predicate := ⟨actual.predicate.val, by
      intro source other related
      apply actual.predicate.property
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
        (.base (structuralDeclaration generated leaf.index).category)) source other
      rw [leaf.carrier]
      exact related⟩
   evaluate := actual.evaluate
   positive := actual.positive
   negative := actual.negative
   completionBudget := actual.completionBudget
   complete_at source typed := actual.complete_at source typed.2.2.1
   complete_above source typed budget enough := actual.complete_above source typed.2.2.1 budget enough}

theorem native_structural_meaning (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (equationFree : generated.plan.equations = [])
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (leaf : Leaf generated expected) (source : Pattern) :
    (tests generated bound expected equationFree mask leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel generated mask bound)
        leaf.index (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs
          generated bound leaf.index leaf.accepts)).meaning source :=
  Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test_generated_comparison
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel_equations equationFree mask)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localBackend generated bound equationFree) leaf.index _
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs_interpreted equationFree bound leaf.index leaf.accepts)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanEffective generated mask bound leaf.index leaf.accepts) source

def decode (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) (raw : Pattern) :
    Except SourceIssue {source : Pattern //
      Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan bound expected source ∧ source = raw} :=
  if checked : checkOpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound expected raw = true then
    .ok ⟨raw, checkOpenPatternWellSorted_sound checked, rfl⟩
  else .error .illScopedOrSorted

theorem decode_complete (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr) (raw : Pattern)
    (admitted : ∃ source, Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan bound expected source ∧ source = raw) :
    (decode generated bound expected raw).isOk = true := by
  obtain ⟨source, typed, rfl⟩ := admitted
  have checked : checkOpenPatternWellSorted generated.snapshot.language generated.snapshot.free bound expected source = true :=
    checkOpenPatternWellSorted_complete typed
  simp only [decode, checked, dite_true]
  rfl

def driver (generated : Generated) (bound : List TypeExpr) (expected : TypeExpr)
    (foundation : generated.plan.complete = true) (equationFree : generated.plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric generated.plan = true)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) : Driver where
  generated := generated
  expected := expected
  system := GeneralOccurrenceSemantics.gslt generated.plan bound expected
  admitted := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan bound expected
  render := id
  render_injective := Function.injective_id
  decode := decode generated bound expected
  decode_complete := decode_complete generated bound expected
  backend := Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.backend generated.plan bound expected rfl foundation equationFree generic
  Leaf := Leaf generated expected
  tests := tests generated bound expected equationFree mask
  leafAdmission := rootAdmission generated expected (fun leaf : Leaf generated expected => leaf.index.val)
  lookup := lookup generated expected

inductive GenerationIssue where
  | operationalObligations (issues : List GeneralExecutionAdmission.Obligation)
  | equationCoverageRequired
  | premiseCoverageRequired
  deriving DecidableEq, Repr

/-- This admission function is uniform in the authored presentation. No
language name or prepared example selects a different local algorithm. -/
def generate (snapshot : Snapshot) (language : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (bound : List TypeExpr) (expected : TypeExpr)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool) : Except GenerationIssue Driver :=
  let output := Mettapedia.OSLF.NativeTypes.Generation.generate snapshot language logic vertex
  if foundation : output.plan.complete = true then
    if equationFree : output.plan.equations = [] then
      if generic : GeneralExecutionTotalAdmission.checkGeneric output.plan = true then
        .ok (driver output bound expected foundation equationFree generic mask)
      else .error .premiseCoverageRequired
    else .error .equationCoverageRequired
  else .error (.operationalObligations output.plan.obligations)

theorem generate_complete (snapshot : Snapshot) (language : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (bound : List TypeExpr) (expected : TypeExpr)
    (mask : List TypeExpr → TypeExpr → ModalHypercube.HSort → Pattern → Bool)
    (foundation : (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot language logic vertex).plan.complete = true)
    (equationFree : (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot language logic vertex).plan.equations = [])
    (generic : GeneralExecutionTotalAdmission.checkGeneric
      (Mettapedia.OSLF.NativeTypes.Generation.generate snapshot language logic vertex).plan = true) :
    (generate snapshot language logic vertex bound expected mask).isOk = true := by
  simp only [generate, foundation, equationFree, generic, dite_true]
  rfl

end Mettapedia.OSLF.NativeTypes.Instances.Local.Driver

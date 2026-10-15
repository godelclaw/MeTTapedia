import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated

open Mettapedia.OSLF.Framework

/-!
# The original partial-recursive machine through the public native interface

The presentation retains all original rules and constructors. Generated
constructor types, connective selection and sort profiles feed the same
certificate-based public checker used for scoped lambda programs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Runtime.Description

structure Configuration where
  logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment := Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
  vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.chosen.language :=
    (fun _ => .star, fun _ => .star)

def generated (configuration : Configuration) : Mettapedia.OSLF.NativeTypes.Generation.Generated :=
  Mettapedia.OSLF.NativeTypes.Generation.generate Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment configuration.logic configuration.vertex

theorem original_snapshot (configuration : Configuration) :
    (generated configuration).snapshot = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot _ Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment = _
  simp only [Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment,
    Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]

theorem original_plan (configuration : Configuration) :
    (generated configuration).plan = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan := by
  unfold Mettapedia.OSLF.NativeTypes.Generation.Generated.plan
  rw [original_snapshot]
  rfl

theorem no_equations (configuration : Configuration) :
    (generated configuration).plan.equations = [] := by
  rw [original_plan]
  exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_equations

theorem admitted_cube (configuration : Configuration) :
    (generated configuration).equationAdmission = some true := rfl

def syntaxMask (_bound : List TypeExpr) (_carrier : TypeExpr)
    (sort : ModalHypercube.HSort) (source : Pattern) : Bool :=
  decide (sort = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.syntaxSort source)

abbrev Leaf := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.CfgFormer

def tests (configuration : Configuration) (bound : List TypeExpr) (leaf : Leaf) :
    Test (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory bound) (Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound) :=
  let actual := Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localTest (generated configuration)
    (no_equations configuration) syntaxMask bound leaf.val (fun _ _ => true)
  {predicate := ⟨actual.predicate.val, by
      intro source other related
      apply actual.predicate.property
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation (generated configuration).plan bound
        (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration (generated configuration) leaf.val).category)) source other
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan bound
        (.base "Cfg")) source other at related
      rw [original_plan]
      change Relation.EqvGen (GeneralOccurrenceSemantics.Equation Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan bound
        (.base (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated
          leaf.val).category)) source other
      rw [leaf.property]
      exact related⟩
   evaluate := actual.evaluate
   positive := actual.positive
   negative := actual.negative
   completionBudget := actual.completionBudget
   complete_at source typed := actual.complete_at source typed.2.2.1
   complete_above source typed budget enough := actual.complete_above source typed.2.2.1 budget enough}

theorem native_structural_meaning (configuration : Configuration) (bound : List TypeExpr)
    (leaf : Leaf) (source : Pattern) :
    (tests configuration bound leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Semantics.Sorted.NativeCodes.structuralCode
        (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel (generated configuration) syntaxMask bound)
        leaf.val (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs
          (generated configuration) bound leaf.val (fun _ _ => true))).meaning source :=
  Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.test_generated_comparison
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanModel_equations (no_equations configuration) syntaxMask)
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.localBackend (generated configuration) bound
      (no_equations configuration)) leaf.val _
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanInputs_interpreted (no_equations configuration)
      bound leaf.val (fun _ _ => true))
    (Mettapedia.OSLF.NativeTypes.Decision.Structural.Generated.booleanEffective (generated configuration) syntaxMask
      bound leaf.val (fun _ _ => true)) source

def decode (bound : List TypeExpr) (raw : Pattern) : Except SourceIssue
    {source : Pattern // Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound source ∧ source = raw} :=
  if checked : checkOpenPatternWellSorted Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan.snapshot.language
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan.snapshot.free bound (.base "Cfg") raw = true then
    .ok ⟨raw, checkOpenPatternWellSorted_sound checked, rfl⟩
  else .error .illScopedOrSorted

theorem decode_complete (bound : List TypeExpr) (raw : Pattern)
    (admitted : ∃ source, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound source ∧ source = raw) :
    (decode bound raw).isOk = true := by
  obtain ⟨source, typed, rfl⟩ := admitted
  simp only [decode, checkOpenPatternWellSorted_complete typed, dite_true]
  rfl

def driver (configuration : Configuration) (bound : List TypeExpr) : Driver where
  generated := generated configuration
  expected := .base "Cfg"
  system := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.theory bound
  admitted := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound
  render := id
  render_injective := Function.injective_id
  decode := decode bound
  decode_complete := decode_complete bound
  backend := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend bound
  Leaf := Leaf
  tests := tests configuration bound
  leafAdmission := rootAdmission (generated configuration) (.base "Cfg") (fun leaf : Leaf => leaf.val.val)
  lookup := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.former?

theorem driver_original_language (configuration : Configuration) (bound : List TypeExpr) :
    (driver configuration bound).generated.snapshot.language =
      Mettapedia.Languages.PartrecMachine.partrecMachine :=
  congrArg Snapshot.language (original_snapshot configuration)

theorem complete (configuration : Configuration) (bound : List TypeExpr)
    (formula : (driver configuration bound).Formula) (raw : Pattern)
    (admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source bound raw)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed configuration.logic
      (driver configuration bound).leafAdmission formula) (budget : Nat)
    (enough : workBound (driver configuration bound).backend (driver configuration bound).tests formula raw ≤ budget) :
    ∃ answer, (search (driver configuration bound) formula raw budget).readout = .judgment (.decided answer) := by
  apply search_complete
  · exact ⟨raw, admitted, rfl⟩
  · exact formed
  · exact admitted_cube configuration
  · intro source
    have same : source.val = raw := source.property.2
    rw [same]
    exact enough

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.Driver

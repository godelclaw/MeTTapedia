import Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource
import Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural
import Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled

open Mettapedia.OSLF.Framework

/-!
# The original rho presentation through the public native interface

The generated constructor catalogue supplies the leaves and their ordered
input carriers. Their native meanings use the independently proved original
rho quotient. COMM, ParCong and reflective substitution use the scheduled
original operational backend. The displayed profile contract remains distinct
from the retained older uniform equation-formation diagnostic.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.OSLF.NativeTypes.Generation (structuralDeclaration)
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource

abbrev Configuration := Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.Configuration

def generated (configuration : Configuration) := (output configuration).generated

structure Leaf where
  index : Fin chosen.language.terms.length
  carrier : (chosen.language.terms[index]).category = "Proc"
  inputs : Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking.Inputs chosen.language.terms[index]

def tests (_configuration : Configuration) (leaf : Leaf) :
    Test rhoReflectiveGSLT Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking.test FreeTypeContext.empty []
    chosen.language.terms[leaf.index] (List.getElem_mem leaf.index.isLt) leaf.inputs

def formers : List Leaf :=
  (List.finRange chosen.language.terms.length).filterMap fun index =>
    if category : chosen.language.terms[index].category = "Proc" then
      some ⟨index, category, fun _ => {
        meaning := fun _ => True
        invariant := fun _ => Iff.rfl
        accepts := fun _ => true
        exact := fun _ => ⟨fun _ => trivial, fun _ => rfl⟩}⟩
    else none

def former? (label : String) : Option Leaf :=
  formers.find? fun leaf => chosen.language.terms[leaf.index].label == label

theorem source_typed (source : rhoReflectiveGSLT.Term) :
    HasType rhoCalc FreeTypeContext.empty [] source.1 (.base "Proc") ∧
      isObjectPattern source.1 = true := by
  have accepted := Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted source
  change Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit source.1 = true at accepted
  have checked := checkOpenPatternWellSorted_sound (Bool.and_eq_true_iff.mp accepted).1
  exact ⟨checked.1, checked.2.2.1⟩

theorem native_structural_meaning (configuration : Configuration)
    (leaf : Leaf) (source : rhoReflectiveGSLT.Term) :
    (tests configuration leaf).predicate source ↔
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural.nativeCode (generated configuration) []
        leaf.index leaf.inputs).meaning source.1 := by
  have typed : HasType (generated configuration).snapshot.language
      (generated configuration).snapshot.free [] source.1
      (.base (structuralDeclaration (generated configuration) leaf.index).category) := by
    change HasType rhoCalc FreeTypeContext.empty [] source.1
      (.base chosen.language.terms[leaf.index].category)
    rw [leaf.carrier]
    exact (source_typed source).1
  have comparison := Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural.native_image_exact
    (generated := generated configuration) (bound := [])
    (original_language configuration)
    (Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural.objectModel (generated configuration) [])
    leaf.index (Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural.nativeInputCodes
      (generated configuration) [] leaf.index leaf.inputs) leaf.inputs
    (Mettapedia.OSLF.NativeTypes.Instances.Rho.GeneratedStructural.native_input_codes_exact
      (generated := generated configuration) (bound := []) leaf.index leaf.inputs) source.1
  constructor
  · intro holds
    exact comparison.mpr ⟨⟨typed, (source_typed source).2⟩, (source_typed source).2, holds⟩
  · intro holds
    exact (comparison.mp holds).2.2

def driver (configuration : Configuration) : Driver where
  generated := generated configuration
  profile := .displayed configuration.vertex [] rfl
  expected := .base "Proc"
  system := rhoReflectiveGSLT
  admitted := Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted
  render := Subtype.val
  render_injective := Subtype.val_injective
  decode := Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.decode
  decode_complete := Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.decode_complete
  backend := Mettapedia.OSLF.NativeTypes.Instances.Rho.Scheduled.backend
  Leaf := Leaf
  tests := tests configuration
  leafAdmission := rootAdmission (generated configuration) (.base "Proc")
    (fun leaf : Leaf => leaf.index.val)
  lookup := former?

theorem driver_original_language (configuration : Configuration) :
    (driver configuration).generated.snapshot.language = rhoCalc :=
  original_language configuration

theorem profile_exact (configuration : Configuration) :
    (driver configuration).profileAdmission = (output configuration).profileAdmission := rfl

theorem default_admitted : (driver {}).profileAdmission = some true := default_profile_admitted

theorem complete (configuration : Configuration) (formula : (driver configuration).Formula)
    (raw : Pattern) (sourceAdmitted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true)
    (formed : Mettapedia.OSLF.NativeTypes.Decision.Admission.Formed configuration.logic
      (driver configuration).leafAdmission formula)
    (profile : (output configuration).profileAdmission = some true) (budget : Nat)
    (enough : ∀ source : (driver configuration).Decoded raw,
      workBound (driver configuration).backend (driver configuration).tests formula source.val ≤ budget) :
    ∃ answer, (search (driver configuration) formula raw budget).readout = .judgment (.decided answer) := by
  apply search_complete
  · let source := presentedRhoProcessEquiv.symm
      (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess raw sourceAdmitted)
    exact ⟨source, Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted source, rfl⟩
  · exact formed
  · exact profile
  · exact enough

end Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver

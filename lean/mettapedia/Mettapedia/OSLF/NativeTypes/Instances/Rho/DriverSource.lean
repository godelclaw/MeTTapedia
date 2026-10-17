import Mettapedia.OSLF.NativeTypes.Runtime.Description
import Mettapedia.OSLF.NativeTypes.Generation.Displayed
import Mettapedia.OSLF.NativeTypes.Instances.Rho.DisplayedProfiles
import Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend

open Mettapedia.OSLF.Framework

/-!
# Original rho source and generated displayed interface

COMM, ParCong, QuoteDrop and the authored parallel algebra remain in the
original presentation. The canonical operational adapter earns their joint
meaning independently of the generic bounded equation enumerator. The full
displayed profile is retained beside the older failed formation diagnostic.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefSemanticAgreement
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.NativeTypes.Runtime.Description

def snapshot : Snapshot := ⟨rhoCalc, [], ⟨[], [], []⟩⟩
def fragment : Mettapedia.OSLF.NativeTypes.Generation.LanguageFragment :=
  {operational := {sites := .rootOnly, reflection := rhoReflectionProfile}}

def chosen : Snapshot := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment

structure Configuration where
  logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment := Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
  vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.Vertex chosen.language :=
    Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.allStar chosen.language

def output (configuration : Configuration) : Mettapedia.OSLF.NativeTypes.Generation.Displayed.Output :=
  Mettapedia.OSLF.NativeTypes.Generation.Displayed.generate snapshot fragment configuration.logic configuration.vertex []

theorem original_snapshot (configuration : Configuration) :
    (output configuration).generated.snapshot = snapshot := by
  change Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot fragment = snapshot
  simp only [Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot, fragment, Mettapedia.OSLF.NativeTypes.Generation.unrestricted_signature]

theorem original_language (configuration : Configuration) :
    (output configuration).generated.snapshot.language = rhoCalc :=
  congrArg Snapshot.language (original_snapshot configuration)

theorem profile_admission_exact (configuration : Configuration) :
    (output configuration).profileAdmission = some true ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.Consistent chosen.language [] configuration.vertex := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.admit? chosen.language [] configuration.vertex = some true ↔ _
  rw [Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.admission_exact]
  have known : Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.carriersKnown chosen.language = true :=
    Mettapedia.OSLF.NativeTypes.Instances.Rho.DisplayedProfiles.original_carriers_known
  exact ⟨fun accepted => accepted.2, fun consistent => ⟨known, consistent⟩⟩

theorem default_profile_admitted : (output {}).profileAdmission = some true :=
  Mettapedia.OSLF.NativeTypes.Instances.Rho.DisplayedProfiles.original_allStar_admitted

theorem original_quoteDrop_retained (configuration : Configuration) :
    (output configuration).generated.snapshot.language.equations = rhoCalc.equations :=
  congrArg LanguageDef.equations (original_language configuration)

def decode (raw : Pattern) : Except SourceIssue
    {source : rhoReflectiveGSLT.Term // Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted source ∧ source.1 = raw} :=
  if accepted : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true then
    let source := presentedRhoProcessEquiv.symm (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admittedProcess raw accepted)
    .ok ⟨source, Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.every_carrier_admitted source, rfl⟩
  else .error .illScopedOrSorted

theorem decode_complete (raw : Pattern)
    (admitted : ∃ source : rhoReflectiveGSLT.Term,
      Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted source ∧ source.1 = raw) :
    (decode raw).isOk = true := by
  obtain ⟨source, accepted, same⟩ := admitted
  have checked : Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit raw = true := same ▸ accepted
  simp only [decode, checked, dite_true]
  rfl

theorem decoded_source_exact {raw : Pattern}
    (source : {source : rhoReflectiveGSLT.Term //
      Mettapedia.OSLF.NativeTypes.Instances.Rho.DecisionBackend.admitted source ∧ source.1 = raw}) : source.val.1 = raw :=
  source.property.2

end Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource

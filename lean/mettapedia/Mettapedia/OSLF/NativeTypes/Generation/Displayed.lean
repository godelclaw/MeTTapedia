import Mettapedia.OSLF.NativeTypes.Generation.Core
import Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph
import Mettapedia.OSLF.NativeTypes.Decision.ProfileAdmission

open Mettapedia.OSLF.Framework

/-!
# Generated catalogues at a displayed modal profile

The finite displayed-profile contract includes index, rely and target slots.
Its catalogue uses the same authored schema and constructor generators as the
original generated type-system implementation. The older uniform equation-formation
diagnostic is retained separately and unchanged; it is not a theorem about
this weaker, explicitly finite profile contract.

Program equations continue to belong to the operational plan. Additional
typed-occurrence matching is explicit input. Bare program-variable names do
not silently acquire generated type-metavariable identities.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Displayed

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation (Generated LanguageFragment)
open Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph

structure Output where
  generated : Generated
  fullVertex : Vertex generated.snapshot.language
  matching : List (EquationMatching generated.snapshot.language)
  profileAdmission : Option Bool
  originalEquationDiagnostic : Option Bool

def generate (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)) : Output :=
  let chosen := Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language
  let original := Mettapedia.OSLF.NativeTypes.Generation.generate snapshot language logic (project chosen.language vertex)
  let status := admit? chosen.language matching vertex
  let accepted := status != some false
  let corrected : Generated :=
    {original with
      modalCatalogue := if accepted && logic.core.modal then
        Mettapedia.OSLF.NativeTypes.Generation.schemas (compile chosen language.operational) else []
      structuralCatalogue := if accepted && logic.core.structural then
        Mettapedia.OSLF.NativeTypes.Structural.structuralFormers chosen.language else []}
  {generated := corrected, fullVertex := vertex, matching := matching,
    profileAdmission := status, originalEquationDiagnostic := original.equationAdmission}

theorem source_preserved (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)) :
    (generate snapshot language logic vertex matching).generated.snapshot =
      Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language := rfl

theorem operational_plan_preserved (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)) :
    (generate snapshot language logic vertex matching).generated.plan =
      compile (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language) language.operational := rfl

theorem old_diagnostic_preserved (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)) :
    (generate snapshot language logic vertex matching).generated.equationAdmission =
      (generate snapshot language logic vertex matching).originalEquationDiagnostic := rfl

theorem admission_exact (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)) :
    (generate snapshot language logic vertex matching).profileAdmission = some true ↔
      carriersKnown (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language = true ∧
        Consistent (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language matching vertex :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph.admission_exact _ matching vertex

theorem structural_catalogue_exact (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language))
    (accepted : (generate snapshot language logic vertex matching).profileAdmission = some true)
    (enabled : logic.core.structural = true) :
    (generate snapshot language logic vertex matching).generated.structuralCatalogue =
      Mettapedia.OSLF.NativeTypes.Structural.structuralFormers
        (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language := by
  change (if _ != some false && logic.core.structural then _ else []) = _
  change admit? (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language matching vertex = some true at accepted
  rw [accepted, enabled]
  rfl

theorem modal_catalogue_exact (snapshot : Snapshot) (language : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Vertex (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language)
    (matching : List (EquationMatching (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language))
    (accepted : (generate snapshot language logic vertex matching).profileAdmission = some true)
    (enabled : logic.core.modal = true) :
    (generate snapshot language logic vertex matching).generated.modalCatalogue =
      Mettapedia.OSLF.NativeTypes.Generation.schemas
        (compile (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language) language.operational) := by
  change (if _ != some false && logic.core.modal then _ else []) = _
  change admit? (Mettapedia.OSLF.NativeTypes.Generation.selectedSnapshot snapshot language).language matching vertex = some true at accepted
  rw [accepted, enabled]
  rfl

end Mettapedia.OSLF.NativeTypes.Generation.Displayed

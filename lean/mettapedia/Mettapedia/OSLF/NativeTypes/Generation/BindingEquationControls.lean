import Mettapedia.OSLF.NativeTypes.Generation.BindingCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingControls

/-!
# Authored binding-equation stream controls

The generator checks the original dependency-function equation at every
vertex. Its negative control retains the authored binding metadata but
changes the equation to the false assertion that every body is identity.
These finite binding-model controls are separate from operational execution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingEquationControls

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingControls

def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩

def fragment : LanguageFragment :=
  {operational := {includeDerivedEquations := false}}

def chosen := selectedSnapshot snapshot fragment

def generated (vertex : SortProfiles.Derived.CubeVertex chosen.language) : Generated :=
  generate snapshot fragment Structural.heytingFragment vertex

theorem original_equation_stream
    (vertex : SortProfiles.Derived.CubeVertex chosen.language) :
    selectedEquationLaws (generated vertex).snapshot.language
      (generated vertex).languageFragment.operational = [law] := by
  rfl

theorem whole_original_equation_stream_checks
    (vertex : SortProfiles.Derived.CubeVertex chosen.language) :
    (generated vertex).literalBindingLawAdmission? = some true := by
  decide +revert +kernel

def falseSnapshot : Snapshot := ⟨falseLanguage, [], ⟨[], []⟩⟩

def falseChosen := selectedSnapshot falseSnapshot fragment

def falseGenerated (vertex : SortProfiles.Derived.CubeVertex falseChosen.language) : Generated :=
  generate falseSnapshot fragment Structural.heytingFragment vertex

theorem false_equation_stream
    (vertex : SortProfiles.Derived.CubeVertex falseChosen.language) :
    selectedEquationLaws (falseGenerated vertex).snapshot.language
      (falseGenerated vertex).languageFragment.operational = [falseLaw] := by
  rfl

theorem incorrect_binder_law_refuted_at_every_vertex
    (vertex : SortProfiles.Derived.CubeVertex falseChosen.language) :
    (falseGenerated vertex).literalBindingLawAdmission? = some false := by
  decide +revert +kernel

end Mettapedia.OSLF.NativeTypes.Generation.BindingEquationControls

import Mettapedia.OSLF.NativeTypes.Generation.Annotated.Checking
import Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls

open Mettapedia.OSLF.Framework

/-!
# Native modal formation at arbitrary source-arrow types

Every checked instance of the actual abstraction template obtains the native
sort coordinates of its authored origin. Its continuation is the genuine
sorted-program code. This constructs the modal code before requiring any
modal inhabitant; no finite carrier catalogue membership is used.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowFormation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls (generated annotation fragment vertex)
open Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls (snapshot language source rule)

theorem equation_admitted : generated.equationAdmission = some true := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.compileLaws Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.chosen.language
      (selectedEquationLaws Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.chosen.language
        Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.permissions))
    vertex.2 = some true
  have empty : Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.chosen.language.equations = [] := by
    rw [Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.chosen_snapshot]
    rfl
  have noLaws : selectedEquationLaws Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.chosen.language
      Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.permissions = [] := by
    simp [selectedEquationLaws, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws, empty]
  rw [noLaws]
  rfl

theorem root_rely_empty (domain : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    checked.schema.relyNames = [] := by
  have retained := instantiated_schema_input_retained produced
  have actualAt := checked.source.present
  rw [retained.1, Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.root_template] at actualAt
  have same := Option.some.inj actualAt.symm
  unfold Schema.relyNames
  change RedexPosition.relyVars checked.schema.declaration.authored.left checked.schema.position = []
  rw [checked.original_authored]
  change RedexPosition.relyVars checked.source.site.rule.left checked.source.site.position = []
  rw [same]
  rfl

def parameters (checked : AnnotatedSchema generated) : ModalParameters checked.schema :=
  (generated.modalParameters? checked.schema).get (by
    exact Option.isSome_iff_exists.mpr
      (generated_annotated_parameters_complete snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex checked))

theorem parameters_computed (checked : AnnotatedSchema generated) :
    generated.modalParameters? checked.schema = some (parameters checked) :=
  (Option.some_get _).symm

def continuationCode (checked : AnnotatedSchema generated) (_assignment : ScopedRuleMatching.Assignment) :
    TypeCode generated.plan checked.schema.bound checked.schema.programCarrier (parameters checked).output where
  meaning result := checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    checked.schema.bound checked.schema.programCarrier result = true
  bounded _ accepted := (checkOpenPatternWellSorted_sound accepted).1

def relyCodes (domain : TypeExpr) (bound : List TypeExpr) (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    RelyCodes checked.schema (parameters checked).inputs := fun name => by
  have member := name.property
  simp only [root_rely_empty domain bound checked produced, List.not_mem_nil] at member

def codes (domain : TypeExpr) (bound : List TypeExpr) (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    ModalInstanceCodes generated checked.schema :=
  ⟨parameters checked, parameters_computed checked,
    relyCodes domain bound checked produced, continuationCode checked⟩

theorem every_arrow_modal_code_formed (domain : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked) :
    ∃ code, generated.annotatedModalFormer? checked (codes domain bound checked produced).actualInputs = some code ∧
      ∃ assignment ∈ generated.sortAssignments,
        assignment.family.origin = .modal checked.schema.declaration.declarationIndex checked.schema.position ∧
        code.1 = assignment.output :=
  generated_annotated_m_form snapshot fragment Mettapedia.OSLF.NativeTypes.Structural.finiteLimitFragment vertex checked
    equation_admitted rfl (codes domain bound checked produced).actualInputs

theorem formed_arrow_carrier (domain : TypeExpr) (bound : List TypeExpr)
    (checked : AnnotatedSchema generated)
    (produced : generated.instantiateAnnotatedSchema? 0 (annotation domain bound) = .ok checked)
    (code : Σ sort : ModalHypercube.HSort,
      TypeCode generated.plan checked.schema.focusBound checked.schema.focusCarrier sort)
    (term : Pattern) (inhabited : code.2.meaning term) :
    HasType generated.snapshot.language generated.snapshot.free bound term
      (.arrow domain Mettapedia.OSLF.NativeTypes.Modal.SourceCarrierControls.carrier) := by
  have shape := Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowControls.every_arrow_schema_readout domain bound checked produced
  have typed := annotated_modal_inhabitant_typed checked inhabited
  rw [shape.2.1, shape.2.2.2] at typed
  exact typed

end Mettapedia.OSLF.NativeTypes.Generation.Annotated.ArrowFormation

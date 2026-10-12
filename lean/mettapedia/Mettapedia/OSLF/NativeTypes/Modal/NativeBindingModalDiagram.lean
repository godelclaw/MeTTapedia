import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingSchemaInputs
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalModel

/-!
# Actual schema diagrams in the shared authored native model

The operational diagram is constructed from independent inputs and complete
scoped receipt frames. Source, specified target, local focus and every
ordered capture land in the original constructor model's actual presheaf
carriers. No semantic map is supplied as a correctness premise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.NativeTypes.Generation
open CurriedBindingLanguage BindingSemanticAdmission IntrinsicScopedConditionalPresheaf
open NativeEventDeclarations NativeBindingSchemaInputs NativeBindingModalAdmission

variable {plan : Plan} {modal : List (NativeModalHeaders.Header plan)}

def programSort {header : NativeModalHeaders.Header plan} (admitted : NativeBindingModalAdmission.Admitted header) :
    String := plan.snapshot.language.types[admitted.programPosition].name

noncomputable def programIso {header : NativeModalHeaders.Header plan}
    (admitted : NativeBindingModalAdmission.Admitted header) :
    meaning header.program ≅ semanticPrograms (algebra plan.snapshot.language) (programSort admitted) :=
  eqToIso (congrArg meaning admitted.program) ≪≫
    programsIso (algebra plan.snapshot.language) (programSort admitted)

def forget (header : NativeModalHeaders.Header plan) (sort : String)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    events header sort freeEmpty ready ⟶ NativeAuthoredEventPresheaf.events
      (GeneralPlanEnvironment.grammar plan) freeEmpty ready sort where
  app _ := TypeCat.ofHom (fun frame => frame.point.val)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro frame
    rfl

noncomputable def source (header : NativeModalHeaders.Header plan)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan)) :
    events header (programSort admitted) freeEmpty ready ⟶ meaning header.program :=
  forget header (programSort admitted) freeEmpty ready ≫
    NativeAuthoredEventPresheaf.source (GeneralPlanEnvironment.grammar plan) freeEmpty ready _ ≫
    (programIso admitted).inv

noncomputable def target (header : NativeModalHeaders.Header plan)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup) :
    events header (programSort admitted) freeEmpty ready ⟶ meaning header.program :=
  forget header (programSort admitted) freeEmpty ready ≫
    NativeAuthoredEventPresheaf.target (GeneralPlanEnvironment.grammar plan) freeEmpty ready languageAdmitted labels _ ≫
    (programIso admitted).inv

def focusInput (header : NativeModalHeaders.Header plan) (sort : String) :
    inputs header sort ⟶ NativeBindingLocalValues.values
      (schema plan header.origin).focusBound (schema plan header.origin).focusCarrier where
  app _ := TypeCat.ofHom Input.focus
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro input
    rfl

def relyInput (header : NativeModalHeaders.Header plan) (sort : String) (index : Fin header.rely.length) :
    inputs header sort ⟶ NativeBindingLocalValues.values
      header.rely[index].slot.dependencies header.rely[index].slot.expected where
  app _ := TypeCat.ofHom (fun input => input.rely index)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro input
    rfl

def matchedInput (header : NativeModalHeaders.Header plan) (sort : String) (index : Fin header.matched.length) :
    inputs header sort ⟶ NativeBindingLocalValues.values
      header.matched[index].slot.dependencies header.matched[index].slot.expected where
  app _ := TypeCat.ofHom (fun input => input.matched index)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro input
    rfl

noncomputable def focus (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup) :
    events header (programSort admitted) freeEmpty ready ⟶ meaning header.focusArgument :=
  observe header decoded _ freeEmpty ready ≫ focusInput header _ ≫
    NativeBindingLocalValues.nativeMap admitted.focus languageAdmitted labels

noncomputable def rely (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup) (index : Fin header.rely.length) :
    events header (programSort admitted) freeEmpty ready ⟶ meaning header.rely[index].carrier :=
  observe header decoded _ freeEmpty ready ≫ relyInput header _ index ≫
    NativeBindingLocalValues.nativeMap (admitted.rely index) languageAdmitted labels

noncomputable def matched (header : NativeModalHeaders.Header plan)
    (decoded : NativeModalHeaders.decode? plan header.origin = some header)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup) (index : Fin header.matched.length) :
    events header (programSort admitted) freeEmpty ready ⟶ meaning header.matched[index].carrier :=
  observe header decoded _ freeEmpty ready ≫ matchedInput header _ index ≫
    NativeBindingLocalValues.nativeMap (admitted.matched index) languageAdmitted labels

noncomputable def diagram
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup)
    (decoded : ∀ index : Fin modal.length, NativeModalHeaders.decode? plan modal[index].origin = some modal[index])
    (admitted : ∀ index : Fin modal.length, NativeBindingModalAdmission.Admitted modal[index]) :
    CurriedNativeModalModel.Diagram plan modal where
  input := fun index => inputs modal[index] (programSort (admitted index))
  events := fun index => events modal[index] (programSort (admitted index)) freeEmpty ready
  observe := fun index => observe modal[index] (decoded index) _ freeEmpty ready
  projection := fun projection => match projection with
    | .source index => source modal[index] (admitted index) freeEmpty ready
    | .target index => target modal[index] (admitted index) freeEmpty ready languageAdmitted labels
    | .focus index => focus modal[index] (decoded index) (admitted index) freeEmpty ready languageAdmitted labels
    | .rely index position => rely modal[index] (decoded index) (admitted index) freeEmpty ready languageAdmitted labels position
    | .matched index position => matched modal[index] (decoded index) (admitted index) freeEmpty ready languageAdmitted labels position

theorem source_read (header : NativeModalHeaders.Header plan)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (X : Base (algebra plan.snapshot.language))
    (frame : (events header (programSort admitted) freeEmpty ready).obj X) :
    (programIso admitted).hom.app X ((source header admitted freeEmpty ready).app X frame) =
      frame.point.val.source := by
  exact ConcreteCategory.congr_hom (congrArg (fun map => map.app X) (programIso admitted).inv_hom_id) _

set_option backward.isDefEq.respectTransparency false in
theorem target_read (header : NativeModalHeaders.Header plan)
    (admitted : NativeBindingModalAdmission.Admitted header)
    (freeEmpty : plan.snapshot.free = FreeTypeContext.empty)
    (ready : NativeOperationalProfile.Admitted (GeneralPlanEnvironment.environment plan))
    (languageAdmitted : BindingSemanticAdmission.Admitted plan.snapshot.language)
    (labels : (plan.snapshot.language.terms.map (·.label)).Nodup)
    (X : Base (algebra plan.snapshot.language))
    (frame : (events header (programSort admitted) freeEmpty ready).obj X) :
    toPattern ((programIso admitted).hom.app X
      ((target header admitted freeEmpty ready languageAdmitted labels).app X frame)) =
      frame.point.val.receipt.target := by
  have same : (programIso admitted).hom.app X ((programIso admitted).inv.app X
      (NativeAuthoredEventAction.targetTerm (GeneralPlanEnvironment.grammar plan) freeEmpty
        languageAdmitted labels frame.point.val)) =
      NativeAuthoredEventAction.targetTerm (GeneralPlanEnvironment.grammar plan) freeEmpty
        languageAdmitted labels frame.point.val := ConcreteCategory.congr_hom (C := Type)
    (congrArg (fun map => map.app X) (programIso admitted).inv_hom_id)
    (NativeAuthoredEventAction.targetTerm (GeneralPlanEnvironment.grammar plan) freeEmpty languageAdmitted labels frame.point.val)
  exact (congrArg toPattern same).trans (NativeAuthoredEventAction.targetTerm_read
    (GeneralPlanEnvironment.grammar plan) freeEmpty languageAdmitted labels frame.point.val)

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingModalDiagram

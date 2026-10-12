import Mettapedia.OSLF.NativeTypes.Generation.AuthoredNativeClassifying
import Mettapedia.OSLF.NativeTypes.Generation.AuthoredBindingNativeModel
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeModalQualification
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeStructuralMeaning
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSourceQualification

/-!
# Independent native meanings for authored cube enrichment

The original binding clone, actual constructor operations, dependent event
families and free cube codes inhabit one concrete presheaf model. The generated
contextual grammar maps to that model through its earned interpretation.
Operational schema instances must construct the event diagram independently.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open _root_.CategoryTheory
open Mettapedia.TypeTheory Mettapedia.TypeTheory.Calculi.NativeDependent
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : AuthoredPipeline.Installed)
variable (diagram : CurriedNativeModalModel.Diagram
  (BindingPipeline.plan installed.operational.generated) installed.operational.modal)

noncomputable abbrev sourceModel :=
  CurriedNativeModalModel.model installed.operational.declarations
    installed.operational.nativeMeaning_admitted diagram

theorem sourceRealization :
    Refinement.SignatureRealization (installed.sourceModel diagram) installed.operational.signature :=
  CurriedNativeModalModel.realization installed.operational.declarations
    installed.operational.nativeMeaning_admitted diagram

noncomputable def semanticModel :=
  CubeNativeSourceExtension.model installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex

theorem semanticRealization :
    Refinement.SignatureRealization (installed.semanticModel diagram) installed.signature :=
  CubeNativeSourceExtension.realization installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex (by decide)

noncomputable def semanticTarget :=
  CubeNativeSourceExtension.qualifiedModel installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex (by decide)

noncomputable def semanticInterpretation :=
  installed.nativeInterpretation (installed.semanticTarget diagram)

theorem source_type_meaning {n : Nat}
    (scope : Refinement.Scope
      (CurriedBindingLanguage.Worlds (BindingPipeline.plan installed.operational.generated).snapshot.language) n)
    (type : Refinement.TypeExpr installed.operational.symbols n) :
    (installed.semanticModel diagram).evaluateType scope
      (Refinement.SignatureSum.typeLeft (Refinement.SignatureSum.typeLeft type)) =
      (installed.sourceModel diagram).evaluateType scope type :=
  CubeNativeSourceExtension.source_type_read installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex scope type

theorem source_term_meaning {n : Nat}
    (scope : Refinement.Scope
      (CurriedBindingLanguage.Worlds (BindingPipeline.plan installed.operational.generated).snapshot.language) n)
    (term : Refinement.TermExpr installed.operational.symbols n) :
    (installed.semanticModel diagram).evaluateTerm scope
      (Refinement.SignatureSum.termLeft (Refinement.SignatureSum.termLeft term)) =
      (installed.sourceModel diagram).evaluateTerm scope term :=
  CubeNativeSourceExtension.source_term_read installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex scope term

theorem interpretation_type_meaning {n : Nat}
    (scope : Refinement.Scope
      (CurriedBindingLanguage.Worlds (BindingPipeline.plan installed.operational.generated).snapshot.language) n)
    (type : Refinement.TypeExpr installed.symbols n) :
    (installed.semanticTarget diagram).data.evaluateType
      (Refinement.NativeAbstractScope.toGeneric scope) type =
      (installed.semanticModel diagram).evaluateType scope type :=
  CubeNativeSourceExtension.qualified_type_read installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex (by decide) scope type

theorem interpretation_term_meaning {n : Nat}
    (scope : Refinement.Scope
      (CurriedBindingLanguage.Worlds (BindingPipeline.plan installed.operational.generated).snapshot.language) n)
    (term : Refinement.TermExpr installed.symbols n) :
    (installed.semanticTarget diagram).data.evaluateTerm
      (Refinement.NativeAbstractScope.toGeneric scope) term =
      (installed.semanticModel diagram).evaluateTerm scope term :=
  CubeNativeSourceExtension.qualified_term_read installed.operational.signature
    (NativeCubeProfile.sourceCarriers installed.operational)
    (installed.sourceModel diagram) (installed.sourceRealization diagram) installed.vertex (by decide) scope term

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

variable (installed : AuthoredPipeline.Installed)

theorem computedMeaningAdmission : AuthoredBindingNativeModel.check installed.operational = true :=
  (AuthoredBindingNativeModel.check_exact installed.operational).mpr
    ⟨(Modal.NativeOperationalProfile.check_exact _).mp installed.operationalMeaning,
      fun index => ⟨installed.modalMeanings index⟩⟩

/-- Successful generation constructs its operational interpretation without
asking the caller to supply a diagram or a native realization theorem. -/
noncomputable def computedDiagram :=
  AuthoredBindingNativeModel.diagram installed.operational installed.freeEmpty
    installed.computedMeaningAdmission

noncomputable def generatedModel := installed.semanticModel installed.computedDiagram

theorem generatedModelRealization : SignatureRealization installed.generatedModel installed.signature :=
  installed.semanticRealization installed.computedDiagram

noncomputable def generatedInterpretation := installed.semanticInterpretation installed.computedDiagram

theorem checked_semantic_sound (certificate : Certificates.Refinement.Certificate installed.signature)
    (judgment : Judgment installed.symbols) (accepted : installed.check certificate judgment = .accepted) :
    Interprets installed.generatedModel judgment := by
  obtain ⟨_, _, derivation, _⟩ := (installed.check_exact certificate judgment).mp accepted
  exact derivation.sound installed.generatedModel installed.generatedModelRealization
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).stableProducts
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).productBeta
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).productEta

theorem searched_semantic_sound (judgment : Judgment installed.symbols) (budget : Nat)
    (tree : Tree (NativeLogic.presentation installed.operational.logic installed.signature))
    (found : (installed.search judgment budget).found = some tree) :
    Interprets installed.generatedModel judgment := by
  obtain ⟨_, _, derivation, _⟩ := installed.sound judgment budget tree found
  exact derivation.sound installed.generatedModel installed.generatedModelRealization
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).stableProducts
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).productBeta
    (Mettapedia.TypeTheory.PresheafNativePredicateModel.qualification _).productEta

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Installed

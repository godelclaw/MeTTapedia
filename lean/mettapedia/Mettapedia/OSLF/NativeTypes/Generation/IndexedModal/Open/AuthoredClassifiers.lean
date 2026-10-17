import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Realization
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Pipeline
import Mettapedia.OSLF.NativeTypes.Generation.CurriedNativeConstructorReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundness

/-!
# Generated classifier meanings from the actual authored binding operations

The complete ordered semantic argument tuple is assembled into the original
constructor telescope. Its original operation supplies the structural
classifier algebra. All open native judgments are then interpreted by the
existing dependent evaluator and its independently earned soundness theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.AuthoredClassifiers

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations Classifier
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open CurriedBindingLanguage

variable {sourceLanguage : MeTTaIL.Syntax.LanguageDef}

noncomputable section

/-- Assemble every ordered argument into the independently constructed
product of the original semantic carriers, including binding functions. -/
def productMap {P : (Worlds sourceLanguage)ᵒᵖ ⥤ Type} :
    (parameters : List (NativeSignature.Carrier sourceLanguage)) →
    (names : ∀ position : Fin parameters.length, P ⟶ meaning parameters[position]) →
      P ⟶ carrierProduct parameters
  | [], _ =>
      {app := fun _ => TypeCat.ofHom (fun _ => PUnit.unit), naturality := by intros; rfl}
  | parameter :: parameters, names =>
      let rest := productMap parameters (fun position => names position.succ)
      { app := fun world => TypeCat.ofHom fun value => ((names 0).app world value, rest.app world value)
        naturality := by
          intro first second arrow
          apply ConcreteCategory.hom_ext
          intro value
          change ((names 0).app second (P.map arrow value), rest.app second (P.map arrow value)) =
            ((meaning parameter).map arrow ((names 0).app first value),
              (carrierProduct parameters).map arrow (rest.app first value))
          exact Prod.ext ((names 0).naturality_apply arrow value) (rest.naturality_apply arrow value) }

variable (installed : Pipeline.Installed)

abbrev language := NativeCubeProfile.language installed.operational
abbrev D := Pipeline.classifierSignature installed.operational
abbrev operational : (D installed).Carrier → (Worlds (language installed))ᵒᵖ ⥤ Type := meaning

def inputName (constructor : (D installed).Former) (position : Fin ((D installed).arity constructor)) :
    StructuralImages.operands (operational installed) constructor ⟶
      meaning ((D installed).input constructor position) where
  app _ := TypeCat.ofHom (fun values => values position)
  naturality _ _ _ := rfl

def constructorScopeMap (constructor : (D installed).Former) :
    StructuralImages.operands (operational installed) constructor ⟶
      (carrierScope (installed.operational.declarations.parameters constructor.val)).1 :=
  productMap (installed.operational.declarations.parameters constructor.val)
    (inputName installed constructor) ≫
    (carrierScopeProductIso (installed.operational.declarations.parameters constructor.val)).inv

def algebra : StructuralImages.Algebra (operational installed) where
  operation constructor :=
    constructorScopeMap installed constructor ≫
      constructorMap installed.operational.nativeMeaning_admitted
        installed.operational.declarations.headers[constructor.val]
        (installed_header_correct installed.operational.declarations constructor.val)

abbrev signature := CubeNativeDeclarations.signature installed.classifierVertex
abbrev symbols := CubeNativeDeclarations.symbols (D installed)

abbrev model := Classifier.Model.model (operational installed) (algebra installed) installed.classifierVertex

theorem realization : SignatureRealization (model installed) (signature installed) :=
  Classifier.Realization.realization (operational installed) (algebra installed) installed.classifierVertex

/-- Every structural predicate reads the authored constructor's actual image,
with every ordered binding argument retained in the original native scope. -/
theorem former_inhabitants {P : (Worlds (language installed))ᵒᵖ ⥤ Type}
    (constructor : (D installed).Former)
    (arguments : ∀ position, P ⟶ Carrier.presheaf (operational installed) ((D installed).input constructor position))
    (world : (Worlds (language installed))ᵒᵖ) (parameter : P.obj world)
    (result : (operational installed ((D installed).output constructor)).obj world) :
    Classifier.Code.Member (.operational result)
      ((StructuralImages.formerName (operational installed) (algebra installed)
        installed.classifierVertex constructor arguments).app world parameter) ↔
      ∃ values : (StructuralImages.operands (operational installed) constructor).obj world,
        (∀ position, Classifier.Code.Member (.operational (values position))
          ((arguments position).app world parameter)) ∧
        (constructorMap installed.operational.nativeMeaning_admitted
          installed.operational.declarations.headers[constructor.val]
          (installed_header_correct installed.operational.declarations constructor.val)).app world
            ((constructorScopeMap installed constructor).app world values) = result :=
  StructuralImages.former_member (operational installed) (algebra installed)
    installed.classifierVertex constructor arguments world parameter result

theorem derivation_sound {judgment : Judgment (symbols installed)}
    (derivation : Derivation (signature installed) judgment) :
    Interprets (model installed) judgment :=
  derivation.native_sound (model installed) (realization installed)

def check (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (symbols installed)) : NativeLogic.CheckResult :=
  NativeLogic.check installed.operational.logic certificate judgment

theorem check_sound (certificate : Certificates.Refinement.Certificate (signature installed))
    (judgment : Judgment (symbols installed))
    (accepted : check installed certificate judgment = .accepted) :
    Interprets (model installed) judgment := by
  obtain ⟨_, _, derivation, _⟩ := (NativeLogic.check_exact installed.operational.logic certificate judgment).mp accepted
  exact derivation_sound installed derivation

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.AuthoredClassifiers

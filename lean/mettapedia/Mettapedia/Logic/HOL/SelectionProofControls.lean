import Mettapedia.Logic.HOL.SelectionProofs
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.Soundness

/-!
# Selection requires both a witness and the selection principle

The identity specification on propositions is inhabited. The standard
constructed choice model selects a satisfying proposition. A second model
interprets selection at propositions as always false: existence still holds,
but the selection principle and the selected specification both fail. Thus
the unconditional selected conclusion has no closed retained HOL proof.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SelectionProofControls

abbrev Const := HOLLightStandardTheory.Symbol Unit

def carrier (_ : Unit) : Type 1 := ULift.{1} Unit
def inhabitant (_ : Unit) : carrier () := ULift.up ()

def selection : ClosedTerm Const (SelectionProofs.Selection .prop) := .const (.select .prop)
def body : Formula Const [.prop] := .var .vz
def selectedFormula : ClosedFormula Const := instantiate (SelectionProofs.selected selection body) body

def existsProof : ProofSyntax Const [] (.ex body) := .exI .top .topI

def selectedProof : ProofSyntax Const [SelectionProofs.principle selection] selectedFormula :=
  SelectionProofs.specification selection body (.hyp 0)
    (existsProof.prepend (SelectionProofs.principle selection))

theorem selectedProof_free : selectedProof.FunctionExtensionalityFree := by
  apply SelectionProofs.specification_free
  · trivial
  · simp [existsProof, ProofSyntax.prepend, ProofSyntax.FunctionExtensionalityFree]

noncomputable def goodModel : HenkinModel.{0, 0, 0} Unit Const :=
  HOLLightStandardTheory.selectionModel carrier inhabitant

theorem good_principle : goodModel.models (SelectionProofs.principle selection) := by
  have actual := HOLLightStandardTheory.selectionModel_models_selection.{0, 0}
    carrier inhabitant (.prop : Ty Unit)
  simpa [SelectionProofs.principle, SelectionProofs.instanceFormula, selection,
    HOLLightStandardTheory.selectionFormula, weaken, HOL.rename, Rename.weaken, goodModel] using actual

theorem good_selected : goodModel.models selectedFormula := by
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant .prop
    (fun value => value) ⟨ULift.up True, trivial⟩

noncomputable def badMeaning : {type : Ty Unit} → Const type → Ty.denote.{0, 0} carrier type
  | _, .select .prop => fun _ => ULift.up False
  | _, .select (.base base) => HOLLightStandardTheory.selectionOperation carrier inhabitant (.base base)
  | _, .select (.arr domain codomain) =>
      HOLLightStandardTheory.selectionOperation carrier inhabitant (.arr domain codomain)

noncomputable def badModel : HenkinModel.{0, 0, 0} Unit Const :=
  .standard carrier badMeaning

theorem bad_exists : badModel.models (.ex body) :=
  ⟨ULift.up True, trivial, trivial⟩

theorem bad_principle : ¬ badModel.models (SelectionProofs.principle selection) := by
  intro known
  exact known (fun value => value) trivial (ULift.up True) trivial trivial

theorem bad_selected : ¬ badModel.models selectedFormula := by
  intro impossible
  exact impossible

theorem selected_not_unconditional : ¬ Nonempty (ProofSyntax Const [] selectedFormula) := by
  rintro ⟨proof⟩
  exact bad_selected (Soundness.extTheorem_sound proof.erase badModel
    (badModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)))

#print axioms selectedProof_free
#print axioms good_principle
#print axioms good_selected
#print axioms bad_exists
#print axioms bad_principle
#print axioms bad_selected
#print axioms selected_not_unconditional

end Mettapedia.Logic.HOL.SelectionProofControls

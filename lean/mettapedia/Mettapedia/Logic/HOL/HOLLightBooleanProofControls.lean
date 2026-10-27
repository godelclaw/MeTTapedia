import Mettapedia.Logic.HOL.HOLLightBooleanProofs
import Mettapedia.Logic.HOL.Soundness

/-!
# Positive and separating controls for Boolean encoding transport

The two conjunction encodings have different syntax but a retained equality
proof. The equality-based source conjunction accepts two true arguments and
rejects a true/false pair in the constructed full-domain model.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HOLLightBooleanProofControls

abbrev Const (_ : Ty Unit) := Empty

def first : ClosedFormula Const := HOLLightBooleanProofs.truth
def second : ClosedFormula Const := .bot

def comparison : ProofSyntax Const []
    (.eq (HOLLightBooleanProofs.conjunction first second) (.and first second)) :=
  HOLLightBooleanProofs.conjunctionEquation first second

theorem comparison_free : comparison.FunctionExtensionalityFree :=
  HOLLightBooleanProofs.conjunctionEquation_free _ _

def unfolding : ProofSyntax Const []
    (.eq (HOLLightBooleanDefinitions.conj first second)
      (HOLLightBooleanProofs.conjunction first second)) :=
  HOLLightBooleanProofs.sourceConjunctionBeta first second

def positive : ProofSyntax Const [] (HOLLightBooleanProofs.conjunction first first) :=
  HOLLightBooleanProofs.introduce HOLLightBooleanProofs.truthProof HOLLightBooleanProofs.truthProof

theorem positive_free : positive.FunctionExtensionalityFree :=
  HOLLightBooleanProofs.introduce_free (Δ := []) (first := first) (second := first)
    HOLLightBooleanProofs.truthProof HOLLightBooleanProofs.truthProof trivial trivial

def model : HenkinModel.{0, 0, 0} Unit Const :=
  .standard (fun _ => ULift.{1} Unit) (fun symbol => nomatch symbol)

theorem positive_holds : model.models (HOLLightBooleanProofs.conjunction first first) :=
  Soundness.extTheorem_sound positive.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))

theorem one_true_refused : ¬ model.models (HOLLightBooleanProofs.conjunction first second) := by
  have equal := Soundness.extTheorem_sound comparison.erase model
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  intro accepted
  exact (equal.mp accepted).2

theorem source_and_expansion_differ :
    HOLLightBooleanProofs.conjunction first second ≠
      ImpredicativeConnectives.expand (.and first second) := by
  intro same
  cases same

#print axioms comparison_free
#print axioms unfolding
#print axioms positive_holds
#print axioms one_true_refused
#print axioms source_and_expansion_differ

end Mettapedia.Logic.HOL.HOLLightBooleanProofControls

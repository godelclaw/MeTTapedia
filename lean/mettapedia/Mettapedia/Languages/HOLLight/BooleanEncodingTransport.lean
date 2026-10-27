import Mettapedia.Logic.HOL.HOLLightBooleanProofs
import Mettapedia.Languages.HOLLight.RetainedCompilation

/-!
# Primitive certificates between the two Boolean connective presentations

Truth and conjunction in the HOL Light source definitions differ from the
impredicative expansion used by the retained proof compiler. These closed
certificate templates prove their equality. Conjunction arguments remain
free Boolean parameters, and the existing typed substitution block supplies
instances without recompiling the template or introducing an axiom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.BooleanEncodingTransport

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation GraphExpansion PrimitiveTransport

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def leftParameter : SourceVar := ⟨Name.global "__boolean_left", Ty.bool⟩
def rightParameter : SourceVar := ⟨Name.global "__boolean_right", Ty.bool⟩

def leftFormula : HOL.ClosedFormula Symbol := .const (.variable leftParameter Ty.toHOL_bool)
def rightFormula : HOL.ClosedFormula Symbol := .const (.variable rightParameter Ty.toHOL_bool)

def truth := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.HOLLightBooleanProofs.truthEquation (Const := Symbol) (Γ := []) (Δ := []))
  HOL.HOLLightBooleanProofs.truthEquation_free Naming.empty ("boolean-truth-encoding", 0)

def conjunction := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.HOLLightBooleanProofs.conjunctionEquation (Δ := []) leftFormula rightFormula)
  (HOL.HOLLightBooleanProofs.conjunctionEquation_free _ _) Naming.empty ("boolean-conjunction-encoding", 0)

theorem truth_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    truth.proof.result truth.proof.certificate = true := truth.proof.accepted

theorem conjunction_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    conjunction.proof.result conjunction.proof.certificate = true := conjunction.proof.accepted

theorem truth_axioms_empty : truth.proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ truth_accepted))

theorem conjunction_axioms_empty : conjunction.proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ conjunction_accepted))

theorem truth_hypotheses_empty : truth.proof.result.sequent.hyp = ∅ := truth.hypotheses_exact
theorem conjunction_hypotheses_empty : conjunction.proof.result.sequent.hyp = ∅ := conjunction.hypotheses_exact

/-- The parameters have distinct names; matching preserves both arguments
even when their supplied values happen to coincide. -/
def arguments (first second : CanonicalTerm) (firstBool : first.IsBool) (secondBool : second.IsBool) :
    TypeCorrectTermSubstitution :=
  ⟨⟨TypeSubst.empty, [(leftParameter, checkedSource first), (rightParameter, checkedSource second)]⟩, by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (congrArg CanonicalTerm.ty (checkedSource_exact first)).trans firstBool
    · exact (congrArg CanonicalTerm.ty (checkedSource_exact second)).trans secondBool⟩

def conjunctionInstance (first second : CanonicalTerm) (firstBool : first.IsBool) (secondBool : second.IsBool) :
    Theorem := substituteTheorem (arguments first second firstBool secondBool) conjunction.proof.result

def conjunctionInstanceBlock (first second : CanonicalTerm)
    (firstBool : first.IsBool) (secondBool : second.IsBool) (origin : ProofExecution.Origin) :
    ProofSystem.Certificate :=
  substitutionBlock (arguments first second firstBool secondBool) conjunction.proof.result origin

theorem conjunctionInstance_checked (policy : AxiomPolicy) [DecidablePred policy]
    (first second : CanonicalTerm) (firstBool : first.IsBool) (secondBool : second.IsBool)
    (origin : ProofExecution.Origin) :
    BlockChecked policy [conjunction.proof.result]
      (conjunctionInstance first second firstBool secondBool)
      (conjunctionInstanceBlock first second firstBool secondBool origin) :=
  substitutionBlock_checked policy _ _ _

theorem parameters_distinct : leftParameter ≠ rightParameter := by
  intro same
  have names := congrArg (fun entry : SourceVar => entry.name.component) same
  exact (by decide : ("__boolean_left" : String) ≠ "__boolean_right") names

#print axioms truth_accepted
#print axioms conjunction_accepted
#print axioms conjunctionInstance_checked

end Mettapedia.Languages.HOLLight.BooleanEncodingTransport

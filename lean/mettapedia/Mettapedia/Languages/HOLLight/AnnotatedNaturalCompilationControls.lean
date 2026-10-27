import Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation
import Mettapedia.Languages.HOLLight.NaturalRecursorCompilation
import Mettapedia.Languages.HOLLight.RetainedElaboration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityInterpreterControls

/-!
# Native compilation controls for interpreted source certificates

The target uses symbolic simple carriers and the actual source selection
symbol. The resulting theorems retain selection and recursion hypotheses;
these controls do not claim their discharge or a concrete natural model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies Programs.Annotated
open NativeNaturalPredicateReading AnnotatedConversion CertificateInterpretation
open ReverseTranslation

def number : Ty := .var (Name.global "SourceNumber")
def result : Ty := .var (Name.global "SourceResult")
def operations : Operations AtomicTy Symbol where
  number := number.toHOL
  result := result.toHOL
  zero := .const (.variable ⟨Name.global "source_zero", number⟩ rfl)
  successor := .const (.variable ⟨Name.global "source_successor", .function number number⟩ (Ty.toHOL_function _ _))
  selection := NaturalRecursorCompilation.selection number result

def profile : Programs.ComputationProfiles.Selection := fun _ => true

def betaEvidence : EqualityAt operations []
    (.app (.lam (.const natName) (.var 0)) (.const zeroName)) (.const zeroName) operations.number :=
  EqualityAt.beta (domainCode := HOL.PredicateProducts.full operations.number)
    (bodyCode := .var .vz) (argumentCode := operations.zero) .natural
    (AnnotatedReads.var (Γ := [operations.number]) .vz) .zero

def betaReceived : CheckedEquality operations profile [] .nil
    (.app (.lam (.const natName) (.var 0)) (.const zeroName)) (.const zeroName) (.const natName) :=
  ⟨.nil, JudgmentReplay.Controls.independent_beta, ⟨operations.number, betaEvidence⟩⟩

def betaCompiled : RetainedCompilation.Compiled emptyAxiomPolicy Naming.empty
    ((assumptions operations []).map HOL.ImpredicativeConnectives.expand)
    (HOL.ImpredicativeConnectives.expand (.eq betaReceived.sourceState.code betaReceived.targetState.code)) :=
  compile betaReceived Naming.empty ("annotated-beta", 0)

theorem beta_accepted : (ProofSystem.checker emptyAxiomPolicy).check betaCompiled.proof.result
    betaCompiled.proof.certificate = true := betaCompiled.proof.accepted

theorem beta_claim_exact : betaCompiled.proof.result.sequent.concl =
    reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand
      (.eq betaReceived.sourceState.code betaReceived.targetState.code)) :=
  betaCompiled.conclusion_exact

def zeroEvidence : EqualityAt operations operations.parameters (Row.zero.left operations)
    (Row.zero.right operations) operations.result :=
  EqualityAt.row .zero CTm.ids HOL.Subst.id (fun index => .var index)

def zeroReceived : CheckedEquality operations profile operations.parameters (Row.zero.context operations)
    (Row.zero.left operations) (Row.zero.right operations) (Row.zero.type operations) :=
  ⟨JudgmentReplay.context_sound profile CertificateInterpretation.Controls.zero_context_checked,
    JudgmentReplay.check_sound profile CertificateInterpretation.Controls.zero_source_checked,
    ⟨operations.result, zeroEvidence⟩⟩

def names : Naming operations.parameters :=
  Naming.cons (Name.global "source_method")
    (Naming.cons (Name.global "source_base") (Naming.cons (Name.global "source_family") Naming.empty))

def zeroCompiled : RetainedCompilation.Compiled emptyAxiomPolicy names
    ((assumptions operations operations.parameters).map HOL.ImpredicativeConnectives.expand)
    (HOL.ImpredicativeConnectives.expand (.eq zeroReceived.sourceState.code zeroReceived.targetState.code)) :=
  compile zeroReceived names ("annotated-zero", 0)

theorem zero_accepted : (ProofSystem.checker emptyAxiomPolicy).check zeroCompiled.proof.result
    zeroCompiled.proof.certificate = true := zeroCompiled.proof.accepted

theorem zero_assumptions_exact : zeroCompiled.proof.result.sequent.hyp =
    reverseHypotheses names ((assumptions operations operations.parameters).map HOL.ImpredicativeConnectives.expand) :=
  zeroCompiled.hypotheses_exact

#print axioms beta_accepted
#print axioms beta_claim_exact
#print axioms zero_accepted
#print axioms zero_assumptions_exact

end Mettapedia.Languages.HOLLight.AnnotatedNaturalCompilation.Controls

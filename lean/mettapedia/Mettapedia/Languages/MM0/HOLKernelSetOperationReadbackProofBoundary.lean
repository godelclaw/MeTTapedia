import Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Statement readback and source derivability are distinct

The syntax reader accepts the faithful encoding of the false proposition.
The actual well-founded material model refutes a derivation of that formula
from no assumptions. An acceptance-to-source theorem must therefore also
use the native inference evidence and its explicit theory policy.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls
open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation (Symbol)
theorem false_source_not_derivable :
    IsEmpty (ProofSyntax Symbol [] (Term.bot : ClosedFormula Symbol)) := by
  refine ⟨fun proof => ?_⟩
  exact Soundness.extDerivation_sound (M := Embedding.ZFSetHenkinInterpretation.model.{0})
    (ρ := fun {_} (index : Var ([] : Ctx Unit) _) => nomatch index) proof.erase
    (Embedding.ZFSetHenkinInterpretation.model.functionsRespectEqv_of_fullDomains
      Embedding.ZFSetHenkinInterpretation.fullDomains)
    (fun index => nomatch index) (by intro formula member; simp at member)

theorem statement_readback_is_not_derivability :
    HOLKernelSetOperationReadback.readSequent references
      (HOLKernelSetOperationInterpretation.statement references [] .bot) = some ([], .bot) ∧
      IsEmpty (ProofSyntax Symbol [] (Term.bot : ClosedFormula Symbol)) :=
  ⟨false_sequent_readback, false_source_not_derivable⟩

#print axioms false_source_not_derivable
#print axioms statement_readback_is_not_derivability
end Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackControls

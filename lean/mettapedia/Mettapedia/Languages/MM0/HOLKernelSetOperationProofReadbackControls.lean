import Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback
import Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackProofBoundary

/-!
# Proof readback controls for the common material signature

Intrinsic formation is retained as term data even though its discharged
logical reading is truth. Union and powerset supply distinct typing claims
with that same logical reading. A reconstructed source proof cannot establish
falsity from no source assumptions in the actual material model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadbackControls

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgmentReadback HOLKernelSetOperationProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol mapping)

theorem distinct_formation_same_logical_reading :
    (Judgment.typing (Term.const Symbol.union) : Judgment Symbol []).formula = .top ∧
    (Judgment.typing (Term.const Symbol.power) : Judgment Symbol []).formula = .top ∧
    HOLKernelSetOperationInterpretation.symbolCode Symbol.union ≠
      HOLKernelSetOperationInterpretation.symbolCode Symbol.power :=
  ⟨rfl, rfl, HOLKernelSetOperationInterpretation.union_power_distinct⟩

theorem closed_typing_readback
    (references : HOLKernelSyntax.Symbol → Nat) (faithful : Function.Injective references)
    {type : Ty Unit} (term : ClosedTerm Symbol type) :
    HOLKernelJudgmentReadback.readTyping references HOLKernelSetOperationReadback.readConstant 7
      NamedElaboration.BinderNames.nil
      (HOLKernelSetOperationReadback.encode references NamedElaboration.BinderNames.nil 0 term)
      (encodeType references HOLKernelSetOperationInterpretation.typeCode type) = some (.typing term) := by
  exact readTyping_encode references faithful HOLKernelSetOperationReadback.readConstant
    HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol
    HOLKernelSetOperationReadback.symbolIndex_bound
    NamedElaboration.BinderNames.nil 0
    ⟨by simp [NamedElaboration.BinderNames.toList], by simp [NamedElaboration.BinderNames.toList]⟩ term

theorem closed_identity_typing :
    HOLKernelJudgmentReadback.readTyping HOLKernelSetOperationReadbackControls.references
      HOLKernelSetOperationReadback.readConstant 7 NamedElaboration.BinderNames.nil
      (HOLKernelSetOperationReadback.encode HOLKernelSetOperationReadbackControls.references
        NamedElaboration.BinderNames.nil 0 (Term.lam (Term.var .vz) : ClosedTerm Symbol (.prop ⇒ .prop)))
      (encodeType HOLKernelSetOperationReadbackControls.references
        HOLKernelSetOperationInterpretation.typeCode (.prop ⇒ .prop)) =
      some (.typing (Term.lam (Term.var .vz) : ClosedTerm Symbol (.prop ⇒ .prop))) :=
  closed_typing_readback HOLKernelSetOperationReadbackControls.references
    HOLKernelSetOperationReadbackControls.references_injective _

variable {terms : TermSignature} {definitions : Definition.Signature} {theorems : TheoremSignature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}

theorem reconstructed_false_requires_assumptions
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {context : Context} {witness : ProofWitness}
    (reconstructed : SourceProofReadback abbreviation theorems context witness)
    (empty : reconstructed.sequent.1 = [])
    (falsity : reconstructed.sequent.2 = .bot) : False :=
  HOLKernelSetOperationReadbackControls.false_source_not_derivable.false
    (ProofSyntax.castIndices empty falsity reconstructed.proof)

#print axioms closed_typing_readback
#print axioms reconstructed_false_requires_assumptions

end Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadbackControls

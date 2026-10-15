import Mettapedia.Languages.HOLLight.DefinitionAdapters

/-!
# Boolean conclusions in registered HOL Light histories

The theorem applies to the existing registered derivation judgment, including
both definition operations. Source theorem records are raw typed data, so
Booleanity is earned from derivability rather than from their record shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight

open Mettapedia.Languages.OpenTheory
open DefinitionAdapters

private theorem substitution_conclusion_boolean (substitution : TypeCorrectTermSubstitution)
    (input out : Theorem) (step : TheoremSubstitutionSemantics substitution input out)
    (boolean : input.sequent.concl.IsBool) : out.sequent.concl.IsBool := by
  obtain ⟨_, _, conclusion⟩ := step
  rw [← (apply_eq_iff_termSubstitutionSemantics _ _ _).mpr conclusion]
  show substitution.raw.types.apply input.sequent.concl.ty = Ty.bool
  rw [show input.sequent.concl.ty = Ty.bool from boolean, TypeSubst.apply_bool]

/-- Every source inference preserves Boolean conclusions, using Boolean
premises only where the source operation actually needs them. -/
theorem InferenceRequest.Semantics.conclusionBoolean {request : InferenceRequest} {out : Theorem}
    (step : request.Semantics out)
    (premises : ∀ premise ∈ request.premises, premise.sequent.concl.IsBool) :
    out.sequent.concl.IsBool := by
  cases request with
  | refl term =>
      obtain ⟨_, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | trans left right =>
      obtain ⟨_, _, _, _, _, _, _, _, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | mkComb left right =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | abs binder input =>
      obtain ⟨_, _, _, _, _, _, _, _, _, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | beta source =>
      obtain ⟨_, _, _, _, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | assume term =>
      obtain ⟨boolean, parts⟩ := step
      rw [parts.2.2]
      exact boolean
  | eqMp equality premise =>
      obtain ⟨left, right, view, same, parts⟩ := step
      rw [parts.2.2]
      show right.ty = Ty.bool
      rw [← view.1, same]
      exact premises premise (by simp [InferenceRequest.premises])
  | deductAntisym left right =>
      obtain ⟨_, construction, parts⟩ := step
      rw [parts.2.2]
      exact construction.resultIsBool
  | instType entries input =>
      exact substitution_conclusion_boolean _ input out step
        (premises input (by simp [InferenceRequest.premises]))
  | inst entries input =>
      obtain ⟨_, _, actual⟩ := step
      exact substitution_conclusion_boolean _ input out actual
        (premises input (by simp [InferenceRequest.premises]))

private theorem source_definition_conclusions_boolean {context : TheoryContext}
    {witnesses : SignatureFormation.InstanceWitnesses} {request : TypeOperatorDefinitionRequest}
    {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context witnesses request = some result) :
    result.output.abstractionRepresentationTheorem.sequent.concl.IsBool ∧
      result.output.representationAbstractionTheorem.sequent.concl.IsBool := by
  cases view : request.existence.sequent.concl.applicationView? with
  | none => simp [admitSourceTypeInTheory, view] at accepted
  | some application =>
      simp only [admitSourceTypeInTheory, view] at accepted
      cases admitted : admitTypeInTheoryFromApplication context witnesses request
          application.function application.argument application.semantics with
      | none => simp [admitted] at accepted
      | some core =>
          simp only [admitted] at accepted
          split at accepted
          · have same := Option.some.inj accepted
            subst result
            exact ⟨rfl, rfl⟩
          · contradiction

/-- Definitions and weakening preserve the same Boolean conclusion invariant
as inference. No additional initial-record admission is introduced. -/
theorem DefinitionAdapters.TheoryDerives.conclusionBoolean {policy : AxiomPolicy}
    {context : TheoryContext} {out : Theorem} (derived : TheoryDerives policy context out) :
    out.sequent.concl.IsBool := by
  induction derived with
  | inference step _ _ _ induction => exact step.conclusionBoolean induction
  | «axiom» _ _ step _ =>
      rw [step.2.2.2]
      exact step.1.1
  | weaken _ _ induction => exact induction
  | constantDefinition accepted _ =>
      have checked := (admitConstantInTheory_result accepted).2.2.2.2.1
      obtain ⟨_, _, _, _, _, _, construction, parts⟩ := checkConstantDefinition_result checked
      rw [parts.2.2]
      exact construction.resultIsBool
  | typeAbstractionDefinition accepted _ _ _ => exact (source_definition_conclusions_boolean accepted).1
  | typeRepresentationDefinition accepted _ _ _ => exact (source_definition_conclusions_boolean accepted).2

end Mettapedia.Languages.HOLLight

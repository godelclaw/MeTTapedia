import Mettapedia.Languages.MM0.HOLKernelProofExtensionalityReadback

/-!
# Admission of truth, hypotheses and eta in material HOL compilation

The actual retained compiler outputs for truth, every ordered hypothesis
occurrence and eta belong to the independent native admission grammar. Canonical
source terms are sorted in the allocated native name bank, and the decoded
formation/assumption context supplies the exact source antecedent.

These constructor cases use the same compiler, rule tables and source statement
as the full forward route. They begin its compiler-image proof; the logical,
binding and conversion constructions retain their own remaining obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)
open HOLKernelProofAllocation HOLKernelEnvironmentReadback

variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature}


theorem compile_topI_witness
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (assumptions : List (ClosedFormula Symbol)) :
    (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
      (ProofSyntax.topI : ProofSyntax Symbol assumptions .top)).val =
      .theoremApp (rules.index .truth)
        [HOLKernelAssumptions.antecedent signature.symbol (HOLKernelSetOperationInterpretation.formation signature.symbol)
          (assumptions.map fun formula => HOLKernelJudgment.holds signature.symbol
            (HOLKernelSetOperationInterpretation.term signature.symbol formula))] [] := by
  rfl


theorem truth_admitted {context : Context}
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (named : signature.names abbreviation.reference = some "bi")
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .truth) = some (.inference .truth))
    (antecedent : Preterm) (g : ClosedFormula Symbol)
    (reading : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 BinderNames.nil antecedent = some g)
    (checked : ProofWitness.Checks terms definitions theorems context []
      (.theoremApp (rules.index .truth) [antecedent] [])
      (HOLKernelJudgment.entails signature.symbol antecedent
        (HOLKernelJudgment.holds signature.symbol (applySymbol signature.symbol .truth [])))) :
    Nonempty (AdmittedProof abbreviation theorems context
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt 1 BinderNames.nil (.theoremApp (rules.index .truth) [antecedent] []) (.imp g .top)) := by
  have scope : InScope 7 (BinderNames.nil : Names []) 0 :=
    ⟨by simp [BinderNames.toList], by simp [BinderNames.toList]⟩
  exact HOLKernelInferenceReadback.application_admitted profile abbreviation
    (abbreviation_reference_distinct abbreviation named) rules BinderNames.nil 0 scope antecedent
    (.truth g) reading ruleAt bindingAt selected
    ⟨[], HOLKernelJudgment.entails signature.symbol antecedent
      (HOLKernelJudgment.holds signature.symbol (applySymbol signature.symbol .truth []))⟩
    (checked.instantiates (rules.declared .truth) .nil) [] checked 0 .nil


theorem compile_topI_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (named : signature.names abbreviation.reference = some "bi")
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ruleAt (rules.index .truth) = some (.inference .truth))
    (assumptions : List (ClosedFormula Symbol)) :
    Nonempty (AdmittedSourceProof signature abbreviation theorems profile
      ((HOLKernelProofAllocation.forProof (ProofSyntax.topI : ProofSyntax Symbol assumptions .top)).target
        (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      ruleAt bindingAt 1
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
        (ProofSyntax.topI : ProofSyntax Symbol assumptions .top)).val (assumptions, .top)) := by
  let compiled := HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
    (ProofSyntax.topI : ProofSyntax Symbol assumptions .top)
  have reading := read_sourceAntecedent profile abbreviation (abbreviation_reference_distinct abbreviation named) assumptions
  have logicalReading : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 BinderNames.nil
      (HOLKernelAssumptions.antecedent signature.symbol (HOLKernelSetOperationInterpretation.formation signature.symbol)
        (assumptions.map fun formula => HOLKernelJudgment.holds signature.symbol
          (HOLKernelSetOperationInterpretation.term signature.symbol formula))) =
      some (sourceContext assumptions).formula := by
    simpa only [readFormulaIn, Option.map_some] using congrArg (Option.map Judgment.formula) reading
  obtain ⟨tree⟩ := truth_admitted signature abbreviation profile rules named ruleAt bindingAt selected
    _ _ logicalReading compiled.property
  exact ⟨AdmittedSourceProof.ofTree signature abbreviation profile named (assumptions, .top)
    compiled.property.eval tree⟩


theorem compile_hyp_witness
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (assumptions : List (ClosedFormula Symbol)) (occurrence : Fin assumptions.length)
    (formed : Preterm.HasType terms
      ((HOLKernelProofAllocation.forProof (ProofSyntax.hyp occurrence : ProofSyntax Symbol assumptions _)).target
        (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      (HOLKernelSetOperationInterpretation.formation signature.symbol) [] signature.ids.wff)
    (sorted : ∀ value ∈ assumptions.map (fun formula => HOLKernelJudgment.holds signature.symbol
        (HOLKernelSetOperationInterpretation.term signature.symbol formula)),
      Preterm.HasType terms
        ((HOLKernelProofAllocation.forProof (ProofSyntax.hyp occurrence : ProofSyntax Symbol assumptions _)).target
          (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
        value [] signature.ids.wff) :
    (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
      (ProofSyntax.hyp occurrence : ProofSyntax Symbol assumptions _)).val =
      (HOLKernelAssumptions.hypothesis (definitions := definitions) (hypotheses := []) signature structural
        (HOLKernelSetOperationInterpretation.formation signature.symbol) formed
        (assumptions.map fun formula => HOLKernelJudgment.holds signature.symbol
          (HOLKernelSetOperationInterpretation.term signature.symbol formula)) sorted
        ⟨occurrence.val, by rw [List.length_map]; exact occurrence.isLt⟩).val := by
  rfl


theorem compile_hyp_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (named : signature.names abbreviation.reference = some "bi")
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (assumptions : List (ClosedFormula Symbol)) (occurrence : Fin assumptions.length) :
    ∃ fuel, Nonempty (AdmittedSourceProof signature abbreviation theorems profile
      ((HOLKernelProofAllocation.forProof (ProofSyntax.hyp occurrence : ProofSyntax Symbol assumptions _)).target
        (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      ruleAt bindingAt fuel
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
        (ProofSyntax.hyp occurrence : ProofSyntax Symbol assumptions _)).val
      (assumptions, assumptions.get occurrence)) := by
  let proof : ProofSyntax Symbol assumptions (assumptions.get occurrence) := .hyp occurrence
  let layout := HOLKernelProofAllocation.forProof proof
  let compiled := HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof
  have distinct := abbreviation_reference_distinct abbreviation named
  obtain ⟨fuel, ⟨tree⟩⟩ := HOLKernelEnvironmentReadback.initial_assumptions_admitted
    abbreviation profile distinct layout structural ruleAt bindingAt selected assumptions
    proof.assumptionBinderDepth_lt occurrence
  exact ⟨fuel, ⟨AdmittedSourceProof.ofTree signature abbreviation profile named
    (assumptions, assumptions.get occurrence) compiled.property.eval tree⟩⟩


#print axioms compile_hyp_admitted

#print axioms compile_hyp_witness

#print axioms compile_topI_admitted

#print axioms compile_topI_witness
theorem compile_eta_admitted
    (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (named : signature.names abbreviation.reference = some "bi")
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (assumptions : List (ClosedFormula Symbol))
    {domain result : Ty Unit} (function : ClosedTerm Symbol (domain ⇒ result)) :
    ∃ fuel, Nonempty (AdmittedSourceProof signature abbreviation theorems profile
      ((forProof (ProofSyntax.eta function : ProofSyntax Symbol assumptions _)).target
        (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      ruleAt bindingAt fuel
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding
        (ProofSyntax.eta function : ProofSyntax Symbol assumptions _)).val
      (assumptions, .eq (.lam (.app (weaken function) (.var .vz))) function)) := by
  let proof : ProofSyntax Symbol assumptions (.eq (.lam (.app (weaken function) (.var .vz))) function) := .eta function
  let layout := forProof proof
  have distinct := abbreviation_reference_distinct abbreviation named
  let reading := initialReading abbreviation profile distinct layout structural assumptions proof.assumptionBinderDepth_lt
  have projection := initial_projection_admitted abbreviation profile distinct layout structural ruleAt bindingAt
    structuralSelected assumptions proof.assumptionBinderDepth_lt
  have fits : function.binderDepth + 1 ≤ layout.width := by
    have own := proof.conclusionBinderDepth_lt
    simp only [Term.binderDepth, weaken, Term.binderDepth_rename] at own
    change _ < layout.width at own
    omega
  have active : 0 < layout.frames := proof.nodeCount_pos
  have before : 0 + layout.width ≤ layout.workDepth 0 := by simp [Layout.workDepth]
  obtain ⟨fuel, ⟨tree⟩⟩ := reading.eta_admitted distinct structural typing rules binding function fits active before
    ruleAt bindingAt selected (structuralSelected .syl) bindingSelected projection
  let compiled := HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof
  exact ⟨fuel, ⟨AdmittedSourceProof.ofTree signature abbreviation profile named
    (assumptions, .eq (.lam (.app (weaken function) (.var .vz))) function) compiled.property.eval tree⟩⟩

#print axioms compile_eta_admitted

end Mettapedia.Languages.MM0.HOLKernelSetOperationProofReadback


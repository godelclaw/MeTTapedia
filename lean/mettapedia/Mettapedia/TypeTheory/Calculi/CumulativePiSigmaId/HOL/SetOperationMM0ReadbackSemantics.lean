import Mettapedia.Languages.MM0.HOLKernelInitialProofReadback
import Mettapedia.Languages.MM0.HOLKernelProofCompilationReadback
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationMaterialProofSemantics

/-!
# Reconstructed MM0 proofs in the cumulative dependent and material readings

A successful native proof readback supplies its computed ordinary HOL proof
to the existing dependent compiler. Typing, substitution and the actual
proof-family interpretation concern that same computed program. The four
material models retain their separate membership relations and the explicit
meanings of the ordered source hypotheses.

The complete common-source compiler image is admitted by the independent
reader. `compiled_readback_program` derives the typed interpreted program
from that same native witness.

This composition does not assert that every native certificate is admitted
by readback or that a material proof reading recovers proof identity.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMM0ReadbackSemantics
open Presentation Presentation.FormationSensitive
open Mettapedia.Logic HOL.Embedding
open ZFSetHenkinInterpretation (Symbol)
open Mettapedia.Languages.MM0
open Kernel HOLKernelSyntax HOLKernelSetOperationProofReadback
open HOLNativeGenericProofCompiler HenkinFamilySemantics
open SetOperationExtensionalProfile (reading)
open SetOperationExtensionalOperations (operations)
open SetOperationSignature (proofName)
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe w
variable {terms : TermSignature} {definitions : Definition.Signature} {theorems : TheoremSignature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}
variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
variable {context : Context} {witness : ProofWitness}

def program (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} (objects : Sub Tower.Head 0 n)
    (hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) :
    Tower.Tm n := SetOperationProofCompilation.compile reconstructed.proof objects hypotheses

theorem program_typed (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {targetContext : Tower.Ctx n} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects (gamma := []) reading targetContext objects)
    (hypothesisTyped : GenericTyping.Hypotheses (gamma := [])
      (delta := reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand)
      reading operations targetContext objects hypotheses) :
    Typing operations.target targetContext (program reconstructed objects hypotheses)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate reading reconstructed.sequent.2))) :=
  SetOperationProofCompilation.compile_typed reconstructed.proof objectTyped hypothesisTyped

theorem program_substitute (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n m : Nat} (objects : Sub Tower.Head 0 n)
    (hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (sigma : Sub Tower.Head n m) :
    program reconstructed (fun index => subst sigma (objects index))
      (fun index => subst sigma (hypotheses index)) = subst sigma (program reconstructed objects hypotheses) :=
  SetOperationProofCompilation.compile_substitute reconstructed.proof objects hypotheses sigma

theorem program_proves (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)
    (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra model full) state hypotheses) :
    SetOperationProofFamilySemantics.Proves model state (program reconstructed objects hypotheses)
      reconstructed.sequent.2 :=
  SetOperationProofCompilerSemantics.compile_proves model full reconstructed.proof state meanings

theorem sets_program_readout (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading ZFSetHenkinInterpretation.model.{w} objects)
    (meanings : GenericSemantics.Hypotheses
      (SetOperationProofCompilerSemantics.algebra _ ZFSetHenkinInterpretation.fullDomains) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state reconstructed.sequent.2)),
      SetOperationProofFamilySemantics.Denotes ZFSetHenkinInterpretation.model state.context
        (program reconstructed objects hypotheses) (truthFamily (formulaMeaning state reconstructed.sequent.2)) value ∧
      ∀ environment,
        (SetOperationMaterialProofSemantics.setProofReadout state reconstructed.sequent.2 value environment).1 = ∅ :=
  SetOperationMaterialProofSemantics.sets_compile_proves reconstructed.proof state meanings

theorem hypersets_program_readout (presentation : HSet.Presentation.{w})
    (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (HypersetHenkinInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (HypersetHenkinInterpretation.fullDomains presentation)) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state reconstructed.sequent.2)),
      SetOperationProofFamilySemantics.Denotes (HypersetHenkinInterpretation.model presentation) state.context
        (program reconstructed objects hypotheses) (truthFamily (formulaMeaning state reconstructed.sequent.2)) value ∧
      ∀ environment,
        (SetOperationMaterialProofSemantics.hypersetProofReadout presentation state reconstructed.sequent.2 value environment).1 = ∅ :=
  SetOperationMaterialProofSemantics.hypersets_compile_proves presentation reconstructed.proof state meanings

theorem wellFounded_program_proves (presentation : HSet.Presentation.{w})
    (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (WellFoundedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (WellFoundedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (WellFoundedHypersetInterpretation.model presentation) state
      (program reconstructed objects hypotheses) reconstructed.sequent.2 :=
  program_proves _ (WellFoundedHypersetInterpretation.fullDomains presentation) reconstructed state meanings

theorem codes_program_proves (presentation : HSet.Presentation.{w})
    (reconstructed : SourceProofReadback abbreviation theorems context witness)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (reconstructed.sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (CodedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (CodedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (CodedHypersetInterpretation.model presentation) state
      (program reconstructed objects hypotheses) reconstructed.sequent.2 :=
  program_proves _ (CodedHypersetInterpretation.fullDomains presentation) reconstructed state meanings

theorem admitted_source_readback {sorts : SortSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule)
    (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (fuel : Nat) (sequent : HOLKernelSetOperationReadback.SourceSequent)
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent) :
    ∃ reconstructed : SourceProofReadback abbreviation theorems context witness,
      readSourceProof signature abbreviation theorems logical context ruleAt bindingAt fuel witness =
        some reconstructed ∧
      reconstructed.sequent = sequent ∧
      HOL.ExtDerivation Symbol sequent.1 sequent.2 := by
  obtain ⟨reconstructed, hread, hseq⟩ :=
    readSourceProof_of_admitted signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent admitted
  refine ⟨reconstructed, hread, hseq, ?_⟩
  have derived := reconstructed.source_derivation
  rw [hseq] at derived
  exact derived

section Admitted
variable {sorts : SortSignature} {signature : Signature sorts terms}
variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
variable {logical : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
variable {ruleAt : Nat → Option HOLKernelRuleReadback.Rule}
variable {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
variable {fuel : Nat} {sequent : HOLKernelSetOperationReadback.SourceSequent}

/-- Compile the source proof computed from an admitted native certificate.
The program is indexed by the submitted sequent, rather than by a separately
supplied source derivation. -/
def admittedProgram
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} (objects : Sub Tower.Head 0 n)
    (hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) : Tower.Tm n :=
  SetOperationProofCompilation.compile admitted.sourceProof objects hypotheses

theorem admittedProgram_typed
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {targetContext : Tower.Ctx n} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects (gamma := []) reading targetContext objects)
    (hypothesisTyped : GenericTyping.Hypotheses (gamma := [])
      (delta := sequent.1.map HOL.ImpredicativeConnectives.expand)
      reading operations targetContext objects hypotheses) :
    Typing operations.target targetContext (admittedProgram admitted objects hypotheses)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate reading sequent.2))) :=
  SetOperationProofCompilation.compile_typed admitted.sourceProof objectTyped hypothesisTyped

theorem admittedProgram_substitute
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n m : Nat} (objects : Sub Tower.Head 0 n)
    (hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n)
    (sigma : Sub Tower.Head n m) :
    admittedProgram admitted (fun index => subst sigma (objects index))
      (fun index => subst sigma (hypotheses index)) =
      subst sigma (admittedProgram admitted objects hypotheses) :=
  SetOperationProofCompilation.compile_substitute admitted.sourceProof objects hypotheses sigma

theorem admittedProgram_proves (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra model full) state hypotheses) :
    SetOperationProofFamilySemantics.Proves model state (admittedProgram admitted objects hypotheses) sequent.2 :=
  SetOperationProofCompilerSemantics.compile_proves model full admitted.sourceProof state meanings

theorem admitted_sets_readout
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading ZFSetHenkinInterpretation.model.{w} objects)
    (meanings : GenericSemantics.Hypotheses
      (SetOperationProofCompilerSemantics.algebra _ ZFSetHenkinInterpretation.fullDomains) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state sequent.2)),
      SetOperationProofFamilySemantics.Denotes ZFSetHenkinInterpretation.model state.context
        (admittedProgram admitted objects hypotheses) (truthFamily (formulaMeaning state sequent.2)) value ∧
      ∀ environment,
        (SetOperationMaterialProofSemantics.setProofReadout state sequent.2 value environment).1 = ∅ :=
  SetOperationMaterialProofSemantics.sets_compile_proves admitted.sourceProof state meanings

theorem admitted_hypersets_readout (presentation : HSet.Presentation.{w})
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (HypersetHenkinInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (HypersetHenkinInterpretation.fullDomains presentation)) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state sequent.2)),
      SetOperationProofFamilySemantics.Denotes (HypersetHenkinInterpretation.model presentation) state.context
        (admittedProgram admitted objects hypotheses) (truthFamily (formulaMeaning state sequent.2)) value ∧
      ∀ environment,
        (SetOperationMaterialProofSemantics.hypersetProofReadout presentation state sequent.2 value environment).1 = ∅ :=
  SetOperationMaterialProofSemantics.hypersets_compile_proves presentation admitted.sourceProof state meanings

theorem admitted_wellFounded_proves (presentation : HSet.Presentation.{w})
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (WellFoundedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (WellFoundedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (WellFoundedHypersetInterpretation.model presentation) state
      (admittedProgram admitted objects hypotheses) sequent.2 :=
  admittedProgram_proves _ (WellFoundedHypersetInterpretation.fullDomains presentation) admitted state meanings

theorem admitted_codes_proves (presentation : HSet.Presentation.{w})
    (admitted : AdmittedSourceProof signature abbreviation theorems logical context
      ruleAt bindingAt fuel witness sequent)
    {n : Nat} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (sequent.1.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (CodedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (CodedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (CodedHypersetInterpretation.model presentation) state
      (admittedProgram admitted objects hypotheses) sequent.2 :=
  admittedProgram_proves _ (CodedHypersetInterpretation.fullDomains presentation) admitted state meanings

end Admitted

/-- The actual MM0 compiler output reconstructs a typed dependent proof with
its source conclusion in any of the full-domain material interpretations. -/
theorem compiled_readback_program
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (ruleAt : Nat → Option HOLKernelRuleReadback.Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    {assumptions : List (HOL.ClosedFormula Symbol)} {formula : HOL.ClosedFormula Symbol}
    (proof : HOL.ProofSyntax Symbol assumptions formula)
    (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)
    {n : Nat} {targetContext : Tower.Ctx n} {objects : Sub Tower.Head 0 n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : GenericTyping.Objects (gamma := []) reading targetContext objects)
    (hypothesisTyped : GenericTyping.Hypotheses (gamma := [])
      (delta := assumptions.map HOL.ImpredicativeConnectives.expand)
      reading operations targetContext objects hypotheses)
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra model full) state hypotheses) :
    ∃ fuel, ∃ admitted : AdmittedSourceProof signature abbreviation theorems profile
      ((HOLKernelProofAllocation.forProof proof).target (HOLKernelSetOperationInterpretation.initialContext signature.ids) signature.ids.object)
      ruleAt bindingAt fuel
      (HOLKernelSetOperationInterpretation.compile signature abbreviation profile structural typing rules binding proof).val
      (assumptions, formula),
      Typing operations.target targetContext (admittedProgram admitted objects hypotheses)
        (FormationSensitiveHOLGenericProofFamily.proof proofName
          (subst objects (HOLImpredicativeRepresentation.translate reading formula))) ∧
      SetOperationProofFamilySemantics.Proves model state (admittedProgram admitted objects hypotheses) formula := by
  obtain ⟨fuel, ⟨admitted⟩⟩ := HOLKernelProofCompilationReadback.closed_compile_admitted
    abbreviation profile distinct structural typing rules binding ruleAt bindingAt
    selected structuralSelected bindingSelected proof
  exact ⟨fuel, admitted, admittedProgram_typed admitted objectTyped hypothesisTyped,
    admittedProgram_proves model full admitted state meanings⟩

#print axioms compiled_readback_program

#print axioms program_typed
#print axioms program_proves
#print axioms sets_program_readout
#print axioms hypersets_program_readout
#print axioms admitted_source_readback
#print axioms admittedProgram
#print axioms admittedProgram_typed
#print axioms admittedProgram_substitute
#print axioms admittedProgram_proves
#print axioms admitted_sets_readout
#print axioms admitted_hypersets_readout
#print axioms admitted_wellFounded_proves
#print axioms admitted_codes_proves
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMM0ReadbackSemantics

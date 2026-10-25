import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationCheckedCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationMaterialProofSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilyConversionBoundary

/-!
# Common-profile kernel checking and actual dependent proof meaning

An accepted Megalodon program constructs its typed native proof and realizes
the original formula in the independently defined proof-family model. The
checking profile remains the admitted opaque six-operation profile, and the
source proof is reconstructed rather than provided. Local hypothesis meanings
remain explicit and ordered.

The retained semantic-codec control still distinguishes two Boolean readings
of one native variable. The proof interpretation supplies a chosen realization;
it asserts neither unique execution meaning nor reflection of every native value.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationKernelProofSemantics
open Presentation
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open Mettapedia.Languages.Megalodon
open MathdataKernel HenkinTermInterpretation NativeProof
open HOLNativeGenericProofCompiler HenkinFamilySemantics
open SetOperationExtensionalProfile (reading)

universe w
variable (model : HOL.HenkinModel.{0,0,w} Unit Symbol) (full : model.FullDomains)
variable (instances : List (HOL.Ty Base × HOL.Ty Base)) (fuel depth : Nat)
variable {gamma : HOL.Ctx Unit}
variable (assumptions : List (HOL.Formula Symbol gamma)) (goal : HOL.Formula Symbol gamma)
variable (program : Pf) (fragment : Fragment (SetOperationExtensionality.environment instances) depth program)
variable (accepted : checkProof (SetOperationExtensionality.environment instances) fuel depth
  ((gamma.map Mettapedia.Languages.Megalodon.SetOperationProofCompilation.type).map reifyType)
  (assumptions.map (fun formula => HOLNormalForms.normalFormCode
    (SetOperationExtensionality.term instances formula))) program
  (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true)

theorem accepted_program_proves {n : Nat} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading model objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra model full) state hypotheses) :
    SetOperationProofFamilySemantics.Proves model state
      (SetOperationCheckedCompilation.compile instances fuel depth assumptions goal program fragment accepted objects hypotheses) goal :=
  SetOperationProofCompilerSemantics.compile_proves model full
    (SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted)
    state meanings

include full

theorem checked_truth_hasMeaning :
    SetOperationProofFamilySemantics.Proves model (SetOperationProofCompilerSemantics.emptyState model)
      SetOperationCheckedCompilation.truthProgram (HOL.Term.top : HOL.ClosedFormula Symbol) :=
  SetOperationProofCompilerSemantics.compile_closed_proves model full
    (SetOperationProofReconstruction.checkedSource [] 2 0 [] .top
      SetOperationProofReconstructionControls.truthProgram
      SetOperationProofReconstructionControls.truth_fragment SetOperationProofReconstructionControls.truth_checked)

omit full

theorem checked_set_truth_hasMeaning :
    SetOperationProofFamilySemantics.Proves Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.model.{w}
      (SetOperationProofCompilerSemantics.emptyState Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.model)
      SetOperationCheckedCompilation.truthProgram (HOL.Term.top : HOL.ClosedFormula Symbol) := by
  apply accepted_program_proves Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.model
    Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.fullDomains
    [] 2 0 [] .top SetOperationProofReconstructionControls.truthProgram
    SetOperationProofReconstructionControls.truth_fragment SetOperationProofReconstructionControls.truth_checked
    (SetOperationProofCompilerSemantics.emptyState _)
  intro index
  nomatch index

theorem semantic_codec_does_not_reflect_values :
    let model := Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.model.{0}
    ∃ first second : Section (ConversionBoundary.booleanContext.{0}.family 0),
      SetOperationProofFamilySemantics.Denotes model ConversionBoundary.booleanContext (.var 0)
        (ConversionBoundary.booleanContext.family 0) first ∧
      SetOperationProofFamilySemantics.Denotes model ConversionBoundary.booleanContext (.var 0)
        (ConversionBoundary.booleanContext.family 0) second ∧ first ≠ second :=
  ⟨ConversionBoundary.falseSection, ConversionBoundary.trueSection,
    .underlying (ConversionBoundary.variable_realizes_false reading _),
    .underlying (ConversionBoundary.variable_recodes_to_true reading _), ConversionBoundary.sections_distinct⟩

#print axioms accepted_program_proves
#print axioms checked_truth_hasMeaning
#print axioms semantic_codec_does_not_reflect_values
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationKernelProofSemantics

import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationProofCompilation
import Mettapedia.Languages.Megalodon.SetOperationProofReconstructionControls

/-!
# Accepted common HOL programs produce typed dependent proofs

The admitted Megalodon checking profile reconstructs the exact source judgment.
The total material-signature compiler then constructs its native dependent
proof term. The source proof is computed from the checked program, rather than
supplied as an extra input. The open-context theorem retains the explicit
native object and ordered proof-hypothesis assignments.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationCheckedCompilation
open Presentation Presentation.FormationSensitive
open Mettapedia.Logic HOL.Embedding.ZFSetHenkinInterpretation
open Mettapedia.Languages.Megalodon
open MathdataKernel HenkinTermInterpretation NativeProof
open SetOperationSignature (proofName)
open SetOperationExtensionalProfile (reading)
open SetOperationExtensionalOperations (operations)

variable (instances : List (HOL.Ty Base × HOL.Ty Base)) (fuel depth : Nat)
variable {gamma : HOL.Ctx Unit}
variable (assumptions : List (HOL.Formula Symbol gamma)) (goal : HOL.Formula Symbol gamma)
variable (program : Pf) (fragment : Fragment (SetOperationExtensionality.environment instances) depth program)
variable (accepted : checkProof (SetOperationExtensionality.environment instances) fuel depth
  ((gamma.map Mettapedia.Languages.Megalodon.SetOperationProofCompilation.type).map reifyType)
  (assumptions.map (fun formula => HOLNormalForms.normalFormCode
    (SetOperationExtensionality.term instances formula))) program
  (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true)

def compile {n : Nat} (objects : Sub Tower.Head gamma.length n)
    (hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n) : Tower.Tm n :=
  SetOperationProofCompilation.compile
    (SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted)
    objects hypotheses

include fragment accepted

theorem compile_typed {n : Nat} {context : Tower.Ctx n} {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (objectTyped : HOLNativeGenericProofCompiler.GenericTyping.Objects reading context objects)
    (hypothesisTyped : HOLNativeGenericProofCompiler.GenericTyping.Hypotheses reading operations context objects hypotheses) :
    Typing operations.target context
      (compile instances fuel depth assumptions goal program fragment accepted objects hypotheses)
      (FormationSensitiveHOLGenericProofFamily.proof proofName
        (subst objects (HOLImpredicativeRepresentation.translate reading goal))) :=
  SetOperationProofCompilation.compile_typed
    (SetOperationProofReconstruction.checkedSource instances fuel depth assumptions goal program fragment accepted)
    objectTyped hypothesisTyped

theorem compile_closed_typed (closed : gamma = []) (empty : assumptions = []) :
    ∃ native : Tower.Tm gamma.length,
      Typing operations.target (FormationSensitiveHOLInterface.context reading.types gamma) native
        (FormationSensitiveHOLGenericProofFamily.proof proofName
          (HOLImpredicativeRepresentation.translate reading goal)) := by
  subst gamma
  subst assumptions
  exact ⟨compile instances fuel depth [] goal program fragment accepted Fin.elim0 Fin.elim0,
    SetOperationProofCompilation.compile_closed_typed
      (SetOperationProofReconstruction.checkedSource instances fuel depth [] goal program fragment accepted)⟩

omit fragment accepted

def truthProgram : Tower.Tm 0 :=
  compile [] 2 0 [] .top SetOperationProofReconstructionControls.truthProgram
    SetOperationProofReconstructionControls.truth_fragment SetOperationProofReconstructionControls.truth_checked
    Fin.elim0 Fin.elim0

theorem truth_typed : Typing operations.target .nil truthProgram
    (FormationSensitiveHOLGenericProofFamily.proof proofName
      (HOLImpredicativeRepresentation.translate reading (HOL.Term.top : HOL.ClosedFormula Symbol))) :=
  SetOperationProofCompilation.compile_closed_typed
    (SetOperationProofReconstruction.checkedSource [] 2 0 [] .top
      SetOperationProofReconstructionControls.truthProgram
      SetOperationProofReconstructionControls.truth_fragment SetOperationProofReconstructionControls.truth_checked)

#print axioms compile
#print axioms compile_typed
#print axioms compile_closed_typed
#print axioms truth_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationCheckedCompilation

import Mettapedia.Languages.Megalodon.SetOperationProofReconstruction
import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation

/-!
# Source-reflection controls for the common Megalodon checking profile

Reconstruction retains the material signature and the exact assumptions. The
well-founded and hyperset source countermodels therefore exclude both sides
of the foundation and self-membership choices for every admitted native proof.
The two same-typed operation parameters also retain their different names.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.SetOperationProofReconstructionControls
open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open MathdataKernel HenkinTermInterpretation NativeProof
open SetOperationExtensionality
open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) (program : Pf)
variable (fragment : Fragment (environment instances) depth program)

def check (assumptions : List (ClosedFormula Symbol)) (goal : ClosedFormula Symbol) : Bool :=
  checkProof (environment instances) fuel depth []
    (assumptions.map (fun formula => HOLNormalForms.normalFormCode (term instances formula)))
    program (HOLTermEncoding.native (term instances goal))

include fragment

theorem setInduction_refused (presentation : HSet.Presentation.{u}) :
    check instances fuel depth program Embedding.HypersetHenkinInterpretation.operationTheory setInduction ≠ true := by
  intro accepted
  exact (Embedding.HypersetHenkinInterpretation.setInduction_independent presentation).1.false
    (SetOperationProofReconstruction.checkedSource instances fuel depth _ _ program fragment accepted)

theorem negatedSetInduction_refused (presentation : HSet.Presentation.{u}) :
    check instances fuel depth program Embedding.HypersetHenkinInterpretation.operationTheory (.not setInduction) ≠ true := by
  intro accepted
  exact (Embedding.HypersetHenkinInterpretation.setInduction_independent presentation).2.false
    (SetOperationProofReconstruction.checkedSource instances fuel depth _ _ program fragment accepted)

theorem selfMember_refused (presentation : HSet.Presentation.{u}) :
    check instances fuel depth program Embedding.HypersetHenkinInterpretation.operationTheory
      Embedding.HypersetHenkinInterpretation.selfMember ≠ true := by
  intro accepted
  exact (Embedding.HypersetHenkinInterpretation.selfMember_independent presentation).1.false
    (SetOperationProofReconstruction.checkedSource instances fuel depth _ _ program fragment accepted)

theorem negatedSelfMember_refused (presentation : HSet.Presentation.{u}) :
    check instances fuel depth program Embedding.HypersetHenkinInterpretation.operationTheory
      (.not Embedding.HypersetHenkinInterpretation.selfMember) ≠ true := by
  intro accepted
  exact (Embedding.HypersetHenkinInterpretation.selfMember_independent presentation).2.false
    (SetOperationProofReconstruction.checkedSource instances fuel depth _ _ program fragment accepted)

omit fragment

theorem same_type_distinct_operation_names :
    SetOperationProofCompilation.symbolName Symbol.union ≠ SetOperationProofCompilation.symbolName Symbol.power := by decide

theorem material_readback_retains_union :
    SetOperationProofReconstruction.materialConstant instances (symbol instances Symbol.union) = Symbol.union := rfl

theorem material_readback_retains_power :
    SetOperationProofReconstruction.materialConstant instances (symbol instances Symbol.power) = Symbol.power := rfl

def truthProgram : Pf := .termLam .prop (.proofLam (.db 0) (.hyp 0))

theorem truth_fragment : Fragment (environment []) 0 truthProgram :=
  .termLam (.proofLam rfl trivial (.hyp 0))

theorem truth_checked : checkProof (environment []) 2 0 [] [] truthProgram
    (HOLTermEncoding.native (term [] (Term.top : ClosedFormula Symbol))) = true := by
  have erased := HOLTermEncoding.native_erased (term [] (Term.top : ClosedFormula Symbol))
  have literal : HOLTermEncoding.native (term [] (Term.top : ClosedFormula Symbol)) =
      .all .prop (.imp (.db 0) (.db 0)) := (Option.some.inj erased).symm
  rw [literal]
  simp [checkProof, checkNormalizedProof, truthProgram, MathdataKernel.normalize,
    deltaNormalize_of_primitive _ (SetOperationProofReconstruction.opaqueTerms []),
    inferProof, inferTerm, Tp.plainWellFormed, Tm.normalize, Tm.normalizeOne]

def truthSource : ProofSyntax Symbol [] (Term.top : ClosedFormula Symbol) :=
  SetOperationProofReconstruction.checkedSource [] 2 0 [] .top truthProgram truth_fragment truth_checked

theorem truth_source_derivation : ExtDerivation Symbol [] (Term.top : ClosedFormula Symbol) :=
  SetOperationProofReconstruction.accepted_source [] 2 0 [] .top truthProgram truth_fragment truth_checked

#print axioms truth_source_derivation
#print axioms truth_checked
#print axioms setInduction_refused
#print axioms negatedSetInduction_refused
#print axioms selfMember_refused
#print axioms negatedSelfMember_refused
#print axioms same_type_distinct_operation_names
end Mettapedia.Languages.Megalodon.SetOperationProofReconstructionControls

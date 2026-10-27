import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateComputation
import Mettapedia.Logic.HOL.NaturalRecursionProofControls

/-!
# Nonconstant controls for the original natural eliminator reading

The source-order method negates its previous Boolean result. The actual
selected-recursion model validates the source commitments, the translated
zero equation and the translated successor equation. A forged zero conclusion
is refuted by that same model. Original open source rows are read at the
constructed operations and survive caller weakening.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation NativeNaturalVectorFamilies

def operations : Operations Unit HOL.NaturalRecursionProofControls.Const where
  number := HOL.NaturalRecursionProofControls.number
  result := .prop
  zero := HOL.NaturalRecursionProofControls.zero
  successor := HOL.NaturalRecursionProofControls.successor
  selection := HOL.NaturalRecursionProofControls.selection

def method : HOL.ClosedTerm HOL.NaturalRecursionProofControls.Const operations.methodType :=
  .lam (.lam (.not (.var .vz)))

def result (number : HOL.ClosedTerm HOL.NaturalRecursionProofControls.Const operations.number) :
    HOL.ClosedFormula HOL.NaturalRecursionProofControls.Const :=
  .app (.app (.app (.app operations.eliminator HOL.NaturalRecursionProofControls.family) HOL.NaturalRecursionProofControls.base) method) number

def zeroProof : HOL.ProofSyntax HOL.NaturalRecursionProofControls.Const []
    (.imp (HOL.SelectionProofs.principle HOL.NaturalRecursionProofControls.selection)
      (.imp (HOL.NaturalRecursionProofs.statement HOL.NaturalRecursionProofControls.zero HOL.NaturalRecursionProofControls.successor .prop)
        (.eq (result HOL.NaturalRecursionProofControls.zero) HOL.NaturalRecursionProofControls.base))) :=
  .impI (.impI (operations.zeroIota HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method (.hyp 1) (.hyp 0)))

def successorProof : HOL.ProofSyntax HOL.NaturalRecursionProofControls.Const []
    (.imp (HOL.SelectionProofs.principle HOL.NaturalRecursionProofControls.selection)
      (.imp (HOL.NaturalRecursionProofs.statement HOL.NaturalRecursionProofControls.zero HOL.NaturalRecursionProofControls.successor .prop)
        (.eq (result (.app HOL.NaturalRecursionProofControls.successor HOL.NaturalRecursionProofControls.zero))
          (.app (.app method HOL.NaturalRecursionProofControls.zero) (result HOL.NaturalRecursionProofControls.zero))))) :=
  .impI (.impI (operations.successorIota HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method HOL.NaturalRecursionProofControls.zero (.hyp 1) (.hyp 0)))

theorem zeroProof_free : zeroProof.FunctionExtensionalityFree := by
  simp only [zeroProof, HOL.ProofSyntax.FunctionExtensionalityFree]
  exact operations.zeroIota_free (Δ := [HOL.NaturalRecursionProofs.statement HOL.NaturalRecursionProofControls.zero HOL.NaturalRecursionProofControls.successor .prop, HOL.SelectionProofs.principle HOL.NaturalRecursionProofControls.selection]) HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method (.hyp 1) (.hyp 0) trivial trivial

theorem successorProof_free : successorProof.FunctionExtensionalityFree := by
  simp only [successorProof, HOL.ProofSyntax.FunctionExtensionalityFree]
  exact operations.successorIota_free (Δ := [HOL.NaturalRecursionProofs.statement HOL.NaturalRecursionProofControls.zero HOL.NaturalRecursionProofControls.successor .prop, HOL.SelectionProofs.principle HOL.NaturalRecursionProofControls.selection]) HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method HOL.NaturalRecursionProofControls.zero (.hyp 1) (.hyp 0) trivial trivial

theorem zero_equation : HOL.NaturalRecursionProofControls.model.models (.eq (result HOL.NaturalRecursionProofControls.zero) HOL.NaturalRecursionProofControls.base) := by
  have valid := HOL.Soundness.extTheorem_sound zeroProof.erase HOL.NaturalRecursionProofControls.model
    (HOL.NaturalRecursionProofControls.model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid HOL.NaturalRecursionProofControls.selection_holds HOL.NaturalRecursionProofControls.recursion_holds

theorem successor_equation : HOL.NaturalRecursionProofControls.model.models
    (.eq (result (.app HOL.NaturalRecursionProofControls.successor HOL.NaturalRecursionProofControls.zero))
      (.app (.app method HOL.NaturalRecursionProofControls.zero) (result HOL.NaturalRecursionProofControls.zero))) := by
  have valid := HOL.Soundness.extTheorem_sound successorProof.erase HOL.NaturalRecursionProofControls.model
    (HOL.NaturalRecursionProofControls.model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid HOL.NaturalRecursionProofControls.selection_holds HOL.NaturalRecursionProofControls.recursion_holds

theorem zero_false : ¬ HOL.NaturalRecursionProofControls.model.models (result HOL.NaturalRecursionProofControls.zero) :=
  fun holds => zero_equation.mp holds

theorem successor_true : HOL.NaturalRecursionProofControls.model.models (result (.app HOL.NaturalRecursionProofControls.successor HOL.NaturalRecursionProofControls.zero)) :=
  successor_equation.mpr zero_false

def typingProof : HOL.ProofSyntax HOL.NaturalRecursionProofControls.Const []
    (.imp (HOL.SelectionProofs.principle operations.selection)
      (.imp (HOL.NaturalRecursionProofs.statement operations.zero operations.successor operations.result)
        (.imp (HOL.NaturalRecursionProofs.inductionPrinciple operations.zero operations.successor)
          (.imp (HOL.NaturalRecursionProofs.holds HOL.NaturalRecursionProofControls.family operations.zero
            HOL.NaturalRecursionProofControls.base)
            (.imp (.app (operations.methodPredicate HOL.NaturalRecursionProofControls.family) method)
              (.app (operations.resultPredicate HOL.NaturalRecursionProofControls.family)
                (.app (.app (.app operations.eliminator HOL.NaturalRecursionProofControls.family)
                  HOL.NaturalRecursionProofControls.base) method))))))) :=
  .impI (.impI (.impI (.impI (.impI (operations.result_typed
    HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method
    (.hyp 4) (.hyp 3) (.hyp 2) (.hyp 1) (.hyp 0))))))

theorem method_guard_holds : HOL.NaturalRecursionProofControls.model.models
    (.app (operations.methodPredicate HOL.NaturalRecursionProofControls.family) method) := by
  intro index _ _ value _ previous
  exact not_congr previous

theorem original_result_typed : HOL.NaturalRecursionProofControls.model.models
    (.app (operations.resultPredicate HOL.NaturalRecursionProofControls.family)
      (.app (.app (.app operations.eliminator HOL.NaturalRecursionProofControls.family)
        HOL.NaturalRecursionProofControls.base) method)) := by
  have valid := HOL.Soundness.extTheorem_sound typingProof.erase HOL.NaturalRecursionProofControls.model
    (HOL.NaturalRecursionProofControls.model.functionsRespectEqv_of_fullDomains
      (HOL.HenkinModel.fullDomains_standard _ _))
  exact valid HOL.NaturalRecursionProofControls.selection_holds
    HOL.NaturalRecursionProofControls.recursion_holds HOL.NaturalRecursionProofControls.induction_holds
    HOL.NaturalRecursionProofControls.base_fits method_guard_holds

theorem false_method_guard_refused : ¬ HOL.NaturalRecursionProofControls.model.models
    (.app (operations.methodPredicate HOL.NaturalRecursionProofControls.falseFamily) method) := by
  intro valid
  exact valid (ULift.up 0) trivial trivial (ULift.up False) trivial (fun no => no) (fun no => no)

theorem false_result_guard_refused : ¬ HOL.NaturalRecursionProofControls.model.models
    (.app (operations.resultPredicate HOL.NaturalRecursionProofControls.falseFamily)
      (.app (.app (.app operations.eliminator HOL.NaturalRecursionProofControls.family)
        HOL.NaturalRecursionProofControls.base) method)) := by
  intro valid
  exact valid (ULift.up 1) trivial trivial successor_true

theorem typingProof_free : typingProof.FunctionExtensionalityFree := by
  simp only [typingProof, HOL.ProofSyntax.FunctionExtensionalityFree]
  exact operations.result_typed_free
    (Δ := [.app (operations.methodPredicate HOL.NaturalRecursionProofControls.family) method,
      HOL.NaturalRecursionProofs.holds HOL.NaturalRecursionProofControls.family operations.zero
        HOL.NaturalRecursionProofControls.base,
      HOL.NaturalRecursionProofs.inductionPrinciple operations.zero operations.successor,
      HOL.NaturalRecursionProofs.statement operations.zero operations.successor operations.result,
      HOL.SelectionProofs.principle operations.selection])
    HOL.NaturalRecursionProofControls.family HOL.NaturalRecursionProofControls.base method
    (.hyp 4) (.hyp 3) (.hyp 2) (.hyp 1) (.hyp 0) trivial trivial trivial trivial trivial

theorem forged_zero_refused : ¬ HOL.ExtDerivation.Theorem HOL.NaturalRecursionProofControls.Const
    (.imp (HOL.SelectionProofs.principle HOL.NaturalRecursionProofControls.selection)
      (.imp (HOL.NaturalRecursionProofs.statement HOL.NaturalRecursionProofControls.zero HOL.NaturalRecursionProofControls.successor .prop)
        (.eq (result HOL.NaturalRecursionProofControls.zero) .top))) := by
  intro proved
  have valid := HOL.Soundness.extTheorem_sound proved HOL.NaturalRecursionProofControls.model
    (HOL.NaturalRecursionProofControls.model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
  exact zero_false ((valid HOL.NaturalRecursionProofControls.selection_holds HOL.NaturalRecursionProofControls.recursion_holds).mpr trivial)

theorem original_type_read : Reads operations (Γ := []) natEliminateType operations.eliminatorCode :=
  operations.eliminatorCode_reads

theorem original_zero_read : Reads operations (Γ := operations.parameters) natZeroIotaLeft operations.zeroLeft :=
  operations.zeroLeft_reads

theorem original_successor_read : Reads operations (Γ := operations.successorParameters)
    natSuccIotaRight operations.successorRight :=
  operations.successorRight_reads

theorem weakened_zero_read : Reads operations (Γ := operations.successorParameters)
    (Presentation.rename wk natZeroIotaLeft) (HOL.weaken operations.zeroLeft) :=
  operations.zeroLeft_reads.rename HOL.Rename.weaken wk (fun _ => rfl)

theorem substituted_zero_read : Reads operations (Γ := operations.successorParameters)
    (Presentation.subst projection natZeroIotaLeft)
    (HOL.subst (HOL.Subst.ofRename HOL.Rename.weaken) operations.zeroLeft) := by
  apply operations.zeroLeft_reads.substitute
  intro type index
  simpa only [projection, renSub, wk, FormationSensitiveHOLInterface.variableIndex, HOL.Subst.ofRename,
    HOL.Rename.weaken] using
    (Reads.var (operations := operations) (Γ := operations.successorParameters) (.vs index))

#print axioms zeroProof_free
#print axioms method_guard_holds
#print axioms original_result_typed
#print axioms false_method_guard_refused
#print axioms false_result_guard_refused
#print axioms typingProof_free
#print axioms successorProof_free
#print axioms zero_false
#print axioms successor_true
#print axioms forged_zero_refused
#print axioms original_type_read
#print axioms weakened_zero_read
#print axioms substituted_zero_read

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.Controls

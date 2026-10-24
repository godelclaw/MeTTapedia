import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationProofCompilerSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.SetOperationMaterialSemantics
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# Compiled dependent proofs in the material graph interpretations

The compiler's actual proof-family denotations instantiate in the four common
material models. The set and hyperset graph evaluators independently determine
the separated singleton proof codes. A pointwise equivalence maps the actual
denoted proof sections into those codes, and interpretation commutes with
source substitution. This observation forgets retained proof presentation;
it does not identify the native terms or membership relations of the models.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
noncomputable section

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMaterialProofSemantics
open Presentation
open Mettapedia.Logic HOL.Embedding
open ZFSetHenkinInterpretation (Symbol)
open ZFSetDependentProducts (Elements)
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HOLNativeGenericProofCompiler HenkinFamilySemantics
open SetOperationExtensionalProfile (reading)
universe u s

def truthElementsEquiv (formula : Prop) :
    ULift.{s,0} (PLift formula) ≃ Elements (ZFSetTraceProofDecoding.truthCode.{u} formula) where
  toFun proof := ⟨∅, (ZFSetTraceProofDecoding.mem_truthCode _ _).mpr ⟨rfl, proof.down.down⟩⟩
  invFun value := ULift.up ⟨((ZFSetTraceProofDecoding.mem_truthCode _ _).mp value.2).2⟩
  left_inv _ := @Subsingleton.elim (ULift.{s,0} (PLift formula)) inferInstance _ _
  right_inv value := Subtype.ext ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp value.2).1.symm

def setGraphProofCode {gamma : HOL.Ctx Unit} (formula : HOL.Formula Symbol gamma)
    (valuation : ZFSetHenkinInterpretation.model.{u}.Valuation gamma) : ZFSet.{u} :=
  ZFSetTraceProofDecoding.truthCode ((SetOperationMaterialSemantics.setGraphMeaning formula valuation).down)

def hypersetGraphProofCode (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (formula : HOL.Formula Symbol gamma)
    (valuation : (HypersetHenkinInterpretation.model presentation).Valuation gamma) : ZFSet.{u} :=
  ZFSetTraceProofDecoding.truthCode
    ((SetOperationMaterialSemantics.hypersetGraphMeaning presentation formula valuation).down)

def wellFoundedGraphProofCode (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (formula : HOL.Formula Symbol gamma)
    (valuation : (WellFoundedHypersetInterpretation.model presentation).Valuation gamma) : ZFSet.{u} :=
  setGraphProofCode formula (HOL.StandardTransport.valuationEquiv
    (WellFoundedHypersetInterpretation.model presentation) ZFSetHenkinInterpretation.model
    WellFoundedHypersetInterpretation.baseEquiv gamma valuation)

def codedGraphProofCode (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (formula : HOL.Formula Symbol gamma)
    (valuation : (CodedHypersetInterpretation.model presentation).Valuation gamma) : ZFSet.{u} :=
  hypersetGraphProofCode presentation formula (HOL.StandardTransport.valuationEquiv
    (CodedHypersetInterpretation.model presentation) (HypersetHenkinInterpretation.model presentation)
    CodedHypersetInterpretation.baseEquiv gamma valuation)

theorem wellFounded_proof_code_square (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (formula : HOL.Formula Symbol gamma)
    (valuation : (WellFoundedHypersetInterpretation.model presentation).Valuation gamma) :
    wellFoundedGraphProofCode presentation formula valuation = ZFSetTraceProofDecoding.truthCode
      (((WellFoundedHypersetInterpretation.model presentation).denote formula valuation).down) := by
  apply congrArg ZFSetTraceProofDecoding.truthCode
  have compared := congrArg ULift.down (SetOperationMaterialSemantics.wellFounded_graph_square
    presentation formula valuation)
  exact compared.trans (by rfl)

theorem coded_proof_code_square (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (formula : HOL.Formula Symbol gamma)
    (valuation : (CodedHypersetInterpretation.model presentation).Valuation gamma) :
    codedGraphProofCode presentation formula valuation = ZFSetTraceProofDecoding.truthCode
      (((CodedHypersetInterpretation.model presentation).denote formula valuation).down) := by
  apply congrArg ZFSetTraceProofDecoding.truthCode
  have compared := congrArg ULift.down (SetOperationMaterialSemantics.coded_graph_square
    presentation formula valuation)
  exact compared.trans (by rfl)

def setProofEquiv {gamma : HOL.Ctx Unit} {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : State reading ZFSetHenkinInterpretation.model.{u} objects)
    (formula : HOL.Formula Symbol gamma) (environment : state.context.Environment) :
    truthFamily (formulaMeaning state formula) environment ≃
      Elements (setGraphProofCode formula (state.valuation environment)) := by
  have agreement := congrFun (SetOperationMaterialSemantics.setGraphMeaning_eq.{u} formula)
    (state.valuation environment)
  exact (iffProofEquiv (Iff.of_eq (congrArg ULift.down agreement.symm))).trans (truthElementsEquiv _)

def hypersetProofEquiv (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State reading (HypersetHenkinInterpretation.model presentation) objects)
    (formula : HOL.Formula Symbol gamma) (environment : state.context.Environment) :
    truthFamily (formulaMeaning state formula) environment ≃
      Elements (hypersetGraphProofCode presentation formula (state.valuation environment)) := by
  have agreement := congrFun (SetOperationMaterialSemantics.hypersetGraphMeaning_eq presentation formula)
    (state.valuation environment)
  exact (iffProofEquiv (Iff.of_eq (congrArg ULift.down agreement.symm))).trans (truthElementsEquiv _)

def wellFoundedProofEquiv (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State reading (WellFoundedHypersetInterpretation.model presentation) objects)
    (formula : HOL.Formula Symbol gamma) (environment : state.context.Environment) :
    truthFamily (formulaMeaning state formula) environment ≃
      Elements (wellFoundedGraphProofCode presentation formula (state.valuation environment)) := by
  rw [wellFounded_proof_code_square]
  exact truthElementsEquiv _

def codedProofEquiv (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State reading (CodedHypersetInterpretation.model presentation) objects)
    (formula : HOL.Formula Symbol gamma) (environment : state.context.Environment) :
    truthFamily (formulaMeaning state formula) environment ≃
      Elements (codedGraphProofCode presentation formula (state.valuation environment)) := by
  rw [coded_proof_code_square]
  exact truthElementsEquiv _

def setProofReadout {gamma : HOL.Ctx Unit} {n : Nat} {objects : Sub Tower.Head gamma.length n}
    (state : State reading ZFSetHenkinInterpretation.model.{u} objects) (formula : HOL.Formula Symbol gamma)
    (value : Section (truthFamily (formulaMeaning state formula))) :
    (environment : state.context.Environment) → Elements (setGraphProofCode formula (state.valuation environment)) :=
  fun environment => setProofEquiv state formula environment (value environment)

def hypersetProofReadout (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit} {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    (state : State reading (HypersetHenkinInterpretation.model presentation) objects)
    (formula : HOL.Formula Symbol gamma) (value : Section (truthFamily (formulaMeaning state formula))) :
    (environment : state.context.Environment) →
      Elements (hypersetGraphProofCode presentation formula (state.valuation environment)) :=
  fun environment => hypersetProofEquiv presentation state formula environment (value environment)

theorem setGraphProofCode_substitution {gamma delta : HOL.Ctx Unit}
    (substitution : HOL.Subst Symbol gamma delta) (formula : HOL.Formula Symbol gamma)
    (valuation : ZFSetHenkinInterpretation.model.{u}.Valuation delta) :
    setGraphProofCode (HOL.subst substitution formula) valuation =
      setGraphProofCode formula (HOL.Soundness.substVal ZFSetHenkinInterpretation.model substitution valuation) := by
  simp only [setGraphProofCode, SetOperationMaterialSemantics.setGraphMeaning_eq, HOL.Soundness.denote_subst]

theorem hypersetGraphProofCode_substitution (presentation : HSet.Presentation.{u}) {gamma delta : HOL.Ctx Unit}
    (substitution : HOL.Subst Symbol gamma delta) (formula : HOL.Formula Symbol gamma)
    (valuation : (HypersetHenkinInterpretation.model presentation).Valuation delta) :
    hypersetGraphProofCode presentation (HOL.subst substitution formula) valuation =
      hypersetGraphProofCode presentation formula
        (HOL.Soundness.substVal (HypersetHenkinInterpretation.model presentation) substitution valuation) := by
  simp only [hypersetGraphProofCode, SetOperationMaterialSemantics.hypersetGraphMeaning_eq, HOL.Soundness.denote_subst]

theorem setGraphProofCode_implication {gamma : HOL.Ctx Unit}
    (left right : HOL.Formula Symbol gamma) :
    (fun valuation : ZFSetHenkinInterpretation.model.{u}.Valuation gamma =>
      setGraphProofCode (.imp left right) valuation) =
      ZFSetTraceContextual.piFamily
        (fun valuation : ZFSetHenkinInterpretation.model.{u}.Valuation gamma => setGraphProofCode left valuation)
        (fun point => setGraphProofCode right (fun {_} index => point.1 index)) := by
  calc
    _ = ZFSetTraceProofDecoding.truthFamily.{u}
        (fun valuation : ZFSetHenkinInterpretation.model.{u}.Valuation gamma =>
          (SetOperationMaterialSemantics.setGraphMeaning left valuation).down →
          (SetOperationMaterialSemantics.setGraphMeaning right valuation).down) := by
      funext valuation
      simp only [ZFSetTraceProofDecoding.truthFamily, setGraphProofCode,
        SetOperationMaterialSemantics.setGraphMeaning_eq]
      rfl
    _ = _ := ZFSetTraceProofDecoding.implication_decoder.{u} _ _

theorem hypersetGraphProofCode_implication (presentation : HSet.Presentation.{u}) {gamma : HOL.Ctx Unit}
    (left right : HOL.Formula Symbol gamma) :
    (fun valuation : (HypersetHenkinInterpretation.model presentation).Valuation gamma =>
      hypersetGraphProofCode presentation (.imp left right) valuation) =
      ZFSetTraceContextual.piFamily
        (fun valuation : (HypersetHenkinInterpretation.model presentation).Valuation gamma =>
          hypersetGraphProofCode presentation left valuation)
        (fun point => hypersetGraphProofCode presentation right (fun {_} index => point.1 index)) := by
  calc
    _ = ZFSetTraceProofDecoding.truthFamily.{u}
        (fun valuation : (HypersetHenkinInterpretation.model presentation).Valuation gamma =>
          (SetOperationMaterialSemantics.hypersetGraphMeaning presentation left valuation).down →
          (SetOperationMaterialSemantics.hypersetGraphMeaning presentation right valuation).down) := by
      funext valuation
      simp only [ZFSetTraceProofDecoding.truthFamily, hypersetGraphProofCode,
        SetOperationMaterialSemantics.hypersetGraphMeaning_eq]
      rfl
    _ = _ := ZFSetTraceProofDecoding.implication_decoder.{u} _ _

theorem sets_compile_proves {gamma : HOL.Ctx Unit} {assumptions : List (HOL.Formula Symbol gamma)}
    {goal : HOL.Formula Symbol gamma} (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading ZFSetHenkinInterpretation.model.{u} objects)
    (meanings : GenericSemantics.Hypotheses
      (SetOperationProofCompilerSemantics.algebra _ ZFSetHenkinInterpretation.fullDomains) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state goal)),
      SetOperationProofFamilySemantics.Denotes ZFSetHenkinInterpretation.model state.context
        (SetOperationProofCompilation.compile source objects hypotheses)
        (truthFamily (formulaMeaning state goal)) value ∧
      ∀ environment, (setProofReadout state goal value environment).1 = ∅ := by
  obtain ⟨value, meaning⟩ := SetOperationProofCompilerSemantics.compile_proves
    _ ZFSetHenkinInterpretation.fullDomains source state meanings
  refine ⟨value, meaning, ?_⟩
  intro environment
  exact ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp
    (setProofReadout state goal value environment).2).1

theorem hypersets_compile_proves (presentation : HSet.Presentation.{u})
    {gamma : HOL.Ctx Unit} {assumptions : List (HOL.Formula Symbol gamma)}
    {goal : HOL.Formula Symbol gamma} (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (HypersetHenkinInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (HypersetHenkinInterpretation.fullDomains presentation)) state hypotheses) :
    ∃ value : Section (truthFamily (formulaMeaning state goal)),
      SetOperationProofFamilySemantics.Denotes (HypersetHenkinInterpretation.model presentation) state.context
        (SetOperationProofCompilation.compile source objects hypotheses)
        (truthFamily (formulaMeaning state goal)) value ∧
      ∀ environment, (hypersetProofReadout presentation state goal value environment).1 = ∅ := by
  obtain ⟨value, meaning⟩ := SetOperationProofCompilerSemantics.compile_proves
    _ (HypersetHenkinInterpretation.fullDomains presentation) source state meanings
  refine ⟨value, meaning, ?_⟩
  intro environment
  exact ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp
    (hypersetProofReadout presentation state goal value environment).2).1

theorem wellFounded_compile_proves (presentation : HSet.Presentation.{u})
    {gamma : HOL.Ctx Unit} {assumptions : List (HOL.Formula Symbol gamma)}
    {goal : HOL.Formula Symbol gamma} (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (WellFoundedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (WellFoundedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (WellFoundedHypersetInterpretation.model presentation) state
      (SetOperationProofCompilation.compile source objects hypotheses) goal :=
  SetOperationProofCompilerSemantics.compile_proves _ (WellFoundedHypersetInterpretation.fullDomains presentation)
    source state meanings

theorem codes_compile_proves (presentation : HSet.Presentation.{u})
    {gamma : HOL.Ctx Unit} {assumptions : List (HOL.Formula Symbol gamma)}
    {goal : HOL.Formula Symbol gamma} (source : HOL.ProofSyntax Symbol assumptions goal) {n : Nat}
    {objects : Sub Tower.Head gamma.length n}
    {hypotheses : Fin (assumptions.map HOL.ImpredicativeConnectives.expand).length → Tower.Tm n}
    (state : State reading (CodedHypersetInterpretation.model presentation) objects)
    (meanings : GenericSemantics.Hypotheses (SetOperationProofCompilerSemantics.algebra _
      (CodedHypersetInterpretation.fullDomains presentation)) state hypotheses) :
    SetOperationProofFamilySemantics.Proves (CodedHypersetInterpretation.model presentation) state
      (SetOperationProofCompilation.compile source objects hypotheses) goal :=
  SetOperationProofCompilerSemantics.compile_proves _ (CodedHypersetInterpretation.fullDomains presentation)
    source state meanings

theorem distinct_programs_same_material_reading :
    let state := SetOperationProofCompilerSemantics.emptyState ZFSetHenkinInterpretation.model.{u}
    let formula : HOL.ClosedFormula Symbol := .eq .top .top
    ∃ first second : Section (truthFamily (formulaMeaning state formula)),
      SetOperationProofFamilySemantics.Denotes ZFSetHenkinInterpretation.model state.context
        SetOperationProofCompilation.extensionalTruthProgram _ first ∧
      SetOperationProofFamilySemantics.Denotes ZFSetHenkinInterpretation.model state.context
        HOLPredicateEqualityDerived.reflTerm _ second ∧
      (∀ environment, setProofReadout state formula first environment =
        setProofReadout state formula second environment) ∧
      SetOperationProofCompilation.extensionalTruthProgram ≠ HOLPredicateEqualityDerived.reflTerm := by
  dsimp only
  obtain ⟨first, firstMeaning⟩ := SetOperationProofCompilerSemantics.extensionalTruth_hasMeaning
    ZFSetHenkinInterpretation.model ZFSetHenkinInterpretation.fullDomains
  obtain ⟨second, secondMeaning⟩ := SetOperationProofCompilerSemantics.compile_closed_proves
    ZFSetHenkinInterpretation.model ZFSetHenkinInterpretation.fullDomains SetOperationPredicateProofs.reflexiveTruth
  refine ⟨first, second, firstMeaning, secondMeaning, ?_, ?_⟩
  · intro environment
    apply Subtype.ext
    exact ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp
      (setProofReadout _ _ first environment).2).1.trans
      ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp
        (setProofReadout _ _ second environment).2).1.symm
  · decide

def setsAlgebra : GenericSemantics.Algebra reading SetOperationSignature.proofName
    SetOperationExtensionalOperations.operations :=
  SetOperationProofCompilerSemantics.algebra ZFSetHenkinInterpretation.model.{u}
    ZFSetHenkinInterpretation.fullDomains

theorem sets_compiled_extensionalTruth :
    SetOperationProofFamilySemantics.Proves ZFSetHenkinInterpretation.model.{u}
      (SetOperationProofCompilerSemantics.emptyState ZFSetHenkinInterpretation.model)
      (SetOperationProofCompilation.compile SetOperationPredicateProofs.extensionalTruth Fin.elim0 Fin.elim0)
      (HOL.Term.eq .top .top : HOL.ClosedFormula Symbol) := by
  apply SetOperationProofCompilerSemantics.compile_proves
    ZFSetHenkinInterpretation.model ZFSetHenkinInterpretation.fullDomains
    SetOperationPredicateProofs.extensionalTruth (SetOperationProofCompilerSemantics.emptyState _)
  intro index
  nomatch index

#print axioms truthElementsEquiv
#print axioms setProofEquiv
#print axioms hypersetProofEquiv
#print axioms sets_compile_proves
#print axioms hypersets_compile_proves
#print axioms wellFounded_compile_proves
#print axioms codes_compile_proves
#print axioms wellFounded_proof_code_square
#print axioms coded_proof_code_square
#print axioms distinct_programs_same_material_reading
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.SetOperationMaterialProofSemantics

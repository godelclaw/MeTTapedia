import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplication
import Mettapedia.GSLT.LanguageDef.InferenceRuleSupport

/-!
# Exact dependency reuse for open rule programs

Reuse consults complete rule lookup results and the cited premise positions.
Absence is a dependency too. The result preserves the actual Boolean verdict,
including a refusal, while retaining the same raw proof. This is a sufficient
syntactic dependency set; it does not assert minimality or validate a source
language's ambient telescope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceRuleSupport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

mutual
  def openRuleSupport : RawOpenProof → List RuleId
    | .premise _ => []
    | .node instantiation children => instantiation.ruleId :: openChildrenSupport children
  def openChildrenSupport : List RawOpenProof → List RuleId
    | [] => []
    | first :: rest => openRuleSupport first ++ openChildrenSupport rest
end

mutual
  def premiseSupport : RawOpenProof → List Nat
    | .premise index => [index]
    | .node _ children => premiseChildrenSupport children
  def premiseChildrenSupport : List RawOpenProof → List Nat
    | [] => []
    | first :: rest => premiseSupport first ++ premiseChildrenSupport rest
end

def ContextAgreement (source target : List Pattern) (positions : List Nat) : Prop :=
  ∀ index ∈ positions, target[index]? = source[index]?

def contextAgreementCheck (source target : List Pattern) (positions : List Nat) : Bool :=
  positions.all fun index => decide (target[index]? = source[index]?)

@[simp] theorem contextAgreementCheck_iff (source target : List Pattern) (positions : List Nat) :
    contextAgreementCheck source target positions = true ↔ ContextAgreement source target positions := by
  simp [contextAgreementCheck, ContextAgreement]

mutual
  theorem checkOpenRaw_eq_of_agreement
      {source target : ValidatedCalculusLanguageDef} {sourceContext targetContext : List Pattern}
      (goal : Pattern) (proof : RawOpenProof)
      (rules : Agreement source target (openRuleSupport proof))
      (context : ContextAgreement sourceContext targetContext (premiseSupport proof)) :
      checkOpenRaw target targetContext goal proof = checkOpenRaw source sourceContext goal proof := by
    cases proof with
    | premise index =>
        simp only [checkOpenRaw, context index (by simp [premiseSupport])]
    | node instantiation children =>
        have same := instantiateRule_eq_of_lookup instantiation
          (rules instantiation.ruleId (by simp [openRuleSupport]))
        simp only [checkOpenRaw, same]
        cases instantiateRule? source instantiation with
        | none => rfl
        | some result =>
            rcases result with ⟨premises, conclusion⟩
            dsimp only
            rw [checkOpenRawChildren_eq_of_agreement premises children
              (fun id member => rules id (by simp [openRuleSupport, member])) context]
  termination_by sizeOf proof

  theorem checkOpenRawChildren_eq_of_agreement
      {source target : ValidatedCalculusLanguageDef} {sourceContext targetContext : List Pattern}
      (goals : List Pattern) (proofs : List RawOpenProof)
      (rules : Agreement source target (openChildrenSupport proofs))
      (context : ContextAgreement sourceContext targetContext (premiseChildrenSupport proofs)) :
      checkOpenRawChildren target targetContext goals proofs =
        checkOpenRawChildren source sourceContext goals proofs := by
    cases goals with
    | nil => cases proofs <;> simp only [checkOpenRawChildren]
    | cons goal goals =>
        cases proofs with
        | nil => simp only [checkOpenRawChildren]
        | cons proof proofs =>
            simp only [checkOpenRawChildren]
            rw [checkOpenRaw_eq_of_agreement goal proof
              (fun id member => rules id (by simp [openChildrenSupport, member]))
              (fun index member => context index (by simp [premiseChildrenSupport, member]))]
            rw [checkOpenRawChildren_eq_of_agreement goals proofs
              (fun id member => rules id (by simp [openChildrenSupport, member]))
              (fun index member => context index (by simp [premiseChildrenSupport, member]))]
  termination_by sizeOf proofs
  decreasing_by all_goals simp_all <;> omega
end

/-- Safe reuse returns the identical rule program, under the updated context.
The caller must independently retain any source-specific formation obligations. -/
def reuseCheckedOpenProof {source target : ValidatedCalculusLanguageDef}
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (proof : {p : RawOpenProof // checkOpenRaw source sourceContext goal p = true})
    (rules : agreementCheck source target (openRuleSupport proof.1) = true)
    (context : contextAgreementCheck sourceContext targetContext (premiseSupport proof.1) = true) :
    {p : RawOpenProof // checkOpenRaw target targetContext goal p = true} :=
  ⟨proof.1, (checkOpenRaw_eq_of_agreement goal proof.1
    ((agreementCheck_iff _ _ _).mp rules)
    ((contextAgreementCheck_iff _ _ _).mp context)).trans proof.2⟩

theorem applyOpen?_eq_of_agreement
    {source target : ValidatedCalculusLanguageDef} {premises sourceContext targetContext : List Pattern}
    (goal : Pattern) (program : RawOpenProof) (arguments : List RawOpenProof)
    (rules : Agreement source target (openRuleSupport program ++ openChildrenSupport arguments))
    (context : ContextAgreement sourceContext targetContext (premiseChildrenSupport arguments)) :
    applyOpen? target premises targetContext goal program arguments =
      applyOpen? source premises sourceContext goal program arguments := by
  unfold applyOpen?
  rw [checkOpenRaw_eq_of_agreement goal program
    (fun id member => rules id (List.mem_append_left _ member)) (fun _ _ => rfl)]
  rw [checkOpenRawChildren_eq_of_agreement premises arguments
    (fun id member => rules id (List.mem_append_right _ member)) context]

/-- A negative cache entry cannot ignore an absent premise lookup. -/
theorem absent_premise_changes_verdict (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    checkOpenRaw definition [] goal (.premise 0) = false ∧
      checkOpenRaw definition [goal] goal (.premise 0) = true ∧
        contextAgreementCheck [] [goal] (premiseSupport (.premise 0)) = false := by
  simp [checkOpenRaw, contextAgreementCheck, premiseSupport]

/-- Dependencies retain repeated citations, just as the proof does. -/
theorem repeated_premise_dependencies (instantiation : RuleInstance) :
    premiseSupport (.node instantiation [.premise 1, .premise 1, .premise 0]) = [1, 1, 0] := rfl

#print axioms checkOpenRaw_eq_of_agreement
#print axioms applyOpen?_eq_of_agreement
#print axioms absent_premise_changes_verdict

end Mettapedia.GSLT.LanguageDef.InferenceRuleSupport

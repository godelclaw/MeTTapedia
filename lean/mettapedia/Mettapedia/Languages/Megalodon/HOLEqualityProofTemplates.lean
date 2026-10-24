import Mettapedia.Languages.Megalodon.HOLProofInference
import Mettapedia.Languages.Megalodon.RelationEqualityProofs

/-!
# Typed HOL schemas for native binary-relation equality proofs

Each formula uses primitive source equality. Its canonical encoding is the
exact statement inferred for the existing native proof combinator. Equality
conversion, its elimination rules, and both application congruences therefore
reuse actual proof programs without adding extensionality assumptions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLEqualityProofTemplates

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base}

def reflexivityFormula (type : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := type) (.eq (.var .vz) (.var .vz))

theorem reflexivity_code (type : Ty Base) :
    normalFormCode (reflexivityFormula type (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.reflexivityStatement (reifyType type) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [reflexivityFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.reflexivityStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem reflexivity_infers (depth : Nat) (type : Ty Base)
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.reflexivity (reifyType type))
      (reflexivityFormula type) := by
  refine ⟨32, ?_⟩
  rw [reflexivity_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.reflexivity_infers environment depth (reifyType type) typeFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms reflexivity_code
#print axioms reflexivity_infers

def symmetryFormula (type : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := type) (.all (σ := type)
    (.imp (.eq (.var (.vs .vz)) (.var .vz)) (.eq (.var .vz) (.var (.vs .vz)))))

theorem symmetry_code (type : Ty Base) :
    normalFormCode (symmetryFormula type (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.symmetryStatement (reifyType type) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [symmetryFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.symmetryStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem symmetry_infers (depth : Nat) (type : Ty Base)
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.symmetry (reifyType type))
      (symmetryFormula type) := by
  refine ⟨32, ?_⟩
  rw [symmetry_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.symmetry_infers environment depth (reifyType type) typeFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms symmetry_code
#print axioms symmetry_infers

def substitutionFormula (type : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := type) (.all (σ := type) (.all (σ := type ⇒ .prop)
    (.imp (.eq (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.imp (.app (.var .vz) (.var (.vs (.vs .vz))))
        (.app (.var .vz) (.var (.vs .vz)))))))

theorem substitution_code (type : Ty Base) :
    normalFormCode (substitutionFormula type (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.substitutionStatement (reifyType type) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [substitutionFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.substitutionStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem substitution_infers (depth : Nat) (type : Ty Base)
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.substitution (reifyType type))
      (substitutionFormula type) := by
  refine ⟨32, ?_⟩
  rw [substitution_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.substitution_infers environment depth (reifyType type) typeFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms substitution_code
#print axioms substitution_infers

def transitivityFormula (type : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := type) (.all (σ := type) (.all (σ := type)
    (.imp (.eq (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.imp (.eq (.var (.vs .vz)) (.var .vz))
        (.eq (.var (.vs (.vs .vz))) (.var .vz))))))

theorem transitivity_code (type : Ty Base) :
    normalFormCode (transitivityFormula type (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.transitivityStatement (reifyType type) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [transitivityFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.transitivityStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem transitivity_infers (depth : Nat) (type : Ty Base)
    (typeFormed : (reifyType type).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.transitivity (reifyType type))
      (transitivityFormula type) := by
  refine ⟨32, ?_⟩
  rw [transitivity_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.transitivity_infers environment depth (reifyType type) typeFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms transitivity_code
#print axioms transitivity_infers

def functionCongruenceFormula (domain result : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := domain ⇒ result) (.all (σ := domain ⇒ result) (.all (σ := domain)
    (.imp (.eq (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.eq (.app (.var (.vs (.vs .vz))) (.var .vz))
        (.app (.var (.vs .vz)) (.var .vz))))))

theorem functionCongruence_code (domain result : Ty Base) :
    normalFormCode (functionCongruenceFormula domain result (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.functionCongruenceStatement (reifyType domain) (reifyType result) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [functionCongruenceFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.functionCongruenceStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem functionCongruence_infers (depth : Nat) (domain result : Ty Base)
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (resultFormed : (reifyType result).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.functionCongruence (reifyType domain) (reifyType result))
      (functionCongruenceFormula domain result) := by
  refine ⟨32, ?_⟩
  rw [functionCongruence_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.functionCongruence_infers environment depth (reifyType domain) (reifyType result) domainFormed resultFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms functionCongruence_code
#print axioms functionCongruence_infers

def argumentCongruenceFormula (domain result : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := domain ⇒ result) (.all (σ := domain) (.all (σ := domain)
    (.imp (.eq (.var (.vs .vz)) (.var .vz))
      (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

theorem argumentCongruence_code (domain result : Ty Base) :
    normalFormCode (argumentCongruenceFormula domain result (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.argumentCongruenceStatement (reifyType domain) (reifyType result) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [argumentCongruenceFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.argumentCongruenceStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem argumentCongruence_infers (depth : Nat) (domain result : Ty Base)
    (domainFormed : (reifyType domain).plainWellFormed depth = true)
    (resultFormed : (reifyType result).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.argumentCongruence (reifyType domain) (reifyType result))
      (argumentCongruenceFormula domain result) := by
  refine ⟨32, ?_⟩
  rw [argumentCongruence_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.argumentCongruence_infers environment depth (reifyType domain) (reifyType result) domainFormed resultFormed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms argumentCongruence_code
#print axioms argumentCongruence_infers

def propositionEliminationFormula : Formula (Constant environment) gamma :=
  .all (σ := .prop) (.all (σ := .prop)
    (.imp (.eq (.var (.vs .vz)) (.var .vz)) (.imp (.var (.vs .vz)) (.var .vz))))

theorem propositionElimination_code :
    normalFormCode (propositionEliminationFormula (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.propositionEliminationStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [propositionEliminationFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.propositionEliminationStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem propositionElimination_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.propositionElimination)
      (propositionEliminationFormula) := by
  refine ⟨32, ?_⟩
  rw [propositionElimination_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.propositionElimination_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms propositionElimination_code
#print axioms propositionElimination_infers

def propositionEliminationReverseFormula : Formula (Constant environment) gamma :=
  .all (σ := .prop) (.all (σ := .prop)
    (.imp (.eq (.var (.vs .vz)) (.var .vz)) (.imp (.var .vz) (.var (.vs .vz)))))

theorem propositionEliminationReverse_code :
    normalFormCode (propositionEliminationReverseFormula (environment := environment) (gamma := gamma)) =
      RelationEqualityProofs.propositionEliminationReverseStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [propositionEliminationReverseFormula, native, encode, expandEquality,
    HenkinEqualityInterpretation.equalityFormula, HenkinEqualityInterpretation.equality,
    ImpredicativeConnectives.expandInline,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt,
    RelationEqualityProofs.propositionEliminationReverseStatement, RelationEqualityProofs.equality,
    RelationEqualityProofs.relationType, RelationEqualityProofs.relationApply]

theorem propositionEliminationReverse_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (RelationEqualityProofs.propositionEliminationReverse)
      (propositionEliminationReverseFormula) := by
  refine ⟨32, ?_⟩
  rw [propositionEliminationReverse_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (RelationEqualityProofs.propositionEliminationReverse_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms propositionEliminationReverse_code
#print axioms propositionEliminationReverse_infers

end Mettapedia.Languages.Megalodon.HOLEqualityProofTemplates

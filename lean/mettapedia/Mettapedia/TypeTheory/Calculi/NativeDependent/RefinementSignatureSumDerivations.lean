import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumCoherence

/-!
# Complete derivation transport into a joined native signature

The earned local-rule comparison constructs genuine translations of the
independently generated derivation trees. Premise positions are kept in order;
the inclusions neither duplicate nor discard a premise occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum

open Mettapedia.TypeTheory

universe u
variable {S T : Symbols.{u}} (left : Signature S) (right : Signature T)

theorem ruleLeft_premise_length (rule : RuleCode left) :
    (ruleLeft (right := right) rule).premises.length = rule.premises.length := by
  rw [ruleLeft_premises, List.length_map]

def premiseLeft (rule : RuleCode left)
    (position : Fin (ruleLeft (right := right) rule).premises.length) :
    Fin rule.premises.length := Fin.cast (ruleLeft_premise_length left right rule) position

theorem premiseLeft_value (rule : RuleCode left)
    (position : Fin (ruleLeft (right := right) rule).premises.length) :
    (premiseLeft left right rule position).val = position.val := rfl

def mapLeft : JudgmentDerivation.SignatureMap (judgmentSignature left)
    (judgmentSignature (signature left right)) where
  judgment := judgmentLeft
  rule := fun rule =>
    ⟨ruleLeft rule.val, (ruleLeft_conclusion _).trans (congrArg judgmentLeft rule.property)⟩
  position := fun rule position => ⟨premiseLeft left right rule.val position.down⟩
  hypothesis := by
    intro judgment rule position
    have valid : position.down.val < rule.val.premises.length := by
      rw [← ruleLeft_premise_length left right rule.val]
      exact position.down.isLt
    change judgmentLeft (rule.val.premises[position.down.val]'valid) =
      (ruleLeft rule.val).premises[position.down.val]
    simp only [ruleLeft_premises, List.getElem_map]

def derivationLeft {judgment : Judgment S} (tree : Derivation left judgment) :
    Derivation (signature left right) (judgmentLeft judgment) :=
  (mapLeft left right).translate tree

theorem ruleRight_premise_length (rule : RuleCode right) :
    (ruleRight (left := left) rule).premises.length = rule.premises.length := by
  rw [ruleRight_premises, List.length_map]

def premiseRight (rule : RuleCode right)
    (position : Fin (ruleRight (left := left) rule).premises.length) :
    Fin rule.premises.length := Fin.cast (ruleRight_premise_length left right rule) position

theorem premiseRight_value (rule : RuleCode right)
    (position : Fin (ruleRight (left := left) rule).premises.length) :
    (premiseRight left right rule position).val = position.val := rfl

def mapRight : JudgmentDerivation.SignatureMap (judgmentSignature right)
    (judgmentSignature (signature left right)) where
  judgment := judgmentRight
  rule := fun rule =>
    ⟨ruleRight rule.val, (ruleRight_conclusion _).trans (congrArg judgmentRight rule.property)⟩
  position := fun rule position => ⟨premiseRight left right rule.val position.down⟩
  hypothesis := by
    intro judgment rule position
    have valid : position.down.val < rule.val.premises.length := by
      rw [← ruleRight_premise_length left right rule.val]
      exact position.down.isLt
    change judgmentRight (rule.val.premises[position.down.val]'valid) =
      (ruleRight rule.val).premises[position.down.val]
    simp only [ruleRight_premises, List.getElem_map]

def derivationRight {judgment : Judgment T} (tree : Derivation right judgment) :
    Derivation (signature left right) (judgmentRight judgment) :=
  (mapRight left right).translate tree

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.SignatureSum


import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Languages.HOLLight.StorageSize
import Mettapedia.Languages.HOLLight.PrimitiveStorageBounds

/-!
# Full payload bounds for equality proof expansion

The bounds charge the stored premise theorems and their axiom/hypothesis
payloads, not only the newly displayed formulas. Symmetry has a linear bound
for its five actual primitive requests and the complete shared equality terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.EqualityStorageBounds

open Mettapedia.Languages.OpenTheory
open EqualityExpansion
open ProofExecution (Origin)

/-- All data supplied to one equality block is charged independently. -/
def inputUnits (input : Theorem) (left right : CanonicalTerm) (source : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.canonical left +
    OpenTheory.StorageSize.canonical right + StorageSize.origin source

theorem reflexivity_size (value : CanonicalTerm) :
    OpenTheory.StorageSize.theoremData (reflexivity value) =
      52 + 2 * OpenTheory.StorageSize.canonical value := by
  rw [reflexivity, OpenTheory.StorageSize.emptyResult_size, OpenTheory.StorageSize.finset_empty,
    PrimitiveStorageBounds.equalityOfSameType_size]
  omega

theorem eqMpResult_size (equation premise : Theorem) (right : CanonicalTerm) :
    OpenTheory.StorageSize.theoremData (eqMpResult equation premise right) ≤
      OpenTheory.StorageSize.theoremData equation + OpenTheory.StorageSize.theoremData premise +
        OpenTheory.StorageSize.canonical right :=
  OpenTheory.StorageSize.unionResult_le _ _ _ _ (fun _ member => member)

theorem appResult_size (functionEquality argumentEquality : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.theoremData (appResult functionEquality argumentEquality left right sameType) ≤
      OpenTheory.StorageSize.theoremData functionEquality + OpenTheory.StorageSize.theoremData argumentEquality +
        48 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have bound := OpenTheory.StorageSize.unionResult_le functionEquality argumentEquality _
    (CanonicalTerm.equalityOfSameType left right sameType) (fun _ member => member)
  rw [PrimitiveStorageBounds.equalityOfSameType_size] at bound
  unfold appResult
  omega

theorem transResult_size (first second : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.theoremData (transResult first second left right sameType) ≤
      OpenTheory.StorageSize.theoremData first + OpenTheory.StorageSize.theoremData second +
        48 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right :=
  appResult_size first second left right sameType

theorem equalityConstant_size (left : CanonicalTerm) :
    OpenTheory.StorageSize.canonical (equalityConstant left) =
      66 + 4 * OpenTheory.StorageSize.ty left.ty := by
  simp only [equalityConstant, CanonicalTerm.constant, OpenTheory.StorageSize.canonical,
    OpenTheory.StorageSize.term]
  rw [OpenTheory.StorageSize.equalityConstant_storage]
  simp only [Ty.equality, OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]
  omega

theorem equalityConstant_le (left : CanonicalTerm) :
    OpenTheory.StorageSize.canonical (equalityConstant left) ≤
      66 + 4 * OpenTheory.StorageSize.canonical left := by
  rw [equalityConstant_size]
  have typed := OpenTheory.StorageSize.canonical_type_le left
  omega

theorem partialLeft_size (left : CanonicalTerm) :
    OpenTheory.StorageSize.canonical (partialLeft left) =
      58 + 3 * OpenTheory.StorageSize.ty left.ty + OpenTheory.StorageSize.term left.term := by
  simp only [partialLeft, CanonicalTerm.applicationOfFunction, equalityConstant, CanonicalTerm.constant,
    OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term]
  rw [OpenTheory.StorageSize.equalityConstant_storage]
  simp only [Ty.equality, OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]
  omega

theorem partialRight_size (left right : CanonicalTerm) (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.canonical (partialRight left right sameType) =
      58 + 3 * OpenTheory.StorageSize.ty left.ty + OpenTheory.StorageSize.term right.term := by
  simp only [partialRight, CanonicalTerm.applicationOfFunction, equalityConstant, CanonicalTerm.constant,
    OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term]
  rw [OpenTheory.StorageSize.equalityConstant_storage]
  simp only [Ty.equality, OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]
  omega

theorem headCongruence_size (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.theoremData (headCongruence input left right sameType) ≤
      OpenTheory.StorageSize.theoremData input + 164 +
        6 * OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have bound := OpenTheory.StorageSize.preserveAxiomsResult_le input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType (partialLeft left) (partialRight left right sameType) rfl)
    (fun _ member => member)
  have size := PrimitiveStorageBounds.equalityOfSameType_size (partialLeft left) (partialRight left right sameType) rfl
  rw [size, partialLeft_size, partialRight_size] at bound
  unfold headCongruence
  have firstType := OpenTheory.StorageSize.canonical_type_le left
  have firstTerm := OpenTheory.StorageSize.canonical_term_le left
  have secondTerm := OpenTheory.StorageSize.canonical_term_le right
  unfold OpenTheory.StorageSize.canonical at *
  change _ ≤ _
  omega

theorem fullCongruence_size (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.theoremData (fullCongruence input left right sameType) ≤
      OpenTheory.StorageSize.theoremData input + 144 +
        3 * OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have bound := OpenTheory.StorageSize.preserveAxiomsResult_le input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType (CanonicalTerm.equalityOfSameType left left rfl)
      (CanonicalTerm.equalityOfSameType right left sameType.symm) rfl) (fun _ member => member)
  have size := PrimitiveStorageBounds.equalityOfSameType_size
    (CanonicalTerm.equalityOfSameType left left rfl)
    (CanonicalTerm.equalityOfSameType right left sameType.symm) rfl
  rw [size] at bound
  simp only [PrimitiveStorageBounds.equalityOfSameType_size] at bound
  unfold fullCongruence
  omega

theorem symmetryResult_size (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.theoremData (symmetryResult input left right sameType) ≤
      OpenTheory.StorageSize.theoremData input + 48 +
        OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have bound := OpenTheory.StorageSize.preserveAxiomsResult_le input input.sequent.hyp
    (CanonicalTerm.equalityOfSameType right left sameType.symm) (fun _ member => member)
  rw [PrimitiveStorageBounds.equalityOfSameType_size] at bound
  unfold symmetryResult
  omega

/-- The actual five-node graph has a full linear payload bound. Earlier
premise proofs are shared, while their theorem values remain explicitly charged. -/
theorem symmetryBlock_payload (input : Theorem) (left right : CanonicalTerm)
    (sameType : left.ty = right.ty) (source : Origin) :
    GraphExpansion.graphWeight StorageSize.receiptPayload (symmetryBlock input left right sameType source).1 ≤
      2000 * inputUnits input left right source := by
  have constantBound := equalityConstant_le left
  have firstRefl := reflexivity_size (equalityConstant left)
  have operandRefl := reflexivity_size left
  have headBound := headCongruence_size input left right sameType
  have fullBound := fullCongruence_size input left right sameType
  have resultBound := symmetryResult_size input left right sameType
  simp only [symmetryBlock, GraphExpansion.graphWeight, GraphExpansion.receiptWeight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest]
  unfold inputUnits
  omega

/-- Complete supplied input to a two-argument beta expansion. -/
def doubleBetaInputSize (first second codomain : Ty) (body : DBTerm)
    (left right : CanonicalTerm) (source : Origin) : Nat :=
  1 + OpenTheory.StorageSize.ty first + OpenTheory.StorageSize.ty second +
    OpenTheory.StorageSize.ty codomain + OpenTheory.StorageSize.term body +
    OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right + StorageSize.origin source

private theorem doubleBeta_first_input_bound (first second codomain : Ty) (body : DBTerm)
    (left right : CanonicalTerm) (source : Origin) :
    PrimitiveStorageBounds.betaInputSize first (.abs second body) (.function second codomain) left +
      StorageSize.origin source ≤ 12 * doubleBetaInputSize first second codomain body left right source := by
  simp only [PrimitiveStorageBounds.betaInputSize, doubleBetaInputSize,
    OpenTheory.StorageSize.term, OpenTheory.StorageSize.functionType_storage]
  omega

private theorem doubleBeta_second_input_bound (first second codomain : Ty) (body : DBTerm)
    (left right : CanonicalTerm) (source : Origin) :
    PrimitiveStorageBounds.betaInputSize second (DBTerm.instantiateAt left.term 1 body) codomain right +
      StorageSize.origin source ≤ 4 * doubleBetaInputSize first second codomain body left right source ^ 2 := by
  let total := doubleBetaInputSize first second codomain body left right source
  have positive : 1 ≤ total := by unfold total doubleBetaInputSize; omega
  have bodySmall : OpenTheory.StorageSize.term body ≤ total := by unfold total doubleBetaInputSize; omega
  have leftSmall : OpenTheory.StorageSize.term left.term ≤ total := by
    have small := OpenTheory.StorageSize.canonical_term_le left
    unfold total doubleBetaInputSize
    omega
  have instantiated := PrimitiveStorageBounds.instantiateAt_size left.term 1 body
  have substituted : OpenTheory.StorageSize.term (DBTerm.instantiateAt left.term 1 body) ≤ total * (total + 1) := by
    apply instantiated.trans
    gcongr
  have remaining : OpenTheory.StorageSize.ty second + OpenTheory.StorageSize.ty codomain +
      OpenTheory.StorageSize.canonical right + 1 + StorageSize.origin source ≤ total := by
    unfold total doubleBetaInputSize
    omega
  unfold PrimitiveStorageBounds.betaInputSize
  change _ ≤ 4 * total ^ 2
  nlinarith

private theorem application_size (function argument : CanonicalTerm) (codomain : Ty)
    (functionType : function.ty.destFunction? = some (argument.ty, codomain)) :
    OpenTheory.StorageSize.canonical (CanonicalTerm.applicationOfFunction function argument codomain functionType) ≤
      OpenTheory.StorageSize.canonical function + OpenTheory.StorageSize.canonical argument +
        OpenTheory.StorageSize.ty codomain + 1 := by
  simp only [CanonicalTerm.applicationOfFunction, OpenTheory.StorageSize.canonical,
    OpenTheory.StorageSize.term]
  omega

set_option maxHeartbeats 1500000 in
/-- The lifted congruence theorem retains all primitive beta data within a
quartic bound on its complete supplied payload. -/
theorem doubleBetaExpansion_application_size (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (source : Origin) :
    OpenTheory.StorageSize.theoremData
      (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType).application ≤
      20000 * doubleBetaInputSize first second codomain body left right source ^ 4 := by
  let total := doubleBetaInputSize first second codomain body left right source
  have positive : 1 ≤ total := by unfold total doubleBetaInputSize; omega
  have innerChecked : (DBTerm.abs second body).inferType [first] = some (.function second codomain) := by
    simp [DBTerm.inferType, bodyChecked]
  let before := PrimitiveTransport.betaRedex first (.abs second body) (.function second codomain) innerChecked left leftType
  let after := PrimitiveTransport.betaReduced first (.abs second body) (.function second codomain) innerChecked left leftType
  let whole := CanonicalTerm.applicationOfFunction before right codomain (by simp [before, PrimitiveTransport.betaRedex, rightType])
  let middle := CanonicalTerm.applicationOfFunction after right codomain (by simp [after, PrimitiveTransport.betaReduced, rightType])
  have firstBound := PrimitiveStorageBounds.betaExpansion_conclusion_size first (.abs second body)
    (.function second codomain) innerChecked left leftType
  have inputBound := doubleBeta_first_input_bound first second codomain body left right source
  have squared : PrimitiveStorageBounds.betaInputSize first (.abs second body) (.function second codomain) left ^ 2 ≤
      (12 * total) ^ 2 := by
    apply Nat.pow_le_pow_left
    unfold total at *
    omega
  have firstLarge : OpenTheory.StorageSize.theoremData
      (PrimitiveTransport.betaExpansion first (.abs second body) (.function second codomain) innerChecked left leftType).conclusion ≤
        11520 * total ^ 2 := by nlinarith
  have rightReflexivity := reflexivity_size right
  have rightSmall : OpenTheory.StorageSize.canonical right ≤ total := by unfold total doubleBetaInputSize; omega
  have leftSmall : OpenTheory.StorageSize.term left.term ≤ total := by
    have small := OpenTheory.StorageSize.canonical_term_le left
    unfold total doubleBetaInputSize; omega
  have bodySmall : OpenTheory.StorageSize.term body ≤ total := by unfold total doubleBetaInputSize; omega
  have beforeSize := PrimitiveStorageBounds.betaRedex_size first (.abs second body) (.function second codomain) innerChecked left leftType
  have beforeLarge : OpenTheory.StorageSize.canonical before ≤ 14 * total := by
    simp only [OpenTheory.StorageSize.term, OpenTheory.StorageSize.functionType_storage] at beforeSize
    unfold before
    rw [beforeSize]
    unfold total doubleBetaInputSize
    have small := OpenTheory.StorageSize.canonical_term_le left
    omega
  have afterSize := PrimitiveStorageBounds.betaReduced_size first (.abs second body) (.function second codomain) innerChecked left leftType
  have substitution := PrimitiveStorageBounds.instantiateAt_size left.term 0 (.abs second body)
  have bodyAbsSmall : OpenTheory.StorageSize.term (.abs second body) ≤ 2 * total := by
    simp only [OpenTheory.StorageSize.term]
    unfold total doubleBetaInputSize
    omega
  have productSmall : OpenTheory.StorageSize.term (.abs second body) * (OpenTheory.StorageSize.term left.term + 1) ≤
      2 * total * (total + 1) := by gcongr
  have afterLarge : OpenTheory.StorageSize.canonical after ≤ 20 * total ^ 2 := by
    have codomainSmall : OpenTheory.StorageSize.ty (.function second codomain) ≤ 10 * total := by
      simp only [OpenTheory.StorageSize.functionType_storage]
      unfold total doubleBetaInputSize
      omega
    unfold after
    nlinarith
  have wholeSize := application_size before right codomain (by simp [before, PrimitiveTransport.betaRedex, rightType])
  have middleSize := application_size after right codomain (by simp [after, PrimitiveTransport.betaReduced, rightType])
  have codomainSmall : OpenTheory.StorageSize.ty codomain ≤ total := by unfold total doubleBetaInputSize; omega
  have wholeLarge : OpenTheory.StorageSize.canonical whole ≤ 17 * total ^ 2 := by
    unfold whole
    nlinarith
  have middleLarge : OpenTheory.StorageSize.canonical middle ≤ 23 * total ^ 2 := by
    unfold middle
    nlinarith
  have outputBound := appResult_size
    (PrimitiveTransport.betaExpansion first (.abs second body) (.function second codomain) innerChecked left leftType).conclusion
    (reflexivity right) whole middle rfl
  change OpenTheory.StorageSize.theoremData (appResult _ _ whole middle rfl) ≤ 20000 * total ^ 4
  have squares : total ^ 2 ≤ total ^ 4 := pow_le_pow_right' positive (by decide)
  nlinarith

/-- The complete double-beta result remains an axiom-free equation, with its
nested copied substitutions charged in the full term measure. -/
theorem doubleBetaExpansion_conclusion_size (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (source : Origin) :
    OpenTheory.StorageSize.theoremData
      (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType).conclusion ≤
      100 * doubleBetaInputSize first second codomain body left right source ^ 4 := by
  let total := doubleBetaInputSize first second codomain body left right source
  have positive : 1 ≤ total := by unfold total doubleBetaInputSize; omega
  have bodySmall : OpenTheory.StorageSize.term body ≤ total := by unfold total doubleBetaInputSize; omega
  have leftSmall : OpenTheory.StorageSize.term left.term ≤ total := by
    have small := OpenTheory.StorageSize.canonical_term_le left
    unfold total doubleBetaInputSize; omega
  have rightSmall : OpenTheory.StorageSize.term right.term ≤ total := by
    have small := OpenTheory.StorageSize.canonical_term_le right
    unfold total doubleBetaInputSize; omega
  have firstSubstitution := PrimitiveStorageBounds.instantiateAt_size left.term 1 body
  have secondSubstitution := PrimitiveStorageBounds.instantiateAt_size right.term 0 (DBTerm.instantiateAt left.term 1 body)
  have firstCopied : OpenTheory.StorageSize.term (DBTerm.instantiateAt left.term 1 body) ≤ total * (total + 1) := by
    apply firstSubstitution.trans
    gcongr
  have secondCopied : OpenTheory.StorageSize.term
      (DBTerm.instantiateAt right.term 0 (DBTerm.instantiateAt left.term 1 body)) ≤ total * (total + 1) * (total + 1) := by
    apply secondSubstitution.trans
    gcongr
  have parts := doubleBetaExpansion_parts first second codomain body bodyChecked left right leftType rightType
  dsimp only at parts
  simp only [OpenTheory.StorageSize.theoremData, OpenTheory.StorageSize.sequent, parts.1, parts.2.1,
    OpenTheory.StorageSize.finset_empty, OpenTheory.StorageSize.canonical, parts.2.2,
    PrimitiveStorageBounds.equalityDB_size, OpenTheory.StorageSize.term]
  have finalType : (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType).conclusion.sequent.concl.ty = Ty.bool := rfl
  rw [finalType, OpenTheory.StorageSize.boolType_storage]
  have leftCanonical := OpenTheory.StorageSize.canonical_term_le left
  have rightCanonical := OpenTheory.StorageSize.canonical_term_le right
  have linear : OpenTheory.StorageSize.ty first + OpenTheory.StorageSize.ty second + OpenTheory.StorageSize.ty codomain +
      OpenTheory.StorageSize.term body + OpenTheory.StorageSize.term left.term + OpenTheory.StorageSize.term right.term ≤ 2 * total := by
    unfold total doubleBetaInputSize
    omega
  change _ ≤ 100 * total ^ 4
  have squareSmall : total ^ 2 ≤ total ^ 4 := pow_le_pow_right' positive (by decide)
  have cubeSmall : total ^ 3 ≤ total ^ 4 := pow_le_pow_right' positive (by decide)
  nlinarith

set_option maxHeartbeats 1500000 in
/-- The seven emitted primitive occurrences have a quartic bound in complete
input storage. This counts retained theorem/request payloads, rather than
only the number of graph nodes. -/
theorem doubleBetaBlock_payload (first second codomain : Ty) (body : DBTerm)
    (bodyChecked : body.inferType [second, first] = some codomain)
    (left right : CanonicalTerm) (leftType : left.ty = first) (rightType : right.ty = second)
    (source : Origin) :
    GraphExpansion.graphWeight StorageSize.receiptPayload
      (doubleBetaBlock (doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType) source).1 ≤
      200000 * doubleBetaInputSize first second codomain body left right source ^ 4 := by
  let total := doubleBetaInputSize first second codomain body left right source
  let expansion := doubleBetaExpansion first second codomain body bodyChecked left right leftType rightType
  have positive : 1 ≤ total := by unfold total doubleBetaInputSize; omega
  have squareSmall : total ^ 2 ≤ total ^ 4 := pow_le_pow_right' positive (by decide)
  have originSmall : StorageSize.origin source ≤ total ^ 4 := by
    have small : StorageSize.origin source ≤ total := by unfold total doubleBetaInputSize; omega
    exact small.trans (by simpa only [pow_one] using (pow_le_pow_right' positive (by decide : 1 ≤ 4)))
  have argumentSmall : OpenTheory.StorageSize.canonical right ≤ total ^ 4 := by
    have small : OpenTheory.StorageSize.canonical right ≤ total := by unfold total doubleBetaInputSize; omega
    exact small.trans (by simpa only [pow_one] using (pow_le_pow_right' positive (by decide : 1 ≤ 4)))
  have innerChecked : (DBTerm.abs second body).inferType [first] = some (.function second codomain) := by
    simp [DBTerm.inferType, bodyChecked]
  have nextChecked : (DBTerm.instantiateAt left.term 1 body).inferType [second] = some codomain := by
    simpa using DBTerm.inferType_instantiateAt left.term body first
      (by simpa [leftType] using left.checked) [second] bodyChecked
  have firstBound := PrimitiveStorageBounds.betaBlock_payload first (.abs second body)
    (.function second codomain) innerChecked left leftType source
  have firstInput := doubleBeta_first_input_bound first second codomain body left right source
  change _ ≤ 12 * total at firstInput
  have firstSquared : (PrimitiveStorageBounds.betaInputSize first (.abs second body) (.function second codomain) left + StorageSize.origin source) ^ 2 ≤
      (12 * total) ^ 2 := Nat.pow_le_pow_left firstInput 2
  have firstLarge : GraphExpansion.graphWeight StorageSize.receiptPayload
      (PrimitiveTransport.betaBlock expansion.first source).1 ≤ 72000 * total ^ 4 := by
    change GraphExpansion.graphWeight StorageSize.receiptPayload
      (PrimitiveTransport.betaBlock (PrimitiveTransport.betaExpansion first (.abs second body) (.function second codomain) innerChecked left leftType) source).1 ≤ _
    nlinarith
  have secondBound := PrimitiveStorageBounds.betaBlock_payload second (DBTerm.instantiateAt left.term 1 body)
    codomain nextChecked right rightType source
  have secondInput := doubleBeta_second_input_bound first second codomain body left right source
  change _ ≤ 4 * total ^ 2 at secondInput
  have secondSquared : (PrimitiveStorageBounds.betaInputSize second (DBTerm.instantiateAt left.term 1 body) codomain right + StorageSize.origin source) ^ 2 ≤
      (4 * total ^ 2) ^ 2 := Nat.pow_le_pow_left secondInput 2
  have secondLarge : GraphExpansion.graphWeight StorageSize.receiptPayload
      (PrimitiveTransport.betaBlock expansion.second source).1 ≤ 8000 * total ^ 4 := by
    change GraphExpansion.graphWeight StorageSize.receiptPayload
      (PrimitiveTransport.betaBlock (PrimitiveTransport.betaExpansion second (DBTerm.instantiateAt left.term 1 body) codomain nextChecked right rightType) source).1 ≤ _
    nlinarith
  have firstConclusion := PrimitiveStorageBounds.betaExpansion_conclusion_size first (.abs second body)
    (.function second codomain) innerChecked left leftType
  have firstAlone : PrimitiveStorageBounds.betaInputSize first (.abs second body) (.function second codomain) left ^ 2 ≤
      (12 * total) ^ 2 := by apply Nat.pow_le_pow_left; omega
  have firstConclusionLarge : OpenTheory.StorageSize.theoremData expansion.first.conclusion ≤ 11520 * total ^ 4 := by
    change OpenTheory.StorageSize.theoremData
      (PrimitiveTransport.betaExpansion first (.abs second body) (.function second codomain) innerChecked left leftType).conclusion ≤ _
    nlinarith
  have secondConclusion := PrimitiveStorageBounds.betaExpansion_conclusion_size second (DBTerm.instantiateAt left.term 1 body)
    codomain nextChecked right rightType
  have secondAlone : PrimitiveStorageBounds.betaInputSize second (DBTerm.instantiateAt left.term 1 body) codomain right ^ 2 ≤
      (4 * total ^ 2) ^ 2 := by apply Nat.pow_le_pow_left; omega
  have secondConclusionLarge : OpenTheory.StorageSize.theoremData expansion.second.conclusion ≤ 1280 * total ^ 4 := by
    change OpenTheory.StorageSize.theoremData
      (PrimitiveTransport.betaExpansion second (DBTerm.instantiateAt left.term 1 body) codomain nextChecked right rightType).conclusion ≤ _
    nlinarith
  have applicationLarge := doubleBetaExpansion_application_size first second codomain body bodyChecked left right leftType rightType source
  have conclusionLarge := doubleBetaExpansion_conclusion_size first second codomain body bodyChecked left right leftType rightType source
  have reflexivitySize := reflexivity_size right
  have argumentSame : expansion.argument = right := rfl
  rw [← argumentSame] at reflexivitySize argumentSmall
  simp only [PrimitiveTransport.betaBlock, GraphExpansion.graphWeight,
    GraphExpansion.receiptWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_nil, List.length_cons, StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest] at firstLarge secondLarge
  change _ ≤ 200000 * total ^ 4
  simp only [doubleBetaBlock, GraphExpansion.graphWeight, GraphExpansion.receiptWeight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, List.length_cons,
    StorageSize.receiptPayload, StorageSize.request, StorageSize.inferenceRequest]
  change _ ≤ _ at applicationLarge conclusionLarge
  nlinarith

end Mettapedia.Languages.HOLLight.EqualityStorageBounds

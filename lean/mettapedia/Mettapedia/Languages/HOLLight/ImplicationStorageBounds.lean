import Mettapedia.Languages.HOLLight.ImplicationExpansion
import Mettapedia.Languages.HOLLight.EqualityStorageBounds

/-!
# Full payload bounds for implication elimination

The operational expansion uses the existing boolean definitions and the ten
primitive HOL Light rules. These bounds charge the complete stored theorems,
requests, names and origin data in the emitted certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ImplicationStorageBounds

open Mettapedia.Languages.OpenTheory
open ImplicationExpansion EqualityExpansion PrimitiveTransport GraphExpansion
open ProofExecution (Origin)
open ExcludedMiddle (impDB impAppDB andDB boolBinaryTy)
open DerivedRules (andAppDB selectSecondDB)
open PrimitiveSentences (truthDB identityBool)

def inputUnits (input premise : Theorem) (left right : CanonicalTerm) (origin : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.theoremData premise +
    OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right + StorageSize.origin origin

theorem conjunction_head_storage : OpenTheory.StorageSize.term andDB ≤ 1000 := by decide +kernel
theorem implication_head_storage : OpenTheory.StorageSize.term impDB ≤ 1000 := by decide +kernel
theorem conjunction_body_storage : OpenTheory.StorageSize.term conjunctionBody ≤ 1000 := by decide +kernel
theorem implication_body_storage : OpenTheory.StorageSize.term implicationBody ≤ 1000 := by decide +kernel
theorem binary_type_storage : OpenTheory.StorageSize.ty boolBinaryTy ≤ 100 := by decide +kernel
theorem selector_storage : OpenTheory.StorageSize.canonical secondSelector ≤ 1000 := by decide +kernel
theorem truth_storage : OpenTheory.StorageSize.canonical DerivedRules.truthTerm ≤ 1000 := by decide +kernel
theorem identity_storage :
    OpenTheory.StorageSize.canonical
      (⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩ : CanonicalTerm) ≤ 1000 := by decide +kernel

theorem conjunction_storage (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    OpenTheory.StorageSize.canonical (conjunction left right leftBool rightBool) ≤
      1014 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have head := conjunction_head_storage
  have first := OpenTheory.StorageSize.canonical_term_le left
  have second := OpenTheory.StorageSize.canonical_term_le right
  simp only [conjunction, andAppDB, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
    OpenTheory.StorageSize.boolType_storage]
  simp only [OpenTheory.StorageSize.canonical] at *
  omega

theorem implication_storage (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    OpenTheory.StorageSize.canonical (implication left right leftBool rightBool) ≤
      1014 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have head := implication_head_storage
  have first := OpenTheory.StorageSize.canonical_term_le left
  have second := OpenTheory.StorageSize.canonical_term_le right
  simp only [implication, impAppDB, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
    OpenTheory.StorageSize.boolType_storage]
  simp only [OpenTheory.StorageSize.canonical] at *
  omega

theorem pair_storage (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    OpenTheory.StorageSize.canonical (pairTerm left right leftBool rightBool) ≤
      225 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have binary := binary_type_storage
  have first := OpenTheory.StorageSize.canonical_term_le left
  have second := OpenTheory.StorageSize.canonical_term_le right
  have zero : OpenTheory.StorageSize.nat 0 = 1 := by decide +kernel
  simp only [pairTerm, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
    OpenTheory.StorageSize.functionType_storage, OpenTheory.StorageSize.boolType_storage]
  simp only [OpenTheory.StorageSize.canonical] at *
  omega

theorem selected_pair_storage (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    OpenTheory.StorageSize.canonical (selectedPair left right leftBool rightBool) ≤
      1240 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have pair := pair_storage left right leftBool rightBool
  have selector := selector_storage
  have first := OpenTheory.StorageSize.canonical_term_le (pairTerm left right leftBool rightBool)
  have second := OpenTheory.StorageSize.canonical_term_le secondSelector
  simp only [selectedPair, CanonicalTerm.applicationOfFunction, OpenTheory.StorageSize.canonical,
    OpenTheory.StorageSize.term, OpenTheory.StorageSize.boolType_storage]
  simp only [OpenTheory.StorageSize.canonical] at *
  omega

theorem selector_application_storage (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    OpenTheory.StorageSize.canonical (selectorApplication left right leftBool rightBool) ≤
      1014 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have selector := OpenTheory.StorageSize.canonical_term_le secondSelector
  have bound := selector_storage
  have first := OpenTheory.StorageSize.canonical_term_le left
  have second := OpenTheory.StorageSize.canonical_term_le right
  simp only [secondSelector] at selector bound
  simp only [selectorApplication, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term,
    OpenTheory.StorageSize.boolType_storage]
  simp only [OpenTheory.StorageSize.canonical] at *
  omega

/-- A deliberately coarse common quartic budget for the fixed logical
expansion. It includes every data field; it is not a measured runtime. -/
def payloadBudget (units : Nat) : Nat := 1000000000000000000000000000000 * units ^ 4

private theorem linear_le_budget (units value : Nat) (positive : 1 ≤ units)
    (bounded : value ≤ 10000 * units) : value ≤ payloadBudget units := by
  have power : units ≤ units ^ 4 := le_self_pow positive (by decide)
  unfold payloadBudget
  nlinarith

private theorem quartic_le_budget (units value coefficient : Nat)
    (bounded : value ≤ 10000 * units) (coefficientBound : coefficient ≤ 1000000000) :
    coefficient * value ^ 4 ≤ payloadBudget units := by
  calc
    coefficient * value ^ 4 ≤ 1000000000 * (10000 * units) ^ 4 :=
      Nat.mul_le_mul coefficientBound (Nat.pow_le_pow_left bounded 4)
    _ = 10000000000000000000000000 * units ^ 4 := by ring
    _ ≤ payloadBudget units := Nat.mul_le_mul_right _ (by decide)

private theorem quadratic_le_budget (units value coefficient : Nat) (positive : 1 ≤ units)
    (bounded : value ≤ 10000 * units) (coefficientBound : coefficient ≤ 1000000000) :
    coefficient * value ^ 2 ≤ payloadBudget units := by
  have powers : units ^ 2 ≤ units ^ 4 := pow_le_pow_right' positive (by decide)
  calc
    coefficient * value ^ 2 ≤ 1000000000 * (10000 * units) ^ 2 :=
      Nat.mul_le_mul coefficientBound (Nat.pow_le_pow_left bounded 2)
    _ = 100000000000000000 * units ^ 2 := by ring
    _ ≤ 100000000000000000 * units ^ 4 := Nat.mul_le_mul_left _ powers
    _ ≤ payloadBudget units := Nat.mul_le_mul_right _ (by decide)

private theorem pairBeta_bounds (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) (origin : Origin) (units : Nat)
    (positive : 1 ≤ units)
    (operands : OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right +
      StorageSize.origin origin ≤ 4000 * units) :
    OpenTheory.StorageSize.theoremData (pairBeta left right leftBool rightBool).conclusion ≤ payloadBudget units ∧
      GraphExpansion.graphWeight StorageSize.receiptPayload
        (betaBlock (pairBeta left right leftBool rightBool) origin).1 ≤ payloadBudget units := by
  let body := DBTerm.app (.app (.bound 0) left.term) right.term
  have bodyChecked : body.inferType [boolBinaryTy] = some Ty.bool :=
    DBTerm.inferType_app_of (DBTerm.inferType_app_of (by simp [boolBinaryTy])
      (DBTerm.inferType_weaken_empty (leftBool ▸ left.checked) _))
      (DBTerm.inferType_weaken_empty (rightBool ▸ right.checked) _)
  have inputBound : PrimitiveStorageBounds.betaInputSize boolBinaryTy body Ty.bool secondSelector +
      StorageSize.origin origin ≤ 10000 * units := by
    have binary := binary_type_storage
    have selector := selector_storage
    have first := OpenTheory.StorageSize.canonical_term_le left
    have second := OpenTheory.StorageSize.canonical_term_le right
    have zero : OpenTheory.StorageSize.nat 0 = 1 := by decide +kernel
    simp only [PrimitiveStorageBounds.betaInputSize, body, OpenTheory.StorageSize.term,
      OpenTheory.StorageSize.boolType_storage]
    omega
  have output := PrimitiveStorageBounds.betaExpansion_conclusion_size boolBinaryTy body Ty.bool
    bodyChecked secondSelector (show secondSelector.ty = boolBinaryTy from rfl)
  have payload := PrimitiveStorageBounds.betaBlock_payload boolBinaryTy body Ty.bool bodyChecked secondSelector
    (show secondSelector.ty = boolBinaryTy from rfl) origin
  have baseBound : PrimitiveStorageBounds.betaInputSize boolBinaryTy body Ty.bool secondSelector ≤ 10000 * units := by omega
  have outputBudget := quadratic_le_budget units _ 80 positive baseBound (by decide)
  have payloadBudgetBound := quadratic_le_budget units _ 500 positive inputBound (by decide)
  constructor
  · change OpenTheory.StorageSize.theoremData
      (betaExpansion boolBinaryTy body Ty.bool bodyChecked secondSelector rfl).conclusion ≤ _
    exact output.trans outputBudget
  · change GraphExpansion.graphWeight StorageSize.receiptPayload
      (betaBlock (betaExpansion boolBinaryTy body Ty.bool bodyChecked secondSelector rfl) origin).1 ≤ _
    exact payload.trans payloadBudgetBound

theorem mpResult_storage (input premise : Theorem) (right : CanonicalTerm) :
    OpenTheory.StorageSize.theoremData (mpResult input premise right) ≤
      OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.theoremData premise +
        OpenTheory.StorageSize.canonical right :=
  OpenTheory.StorageSize.unionResult_le _ _ _ _ (fun _ member => member)

/-- The consequent is a stored subterm of an admitted implication. -/
theorem right_storage_le (input : Theorem) (left right : CanonicalTerm)
    (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term) :
    OpenTheory.StorageSize.canonical right ≤ OpenTheory.StorageSize.theoremData input + 12 := by
  have rightTerm := OpenTheory.StorageSize.application_argument_le (.app impDB left.term) right.term
  change OpenTheory.StorageSize.term right.term ≤ OpenTheory.StorageSize.term (impAppDB left.term right.term) at rightTerm
  rw [← shape] at rightTerm
  have termBound := rightTerm.trans ((OpenTheory.StorageSize.canonical_term_le input.sequent.concl).trans
    (OpenTheory.StorageSize.theorem_conclusion_le input))
  have rightSize : OpenTheory.StorageSize.canonical right = 12 + OpenTheory.StorageSize.term right.term := by
    simp only [OpenTheory.StorageSize.canonical, rightBool, OpenTheory.StorageSize.boolType_storage]
    omega
  omega

/-- The typed operands are already present in the actual two input theorems. -/
theorem inputUnits_le_actual (input premise : Theorem) (left right : CanonicalTerm)
    (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    inputUnits input premise left right origin ≤
      20 * (1 + OpenTheory.StorageSize.theoremData input + OpenTheory.StorageSize.theoremData premise +
        StorageSize.origin origin) := by
  have leftBound := OpenTheory.StorageSize.theorem_conclusion_le premise
  rw [matching] at leftBound
  have rightBound := right_storage_le input left right rightBool shape
  unfold inputUnits
  omega

private theorem booleanDoubleBeta_bounds (body : DBTerm)
    (bodyChecked : body.inferType [Ty.bool, Ty.bool] = some Ty.bool)
    (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (origin : Origin) (units : Nat) (positive : 1 ≤ units)
    (bodyBound : OpenTheory.StorageSize.term body ≤ 1000)
    (operands : OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right +
      StorageSize.origin origin ≤ 4000 * units) :
    OpenTheory.StorageSize.theoremData
        (doubleBetaExpansion Ty.bool Ty.bool Ty.bool body bodyChecked left right leftBool rightBool).conclusion ≤
      payloadBudget units ∧
      GraphExpansion.graphWeight StorageSize.receiptPayload
        (doubleBetaBlock (doubleBetaExpansion Ty.bool Ty.bool Ty.bool body bodyChecked left right leftBool rightBool) origin).1 ≤
      payloadBudget units := by
  have inputBound : EqualityStorageBounds.doubleBetaInputSize Ty.bool Ty.bool Ty.bool body left right origin ≤
      10000 * units := by
    simp only [EqualityStorageBounds.doubleBetaInputSize, OpenTheory.StorageSize.boolType_storage]
    omega
  have output := EqualityStorageBounds.doubleBetaExpansion_conclusion_size Ty.bool Ty.bool Ty.bool body bodyChecked
    left right leftBool rightBool origin
  have payload := EqualityStorageBounds.doubleBetaBlock_payload Ty.bool Ty.bool Ty.bool body bodyChecked
    left right leftBool rightBool origin
  constructor
  · exact output.trans (quartic_le_budget units _ _ inputBound (by decide))
  · exact payload.trans (quartic_le_budget units _ _ inputBound (by decide))

set_option maxHeartbeats 3000000 in
/-- The complete twenty-block MP plan has a quartic full-data bound. Incoming
proof roots remain shared, while every copied premise theorem is charged. -/
theorem mpPlan_payload (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (origin : Origin) :
    ((mpPlan input premise left right leftBool rightBool origin).1.map
      (fun request => GraphExpansion.graphWeight StorageSize.receiptPayload request.witness.1)).sum ≤
      2000000 * payloadBudget (inputUnits input premise left right origin) := by
  let units := inputUnits input premise left right origin
  let budget := payloadBudget units
  have positive : 1 ≤ units := by unfold units inputUnits; omega
  have enough : 10000 * units ≤ budget := linear_le_budget units _ positive (by omega)
  have inputBound : OpenTheory.StorageSize.theoremData input ≤ budget := by unfold units inputUnits at enough; omega
  have premiseBound : OpenTheory.StorageSize.theoremData premise ≤ budget := by unfold units inputUnits at enough; omega
  have leftBound : OpenTheory.StorageSize.canonical left ≤ budget := by unfold units inputUnits at enough; omega
  have rightBound : OpenTheory.StorageSize.canonical right ≤ budget := by unfold units inputUnits at enough; omega
  have originBound : StorageSize.origin origin ≤ budget := by unfold units inputUnits at enough; omega
  have operands : OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right +
      StorageSize.origin origin ≤ 4000 * units := by unfold units inputUnits; omega
  have truthOperands : 2 * OpenTheory.StorageSize.canonical DerivedRules.truthTerm + StorageSize.origin origin ≤
      4000 * units := by
    have truth := truth_storage
    unfold units inputUnits
    omega
  let andTerm := conjunction left right leftBool rightBool
  let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
  let impExpansion := implicationBeta left right leftBool rightBool
  let converted := eqMpResult impExpansion.conclusion input andEquation
  let reversedImp := symmetryResult converted andTerm left leftBool.symm
  let andProof := eqMpResult reversedImp premise andTerm
  let andExpansion := conjunctionBeta left right leftBool rightBool
  let pairLeft := pairTerm left right leftBool rightBool
  let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
  let bodyProof := eqMpResult andExpansion.conclusion andProof pairEquation
  let selectedLeft := selectedPair left right leftBool rightBool
  let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let selectorProof := reflexivity secondSelector
  let bodyApplication := appResult bodyProof selectorProof selectedLeft selectedTruth rfl
  let leftPairBeta := pairBeta left right leftBool rightBool
  let leftSelectorBeta := selectorBeta left right leftBool rightBool
  let leftReduction := transResult leftPairBeta.conclusion leftSelectorBeta.conclusion selectedLeft right rightBool.symm
  let reversedLeft := symmetryResult leftReduction selectedLeft right rightBool.symm
  let truthPairBeta := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthSelectorBeta := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthReduction := transResult truthPairBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
  let joinedLeft := transResult reversedLeft bodyApplication right selectedTruth rightBool
  let joinedTruth := transResult joinedLeft truthReduction right DerivedRules.truthTerm rightBool
  let reversedTruth := symmetryResult joinedTruth right DerivedRules.truthTerm rightBool
  let identityTerm : CanonicalTerm :=
    ⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
  let truthProof := reflexivity identityTerm
  let result := eqMpResult reversedTruth truthProof right
  have andTermBound : OpenTheory.StorageSize.canonical andTerm ≤ budget := by
    apply linear_le_budget units _ positive
    have size := conjunction_storage left right leftBool rightBool
    change OpenTheory.StorageSize.canonical andTerm ≤ _ at size
    unfold units inputUnits
    omega
  have andEquationBound : OpenTheory.StorageSize.canonical andEquation ≤ budget := by
    apply linear_le_budget units _ positive
    have size := PrimitiveStorageBounds.equalityOfSameType_size andTerm left leftBool.symm
    have andSize := conjunction_storage left right leftBool rightBool
    change OpenTheory.StorageSize.canonical andTerm ≤ _ at andSize
    change OpenTheory.StorageSize.canonical andEquation = _ at size
    unfold units inputUnits
    omega
  have pairEquationBound : OpenTheory.StorageSize.canonical pairEquation ≤ budget := by
    apply linear_le_budget units _ positive
    have size := PrimitiveStorageBounds.equalityOfSameType_size pairLeft pairTruth rfl
    have first := pair_storage left right leftBool rightBool
    have second := pair_storage DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have truth := truth_storage
    change OpenTheory.StorageSize.canonical pairLeft ≤ _ at first
    change OpenTheory.StorageSize.canonical pairTruth ≤ _ at second
    change OpenTheory.StorageSize.canonical pairEquation = _ at size
    unfold units inputUnits
    omega
  have selectedLeftBound : OpenTheory.StorageSize.canonical selectedLeft ≤ budget := by
    apply linear_le_budget units _ positive
    have size := selected_pair_storage left right leftBool rightBool
    change OpenTheory.StorageSize.canonical selectedLeft ≤ _ at size
    unfold units inputUnits
    omega
  have selectedTruthBound : OpenTheory.StorageSize.canonical selectedTruth ≤ budget := by
    apply linear_le_budget units _ positive
    have size := selected_pair_storage DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have truth := truth_storage
    change OpenTheory.StorageSize.canonical selectedTruth ≤ _ at size
    unfold units inputUnits
    omega
  have selectorBound : OpenTheory.StorageSize.canonical secondSelector ≤ budget := by
    have size := selector_storage
    omega
  have truthBound : OpenTheory.StorageSize.canonical DerivedRules.truthTerm ≤ budget := by
    have size := truth_storage
    omega
  have identityBound : OpenTheory.StorageSize.canonical identityTerm ≤ budget := by
    have size := identity_storage
    change OpenTheory.StorageSize.canonical identityTerm ≤ _ at size
    omega
  have ⟨impConclusion, impBlock⟩ := booleanDoubleBeta_bounds implicationBody implicationBody_checked
    left right leftBool rightBool origin units positive implication_body_storage operands
  have ⟨andConclusion, andBlock⟩ := booleanDoubleBeta_bounds conjunctionBody conjunctionBody_checked
    left right leftBool rightBool origin units positive conjunction_body_storage operands
  have boundStorage : OpenTheory.StorageSize.term (.bound 0) ≤ 1000 := by decide +kernel
  have ⟨leftSelectorConclusion, leftSelectorBlock⟩ := booleanDoubleBeta_bounds (.bound 0) (by simp)
    left right leftBool rightBool origin units positive boundStorage operands
  have ⟨truthSelectorConclusion, truthSelectorBlock⟩ := booleanDoubleBeta_bounds (.bound 0) (by simp)
    DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl origin units positive boundStorage (by simpa [two_mul] using truthOperands)
  have ⟨leftPairConclusion, leftPairBlock⟩ := pairBeta_bounds left right leftBool rightBool origin units positive operands
  have ⟨truthPairConclusion, truthPairBlock⟩ := pairBeta_bounds DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl origin
    units positive (by simpa [two_mul] using truthOperands)
  change OpenTheory.StorageSize.theoremData impExpansion.conclusion ≤ budget at impConclusion
  change OpenTheory.StorageSize.theoremData andExpansion.conclusion ≤ budget at andConclusion
  change OpenTheory.StorageSize.theoremData leftSelectorBeta.conclusion ≤ budget at leftSelectorConclusion
  change OpenTheory.StorageSize.theoremData truthSelectorBeta.conclusion ≤ budget at truthSelectorConclusion
  change OpenTheory.StorageSize.theoremData leftPairBeta.conclusion ≤ budget at leftPairConclusion
  change OpenTheory.StorageSize.theoremData truthPairBeta.conclusion ≤ budget at truthPairConclusion
  have selectorProofSize := EqualityStorageBounds.reflexivity_size secondSelector
  change OpenTheory.StorageSize.theoremData selectorProof = _ at selectorProofSize
  have selectorProofBound : OpenTheory.StorageSize.theoremData selectorProof ≤ 3 * budget := by omega
  have truthProofSize := EqualityStorageBounds.reflexivity_size identityTerm
  change OpenTheory.StorageSize.theoremData truthProof = _ at truthProofSize
  have truthProofBound : OpenTheory.StorageSize.theoremData truthProof ≤ 3 * budget := by omega
  have convertedSize := EqualityStorageBounds.eqMpResult_size impExpansion.conclusion input andEquation
  change OpenTheory.StorageSize.theoremData converted ≤ _ at convertedSize
  have convertedBound : OpenTheory.StorageSize.theoremData converted ≤ 3 * budget := by omega
  have reversedImpSize := EqualityStorageBounds.symmetryResult_size converted andTerm left leftBool.symm
  change OpenTheory.StorageSize.theoremData reversedImp ≤ _ at reversedImpSize
  have reversedImpBound : OpenTheory.StorageSize.theoremData reversedImp ≤ 6 * budget := by omega
  have andProofSize := EqualityStorageBounds.eqMpResult_size reversedImp premise andTerm
  change OpenTheory.StorageSize.theoremData andProof ≤ _ at andProofSize
  have andProofBound : OpenTheory.StorageSize.theoremData andProof ≤ 8 * budget := by omega
  have bodyProofSize := EqualityStorageBounds.eqMpResult_size andExpansion.conclusion andProof pairEquation
  change OpenTheory.StorageSize.theoremData bodyProof ≤ _ at bodyProofSize
  have bodyProofBound : OpenTheory.StorageSize.theoremData bodyProof ≤ 10 * budget := by omega
  have bodyApplicationSize := EqualityStorageBounds.appResult_size bodyProof selectorProof selectedLeft selectedTruth rfl
  change OpenTheory.StorageSize.theoremData bodyApplication ≤ _ at bodyApplicationSize
  have bodyApplicationBound : OpenTheory.StorageSize.theoremData bodyApplication ≤ 16 * budget := by omega
  have leftReductionSize := EqualityStorageBounds.transResult_size leftPairBeta.conclusion leftSelectorBeta.conclusion selectedLeft right rightBool.symm
  change OpenTheory.StorageSize.theoremData leftReduction ≤ _ at leftReductionSize
  have leftReductionBound : OpenTheory.StorageSize.theoremData leftReduction ≤ 5 * budget := by omega
  have reversedLeftSize := EqualityStorageBounds.symmetryResult_size leftReduction selectedLeft right rightBool.symm
  change OpenTheory.StorageSize.theoremData reversedLeft ≤ _ at reversedLeftSize
  have reversedLeftBound : OpenTheory.StorageSize.theoremData reversedLeft ≤ 8 * budget := by omega
  have truthReductionSize := EqualityStorageBounds.transResult_size truthPairBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
  change OpenTheory.StorageSize.theoremData truthReduction ≤ _ at truthReductionSize
  have truthReductionBound : OpenTheory.StorageSize.theoremData truthReduction ≤ 5 * budget := by omega
  have joinedLeftSize := EqualityStorageBounds.transResult_size reversedLeft bodyApplication right selectedTruth rightBool
  change OpenTheory.StorageSize.theoremData joinedLeft ≤ _ at joinedLeftSize
  have joinedLeftBound : OpenTheory.StorageSize.theoremData joinedLeft ≤ 27 * budget := by omega
  have joinedTruthSize := EqualityStorageBounds.transResult_size joinedLeft truthReduction right DerivedRules.truthTerm rightBool
  change OpenTheory.StorageSize.theoremData joinedTruth ≤ _ at joinedTruthSize
  have joinedTruthBound : OpenTheory.StorageSize.theoremData joinedTruth ≤ 35 * budget := by omega
  have reversedTruthSize := EqualityStorageBounds.symmetryResult_size joinedTruth right DerivedRules.truthTerm rightBool
  change OpenTheory.StorageSize.theoremData reversedTruth ≤ _ at reversedTruthSize
  have reversedTruthBound : OpenTheory.StorageSize.theoremData reversedTruth ≤ 38 * budget := by omega
  have resultSize := EqualityStorageBounds.eqMpResult_size reversedTruth truthProof right
  change OpenTheory.StorageSize.theoremData result ≤ _ at resultSize
  have resultBound : OpenTheory.StorageSize.theoremData result ≤ 42 * budget := by omega
  have impSymmetry := EqualityStorageBounds.symmetryBlock_payload converted andTerm left leftBool.symm origin
  have leftSymmetry := EqualityStorageBounds.symmetryBlock_payload leftReduction selectedLeft right rightBool.symm origin
  have truthSymmetry := EqualityStorageBounds.symmetryBlock_payload joinedTruth right DerivedRules.truthTerm rightBool origin
  unfold EqualityStorageBounds.inputUnits at impSymmetry leftSymmetry truthSymmetry
  change GraphExpansion.graphWeight StorageSize.receiptPayload (doubleBetaBlock impExpansion origin).1 ≤ budget at impBlock
  change GraphExpansion.graphWeight StorageSize.receiptPayload (doubleBetaBlock andExpansion origin).1 ≤ budget at andBlock
  change GraphExpansion.graphWeight StorageSize.receiptPayload (doubleBetaBlock leftSelectorBeta origin).1 ≤ budget at leftSelectorBlock
  change GraphExpansion.graphWeight StorageSize.receiptPayload (doubleBetaBlock truthSelectorBeta origin).1 ≤ budget at truthSelectorBlock
  change GraphExpansion.graphWeight StorageSize.receiptPayload (betaBlock leftPairBeta origin).1 ≤ budget at leftPairBlock
  change GraphExpansion.graphWeight StorageSize.receiptPayload (betaBlock truthPairBeta origin).1 ≤ budget at truthPairBlock
  have requestsSame : (mpPlan input premise left right leftBool rightBool origin).1 =
    [⟨impExpansion.conclusion, doubleBetaBlock impExpansion origin, [], origin⟩,
     ⟨converted, primitiveBlock (.inference (.eqMp impExpansion.conclusion input)) converted origin, [2, 0], origin⟩,
     ⟨reversedImp, symmetryBlock converted andTerm left leftBool.symm origin, [3], origin⟩,
     ⟨andProof, primitiveBlock (.inference (.eqMp reversedImp premise)) andProof origin, [4, 1], origin⟩,
     ⟨andExpansion.conclusion, doubleBetaBlock andExpansion origin, [], origin⟩,
     ⟨bodyProof, primitiveBlock (.inference (.eqMp andExpansion.conclusion andProof)) bodyProof origin, [6, 5], origin⟩,
     ⟨selectorProof, primitiveBlock (.inference (.refl secondSelector)) selectorProof origin, [], origin⟩,
     ⟨bodyApplication, primitiveBlock (.inference (.mkComb bodyProof selectorProof)) bodyApplication origin, [7, 8], origin⟩,
     ⟨leftPairBeta.conclusion, betaBlock leftPairBeta origin, [], origin⟩,
     ⟨leftSelectorBeta.conclusion, doubleBetaBlock leftSelectorBeta origin, [], origin⟩,
     ⟨leftReduction, primitiveBlock (.inference (.trans leftPairBeta.conclusion leftSelectorBeta.conclusion)) leftReduction origin, [10, 11], origin⟩,
     ⟨reversedLeft, symmetryBlock leftReduction selectedLeft right rightBool.symm origin, [12], origin⟩,
     ⟨truthPairBeta.conclusion, betaBlock truthPairBeta origin, [], origin⟩,
     ⟨truthSelectorBeta.conclusion, doubleBetaBlock truthSelectorBeta origin, [], origin⟩,
     ⟨truthReduction, primitiveBlock (.inference (.trans truthPairBeta.conclusion truthSelectorBeta.conclusion)) truthReduction origin, [14, 15], origin⟩,
     ⟨joinedLeft, primitiveBlock (.inference (.trans reversedLeft bodyApplication)) joinedLeft origin, [13, 9], origin⟩,
     ⟨joinedTruth, primitiveBlock (.inference (.trans joinedLeft truthReduction)) joinedTruth origin, [17, 16], origin⟩,
     ⟨reversedTruth, symmetryBlock joinedTruth right DerivedRules.truthTerm rightBool origin, [18], origin⟩,
     ⟨truthProof, primitiveBlock (.inference (.refl identityTerm)) truthProof origin, [], origin⟩,
     ⟨result, primitiveBlock (.inference (.eqMp reversedTruth truthProof)) result origin, [19, 20], origin⟩] := by
    rfl
  rw [requestsSame]
  simp only [List.map_cons, List.map_nil]
  apply (List.sum_le_card_nsmul _ (100000 * budget) ?_).trans
  · simp only [List.length_cons, List.length_nil, Nat.nsmul_eq_mul]
    change 20 * (100000 * budget) ≤ 2000000 * budget
    omega
  · intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · rw [StorageSize.eqMp_payload]; omega
    · omega
    · rw [StorageSize.eqMp_payload]; omega
    · omega
    · rw [StorageSize.eqMp_payload]; omega
    · rw [StorageSize.refl_payload]; omega
    · rw [StorageSize.app_payload]; omega
    · omega
    · omega
    · rw [StorageSize.trans_payload]; omega
    · omega
    · omega
    · omega
    · rw [StorageSize.trans_payload]; omega
    · rw [StorageSize.trans_payload]; omega
    · rw [StorageSize.trans_payload]; omega
    · omega
    · rw [StorageSize.refl_payload]; omega
    · rw [StorageSize.eqMp_payload]; omega

/-- The checked expansion uses the same bounded executable data plan. -/
theorem mpExpansion_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    ((mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests.map
      (fun request => GraphExpansion.graphWeight StorageSize.receiptPayload request.witness.1)).sum ≤
      2000000 * payloadBudget (inputUnits input premise left right origin) := by
  rw [mpExpansion_requests]
  exact mpPlan_payload input premise left right leftBool rightBool origin

/-- Successful compilation retains exactly the concrete plan's bounded payload. -/
theorem mpTypedBlock?_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    GraphExpansion.graphWeight StorageSize.receiptPayload block.1 ≤
      2000000 * payloadBudget (inputUnits input premise left right origin) := by
  have actual := GraphExpansion.finishPlan_weight StorageSize.receiptPayload computed
  simp only [GraphExpansion.start, GraphExpansion.graphWeight, List.map_nil, List.sum_nil, zero_add] at actual
  change GraphExpansion.graphWeight StorageSize.receiptPayload block.1 =
    ((mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests.map
      (fun request => GraphExpansion.graphWeight StorageSize.receiptPayload request.witness.1)).sum at actual
  rw [actual]
  exact mpExpansion_payload policy input premise left right leftBool rightBool shape matching origin

/-- Only the actual supplied theorem and remaining ordered premises are
needed to bound an implication-elimination chain. -/
def chainInputUnits (input : Theorem) (premises : List Theorem) (origin : Origin) : Nat :=
  1 + OpenTheory.StorageSize.theoremData input +
    (premises.map OpenTheory.StorageSize.theoremData).sum + StorageSize.origin origin

/-- Coarse coefficient for the fixed primitive MP expansion. -/
def payloadCoefficient : Nat := 2000000 * 1000000000000000000000000000000 * 20 ^ 4

/-- A fixed-length MP chain has a quartic payload bound. The coefficient
records its sequential packet growth, rather than charging an unbounded state. -/
def chainCoefficient : Nat → Nat
  | 0 => 0
  | n + 1 => payloadCoefficient + 16 ^ 4 * chainCoefficient n


theorem chainCoefficient_mono {left right : Nat} (ordered : left ≤ right) :
    chainCoefficient left ≤ chainCoefficient right := by
  apply (monotone_nat_of_le_succ ?_) ordered
  intro n
  simp only [chainCoefficient]
  omega

theorem chainInputUnits_step (input premise : Theorem) (left right : CanonicalTerm)
    (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (rest : List Theorem) (origin : Origin) :
    chainInputUnits (mpResult input premise right) rest origin ≤
      16 * chainInputUnits input (premise :: rest) origin := by
  have result := mpResult_storage input premise right
  have consequent := right_storage_le input left right rightBool shape
  simp only [chainInputUnits, List.map_cons, List.sum_cons]
  omega

/-- The primitive MP block is bounded by the complete actual two-theorem
packet. Its typed parser operands need no independent size parameter. -/
theorem mpTypedBlock?_actual_payload (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    GraphExpansion.graphWeight StorageSize.receiptPayload block.1 ≤
      payloadCoefficient * chainInputUnits input [premise] origin ^ 4 := by
  have payload := mpTypedBlock?_payload policy input premise left right leftBool rightBool shape matching origin computed
  have actual := inputUnits_le_actual input premise left right rightBool shape matching origin
  have normalized : inputUnits input premise left right origin ≤ 20 * chainInputUnits input [premise] origin := by
    simpa [chainInputUnits] using actual
  calc
    GraphExpansion.graphWeight StorageSize.receiptPayload block.1 ≤
        2000000 * payloadBudget (inputUnits input premise left right origin) := payload
    _ ≤ 2000000 * payloadBudget (20 * chainInputUnits input [premise] origin) := by
      unfold payloadBudget
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left normalized 4))
    _ = payloadCoefficient * chainInputUnits input [premise] origin ^ 4 := by
      unfold payloadCoefficient payloadBudget
      ring

end Mettapedia.Languages.HOLLight.ImplicationStorageBounds

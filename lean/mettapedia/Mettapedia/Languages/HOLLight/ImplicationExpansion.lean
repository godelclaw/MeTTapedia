import Mettapedia.Languages.HOLLight.EqualityExpansion
import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives

/-!
# Explicit implication elimination in HOL Light

The defined implication and conjunction are expanded using source BETA/INST,
REFL, MK_COMB, TRANS and EQ_MP. The two incoming theorem roots remain shared;
the emitted graph retains full axiom and hypothesis sets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ImplicationExpansion

open Mettapedia.Languages.OpenTheory
open GraphExpansion EqualityExpansion PrimitiveTransport
open ProofExecution (Origin)
open ExcludedMiddle (impDB impAppDB andDB boolBinaryTy)
open DerivedRules (andAppDB andBodyDB selectSecondDB)
open PrimitiveSentences (truthDB identityBool)

/-- Canonical inlined conjunction of two checked boolean terms. -/
def conjunction (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : CanonicalTerm :=
  ⟨andAppDB left.term right.term, Ty.bool,
    DerivedRules.inferType_andAppDB (leftBool ▸ left.checked) (rightBool ▸ right.checked)⟩

def implication (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : CanonicalTerm :=
  ⟨impAppDB left.term right.term, Ty.bool,
    DerivedRules.inferType_impAppDB (leftBool ▸ left.checked) (rightBool ▸ right.checked)⟩

/-- The body of the curried conjunction definition. -/
def conjunctionBody : DBTerm :=
  CanonicalTerm.equalityDB (.function boolBinaryTy Ty.bool)
    (.abs boolBinaryTy (.app (.app (.bound 0) (.bound 2)) (.bound 1)))
    (.abs boolBinaryTy (.app (.app (.bound 0) truthDB) truthDB))

theorem conjunctionBody_checked : conjunctionBody.inferType [Ty.bool, Ty.bool] = some Ty.bool := by
  simp [conjunctionBody, boolBinaryTy, CanonicalTerm.equalityDB, DBTerm.inferType,
    PrimitiveSentences.truthDB, PrimitiveSentences.identityBool, Ty.equality]

/-- The body of the curried implication definition. -/
def implicationBody : DBTerm :=
  CanonicalTerm.equalityDB Ty.bool (andAppDB (.bound 1) (.bound 0)) (.bound 1)

theorem implicationBody_checked : implicationBody.inferType [Ty.bool, Ty.bool] = some Ty.bool :=
  DBTerm.inferType_equalityDB (DerivedRules.inferType_andAppDB (by simp) (by simp)) (by simp)

def secondSelector : CanonicalTerm :=
  ⟨selectSecondDB, boolBinaryTy, DerivedRules.inferType_selectSecondDB⟩

def pairTerm (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : CanonicalTerm :=
  ⟨.abs boolBinaryTy (.app (.app (.bound 0) left.term) right.term),
    .function boolBinaryTy Ty.bool,
    DBTerm.inferType_abs_of (DBTerm.inferType_app_of (DBTerm.inferType_app_of
      (by simp [boolBinaryTy]) (DBTerm.inferType_weaken_empty (leftBool ▸ left.checked) _))
      (DBTerm.inferType_weaken_empty (rightBool ▸ right.checked) _))⟩

def selectedPair (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : CanonicalTerm :=
  CanonicalTerm.applicationOfFunction (pairTerm left right leftBool rightBool) secondSelector Ty.bool (by simp [pairTerm, secondSelector])

def selectorApplication (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : CanonicalTerm :=
  ⟨.app (.app selectSecondDB left.term) right.term, Ty.bool,
    (DerivedRules.inferType_binary_iff DerivedRules.inferType_selectSecondDB).mpr
      ⟨leftBool ▸ left.checked, rightBool ▸ right.checked, rfl⟩⟩

/-- The beta pair used by every conjunction occurrence. -/
def conjunctionBeta (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : DoubleBetaExpansion :=
  doubleBetaExpansion Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked left right leftBool rightBool

/-- The beta pair used by every implication occurrence. -/
def implicationBeta (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : DoubleBetaExpansion :=
  doubleBetaExpansion Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked left right leftBool rightBool

def selectorBeta (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : DoubleBetaExpansion :=
  doubleBetaExpansion Ty.bool Ty.bool Ty.bool (.bound 0) (by simp) left right leftBool rightBool

def pairBeta (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) : BetaExpansion :=
  betaExpansion boolBinaryTy (.app (.app (.bound 0) left.term) right.term) Ty.bool
    (DBTerm.inferType_app_of (DBTerm.inferType_app_of (by simp [boolBinaryTy])
      (DBTerm.inferType_weaken_empty (leftBool ▸ left.checked) _))
      (DBTerm.inferType_weaken_empty (rightBool ▸ right.checked) _)) secondSelector (show secondSelector.ty = boolBinaryTy from rfl)

theorem conjunctionBeta_view (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    CanonicalTerm.EqualityViewSemantics (conjunctionBeta left right leftBool rightBool).conclusion.sequent.concl
      (conjunction left right leftBool rightBool)
      (CanonicalTerm.equalityOfSameType (pairTerm left right leftBool rightBool)
        (pairTerm DerivedRules.truthTerm DerivedRules.truthTerm (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)) rfl) := by
  refine ⟨rfl, ?_⟩
  have shape := (doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
    left right leftBool rightBool).2.2
  change (conjunctionBeta left right leftBool rightBool).conclusion.sequent.concl.term = _
  simp only [conjunctionBeta]
  rw [shape]
  simp [conjunctionBody, conjunction, andAppDB, andDB, pairTerm, CanonicalTerm.equalityOfSameType,
    CanonicalTerm.equalityDB, DBTerm.instantiateAt, DBTerm.instantiateAt_closed (leftBool ▸ left.checked),
    DerivedRules.truthTerm, DerivedRules.instantiateAt_truthDB]

theorem implicationBeta_view (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    CanonicalTerm.EqualityViewSemantics (implicationBeta left right leftBool rightBool).conclusion.sequent.concl
      (implication left right leftBool rightBool)
      (CanonicalTerm.equalityOfSameType (conjunction left right leftBool rightBool) left leftBool.symm) := by
  refine ⟨rfl, ?_⟩
  have shape := (doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked
    left right leftBool rightBool).2.2
  change (implicationBeta left right leftBool rightBool).conclusion.sequent.concl.term = _
  simp only [implicationBeta]
  rw [shape]
  simp [implicationBody, implication, impAppDB, impDB, conjunction, andAppDB,
    CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, DBTerm.instantiateAt,
    DBTerm.instantiateAt_closed (leftBool ▸ left.checked)]

theorem selectorBeta_view (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    CanonicalTerm.EqualityViewSemantics (selectorBeta left right leftBool rightBool).conclusion.sequent.concl
      (selectorApplication left right leftBool rightBool) right := by
  refine ⟨rightBool.symm, ?_⟩
  have shape := (doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
    left right leftBool rightBool).2.2
  change (selectorBeta left right leftBool rightBool).conclusion.sequent.concl.term = _
  simp only [selectorBeta]
  rw [shape]
  simp [selectorApplication, selectSecondDB, DBTerm.instantiateAt]

theorem pairBeta_view (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool) :
    CanonicalTerm.EqualityViewSemantics (pairBeta left right leftBool rightBool).conclusion.sequent.concl
      (selectedPair left right leftBool rightBool) (selectorApplication left right leftBool rightBool) := by
  unfold pairBeta
  rw [betaExpansion_conclusion]
  refine ⟨rfl, ?_⟩
  simp [Theorem.emptyResult, betaRedex, betaReduced, selectedPair, pairTerm, secondSelector, selectorApplication,
    CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType, DBTerm.instantiateAt,
    DBTerm.instantiateAt_closed (leftBool ▸ left.checked), DBTerm.instantiateAt_closed (rightBool ▸ right.checked)]


/-- MP's exact result retains both incoming dependency sets. -/
def mpResult (input premise : Theorem) (right : CanonicalTerm) : Theorem :=
  Theorem.unionResult input premise (input.sequent.hyp ∪ premise.sequent.hyp) right

/-- The implication-elimination plan is made only of existing checked graph blocks. -/
structure MpExpansion (policy : AxiomPolicy) [DecidablePred policy] (input premise : Theorem) where
  requests : List BlockRequest
  conclusion : Theorem
  checked : LocallyChecked policy #[input, premise] requests

/-- The executable implication-elimination data is independent of its
admission proof. Its two external roots and twenty macro occurrences are
shared unchanged by the checked builder and the storage account. -/
def mpPlan (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (origin : Origin) : List BlockRequest × Theorem := by
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
  let requests : List BlockRequest :=
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
     ⟨result, primitiveBlock (.inference (.eqMp reversedTruth truthProof)) result origin, [19, 20], origin⟩]
  exact ⟨requests, result⟩

set_option maxHeartbeats 3000000 in
def mpExpansion (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) : MpExpansion policy input premise := by
  let andTerm := conjunction left right leftBool rightBool
  let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
  let impExpansion := implicationBeta left right leftBool rightBool
  have impEqual : implication left right leftBool rightBool = input.sequent.concl :=
    CanonicalTerm.ext_term shape.symm
  have impView : CanonicalTerm.EqualityViewSemantics impExpansion.conclusion.sequent.concl
      input.sequent.concl andEquation := by
    simpa only [impEqual] using implicationBeta_view left right leftBool rightBool
  let converted := eqMpResult impExpansion.conclusion input andEquation
  have convertedChecked : checkEqMp impExpansion.conclusion input = some converted :=
    eqMpResult_checked _ _ _ _ impView rfl
  let reversedImp := symmetryResult converted andTerm left leftBool.symm
  let andProof := eqMpResult reversedImp premise andTerm
  have andChecked : checkEqMp reversedImp premise = some andProof :=
    eqMpResult_checked _ _ left andTerm (equality_view left andTerm leftBool) matching.symm
  let andExpansion := conjunctionBeta left right leftBool rightBool
  let pairLeft := pairTerm left right leftBool rightBool
  let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm
    (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)
  let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
  let bodyProof := eqMpResult andExpansion.conclusion andProof pairEquation
  have bodyChecked : checkEqMp andExpansion.conclusion andProof = some bodyProof :=
    eqMpResult_checked _ _ andTerm pairEquation (conjunctionBeta_view left right leftBool rightBool) rfl
  let selectedLeft := selectedPair left right leftBool rightBool
  let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm
    (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)
  let selectorProof := reflexivity secondSelector
  let bodyApplication := appResult bodyProof selectorProof selectedLeft selectedTruth rfl
  have bodyApplicationChecked : checkApp bodyProof selectorProof = some bodyApplication := by
    apply appResult_checked _ _ pairLeft pairTruth secondSelector secondSelector selectedLeft selectedTruth rfl
    · exact equality_view pairLeft pairTruth rfl
    · exact equality_view secondSelector secondSelector rfl
    · exact CanonicalTerm.applicationOfFunction_semantics _ _ _ _
    · exact CanonicalTerm.applicationOfFunction_semantics _ _ _ _
  let leftPairBeta := pairBeta left right leftBool rightBool
  let leftSelectorBeta := selectorBeta left right leftBool rightBool
  let selectedLeftArguments := selectorApplication left right leftBool rightBool
  let leftReduction := transResult leftPairBeta.conclusion leftSelectorBeta.conclusion selectedLeft right rightBool.symm
  have leftReductionChecked : checkTrans leftPairBeta.conclusion leftSelectorBeta.conclusion = some leftReduction :=
    transResult_checked _ _ selectedLeft selectedLeftArguments right rightBool.symm
      (pairBeta_view left right leftBool rightBool) (selectorBeta_view left right leftBool rightBool)
  let reversedLeft := symmetryResult leftReduction selectedLeft right rightBool.symm
  let truthPairBeta := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm
    (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)
  let truthSelectorBeta := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm
    (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)
  let selectedTruthArguments := selectorApplication DerivedRules.truthTerm DerivedRules.truthTerm
    (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl)
  let truthReduction := transResult truthPairBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
  have truthReductionChecked : checkTrans truthPairBeta.conclusion truthSelectorBeta.conclusion = some truthReduction :=
    transResult_checked _ _ selectedTruth selectedTruthArguments DerivedRules.truthTerm rfl
      (pairBeta_view _ _ (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl))
      (selectorBeta_view _ _ (show DerivedRules.truthTerm.ty = Ty.bool from rfl) (show DerivedRules.truthTerm.ty = Ty.bool from rfl))
  let joinedLeft := transResult reversedLeft bodyApplication right selectedTruth rightBool
  have joinedLeftChecked : checkTrans reversedLeft bodyApplication = some joinedLeft :=
    transResult_checked _ _ right selectedLeft selectedTruth rightBool
      (equality_view right selectedLeft rightBool) (equality_view selectedLeft selectedTruth rfl)
  let joinedTruth := transResult joinedLeft truthReduction right DerivedRules.truthTerm rightBool
  have joinedTruthChecked : checkTrans joinedLeft truthReduction = some joinedTruth :=
    transResult_checked _ _ right selectedTruth DerivedRules.truthTerm rightBool
      (equality_view right selectedTruth rightBool) (equality_view selectedTruth DerivedRules.truthTerm rfl)
  let reversedTruth := symmetryResult joinedTruth right DerivedRules.truthTerm rightBool
  let identityTerm : CanonicalTerm :=
    ⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
  let truthProof := reflexivity identityTerm
  have truthConclusion : truthProof.sequent.concl = DerivedRules.truthTerm :=
    CanonicalTerm.ext_term rfl
  let result := eqMpResult reversedTruth truthProof right
  have resultChecked : checkEqMp reversedTruth truthProof = some result :=
    eqMpResult_checked _ _ DerivedRules.truthTerm right
      (equality_view DerivedRules.truthTerm right rightBool.symm) truthConclusion.symm
  let requests : List BlockRequest :=
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
     ⟨result, primitiveBlock (.inference (.eqMp reversedTruth truthProof)) result origin, [19, 20], origin⟩]
  refine ⟨(mpPlan input premise left right leftBool rightBool origin).1,
    (mpPlan input premise left right leftBool rightBool origin).2, ?_⟩
  change LocallyChecked policy #[input, premise] requests
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy impExpansion origin
  apply LocallyChecked.cons (premises := [impExpansion.conclusion, input]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.eqMp impExpansion.conclusion input)) converted origin convertedChecked
  apply LocallyChecked.cons (premises := [converted]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact symmetryBlock_checked policy converted andTerm left leftBool.symm
      (equality_view andTerm left leftBool.symm) origin
  apply LocallyChecked.cons (premises := [reversedImp, premise]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.eqMp reversedImp premise)) andProof origin andChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy andExpansion origin
  apply LocallyChecked.cons (premises := [andExpansion.conclusion, andProof]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.eqMp andExpansion.conclusion andProof)) bodyProof origin bodyChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl secondSelector)) selectorProof origin (reflexivity_checked secondSelector)
  apply LocallyChecked.cons (premises := [bodyProof, selectorProof]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.mkComb bodyProof selectorProof)) bodyApplication origin bodyApplicationChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy leftPairBeta origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy leftSelectorBeta origin
  apply LocallyChecked.cons (premises := [leftPairBeta.conclusion, leftSelectorBeta.conclusion]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.trans leftPairBeta.conclusion leftSelectorBeta.conclusion)) leftReduction origin leftReductionChecked
  apply LocallyChecked.cons (premises := [leftReduction]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact symmetryBlock_checked policy leftReduction selectedLeft right rightBool.symm
      (equality_view selectedLeft right rightBool.symm) origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy truthPairBeta origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy truthSelectorBeta origin
  apply LocallyChecked.cons (premises := [truthPairBeta.conclusion, truthSelectorBeta.conclusion]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.trans truthPairBeta.conclusion truthSelectorBeta.conclusion)) truthReduction origin truthReductionChecked
  apply LocallyChecked.cons (premises := [reversedLeft, bodyApplication]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.trans reversedLeft bodyApplication)) joinedLeft origin joinedLeftChecked
  apply LocallyChecked.cons (premises := [joinedLeft, truthReduction]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.trans joinedLeft truthReduction)) joinedTruth origin joinedTruthChecked
  apply LocallyChecked.cons (premises := [joinedTruth]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact symmetryBlock_checked policy joinedTruth right DerivedRules.truthTerm rightBool
      (equality_view right DerivedRules.truthTerm rightBool) origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl identityTerm)) truthProof origin (reflexivity_checked identityTerm)
  apply LocallyChecked.cons (premises := [reversedTruth, truthProof]) (by simp [Mettapedia.Logic.DerivationGraph.lookupPremises])
  · exact primitiveBlock_checked (.inference (.eqMp reversedTruth truthProof)) result origin resultChecked
  exact .nil _


/-- Checked admission retains exactly the independently computed plan. -/
theorem mpExpansion_requests (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    (mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests =
      (mpPlan input premise left right leftBool rightBool origin).1 := rfl

set_option maxHeartbeats 3000000 in
theorem mpExpansion_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    (mpExpansion policy input premise left right leftBool rightBool shape matching origin).conclusion =
      mpResult input premise right := by
  apply Theorem.ext
  · simp [mpExpansion, mpPlan, eqMpResult, appResult, transResult, symmetryResult, reflexivity,
      implicationBeta, conjunctionBeta, selectorBeta, pairBeta, doubleBetaExpansion,
      betaExpansion, substituteTheorem,
      TypeCorrectTermSubstitution.applyHypotheses, Theorem.unionResult, Theorem.emptyResult,
      Theorem.preserveAxiomsResult, mpResult]
  · apply Sequent.ext
    · simp [mpExpansion, mpPlan, eqMpResult, appResult, transResult, symmetryResult, reflexivity,
        implicationBeta, conjunctionBeta, selectorBeta, pairBeta, doubleBetaExpansion,
        betaExpansion, substituteTheorem,
      TypeCorrectTermSubstitution.applyHypotheses, Theorem.unionResult, Theorem.emptyResult,
        Theorem.preserveAxiomsResult, mpResult]
    · rfl

/-- Compile actual implication-elimination requests with two external roots. -/
def mpTypedBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) : Option ProofSystem.Certificate :=
  finishPlan policy (start [input, premise]) #[0, 1]
    (mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests 21

set_option maxHeartbeats 3000000 in
theorem mpTypedBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    ∃ block, mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block ∧
      BlockChecked policy [input, premise] (mpResult input premise right) block := by
  let expansion := mpExpansion policy input premise left right leftBool rightBool shape matching origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[input, premise]) (roots := #[0, 1]) (start_checked policy [input, premise]) rfl
    expansion.checked (index := 21) (conclusion := expansion.conclusion) (by rfl)
  refine ⟨block, computed, ?_⟩
  simpa only [expansion, mpExpansion_conclusion] using checked

set_option maxHeartbeats 3000000 in
theorem mpExpansion_node_count (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    (((mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests).map
      (fun request => request.witness.1.length)).sum = 58 := by
  simp [mpExpansion, mpPlan, doubleBetaBlock, betaBlock, symmetryBlock, primitiveBlock]

theorem mpTypedBlock?_size (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    block.1.length = 58 := by
  have count := finishPlan_size computed
  simpa [start, mpExpansion_node_count] using count


/-- Recognized operands of the actual inlined boolean implication definition. -/
structure ImplicationOperands (input : CanonicalTerm) where
  left : CanonicalTerm
  right : CanonicalTerm
  leftBool : left.ty = Ty.bool
  rightBool : right.ty = Ty.bool
  shape : input.term = impAppDB left.term right.term

/-- Parse the curried implication shape, rechecking both operand sorts. -/
def implicationOperands? (input : CanonicalTerm) : Option (ImplicationOperands input) :=
  match shape : input.term with
  | .app (.app operator left) right =>
      if symbol : DBTerm.same operator impDB = true then
        match checkedLeft : left.inferType [] with
        | some leftType =>
          match checkedRight : right.inferType [] with
          | some rightType =>
            if leftBool : Ty.same leftType Ty.bool = true then
              if rightBool : Ty.same rightType Ty.bool = true then
                some ⟨⟨left, Ty.bool,
                    checkedLeft.trans (congrArg some ((Ty.same_eq_true_iff _ _).mp leftBool))⟩,
                  ⟨right, Ty.bool,
                    checkedRight.trans (congrArg some ((Ty.same_eq_true_iff _ _).mp rightBool))⟩,
                  rfl, rfl, by rw [shape, (DBTerm.same_eq_true_iff _ _).mp symbol]; rfl⟩
              else none
            else none
          | none => none
        | none => none
      else none
  | _ => none

theorem implicationOperands?_complete (input : CanonicalTerm) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.term = impAppDB left.term right.term) :
    implicationOperands? input = some ⟨left, right, leftBool, rightBool, shape⟩ := by
  cases left with
  | mk leftTerm leftType checkedLeft =>
    cases right with
    | mk rightTerm rightType checkedRight =>
      dsimp at leftBool rightBool
      subst leftType rightType
      cases input with
      | mk inputTerm inputType checkedInput =>
        dsimp at shape
        subst inputTerm
        unfold implicationOperands?
        simp only [impAppDB]
        have sameSymbol := (DBTerm.same_eq_true_iff impDB impDB).mpr rfl
        rw [dif_pos sameSymbol]
        split
        · rename_i type actual
          have equal := Option.some.inj (actual.symm.trans checkedLeft)
          subst type
          split
          · rename_i type actual
            have equal := Option.some.inj (actual.symm.trans checkedRight)
            subst type
            have sameBool := (Ty.same_eq_true_iff Ty.bool Ty.bool).mpr rfl
            rw [dif_pos sameBool, dif_pos sameBool]
          · rename_i rejected
            rw [checkedRight] at rejected
            contradiction
        · rename_i rejected
          rw [checkedLeft] at rejected
          contradiction

/-- Raw MP result discovery checks the actual implication and its antecedent. -/
def mpResult? (input premise : Theorem) : Option Theorem := do
  let operands ← implicationOperands? input.sequent.concl
  if _same : CanonicalTerm.same premise.sequent.concl operands.left = true then
    pure (mpResult input premise operands.right)
  else none

/-- Raw MP graph generation uses the same checked shape and operand matching. -/
def mpBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (origin : Origin) : Option ProofSystem.Certificate := do
  let operands ← implicationOperands? input.sequent.concl
  if same : CanonicalTerm.same premise.sequent.concl operands.left = true then
    mpTypedBlock? policy input premise operands.left operands.right operands.leftBool operands.rightBool
      operands.shape ((CanonicalTerm.same_eq_true_iff _ _).mp same) origin
  else none

theorem mpResult?_complete (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) :
    mpResult? input premise = some (mpResult input premise right) := by
  have parsed := implicationOperands?_complete input.sequent.concl left right leftBool rightBool shape
  simp [mpResult?, parsed, matching]

theorem mpBlock?_complete (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    ∃ block, mpBlock? policy input premise origin = some block ∧
      BlockChecked policy [input, premise] (mpResult input premise right) block := by
  obtain ⟨block, computed, checked⟩ := mpTypedBlock?_checked policy input premise left right leftBool rightBool shape matching origin
  have parsed := implicationOperands?_complete input.sequent.concl left right leftBool rightBool shape
  refine ⟨block, ?_, checked⟩
  simpa [mpBlock?, parsed, matching] using computed

theorem mpBlock?_checked_of_result (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (origin : Origin) {result : Theorem}
    (found : mpResult? input premise = some result) :
    ∃ block, mpBlock? policy input premise origin = some block ∧ BlockChecked policy [input, premise] result block := by
  cases parsed : implicationOperands? input.sequent.concl with
  | none => simp [mpResult?, parsed] at found
  | some operands =>
      by_cases same : CanonicalTerm.same premise.sequent.concl operands.left = true
      · have matching := (CanonicalTerm.same_eq_true_iff _ _).mp same
        have expected : mpResult input premise operands.right = result := by
          simpa [mpResult?, parsed, matching] using found
        rw [← expected]
        exact mpBlock?_complete policy input premise operands.left operands.right operands.leftBool operands.rightBool
          operands.shape ((CanonicalTerm.same_eq_true_iff _ _).mp same) origin
      · have mismatching : premise.sequent.concl ≠ operands.left :=
          fun equal => same ((CanonicalTerm.same_eq_true_iff _ _).mpr equal)
        simp [mpResult?, parsed, mismatching] at found

theorem mpBlock?_size (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpBlock? policy input premise origin = some block) : block.1.length = 58 := by
  cases parsed : implicationOperands? input.sequent.concl with
  | none => simp [mpBlock?, parsed] at computed
  | some operands =>
      by_cases same : CanonicalTerm.same premise.sequent.concl operands.left = true
      · have matching := (CanonicalTerm.same_eq_true_iff _ _).mp same
        have emitted : mpTypedBlock? policy input premise operands.left operands.right operands.leftBool operands.rightBool
            operands.shape ((CanonicalTerm.same_eq_true_iff _ _).mp same) origin = some block := by
          simpa [mpBlock?, parsed, matching] using computed
        exact mpTypedBlock?_size _ _ _ _ _ _ _ _ _ _ emitted
      · have mismatching : premise.sequent.concl ≠ operands.left :=
          fun equal => same ((CanonicalTerm.same_eq_true_iff _ _).mpr equal)
        simp [mpBlock?, parsed, mismatching] at computed

theorem mpBlock?_sound (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpBlock? policy input premise origin = some block) :
    ∃ result, mpResult? input premise = some result ∧ BlockChecked policy [input, premise] result block := by
  cases parsed : implicationOperands? input.sequent.concl with
  | none => simp [mpBlock?, parsed] at computed
  | some operands =>
      by_cases same : CanonicalTerm.same premise.sequent.concl operands.left = true
      · have matching := (CanonicalTerm.same_eq_true_iff _ _).mp same
        let result := mpResult input premise operands.right
        have found : mpResult? input premise = some result := by simp [mpResult?, parsed, matching, result]
        obtain ⟨actual, emitted, checked⟩ := mpBlock?_checked_of_result policy input premise origin found
        have actualEqual : actual = block := Option.some.inj (emitted.symm.trans computed)
        exact ⟨result, found, actualEqual ▸ checked⟩
      · have mismatching : premise.sequent.concl ≠ operands.left :=
          fun equal => same ((CanonicalTerm.same_eq_true_iff _ _).mpr equal)
        simp [mpBlock?, parsed, mismatching] at computed

/-- A well-formed implication still refuses a different antecedent theorem. -/
theorem mpBlock?_antecedent_refused (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (mismatching : premise.sequent.concl ≠ left) (origin : Origin) :
    mpBlock? policy input premise origin = none := by
  have parsed := implicationOperands?_complete input.sequent.concl left right leftBool rightBool shape
  simp [mpBlock?, parsed, mismatching]


theorem mpExpansion_origins (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) :
    (mpExpansion policy input premise left right leftBool rightBool shape matching origin).requests.flatMap
      (fun request => request.witness.1.map (·.origin)) = List.replicate 58 origin := by
  simp [mpExpansion, mpPlan, doubleBetaBlock, betaBlock, symmetryBlock, primitiveBlock,
    List.replicate_succ, List.replicate_zero]

theorem mpTypedBlock?_origins (policy : AxiomPolicy) [DecidablePred policy]
    (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (shape : input.sequent.concl.term = impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (origin : Origin) {block : ProofSystem.Certificate}
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    block.1.map (·.origin) = List.replicate 58 origin := by
  have preserved := finishPlan_witnesses computed
  have origins := congrArg (List.map (fun pair => pair.2)) preserved
  simpa [start, List.map_map, Function.comp_def, List.map_flatMap, mpExpansion_origins] using origins

namespace Controls

open Mettapedia.Logic.DerivationGraph

def left : CanonicalTerm := SequentExamples.boolVariable "p"
def right : CanonicalTerm := SequentExamples.boolVariable "q"
def implicationTerm : CanonicalTerm := implication left right rfl rfl
def implicationAssumed : Theorem := Theorem.emptyResult {implicationTerm} implicationTerm
def antecedentAssumed : Theorem := Theorem.emptyResult {left} left

def initialNodes (origin : Origin) : List ProofExecution.Receipt :=
  [⟨implicationAssumed, .inference (.assume implicationTerm), [], origin⟩,
   ⟨antecedentAssumed, .inference (.assume left), [], origin⟩]

theorem initial_checked (origin : Origin) :
    replay (ruleWitness emptyAxiomPolicy) (initialNodes origin) = some #[implicationAssumed, antecedentAssumed] := by
  have length : (initialNodes origin).length = 2 := rfl
  have implicationCheck : checkAssume implicationTerm = some implicationAssumed :=
    (checkAssume_eq_some_iff _ _).mpr ⟨rfl, rfl, rfl, rfl⟩
  have antecedentCheck : checkAssume left = some antecedentAssumed :=
    (checkAssume_eq_some_iff _ _).mpr ⟨rfl, rfl, rfl, rfl⟩
  have first : (initialNodes origin)[0].replay (ruleWitness emptyAxiomPolicy) #[] = some #[implicationAssumed] := by
    apply (ProofSystem.node_replay_iff _ _ _ _).mpr
    exact ⟨rfl, implicationCheck, rfl⟩
  have second : (initialNodes origin)[1].replay (ruleWitness emptyAxiomPolicy) #[implicationAssumed] =
      some #[implicationAssumed, antecedentAssumed] := by
    apply (ProofSystem.node_replay_iff _ _ _ _).mpr
    exact ⟨rfl, antecedentCheck, rfl⟩
  change replayFrom (ruleWitness emptyAxiomPolicy) #[] [(initialNodes origin)[0], (initialNodes origin)[1]] = _
  simp [replayFrom, first, second]

/-- Both supplied proofs are genuine ASSUME nodes, followed by the generated
58-node MP graph. The public HOL Light checker accepts the complete graph. -/
def implicationGraph? (origin : Origin) : Option ProofSystem.Certificate := do
  let block ← mpBlock? emptyAxiomPolicy implicationAssumed antecedentAssumed origin
  let expanded := expandBlock [0, 1] 2 block
  pure (initialNodes origin ++ expanded.1, expanded.2)

theorem implicationGraph_checked (origin : Origin) :
    ∃ certificate, implicationGraph? origin = some certificate ∧ certificate.1.length = 60 ∧
      (ProofSystem.checker emptyAxiomPolicy).check
        (mpResult implicationAssumed antecedentAssumed right) certificate = true := by
  obtain ⟨block, computed, checked⟩ := mpBlock?_complete emptyAxiomPolicy implicationAssumed antecedentAssumed
    left right rfl rfl rfl rfl origin
  let expanded := expandBlock [0, 1] 2 block
  let certificate : ProofSystem.Certificate := (initialNodes origin ++ expanded.1, expanded.2)
  have accepted := appendBlock_accepted (initial_checked origin)
    (show lookupPremises #[implicationAssumed, antecedentAssumed] [0, 1] =
      some [implicationAssumed, antecedentAssumed] from rfl) checked
  refine ⟨certificate, ?_, ?_, accepted⟩
  · simp [implicationGraph?, computed, certificate, expanded]
  · simp [certificate, initialNodes, expanded, expandBlock, mpBlock?_size _ _ _ _ computed]

/-- Replacing the antecedent `p` by a proof of `q` is refused. -/
theorem different_antecedent_refused (origin : Origin) :
    mpBlock? emptyAxiomPolicy implicationAssumed (Theorem.emptyResult {right} right) origin = none :=
  mpBlock?_antecedent_refused _ _ _ left right rfl rfl rfl (by
    intro equal
    have same := congrArg (fun term : CanonicalTerm => term.term) equal
    simp [Theorem.emptyResult, left, right, SequentExamples.boolVariable, Name.global] at same) origin

/-- A bare boolean variable is not silently interpreted as an implication. -/
theorem missing_implication_refused (origin : Origin) :
    mpBlock? emptyAxiomPolicy antecedentAssumed antecedentAssumed origin = none := by
  rfl

end Controls

namespace Emission

open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open ProofDataEncoding
open Mettapedia.Logic.DerivationGraph
open _root_.Computability Turing StateTransition Polynomial

/-- The selected-pair body has no free variable names when its two operands
are closed data representations, so its original fresh binder is fixed. -/
def pairNeedle : SourceVar := betaNeedle boolBinaryTy (.bound 0)

theorem pairNeedle_same (left right : CanonicalTerm)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = []) :
    betaNeedle boolBinaryTy (.app (.app (.bound 0) left.term) right.term) = pairNeedle := by
  simp [betaNeedle, freeNames, leftEmpty, rightEmpty, pairNeedle]

/-- The original named scanner retains each complete operand under the
original pair binder; this theorem does not invent a new source syntax. -/
theorem pairSource_exact (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftSource rightSource : SourceTerm)
    (leftNamed : named? left.term [pairNeedle] = some leftSource)
    (rightNamed : named? right.term [pairNeedle] = some rightSource) :
    (pairBeta left right leftBool rightBool).source.source =
      .app (.abs pairNeedle.name boolBinaryTy
        (.app (.app (.var pairNeedle.name boolBinaryTy) leftSource) rightSource)) (.var pairNeedle.name boolBinaryTy) := by
  simp only [pairBeta, EqualityExpansion.Emission.betaExpansion_source_exact, betaSource]
  simp only [pairNeedle_same left right leftEmpty rightEmpty]
  congr 3
  apply Option.some.inj
  rw [← TemplateInstantiationMachine.Named.named_computed]
  dsimp only [pairNeedle] at leftNamed rightNamed
  simp [named?, leftNamed, rightNamed, pairNeedle]
  all_goals rfl

/-- The selected-pair BETA/INST block depends on both operand fields.
Its binder, selector witness and type remain the original fixed definitions. -/
def pairNodes : List (Mettapedia.Logic.DerivationGraph.Node
    (Indexed.Template Alphabet 5) (Indexed.Template Alphabet 5)
    (Indexed.Template Alphabet 5)) :=
  let left : Indexed.Template Alphabet 5 := [.inr 0]
  let right : Indexed.Template Alphabet 5 := [.inr 1]
  let leftSource : Indexed.Template Alphabet 5 := [.inr 2]
  let rightSource : Indexed.Template Alphabet 5 := [.inr 3]
  let origin : Indexed.Template Alphabet 5 := [.inr 4]
  let needleTerm := Templates.literal (putTerm (.free pairNeedle))
  let needleSource := Templates.literal (putSourceTerm (.var pairNeedle.name boolBinaryTy))
  let body := Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) left) right
  let abstraction := Templates.pair (Templates.literal (.atom 4))
    (Templates.pair (Templates.literal (putTy boolBinaryTy)) body)
  let namedBody := Templates.sourceApplication (Templates.sourceApplication needleSource leftSource) rightSource
  let source := Templates.pair
    (Templates.sourceApplication (Templates.sourceAbstraction pairNeedle.name boolBinaryTy namedBody) needleSource)
    (Templates.literal (putTy Ty.bool))
  let intermediate := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality Ty.bool
      (Templates.application abstraction needleTerm)
      (Templates.application (Templates.application needleTerm left) right)))
  let selector := Templates.literal (putTerm selectSecondDB)
  let final := Templates.theoremTemplate ∅ ∅
    (Templates.canonical Ty.bool (Templates.equality Ty.bool
      (Templates.application abstraction selector)
      (Templates.application (Templates.application selector left) right)))
  let entries := Templates.pair
    (Templates.literal (termMapletCodec.put
      (checkedSource secondSelector, .var pairNeedle.name boolBinaryTy)))
    (Templates.literal (.atom 0))
  [⟨intermediate, EqualityExpansion.Emission.unaryRequest 4 source, [], origin⟩,
   ⟨final, EqualityExpansion.Emission.unaryRequest 9 (Templates.pair entries intermediate), [0], origin⟩]

def pairTemplate : Indexed.Template Alphabet 5 :=
  EqualityExpansion.Emission.certificateTemplate (pairNodes, 1)

/-- Operand representatives are supplied for the original pair binder
context. Their byte fields may differ from the empty-context representative. -/
def pairFields (left right : CanonicalTerm) (leftSource rightSource : SourceTerm) (origin : Origin) :
    Fin 5 → List Alphabet :=
  ![encodeWith dbTermCodec left.term, encodeWith dbTermCodec right.term,
    encodeWith sourceTermCodec leftSource, encodeWith sourceTermCodec rightSource, encodeWith originCodec origin]

def pairInput (left right : CanonicalTerm) (leftSource rightSource : SourceTerm) (origin : Origin) :
    List (Option Alphabet) := Indexed.argumentWire (pairFields left right leftSource rightSource origin)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem pairNodes_exact (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftSource rightSource : SourceTerm)
    (leftNamed : named? left.term [pairNeedle] = some leftSource)
    (rightNamed : named? right.term [pairNeedle] = some rightSource)
    (origin : Origin) :
    pairNodes.map
      (Node.map (fun template => Indexed.instantiate template (pairFields left right leftSource rightSource origin))
        (fun template => Indexed.instantiate template (pairFields left right leftSource rightSource origin))
        (fun template => Indexed.instantiate template (pairFields left right leftSource rightSource origin))) =
      (betaBlock (pairBeta left right leftBool rightBool) origin).1.map
        (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  have sourceSame := pairSource_exact left right leftBool rightBool leftEmpty rightEmpty leftSource rightSource leftNamed rightNamed
  simp only [pairBeta, EqualityExpansion.Emission.betaExpansion_source_exact] at sourceSame
  have needleSame := pairNeedle_same left right leftEmpty rightEmpty
  simp only [pairNodes, Node.map, List.map_cons, List.map_nil, EqualityExpansion.Emission.unaryRequest,
    Templates.theoremTemplate, Templates.canonical, Templates.equality,
    Templates.application, Templates.sourceApplication, Templates.sourceAbstraction,
    Templates.pair_exact, Templates.literal_exact, Indexed.instantiate_hole, Indexed.instantiate_nil]
  simp [Node.map, pairFields, betaBlock, pairBeta,
    EqualityExpansion.Emission.betaIntermediate_exact, EqualityExpansion.Emission.betaEntries_exact,
    betaExpansion_conclusion, EqualityExpansion.Emission.betaExpansion_source_exact, sourceSame, needleSame,
    Theorem.emptyResult, CanonicalTerm.equalityOfSameType, CanonicalTerm.free,
    betaRedex, betaReduced, DBTerm.instantiateAt, DBTerm.instantiateAt_closed left.checked,
    DBTerm.instantiateAt_closed right.checked, secondSelector,
    requestCodec, putRequest, putInference,
    canonicalCodec, theoremCodec, sequentCodec, termMapletCodec, checkedSourceCodec, sourceTermCodec,
    dbTermCodec, tyCodec, Codec.prod, Codec.mapped, Codec.list, Codec.putList,
    encodeWith, encodeData_pair, putSourceTerm, putTerm, CanonicalTerm.equalityDB, List.append_assoc]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem pair_exact (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftSource rightSource : SourceTerm)
    (leftNamed : named? left.term [pairNeedle] = some leftSource)
    (rightNamed : named? right.term [pairNeedle] = some rightSource)
    (origin : Origin) :
    Indexed.instantiate pairTemplate (pairFields left right leftSource rightSource origin) =
      encodeCertificate (betaBlock (pairBeta left right leftBool rightBool) origin) := by
  exact EqualityExpansion.Emission.certificateTemplate_of_nodes pairNodes
    (betaBlock (pairBeta left right leftBool rightBool) origin).1 1
    (pairFields left right leftSource rightSource origin)
    (pairNodes_exact left right leftBool rightBool leftEmpty rightEmpty leftSource rightSource
      leftNamed rightNamed origin)

/-- Selected-pair reduction has the original two physical nodes and an
attached transition account for all five complete input fields. -/
def pairOutputs (left right : CanonicalTerm) (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftSource rightSource : SourceTerm)
    (leftNamed : named? left.term [pairNeedle] = some leftSource)
    (rightNamed : named? right.term [pairNeedle] = some rightSource)
    (origin : Origin) :
    TM2OutputsInTime (Indexed.machine pairTemplate)
      (pairInput left right leftSource rightSource origin)
      (some (encodeCertificate (betaBlock (pairBeta left right leftBool rightBool) origin)))
      (4 * (pairTemplate.length + 1) * ((pairInput left right leftSource rightSource origin).length + 1)) := by
  have ran := Indexed.outputs pairTemplate (pairFields left right leftSource rightSource origin)
  have same := pair_exact left right leftBool rightBool leftEmpty rightEmpty leftSource rightSource leftNamed rightNamed origin
  exact same ▸ ran

/-- A local macro's output is its actual final physical occurrence. Empty
local plans are refused before chronological assembly. -/
def macroRequest? {arity : Nat}
    (nodes : List (Node (Indexed.Template Alphabet arity)
      (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)))
    (root : Nat) (parents : List Nat) (origin : Indexed.Template Alphabet arity) :
    Option (Node (Indexed.Template Alphabet arity)
      (List (Node (Indexed.Template Alphabet arity)
        (Indexed.Template Alphabet arity) (Indexed.Template Alphabet arity)) × Nat)
      (Indexed.Template Alphabet arity)) := do
  let output ← nodes.getLast?
  return ⟨output.conclusion, (nodes, root), parents, origin⟩

/-- The twenty original implication macros lower to a single fixed field
plan. The two incoming theorems, operand words, named representatives and
origin remain physical independently framed fields. -/
def mpRequests? (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) :
    Option (List (Node (Indexed.Template Alphabet 9)
      (List (Node (Indexed.Template Alphabet 9)
        (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9)) × Nat)
      (Indexed.Template Alphabet 9))) := do
  let input : Indexed.Template Alphabet 9 := [.inr 0]
  let premise : Indexed.Template Alphabet 9 := [.inr 1]
  let left : Indexed.Template Alphabet 9 := [.inr 2]
  let right : Indexed.Template Alphabet 9 := [.inr 3]
  let leftSource : Indexed.Template Alphabet 9 := [.inr 4]
  let rightSource : Indexed.Template Alphabet 9 := [.inr 5]
  let origin : Indexed.Template Alphabet 9 := [.inr 6]
  let pairLeftSource : Indexed.Template Alphabet 9 := [.inr 7]
  let pairRightSource : Indexed.Template Alphabet 9 := [.inr 8]
  let combinedAxioms := inputAxioms ∪ premiseAxioms
  let combinedHypotheses := inputHypotheses ∪ premiseHypotheses
  let boolTerm := Templates.canonical Ty.bool
  let emptyTheorem := Templates.theoremTemplate ∅ ∅
  let inputTheorem := Templates.theoremTemplate inputAxioms inputHypotheses
  let combinedTheorem := Templates.theoremTemplate combinedAxioms combinedHypotheses
  let equality := Templates.equality Ty.bool
  let truth := Templates.literal (putTerm truthDB)
  let selector := Templates.literal (putTerm selectSecondDB)
  let andTerm := Templates.application (Templates.application (Templates.literal (putTerm andDB)) left) right
  let pairLeft := Templates.pair (Templates.literal (.atom 4))
    (Templates.pair (Templates.literal (putTy boolBinaryTy))
      (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) left) right))
  let pairTruth := Templates.literal (putTerm (pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl).term)
  let selectedLeft := Templates.application pairLeft selector
  let selectedTruth := Templates.application pairTruth selector
  let andEquation := equality andTerm left
  let pairEquation := Templates.equality (.function boolBinaryTy Ty.bool) pairLeft pairTruth
  let doubleSlots : Fin 5 → Indexed.Template Alphabet 9 := ![left, right, leftSource, rightSource, origin]
  let primitive (count : Nat) (claim request : Indexed.Template Alphabet 9) :=
    EqualityExpansion.Emission.primitiveNodes count claim request origin
  let sym (axioms : Finset Sequent) (hypotheses : Finset CanonicalTerm)
      (theoremField left right : Indexed.Template Alphabet 9) :=
    EqualityExpansion.Emission.substituteNodes ![theoremField, left, right, origin]
      (EqualityExpansion.Emission.symmetryNodes axioms hypotheses Ty.bool)
  let fixed (block : ProofSystem.Certificate) :=
    EqualityExpansion.Emission.substituteNodes ![origin] (EqualityExpansion.Emission.blockNodes block)
  let implicationNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked)
  let conjunctionNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked)
  let implicationConclusion := (implicationNodes.getLast?).map (·.conclusion)
  let conjunctionConclusion := (conjunctionNodes.getLast?).map (·.conclusion)
  let implicationConclusion ← implicationConclusion
  let conjunctionConclusion ← conjunctionConclusion
  let converted := inputTheorem (boolTerm andEquation)
  let reversedImp := inputTheorem (boolTerm (equality left andTerm))
  let andProof := combinedTheorem (boolTerm andTerm)
  let bodyProof := combinedTheorem (boolTerm pairEquation)
  let selectorCanonical := Templates.canonical boolBinaryTy selector
  let selectorProof := emptyTheorem (boolTerm (Templates.equality boolBinaryTy selector selector))
  let bodyApplication := combinedTheorem (boolTerm (equality selectedLeft selectedTruth))
  let pairNodes := EqualityExpansion.Emission.substituteNodes
    ![left, right, pairLeftSource, pairRightSource, origin] pairNodes
  let selectorNodes := EqualityExpansion.Emission.substituteNodes doubleSlots
    (EqualityExpansion.Emission.doubleBetaNodes Ty.bool Ty.bool Ty.bool (.bound 0) (by simp))
  let leftPairConclusion ← (pairNodes.getLast?).map (·.conclusion)
  let leftSelectorConclusion ← (selectorNodes.getLast?).map (·.conclusion)
  let leftReduction := emptyTheorem (boolTerm (equality selectedLeft right))
  let reversedLeft := emptyTheorem (boolTerm (equality right selectedLeft))
  let truthPair := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthSelector := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthPairNodes := fixed (betaBlock truthPair ("", 0))
  let truthSelectorNodes := fixed (doubleBetaBlock truthSelector ("", 0))
  let truthPairConclusion := Templates.literal (theoremCodec.put truthPair.conclusion)
  let truthSelectorConclusion := Templates.literal (theoremCodec.put truthSelector.conclusion)
  let truthReduction := emptyTheorem (boolTerm (equality selectedTruth truth))
  let joinedLeft := combinedTheorem (boolTerm (equality right selectedTruth))
  let joinedTruth := combinedTheorem (boolTerm (equality right truth))
  let reversedTruth := combinedTheorem (boolTerm (equality truth right))
  let identityCanonical := Templates.literal (canonicalCodec.put
    (⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩ : CanonicalTerm))
  let truthProof := Templates.literal (theoremCodec.put (reflexivity
    (⟨identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩ : CanonicalTerm)))
  let result := combinedTheorem (boolTerm right)
  let request0 ← macroRequest? implicationNodes 6 [] origin
  let request1 ← macroRequest? (primitive 2 converted
    (EqualityExpansion.Emission.binaryRequest 6 implicationConclusion input)) 2 [2, 0] origin
  let request2 ← macroRequest? (sym inputAxioms inputHypotheses converted andTerm left) 5 [3] origin
  let request3 ← macroRequest? (primitive 2 andProof
    (EqualityExpansion.Emission.binaryRequest 6 reversedImp premise)) 2 [4, 1] origin
  let request4 ← macroRequest? conjunctionNodes 6 [] origin
  let request5 ← macroRequest? (primitive 2 bodyProof
    (EqualityExpansion.Emission.binaryRequest 6 conjunctionConclusion andProof)) 2 [6, 5] origin
  let request6 ← macroRequest? (primitive 0 selectorProof
    (EqualityExpansion.Emission.unaryRequest 0 selectorCanonical)) 0 [] origin
  let request7 ← macroRequest? (primitive 2 bodyApplication
    (EqualityExpansion.Emission.binaryRequest 2 bodyProof selectorProof)) 2 [7, 8] origin
  let request8 ← macroRequest? pairNodes 1 [] origin
  let request9 ← macroRequest? selectorNodes 6 [] origin
  let request10 ← macroRequest? (primitive 2 leftReduction
    (EqualityExpansion.Emission.binaryRequest 1 leftPairConclusion leftSelectorConclusion)) 2 [10, 11] origin
  let request11 ← macroRequest? (sym ∅ ∅ leftReduction selectedLeft right) 5 [12] origin
  let request12 ← macroRequest? truthPairNodes 1 [] origin
  let request13 ← macroRequest? truthSelectorNodes 6 [] origin
  let request14 ← macroRequest? (primitive 2 truthReduction
    (EqualityExpansion.Emission.binaryRequest 1 truthPairConclusion truthSelectorConclusion)) 2 [14, 15] origin
  let request15 ← macroRequest? (primitive 2 joinedLeft
    (EqualityExpansion.Emission.binaryRequest 1 reversedLeft bodyApplication)) 2 [13, 9] origin
  let request16 ← macroRequest? (primitive 2 joinedTruth
    (EqualityExpansion.Emission.binaryRequest 1 joinedLeft truthReduction)) 2 [17, 16] origin
  let request17 ← macroRequest? (sym combinedAxioms combinedHypotheses joinedTruth right truth) 5 [18] origin
  let request18 ← macroRequest? (primitive 0 truthProof
    (EqualityExpansion.Emission.unaryRequest 0 identityCanonical)) 0 [] origin
  let request19 ← macroRequest? (primitive 2 result
    (EqualityExpansion.Emission.binaryRequest 6 reversedTruth truthProof)) 2 [19, 20] origin
  return [request0, request1, request2, request3, request4, request5, request6, request7, request8, request9,
    request10, request11, request12, request13, request14, request15, request16, request17, request18, request19]

/-- Local MP assembly retains its two external cache entries. Every macro
uses the shared chronological relocation operation. -/
def mpTemplate? (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) : Option (Indexed.Template Alphabet 9) := do
  let requests ← mpRequests? inputAxioms premiseAxioms inputHypotheses premiseHypotheses
  let (nodes, roots) ← GraphExpansion.expandFrom [] #[0, 1] requests 2
  let root ← roots[21]?
  return EqualityExpansion.Emission.certificateTemplate (nodes, root)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem mpTemplate_isSome (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) :
    (mpTemplate? inputAxioms premiseAxioms inputHypotheses premiseHypotheses).isSome = true := by
  simp [mpTemplate?, mpRequests?, macroRequest?, EqualityExpansion.Emission.substituteNodes,
    EqualityExpansion.Emission.doubleBetaNodes, EqualityExpansion.Emission.symmetryNodes,
    EqualityExpansion.Emission.primitiveNodes, EqualityExpansion.Emission.blockNodes, pairNodes,
    betaBlock, doubleBetaBlock, GraphExpansion.expandFrom, GraphExpansion.expandBlock,
    lookupPremises, GraphExpansion.address, Node.map, Node.relocate]

/-- Static assembly is total for every fixed incoming dependency basis. The
result is the actual twenty-macro field plan, not an independent emitter. -/
def mpTemplate (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) : Indexed.Template Alphabet 9 :=
  (mpTemplate? inputAxioms premiseAxioms inputHypotheses premiseHypotheses).get
    (by rw [mpTemplate_isSome])

theorem mpTemplate_computed (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) :
    mpTemplate? inputAxioms premiseAxioms inputHypotheses premiseHypotheses =
      some (mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses) :=
  (Option.some_get _).symm

/-- Every raw framed field packet is physically scanned and copied by the
whole emitted plan. Logical input admission and byte-exact correspondence
with the source MP block are separate from this unconditional execution law. -/
def mpOutputsWire (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) (input : List (Option Alphabet)) :
    TM2OutputsInTime (Indexed.machine (mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses))
      input (some (Indexed.instantiateWire
        (mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses) input))
      (4 * ((mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses).length + 1) *
        (input.length + 1)) :=
  Indexed.outputsWire _ input

/-- The field-emission phase has a genuine linear finite-machine execution
account for its fixed dependency basis. Upstream field producers and source
admission are required to give its output the source rule's meaning. -/
noncomputable def mpFieldRealization (inputAxioms premiseAxioms : Finset Sequent)
    (inputHypotheses premiseHypotheses : Finset CanonicalTerm) :
    TM2ComputableInPolyTime id id
      (fun (input : List (Option Alphabet)) => Indexed.instantiateWire
        (mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses) input) :=
  Indexed.wireComputable (mpTemplate inputAxioms premiseAxioms inputHypotheses premiseHypotheses)

def mpFields (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : Origin) : Fin 9 → List Alphabet :=
  ![encodeWith theoremCodec input, encodeWith theoremCodec premise,
    encodeWith dbTermCodec left.term, encodeWith dbTermCodec right.term,
    encodeWith sourceTermCodec (checkedSource left).source, encodeWith sourceTermCodec (checkedSource right).source,
    encodeWith originCodec origin, encodeWith sourceTermCodec pairLeftSource, encodeWith sourceTermCodec pairRightSource]

def mpInput (input premise : Theorem) (left right : CanonicalTerm)
    (pairLeftSource pairRightSource : SourceTerm) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (mpFields input premise left right pairLeftSource pairRightSource origin)

open EqualityExpansion.Emission

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The three dynamic two-beta macros lower to the original local HOL
nodes, including the named source requests and substitution entries. -/
theorem mpDoubleBetaMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) (kind : Fin 3) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![0,4,9] : Fin 3 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![0,4,9] : Fin 3 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let slots : Fin 5 → Indexed.Template Alphabet 9 :=
    ![[.inr 2], [.inr 3], [.inr 4], [.inr 5], [.inr 6]]
  have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) = doubleBetaFields left right origin := by
    funext slot
    fin_cases slot <;> simp [slots, fields, mpFields, doubleBetaFields, Indexed.instantiate]
  have lower (body : DBTerm) (checked : body.inferType [Ty.bool, Ty.bool] = some Ty.bool) :
      (substituteNodes slots (doubleBetaNodes Ty.bool Ty.bool Ty.bool body checked)).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)) =
      (EqualityExpansion.doubleBetaBlock
        (EqualityExpansion.doubleBetaExpansion Ty.bool Ty.bool Ty.bool body checked left right leftBool rightBool) origin).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
    rw [substituteNodes_exact, fieldsSame]
    exact doubleBetaNodes_exact Ty.bool Ty.bool Ty.bool body checked
      left right leftBool rightBool leftEmpty leftNamed origin
  fin_cases kind
  · change some (some _) = some (some _)
    exact congrArg (fun nodes => some (some nodes)) (lower implicationBody implicationBody_checked)
  · change some (some _) = some (some _)
    exact congrArg (fun nodes => some (some nodes)) (lower conjunctionBody conjunctionBody_checked)
  · change some (some _) = some (some _)
    exact congrArg (fun nodes => some (some nodes)) (lower (.bound 0) (by simp))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The dynamic pair beta retains the original binder-context named
representatives, rather than merely an alpha-equivalent replacement. -/
theorem mpPairMacro_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (pairLeftSource pairRightSource : SourceTerm)
    (leftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (rightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[8]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[8]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let slots : Fin 5 → Indexed.Template Alphabet 9 :=
    ![[.inr 2], [.inr 3], [.inr 7], [.inr 8], [.inr 6]]
  change some (some ((substituteNodes slots pairNodes).map
    (Node.map (fun template => Indexed.instantiate template fields)
      (fun template => Indexed.instantiate template fields)
      (fun template => Indexed.instantiate template fields)))) = some (some _)
  rw [substituteNodes_exact]
  have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) =
      pairFields left right pairLeftSource pairRightSource origin := by
    funext slot
    fin_cases slot <;> simp [slots, fields, mpFields, pairFields, Indexed.instantiate]
  rw [fieldsSame]
  exact congrArg (fun nodes => some (some nodes))
    (pairNodes_exact left right leftBool rightBool leftEmpty rightEmpty
      pairLeftSource pairRightSource leftNamed rightNamed origin)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The two authored truth macros retain every original local request;
only the originating occurrence is supplied dynamically. -/
theorem mpFixedMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) (kind : Fin 2) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![12,13] : Fin 2 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![12,13] : Fin 2 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let slots : Fin 1 → Indexed.Template Alphabet 9 := ![[.inr 6]]
  have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) = originFields origin := by
    funext slot
    fin_cases slot
    simp [slots, fields, mpFields, originFields, Indexed.instantiate]
  have lower (block : ProofSystem.Certificate) :
      (substituteNodes slots (blockNodes block)).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)) =
      (stampedBlock origin block).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
    rw [substituteNodes_exact, fieldsSame]
    exact blockNodes_exact block origin
  fin_cases kind
  · change some (some _) = some (some _)
    have exactNodes := lower (betaBlock (pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl) ("",0))
    simpa only [stampedBlock, betaBlock, List.map_cons, List.map_nil] using
      congrArg (fun nodes => some (some nodes)) exactNodes
  · change some (some _) = some (some _)
    have exactNodes := lower (EqualityExpansion.doubleBetaBlock
      (selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl) ("",0))
    simpa only [stampedBlock, EqualityExpansion.doubleBetaBlock, List.map_cons, List.map_nil] using
      congrArg (fun nodes => some (some nodes)) exactNodes

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Every symmetry occurrence lowers to the original five-node block.
Its full incoming dependencies survive the intervening equality and beta
steps, while the operand's displayed Boolean type is handled explicitly. -/
theorem mpSymmetryMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) (kind : Fin 3) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![2,11,17] : Fin 3 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![2,11,17] : Fin 3 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  fin_cases kind
  ·
    let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let convertedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool a l))
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r, fields, mpFields, Indexed.instantiate]
    have convertedExact : Indexed.instantiate convertedPlan fields = encodeWith theoremCodec converted := by
      apply Templates.theoremTemplate_exact _ _ _ _ _ axioms hypotheses
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool a l) fields andEquation rfl
        (Templates.equality_exact _ _ _ _ _ _ aExact (by simp [l,fields,mpFields,Indexed.instantiate]))
    let slots : Fin 4 → Indexed.Template Alphabet 9 := ![convertedPlan, a, l, o]
    change some (some ((substituteNodes slots (symmetryNodes input.axioms input.sequent.hyp Ty.bool)).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    rw [substituteNodes_exact]
    have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) =
        symmetryFields converted andTerm left origin := by
      funext slot
      fin_cases slot
      · exact convertedExact
      · exact aExact
      · simp [slots,l,fields,mpFields,symmetryFields,Indexed.instantiate]
      · simp [slots,o,fields,mpFields,symmetryFields,Indexed.instantiate]
    rw [fieldsSame]
    exact congrArg (fun nodes => some (some nodes))
      (symmetryNodes_exact input.axioms input.sequent.hyp Ty.bool converted andTerm left
        axioms hypotheses rfl leftBool origin)
  ·
    let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let selector : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
    let pairPlan := Templates.pair (Templates.literal (.atom 4))
      (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
        (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
    let selectedPlan := Templates.application pairPlan selector
    let reductionPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan r))
    let selected := selectedPair left right leftBool rightBool
    let pair := pairBeta left right leftBool rightBool
    let selectorBeta := ImplicationExpansion.selectorBeta left right leftBool rightBool
    let reduction := transResult pair.conclusion selectorBeta.conclusion selected right rightBool.symm
    have pairParts : pair.conclusion.axioms = ∅ ∧ pair.conclusion.sequent.hyp = ∅ := by
      simp [pair,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      left right leftBool rightBool
    have axioms : reduction.axioms = ∅ := by
      simp only [reduction,selectorBeta,ImplicationExpansion.selectorBeta,transResult,Theorem.unionResult,
        pairParts.1,selectorParts.1,Finset.empty_union]
    have hypotheses : reduction.sequent.hyp = ∅ := by
      simp only [reduction,selectorBeta,ImplicationExpansion.selectorBeta,transResult,Theorem.unionResult,
        pairParts.2,selectorParts.2.1,Finset.empty_union]
    have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec
        (pairTerm left right leftBool rightBool).term := by
      have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
        fields (.app (.bound 0) left.term) right.term
        (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate]))
        (by simp [r,fields,mpFields,Indexed.instantiate])
      simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
      rfl
    have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
      Templates.application_exact _ _ _ _ _ pairExact (Templates.literal_exact _ _)
    have reductionExact : Indexed.instantiate reductionPlan fields = encodeWith theoremCodec reduction := by
      apply Templates.theoremTemplate_exact _ _ _ _ _ axioms hypotheses
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan r) fields
        (CanonicalTerm.equalityOfSameType selected right rightBool.symm) rfl
        (Templates.equality_exact _ _ _ _ _ _ selectedExact (by simp [r,fields,mpFields,Indexed.instantiate]))
    let slots : Fin 4 → Indexed.Template Alphabet 9 := ![reductionPlan,selectedPlan,r,o]
    change some (some ((substituteNodes slots (symmetryNodes ∅ ∅ Ty.bool)).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    rw [substituteNodes_exact]
    have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) =
        symmetryFields reduction selected right origin := by
      funext slot
      fin_cases slot
      · exact reductionExact
      · exact selectedExact
      · simp [slots,r,fields,mpFields,symmetryFields,Indexed.instantiate]
      · simp [slots,o,fields,mpFields,symmetryFields,Indexed.instantiate]
    rw [fieldsSame]
    exact congrArg (fun nodes => some (some nodes))
      (symmetryNodes_exact ∅ ∅ Ty.bool reduction selected right
        axioms hypotheses rfl rightBool origin)
  ·
    let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let truth : Indexed.Template Alphabet 9 := Templates.literal (putTerm PrimitiveSentences.truthDB)
    let joinedPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r truth))
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let andProof := eqMpResult reversed premise andTerm
    let andBeta := conjunctionBeta left right leftBool rightBool
    let pairLeft := pairTerm left right leftBool rightBool
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let bodyProof := eqMpResult andBeta.conclusion andProof (CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl)
    let selected := selectedPair left right leftBool rightBool
    let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let bodyApplication := appResult bodyProof (reflexivity secondSelector) selected selectedTruth rfl
    let leftBeta := pairBeta left right leftBool rightBool
    let leftSelectorBeta := selectorBeta left right leftBool rightBool
    let leftReduction := transResult leftBeta.conclusion leftSelectorBeta.conclusion selected right rightBool.symm
    let reversedLeft := symmetryResult leftReduction selected right rightBool.symm
    let truthBeta := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthSelectorBeta := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthReduction := transResult truthBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
    let joinedLeft := transResult reversedLeft bodyApplication right selectedTruth rightBool
    let joinedTruth := transResult joinedLeft truthReduction right DerivedRules.truthTerm rightBool
    have impParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked left right leftBool rightBool
    have andParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked left right leftBool rightBool
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp) left right leftBool rightBool
    have truthSelectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp) DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have leftBetaParts : leftBeta.conclusion.axioms = ∅ ∧ leftBeta.conclusion.sequent.hyp = ∅ := by
      simp [leftBeta,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have truthBetaParts : truthBeta.conclusion.axioms = ∅ ∧ truthBeta.conclusion.sequent.hyp = ∅ := by
      simp [truthBeta,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have axioms : joinedTruth.axioms = input.axioms ∪ premise.axioms := by
      simp only [joinedTruth,joinedLeft,truthReduction,reversedLeft,leftReduction,bodyApplication,bodyProof,andProof,
        reversed,converted,impBeta,andBeta,leftSelectorBeta,truthSelectorBeta,
        implicationBeta,conjunctionBeta,selectorBeta,
        transResult,appResult,eqMpResult,symmetryResult,reflexivity,
        Theorem.unionResult,Theorem.preserveAxiomsResult,Theorem.emptyResult,
        impParts.1,andParts.1,selectorParts.1,truthSelectorParts.1,leftBetaParts.1,truthBetaParts.1,
        Finset.empty_union,Finset.union_empty]
    have hypotheses : joinedTruth.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [joinedTruth,joinedLeft,truthReduction,reversedLeft,leftReduction,bodyApplication,bodyProof,andProof,
        reversed,converted,impBeta,andBeta,leftSelectorBeta,truthSelectorBeta,
        implicationBeta,conjunctionBeta,selectorBeta,
        transResult,appResult,eqMpResult,symmetryResult,reflexivity,
        Theorem.unionResult,Theorem.preserveAxiomsResult,Theorem.emptyResult,
        impParts.2.1,andParts.2.1,selectorParts.2.1,truthSelectorParts.2.1,leftBetaParts.2,truthBetaParts.2,
        Finset.empty_union,Finset.union_empty]
    have rightExact : Indexed.instantiate r fields = encodeWith dbTermCodec right.term := by
      simp [r,fields,mpFields,Indexed.instantiate]
    have joinedExact : Indexed.instantiate joinedPlan fields = encodeWith theoremCodec joinedTruth := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool (Templates.equality Ty.bool r truth))
        fields joinedTruth axioms hypotheses
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r truth) fields
        (CanonicalTerm.equalityOfSameType right DerivedRules.truthTerm rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType, DerivedRules.truthTerm, rightBool] using
        (Templates.equality_exact Ty.bool r truth fields right.term PrimitiveSentences.truthDB
          rightExact (Templates.literal_exact (putTerm PrimitiveSentences.truthDB) fields))
    let slots : Fin 4 → Indexed.Template Alphabet 9 := ![joinedPlan,r,truth,o]
    change some (some ((substituteNodes slots (symmetryNodes
        (input.axioms ∪ premise.axioms) (input.sequent.hyp ∪ premise.sequent.hyp) Ty.bool)).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    rw [substituteNodes_exact]
    have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) =
        symmetryFields joinedTruth right DerivedRules.truthTerm origin := by
      funext slot
      fin_cases slot
      · exact joinedExact
      · exact rightExact
      · exact Templates.literal_exact _ _
      · simp [slots,o,fields,mpFields,symmetryFields,Indexed.instantiate]
    rw [fieldsSame]
    exact congrArg (fun nodes => some (some nodes))
      (symmetryNodes_exact (input.axioms ∪ premise.axioms) (input.sequent.hyp ∪ premise.sequent.hyp)
        Ty.bool joinedTruth right DerivedRules.truthTerm axioms hypotheses rightBool rfl origin)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Both reflexivity occurrences preserve the original canonical operand,
request, claim and empty local parent vector. -/
theorem mpReflexivityMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) (kind : Fin 2) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![6,18] : Fin 2 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![6,18] : Fin 2 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let o : Indexed.Template Alphabet 9 := [.inr 6]
  have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
    simp [o,fields,mpFields,Indexed.instantiate]
  fin_cases kind
  · change some (some _) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (reflexivityNodes_exact (Templates.literal (putTerm DerivedRules.selectSecondDB)) o fields
        secondSelector ExcludedMiddle.boolBinaryTy rfl origin (Templates.literal_exact _ _) originExact)
  · let identity : CanonicalTerm :=
      ⟨PrimitiveSentences.identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
    let claim := EqualityExpansion.reflexivity identity
    let claimPlan : Indexed.Template Alphabet 9 := Templates.literal (theoremCodec.put claim)
    let requestPlan : Indexed.Template Alphabet 9 := unaryRequest 0 (Templates.literal (canonicalCodec.put identity))
    change some (some ((primitiveNodes 0 claimPlan requestPlan o).map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)))) = some (some _)
    apply congrArg (fun nodes => some (some nodes))
    apply primitiveNodes_exact 0 claimPlan requestPlan o fields (.inference (.refl identity)) claim origin rfl
    · exact Templates.literal_exact _ _
    · simp only [requestPlan, unaryRequest, Templates.pair_exact, Templates.literal_exact,
        encodeWith, requestCodec, ProofDataEncoding.putRequest, ProofDataEncoding.putInference, encodeData_pair, List.cons_append]
    · exact originExact

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The four equality-elimination occurrences preserve the complete original
claims, requests, local parents and origins. Beta-derived claim fields are
obtained from the same checked primitive blocks used by the source plan. -/
theorem mpEqMpMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) (kind : Fin 4) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![1,3,5,19] : Fin 4 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![1,3,5,19] : Fin 4 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  fin_cases kind
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let i : Indexed.Template Alphabet 9 := [.inr 0]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let convertedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool a l))
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    let slots : Fin 5 → Indexed.Template Alphabet 9 := ![l,r,[.inr 4],[.inr 5],o]
    let betaNodes := substituteNodes slots
      (doubleBetaNodes Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked)
    let betaClaim : Indexed.Template Alphabet 9 := (betaNodes.getLast?.map Node.conclusion).getD []
    have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) = doubleBetaFields left right origin := by
      funext slot
      fin_cases slot <;> simp [slots,l,r,o,fields,mpFields,doubleBetaFields,Indexed.instantiate]
    have betaNodesExact : betaNodes.map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)) =
        (doubleBetaBlock impBeta origin).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
      rw [substituteNodes_exact,fieldsSame]
      exact doubleBetaNodes_exact Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked
        left right leftBool rightBool leftEmpty leftNamed origin
    have betaClaimExact : Indexed.instantiate betaClaim fields = encodeWith theoremCodec impBeta.conclusion :=
      lastConclusion_exact betaNodes (doubleBetaBlock impBeta origin).1 betaClaim impBeta.conclusion fields
        betaNodesExact (by rfl) (by rfl)
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted,impBeta,implicationBeta,eqMpResult,Theorem.unionResult,betaParts.1,Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted,impBeta,implicationBeta,eqMpResult,Theorem.unionResult,betaParts.2.1,Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r,fields,mpFields,Indexed.instantiate]
    have convertedExact : Indexed.instantiate convertedPlan fields = encodeWith theoremCodec converted := by
      apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
        (Templates.canonical Ty.bool (Templates.equality Ty.bool a l)) fields converted axioms hypotheses
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool a l) fields andEquation rfl
        (Templates.equality_exact Ty.bool a l fields andTerm.term left.term aExact
          (by simp [l,fields,mpFields,Indexed.instantiate]))
    have inputExact : Indexed.instantiate i fields = encodeWith theoremCodec input := by
      simp [i,fields,mpFields,Indexed.instantiate]
    have requestExact : Indexed.instantiate (binaryRequest 6 betaClaim i) fields =
        encodeWith requestCodec (.inference (.eqMp impBeta.conclusion input)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        betaClaimExact,inputExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 convertedPlan (binaryRequest 6 betaClaim i) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 convertedPlan (binaryRequest 6 betaClaim i) o fields
        (.inference (.eqMp impBeta.conclusion input)) converted origin rfl
        convertedExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r, fields, mpFields, Indexed.instantiate]
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let reversedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool l a))
    have reversedAxes : reversed.axioms = input.axioms := axioms
    have reversedHyp : reversed.sequent.hyp = input.sequent.hyp := hypotheses
    have leftExact : Indexed.instantiate l fields = encodeWith dbTermCodec left.term := by
      simp [l,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
        (Templates.canonical Ty.bool (Templates.equality Ty.bool l a)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool l a) fields
        (CanonicalTerm.equalityOfSameType left andTerm leftBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType, leftBool] using
        Templates.equality_exact Ty.bool l a fields left.term andTerm.term leftExact aExact
    let andProof := eqMpResult reversed premise andTerm
    let andPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a)
    have andAxes : andProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedAxes]
    have andHyp : andProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedHyp]
    have andExact : Indexed.instantiate andPlan fields = encodeWith theoremCodec andProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a) fields andProof andAxes andHyp
      exact Templates.canonical_exact Ty.bool a fields andTerm rfl aExact
    let p : Indexed.Template Alphabet 9 := [.inr 1]
    have premiseExact : Indexed.instantiate p fields = encodeWith theoremCodec premise := by
      simp [p,fields,mpFields,Indexed.instantiate]
    have requestExact : Indexed.instantiate (binaryRequest 6 reversedPlan p) fields =
        encodeWith requestCodec (.inference (.eqMp reversed premise)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        reversedExact,premiseExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 andPlan (binaryRequest 6 reversedPlan p) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 andPlan (binaryRequest 6 reversedPlan p) o fields
        (.inference (.eqMp reversed premise)) andProof origin rfl andExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r, fields, mpFields, Indexed.instantiate]
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let reversedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool l a))
    have reversedAxes : reversed.axioms = input.axioms := axioms
    have reversedHyp : reversed.sequent.hyp = input.sequent.hyp := hypotheses
    have leftExact : Indexed.instantiate l fields = encodeWith dbTermCodec left.term := by
      simp [l,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
        (Templates.canonical Ty.bool (Templates.equality Ty.bool l a)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool l a) fields
        (CanonicalTerm.equalityOfSameType left andTerm leftBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType, leftBool] using
        Templates.equality_exact Ty.bool l a fields left.term andTerm.term leftExact aExact
    let andProof := eqMpResult reversed premise andTerm
    let andPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a)
    have andAxes : andProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedAxes]
    have andHyp : andProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedHyp]
    have andExact : Indexed.instantiate andPlan fields = encodeWith theoremCodec andProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a) fields andProof andAxes andHyp
      exact Templates.canonical_exact Ty.bool a fields andTerm rfl aExact
    let andBeta := conjunctionBeta left right leftBool rightBool
    let slots : Fin 5 → Indexed.Template Alphabet 9 := ![l,r,[.inr 4],[.inr 5],o]
    let betaNodes := substituteNodes slots
      (doubleBetaNodes Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked)
    let betaClaim : Indexed.Template Alphabet 9 := (betaNodes.getLast?.map Node.conclusion).getD []
    have fieldsSame : (fun slot => Indexed.instantiate (slots slot) fields) = doubleBetaFields left right origin := by
      funext slot
      fin_cases slot <;> simp [slots,l,r,o,fields,mpFields,doubleBetaFields,Indexed.instantiate]
    have betaNodesExact : betaNodes.map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)) =
        (doubleBetaBlock andBeta origin).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
      rw [substituteNodes_exact,fieldsSame]
      exact doubleBetaNodes_exact Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
        left right leftBool rightBool leftEmpty leftNamed origin
    have betaClaimExact : Indexed.instantiate betaClaim fields = encodeWith theoremCodec andBeta.conclusion :=
      lastConclusion_exact betaNodes (doubleBetaBlock andBeta origin).1 betaClaim andBeta.conclusion fields
        betaNodesExact (by rfl) (by rfl)
    let pairLeft := pairTerm left right leftBool rightBool
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
    let pairPlan := Templates.pair (Templates.literal (.atom 4))
      (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
        (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
    let truthPairPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm pairTruth.term)
    let equationPlan := Templates.equality (.function ExcludedMiddle.boolBinaryTy Ty.bool) pairPlan truthPairPlan
    have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec pairLeft.term := by
      have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
        fields (.app (.bound 0) left.term) right.term
        (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) leftExact)
        (by simp [r,fields,mpFields,Indexed.instantiate])
      simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
      rfl
    have equationExact : Indexed.instantiate equationPlan fields = encodeWith dbTermCodec pairEquation.term :=
      Templates.equality_exact _ _ _ fields pairLeft.term pairTruth.term pairExact (Templates.literal_exact _ _)
    let bodyProof := eqMpResult andBeta.conclusion andProof pairEquation
    let bodyPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan)
    have andBetaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
      left right leftBool rightBool
    have bodyAxes : bodyProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.1,andAxes,Finset.empty_union]
    have bodyHyp : bodyProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.2.1,andHyp,Finset.empty_union]
    have bodyExact : Indexed.instantiate bodyPlan fields = encodeWith theoremCodec bodyProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan) fields bodyProof bodyAxes bodyHyp
      exact Templates.canonical_exact Ty.bool equationPlan fields pairEquation rfl equationExact
    have requestExact : Indexed.instantiate (binaryRequest 6 betaClaim andPlan) fields =
        encodeWith requestCodec (.inference (.eqMp andBeta.conclusion andProof)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        betaClaimExact,andExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 bodyPlan (binaryRequest 6 betaClaim andPlan) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 bodyPlan (binaryRequest 6 betaClaim andPlan) o fields
        (.inference (.eqMp andBeta.conclusion andProof)) bodyProof origin rfl bodyExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let truth : Indexed.Template Alphabet 9 := Templates.literal (putTerm PrimitiveSentences.truthDB)
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let andProof := eqMpResult reversed premise andTerm
    let andBeta := conjunctionBeta left right leftBool rightBool
    let pairLeft := pairTerm left right leftBool rightBool
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let bodyProof := eqMpResult andBeta.conclusion andProof (CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl)
    let selected := selectedPair left right leftBool rightBool
    let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let bodyApplication := appResult bodyProof (reflexivity secondSelector) selected selectedTruth rfl
    let leftBeta := pairBeta left right leftBool rightBool
    let leftSelectorBeta := selectorBeta left right leftBool rightBool
    let leftReduction := transResult leftBeta.conclusion leftSelectorBeta.conclusion selected right rightBool.symm
    let reversedLeft := symmetryResult leftReduction selected right rightBool.symm
    let truthBeta := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthSelectorBeta := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthReduction := transResult truthBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
    let joinedLeft := transResult reversedLeft bodyApplication right selectedTruth rightBool
    let joinedTruth := transResult joinedLeft truthReduction right DerivedRules.truthTerm rightBool
    have impParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody implicationBody_checked left right leftBool rightBool
    have andParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked left right leftBool rightBool
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp) left right leftBool rightBool
    have truthSelectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp) DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have leftBetaParts : leftBeta.conclusion.axioms = ∅ ∧ leftBeta.conclusion.sequent.hyp = ∅ := by
      simp [leftBeta,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have truthBetaParts : truthBeta.conclusion.axioms = ∅ ∧ truthBeta.conclusion.sequent.hyp = ∅ := by
      simp [truthBeta,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have axioms : joinedTruth.axioms = input.axioms ∪ premise.axioms := by
      simp only [joinedTruth,joinedLeft,truthReduction,reversedLeft,leftReduction,bodyApplication,bodyProof,andProof,
        reversed,converted,impBeta,andBeta,leftSelectorBeta,truthSelectorBeta,
        implicationBeta,conjunctionBeta,selectorBeta,
        transResult,appResult,eqMpResult,symmetryResult,reflexivity,
        Theorem.unionResult,Theorem.preserveAxiomsResult,Theorem.emptyResult,
        impParts.1,andParts.1,selectorParts.1,truthSelectorParts.1,leftBetaParts.1,truthBetaParts.1,
        Finset.empty_union,Finset.union_empty]
    have hypotheses : joinedTruth.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [joinedTruth,joinedLeft,truthReduction,reversedLeft,leftReduction,bodyApplication,bodyProof,andProof,
        reversed,converted,impBeta,andBeta,leftSelectorBeta,truthSelectorBeta,
        implicationBeta,conjunctionBeta,selectorBeta,
        transResult,appResult,eqMpResult,symmetryResult,reflexivity,
        Theorem.unionResult,Theorem.preserveAxiomsResult,Theorem.emptyResult,
        impParts.2.1,andParts.2.1,selectorParts.2.1,truthSelectorParts.2.1,leftBetaParts.2,truthBetaParts.2,
        Finset.empty_union,Finset.union_empty]
    let reversedTruth := symmetryResult joinedTruth right DerivedRules.truthTerm rightBool
    let reversedPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool truth r))
    have reversedAxes : reversedTruth.axioms = input.axioms ∪ premise.axioms := axioms
    have reversedHyp : reversedTruth.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := hypotheses
    have rightExact : Indexed.instantiate r fields = encodeWith dbTermCodec right.term := by
      simp [r,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversedTruth := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool truth r)) fields reversedTruth reversedAxes reversedHyp
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool truth r) fields
        (CanonicalTerm.equalityOfSameType DerivedRules.truthTerm right rightBool.symm) rfl
        (Templates.equality_exact Ty.bool truth r fields DerivedRules.truthTerm.term right.term
          (Templates.literal_exact (putTerm PrimitiveSentences.truthDB) fields) rightExact)
    let identity : CanonicalTerm :=
      ⟨PrimitiveSentences.identityBool, .function Ty.bool Ty.bool, DerivedRules.inferType_identityBool⟩
    let truthProof := reflexivity identity
    let truthPlan : Indexed.Template Alphabet 9 := Templates.literal (theoremCodec.put truthProof)
    let result := eqMpResult reversedTruth truthProof right
    let resultPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool r)
    have resultAxes : result.axioms = input.axioms ∪ premise.axioms := by
      simp only [result,eqMpResult,Theorem.unionResult,reversedAxes,truthProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have resultHyp : result.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [result,eqMpResult,Theorem.unionResult,reversedHyp,truthProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have resultExact : Indexed.instantiate resultPlan fields = encodeWith theoremCodec result := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool r) fields result resultAxes resultHyp
      exact Templates.canonical_exact Ty.bool r fields right rightBool rightExact
    have requestExact : Indexed.instantiate (binaryRequest 6 reversedPlan truthPlan) fields =
        encodeWith requestCodec (.inference (.eqMp reversedTruth truthProof)) := by
      simp only [truthPlan,binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        reversedExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 resultPlan (binaryRequest 6 reversedPlan truthPlan) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 resultPlan (binaryRequest 6 reversedPlan truthPlan) o fields
        (.inference (.eqMp reversedTruth truthProof)) result origin rfl resultExact requestExact originExact)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Application of equality preserves the ordered two-parent request and its
full dependency-carrying claim in the original MP expansion. -/
theorem mpCombinationMacro_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (pairLeftSource pairRightSource : SourceTerm) (origin : ProofExecution.Origin) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[7]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[7]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let l : Indexed.Template Alphabet 9 := [.inr 2]
  let r : Indexed.Template Alphabet 9 := [.inr 3]
  let o : Indexed.Template Alphabet 9 := [.inr 6]
  let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
  let andTerm := conjunction left right leftBool rightBool
  let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
  let impBeta := implicationBeta left right leftBool rightBool
  let converted := eqMpResult impBeta.conclusion input andEquation
  have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
    implicationBody_checked left right leftBool rightBool
  have axioms : converted.axioms = input.axioms := by
    simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
  have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
    simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
  have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
    apply Templates.application_exact
    · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
    · simp [r, fields, mpFields, Indexed.instantiate]
  let reversed := symmetryResult converted andTerm left leftBool.symm
  let reversedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
    (Templates.canonical Ty.bool (Templates.equality Ty.bool l a))
  have reversedAxes : reversed.axioms = input.axioms := axioms
  have reversedHyp : reversed.sequent.hyp = input.sequent.hyp := hypotheses
  have leftExact : Indexed.instantiate l fields = encodeWith dbTermCodec left.term := by
    simp [l,fields,mpFields,Indexed.instantiate]
  have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
    apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool l a)) fields reversed reversedAxes reversedHyp
    apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool l a) fields
      (CanonicalTerm.equalityOfSameType left andTerm leftBool) rfl
    simpa only [CanonicalTerm.equalityOfSameType, leftBool] using
      Templates.equality_exact Ty.bool l a fields left.term andTerm.term leftExact aExact
  let andProof := eqMpResult reversed premise andTerm
  let andPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
    (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a)
  have andAxes : andProof.axioms = input.axioms ∪ premise.axioms := by
    simp only [andProof,eqMpResult,Theorem.unionResult,reversedAxes]
  have andHyp : andProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
    simp only [andProof,eqMpResult,Theorem.unionResult,reversedHyp]
  have andExact : Indexed.instantiate andPlan fields = encodeWith theoremCodec andProof := by
    apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a) fields andProof andAxes andHyp
    exact Templates.canonical_exact Ty.bool a fields andTerm rfl aExact
  let andBeta := conjunctionBeta left right leftBool rightBool
  let pairLeft := pairTerm left right leftBool rightBool
  let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
  let pairPlan := Templates.pair (Templates.literal (.atom 4))
    (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
      (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
  let truthPairPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm pairTruth.term)
  let equationPlan := Templates.equality (.function ExcludedMiddle.boolBinaryTy Ty.bool) pairPlan truthPairPlan
  have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec pairLeft.term := by
    have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
      fields (.app (.bound 0) left.term) right.term
      (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) leftExact)
      (by simp [r,fields,mpFields,Indexed.instantiate])
    simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
    rfl
  have equationExact : Indexed.instantiate equationPlan fields = encodeWith dbTermCodec pairEquation.term :=
    Templates.equality_exact _ _ _ fields pairLeft.term pairTruth.term pairExact (Templates.literal_exact _ _)
  let bodyProof := eqMpResult andBeta.conclusion andProof pairEquation
  let bodyPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
    (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan)
  have andBetaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
    left right leftBool rightBool
  have bodyAxes : bodyProof.axioms = input.axioms ∪ premise.axioms := by
    simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.1,andAxes,Finset.empty_union]
  have bodyHyp : bodyProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
    simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.2.1,andHyp,Finset.empty_union]
  have bodyExact : Indexed.instantiate bodyPlan fields = encodeWith theoremCodec bodyProof := by
    apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan) fields bodyProof bodyAxes bodyHyp
    exact Templates.canonical_exact Ty.bool equationPlan fields pairEquation rfl equationExact
  let selectorPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
  let selected := selectedPair left right leftBool rightBool
  let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let selectedPlan := Templates.application pairPlan selectorPlan
  let selectedTruthPlan := Templates.application truthPairPlan selectorPlan
  have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
    Templates.application_exact pairPlan selectorPlan fields pairLeft.term secondSelector.term pairExact
      (Templates.literal_exact _ _)
  have selectedTruthExact : Indexed.instantiate selectedTruthPlan fields = encodeWith dbTermCodec selectedTruth.term :=
    Templates.application_exact truthPairPlan selectorPlan fields pairTruth.term secondSelector.term
      (Templates.literal_exact _ _) (Templates.literal_exact _ _)
  let selectorProof := reflexivity secondSelector
  let selectorProofPlan := Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool
    (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
  have selectorProofExact : Indexed.instantiate selectorProofPlan fields = encodeWith theoremCodec selectorProof := by
    apply Templates.theoremTemplate_exact ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
      fields selectorProof rfl rfl
    exact Templates.canonical_exact Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan)
      fields (CanonicalTerm.equalityOfSameType secondSelector secondSelector rfl) rfl
      (Templates.equality_exact ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan fields
        secondSelector.term secondSelector.term (Templates.literal_exact _ _) (Templates.literal_exact _ _))
  let result := appResult bodyProof selectorProof selected selectedTruth rfl
  let resultPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
    (input.sequent.hyp ∪ premise.sequent.hyp)
    (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan))
  have resultAxes : result.axioms = input.axioms ∪ premise.axioms := by
    simp only [result,appResult,Theorem.unionResult,bodyAxes,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
  have resultHyp : result.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
    simp only [result,appResult,Theorem.unionResult,bodyHyp,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
  have resultExact : Indexed.instantiate resultPlan fields = encodeWith theoremCodec result := by
    apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan)) fields result resultAxes resultHyp
    exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan) fields
      (CanonicalTerm.equalityOfSameType selected selectedTruth rfl) rfl
      (Templates.equality_exact Ty.bool selectedPlan selectedTruthPlan fields selected.term selectedTruth.term
        selectedExact selectedTruthExact)
  have requestExact : Indexed.instantiate (binaryRequest 2 bodyPlan selectorProofPlan) fields =
      encodeWith requestCodec (.inference (.mkComb bodyProof selectorProof)) := by
    simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
      bodyExact,selectorProofExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
      encodeData_pair,List.cons_append]
  have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
    simp [o,fields,mpFields,Indexed.instantiate]
  change some (some ((primitiveNodes 2 resultPlan (binaryRequest 2 bodyPlan selectorProofPlan) o).map
      (Node.map (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields)))) = some (some _)
  exact congrArg (fun nodes => some (some nodes))
    (primitiveNodes_exact 2 resultPlan (binaryRequest 2 bodyPlan selectorProofPlan) o fields
      (.inference (.mkComb bodyProof selectorProof)) result origin rfl resultExact requestExact originExact)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Transitivity retains every original ordered parent occurrence and full
claim, including the two joins carrying the incoming dependencies. -/
theorem mpTransMacros_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) (kind : Fin 4) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => (requests[(![10,14,15,16] : Fin 4 → Nat) kind]?).map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[(![10,14,15,16] : Fin 4 → Nat) kind]?).map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  fin_cases kind
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let selector : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
    let pairPlan := Templates.pair (Templates.literal (.atom 4))
      (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
        (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
    let selectedPlan := Templates.application pairPlan selector
    let reductionPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan r))
    let selected := selectedPair left right leftBool rightBool
    let pair := pairBeta left right leftBool rightBool
    let selectorBeta := ImplicationExpansion.selectorBeta left right leftBool rightBool
    let reduction := transResult pair.conclusion selectorBeta.conclusion selected right rightBool.symm
    have pairParts : pair.conclusion.axioms = ∅ ∧ pair.conclusion.sequent.hyp = ∅ := by
      simp [pair,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      left right leftBool rightBool
    have axioms : reduction.axioms = ∅ := by
      simp only [reduction,selectorBeta,ImplicationExpansion.selectorBeta,transResult,Theorem.unionResult,
        pairParts.1,selectorParts.1,Finset.empty_union]
    have hypotheses : reduction.sequent.hyp = ∅ := by
      simp only [reduction,selectorBeta,ImplicationExpansion.selectorBeta,transResult,Theorem.unionResult,
        pairParts.2,selectorParts.2.1,Finset.empty_union]
    have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec
        (pairTerm left right leftBool rightBool).term := by
      have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
        fields (.app (.bound 0) left.term) right.term
        (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate]))
        (by simp [r,fields,mpFields,Indexed.instantiate])
      simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
      rfl
    have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
      Templates.application_exact _ _ _ _ _ pairExact (Templates.literal_exact _ _)
    have reductionExact : Indexed.instantiate reductionPlan fields = encodeWith theoremCodec reduction := by
      apply Templates.theoremTemplate_exact _ _ _ _ _ axioms hypotheses
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan r) fields
        (CanonicalTerm.equalityOfSameType selected right rightBool.symm) rfl
        (Templates.equality_exact _ _ _ _ _ _ selectedExact (by simp [r,fields,mpFields,Indexed.instantiate]))
    let pairSlots : Fin 5 → Indexed.Template Alphabet 9 := ![l,r,[.inr 7],[.inr 8],o]
    let pairTemplates := substituteNodes pairSlots pairNodes
    let pairClaim : Indexed.Template Alphabet 9 := (pairTemplates.getLast?.map Node.conclusion).getD []
    have pairFieldsSame : (fun slot => Indexed.instantiate (pairSlots slot) fields) =
        pairFields left right pairLeftSource pairRightSource origin := by
      funext slot
      fin_cases slot <;> simp [pairSlots,l,r,o,fields,mpFields,pairFields,Indexed.instantiate]
    have pairNodesExact : pairTemplates.map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)) =
        (betaBlock pair origin).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
      rw [substituteNodes_exact,pairFieldsSame]
      exact pairNodes_exact left right leftBool rightBool leftEmpty rightEmpty
        pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin
    have pairClaimExact : Indexed.instantiate pairClaim fields = encodeWith theoremCodec pair.conclusion :=
      lastConclusion_exact pairTemplates (betaBlock pair origin).1 pairClaim pair.conclusion fields
        pairNodesExact (by rfl) (by rfl)
    let selectorSlots : Fin 5 → Indexed.Template Alphabet 9 := ![l,r,[.inr 4],[.inr 5],o]
    let selectorTemplates := substituteNodes selectorSlots (doubleBetaNodes Ty.bool Ty.bool Ty.bool (.bound 0) (by simp))
    let selectorClaim : Indexed.Template Alphabet 9 := (selectorTemplates.getLast?.map Node.conclusion).getD []
    have selectorFieldsSame : (fun slot => Indexed.instantiate (selectorSlots slot) fields) =
        doubleBetaFields left right origin := by
      funext slot
      fin_cases slot <;> simp [selectorSlots,l,r,o,fields,mpFields,doubleBetaFields,Indexed.instantiate]
    have selectorNodesExact : selectorTemplates.map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)) =
        (doubleBetaBlock selectorBeta origin).1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
      rw [substituteNodes_exact,selectorFieldsSame]
      exact doubleBetaNodes_exact Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
        left right leftBool rightBool leftEmpty leftNamed origin
    have selectorClaimExact : Indexed.instantiate selectorClaim fields = encodeWith theoremCodec selectorBeta.conclusion :=
      lastConclusion_exact selectorTemplates (doubleBetaBlock selectorBeta origin).1 selectorClaim selectorBeta.conclusion fields
        selectorNodesExact (by rfl) (by rfl)
    have requestExact : Indexed.instantiate (binaryRequest 1 pairClaim selectorClaim) fields =
        encodeWith requestCodec (.inference (.trans pair.conclusion selectorBeta.conclusion)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        pairClaimExact,selectorClaimExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 reductionPlan (binaryRequest 1 pairClaim selectorClaim) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 reductionPlan (binaryRequest 1 pairClaim selectorClaim) o fields
        (.inference (.trans pair.conclusion selectorBeta.conclusion)) reduction origin rfl reductionExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let truth : Indexed.Template Alphabet 9 := Templates.literal (putTerm PrimitiveSentences.truthDB)
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let pairPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm pairTruth.term)
    let selectorPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
    let selected := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let selectedPlan := Templates.application pairPlan selectorPlan
    let pair := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let selector := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let pairClaim : Indexed.Template Alphabet 9 := Templates.literal (theoremCodec.put pair.conclusion)
    let selectorClaim : Indexed.Template Alphabet 9 := Templates.literal (theoremCodec.put selector.conclusion)
    let result := transResult pair.conclusion selector.conclusion selected DerivedRules.truthTerm rfl
    let resultPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan truth))
    have pairParts : pair.conclusion.axioms = ∅ ∧ pair.conclusion.sequent.hyp = ∅ := by
      simp [pair,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have resultAxes : result.axioms = ∅ := by
      simp only [result,selector,selectorBeta,transResult,Theorem.unionResult,pairParts.1,selectorParts.1,Finset.empty_union]
    have resultHyp : result.sequent.hyp = ∅ := by
      simp only [result,selector,selectorBeta,transResult,Theorem.unionResult,pairParts.2,selectorParts.2.1,Finset.empty_union]
    have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
      Templates.application_exact pairPlan selectorPlan fields pairTruth.term secondSelector.term
        (Templates.literal_exact _ _) (Templates.literal_exact _ _)
    have resultExact : Indexed.instantiate resultPlan fields = encodeWith theoremCodec result := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan truth)) fields result resultAxes resultHyp
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan truth) fields
        (CanonicalTerm.equalityOfSameType selected DerivedRules.truthTerm rfl) rfl
        (Templates.equality_exact Ty.bool selectedPlan truth fields selected.term DerivedRules.truthTerm.term
          selectedExact (Templates.literal_exact _ _))
    have requestExact : Indexed.instantiate (binaryRequest 1 pairClaim selectorClaim) fields =
        encodeWith requestCodec (.inference (.trans pair.conclusion selector.conclusion)) := by
      simp only [pairClaim,selectorClaim,binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 resultPlan (binaryRequest 1 pairClaim selectorClaim) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 resultPlan (binaryRequest 1 pairClaim selectorClaim) o fields
        (.inference (.trans pair.conclusion selector.conclusion)) result origin rfl resultExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r, fields, mpFields, Indexed.instantiate]
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let reversedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool l a))
    have reversedAxes : reversed.axioms = input.axioms := axioms
    have reversedHyp : reversed.sequent.hyp = input.sequent.hyp := hypotheses
    have leftExact : Indexed.instantiate l fields = encodeWith dbTermCodec left.term := by
      simp [l,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
        (Templates.canonical Ty.bool (Templates.equality Ty.bool l a)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool l a) fields
        (CanonicalTerm.equalityOfSameType left andTerm leftBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType, leftBool] using
        Templates.equality_exact Ty.bool l a fields left.term andTerm.term leftExact aExact
    let andProof := eqMpResult reversed premise andTerm
    let andPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a)
    have andAxes : andProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedAxes]
    have andHyp : andProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedHyp]
    have andExact : Indexed.instantiate andPlan fields = encodeWith theoremCodec andProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a) fields andProof andAxes andHyp
      exact Templates.canonical_exact Ty.bool a fields andTerm rfl aExact
    let andBeta := conjunctionBeta left right leftBool rightBool
    let pairLeft := pairTerm left right leftBool rightBool
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
    let pairPlan := Templates.pair (Templates.literal (.atom 4))
      (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
        (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
    let truthPairPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm pairTruth.term)
    let equationPlan := Templates.equality (.function ExcludedMiddle.boolBinaryTy Ty.bool) pairPlan truthPairPlan
    have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec pairLeft.term := by
      have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
        fields (.app (.bound 0) left.term) right.term
        (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) leftExact)
        (by simp [r,fields,mpFields,Indexed.instantiate])
      simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
      rfl
    have equationExact : Indexed.instantiate equationPlan fields = encodeWith dbTermCodec pairEquation.term :=
      Templates.equality_exact _ _ _ fields pairLeft.term pairTruth.term pairExact (Templates.literal_exact _ _)
    let bodyProof := eqMpResult andBeta.conclusion andProof pairEquation
    let bodyPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan)
    have andBetaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
      left right leftBool rightBool
    have bodyAxes : bodyProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.1,andAxes,Finset.empty_union]
    have bodyHyp : bodyProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.2.1,andHyp,Finset.empty_union]
    have bodyExact : Indexed.instantiate bodyPlan fields = encodeWith theoremCodec bodyProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan) fields bodyProof bodyAxes bodyHyp
      exact Templates.canonical_exact Ty.bool equationPlan fields pairEquation rfl equationExact
    let selectorPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
    let selected := selectedPair left right leftBool rightBool
    let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let selectedPlan := Templates.application pairPlan selectorPlan
    let selectedTruthPlan := Templates.application truthPairPlan selectorPlan
    have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
      Templates.application_exact pairPlan selectorPlan fields pairLeft.term secondSelector.term pairExact
        (Templates.literal_exact _ _)
    have selectedTruthExact : Indexed.instantiate selectedTruthPlan fields = encodeWith dbTermCodec selectedTruth.term :=
      Templates.application_exact truthPairPlan selectorPlan fields pairTruth.term secondSelector.term
        (Templates.literal_exact _ _) (Templates.literal_exact _ _)
    let selectorProof := reflexivity secondSelector
    let selectorProofPlan := Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool
      (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
    have selectorProofExact : Indexed.instantiate selectorProofPlan fields = encodeWith theoremCodec selectorProof := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
        fields selectorProof rfl rfl
      exact Templates.canonical_exact Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan)
        fields (CanonicalTerm.equalityOfSameType secondSelector secondSelector rfl) rfl
        (Templates.equality_exact ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan fields
          secondSelector.term secondSelector.term (Templates.literal_exact _ _) (Templates.literal_exact _ _))
    let bodyApplication := appResult bodyProof selectorProof selected selectedTruth rfl
    let applicationPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan))
    have applicationAxes : bodyApplication.axioms = input.axioms ∪ premise.axioms := by
      simp only [bodyApplication,appResult,Theorem.unionResult,bodyAxes,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have applicationHyp : bodyApplication.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [bodyApplication,appResult,Theorem.unionResult,bodyHyp,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have applicationExact : Indexed.instantiate applicationPlan fields = encodeWith theoremCodec bodyApplication := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan)) fields bodyApplication applicationAxes applicationHyp
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan) fields
        (CanonicalTerm.equalityOfSameType selected selectedTruth rfl) rfl
        (Templates.equality_exact Ty.bool selectedPlan selectedTruthPlan fields selected.term selectedTruth.term
          selectedExact selectedTruthExact)
    let pairBetaExpansion := pairBeta left right leftBool rightBool
    let selectorBetaExpansion := selectorBeta left right leftBool rightBool
    let reduction := transResult pairBetaExpansion.conclusion selectorBetaExpansion.conclusion selected right rightBool.symm
    let reversed := symmetryResult reduction selected right rightBool.symm
    let reversedPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedPlan))
    have pairParts : pairBetaExpansion.conclusion.axioms = ∅ ∧ pairBetaExpansion.conclusion.sequent.hyp = ∅ := by
      simp [pairBetaExpansion,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      left right leftBool rightBool
    have reversedAxes : reversed.axioms = ∅ := by
      simp only [reversed,reduction,selectorBetaExpansion,selectorBeta,symmetryResult,transResult,
        Theorem.preserveAxiomsResult,Theorem.unionResult,pairParts.1,selectorParts.1,Finset.empty_union]
    have reversedHyp : reversed.sequent.hyp = ∅ := by
      simp only [reversed,reduction,selectorBetaExpansion,selectorBeta,symmetryResult,transResult,
        Theorem.preserveAxiomsResult,Theorem.unionResult,pairParts.2,selectorParts.2.1,Finset.empty_union]
    have rightExact : Indexed.instantiate r fields = encodeWith dbTermCodec right.term := by
      simp [r,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedPlan)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r selectedPlan) fields
        (CanonicalTerm.equalityOfSameType right selected rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType,rightBool] using
        Templates.equality_exact Ty.bool r selectedPlan fields right.term selected.term rightExact selectedExact
    let result := transResult reversed bodyApplication right selectedTruth rightBool
    let resultPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedTruthPlan))
    have resultAxes : result.axioms = input.axioms ∪ premise.axioms := by
      simp only [result,transResult,Theorem.unionResult,reversedAxes,applicationAxes,Finset.empty_union]
    have resultHyp : result.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [result,transResult,Theorem.unionResult,reversedHyp,applicationHyp,Finset.empty_union]
    have resultExact : Indexed.instantiate resultPlan fields = encodeWith theoremCodec result := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedTruthPlan)) fields result resultAxes resultHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r selectedTruthPlan) fields
        (CanonicalTerm.equalityOfSameType right selectedTruth rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType,rightBool] using
        Templates.equality_exact Ty.bool r selectedTruthPlan fields right.term selectedTruth.term rightExact selectedTruthExact
    have requestExact : Indexed.instantiate (binaryRequest 1 reversedPlan applicationPlan) fields =
        encodeWith requestCodec (.inference (.trans reversed bodyApplication)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        reversedExact,applicationExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 resultPlan (binaryRequest 1 reversedPlan applicationPlan) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 resultPlan (binaryRequest 1 reversedPlan applicationPlan) o fields
        (.inference (.trans reversed bodyApplication)) result origin rfl resultExact requestExact originExact)
  · let fields := mpFields input premise left right pairLeftSource pairRightSource origin
    let l : Indexed.Template Alphabet 9 := [.inr 2]
    let r : Indexed.Template Alphabet 9 := [.inr 3]
    let o : Indexed.Template Alphabet 9 := [.inr 6]
    let a := Templates.application (Templates.application (Templates.literal (putTerm andDB)) l) r
    let andTerm := conjunction left right leftBool rightBool
    let andEquation := CanonicalTerm.equalityOfSameType andTerm left leftBool.symm
    let impBeta := implicationBeta left right leftBool rightBool
    let converted := eqMpResult impBeta.conclusion input andEquation
    have betaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool implicationBody
      implicationBody_checked left right leftBool rightBool
    have axioms : converted.axioms = input.axioms := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.1, Finset.empty_union]
    have hypotheses : converted.sequent.hyp = input.sequent.hyp := by
      simp only [converted, impBeta, implicationBeta, eqMpResult, Theorem.unionResult, betaParts.2.1, Finset.empty_union]
    have aExact : Indexed.instantiate a fields = encodeWith dbTermCodec andTerm.term := by
      apply Templates.application_exact
      · exact Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) (by simp [l,fields,mpFields,Indexed.instantiate])
      · simp [r, fields, mpFields, Indexed.instantiate]
    let reversed := symmetryResult converted andTerm left leftBool.symm
    let reversedPlan := Templates.theoremTemplate input.axioms input.sequent.hyp
      (Templates.canonical Ty.bool (Templates.equality Ty.bool l a))
    have reversedAxes : reversed.axioms = input.axioms := axioms
    have reversedHyp : reversed.sequent.hyp = input.sequent.hyp := hypotheses
    have leftExact : Indexed.instantiate l fields = encodeWith dbTermCodec left.term := by
      simp [l,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact input.axioms input.sequent.hyp
        (Templates.canonical Ty.bool (Templates.equality Ty.bool l a)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool l a) fields
        (CanonicalTerm.equalityOfSameType left andTerm leftBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType, leftBool] using
        Templates.equality_exact Ty.bool l a fields left.term andTerm.term leftExact aExact
    let andProof := eqMpResult reversed premise andTerm
    let andPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a)
    have andAxes : andProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedAxes]
    have andHyp : andProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [andProof,eqMpResult,Theorem.unionResult,reversedHyp]
    have andExact : Indexed.instantiate andPlan fields = encodeWith theoremCodec andProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool a) fields andProof andAxes andHyp
      exact Templates.canonical_exact Ty.bool a fields andTerm rfl aExact
    let andBeta := conjunctionBeta left right leftBool rightBool
    let pairLeft := pairTerm left right leftBool rightBool
    let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let pairEquation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
    let pairPlan := Templates.pair (Templates.literal (.atom 4))
      (Templates.pair (Templates.literal (putTy ExcludedMiddle.boolBinaryTy))
        (Templates.application (Templates.application (Templates.literal (putTerm (.bound 0))) l) r))
    let truthPairPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm pairTruth.term)
    let equationPlan := Templates.equality (.function ExcludedMiddle.boolBinaryTy Ty.bool) pairPlan truthPairPlan
    have pairExact : Indexed.instantiate pairPlan fields = encodeWith dbTermCodec pairLeft.term := by
      have applications := Templates.application_exact (Templates.application (Templates.literal (putTerm (.bound 0))) l) r
        fields (.app (.bound 0) left.term) right.term
        (Templates.application_exact _ _ _ _ _ (Templates.literal_exact _ _) leftExact)
        (by simp [r,fields,mpFields,Indexed.instantiate])
      simp only [pairPlan,Templates.pair_exact,Templates.literal_exact,applications]
      rfl
    have equationExact : Indexed.instantiate equationPlan fields = encodeWith dbTermCodec pairEquation.term :=
      Templates.equality_exact _ _ _ fields pairLeft.term pairTruth.term pairExact (Templates.literal_exact _ _)
    let bodyProof := eqMpResult andBeta.conclusion andProof pairEquation
    let bodyPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan)
    have andBetaParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool conjunctionBody conjunctionBody_checked
      left right leftBool rightBool
    have bodyAxes : bodyProof.axioms = input.axioms ∪ premise.axioms := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.1,andAxes,Finset.empty_union]
    have bodyHyp : bodyProof.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [bodyProof,andBeta,conjunctionBeta,eqMpResult,Theorem.unionResult,andBetaParts.2.1,andHyp,Finset.empty_union]
    have bodyExact : Indexed.instantiate bodyPlan fields = encodeWith theoremCodec bodyProof := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp) (Templates.canonical Ty.bool equationPlan) fields bodyProof bodyAxes bodyHyp
      exact Templates.canonical_exact Ty.bool equationPlan fields pairEquation rfl equationExact
    let selectorPlan : Indexed.Template Alphabet 9 := Templates.literal (putTerm DerivedRules.selectSecondDB)
    let selected := selectedPair left right leftBool rightBool
    let selectedTruth := selectedPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let selectedPlan := Templates.application pairPlan selectorPlan
    let selectedTruthPlan := Templates.application truthPairPlan selectorPlan
    have selectedExact : Indexed.instantiate selectedPlan fields = encodeWith dbTermCodec selected.term :=
      Templates.application_exact pairPlan selectorPlan fields pairLeft.term secondSelector.term pairExact
        (Templates.literal_exact _ _)
    have selectedTruthExact : Indexed.instantiate selectedTruthPlan fields = encodeWith dbTermCodec selectedTruth.term :=
      Templates.application_exact truthPairPlan selectorPlan fields pairTruth.term secondSelector.term
        (Templates.literal_exact _ _) (Templates.literal_exact _ _)
    let selectorProof := reflexivity secondSelector
    let selectorProofPlan := Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool
      (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
    have selectorProofExact : Indexed.instantiate selectorProofPlan fields = encodeWith theoremCodec selectorProof := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan))
        fields selectorProof rfl rfl
      exact Templates.canonical_exact Ty.bool (Templates.equality ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan)
        fields (CanonicalTerm.equalityOfSameType secondSelector secondSelector rfl) rfl
        (Templates.equality_exact ExcludedMiddle.boolBinaryTy selectorPlan selectorPlan fields
          secondSelector.term secondSelector.term (Templates.literal_exact _ _) (Templates.literal_exact _ _))
    let bodyApplication := appResult bodyProof selectorProof selected selectedTruth rfl
    let applicationPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan))
    have applicationAxes : bodyApplication.axioms = input.axioms ∪ premise.axioms := by
      simp only [bodyApplication,appResult,Theorem.unionResult,bodyAxes,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have applicationHyp : bodyApplication.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [bodyApplication,appResult,Theorem.unionResult,bodyHyp,selectorProof,reflexivity,Theorem.emptyResult,Finset.union_empty]
    have applicationExact : Indexed.instantiate applicationPlan fields = encodeWith theoremCodec bodyApplication := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan)) fields bodyApplication applicationAxes applicationHyp
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedPlan selectedTruthPlan) fields
        (CanonicalTerm.equalityOfSameType selected selectedTruth rfl) rfl
        (Templates.equality_exact Ty.bool selectedPlan selectedTruthPlan fields selected.term selectedTruth.term
          selectedExact selectedTruthExact)
    let pairBetaExpansion := pairBeta left right leftBool rightBool
    let selectorBetaExpansion := selectorBeta left right leftBool rightBool
    let reduction := transResult pairBetaExpansion.conclusion selectorBetaExpansion.conclusion selected right rightBool.symm
    let reversed := symmetryResult reduction selected right rightBool.symm
    let reversedPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedPlan))
    have pairParts : pairBetaExpansion.conclusion.axioms = ∅ ∧ pairBetaExpansion.conclusion.sequent.hyp = ∅ := by
      simp [pairBetaExpansion,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have selectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      left right leftBool rightBool
    have reversedAxes : reversed.axioms = ∅ := by
      simp only [reversed,reduction,selectorBetaExpansion,selectorBeta,symmetryResult,transResult,
        Theorem.preserveAxiomsResult,Theorem.unionResult,pairParts.1,selectorParts.1,Finset.empty_union]
    have reversedHyp : reversed.sequent.hyp = ∅ := by
      simp only [reversed,reduction,selectorBetaExpansion,selectorBeta,symmetryResult,transResult,
        Theorem.preserveAxiomsResult,Theorem.unionResult,pairParts.2,selectorParts.2.1,Finset.empty_union]
    have rightExact : Indexed.instantiate r fields = encodeWith dbTermCodec right.term := by
      simp [r,fields,mpFields,Indexed.instantiate]
    have reversedExact : Indexed.instantiate reversedPlan fields = encodeWith theoremCodec reversed := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedPlan)) fields reversed reversedAxes reversedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r selectedPlan) fields
        (CanonicalTerm.equalityOfSameType right selected rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType,rightBool] using
        Templates.equality_exact Ty.bool r selectedPlan fields right.term selected.term rightExact selectedExact
    let joinedLeft := transResult reversed bodyApplication right selectedTruth rightBool
    let joinedPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedTruthPlan))
    have joinedAxes : joinedLeft.axioms = input.axioms ∪ premise.axioms := by
      simp only [joinedLeft,transResult,Theorem.unionResult,reversedAxes,applicationAxes,Finset.empty_union]
    have joinedHyp : joinedLeft.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [joinedLeft,transResult,Theorem.unionResult,reversedHyp,applicationHyp,Finset.empty_union]
    have joinedExact : Indexed.instantiate joinedPlan fields = encodeWith theoremCodec joinedLeft := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool r selectedTruthPlan)) fields joinedLeft joinedAxes joinedHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r selectedTruthPlan) fields
        (CanonicalTerm.equalityOfSameType right selectedTruth rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType,rightBool] using
        Templates.equality_exact Ty.bool r selectedTruthPlan fields right.term selectedTruth.term rightExact selectedTruthExact
    let truth : Indexed.Template Alphabet 9 := Templates.literal (putTerm PrimitiveSentences.truthDB)
    let truthPairBeta := pairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthSelectorBeta := selectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    let truthReduction := transResult truthPairBeta.conclusion truthSelectorBeta.conclusion selectedTruth DerivedRules.truthTerm rfl
    let truthReductionPlan := Templates.theoremTemplate ∅ ∅
      (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedTruthPlan truth))
    have truthPairParts : truthPairBeta.conclusion.axioms = ∅ ∧ truthPairBeta.conclusion.sequent.hyp = ∅ := by
      simp [truthPairBeta,pairBeta,betaExpansion_conclusion,Theorem.emptyResult]
    have truthSelectorParts := doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 0) (by simp)
      DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
    have truthReductionAxes : truthReduction.axioms = ∅ := by
      simp only [truthReduction,truthSelectorBeta,selectorBeta,transResult,Theorem.unionResult,
        truthPairParts.1,truthSelectorParts.1,Finset.empty_union]
    have truthReductionHyp : truthReduction.sequent.hyp = ∅ := by
      simp only [truthReduction,truthSelectorBeta,selectorBeta,transResult,Theorem.unionResult,
        truthPairParts.2,truthSelectorParts.2.1,Finset.empty_union]
    have truthReductionExact : Indexed.instantiate truthReductionPlan fields = encodeWith theoremCodec truthReduction := by
      apply Templates.theoremTemplate_exact ∅ ∅
        (Templates.canonical Ty.bool (Templates.equality Ty.bool selectedTruthPlan truth)) fields
        truthReduction truthReductionAxes truthReductionHyp
      exact Templates.canonical_exact Ty.bool (Templates.equality Ty.bool selectedTruthPlan truth) fields
        (CanonicalTerm.equalityOfSameType selectedTruth DerivedRules.truthTerm rfl) rfl
        (Templates.equality_exact Ty.bool selectedTruthPlan truth fields selectedTruth.term DerivedRules.truthTerm.term
          selectedTruthExact (Templates.literal_exact _ _))
    let result := transResult joinedLeft truthReduction right DerivedRules.truthTerm rightBool
    let resultPlan := Templates.theoremTemplate (input.axioms ∪ premise.axioms)
      (input.sequent.hyp ∪ premise.sequent.hyp)
      (Templates.canonical Ty.bool (Templates.equality Ty.bool r truth))
    have resultAxes : result.axioms = input.axioms ∪ premise.axioms := by
      simp only [result,transResult,Theorem.unionResult,joinedAxes,truthReductionAxes,Finset.union_empty]
    have resultHyp : result.sequent.hyp = input.sequent.hyp ∪ premise.sequent.hyp := by
      simp only [result,transResult,Theorem.unionResult,joinedHyp,truthReductionHyp,Finset.union_empty]
    have resultExact : Indexed.instantiate resultPlan fields = encodeWith theoremCodec result := by
      apply Templates.theoremTemplate_exact (input.axioms ∪ premise.axioms)
        (input.sequent.hyp ∪ premise.sequent.hyp)
        (Templates.canonical Ty.bool (Templates.equality Ty.bool r truth)) fields result resultAxes resultHyp
      apply Templates.canonical_exact Ty.bool (Templates.equality Ty.bool r truth) fields
        (CanonicalTerm.equalityOfSameType right DerivedRules.truthTerm rightBool) rfl
      simpa only [CanonicalTerm.equalityOfSameType,DerivedRules.truthTerm,rightBool] using
        Templates.equality_exact Ty.bool r truth fields right.term DerivedRules.truthTerm.term
          rightExact (Templates.literal_exact _ _)
    have requestExact : Indexed.instantiate (binaryRequest 1 joinedPlan truthReductionPlan) fields =
        encodeWith requestCodec (.inference (.trans joinedLeft truthReduction)) := by
      simp only [binaryRequest,unaryRequest,Templates.pair_exact,Templates.literal_exact,
        joinedExact,truthReductionExact,encodeWith,requestCodec,ProofDataEncoding.putRequest,ProofDataEncoding.putInference,
        encodeData_pair,List.cons_append]
    have originExact : Indexed.instantiate o fields = encodeWith originCodec origin := by
      simp [o,fields,mpFields,Indexed.instantiate]
    change some (some ((primitiveNodes 2 resultPlan (binaryRequest 1 joinedPlan truthReductionPlan) o).map
        (Node.map (fun template => Indexed.instantiate template fields)
          (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)))) = some (some _)
    exact congrArg (fun nodes => some (some nodes))
      (primitiveNodes_exact 2 resultPlan (binaryRequest 1 joinedPlan truthReductionPlan) o fields
        (.inference (.trans joinedLeft truthReduction)) result origin rfl resultExact requestExact originExact)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- Every local MP witness lowers to the original primitive nodes. This joins all twenty macro families while preserving their ordered occurrences. -/
theorem mpWitnessNodes_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => requests.map (fun request => request.witness.1.map
        (Node.map (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template
            (mpFields input premise left right pairLeftSource pairRightSource origin))))) =
      some ((mpPlan input premise left right leftBool rightBool origin).1.map
        (fun request => request.witness.1.map
          (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let lower := Node.map (fun template => Indexed.instantiate template fields)
    (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)
  let encode := Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)
  have entries : ∀ index : Fin 20,
      (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
        (fun requests => (requests[index.val]?).map (fun request => request.witness.1.map lower)) =
      some (((mpPlan input premise left right leftBool rightBool origin).1[index.val]?).map
        (fun request => request.witness.1.map encode)) := by
    intro index
    fin_cases index
    · exact mpDoubleBetaMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 0
    · exact mpEqMpMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 0
    · exact mpSymmetryMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 0
    · exact mpEqMpMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 1
    · exact mpDoubleBetaMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 1
    · exact mpEqMpMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 2
    · exact mpReflexivityMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 0
    · exact mpCombinationMacro_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin
    · exact mpPairMacro_lowered input premise left right leftBool rightBool leftEmpty rightEmpty pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin
    · exact mpDoubleBetaMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 2
    · exact mpTransMacros_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin 0
    · exact mpSymmetryMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 1
    · exact mpFixedMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 0
    · exact mpFixedMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 1
    · exact mpTransMacros_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin 1
    · exact mpTransMacros_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin 2
    · exact mpTransMacros_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin 3
    · exact mpSymmetryMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 2
    · exact mpReflexivityMacros_lowered input premise left right leftBool rightBool pairLeftSource pairRightSource origin 1
    · exact mpEqMpMacros_lowered input premise left right leftBool rightBool leftEmpty leftNamed pairLeftSource pairRightSource origin 3
  have templateCount :
      (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map List.length = some 20 := by rfl
  cases formed : mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp with
  | none => simp [formed] at templateCount
  | some requests =>
      have count : requests.length = 20 := by simpa [formed] using templateCount
      have sourceCount : (mpPlan input premise left right leftBool rightBool origin).1.length = 20 := rfl
      apply congrArg some
      apply List.ext_getElem?
      intro index
      by_cases inside : index < 20
      · have entry := entries ⟨index,inside⟩
        simp only [formed,Option.map_some] at entry
        simpa only [List.getElem?_map] using Option.some.inj entry
      · rw [List.getElem?_eq_none (by simpa [List.length_map,count] using Nat.le_of_not_gt inside),
          List.getElem?_eq_none (by simpa [List.length_map,sourceCount] using Nat.le_of_not_gt inside)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The complete MP macro requests retain the original conclusions, local roots, parent lists, primitive requests and provenance under field lowering. -/
theorem mpRequests_lowered (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin) :
    (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
      (fun requests => requests.map (Node.map
        (fun template => Indexed.instantiate template (mpFields input premise left right pairLeftSource pairRightSource origin))
        (fun block => (block.1.map (Node.map
          (fun template => Indexed.instantiate template (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template (mpFields input premise left right pairLeftSource pairRightSource origin))
          (fun template => Indexed.instantiate template (mpFields input premise left right pairLeftSource pairRightSource origin))), block.2))
        (fun template => Indexed.instantiate template (mpFields input premise left right pairLeftSource pairRightSource origin)))) =
      some ((mpPlan input premise left right leftBool rightBool origin).1.map (Node.map
        (encodeWith theoremCodec)
        (fun block => (block.1.map (Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)), block.2))
        (encodeWith originCodec))) := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let lower := Node.map (fun template => Indexed.instantiate template fields)
    (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)
  let encode := Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)
  let source := (mpPlan input premise left right leftBool rightBool origin).1
  have witnesses := mpWitnessNodes_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin
  have templateFinal :
      (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
        (fun requests => requests.map (fun request => request.witness.1.getLast?.map Node.conclusion)) =
      (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
        (fun requests => requests.map (fun request => some request.conclusion)) := by rfl
  have sourceFinal : source.map (fun request => request.witness.1.getLast?.map Node.conclusion) =
      source.map (fun request => some request.conclusion) := by rfl
  have metadata :
      (mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).map
        (fun requests => requests.map (fun request => (request.witness.2,request.parents,Indexed.instantiate request.origin fields))) =
      some (source.map (fun request => (request.witness.2,request.parents,encodeWith originCodec request.origin))) := by
    change some [ (6,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[2,0],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (5,[3],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[4,1],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (6,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[6,5],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (0,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[7,8],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (1,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (6,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[10,11],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (5,[12],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (1,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (6,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[14,15],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[13,9],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[17,16],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (5,[18],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (0,[],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields), (2,[19,20],Indexed.instantiate ([.inr 6] : Indexed.Template Alphabet 9) fields) ] = some [ (6,[],encodeWith originCodec origin), (2,[2,0],encodeWith originCodec origin), (5,[3],encodeWith originCodec origin), (2,[4,1],encodeWith originCodec origin), (6,[],encodeWith originCodec origin), (2,[6,5],encodeWith originCodec origin), (0,[],encodeWith originCodec origin), (2,[7,8],encodeWith originCodec origin), (1,[],encodeWith originCodec origin), (6,[],encodeWith originCodec origin), (2,[10,11],encodeWith originCodec origin), (5,[12],encodeWith originCodec origin), (1,[],encodeWith originCodec origin), (6,[],encodeWith originCodec origin), (2,[14,15],encodeWith originCodec origin), (2,[13,9],encodeWith originCodec origin), (2,[17,16],encodeWith originCodec origin), (5,[18],encodeWith originCodec origin), (0,[],encodeWith originCodec origin), (2,[19,20],encodeWith originCodec origin) ]
    simp [fields,mpFields,Indexed.instantiate]
  cases formed : mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp with
  | none => simp [formed] at witnesses
  | some requests =>
      simp only [formed,Option.map_some] at witnesses templateFinal metadata
      have witnessLists := Option.some.inj witnesses
      change requests.map (fun request => request.witness.1.map lower) =
        source.map (fun request => request.witness.1.map encode) at witnessLists
      have templateFinalLists := Option.some.inj templateFinal
      have metadataLists := Option.some.inj metadata
      apply congrArg some
      apply List.ext_getElem?
      intro index
      have localNodes := congrArg (fun values => values[index]?) witnessLists
      have localPlanLast := congrArg (fun values => values[index]?) templateFinalLists
      have localSourceLast := congrArg (fun values => values[index]?) sourceFinal
      have localMetadata := congrArg (fun values => values[index]?) metadataLists
      simp only [List.getElem?_map] at localNodes localPlanLast localSourceLast localMetadata ⊢
      cases planAt : requests[index]? with
      | none =>
          cases sourceAt : source[index]? with
          | none => rfl
          | some actual => simp [planAt,sourceAt] at localNodes
      | some planned =>
          cases sourceAt : source[index]? with
          | none => simp [planAt,sourceAt] at localNodes
          | some actual =>
              simp only [planAt,sourceAt,Option.map_some] at localNodes localPlanLast localSourceLast localMetadata ⊢
              have nodesExact := Option.some.inj localNodes
              have planLast := Option.some.inj localPlanLast
              have actualLast := Option.some.inj localSourceLast
              have structures := Option.some.inj localMetadata
              have claimExact := lastConclusion_exact planned.witness.1 actual.witness.1 planned.conclusion
                actual.conclusion fields nodesExact planLast actualLast
              have rootsExact : planned.witness.2 = actual.witness.2 := congrArg (fun value => value.1) structures
              have parentsExact : planned.parents = actual.parents := congrArg (fun value => value.2.1) structures
              have originExact : Indexed.instantiate planned.origin fields = encodeWith originCodec actual.origin :=
                congrArg (fun value => value.2.2) structures
              apply congrArg some
              change (⟨Indexed.instantiate planned.conclusion fields,
                (planned.witness.1.map lower,planned.witness.2), planned.parents,
                Indexed.instantiate planned.origin fields⟩ : Node (List Alphabet)
                  (List (Node (List Alphabet) (List Alphabet) (List Alphabet)) × Nat) (List Alphabet)) =
                ⟨encodeWith theoremCodec actual.conclusion,
                  (actual.witness.1.map encode,actual.witness.2), actual.parents, encodeWith originCodec actual.origin⟩
              simp only [claimExact,nodesExact,rootsExact,parentsExact,originExact]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
/-- The complete emitted MP certificate is byte-exactly the original checked block, including the two external roots and all fifty-eight primitive occurrences. -/
theorem mpTemplate_exact (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin)
    (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (block : ProofSystem.Certificate)
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    Indexed.instantiate (mpTemplate input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp)
      (mpFields input premise left right pairLeftSource pairRightSource origin) = ProofDataEncoding.encodeCertificate block := by
  let fields := mpFields input premise left right pairLeftSource pairRightSource origin
  let source := (mpPlan input premise left right leftBool rightBool origin).1
  let lower := Node.map (fun template => Indexed.instantiate template fields)
    (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)
  let encode := Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)
  have finished : GraphExpansion.finishPlan policy (GraphExpansion.start [input,premise]) #[0,1] source 21 = some block := by
    simpa only [mpTypedBlock?,mpExpansion_requests] using computed
  have sourceAssembly := GraphExpansion.finishPlan_expanded (GraphExpansion.start_checked policy [input,premise]) finished
  change (do let (nodes,roots) ← GraphExpansion.expandFrom [] #[0,1] source 2
             let root ← roots[21]?
             pure (nodes,root)) = some block at sourceAssembly
  have sourceTransport := GraphExpansion.expandFrom_selected_bind_map (encodeWith theoremCodec)
    (encodeWith requestCodec) (encodeWith originCodec) #[0,1] source 21 2
  have encodedComputed := congrArg
    (Option.map (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2))) sourceAssembly
  simp only [Option.map_some] at encodedComputed
  have sourceMapped := sourceTransport.trans encodedComputed
  have requestTransport := mpRequests_lowered input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin
  cases formed : mpRequests? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp with
  | none => simp [formed] at requestTransport
  | some requests =>
      simp only [formed,Option.map_some] at requestTransport
      have requestsExact := Option.some.inj requestTransport
      change requests.map (Node.map (fun template => Indexed.instantiate template fields)
        (fun (localBlock : List (Node (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9) (Indexed.Template Alphabet 9)) × Nat) => (localBlock.1.map lower,localBlock.2)) (fun template => Indexed.instantiate template fields)) =
        source.map (Node.map (encodeWith theoremCodec) (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2)) (encodeWith originCodec)) at requestsExact
      have targetTransport := GraphExpansion.expandFrom_selected_bind_map_of_eq
        (fun template => Indexed.instantiate template fields) (fun template => Indexed.instantiate template fields)
        (fun template => Indexed.instantiate template fields) #[0,1] requests
        (source.map (Node.map (encodeWith theoremCodec)
          (fun (localBlock : ProofSystem.Certificate) => (localBlock.1.map encode,localBlock.2)) (encodeWith originCodec)))
        21 2 (block.1.map encode,block.2) requestsExact sourceMapped
      cases assembled : GraphExpansion.expandFrom [] #[0,1] requests 2 with
      | none => simp [assembled] at targetTransport
      | some result =>
          rcases result with ⟨nodes,roots⟩
          cases selected : roots[21]? with
          | none => simp [assembled,selected] at targetTransport
          | some root =>
              have aligned : (block.1.map encode,block.2) = (nodes.map lower,root) := by
                symm
                simpa [assembled,selected] using targetTransport
              have templateComputed : mpTemplate? input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp =
                  some (certificateTemplate (nodes,root)) := by
                simp [mpTemplate?,formed,assembled,selected]
              have templateSame := Option.some.inj
                ((mpTemplate_computed input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).symm.trans templateComputed)
              rw [templateSame]
              have nodesExact : nodes.map lower = block.1.map encode := (congrArg Prod.fst aligned).symm
              have rootExact : root = block.2 := (congrArg Prod.snd aligned).symm
              rw [rootExact]
              exact certificateTemplate_of_nodes nodes block.1 block.2 fields nodesExact

/-- The actual finite field-emission machine produces the complete original
MP certificate. Its clock charges every supplied field and every emitted
occurrence; constructing the fields and choosing the dependency basis remain
separate operational phases. -/
def mpOutputs (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin)
    (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (block : ProofSystem.Certificate)
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    TM2OutputsInTime
      (Indexed.machine (mpTemplate input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp))
      (mpInput input premise left right pairLeftSource pairRightSource origin)
      (some (encodeCertificate block))
      (4 * ((mpTemplate input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp).length + 1) *
        ((mpInput input premise left right pairLeftSource pairRightSource origin).length + 1)) := by
  have ran := Indexed.outputs (mpTemplate input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp)
    (mpFields input premise left right pairLeftSource pairRightSource origin)
  have same := mpTemplate_exact input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy shape matching block computed
  exact same ▸ ran

/-- Decoding the emitted whole MP program returns the original block,
retaining its ordinary HOL replay authority and both external premises. -/
theorem mp_decodes (input premise : Theorem) (left right : CanonicalTerm)
    (leftBool : left.ty = Ty.bool) (rightBool : right.ty = Ty.bool)
    (leftEmpty : freeNames left.term = []) (rightEmpty : freeNames right.term = [])
    (leftNamed : ∀ binders, named? left.term binders = some (checkedSource left).source)
    (pairLeftSource pairRightSource : SourceTerm)
    (pairLeftNamed : named? left.term [pairNeedle] = some pairLeftSource)
    (pairRightNamed : named? right.term [pairNeedle] = some pairRightSource)
    (origin : ProofExecution.Origin)
    (policy : AxiomPolicy) [DecidablePred policy]
    (shape : input.sequent.concl.term = ExcludedMiddle.impAppDB left.term right.term)
    (matching : premise.sequent.concl = left) (block : ProofSystem.Certificate)
    (computed : mpTypedBlock? policy input premise left right leftBool rightBool shape matching origin = some block) :
    decodeCertificate (Indexed.instantiate
      (mpTemplate input.axioms premise.axioms input.sequent.hyp premise.sequent.hyp)
      (mpFields input premise left right pairLeftSource pairRightSource origin)) = some block := by
  rw [mpTemplate_exact input premise left right leftBool rightBool leftEmpty rightEmpty leftNamed
    pairLeftSource pairRightSource pairLeftNamed pairRightNamed origin policy shape matching block computed,
    decodeCertificate_encodeCertificate]

end Emission

end Mettapedia.Languages.HOLLight.ImplicationExpansion

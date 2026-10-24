import Mettapedia.Languages.HOLLight.HypothesisExpansion
import Mettapedia.Languages.HOLLight.ImplicationExpansion

/-!
# Constructive conjunction introduction in HOL Light

The Boolean conjunction definition is proved by applying a fresh selector to
two truth equalities, abstracting that selector, and converting the result by
the original BETA/INST rules. All hypotheses and axiom dependencies of both
inputs are retained. The selector is explicitly fresh in the inputs; its
choice is independent of the two proof roots.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConjunctionExpansion

open Mettapedia.Languages.OpenTheory
open GraphExpansion EqualityExpansion HypothesisExpansion ImplicationExpansion PrimitiveTransport
open ProofExecution (Origin)
open ExcludedMiddle (boolBinaryTy)

def conjunctionResult (left right : Theorem)
    (leftBool : left.sequent.concl.IsBool) (rightBool : right.sequent.concl.IsBool) : Theorem :=
  Theorem.unionResult left right (left.sequent.hyp ∪ right.sequent.hyp)
    (conjunction left.sequent.concl right.sequent.concl leftBool rightBool)

structure ConjExpansion (policy : AxiomPolicy) [DecidablePred policy] (left right : Theorem) where
  requests : List BlockRequest
  conclusion : Theorem
  checked : LocallyChecked policy #[left, right] requests

/-- A fresh selector creates the actual equality of Boolean eliminators. -/
def conjExpansion (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Theorem) (leftBool : left.sequent.concl.IsBool) (rightBool : right.sequent.concl.IsBool)
    (name : Name) (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ (left.sequent.hyp ∪ right.sequent.hyp))
    (absentLeft : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ left.sequent.concl.term)
    (absentRight : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ right.sequent.concl.term)
    (origin : Origin) : ConjExpansion policy left right := by
  let binder : SourceVar := ⟨name, boolBinaryTy⟩
  let selector := CanonicalTerm.free binder
  let p := left.sequent.concl
  let q := right.sequent.concl
  have pType : p.ty = Ty.bool := leftBool
  have qType : q.ty = Ty.bool := rightBool
  let pTruth := truthEqualityResult left leftBool
  let qTruth := truthEqualityResult right rightBool
  let selectP := CanonicalTerm.applicationOfFunction selector p (.function Ty.bool Ty.bool)
    (by simp [selector, binder, CanonicalTerm.free, boolBinaryTy, pType])
  let selectTruth := CanonicalTerm.applicationOfFunction selector DerivedRules.truthTerm
    (.function Ty.bool Ty.bool)
    (by simp [selector, binder, CanonicalTerm.free, boolBinaryTy, DerivedRules.truthTerm])
  let first := appResult (reflexivity selector) pTruth selectP selectTruth rfl
  have firstChecked : checkApp (reflexivity selector) pTruth = some first := by
    apply appResult_checked _ _ selector selector p DerivedRules.truthTerm selectP selectTruth rfl
    · exact equality_view selector selector rfl
    · exact equality_view p DerivedRules.truthTerm leftBool
    · exact ⟨Ty.bool, .function Ty.bool Ty.bool,
        by simp [selector, binder, CanonicalTerm.free, boolBinaryTy], leftBool.symm, rfl⟩
    · exact ⟨Ty.bool, .function Ty.bool Ty.bool,
        by simp [selector, binder, CanonicalTerm.free, boolBinaryTy], rfl, rfl⟩
  let selectPQ := CanonicalTerm.applicationOfFunction selectP q Ty.bool
    (by simp [selectP, CanonicalTerm.applicationOfFunction, qType])
  let selectTT := CanonicalTerm.applicationOfFunction selectTruth DerivedRules.truthTerm Ty.bool
    (by simp [selectTruth, CanonicalTerm.applicationOfFunction, DerivedRules.truthTerm])
  let second := appResult first qTruth selectPQ selectTT rfl
  have secondChecked : checkApp first qTruth = some second := by
    apply appResult_checked _ _ selectP selectTruth q DerivedRules.truthTerm selectPQ selectTT rfl
    · exact equality_view selectP selectTruth rfl
    · exact equality_view q DerivedRules.truthTerm rightBool
    · exact ⟨Ty.bool, Ty.bool,
        by simp [selectP, CanonicalTerm.applicationOfFunction], rightBool.symm, rfl⟩
    · exact ⟨Ty.bool, Ty.bool,
        by simp [selectTruth, CanonicalTerm.applicationOfFunction], rfl, rfl⟩
  let abstracted := abstractionResult binder second selectPQ selectTT rfl
  have absent : ¬ FreeInHypotheses binder second.sequent.hyp := by
    simpa [second, first, appResult, reflexivity, pTruth, qTruth, truthEqualityResult,
      Theorem.unionResult, Theorem.emptyResult, Theorem.preserveAxiomsResult] using fresh
  let pairPQ := pairTerm p q leftBool rightBool
  let pairTT := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let pairEquation := CanonicalTerm.equalityOfSameType pairPQ pairTT rfl
  have abstractedConclusion : abstracted.sequent.concl = pairEquation := by
    apply CanonicalTerm.ext_term
    simp [abstracted, abstractionResult, pairEquation, pairPQ, pairTT, pairTerm,
      selectPQ, selectTT, selectP, selectTruth, CanonicalTerm.applicationOfFunction,
      CanonicalTerm.equalityOfSameType, CanonicalTerm.abstractFree, selector,
      CanonicalTerm.free, Theorem.preserveAxiomsResult, binder, DBTerm.closeFreeAt,
      DBTerm.closeFreeAt_of_not_freeOccurrence absentLeft,
      DBTerm.closeFreeAt_of_not_freeOccurrence absentRight, p, q,
      DerivedRules.truthTerm, DerivedRules.closeFreeAt_truthDB]
  let conversion := conjunctionBeta p q leftBool rightBool
  let resultTerm := conjunction p q leftBool rightBool
  let reversed := symmetryResult conversion.conclusion resultTerm pairEquation rfl
  let result := eqMpResult reversed abstracted resultTerm
  have resultChecked : checkEqMp reversed abstracted = some result :=
    eqMpResult_checked _ _ pairEquation resultTerm
      (equality_view pairEquation resultTerm rfl) abstractedConclusion.symm
  let requests : List BlockRequest :=
    [⟨reflexivity selector, primitiveBlock (.inference (.refl selector)) (reflexivity selector) origin, [], origin⟩,
     ⟨pTruth, truthEqualityBlock left leftBool origin, [0], origin⟩,
     ⟨qTruth, truthEqualityBlock right rightBool origin, [1], origin⟩,
     ⟨first, primitiveBlock (.inference (.mkComb (reflexivity selector) pTruth)) first origin, [2, 3], origin⟩,
     ⟨second, primitiveBlock (.inference (.mkComb first qTruth)) second origin, [5, 4], origin⟩,
     ⟨abstracted, abstractionBlock binder second selectPQ selectTT rfl origin, [6], origin⟩,
     ⟨conversion.conclusion, doubleBetaBlock conversion origin, [], origin⟩,
     ⟨reversed, symmetryBlock conversion.conclusion resultTerm pairEquation rfl origin, [8], origin⟩,
     ⟨result, primitiveBlock (.inference (.eqMp reversed abstracted)) result origin, [9, 7], origin⟩]
  refine ⟨requests, result, ?_⟩
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl selector)) _ origin (reflexivity_checked selector)
  apply LocallyChecked.cons (premises := [left]) rfl
  · exact truthEqualityBlock_checked policy left leftBool origin
  apply LocallyChecked.cons (premises := [right]) rfl
  · exact truthEqualityBlock_checked policy right rightBool origin
  apply LocallyChecked.cons (premises := [reflexivity selector, pTruth]) rfl
  · exact primitiveBlock_checked (.inference (.mkComb (reflexivity selector) pTruth)) first origin firstChecked
  apply LocallyChecked.cons (premises := [first, qTruth]) rfl
  · exact primitiveBlock_checked (.inference (.mkComb first qTruth)) second origin secondChecked
  apply LocallyChecked.cons (premises := [second]) rfl
  · exact abstractionBlock_checked policy binder second selectPQ selectTT rfl
      (equality_view selectPQ selectTT rfl) absent origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy conversion origin
  apply LocallyChecked.cons (premises := [conversion.conclusion]) rfl
  · exact symmetryBlock_checked policy conversion.conclusion resultTerm pairEquation rfl
      (conjunctionBeta_view p q leftBool rightBool) origin
  apply LocallyChecked.cons (premises := [reversed, abstracted]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp reversed abstracted)) result origin resultChecked
  exact .nil _

theorem conjExpansion_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Theorem) (leftBool : left.sequent.concl.IsBool) (rightBool : right.sequent.concl.IsBool)
    (name : Name) (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ (left.sequent.hyp ∪ right.sequent.hyp))
    (absentLeft : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ left.sequent.concl.term)
    (absentRight : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ right.sequent.concl.term)
    (origin : Origin) :
    (conjExpansion policy left right leftBool rightBool name fresh absentLeft absentRight origin).conclusion =
      conjunctionResult left right leftBool rightBool := by
  apply Theorem.ext
  · simp [conjExpansion, conjunctionResult, eqMpResult, symmetryResult, abstractionResult,
      appResult, transResult, reflexivity, truthEqualityResult, conjunctionBeta, doubleBetaExpansion,
      betaExpansion, substituteTheorem, Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult]
  · apply Sequent.ext
    · simp [conjExpansion, conjunctionResult, eqMpResult, symmetryResult, abstractionResult,
        appResult, transResult, reflexivity, truthEqualityResult, conjunctionBeta, doubleBetaExpansion,
        betaExpansion, substituteTheorem, TypeCorrectTermSubstitution.applyHypotheses,
        Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult]
    · rfl

def conjTypedBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Theorem) (leftBool : left.sequent.concl.IsBool) (rightBool : right.sequent.concl.IsBool)
    (name : Name) (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ (left.sequent.hyp ∪ right.sequent.hyp))
    (absentLeft : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ left.sequent.concl.term)
    (absentRight : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ right.sequent.concl.term)
    (origin : Origin) : Option ProofSystem.Certificate :=
  finishPlan policy (start [left, right]) #[0, 1]
    (conjExpansion policy left right leftBool rightBool name fresh absentLeft absentRight origin).requests 10

theorem conjTypedBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Theorem) (leftBool : left.sequent.concl.IsBool) (rightBool : right.sequent.concl.IsBool)
    (name : Name) (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ (left.sequent.hyp ∪ right.sequent.hyp))
    (absentLeft : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ left.sequent.concl.term)
    (absentRight : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ right.sequent.concl.term)
    (origin : Origin) :
    ∃ block, conjTypedBlock? policy left right leftBool rightBool name fresh absentLeft absentRight origin = some block ∧
      BlockChecked policy [left, right] (conjunctionResult left right leftBool rightBool) block := by
  let expansion := conjExpansion policy left right leftBool rightBool name fresh absentLeft absentRight origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[left, right]) (roots := #[0, 1]) (start_checked policy [left, right]) rfl
    expansion.checked (index := 10) (conclusion := expansion.conclusion) (by rfl)
  refine ⟨block, computed, ?_⟩
  simpa only [expansion, conjExpansion_conclusion] using checked


/-! ## Left projection -/

def firstSelector : CanonicalTerm :=
  ⟨DerivedRules.selectFirstDB, boolBinaryTy, DerivedRules.inferType_selectFirstDB⟩

def selectedFirstPair (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    CanonicalTerm :=
  CanonicalTerm.applicationOfFunction (pairTerm left right leftBool rightBool) firstSelector Ty.bool
    (by simp [pairTerm, firstSelector])

def firstSelectorApplication (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    CanonicalTerm :=
  ⟨.app (.app DerivedRules.selectFirstDB left.term) right.term, Ty.bool,
    (DerivedRules.inferType_binary_iff DerivedRules.inferType_selectFirstDB).mpr
      ⟨leftBool ▸ left.checked, rightBool ▸ right.checked, rfl⟩⟩

def firstSelectorBeta (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    DoubleBetaExpansion :=
  doubleBetaExpansion Ty.bool Ty.bool Ty.bool (.bound 1) (by simp) left right leftBool rightBool

def firstPairBeta (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    BetaExpansion :=
  betaExpansion boolBinaryTy (.app (.app (.bound 0) left.term) right.term) Ty.bool
    (DBTerm.inferType_app_of (DBTerm.inferType_app_of (by simp [boolBinaryTy])
      (DBTerm.inferType_weaken_empty (leftBool ▸ left.checked) _))
      (DBTerm.inferType_weaken_empty (rightBool ▸ right.checked) _)) firstSelector
      (show firstSelector.ty = boolBinaryTy from rfl)

theorem firstSelectorBeta_view (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    CanonicalTerm.EqualityViewSemantics (firstSelectorBeta left right leftBool rightBool).conclusion.sequent.concl
      (firstSelectorApplication left right leftBool rightBool) left := by
  refine ⟨leftBool.symm, ?_⟩
  have shape := (doubleBetaExpansion_parts Ty.bool Ty.bool Ty.bool (.bound 1) (by simp)
    left right leftBool rightBool).2.2
  change (firstSelectorBeta left right leftBool rightBool).conclusion.sequent.concl.term = _
  simp only [firstSelectorBeta]
  rw [shape]
  simp [firstSelectorApplication, DerivedRules.selectFirstDB,
    DBTerm.instantiateAt_closed (leftBool ▸ left.checked)]

theorem firstPairBeta_view (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool) :
    CanonicalTerm.EqualityViewSemantics (firstPairBeta left right leftBool rightBool).conclusion.sequent.concl
      (selectedFirstPair left right leftBool rightBool) (firstSelectorApplication left right leftBool rightBool) := by
  unfold firstPairBeta
  rw [betaExpansion_conclusion]
  refine ⟨rfl, ?_⟩
  simp [Theorem.emptyResult, betaRedex, betaReduced, selectedFirstPair, pairTerm, firstSelector,
    firstSelectorApplication, CanonicalTerm.applicationOfFunction, CanonicalTerm.equalityOfSameType,
    DBTerm.instantiateAt, DBTerm.instantiateAt_closed (leftBool ▸ left.checked),
    DBTerm.instantiateAt_closed (rightBool ▸ right.checked)]

structure ProjectionExpansion (policy : AxiomPolicy) [DecidablePred policy] (input : Theorem) where
  requests : List BlockRequest
  conclusion : Theorem
  checked : LocallyChecked policy #[input] requests

def conjunct1Result (input : Theorem) (left : CanonicalTerm) : Theorem :=
  Theorem.preserveAxiomsResult input input.sequent.hyp left

set_option maxHeartbeats 3000000 in
def conjunct1Expansion (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool)
    (shape : input.sequent.concl = conjunction left right leftBool rightBool)
    (origin : Origin) : ProjectionExpansion policy input := by
  let conversion := conjunctionBeta left right leftBool rightBool
  let pairLeft := pairTerm left right leftBool rightBool
  let pairTruth := pairTerm DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let equation := CanonicalTerm.equalityOfSameType pairLeft pairTruth rfl
  let equationProof := eqMpResult conversion.conclusion input equation
  have equationChecked : checkEqMp conversion.conclusion input = some equationProof :=
    eqMpResult_checked _ _ _ _ (conjunctionBeta_view left right leftBool rightBool) shape.symm
  let selected := selectedFirstPair left right leftBool rightBool
  let selectedTruth := selectedFirstPair DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let application := appResult equationProof (reflexivity firstSelector) selected selectedTruth rfl
  have applicationChecked : checkApp equationProof (reflexivity firstSelector) = some application := by
    apply appResult_checked _ _ pairLeft pairTruth firstSelector firstSelector selected selectedTruth rfl
    · exact equality_view pairLeft pairTruth rfl
    · exact equality_view firstSelector firstSelector rfl
    · exact ⟨boolBinaryTy, Ty.bool, by simp [pairLeft, pairTerm], rfl, rfl⟩
    · exact ⟨boolBinaryTy, Ty.bool, by simp [pairTruth, pairTerm], rfl, rfl⟩
  let leftPair := firstPairBeta left right leftBool rightBool
  let leftSelector := firstSelectorBeta left right leftBool rightBool
  let selectedArguments := firstSelectorApplication left right leftBool rightBool
  let leftReduction := transResult leftPair.conclusion leftSelector.conclusion selected left leftBool.symm
  have leftChecked : checkTrans leftPair.conclusion leftSelector.conclusion = some leftReduction :=
    transResult_checked _ _ selected selectedArguments left leftBool.symm
      (firstPairBeta_view left right leftBool rightBool) (firstSelectorBeta_view left right leftBool rightBool)
  let leftReversed := symmetryResult leftReduction selected left leftBool.symm
  let truthPair := firstPairBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthSelector := firstSelectorBeta DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthArguments := firstSelectorApplication DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl
  let truthReduction := transResult truthPair.conclusion truthSelector.conclusion selectedTruth DerivedRules.truthTerm rfl
  have truthChecked : checkTrans truthPair.conclusion truthSelector.conclusion = some truthReduction :=
    transResult_checked _ _ selectedTruth truthArguments DerivedRules.truthTerm rfl
      (firstPairBeta_view DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl)
      (firstSelectorBeta_view DerivedRules.truthTerm DerivedRules.truthTerm rfl rfl)
  let joinedLeft := transResult leftReversed application left selectedTruth leftBool
  have joinedLeftChecked : checkTrans leftReversed application = some joinedLeft :=
    transResult_checked _ _ left selected selectedTruth leftBool
      (equality_view left selected leftBool) (equality_view selected selectedTruth rfl)
  let joined := transResult joinedLeft truthReduction left DerivedRules.truthTerm leftBool
  have joinedChecked : checkTrans joinedLeft truthReduction = some joined :=
    transResult_checked _ _ left selectedTruth DerivedRules.truthTerm leftBool
      (equality_view left selectedTruth leftBool) (equality_view selectedTruth DerivedRules.truthTerm rfl)
  let reversed := symmetryResult joined left DerivedRules.truthTerm leftBool
  let result := eqMpResult reversed truthTheorem left
  have resultChecked : checkEqMp reversed truthTheorem = some result :=
    eqMpResult_checked _ _ DerivedRules.truthTerm left
      (equality_view DerivedRules.truthTerm left leftBool.symm) rfl
  let requests : List BlockRequest :=
    [⟨conversion.conclusion, doubleBetaBlock conversion origin, [], origin⟩,
     ⟨equationProof, primitiveBlock (.inference (.eqMp conversion.conclusion input)) equationProof origin, [1, 0], origin⟩,
     ⟨reflexivity firstSelector, primitiveBlock (.inference (.refl firstSelector)) (reflexivity firstSelector) origin, [], origin⟩,
     ⟨application, primitiveBlock (.inference (.mkComb equationProof (reflexivity firstSelector))) application origin, [2, 3], origin⟩,
     ⟨leftPair.conclusion, betaBlock leftPair origin, [], origin⟩,
     ⟨leftSelector.conclusion, doubleBetaBlock leftSelector origin, [], origin⟩,
     ⟨leftReduction, primitiveBlock (.inference (.trans leftPair.conclusion leftSelector.conclusion)) leftReduction origin, [5, 6], origin⟩,
     ⟨leftReversed, symmetryBlock leftReduction selected left leftBool.symm origin, [7], origin⟩,
     ⟨truthPair.conclusion, betaBlock truthPair origin, [], origin⟩,
     ⟨truthSelector.conclusion, doubleBetaBlock truthSelector origin, [], origin⟩,
     ⟨truthReduction, primitiveBlock (.inference (.trans truthPair.conclusion truthSelector.conclusion)) truthReduction origin, [9, 10], origin⟩,
     ⟨joinedLeft, primitiveBlock (.inference (.trans leftReversed application)) joinedLeft origin, [8, 4], origin⟩,
     ⟨joined, primitiveBlock (.inference (.trans joinedLeft truthReduction)) joined origin, [12, 11], origin⟩,
     ⟨reversed, symmetryBlock joined left DerivedRules.truthTerm leftBool origin, [13], origin⟩,
     ⟨truthTheorem, primitiveBlock (.inference (.refl booleanIdentity)) truthTheorem origin, [], origin⟩,
     ⟨result, primitiveBlock (.inference (.eqMp reversed truthTheorem)) result origin, [14, 15], origin⟩]
  refine ⟨requests, result, ?_⟩
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy conversion origin
  apply LocallyChecked.cons (premises := [conversion.conclusion, input]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp conversion.conclusion input)) _ origin equationChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl firstSelector)) _ origin (reflexivity_checked firstSelector)
  apply LocallyChecked.cons (premises := [equationProof, reflexivity firstSelector]) rfl
  · exact primitiveBlock_checked (.inference (.mkComb equationProof (reflexivity firstSelector))) _ origin applicationChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy leftPair origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy leftSelector origin
  apply LocallyChecked.cons (premises := [leftPair.conclusion, leftSelector.conclusion]) rfl
  · exact primitiveBlock_checked (.inference (.trans leftPair.conclusion leftSelector.conclusion)) _ origin leftChecked
  apply LocallyChecked.cons (premises := [leftReduction]) rfl
  · exact symmetryBlock_checked policy _ selected left leftBool.symm
      (equality_view selected left leftBool.symm) origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact betaBlock_checked policy truthPair origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy truthSelector origin
  apply LocallyChecked.cons (premises := [truthPair.conclusion, truthSelector.conclusion]) rfl
  · exact primitiveBlock_checked (.inference (.trans truthPair.conclusion truthSelector.conclusion)) _ origin truthChecked
  apply LocallyChecked.cons (premises := [leftReversed, application]) rfl
  · exact primitiveBlock_checked (.inference (.trans leftReversed application)) _ origin joinedLeftChecked
  apply LocallyChecked.cons (premises := [joinedLeft, truthReduction]) rfl
  · exact primitiveBlock_checked (.inference (.trans joinedLeft truthReduction)) _ origin joinedChecked
  apply LocallyChecked.cons (premises := [joined]) rfl
  · exact symmetryBlock_checked policy _ left DerivedRules.truthTerm leftBool
      (equality_view left DerivedRules.truthTerm leftBool) origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact primitiveBlock_checked (.inference (.refl booleanIdentity)) _ origin truthTheorem_checked
  apply LocallyChecked.cons (premises := [reversed, truthTheorem]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp reversed truthTheorem)) _ origin resultChecked
  exact .nil _

set_option maxHeartbeats 3000000 in
theorem conjunct1Expansion_conclusion (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool)
    (shape : input.sequent.concl = conjunction left right leftBool rightBool) (origin : Origin) :
    (conjunct1Expansion policy input left right leftBool rightBool shape origin).conclusion =
      conjunct1Result input left := by
  apply Theorem.ext
  · simp [conjunct1Expansion, conjunct1Result, eqMpResult, symmetryResult, transResult, appResult,
      reflexivity, truthTheorem, conjunctionBeta, doubleBetaExpansion, firstPairBeta, firstSelectorBeta,
      betaExpansion, substituteTheorem, Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult]
  · apply Sequent.ext
    · simp [conjunct1Expansion, conjunct1Result, eqMpResult, symmetryResult, transResult, appResult,
        reflexivity, truthTheorem, conjunctionBeta, doubleBetaExpansion, firstPairBeta, firstSelectorBeta,
        betaExpansion, substituteTheorem, TypeCorrectTermSubstitution.applyHypotheses,
        Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult]
    · rfl

def conjunct1TypedBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool)
    (shape : input.sequent.concl = conjunction left right leftBool rightBool) (origin : Origin) :
    Option ProofSystem.Certificate :=
  finishPlan policy (start [input]) #[0]
    (conjunct1Expansion policy input left right leftBool rightBool shape origin).requests 16

theorem conjunct1TypedBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (left right : CanonicalTerm) (leftBool : left.IsBool) (rightBool : right.IsBool)
    (shape : input.sequent.concl = conjunction left right leftBool rightBool) (origin : Origin) :
    ∃ block, conjunct1TypedBlock? policy input left right leftBool rightBool shape origin = some block ∧
      BlockChecked policy [input] (conjunct1Result input left) block := by
  let expansion := conjunct1Expansion policy input left right leftBool rightBool shape origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[input]) (roots := #[0]) (start_checked policy [input]) rfl
    expansion.checked (index := 16) (conclusion := expansion.conclusion) (by rfl)
  refine ⟨block, computed, ?_⟩
  simpa only [expansion, conjunct1Expansion_conclusion] using checked

end Mettapedia.Languages.HOLLight.ConjunctionExpansion

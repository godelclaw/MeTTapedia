import Mettapedia.Languages.HOLLight.ConjunctionExpansion

/-!
# Constructive discharge in HOL Light

DISCH constructs conjunction introduction, conjunction elimination and
DEDUCT_ANTISYM, then uses the original beta expansion of implication. The
exporter erases exactly the discharged proposition from the hypothesis set;
it retains the complete input axiom set. No derived inference is added to
the checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ImplicationIntroduction

open Mettapedia.Languages.OpenTheory
open GraphExpansion EqualityExpansion HypothesisExpansion ImplicationExpansion ConjunctionExpansion
open ProofExecution (Origin)
open ExcludedMiddle (boolBinaryTy)

def dischResult (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool) : Theorem :=
  Theorem.preserveAxiomsResult input (input.sequent.hyp.erase premise)
    (implication premise input.sequent.concl premiseBool inputBool)

/-- The eight local blocks have one external input and two explicitly shared
assumption nodes. -/
def dischPlan (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (conjBlock projectionBlock : ProofSystem.Certificate) (origin : Origin) :
    List BlockRequest × Theorem := by
  let assumed := assumption premise
  let conjunction := conjunctionResult assumed input premiseBool inputBool
  let assumedConjunction := assumption conjunction.sequent.concl
  let projected := conjunct1Result assumedConjunction premise
  let equation := deductionResult conjunction projected premiseBool.symm
  let conversion := implicationBeta premise input.sequent.concl premiseBool inputBool
  let resultTerm := implication premise input.sequent.concl premiseBool inputBool
  let equationTerm := CanonicalTerm.equalityOfSameType conjunction.sequent.concl premise premiseBool.symm
  let reversed := symmetryResult conversion.conclusion resultTerm equationTerm rfl
  let result := eqMpResult reversed equation resultTerm
  exact ([⟨assumed, assumptionBlock premise origin, [], origin⟩,
    ⟨conjunction, conjBlock, [1, 0], origin⟩,
    ⟨assumedConjunction, assumptionBlock conjunction.sequent.concl origin, [], origin⟩,
    ⟨projected, projectionBlock, [3], origin⟩,
    ⟨equation, deductionBlock conjunction projected premiseBool.symm origin, [2, 4], origin⟩,
    ⟨conversion.conclusion, doubleBetaBlock conversion origin, [], origin⟩,
    ⟨reversed, symmetryBlock conversion.conclusion resultTerm equationTerm rfl origin, [6], origin⟩,
    ⟨result, primitiveBlock (.inference (.eqMp reversed equation)) result origin, [7, 5], origin⟩], result)

theorem dischPlan_checked (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (conjBlock projectionBlock : ProofSystem.Certificate) (origin : Origin)
    (conjChecked : BlockChecked policy [assumption premise, input]
      (conjunctionResult (assumption premise) input premiseBool inputBool) conjBlock)
    (projectionChecked : BlockChecked policy
      [assumption (conjunction premise input.sequent.concl premiseBool inputBool)]
      (conjunct1Result (assumption (conjunction premise input.sequent.concl premiseBool inputBool)) premise)
      projectionBlock) :
    LocallyChecked policy #[input] (dischPlan premise input premiseBool inputBool conjBlock projectionBlock origin).1 := by
  let joinedConjunction := conjunctionResult (assumption premise) input premiseBool inputBool
  let projected := conjunct1Result (assumption joinedConjunction.sequent.concl) premise
  let equation := deductionResult joinedConjunction projected premiseBool.symm
  let conversion := implicationBeta premise input.sequent.concl premiseBool inputBool
  let resultTerm := implication premise input.sequent.concl premiseBool inputBool
  let equationTerm := CanonicalTerm.equalityOfSameType joinedConjunction.sequent.concl premise premiseBool.symm
  let reversed := symmetryResult conversion.conclusion resultTerm equationTerm rfl
  let result := eqMpResult reversed equation resultTerm
  apply LocallyChecked.cons (premises := []) rfl
  · exact assumptionBlock_checked policy premise premiseBool origin
  apply LocallyChecked.cons (premises := [assumption premise, input]) rfl
  · exact conjChecked
  apply LocallyChecked.cons (premises := []) rfl
  · exact assumptionBlock_checked policy joinedConjunction.sequent.concl rfl origin
  apply LocallyChecked.cons (premises := [assumption (conjunction premise input.sequent.concl premiseBool inputBool)]) rfl
  · exact projectionChecked
  apply LocallyChecked.cons (premises := [conjunctionResult (assumption premise) input premiseBool inputBool,
    conjunct1Result (assumption (conjunction premise input.sequent.concl premiseBool inputBool)) premise]) rfl
  · exact deductionBlock_checked policy _ _ premiseBool.symm origin
  apply LocallyChecked.cons (premises := []) rfl
  · exact doubleBetaBlock_checked policy _ origin
  apply LocallyChecked.cons (premises := [(implicationBeta premise input.sequent.concl premiseBool inputBool).conclusion]) rfl
  · exact symmetryBlock_checked policy conversion.conclusion resultTerm equationTerm rfl
      (implicationBeta_view premise input.sequent.concl premiseBool inputBool) origin
  apply LocallyChecked.cons (premises := [reversed, equation]) rfl
  · exact primitiveBlock_checked (.inference (.eqMp reversed equation)) result origin
      (eqMpResult_checked reversed equation equationTerm resultTerm
        (equality_view equationTerm resultTerm rfl) rfl)
  exact .nil _

theorem dischPlan_conclusion (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (conjBlock projectionBlock : ProofSystem.Certificate) (origin : Origin) :
    (dischPlan premise input premiseBool inputBool conjBlock projectionBlock origin).2 =
      dischResult premise input premiseBool inputBool := by
  apply Theorem.ext
  · simp [dischPlan, dischResult, eqMpResult, symmetryResult, deductionResult, conjunctionResult,
      conjunct1Result, assumption, implicationBeta, doubleBetaExpansion, appResult, transResult, reflexivity,
      PrimitiveTransport.betaExpansion, substituteTheorem, Theorem.preserveAxiomsResult,
      Theorem.unionResult, Theorem.emptyResult]
  · apply Sequent.ext
    · simp [dischPlan, dischResult, eqMpResult, symmetryResult, deductionResult, conjunctionResult,
        conjunct1Result, assumption, implicationBeta, doubleBetaExpansion, appResult, transResult, reflexivity,
        PrimitiveTransport.betaExpansion, substituteTheorem, TypeCorrectTermSubstitution.applyHypotheses,
        Theorem.preserveAxiomsResult, Theorem.unionResult, Theorem.emptyResult]
    · rfl

def dischBlock? (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (name : Name)
    (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ ({premise} ∪ input.sequent.hyp))
    (absentPremise : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ premise.term)
    (absentConclusion : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ input.sequent.concl.term)
    (origin : Origin) : Option ProofSystem.Certificate := do
  let conjBlock ← conjTypedBlock? policy (assumption premise) input premiseBool inputBool name
    fresh absentPremise absentConclusion origin
  let projectionBlock ← conjunct1TypedBlock? policy
    (assumption (conjunction premise input.sequent.concl premiseBool inputBool))
    premise input.sequent.concl premiseBool inputBool rfl origin
  finishPlan policy (start [input]) #[0]
    (dischPlan premise input premiseBool inputBool conjBlock projectionBlock origin).1 8

theorem dischBlock?_checked (policy : AxiomPolicy) [DecidablePred policy]
    (premise : CanonicalTerm) (input : Theorem)
    (premiseBool : premise.IsBool) (inputBool : input.sequent.concl.IsBool)
    (name : Name)
    (fresh : ¬ FreeInHypotheses ⟨name, boolBinaryTy⟩ ({premise} ∪ input.sequent.hyp))
    (absentPremise : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ premise.term)
    (absentConclusion : ¬ DBTerm.FreeOccurrence ⟨name, boolBinaryTy⟩ input.sequent.concl.term)
    (origin : Origin) :
    ∃ block, dischBlock? policy premise input premiseBool inputBool name
      fresh absentPremise absentConclusion origin = some block ∧
      BlockChecked policy [input] (dischResult premise input premiseBool inputBool) block := by
  obtain ⟨conjBlock, computedConj, checkedConj⟩ := conjTypedBlock?_checked policy
    (assumption premise) input premiseBool inputBool name fresh absentPremise absentConclusion origin
  obtain ⟨projectionBlock, computedProjection, checkedProjection⟩ := conjunct1TypedBlock?_checked policy
    (assumption (conjunction premise input.sequent.concl premiseBool inputBool))
    premise input.sequent.concl premiseBool inputBool rfl origin
  obtain ⟨block, computed, checked⟩ := finishPlan_checked (policy := policy)
    (outputs := #[input]) (roots := #[0]) (start_checked policy [input]) rfl
    (dischPlan_checked policy premise input premiseBool inputBool conjBlock projectionBlock origin
      checkedConj checkedProjection) (index := 8)
    (conclusion := (dischPlan premise input premiseBool inputBool conjBlock projectionBlock origin).2) (by rfl)
  refine ⟨block, ?_, ?_⟩
  · simpa [dischBlock?, computedConj, computedProjection] using computed
  · simpa only [dischPlan_conclusion] using checked

end Mettapedia.Languages.HOLLight.ImplicationIntroduction

import Mettapedia.Languages.MM0.HOLKernelTermTyping
import Mettapedia.Languages.MM0.HOLKernelTermCongruence

/-!
# Checked alpha-renaming across finite native binder windows

The construction compares actual encodings of every intrinsic HOL term under
two disjoint finite binder windows. It uses the maintained change-of-variable
rule, constructs both body-typing premises, and joins pointwise assignment
congruence to the recursive binder comparison. Complete occurrence support and
all native bound images remain explicit. No alpha equation is an input premise. Overlapping source and target windows
are compared through a third fresh window by the constructed rebind proof.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelAlpha
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelTypeSupport
open HOLKernelTermTyping (weakenVariables weakenConstants)
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

private theorem equalityContext_independent (index first second : Nat) (sort : Nat)
    (references : Symbol → Nat) (antecedent domain : Preterm)
    (firstBound : context[first]? = some (.bound sort))
    (secondBound : context[second]? = some (.bound sort))
    (differentFirst : index ≠ first) (differentSecond : index ≠ second)
    (antecedentIndependent : ¬ Preterm.HasVar context index antecedent)
    (domainIndependent : ¬ Preterm.HasVar context index domain) :
    ¬ Preterm.HasVar context index (conjunction references antecedent
      (holds references (equality references domain (.var first) (.var second)))) := by
  exact substitutionContext_independent context index first references antecedent domain (.var second)
    antecedentIndependent domainIndependent
    (boundVariable_independent context index first sort firstBound differentFirst)
    (boundVariable_independent context index second sort secondBound differentSecond)

def alphaDisjoint (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (leftBinders rightBinders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (leftInjective : Function.Injective leftBinders) (rightInjective : Function.Injective rightBinders)
    (baseIndependentLeft : ∀ slot index, ¬ Preterm.HasVar context (leftBinders slot) (base index))
    (baseIndependentRight : ∀ slot index, ¬ Preterm.HasVar context (rightBinders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (leftDepth rightDepth : Nat) (antecedent : Preterm),
      Preterm.HasType terms context antecedent [] signature.ids.wff →
      (∀ {type} (index : Var gamma type),
        Preterm.HasType terms context (assignment index) [] signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[leftBinders (leftDepth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth,
        context[rightBinders (rightDepth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth,
        ¬ Preterm.HasVar context (leftBinders (leftDepth + offset)) antecedent) →
      (∀ offset < source.binderDepth,
        ¬ Preterm.HasVar context (rightBinders (rightDepth + offset)) antecedent) →
      (∀ leftOffset < source.binderDepth, ∀ rightOffset < source.binderDepth,
        leftBinders (leftDepth + leftOffset) ≠ rightBinders (rightDepth + rightOffset)) →
      (∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type))) →
      (∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base type)
            (encodeWithAssignment signature.symbol base constant leftBinders assignment leftDepth source)
            (encodeWithAssignment signature.symbol base constant rightBinders assignment rightDepth source)))) := by
  match source with
  | .var index =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (assignmentSorted index) (variableTyping index)
  | .const symbol =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantTyping symbol)
  | .top =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .truth [] .nil)
        (HOLKernelTypingProofs.truthTyping signature typing antecedent antecedentSorted)
  | .bot =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .falsity [] .nil)
        (HOLKernelTypingProofs.falsityTyping signature typing antecedent antecedentSorted)
  | .app first second | .and first second | .or first second | .imp first second =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      have firstLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
      have rightFirstSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
      let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
        firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      have leftSecondSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
      have rightSecondSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
      let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
        secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      first
      | exact HOLKernelCongruence.application signature rules binding antecedent _ _ _ _ _ _
          antecedentSorted (encodeType_sorted signature context base baseSorted _)
          (encodeType_sorted signature context base baseSorted _) leftFirstSorted rightFirstSorted
          leftSecondSorted rightSecondSorted firstProof secondProof
      | exact HOLKernelCongruence.conjunctionCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof
      | exact HOLKernelCongruence.disjunctionCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof
      | exact HOLKernelCongruence.implicationCongruence signature profile rules binding antecedent _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof
  | .not body =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      exact HOLKernelCongruence.negationCongruence signature profile rules antecedent _ _ antecedentSorted
        (encode_sorted signature context base constant leftBinders baseSorted constantSorted body
          assignment leftDepth assignmentSorted leftSlots)
        (encode_sorted signature context base constant rightBinders baseSorted constantSorted body
          assignment rightDepth assignmentSorted rightSlots)
        (alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
          baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight body
          assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
          leftFresh rightFresh disjoint variableTyping constantTyping)
  | .eq (τ := type) first second =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      have firstLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
      have rightFirstSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
      let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
        firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      have leftSecondSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
      have rightSecondSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
      let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
        secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      exact HOLKernelCongruence.equalityCongruence signature profile rules binding antecedent
        (encodeType signature.symbol base type) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted type)
        leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof
  | .lam (σ := domain) body | .all (σ := domain) body | .ex (σ := domain) body =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots leftFresh rightFresh disjoint variableTyping constantTyping
      have leftHead : context[leftBinders leftDepth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using leftSlots 0 (Nat.zero_lt_succ _)
      have rightHead : context[rightBinders rightDepth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using rightSlots 0 (Nat.zero_lt_succ _)
      have leftBodySlots : ∀ offset < body.binderDepth,
          context[leftBinders (leftDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := leftSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have rightBodySlots : ∀ offset < body.binderDepth,
          context[rightBinders (rightDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := rightSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have leftHeadSorted : Preterm.HasType terms context (.var (leftBinders leftDepth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) leftHead
      have rightHeadSorted : Preterm.HasType terms context (.var (rightBinders rightDepth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) rightHead
      let leftExtra := hasType signature.symbol (.var (leftBinders leftDepth)) (encodeType signature.symbol base domain)
      let rightExtra := hasType signature.symbol (.var (rightBinders rightDepth)) (encodeType signature.symbol base domain)
      let equalityExtra := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
        (.var (leftBinders leftDepth)) (.var (rightBinders rightDepth)))
      let leftContext := conjunction signature.symbol antecedent leftExtra
      let rightContext := conjunction signature.symbol antecedent rightExtra
      let equalityContext := conjunction signature.symbol antecedent equalityExtra
      have leftExtraSorted := hasType_sorted signature context leftHeadSorted domainSorted
      have rightExtraSorted := hasType_sorted signature context rightHeadSorted domainSorted
      have equalityExtraSorted := holds_sorted signature context (signature.application context .eqc _
        (.cons (.regular domainSorted) (.cons (.regular leftHeadSorted) (.cons (.regular rightHeadSorted) .nil))))
      have leftContextSorted := conjunction_sorted signature context antecedentSorted leftExtraSorted
      have rightContextSorted := conjunction_sorted signature context antecedentSorted rightExtraSorted
      have equalityContextSorted := conjunction_sorted signature context antecedentSorted equalityExtraSorted
      have leftExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context _ assignment leftHeadSorted assignmentSorted
      have rightExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context _ assignment rightHeadSorted assignmentSorted
      have leftBodyFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (leftBinders (leftDepth + 1 + offset)) leftContext := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ leftHead
        · intro same
          have impossible := leftInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            leftFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentLeft _) domain
      have rightBodyFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (rightBinders (rightDepth + 1 + offset)) rightContext := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ rightHead
        · intro same
          have impossible := rightInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            rightFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentRight _) domain
      have equalityLeftFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (leftBinders (leftDepth + 1 + offset)) equalityContext := by
        intro offset smaller
        apply equalityContext_independent _ _ _ signature.ids.object signature.symbol _ _ leftHead rightHead
        · intro same
          have impossible := leftInjective same
          omega
        · have apart := disjoint (offset + 1) (Nat.add_lt_add_right smaller 1) 0 (Nat.zero_lt_succ _)
          simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            leftFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentLeft _) domain
      have equalityRightFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (rightBinders (rightDepth + 1 + offset)) equalityContext := by
        intro offset smaller
        apply equalityContext_independent _ _ _ signature.ids.object signature.symbol _ _ leftHead rightHead
        · have apart := Ne.symm (disjoint 0 (Nat.zero_lt_succ _) (offset + 1) (Nat.add_lt_add_right smaller 1))
          simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
        · intro same
          have impossible := rightInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            rightFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentRight _) domain
      have bodyDisjoint : ∀ leftOffset < body.binderDepth, ∀ rightOffset < body.binderDepth,
          leftBinders (leftDepth + 1 + leftOffset) ≠ rightBinders (rightDepth + 1 + rightOffset) := by
        intro leftOffset leftSmaller rightOffset rightSmaller
        have apart := disjoint (leftOffset + 1) (Nat.add_lt_add_right leftSmaller 1)
          (rightOffset + 1) (Nat.add_lt_add_right rightSmaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 leftOffset, Nat.add_comm 1 rightOffset] using apart
      let leftProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent leftExtra antecedentSorted leftExtraSorted
      let rightProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent rightExtra antecedentSorted rightExtraSorted
      let relation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent equalityExtra antecedentSorted equalityExtraSorted
      have leftVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol leftContext (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact leftProjection
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent leftExtra
              antecedentSorted leftExtraSorted baseSorted assignmentSorted variableTyping) index
      have rightVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol rightContext (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact rightProjection
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent rightExtra
              antecedentSorted rightExtraSorted baseSorted assignmentSorted variableTyping) index
      have leftConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol leftContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent leftExtra
          antecedentSorted leftExtraSorted baseSorted constantSorted constantTyping
      have rightConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol rightContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent rightExtra
          antecedentSorted rightExtraSorted baseSorted constantSorted constantTyping
      have equalityConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol equalityContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent equalityExtra
          antecedentSorted equalityExtraSorted baseSorted constantSorted constantTyping
      have bodyLeftTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant leftBinders
        baseSorted constantSorted leftInjective baseIndependentLeft body
        (Assignment.extend (.var (leftBinders leftDepth)) assignment) (leftDepth + 1) leftContext
        leftContextSorted leftExtendedSorted leftBodySlots leftBodyFresh leftVariables leftConstants
      have bodyRightTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant rightBinders
        baseSorted constantSorted rightInjective baseIndependentRight body
        (Assignment.extend (.var (rightBinders rightDepth)) assignment) (rightDepth + 1) rightContext
        rightContextSorted rightExtendedSorted rightBodySlots rightBodyFresh rightVariables rightConstants
      have related : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol equalityContext (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
                (Assignment.extend (.var (rightBinders rightDepth)) assignment index)))) := by
        intro type index
        cases index with
        | vz => exact relation
        | vs index =>
            apply HOLKernelStructuralRules.weaken signature structural antecedent equalityExtra _
              antecedentSorted equalityExtraSorted _
              (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
                (encodeType_sorted signature context base baseSorted type) (assignmentSorted index) (variableTyping index))
            exact holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (assignmentSorted index)) (.cons (.regular (assignmentSorted index)) .nil))))
      let rightHeadInEquality := HOLKernelBindingProofs.Native.equalityRightTyping signature binding
        (encodeType signature.symbol base domain) equalityContext (.var (leftBinders leftDepth))
        (.var (rightBinders rightDepth)) domainSorted equalityContextSorted leftHeadSorted rightHeadSorted relation
      have equalityVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol equalityContext
              (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact rightHeadInEquality
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent equalityExtra
              antecedentSorted equalityExtraSorted baseSorted assignmentSorted variableTyping) index
      let assignmentComparison := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
        base constant leftBinders baseSorted constantSorted leftInjective baseIndependentLeft body
        (Assignment.extend (.var (leftBinders leftDepth)) assignment)
        (Assignment.extend (.var (rightBinders rightDepth)) assignment) (leftDepth + 1) equalityContext
        equalityContextSorted leftExtendedSorted rightExtendedSorted leftBodySlots equalityLeftFresh related equalityConstants
      let binderComparison := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight body
        (Assignment.extend (.var (rightBinders rightDepth)) assignment)
        (leftDepth + 1) (rightDepth + 1) equalityContext equalityContextSorted rightExtendedSorted
        leftBodySlots rightBodySlots equalityLeftFresh equalityRightFresh bodyDisjoint equalityVariables equalityConstants
      have leftBodySorted := encode_sorted signature context base constant leftBinders baseSorted constantSorted
        body _ (leftDepth + 1) leftExtendedSorted leftBodySlots
      have middleBodySorted := encode_sorted signature context base constant leftBinders baseSorted constantSorted
        body _ (leftDepth + 1) rightExtendedSorted leftBodySlots
      have rightBodySorted := encode_sorted signature context base constant rightBinders baseSorted constantSorted
        body _ (rightDepth + 1) rightExtendedSorted rightBodySlots
      let bodyEquality := HOLKernelInferenceProofs.Native.transitivity signature rules equalityContext _ _ _ _
        equalityContextSorted (encodeType_sorted signature context base baseSorted _)
        leftBodySorted middleBodySorted rightBodySorted assignmentComparison binderComparison
      have abstractionEquality := HOLKernelBindingProofs.Native.abstractionRenaming signature binding
        (encodeType signature.symbol base domain) _ antecedent (leftBinders leftDepth) (rightBinders rightDepth)
        _ _ domainSorted (encodeType_sorted signature context base baseSorted _) antecedentSorted
        leftHead rightHead leftBodySorted rightBodySorted
        (encodeType_independent context _ signature.symbol base (baseIndependentLeft leftDepth) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependentLeft leftDepth) _)
        (by simpa only [Nat.add_zero] using leftFresh 0 (Nat.zero_lt_succ _))
        (encodeType_independent context _ signature.symbol base (baseIndependentRight rightDepth) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependentRight rightDepth) _)
        (by simpa only [Nat.add_zero] using rightFresh 0 (Nat.zero_lt_succ _))
        (by simpa only [Nat.add_zero] using disjoint 0 (Nat.zero_lt_succ _) 0 (Nat.zero_lt_succ _))
        bodyLeftTyping bodyRightTyping bodyEquality
      first
      | exact abstractionEquality
      | exact HOLKernelCongruence.universalCongruence signature profile rules antecedent _ _ _
          (leftBinders leftDepth) (rightBinders rightDepth) antecedentSorted domainSorted leftHead rightHead
          leftBodySorted rightBodySorted abstractionEquality
      | exact HOLKernelCongruence.existentialCongruence signature profile rules antecedent _ _ _
          (leftBinders leftDepth) (rightBinders rightDepth) antecedentSorted domainSorted leftHead rightHead
          leftBodySorted rightBodySorted abstractionEquality
termination_by structural source

def rebind (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (assignment : Assignment gamma) (sourceDepth targetDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < source.binderDepth,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (targetSlots : ∀ offset < source.binderDepth,
      context[binders (targetDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < source.binderDepth,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (targetFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (targetDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (firstDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (secondDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      temporary (temporaryDepth + firstOffset) ≠ binders (targetDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base type)
          (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth source)
          (encodeWithAssignment signature.symbol base constant binders assignment targetDepth source)))) := by
  let first := alphaDisjoint signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    source assignment sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    sourceSlots temporarySlots sourceFresh temporaryFresh firstDisjoint variableTyping constantTyping
  let second := alphaDisjoint signature profile structural typing rules binding base constant temporary binders
    baseSorted constantSorted temporaryInjective bindersInjective temporaryIndependent baseIndependent
    source assignment temporaryDepth targetDepth antecedent antecedentSorted assignmentSorted
    temporarySlots targetSlots temporaryFresh targetFresh secondDisjoint variableTyping constantTyping
  exact HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted
    (encodeType_sorted signature context base baseSorted type)
    (encode_sorted signature context base constant binders baseSorted constantSorted source assignment
      sourceDepth assignmentSorted sourceSlots)
    (encode_sorted signature context base constant temporary baseSorted constantSorted source assignment
      temporaryDepth assignmentSorted temporarySlots)
    (encode_sorted signature context base constant binders baseSorted constantSorted source assignment
      targetDepth assignmentSorted targetSlots) first second

#print axioms alphaDisjoint
#print axioms rebind
/-! ## Scope of the generated alpha-renaming receipts -/

theorem alphaDisjoint_varsBelow (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (leftBinders rightBinders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (leftInjective : Function.Injective leftBinders) (rightInjective : Function.Injective rightBinders)
    (baseIndependentLeft : ∀ slot index, ¬ Preterm.HasVar context (leftBinders slot) (base index))
    (baseIndependentRight : ∀ slot index, ¬ Preterm.HasVar context (rightBinders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (assignment : Assignment gamma) (leftDepth rightDepth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
      (leftSlots : ∀ offset < source.binderDepth, context[leftBinders (leftDepth + offset)]? = some (.bound signature.ids.object))
      (rightSlots : ∀ offset < source.binderDepth, context[rightBinders (rightDepth + offset)]? = some (.bound signature.ids.object))
      (leftFresh : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (leftBinders (leftDepth + offset)) antecedent)
      (rightFresh : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (rightBinders (rightDepth + offset)) antecedent)
      (disjoint : ∀ leftOffset < source.binderDepth, ∀ rightOffset < source.binderDepth,
        leftBinders (leftDepth + leftOffset) ≠ rightBinders (rightDepth + rightOffset))
      (variableTyping : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
      (constantTyping : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      (limit : Nat)
      (_ : ∀ index, Preterm.VarsBelow limit (base index))
      (_ : ∀ {type} (symbol : Const type), Preterm.VarsBelow limit (constant symbol))
      (_ : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (assignment index))
      (_ : Preterm.VarsBelow limit antecedent)
      (_ : ∀ offset < source.binderDepth, leftBinders (leftDepth + offset) < limit)
      (_ : ∀ offset < source.binderDepth, rightBinders (rightDepth + offset) < limit)
      (_ : ∀ {type} (index : Var gamma type), (variableTyping index).val.VarsBelow limit)
      (_ : ∀ {type} (symbol : Const type), (constantTyping symbol).val.VarsBelow limit),
      (alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
        baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight source
        assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping).val.VarsBelow limit := by
  induction source with
  | var index =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simp only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound _, assignmentBound index⟩, variableBound index⟩
  | const symbol =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simp only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound _, constantBound symbol⟩, constantsBound symbol⟩
  | top | bot =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ [.theoremApp _ [antecedent] []])
      simp [ProofWitness.VarsBelow, Preterm.VarsBelow, applySymbol, Preterm.applyArgs,
        encodeType, encodeWithAssignment, antecedentBound]
  | @app gamma domain result first second ihFirst ihSecond =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      have firstLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
      have rightFirstSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
      let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
        firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      have leftSecondSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
      have rightSecondSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
      let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
        secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      have firstLeftNames : ∀ offset < first.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstRightNames : ∀ offset < first.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstScope := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound firstLeftNames firstRightNames variableBound constantsBound
      have firstLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        first assignment leftDepth assignmentBound firstLeftNames
      have firstRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        first assignment rightDepth assignmentBound firstRightNames
      have secondLeftNames : ∀ offset < second.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondRightNames : ∀ offset < second.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondScope := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound secondLeftNames secondRightNames variableBound constantsBound
      have secondLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        second assignment leftDepth assignmentBound secondLeftNames
      have secondRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        second assignment rightDepth assignmentBound secondRightNames
      simp only [alphaDisjoint]
      exact HOLKernelCongruence.application_varsBelow signature rules binding antecedent
        (encodeType signature.symbol base domain) (encodeType signature.symbol base result) _ _ _ _
        antecedentSorted (encodeType_sorted signature context base baseSorted domain)
        (encodeType_sorted signature context base baseSorted result)
        leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof limit
        antecedentBound (encodeType_varsBelow _ _ _ baseBound _) (encodeType_varsBelow _ _ _ baseBound _)
        firstLeftScope firstRightScope secondLeftScope secondRightScope firstScope secondScope
  | and first second ihFirst ihSecond | or first second ihFirst ihSecond | imp first second ihFirst ihSecond =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      have firstLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
      have rightFirstSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
      let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
        firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      have leftSecondSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
      have rightSecondSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
      let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
        secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      have firstLeftNames : ∀ offset < first.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstRightNames : ∀ offset < first.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstScope := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound firstLeftNames firstRightNames variableBound constantsBound
      have firstLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        first assignment leftDepth assignmentBound firstLeftNames
      have firstRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        first assignment rightDepth assignmentBound firstRightNames
      have secondLeftNames : ∀ offset < second.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondRightNames : ∀ offset < second.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondScope := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound secondLeftNames secondRightNames variableBound constantsBound
      have secondLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        second assignment leftDepth assignmentBound secondLeftNames
      have secondRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        second assignment rightDepth assignmentBound secondRightNames
      simp only [alphaDisjoint]
      first
      | exact HOLKernelCongruence.conjunctionCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof limit
          antecedentBound firstLeftScope firstRightScope secondLeftScope secondRightScope firstScope secondScope
      | exact HOLKernelCongruence.disjunctionCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof limit
          antecedentBound firstLeftScope firstRightScope secondLeftScope secondRightScope firstScope secondScope
      | exact HOLKernelCongruence.implicationCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof limit
          antecedentBound firstLeftScope firstRightScope secondLeftScope secondRightScope firstScope secondScope
  | @eq gamma type first second ihFirst ihSecond =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      have firstLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftSlots := fun offset smaller => leftSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightSlots := fun offset smaller => rightSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondLeftFresh := fun offset smaller => leftFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondRightFresh := fun offset smaller => rightFresh offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondDisjoint := fun leftOffset leftSmaller rightOffset rightSmaller =>
        disjoint leftOffset (Nat.lt_of_lt_of_le leftSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
          rightOffset (Nat.lt_of_lt_of_le rightSmaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted first assignment leftDepth assignmentSorted firstLeftSlots
      have rightFirstSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted first assignment rightDepth assignmentSorted firstRightSlots
      let firstProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight first assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted firstLeftSlots firstRightSlots
        firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
      have leftSecondSorted := encode_sorted signature context base constant leftBinders
        baseSorted constantSorted second assignment leftDepth assignmentSorted secondLeftSlots
      have rightSecondSorted := encode_sorted signature context base constant rightBinders
        baseSorted constantSorted second assignment rightDepth assignmentSorted secondRightSlots
      let secondProof := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight second assignment leftDepth rightDepth antecedent
        antecedentSorted assignmentSorted secondLeftSlots secondRightSlots
        secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
      have firstLeftNames : ∀ offset < first.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstRightNames : ∀ offset < first.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have firstScope := ihFirst assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        firstLeftSlots firstRightSlots firstLeftFresh firstRightFresh firstDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound firstLeftNames firstRightNames variableBound constantsBound
      have firstLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        first assignment leftDepth assignmentBound firstLeftNames
      have firstRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        first assignment rightDepth assignmentBound firstRightNames
      have secondLeftNames : ∀ offset < second.binderDepth, leftBinders (leftDepth + offset) < limit :=
        fun offset smaller => leftNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondRightNames : ∀ offset < second.binderDepth, rightBinders (rightDepth + offset) < limit :=
        fun offset smaller => rightNames offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have secondScope := ihSecond assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted
        secondLeftSlots secondRightSlots secondLeftFresh secondRightFresh secondDisjoint variableTyping constantTyping
        limit baseBound constantBound assignmentBound antecedentBound secondLeftNames secondRightNames variableBound constantsBound
      have secondLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        second assignment leftDepth assignmentBound secondLeftNames
      have secondRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        second assignment rightDepth assignmentBound secondRightNames
      simp only [alphaDisjoint]
      exact HOLKernelCongruence.equalityCongruence_varsBelow signature profile rules binding antecedent
        (encodeType signature.symbol base type) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted type)
        leftFirstSorted rightFirstSorted leftSecondSorted rightSecondSorted firstProof secondProof limit
        antecedentBound (encodeType_varsBelow _ _ _ baseBound type)
        firstLeftScope firstRightScope secondLeftScope secondRightScope firstScope secondScope
  | not body ih =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      let bodyProof := alphaDisjoint signature profile structural typing rules binding base constant leftBinders rightBinders
        baseSorted constantSorted leftInjective rightInjective baseIndependentLeft baseIndependentRight body
        assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping
      have bodyScope := ih assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      have bodyLeftScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound
        body assignment leftDepth assignmentBound leftNames
      have bodyRightScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound
        body assignment rightDepth assignmentBound rightNames
      exact HOLKernelCongruence.negationCongruence_varsBelow signature profile rules _ _ _ antecedentSorted
        (encode_sorted signature context base constant leftBinders baseSorted constantSorted body assignment leftDepth assignmentSorted leftSlots)
        (encode_sorted signature context base constant rightBinders baseSorted constantSorted body assignment rightDepth assignmentSorted rightSlots)
        bodyProof limit antecedentBound bodyLeftScope bodyRightScope bodyScope
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro assignment leftDepth rightDepth antecedent antecedentSorted assignmentSorted leftSlots rightSlots
        leftFresh rightFresh disjoint variableTyping constantTyping limit baseBound constantBound assignmentBound
        antecedentBound leftNames rightNames variableBound constantsBound
      have leftHead : context[leftBinders leftDepth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using leftSlots 0 (Nat.zero_lt_succ _)
      have rightHead : context[rightBinders rightDepth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using rightSlots 0 (Nat.zero_lt_succ _)
      have leftBodySlots : ∀ offset < body.binderDepth,
          context[leftBinders (leftDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := leftSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have rightBodySlots : ∀ offset < body.binderDepth,
          context[rightBinders (rightDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := rightSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have leftHeadSorted : Preterm.HasType terms context (.var (leftBinders leftDepth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) leftHead
      have rightHeadSorted : Preterm.HasType terms context (.var (rightBinders rightDepth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) rightHead
      let leftExtra := hasType signature.symbol (.var (leftBinders leftDepth)) (encodeType signature.symbol base domain)
      let rightExtra := hasType signature.symbol (.var (rightBinders rightDepth)) (encodeType signature.symbol base domain)
      let equalityExtra := holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
        (.var (leftBinders leftDepth)) (.var (rightBinders rightDepth)))
      let leftContext := conjunction signature.symbol antecedent leftExtra
      let rightContext := conjunction signature.symbol antecedent rightExtra
      let equalityContext := conjunction signature.symbol antecedent equalityExtra
      have leftExtraSorted := hasType_sorted signature context leftHeadSorted domainSorted
      have rightExtraSorted := hasType_sorted signature context rightHeadSorted domainSorted
      have equalityExtraSorted := holds_sorted signature context (signature.application context .eqc _
        (.cons (.regular domainSorted) (.cons (.regular leftHeadSorted) (.cons (.regular rightHeadSorted) .nil))))
      have leftContextSorted := conjunction_sorted signature context antecedentSorted leftExtraSorted
      have rightContextSorted := conjunction_sorted signature context antecedentSorted rightExtraSorted
      have equalityContextSorted := conjunction_sorted signature context antecedentSorted equalityExtraSorted
      have leftExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context _ assignment leftHeadSorted assignmentSorted
      have rightExtendedSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context _ assignment rightHeadSorted assignmentSorted
      have leftBodyFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (leftBinders (leftDepth + 1 + offset)) leftContext := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ leftHead
        · intro same
          have impossible := leftInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            leftFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentLeft _) domain
      have rightBodyFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (rightBinders (rightDepth + 1 + offset)) rightContext := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ rightHead
        · intro same
          have impossible := rightInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            rightFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentRight _) domain
      have equalityLeftFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (leftBinders (leftDepth + 1 + offset)) equalityContext := by
        intro offset smaller
        apply equalityContext_independent _ _ _ signature.ids.object signature.symbol _ _ leftHead rightHead
        · intro same
          have impossible := leftInjective same
          omega
        · have apart := disjoint (offset + 1) (Nat.add_lt_add_right smaller 1) 0 (Nat.zero_lt_succ _)
          simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            leftFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentLeft _) domain
      have equalityRightFresh : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (rightBinders (rightDepth + 1 + offset)) equalityContext := by
        intro offset smaller
        apply equalityContext_independent _ _ _ signature.ids.object signature.symbol _ _ leftHead rightHead
        · have apart := Ne.symm (disjoint 0 (Nat.zero_lt_succ _) (offset + 1) (Nat.add_lt_add_right smaller 1))
          simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1 offset] using apart
        · intro same
          have impossible := rightInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using
            rightFresh (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependentRight _) domain
      have bodyDisjoint : ∀ leftOffset < body.binderDepth, ∀ rightOffset < body.binderDepth,
          leftBinders (leftDepth + 1 + leftOffset) ≠ rightBinders (rightDepth + 1 + rightOffset) := by
        intro leftOffset leftSmaller rightOffset rightSmaller
        have apart := disjoint (leftOffset + 1) (Nat.add_lt_add_right leftSmaller 1)
          (rightOffset + 1) (Nat.add_lt_add_right rightSmaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 leftOffset, Nat.add_comm 1 rightOffset] using apart
      let leftProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent leftExtra antecedentSorted leftExtraSorted
      let rightProjection := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent rightExtra antecedentSorted rightExtraSorted
      let relation := HOLKernelStructuralRules.right (definitions := definitions) (hypotheses := hypotheses)
        signature structural antecedent equalityExtra antecedentSorted equalityExtraSorted
      let leftVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol leftContext (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact leftProjection
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent leftExtra
              antecedentSorted leftExtraSorted baseSorted assignmentSorted variableTyping) index
      let rightVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol rightContext (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact rightProjection
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent rightExtra
              antecedentSorted rightExtraSorted baseSorted assignmentSorted variableTyping) index
      let leftConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol leftContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent leftExtra
          antecedentSorted leftExtraSorted baseSorted constantSorted constantTyping
      let rightConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol rightContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent rightExtra
          antecedentSorted rightExtraSorted baseSorted constantSorted constantTyping
      let equalityConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol equalityContext (constant symbol) (encodeType signature.symbol base type)) :=
        weakenConstants signature structural base constant antecedent equalityExtra
          antecedentSorted equalityExtraSorted baseSorted constantSorted constantTyping
      let bodyLeftTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant leftBinders
        baseSorted constantSorted leftInjective baseIndependentLeft body
        (Assignment.extend (.var (leftBinders leftDepth)) assignment) (leftDepth + 1) leftContext
        leftContextSorted leftExtendedSorted leftBodySlots leftBodyFresh leftVariables leftConstants
      let bodyRightTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant rightBinders
        baseSorted constantSorted rightInjective baseIndependentRight body
        (Assignment.extend (.var (rightBinders rightDepth)) assignment) (rightDepth + 1) rightContext
        rightContextSorted rightExtendedSorted rightBodySlots rightBodyFresh rightVariables rightConstants
      let related : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol equalityContext (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (Assignment.extend (.var (leftBinders leftDepth)) assignment index)
                (Assignment.extend (.var (rightBinders rightDepth)) assignment index)))) := by
        intro type index
        cases index with
        | vz => exact relation
        | vs index =>
            apply HOLKernelStructuralRules.weaken signature structural antecedent equalityExtra _
              antecedentSorted equalityExtraSorted _
              (HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
                (encodeType_sorted signature context base baseSorted type) (assignmentSorted index) (variableTyping index))
            exact holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (assignmentSorted index)) (.cons (.regular (assignmentSorted index)) .nil))))
      let rightHeadInEquality := HOLKernelBindingProofs.Native.equalityRightTyping signature binding
        (encodeType signature.symbol base domain) equalityContext (.var (leftBinders leftDepth))
        (.var (rightBinders rightDepth)) domainSorted equalityContextSorted leftHeadSorted rightHeadSorted relation
      let equalityVariables : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol equalityContext
              (Assignment.extend (.var (rightBinders rightDepth)) assignment index)
              (encodeType signature.symbol base type)) := by
        intro type index
        cases index with
        | vz => exact rightHeadInEquality
        | vs index =>
            exact (weakenVariables signature structural base assignment antecedent equalityExtra
              antecedentSorted equalityExtraSorted baseSorted assignmentSorted variableTyping) index
      let assignmentComparison := HOLKernelTermCongruence.congruence signature profile structural typing rules binding
        base constant leftBinders baseSorted constantSorted leftInjective baseIndependentLeft body
        (Assignment.extend (.var (leftBinders leftDepth)) assignment)
        (Assignment.extend (.var (rightBinders rightDepth)) assignment) (leftDepth + 1) equalityContext
        equalityContextSorted leftExtendedSorted rightExtendedSorted leftBodySlots equalityLeftFresh related equalityConstants
      let binderComparison := alphaDisjoint signature profile structural typing rules binding base constant
        leftBinders rightBinders baseSorted constantSorted leftInjective rightInjective
        baseIndependentLeft baseIndependentRight body
        (Assignment.extend (.var (rightBinders rightDepth)) assignment)
        (leftDepth + 1) (rightDepth + 1) equalityContext equalityContextSorted rightExtendedSorted
        leftBodySlots rightBodySlots equalityLeftFresh equalityRightFresh bodyDisjoint equalityVariables equalityConstants
      have leftBodySorted := encode_sorted signature context base constant leftBinders baseSorted constantSorted
        body _ (leftDepth + 1) leftExtendedSorted leftBodySlots
      have middleBodySorted := encode_sorted signature context base constant leftBinders baseSorted constantSorted
        body _ (leftDepth + 1) rightExtendedSorted leftBodySlots
      have rightBodySorted := encode_sorted signature context base constant rightBinders baseSorted constantSorted
        body _ (rightDepth + 1) rightExtendedSorted rightBodySlots
      let bodyEquality := HOLKernelInferenceProofs.Native.transitivity signature rules equalityContext _ _ _ _
        equalityContextSorted (encodeType_sorted signature context base baseSorted _)
        leftBodySorted middleBodySorted rightBodySorted assignmentComparison binderComparison
      let abstractionEquality := HOLKernelBindingProofs.Native.abstractionRenaming signature binding
        (encodeType signature.symbol base domain) _ antecedent (leftBinders leftDepth) (rightBinders rightDepth)
        _ _ domainSorted (encodeType_sorted signature context base baseSorted _) antecedentSorted
        leftHead rightHead leftBodySorted rightBodySorted
        (encodeType_independent context _ signature.symbol base (baseIndependentLeft leftDepth) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependentLeft leftDepth) _)
        (by simpa only [Nat.add_zero] using leftFresh 0 (Nat.zero_lt_succ _))
        (encodeType_independent context _ signature.symbol base (baseIndependentRight rightDepth) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependentRight rightDepth) _)
        (by simpa only [Nat.add_zero] using rightFresh 0 (Nat.zero_lt_succ _))
        (by simpa only [Nat.add_zero] using disjoint 0 (Nat.zero_lt_succ _) 0 (Nat.zero_lt_succ _))
        bodyLeftTyping bodyRightTyping bodyEquality
      have leftRoot : leftBinders leftDepth < limit := by
        simpa only [Nat.add_zero] using leftNames 0 (Nat.zero_lt_succ _)
      have rightRoot : rightBinders rightDepth < limit := by
        simpa only [Nat.add_zero] using rightNames 0 (Nat.zero_lt_succ _)
      have domainScope := encodeType_varsBelow signature.symbol base limit baseBound domain
      have leftExtraScope : Preterm.VarsBelow limit leftExtra := ⟨⟨trivial, leftRoot⟩, domainScope⟩
      have rightExtraScope : Preterm.VarsBelow limit rightExtra := ⟨⟨trivial, rightRoot⟩, domainScope⟩
      have equalityExtraScope : Preterm.VarsBelow limit equalityExtra :=
        ⟨trivial, ⟨⟨⟨trivial, domainScope⟩, leftRoot⟩, rightRoot⟩⟩
      have leftContextScope : Preterm.VarsBelow limit leftContext := ⟨⟨trivial, antecedentBound⟩, leftExtraScope⟩
      have rightContextScope : Preterm.VarsBelow limit rightContext := ⟨⟨trivial, antecedentBound⟩, rightExtraScope⟩
      have equalityContextScope : Preterm.VarsBelow limit equalityContext := ⟨⟨trivial, antecedentBound⟩, equalityExtraScope⟩
      have leftExtendedScope : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.VarsBelow limit (Assignment.extend (.var (leftBinders leftDepth)) assignment index) :=
        Assignment.extend_varsBelow limit (.var (leftBinders leftDepth)) assignment leftRoot assignmentBound
      have rightExtendedScope : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.VarsBelow limit (Assignment.extend (.var (rightBinders rightDepth)) assignment index) :=
        Assignment.extend_varsBelow limit (.var (rightBinders rightDepth)) assignment rightRoot assignmentBound
      have leftBodyNames : ∀ offset < body.binderDepth, leftBinders (leftDepth + 1 + offset) < limit := by
        intro offset smaller
        have found := leftNames (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have rightBodyNames : ∀ offset < body.binderDepth, rightBinders (rightDepth + 1 + offset) < limit := by
        intro offset smaller
        have found := rightNames (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have leftVariablesScope : ∀ {type} (index : Var (domain :: gamma) type), (leftVariables index).val.VarsBelow limit := by
        intro type index
        cases index with
        | vz => exact HOLKernelStructuralRules.right_varsBelow signature structural limit _ _ antecedentSorted leftExtraSorted antecedentBound leftExtraScope
        | vs index =>
            exact HOLKernelTermTyping.weakenVariables_varsBelow signature structural base assignment _ _
              antecedentSorted leftExtraSorted baseSorted assignmentSorted variableTyping limit baseBound assignmentBound
              antecedentBound leftExtraScope variableBound index
      have rightVariablesScope : ∀ {type} (index : Var (domain :: gamma) type), (rightVariables index).val.VarsBelow limit := by
        intro type index
        cases index with
        | vz => exact HOLKernelStructuralRules.right_varsBelow signature structural limit _ _ antecedentSorted rightExtraSorted antecedentBound rightExtraScope
        | vs index =>
            exact HOLKernelTermTyping.weakenVariables_varsBelow signature structural base assignment _ _
              antecedentSorted rightExtraSorted baseSorted assignmentSorted variableTyping limit baseBound assignmentBound
              antecedentBound rightExtraScope variableBound index
      have leftConstantsScope : ∀ {type} (symbol : Const type), (leftConstants symbol).val.VarsBelow limit :=
        HOLKernelTermTyping.weakenConstants_varsBelow signature structural base constant _ _
          antecedentSorted leftExtraSorted baseSorted constantSorted constantTyping limit baseBound constantBound
          antecedentBound leftExtraScope constantsBound
      have rightConstantsScope : ∀ {type} (symbol : Const type), (rightConstants symbol).val.VarsBelow limit :=
        HOLKernelTermTyping.weakenConstants_varsBelow signature structural base constant _ _
          antecedentSorted rightExtraSorted baseSorted constantSorted constantTyping limit baseBound constantBound
          antecedentBound rightExtraScope constantsBound
      have equalityConstantsScope : ∀ {type} (symbol : Const type), (equalityConstants symbol).val.VarsBelow limit :=
        HOLKernelTermTyping.weakenConstants_varsBelow signature structural base constant _ _
          antecedentSorted equalityExtraSorted baseSorted constantSorted constantTyping limit baseBound constantBound
          antecedentBound equalityExtraScope constantsBound
      have bodyLeftTypingScope := HOLKernelTermTyping.compileWithAssignment_varsBelow signature structural typing base constant leftBinders
        baseSorted constantSorted leftInjective baseIndependentLeft body _ _ _ leftContextSorted leftExtendedSorted
        leftBodySlots leftBodyFresh leftVariables leftConstants limit baseBound constantBound leftExtendedScope leftContextScope
        leftBodyNames leftVariablesScope leftConstantsScope
      have bodyRightTypingScope := HOLKernelTermTyping.compileWithAssignment_varsBelow signature structural typing base constant rightBinders
        baseSorted constantSorted rightInjective baseIndependentRight body _ _ _ rightContextSorted rightExtendedSorted
        rightBodySlots rightBodyFresh rightVariables rightConstants limit baseBound constantBound rightExtendedScope rightContextScope
        rightBodyNames rightVariablesScope rightConstantsScope
      have relationScope : relation.val.VarsBelow limit :=
        HOLKernelStructuralRules.right_varsBelow signature structural limit _ _ antecedentSorted equalityExtraSorted antecedentBound equalityExtraScope
      have relatedScope : ∀ {type} (index : Var (domain :: gamma) type), (related index).val.VarsBelow limit := by
        intro type index
        cases index with
        | vz => exact relationScope
        | vs index =>
            apply HOLKernelStructuralRules.weaken_varsBelow signature structural limit _ _ _
              antecedentSorted equalityExtraSorted
              (holds_sorted signature context (signature.application context .eqc _
                (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                  (.cons (.regular (assignmentSorted index)) (.cons (.regular (assignmentSorted index)) .nil)))))
            · exact antecedentBound
            · exact equalityExtraScope
            · exact ⟨trivial, ⟨⟨⟨trivial, encodeType_varsBelow _ _ _ baseBound type⟩, assignmentBound index⟩, assignmentBound index⟩⟩
            · change ProofWitness.VarsBelow limit (.theoremApp _ _ [(variableTyping index).val])
              simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
                And.intro ⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound type, assignmentBound index⟩ (variableBound index)
      have rightHeadScope : rightHeadInEquality.val.VarsBelow limit := by
        change ProofWitness.VarsBelow limit (.theoremApp _ _ [relation.val])
        simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro ⟨domainScope, equalityContextScope, leftRoot, rightRoot⟩ relationScope
      have equalityVariablesScope : ∀ {type} (index : Var (domain :: gamma) type), (equalityVariables index).val.VarsBelow limit := by
        intro type index
        cases index with
        | vz => exact rightHeadScope
        | vs index =>
            exact HOLKernelTermTyping.weakenVariables_varsBelow signature structural base assignment _ _
              antecedentSorted equalityExtraSorted baseSorted assignmentSorted variableTyping limit baseBound assignmentBound
              antecedentBound equalityExtraScope variableBound index
      have assignmentComparisonScope := HOLKernelTermCongruence.congruence_varsBelow signature profile structural typing rules binding
        base constant leftBinders baseSorted constantSorted leftInjective baseIndependentLeft body _ _ _ _
        equalityContextSorted leftExtendedSorted rightExtendedSorted leftBodySlots equalityLeftFresh related equalityConstants limit
        baseBound constantBound leftExtendedScope rightExtendedScope equalityContextScope leftBodyNames relatedScope equalityConstantsScope
      have binderComparisonScope := ih _ _ _ _ equalityContextSorted rightExtendedSorted leftBodySlots rightBodySlots
        equalityLeftFresh equalityRightFresh bodyDisjoint equalityVariables equalityConstants limit baseBound constantBound
        rightExtendedScope equalityContextScope leftBodyNames rightBodyNames equalityVariablesScope equalityConstantsScope
      have leftBodyScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound body _ _ leftExtendedScope leftBodyNames
      have middleBodyScope := encode_varsBelow signature.symbol base constant leftBinders limit baseBound constantBound body _ _ rightExtendedScope leftBodyNames
      have rightBodyScope := encode_varsBelow signature.symbol base constant rightBinders limit baseBound constantBound body _ _ rightExtendedScope rightBodyNames
      have bodyEqualityScope : bodyEquality.val.VarsBelow limit := by
        change ProofWitness.VarsBelow limit (.theoremApp _ _ [assignmentComparison.val, binderComparison.val])
        simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro ⟨equalityContextScope, encodeType_varsBelow _ _ _ baseBound _, leftBodyScope, middleBodyScope, rightBodyScope⟩
            ⟨assignmentComparisonScope, binderComparisonScope⟩
      have abstractionScope : abstractionEquality.val.VarsBelow limit := by
        change ProofWitness.VarsBelow limit (.theoremApp _ _ [bodyLeftTyping.val, bodyRightTyping.val, bodyEquality.val])
        simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro ⟨domainScope, encodeType_varsBelow _ _ _ baseBound _, antecedentBound, leftRoot, rightRoot, leftBodyScope, rightBodyScope⟩
            ⟨bodyLeftTypingScope, bodyRightTypingScope, bodyEqualityScope⟩
      simp only [alphaDisjoint]
      first
      | exact abstractionScope
      | exact HOLKernelCongruence.universalCongruence_varsBelow signature profile rules _ _ _ _ _ _
          antecedentSorted domainSorted leftHead rightHead leftBodySorted rightBodySorted abstractionEquality limit
          antecedentBound domainScope leftBodyScope rightBodyScope leftRoot rightRoot abstractionScope
      | exact HOLKernelCongruence.existentialCongruence_varsBelow signature profile rules _ _ _ _ _ _
          antecedentSorted domainSorted leftHead rightHead leftBodySorted rightBodySorted abstractionEquality limit
          antecedentBound domainScope leftBodyScope rightBodyScope leftRoot rightRoot abstractionScope

#print axioms alphaDisjoint_varsBelow
theorem rebind_varsBelow (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type)
    (assignment : Assignment gamma) (sourceDepth targetDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < source.binderDepth,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (targetSlots : ∀ offset < source.binderDepth,
      context[binders (targetDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < source.binderDepth,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (targetFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (binders (targetDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < source.binderDepth,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (firstDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (secondDisjoint : ∀ firstOffset < source.binderDepth, ∀ secondOffset < source.binderDepth,
      temporary (temporaryDepth + firstOffset) ≠ binders (targetDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (limit : Nat)
    (baseBound : ∀ index, Preterm.VarsBelow limit (base index))
    (constantBound : ∀ {type} (symbol : Const type), Preterm.VarsBelow limit (constant symbol))
    (assignmentBound : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (assignment index))
    (antecedentBound : Preterm.VarsBelow limit antecedent)
    (sourceNames : ∀ offset < source.binderDepth, binders (sourceDepth + offset) < limit)
    (targetNames : ∀ offset < source.binderDepth, binders (targetDepth + offset) < limit)
    (temporaryNames : ∀ offset < source.binderDepth, temporary (temporaryDepth + offset) < limit)
    (variableBound : ∀ {type} (index : Var gamma type), (variableTyping index).val.VarsBelow limit)
    (constantsBound : ∀ {type} (symbol : Const type), (constantTyping symbol).val.VarsBelow limit) :
    (rebind signature profile structural typing rules binding base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment sourceDepth targetDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots targetSlots temporarySlots sourceFresh targetFresh temporaryFresh firstDisjoint secondDisjoint variableTyping constantTyping).val.VarsBelow limit := by
  let first := alphaDisjoint signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    source assignment sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    sourceSlots temporarySlots sourceFresh temporaryFresh firstDisjoint variableTyping constantTyping
  let second := alphaDisjoint signature profile structural typing rules binding base constant temporary binders
    baseSorted constantSorted temporaryInjective bindersInjective temporaryIndependent baseIndependent
    source assignment temporaryDepth targetDepth antecedent antecedentSorted assignmentSorted
    temporarySlots targetSlots temporaryFresh targetFresh secondDisjoint variableTyping constantTyping
  have firstScope := alphaDisjoint_varsBelow signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
    sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots temporarySlots sourceFresh temporaryFresh
    firstDisjoint variableTyping constantTyping limit baseBound constantBound assignmentBound antecedentBound sourceNames temporaryNames
    variableBound constantsBound
  have secondScope := alphaDisjoint_varsBelow signature profile structural typing rules binding base constant temporary binders
    baseSorted constantSorted temporaryInjective bindersInjective temporaryIndependent baseIndependent source assignment
    temporaryDepth targetDepth antecedent antecedentSorted assignmentSorted temporarySlots targetSlots temporaryFresh targetFresh
    secondDisjoint variableTyping constantTyping limit baseBound constantBound assignmentBound antecedentBound temporaryNames targetNames
    variableBound constantsBound
  have sourceScope := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound source assignment sourceDepth assignmentBound sourceNames
  have targetScope := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound source assignment targetDepth assignmentBound targetNames
  have temporaryScope := encode_varsBelow signature.symbol base constant temporary limit baseBound constantBound source assignment temporaryDepth assignmentBound temporaryNames
  change ProofWitness.VarsBelow limit (.theoremApp _ _ [first.val, second.val])
  simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro ⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound type, sourceScope, temporaryScope, targetScope⟩ ⟨firstScope, secondScope⟩

#print axioms rebind_varsBelow


end Mettapedia.Languages.MM0.HOLKernelAlpha

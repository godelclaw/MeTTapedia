import Mettapedia.Languages.MM0.HOLKernelTermTyping
import Mettapedia.Languages.MM0.HOLKernelTermAssignments
import Mettapedia.Languages.MM0.HOLKernelTypingProofs
import Mettapedia.Languages.MM0.HOLKernelTypeSupport
import Mettapedia.Languages.MM0.HOLKernelCongruence

/-!
# Pointwise term-assignment congruence for maintained MM0 HOL

Checked equalities between native variable images lift through all thirteen
intrinsic HOL term constructors. Both encodings use the same binder family
and depth. Context freshness is required only in the finite source binder-depth
window; names beyond that window impose no condition. Binding cases extend the native logical context, construct equality
of the new variable, and weaken the retained equalities and constant typings.

Changing binder families and comparing with source simultaneous substitution
are further alpha-transport obligations. This construction compares the actual
terms obtained from the specified assignments, rather than assumed denotations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermCongruence
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelTypeSupport
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

def congruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (left right : Assignment gamma) (depth : Nat) (antecedent : Preterm),
      Preterm.HasType terms context antecedent [] signature.ids.wff →
      (∀ {type} (index : Var gamma type),
        Preterm.HasType terms context (left index) [] signature.ids.object) →
      (∀ {type} (index : Var gamma type),
        Preterm.HasType terms context (right index) [] signature.ids.object) →
      (∀ offset < source.binderDepth,
        context[binders (depth + offset)]? = some (.bound signature.ids.object)) →
      (∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent) →
      (∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (entails signature.symbol antecedent (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type) (left index) (right index))))) →
      (∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) →
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (entails signature.symbol antecedent (holds signature.symbol
          (equality signature.symbol (encodeType signature.symbol base type)
            (encodeWithAssignment signature.symbol base constant binders left depth source)
            (encodeWithAssignment signature.symbol base constant binders right depth source)))) := by
  match source with
  | .var index =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      exact variableEquality index
  | .const symbol =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted _) (constantSorted symbol) (constantProof symbol)
  | .top =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .truth [] .nil)
        (HOLKernelTypingProofs.truthTyping signature typing antecedent antecedentSorted)
  | .bot =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      exact HOLKernelInferenceProofs.Native.reflexivity signature rules antecedent _ _ antecedentSorted
        (signature.application context .bool [] .nil) (signature.application context .falsity [] .nil)
        (HOLKernelTypingProofs.falsityTyping signature typing antecedent antecedentSorted)
  | .app first second | .and first second | .or first second | .imp first second =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      have firstSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have leftFirstSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted first left depth leftSorted firstSlots
      have rightFirstSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted first right depth rightSorted firstSlots
      have leftSecondSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted second left depth leftSorted secondSlots
      have rightSecondSorted := encode_sorted signature context base constant binders baseSorted
        constantSorted second right depth rightSorted secondSlots
      let firstProof := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent first left right depth antecedent
        antecedentSorted leftSorted rightSorted firstSlots firstIndependent variableEquality constantProof
      let secondProof := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent second left right depth antecedent
        antecedentSorted leftSorted rightSorted secondSlots secondIndependent variableEquality constantProof
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
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      exact HOLKernelCongruence.negationCongruence signature profile rules antecedent _ _ antecedentSorted
        (encode_sorted signature context base constant binders baseSorted constantSorted body left depth leftSorted boundSlots)
        (encode_sorted signature context base constant binders baseSorted constantSorted body right depth rightSorted boundSlots)
        (congruence signature profile structural typing rules binding base constant binders baseSorted constantSorted
          bindersInjective baseIndependent body left right depth antecedent antecedentSorted leftSorted rightSorted
          boundSlots independent variableEquality constantProof)
  | .eq (τ := type) first second =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      have firstSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondSlots := fun offset smaller => boundSlots offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      have firstIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_left first.binderDepth second.binderDepth))
      have secondIndependent := fun offset smaller => independent offset
        (Nat.lt_of_lt_of_le smaller (Nat.le_max_right first.binderDepth second.binderDepth))
      exact HOLKernelCongruence.equalityCongruence signature profile rules binding antecedent
        (encodeType signature.symbol base type) _ _ _ _ antecedentSorted
        (encodeType_sorted signature context base baseSorted type)
        (encode_sorted signature context base constant binders baseSorted constantSorted first left depth leftSorted firstSlots)
        (encode_sorted signature context base constant binders baseSorted constantSorted first right depth rightSorted firstSlots)
        (encode_sorted signature context base constant binders baseSorted constantSorted second left depth leftSorted secondSlots)
        (encode_sorted signature context base constant binders baseSorted constantSorted second right depth rightSorted secondSlots)
        (congruence signature profile structural typing rules binding base constant binders baseSorted constantSorted
          bindersInjective baseIndependent first left right depth antecedent antecedentSorted leftSorted rightSorted
          firstSlots firstIndependent variableEquality constantProof)
        (congruence signature profile structural typing rules binding base constant binders baseSorted constantSorted
          bindersInjective baseIndependent second left right depth antecedent antecedentSorted leftSorted rightSorted
          secondSlots secondIndependent variableEquality constantProof)
  | .lam (σ := domain) body | .all (σ := domain) body | .ex (σ := domain) body =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted boundSlots independent variableEquality constantProof
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using boundSlots 0 (Nat.zero_lt_succ _)
      have bodySlots : ∀ offset < body.binderDepth,
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := boundSlots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have boundSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) head
      let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
      have extraSorted := hasType_sorted signature context boundSorted domainSorted
      let extended := conjunction signature.symbol antecedent extra
      have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
      have extendedIndependent : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
        · intro same
          have impossible := bindersInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
      have extendedEqualities : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol extended (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (Assignment.extend (.var (binders depth)) left index)
                (Assignment.extend (.var (binders depth)) right index)))) := by
        intro type index
        cases index with
        | vz =>
            exact HOLKernelInferenceProofs.Native.reflexivity signature rules extended _ _ extendedSorted
              domainSorted boundSorted
              (HOLKernelStructuralRules.right signature structural _ _ antecedentSorted extraSorted)
        | vs index =>
            apply HOLKernelStructuralRules.weaken signature structural antecedent extra _
              antecedentSorted extraSorted _ (variableEquality index)
            exact holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil))))
      have extendedConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
        HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
          antecedentSorted extraSorted baseSorted constantSorted constantProof
      have extendedLeftSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) left index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context (.var (binders depth)) left boundSorted leftSorted
      have extendedRightSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) right index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context (.var (binders depth)) right boundSorted rightSorted
      let bodyProof := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent body
        (Assignment.extend (.var (binders depth)) left) (Assignment.extend (.var (binders depth)) right)
        (depth + 1) extended extendedSorted extendedLeftSorted extendedRightSorted bodySlots
        extendedIndependent extendedEqualities extendedConstants
      have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
        body _ (depth + 1) extendedLeftSorted bodySlots
      have rightBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
        body _ (depth + 1) extendedRightSorted bodySlots
      have abstractionEquality := HOLKernelBindingProofs.Native.abstractionCongruence signature binding
        antecedent (encodeType signature.symbol base domain) _ (binders depth) _ _ antecedentSorted domainSorted
        (encodeType_sorted signature context base baseSorted _) head leftBodySorted rightBodySorted
        (by simpa only [Nat.add_zero] using independent 0 (Nat.zero_lt_succ _))
        (encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependent _) _) bodyProof
      first
      | exact abstractionEquality
      | exact HOLKernelCongruence.universalCongruence signature profile rules antecedent _ _ _
          (binders depth) (binders depth) antecedentSorted domainSorted head head
          leftBodySorted rightBodySorted abstractionEquality
      | exact HOLKernelCongruence.existentialCongruence signature profile rules antecedent _ _ _
          (binders depth) (binders depth) antecedentSorted domainSorted head head
          leftBodySorted rightBodySorted abstractionEquality
termination_by structural source


#print axioms congruence
/-- The complete congruence receipt uses only the names supplied by its
encodings, binder window and input equality/constant-typing receipts. -/
theorem congruence_varsBelow (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) :
    ∀ (left right : Assignment gamma) (depth : Nat) (antecedent : Preterm)
      (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
      (leftSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (left index) [] signature.ids.object)
      (rightSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (right index) [] signature.ids.object)
      (slots : ∀ offset < source.binderDepth, context[binders (depth + offset)]? = some (.bound signature.ids.object))
      (independent : ∀ offset < source.binderDepth, ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
      (variableEquality : ∀ {type} (index : Var gamma type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (entails signature.symbol antecedent (holds signature.symbol
            (equality signature.symbol (encodeType signature.symbol base type) (left index) (right index)))))
      (constantProof : ∀ {type} (symbol : Const type),
        CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
          (context := context) (hypotheses := hypotheses)
          (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
      (limit : Nat)
      (_ : ∀ index, Preterm.VarsBelow limit (base index))
      (_ : ∀ {type} (symbol : Const type), Preterm.VarsBelow limit (constant symbol))
      (_ : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (left index))
      (_ : ∀ {type} (index : Var gamma type), Preterm.VarsBelow limit (right index))
      (_ : Preterm.VarsBelow limit antecedent)
      (_ : ∀ offset < source.binderDepth, binders (depth + offset) < limit)
      (_ : ∀ {type} (index : Var gamma type), (variableEquality index).val.VarsBelow limit)
      (_ : ∀ {type} (symbol : Const type), (constantProof symbol).val.VarsBelow limit),
      (congruence signature profile structural typing rules binding base constant binders baseSorted constantSorted
        bindersInjective baseIndependent source left right depth antecedent antecedentSorted leftSorted rightSorted
        slots independent variableEquality constantProof).val.VarsBelow limit := by
  induction source with
  | var index =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      exact variableBound index
  | const symbol =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ _)
      simp only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨antecedentBound, encodeType_varsBelow _ _ _ baseBound _, constantBound symbol⟩, constantsBound symbol⟩
  | top | bot =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      change ProofWitness.VarsBelow limit (.theoremApp _ _ [.theoremApp _ [antecedent] []])
      simp [ProofWitness.VarsBelow, Preterm.VarsBelow, applySymbol, Preterm.applyArgs, encodeType, encodeWithAssignment, antecedentBound]
  | @app gamma domain result first second ihFirst ihSecond =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      have firstNames (offset : Nat) (smaller : offset < first.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have secondNames (offset : Nat) (smaller : offset < second.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have firstLeft := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound first left depth leftBound firstNames
      have firstRight := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound first right depth rightBound firstNames
      have secondLeft := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound second left depth leftBound secondNames
      have secondRight := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound second right depth rightBound secondNames
      have firstProof := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        variableEquality constantProof limit baseBound constantBound leftBound rightBound antecedentBound firstNames variableBound constantsBound
      have secondProof := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        variableEquality constantProof limit baseBound constantBound leftBound rightBound antecedentBound secondNames variableBound constantsBound
      let firstNative := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent first left right depth antecedent
        antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        variableEquality constantProof
      let secondNative := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent second left right depth antecedent
        antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        variableEquality constantProof
      simp only [congruence]
      exact HOLKernelCongruence.application_varsBelow signature rules binding antecedent (encodeType signature.symbol base domain) (encodeType signature.symbol base result) _ _ _ _
          antecedentSorted (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
          (encode_sorted signature context base constant binders baseSorted constantSorted first left depth leftSorted (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))))
          (encode_sorted signature context base constant binders baseSorted constantSorted first right depth rightSorted (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))))
          (encode_sorted signature context base constant binders baseSorted constantSorted second left depth leftSorted (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))))
          (encode_sorted signature context base constant binders baseSorted constantSorted second right depth rightSorted (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))) firstNative secondNative
          limit antecedentBound (encodeType_varsBelow _ _ _ baseBound _) (encodeType_varsBelow _ _ _ baseBound _)
          firstLeft firstRight secondLeft secondRight firstProof secondProof
  | and first second ihFirst ihSecond | or first second ihFirst ihSecond | imp first second ihFirst ihSecond | eq first second ihFirst ihSecond =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      have firstNames (offset : Nat) (smaller : offset < first.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _))
      have secondNames (offset : Nat) (smaller : offset < second.binderDepth) : binders (depth + offset) < limit :=
        bindersBound offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _))
      have firstLeft := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound first left depth leftBound firstNames
      have firstRight := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound first right depth rightBound firstNames
      have secondLeft := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound second left depth leftBound secondNames
      have secondRight := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound second right depth rightBound secondNames
      have firstProof := ihFirst left right depth antecedent antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        variableEquality constantProof limit baseBound constantBound leftBound rightBound antecedentBound firstNames variableBound constantsBound
      have secondProof := ihSecond left right depth antecedent antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        variableEquality constantProof limit baseBound constantBound leftBound rightBound antecedentBound secondNames variableBound constantsBound
      let firstNative := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent first left right depth antecedent
        antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
        variableEquality constantProof
      let secondNative := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent second left right depth antecedent
        antecedentSorted leftSorted rightSorted
        (fun offset smaller => slots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        (fun offset smaller => independent offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
        variableEquality constantProof
      simp only [congruence]
      first
      | exact HOLKernelCongruence.conjunctionCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted _ _ _ _ firstNative secondNative limit antecedentBound firstLeft firstRight secondLeft secondRight firstProof secondProof
      | exact HOLKernelCongruence.disjunctionCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted _ _ _ _ firstNative secondNative limit antecedentBound firstLeft firstRight secondLeft secondRight firstProof secondProof
      | exact HOLKernelCongruence.implicationCongruence_varsBelow signature profile rules binding _ _ _ _ _
          antecedentSorted _ _ _ _ firstNative secondNative limit antecedentBound firstLeft firstRight secondLeft secondRight firstProof secondProof
      | exact HOLKernelCongruence.equalityCongruence_varsBelow signature profile rules binding _ _ _ _ _ _
          antecedentSorted _ _ _ _ _ firstNative secondNative limit antecedentBound (encodeType_varsBelow _ _ _ baseBound _)
          firstLeft firstRight secondLeft secondRight firstProof secondProof
  | not body ih =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      have leftBody := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body left depth leftBound bindersBound
      have rightBody := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body right depth rightBound bindersBound
      have bodyProof := ih left right depth antecedent antecedentSorted leftSorted rightSorted slots independent
        variableEquality constantProof limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      exact HOLKernelCongruence.negationCongruence_varsBelow signature profile rules _ _ _
        antecedentSorted _ _ _ limit antecedentBound leftBody rightBody bodyProof
  | @lam domain gamma result body ih | @all domain gamma body ih | @ex domain gamma body ih =>
      intro left right depth antecedent antecedentSorted leftSorted rightSorted slots independent variableEquality constantProof
        limit baseBound constantBound leftBound rightBound antecedentBound bindersBound variableBound constantsBound
      have head : context[binders depth]? = some (.bound signature.ids.object) := by
        simpa only [Nat.add_zero] using slots 0 (Nat.zero_lt_succ _)
      have bodySlots : ∀ offset < body.binderDepth,
          context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
        intro offset smaller
        have found := slots (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have domainSorted := encodeType_sorted signature context base baseSorted domain
      have boundSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
        .var (binder := .bound signature.ids.object) head
      let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
      have extraSorted := hasType_sorted signature context boundSorted domainSorted
      let extended := conjunction signature.symbol antecedent extra
      have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
      have extendedIndependent : ∀ offset < body.binderDepth,
          ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
        intro offset smaller
        apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
        · intro same
          have impossible := bindersInjective same
          omega
        · simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent (offset + 1) (Nat.add_lt_add_right smaller 1)
        · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
      let extendedEqualities : ∀ {type} (index : Var (domain :: gamma) type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (entails signature.symbol extended (holds signature.symbol
              (equality signature.symbol (encodeType signature.symbol base type)
                (Assignment.extend (.var (binders depth)) left index)
                (Assignment.extend (.var (binders depth)) right index)))) := by
        intro type index
        cases index with
        | vz =>
            exact HOLKernelInferenceProofs.Native.reflexivity signature rules extended _ _ extendedSorted
              domainSorted boundSorted
              (HOLKernelStructuralRules.right signature structural _ _ antecedentSorted extraSorted)
        | vs index =>
            apply HOLKernelStructuralRules.weaken signature structural antecedent extra _
              antecedentSorted extraSorted _ (variableEquality index)
            exact holds_sorted signature context (signature.application context .eqc _
              (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil))))
      let extendedConstants : ∀ {type} (symbol : Const type),
          CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
            (context := context) (hypotheses := hypotheses)
            (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
        HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
          antecedentSorted extraSorted baseSorted constantSorted constantProof
      have extendedLeftSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) left index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context (.var (binders depth)) left boundSorted leftSorted
      have extendedRightSorted : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.HasType terms context (Assignment.extend (.var (binders depth)) right index)
            [] signature.ids.object :=
        Assignment.extend_sorted signature context (.var (binders depth)) right boundSorted rightSorted
      let bodyProof := congruence signature profile structural typing rules binding base constant binders
        baseSorted constantSorted bindersInjective baseIndependent body
        (Assignment.extend (.var (binders depth)) left) (Assignment.extend (.var (binders depth)) right)
        (depth + 1) extended extendedSorted extendedLeftSorted extendedRightSorted bodySlots
        extendedIndependent extendedEqualities extendedConstants
      have leftBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
        body _ (depth + 1) extendedLeftSorted bodySlots
      have rightBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted
        body _ (depth + 1) extendedRightSorted bodySlots
      let abstractionEquality := HOLKernelBindingProofs.Native.abstractionCongruence signature binding
        antecedent (encodeType signature.symbol base domain) _ (binders depth) _ _ antecedentSorted domainSorted
        (encodeType_sorted signature context base baseSorted _) head leftBodySorted rightBodySorted
        (by simpa only [Nat.add_zero] using independent 0 (Nat.zero_lt_succ _))
        (encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
        (encodeType_independent context _ signature.symbol base (baseIndependent _) _) bodyProof

      have rootBound : binders depth < limit := by
        simpa only [Nat.add_zero] using bindersBound 0 (Nat.zero_lt_succ _)
      have domainBound := encodeType_varsBelow signature.symbol base limit baseBound domain
      have extraBound : Preterm.VarsBelow limit extra := ⟨⟨trivial, rootBound⟩, domainBound⟩
      have extendedBound : Preterm.VarsBelow limit extended := ⟨⟨trivial, antecedentBound⟩, extraBound⟩
      have extendedLeftBound : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.VarsBelow limit (Assignment.extend (.var (binders depth)) left index) :=
        Assignment.extend_varsBelow limit (.var (binders depth)) left rootBound leftBound
      have extendedRightBound : ∀ {type} (index : Var (domain :: gamma) type),
          Preterm.VarsBelow limit (Assignment.extend (.var (binders depth)) right index) :=
        Assignment.extend_varsBelow limit (.var (binders depth)) right rootBound rightBound
      have bodyNames : ∀ offset < body.binderDepth, binders (depth + 1 + offset) < limit := by
        intro offset smaller
        have found := bindersBound (offset + 1) (Nat.add_lt_add_right smaller 1)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
      have leftBodyBound := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body
        (Assignment.extend (.var (binders depth)) left) (depth + 1) extendedLeftBound bodyNames
      have rightBodyBound := encode_varsBelow signature.symbol base constant binders limit baseBound constantBound body
        (Assignment.extend (.var (binders depth)) right) (depth + 1) extendedRightBound bodyNames
      have extendedEqualitiesBound : ∀ {type} (index : Var (domain :: gamma) type),
          (extendedEqualities index).val.VarsBelow limit := by
        intro type index
        cases index with
        | vz =>
            change ProofWitness.VarsBelow limit (.theoremApp _ _ [.theoremApp _ _ []])
            simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false,
              forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, and_true] using
              And.intro ⟨extendedBound, domainBound, rootBound⟩ ⟨antecedentBound, extraBound⟩
        | vs index =>
            exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
              antecedentSorted extraSorted
              (holds_sorted signature context (signature.application context .eqc _
                (.cons (.regular (encodeType_sorted signature context base baseSorted type))
                  (.cons (.regular (leftSorted index)) (.cons (.regular (rightSorted index)) .nil)))))
              (variableEquality index) antecedentBound extraBound
              ⟨trivial, ⟨⟨⟨trivial, encodeType_varsBelow _ _ _ baseBound type⟩, leftBound index⟩, rightBound index⟩⟩
              (variableBound index)
      have extendedConstantsBound : ∀ {type} (symbol : Const type),
          (extendedConstants symbol).val.VarsBelow limit := by
        intro type symbol
        exact HOLKernelStructuralRules.weaken_varsBelow signature structural limit antecedent extra _
          antecedentSorted extraSorted
          (hasType_sorted signature context (constantSorted symbol) (encodeType_sorted signature context base baseSorted type))
          (constantProof symbol) antecedentBound extraBound
          ⟨⟨trivial, constantBound symbol⟩, encodeType_varsBelow _ _ _ baseBound type⟩ (constantsBound symbol)
      have bodyProofBound := ih _ _ _ _ extendedSorted extendedLeftSorted extendedRightSorted bodySlots
        extendedIndependent extendedEqualities extendedConstants limit baseBound constantBound
        extendedLeftBound extendedRightBound extendedBound bodyNames extendedEqualitiesBound extendedConstantsBound
      have abstractionBound : abstractionEquality.val.VarsBelow limit := by
        change ProofWitness.VarsBelow limit (.theoremApp _ _ [bodyProof.val])
        simpa only [ProofWitness.VarsBelow, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro ⟨antecedentBound, domainBound, encodeType_varsBelow _ _ _ baseBound _, rootBound, leftBodyBound, rightBodyBound⟩ bodyProofBound
      simp only [congruence]
      first
      | exact abstractionBound
      | exact HOLKernelCongruence.universalCongruence_varsBelow signature profile rules _ _ _ _ _ _
          antecedentSorted domainSorted head head leftBodySorted rightBodySorted abstractionEquality limit
          antecedentBound domainBound leftBodyBound rightBodyBound rootBound rootBound abstractionBound
      | exact HOLKernelCongruence.existentialCongruence_varsBelow signature profile rules _ _ _ _ _ _
          antecedentSorted domainSorted head head leftBodySorted rightBodySorted abstractionEquality limit
          antecedentBound domainBound leftBodyBound rightBodyBound rootBound rootBound abstractionBound

#print axioms congruence_varsBelow

end Mettapedia.Languages.MM0.HOLKernelTermCongruence

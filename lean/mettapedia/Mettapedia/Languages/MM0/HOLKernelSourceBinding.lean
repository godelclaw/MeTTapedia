import Mettapedia.Languages.MM0.HOLKernelAlpha

/-!
# Canonical source conclusions for HOL binder inference

Translated body proofs close under the maintained GEN, leq and CHOOSE rules at a
fresh native variable. Outer alpha equations are constructed in the formation
context, then transported to the logical context to restore the source
encoding. Internal source names may occur in retained logical assumptions.

The finite windows record actual slots, occurrence independence and
disjointness. The constructions consume the translated local body premises;
assembling them recursively from all retained source proofs is separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSourceBinding
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelTypingRules (typed boolType functionType)
open HOLKernelInferenceRules (equality)
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
variable {equivalenceReference : Nat}

structure RebindingWindows (context : Context) (object : Nat) (formation : Preterm)
    (binders temporary : Nat → Nat) where
  width : Nat
  sourceDepth : Nat
  workDepth : Nat
  temporaryDepth : Nat
  sourceSlots : ∀ offset < width, context[binders (sourceDepth + offset)]? = some (.bound object)
  workSlots : ∀ offset < width, context[binders (workDepth + offset)]? = some (.bound object)
  temporarySlots : ∀ offset < width, context[temporary (temporaryDepth + offset)]? = some (.bound object)
  sourceFresh : ∀ offset < width, ¬ Preterm.HasVar context (binders (sourceDepth + offset)) formation
  workFresh : ∀ offset < width, ¬ Preterm.HasVar context (binders (workDepth + offset)) formation
  temporaryFresh : ∀ offset < width, ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) formation
  sourceDisjoint : ∀ first < width, ∀ second < width,
    binders (sourceDepth + first) ≠ temporary (temporaryDepth + second)
  workDisjoint : ∀ first < width, ∀ second < width,
    binders (workDepth + first) ≠ temporary (temporaryDepth + second)

def RebindingWindows.bodyWindow {object : Nat} {formation : Preterm} {binders temporary : Nat → Nat}
    (windows : RebindingWindows context object formation binders temporary) (size : Nat)
    (fits : size + 1 ≤ windows.width) : RebindingWindows context object formation binders temporary := by
  let inner : RebindingWindows context object formation binders temporary := {
    width := size, sourceDepth := windows.sourceDepth, workDepth := windows.workDepth + 1,
    temporaryDepth := windows.temporaryDepth
    sourceSlots := fun offset smaller => windows.sourceSlots offset (by omega)
    workSlots := by
      intro offset smaller
      have found := windows.workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    temporarySlots := fun offset smaller => windows.temporarySlots offset (by omega)
    sourceFresh := fun offset smaller => windows.sourceFresh offset (by omega)
    workFresh := by
      intro offset smaller
      have found := windows.workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
    temporaryFresh := fun offset smaller => windows.temporaryFresh offset (by omega)
    sourceDisjoint := fun first firstSmaller second secondSmaller => windows.sourceDisjoint first (by omega) second (by omega)
    workDisjoint := by
      intro first firstSmaller second secondSmaller
      have found := windows.workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using found }
  exact inner

def rebindInContext (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {type : Ty Base} (source : Term Const gamma type) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : source.binderDepth ≤ windows.width)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base type)
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth source)
        (encodeWithAssignment signature.symbol base constant binders assignment windows.workDepth source)))) := by
  let equation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent source assignment
    windows.sourceDepth windows.workDepth windows.temporaryDepth scope.formation scope.formationSorted assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset smaller => windows.temporarySlots offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset smaller => windows.sourceFresh offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset smaller => windows.workFresh offset (Nat.lt_of_lt_of_le smaller fits))
    (fun offset smaller => windows.temporaryFresh offset (Nat.lt_of_lt_of_le smaller fits))
    (fun first firstSmall second secondSmall => windows.sourceDisjoint first (Nat.lt_of_lt_of_le firstSmall fits)
      second (Nat.lt_of_lt_of_le secondSmall fits))
    (fun first firstSmall second secondSmall => Ne.symm (windows.workDisjoint second (Nat.lt_of_lt_of_le secondSmall fits)
      first (Nat.lt_of_lt_of_le firstSmall fits))) variableTyping constantTyping
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted source assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller fits))
  have workSorted := encode_sorted signature context base constant binders baseSorted constantSorted source assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller fits))
  exact scope.promote signature structural _ (holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular (encodeType_sorted signature context base baseSorted type))
      (.cons (.regular sourceSorted) (.cons (.regular workSorted) .nil))))) equation

def universalIntroduction (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base} (body : Term Const (domain :: gamma) .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : body.binderDepth + 1 ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol scope.logical
        (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth (.all body)))) := by
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body _ (windows.workDepth + 1)
    extendedSorted (by
      intro offset smaller
      have found := windows.workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
  let workProof := HOLKernelBindingProofs.Native.universalIntroduction signature binding scope.logical _
    (binders windows.workDepth) _ scope.logicalSorted domainSorted head bodySorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain) bodyProof
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.all body) assignment
    scope windows fits assignmentSorted variableTyping constantTyping
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller fits))
  have workSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller fits))
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    (signature.application context .bool [] .nil) scope.logicalSorted sourceSorted workSorted equation
  exact HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules scope.logical _ _ scope.logicalSorted
    workSorted sourceSorted reversed workProof

def abstractionCongruence (signature : Signature sorts terms)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain result : Ty Base} (first second : Term Const (domain :: gamma) result) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : max first.binderDepth second.binderDepth + 1 ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol scope.logical
        (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base result)
          (encodeWithAssignment signature.symbol base constant binders
            (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) first)
          (encodeWithAssignment signature.symbol base constant binders
            (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) second))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base (.arr domain result))
          (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth (.lam first))
          (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth (.lam second))))) := by
  have firstFits : (Term.lam first).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have secondFits : (Term.lam second).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have resultSorted := encodeType_sorted signature context base baseSorted result
  have functionSorted := encodeType_sorted signature context base baseSorted (.arr domain result)
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySlots : ∀ offset < max first.binderDepth second.binderDepth,
      context[binders (windows.workDepth + 1 + offset)]? = some (.bound signature.ids.object) := by
    intro offset smaller
    have found := windows.workSlots (offset + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
  have firstBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted first _ (windows.workDepth + 1)
    extendedSorted (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_left _ _)))
  have secondBodySorted := encode_sorted signature context base constant binders baseSorted constantSorted second _ (windows.workDepth + 1)
    extendedSorted (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller (Nat.le_max_right _ _)))
  let workProof := HOLKernelBindingProofs.Native.abstractionCongruence signature binding scope.logical _ _
    (binders windows.workDepth) _ _ scope.logicalSorted domainSorted resultSorted head firstBodySorted secondBodySorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) result) bodyProof
  let firstEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam first) assignment
    scope windows firstFits assignmentSorted variableTyping constantTyping
  let secondEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam second) assignment
    scope windows secondFits assignmentSorted variableTyping constantTyping
  have firstSourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam first) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller firstFits))
  have firstWorkSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam first) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller firstFits))
  have secondSourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam second) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller secondFits))
  have secondWorkSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam second) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller secondFits))
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules _ scope.logical _ _
    functionSorted scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
  let middle := HOLKernelInferenceProofs.Native.transitivity signature rules scope.logical _ _ _ _ scope.logicalSorted
    functionSorted firstSourceSorted firstWorkSorted secondWorkSorted firstEquation workProof
  exact HOLKernelInferenceProofs.Native.transitivity signature rules scope.logical _ _ _ _ scope.logicalSorted
    functionSorted firstSourceSorted secondWorkSorted secondSourceSorted middle reversed

def weakenAssumption (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base} (formula : Term Const gamma .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : formula.binderDepth + 1 ≤ windows.width)
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth formula)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol scope.logical
        (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
          (weaken (σ := domain) formula)))) := by
  let inner := windows.bodyWindow formula.binderDepth fits
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent formula assignment
    scope inner (Nat.le_refl _) assignmentSorted variableTyping constantTyping
  have sourceSorted := encode_sorted signature context base constant binders baseSorted constantSorted formula assignment
    inner.sourceDepth assignmentSorted inner.sourceSlots
  have childSorted := encode_sorted signature context base constant binders baseSorted constantSorted formula assignment
    inner.workDepth assignmentSorted inner.workSlots
  let carried := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules scope.logical _ _ scope.logicalSorted
    sourceSorted childSorted equation premise
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extraSorted := hasType_sorted signature context headSorted (encodeType_sorted signature context base baseSorted domain)
  have coherence := encode_rename (delta := domain :: gamma) signature.symbol base constant binders formula
    (fun {_} index => Var.vs index) (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
  change encodeWithAssignment signature.symbol base constant binders
      (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) (weaken (σ := domain) formula) =
    encodeWithAssignment signature.symbol base constant binders assignment (windows.workDepth + 1) formula at coherence
  rw [coherence]
  exact HOLKernelStructuralRules.weaken signature structural scope.logical _ _ scope.logicalSorted extraSorted
    (holds_sorted signature context childSorted) carried

def existentialElimination (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm) (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type), Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base} (body : Term Const (domain :: gamma) .prop) (result : Term Const gamma .prop) (assignment : Assignment gamma)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses signature.symbol signature.ids.wff)
    (windows : RebindingWindows context signature.ids.object scope.formation binders temporary)
    (fits : max (body.binderDepth + 1) (result.binderDepth + 1) ≤ windows.width)
    (logicalFresh : ¬ Preterm.HasVar context (binders windows.workDepth) scope.logical)
    (variableIndependent : ∀ {type} (index : Var gamma type),
      ¬ Preterm.HasVar context (binders windows.workDepth) (assignment index))
    (constantIndependent : ∀ {type} (symbol : Const type),
      ¬ Preterm.HasVar context (binders windows.workDepth) (constant symbol))
    (resultNamesApart : ∀ offset < result.binderDepth,
      binders windows.workDepth ≠ binders (windows.sourceDepth + offset))
    (assignmentSorted : ∀ {type} (index : Var gamma type), Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (existsProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth (.ex body)))))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol (conjunction signature.symbol
        (conjunction signature.symbol scope.logical
          (hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body)))
        (holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
          (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
          (weaken (σ := domain) result))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems) (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth result))) := by
  have bodyFits : (Term.ex body).binderDepth ≤ windows.width := by simp only [Term.binderDepth]; omega
  have resultFits : result.binderDepth ≤ windows.width := by omega
  have head : context[binders windows.workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using windows.workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have headSorted : Preterm.HasType terms context (.var (binders windows.workDepth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  have extendedSorted : ∀ {type} (index : Var (domain :: gamma) type), Preterm.HasType terms context
      (Assignment.extend (.var (binders windows.workDepth)) assignment index) [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have bodySorted := encode_sorted signature context base constant binders baseSorted constantSorted body _ (windows.workDepth + 1)
    extendedSorted (by
      intro offset smaller
      have found := windows.workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
  have resultSorted := encode_sorted signature context base constant binders baseSorted constantSorted result assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits))
  have resultIndependent : ¬ Preterm.HasVar context (binders windows.workDepth)
      (encodeWithAssignment signature.symbol base constant binders assignment windows.sourceDepth result) := by
    apply encode_independent context (binders windows.workDepth) signature.symbol base constant binders
      (baseIndependent windows.workDepth) constantIndependent result assignment windows.sourceDepth variableIndependent
    intro offset smaller
    exact HOLKernelTypeSupport.boundVariable_independent context _ _ signature.ids.object
      (windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits)) (resultNamesApart offset smaller)
  let formationTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent result assignment windows.sourceDepth scope.formation scope.formationSorted
    assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller resultFits))
    (fun offset smaller => windows.sourceFresh offset (Nat.lt_of_lt_of_le smaller resultFits)) variableTyping constantTyping
  let resultTyping := scope.promote signature structural _
    (hasType_sorted signature context resultSorted (signature.application context .bool [] .nil)) formationTyping
  let equation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.ex body) assignment
    scope windows bodyFits assignmentSorted variableTyping constantTyping
  have sourceExistsSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body) assignment
    windows.sourceDepth assignmentSorted (fun offset smaller => windows.sourceSlots offset (Nat.lt_of_lt_of_le smaller bodyFits))
  have workExistsSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body) assignment
    windows.workDepth assignmentSorted (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller bodyFits))
  let workExists := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules scope.logical _ _ scope.logicalSorted
    sourceExistsSorted workExistsSorted equation existsProof
  let typeExtra := hasType signature.symbol (.var (binders windows.workDepth)) (encodeType signature.symbol base domain)
  have typeExtraSorted := hasType_sorted signature context headSorted domainSorted
  let bodyExtra := holds signature.symbol (encodeWithAssignment signature.symbol base constant binders
    (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) body)
  have bodyExtraSorted := holds_sorted signature context bodySorted
  let childScope := (scope.under signature structural typeExtra typeExtraSorted).under signature structural bodyExtra bodyExtraSorted
  let childWindows := windows.bodyWindow result.binderDepth (by omega)
  let resultEquation := rebindInContext signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent result assignment
    childScope childWindows (Nat.le_refl _) assignmentSorted variableTyping constantTyping
  have childResultSorted := encode_sorted signature context base constant binders baseSorted constantSorted result assignment
    childWindows.workDepth assignmentSorted childWindows.workSlots
  have coherence := encode_rename (delta := domain :: gamma) signature.symbol base constant binders result
    (fun {_} index => Var.vs index) (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1)
  change encodeWithAssignment signature.symbol base constant binders
      (Assignment.extend (.var (binders windows.workDepth)) assignment) (windows.workDepth + 1) (weaken (σ := domain) result) =
    encodeWithAssignment signature.symbol base constant binders assignment (windows.workDepth + 1) result at coherence
  rw [coherence] at bodyProof
  let reversed := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) childScope.logical _ _
    (signature.application context .bool [] .nil) childScope.logicalSorted resultSorted childResultSorted resultEquation
  let parentConclusion := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules childScope.logical _ _
    childScope.logicalSorted childResultSorted resultSorted reversed bodyProof
  exact HOLKernelBindingProofs.Native.existentialElimination signature binding scope.logical _ (binders windows.workDepth) _ _
    scope.logicalSorted domainSorted head bodySorted resultSorted logicalFresh
    (HOLKernelTypeSupport.encodeType_independent context _ signature.symbol base (baseIndependent _) domain)
    resultIndependent resultTyping workExists parentConclusion

#print axioms RebindingWindows.bodyWindow
#print axioms rebindInContext
#print axioms universalIntroduction
#print axioms weakenAssumption
#print axioms abstractionCongruence
#print axioms existentialElimination
end Mettapedia.Languages.MM0.HOLKernelSourceBinding

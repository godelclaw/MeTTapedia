import Mettapedia.Languages.MM0.HOLKernelSubstitution
import Mettapedia.Languages.MM0.HOLKernelQuantifierProofs

/-!
# Source-derived beta and quantifier instantiation

The constructions take actual source argument and body terms. One shared
instance derivation builds
the body typing, instantiated-result typing and equation under the maintained
rule's equality assumption. Argument readback is an explicit checked equation
in the preceding context. The result uses the specified fresh body window;
outer alpha transport can restore another result encoding after beta discharges
the equality context. Universal elimination and existential introduction reuse
the constructed instance equation, with checked Boolean-definition conversion.
The canonical constructions compose the outer alpha steps and derive exact
source-encoded beta and quantifier conclusions.

The canonical quantifier rules distinguish formation from logical antecedents.
Typing and equality are constructed in the formation antecedent and transported
along a checked context projection. Only the fresh native quantifier variable
must be absent from the logical antecedent; internal canonical names may occur
in its retained assumptions.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSourceInstantiation
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

structure InstancePremises (signature : Signature sorts terms)
    (definitions : Definition.Signature) (theorems : TheoremSignature) (context : Context)
    (hypotheses : List Preterm) (antecedent domain resultType argument body result : Preterm)
    (boundIndex : Nat) where
  bodySorted : Preterm.HasType terms context body [] signature.ids.object
  resultSorted : Preterm.HasType terms context result [] signature.ids.object
  bodyTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses)
    (typed signature.symbol (conjunction signature.symbol antecedent
      (hasType signature.symbol (.var boundIndex) domain)) body resultType)
  resultTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent result resultType)
  equation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses)
    (entails signature.symbol (conjunction signature.symbol antecedent
      (holds signature.symbol (equality signature.symbol domain (.var boundIndex) argument)))
      (holds signature.symbol (equality signature.symbol resultType body result)))

private def promoteTyping (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff) (term type : Preterm)
    (termSorted : Preterm.HasType terms context term [] signature.ids.object)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (proof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol scope.formation term type)) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses) (typed signature.symbol scope.logical term type) :=
  scope.promote signature structural _ (hasType_sorted signature context termSorted typeSorted) proof

private theorem equalitySorted (signature : Signature sorts terms) (type first second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object) :
    Preterm.HasType terms context (holds signature.symbol (equality signature.symbol type first second))
      [] signature.ids.wff :=
  holds_sorted signature context (signature.application context .eqc _
    (.cons (.regular typeSorted) (.cons (.regular firstSorted) (.cons (.regular secondSorted) .nil))))

private def promoteEquality (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff) (type first second : Preterm)
    (typeSorted : Preterm.HasType terms context type [] signature.ids.type)
    (firstSorted : Preterm.HasType terms context first [] signature.ids.object)
    (secondSorted : Preterm.HasType terms context second [] signature.ids.object)
    (proof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.formation (holds signature.symbol (equality signature.symbol type first second)))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol (equality signature.symbol type first second))) :=
  scope.promote signature structural _ (equalitySorted signature type first second typeSorted firstSorted secondSorted) proof

def InstancePremises.promote (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff) (domain resultType argument body result : Preterm) (boundIndex : Nat)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultTypeSorted : Preterm.HasType terms context resultType [] signature.ids.type)
    (argumentSorted : Preterm.HasType terms context argument [] signature.ids.object)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (source : InstancePremises signature definitions theorems context hypotheses scope.formation
      domain resultType argument body result boundIndex) :
    InstancePremises signature definitions theorems context hypotheses scope.logical
      domain resultType argument body result boundIndex := by
  have boundSorted : Preterm.HasType terms context (.var boundIndex) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) bound
  exact ⟨source.bodySorted, source.resultSorted,
    scope.promoteUnder signature structural _ _ (hasType_sorted signature context boundSorted domainSorted)
      (hasType_sorted signature context source.bodySorted resultTypeSorted) source.bodyTyping,
    promoteTyping signature structural scope result resultType source.resultSorted resultTypeSorted source.resultTyping,
    scope.promoteUnder signature structural _ _
      (equalitySorted signature domain (.var boundIndex) argument domainSorted boundSorted argumentSorted)
      (equalitySorted signature resultType body result resultTypeSorted source.bodySorted source.resultSorted)
      source.equation⟩

def deriveInstance (signature : Signature sorts terms)
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
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument))))) :
    InstancePremises signature definitions theorems context hypotheses antecedent
      (encodeType signature.symbol base domain) (encodeType signature.symbol base result) argumentCode
      (encodeWithAssignment signature.symbol base constant binders
        (Assignment.extend (.var (binders depth)) assignment) (depth + 1) body)
      (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1)
        (instantiate argument body)) (binders depth) := by
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    have found := slots 0 (by omega)
    simpa only [Nat.add_zero] using found
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have resultSorted := encodeType_sorted signature context base baseSorted result
  have headSorted : Preterm.HasType terms context (.var (binders depth)) [] signature.ids.object :=
    .var (binder := .bound signature.ids.object) head
  let extra := hasType signature.symbol (.var (binders depth)) (encodeType signature.symbol base domain)
  let extended := conjunction signature.symbol antecedent extra
  have extraSorted := hasType_sorted signature context headSorted domainSorted
  have extendedSorted := conjunction_sorted signature context antecedentSorted extraSorted
  have bodySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[binders (depth + 1 + offset)]? = some (.bound signature.ids.object) := by
    intro offset smaller
    have found := slots (offset + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found
  have bodyFresh : ∀ offset < body.binderDepth,
      ¬ Preterm.HasVar context (binders (depth + 1 + offset)) extended := by
    intro offset smaller
    apply contextExtension_independent context _ _ signature.ids.object signature.symbol _ _ head
    · intro same
      have impossible := bindersInjective same
      omega
    · have independent := fresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent
    · exact encodeType_independent context _ signature.symbol base (baseIndependent _) domain
  have extendedAssignmentSorted : ∀ {type} (index : Var (domain :: gamma) type),
      Preterm.HasType terms context (Assignment.extend (.var (binders depth)) assignment index)
        [] signature.ids.object :=
    Assignment.extend_sorted signature context _ assignment headSorted assignmentSorted
  have extendedVariables : ∀ {type} (index : Var (domain :: gamma) type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol extended (Assignment.extend (.var (binders depth)) assignment index)
          (encodeType signature.symbol base type)) := by
    intro type index
    cases index with
    | vz => exact HOLKernelStructuralRules.right signature structural antecedent extra antecedentSorted extraSorted
    | vs index =>
        exact (HOLKernelTermTyping.weakenVariables signature structural base assignment antecedent extra
          antecedentSorted extraSorted baseSorted assignmentSorted variableTyping) index
  have extendedConstants : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol extended (constant symbol) (encodeType signature.symbol base type)) :=
    HOLKernelTermTyping.weakenConstants signature structural base constant antecedent extra
      antecedentSorted extraSorted baseSorted constantSorted constantTyping
  let bodyTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent body
    (Assignment.extend (.var (binders depth)) assignment) (depth + 1) extended extendedSorted
    extendedAssignmentSorted (fun offset smaller => bodySlots offset (by omega)) bodyFresh extendedVariables extendedConstants
  have instanceDepth := Term.binderDepth_subst_le body (Subst.single argument)
  let resultTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent (instantiate argument body)
    assignment (depth + 1) antecedent antecedentSorted assignmentSorted
    (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller instanceDepth))
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have independent := fresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    variableTyping constantTyping
  let equation := HOLKernelSubstitution.instanceEquation signature profile structural typing rules binding
    base constant binders temporary baseSorted constantSorted bindersInjective temporaryInjective
    baseIndependent temporaryIndependent argument body assignment (depth + 1) temporaryDepth (binders depth)
    antecedent argumentCode antecedentSorted argumentSorted head assignmentSorted bodySlots temporarySlots
    equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  exact ⟨
    encode_sorted signature context base constant binders baseSorted constantSorted body _ (depth + 1)
      extendedAssignmentSorted (fun offset smaller => bodySlots offset (by omega)),
    encode_sorted signature context base constant binders baseSorted constantSorted (instantiate argument body)
      assignment (depth + 1) assignmentSorted
      (fun offset smaller => bodySlots offset (Nat.lt_of_lt_of_le smaller instanceDepth)),
    bodyTyping, resultTyping, equation⟩

def beta (signature : Signature sorts terms)
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
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base result)
          (applySymbol signature.symbol .app
            [encodeWithAssignment signature.symbol base constant binders assignment depth (.lam body), argumentCode])
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1)
            (instantiate argument body))))) := by
  let derived := deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  exact HOLKernelBindingProofs.Native.beta signature binding antecedent _ _ (binders depth) argumentCode _ _
    antecedentSorted (encodeType_sorted signature context base baseSorted domain)
    (encodeType_sorted signature context base baseSorted result) head argumentSorted
    derived.bodySorted derived.resultSorted
    (by simpa only [Nat.add_zero] using fresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) result)
    derived.bodyTyping argumentTyping derived.resultTyping derived.equation

def universalElimination (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment depth (.all body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1)
          (instantiate argument body)))) := by
  let derived := deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  exact HOLKernelQuantifierProofs.universalElimination signature abbreviation binding
    antecedent _ argumentCode _ _ (binders depth) antecedentSorted
    (encodeType_sorted signature context base baseSorted domain) head argumentSorted
    derived.bodySorted derived.resultSorted
    (by simpa only [Nat.add_zero] using fresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
    argumentTyping derived.resultTyping derived.equation universal

def existentialIntroduction (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (depth temporaryDepth : Nat)
    (antecedent argumentCode : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (argumentSorted : Preterm.HasType terms context argumentCode [] signature.ids.object)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (slots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (depth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (fresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (depth + offset)) antecedent)
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (depth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders depth)) argumentCode))))
    (disjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
        binders (depth + 1 + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type)))
    (argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (typed signature.symbol antecedent argumentCode (encodeType signature.symbol base domain)))
    (argumentEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (equality signature.symbol (encodeType signature.symbol base domain) argumentCode
          (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1) argument)))))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment (depth + 1)
          (instantiate argument body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol antecedent (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment depth (.ex body)))) := by
  let derived := deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment depth temporaryDepth antecedent argumentCode antecedentSorted argumentSorted assignmentSorted
    slots temporarySlots fresh equationFresh temporaryFresh disjoint variableTyping constantTyping argumentEquation
  have head : context[binders depth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using slots 0 (by omega)
  exact HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation binding
    antecedent _ argumentCode _ _ (binders depth) antecedentSorted
    (encodeType_sorted signature context base baseSorted domain) head argumentSorted
    derived.bodySorted derived.resultSorted
    (by simpa only [Nat.add_zero] using fresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent depth) domain)
    derived.bodyTyping argumentTyping derived.equation instanceProof

structure CanonicalInstancePremises (signature : Signature sorts terms)
    (definitions : Definition.Signature) (theorems : TheoremSignature) (context : Context)
    (hypotheses : List Preterm) (antecedent domain resultType argument sourceResult body workResult : Preterm)
    (boundIndex : Nat) where
  argumentSorted : Preterm.HasType terms context argument [] signature.ids.object
  sourceResultSorted : Preterm.HasType terms context sourceResult [] signature.ids.object
  argumentTyping : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses) (typed signature.symbol antecedent argument domain)
  native : InstancePremises signature definitions theorems context hypotheses antecedent
    domain resultType argument body workResult boundIndex
  resultEquation : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
    (context := context) (hypotheses := hypotheses)
    (entails signature.symbol antecedent (holds signature.symbol
      (equality signature.symbol resultType workResult sourceResult)))

def CanonicalInstancePremises.promote (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff)
    (domain resultType argument sourceResult body workResult : Preterm) (boundIndex : Nat)
    (domainSorted : Preterm.HasType terms context domain [] signature.ids.type)
    (resultTypeSorted : Preterm.HasType terms context resultType [] signature.ids.type)
    (bound : context[boundIndex]? = some (.bound signature.ids.object))
    (source : CanonicalInstancePremises signature definitions theorems context hypotheses scope.formation
      domain resultType argument sourceResult body workResult boundIndex) :
    CanonicalInstancePremises signature definitions theorems context hypotheses scope.logical
      domain resultType argument sourceResult body workResult boundIndex :=
  ⟨source.argumentSorted, source.sourceResultSorted,
    promoteTyping signature structural scope argument domain source.argumentSorted domainSorted source.argumentTyping,
    source.native.promote signature structural scope domain resultType argument body workResult boundIndex
      domainSorted resultTypeSorted source.argumentSorted bound,
    promoteEquality signature structural scope resultType workResult sourceResult resultTypeSorted
      source.native.resultSorted source.sourceResultSorted source.resultEquation⟩

def deriveCanonicalInstance (signature : Signature sorts terms)
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
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol antecedent (constant symbol) (encodeType signature.symbol base type))) :
    CanonicalInstancePremises signature definitions theorems context hypotheses antecedent
      (encodeType signature.symbol base domain) (encodeType signature.symbol base result)
      (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)
      (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (instantiate argument body))
      (encodeWithAssignment signature.symbol base constant binders
        (Assignment.extend (.var (binders workDepth)) assignment) (workDepth + 1) body)
      (encodeWithAssignment signature.symbol base constant binders assignment (workDepth + 1) (instantiate argument body))
      (binders workDepth) := by
  have imageHeight : argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) :=
    Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have argumentSorted := encode_sorted signature context base constant binders baseSorted constantSorted argument
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
  let argumentTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing base constant binders
    baseSorted constantSorted bindersInjective baseIndependent argument assignment sourceDepth antecedent
    antecedentSorted assignmentSorted (fun offset smaller => sourceSlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega)) variableTyping constantTyping
  let argumentEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument
    assignment sourceDepth (workDepth + 1) temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by omega))
    (by
      intro offset smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (fun offset smaller => temporarySlots offset (by omega))
    (fun offset smaller => sourceFresh offset (by omega))
    (by
      intro offset smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (fun offset smaller => temporaryFresh offset (by omega))
    (by intro first firstSmaller second secondSmaller; exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      have apart := Ne.symm (workDisjoint (second + 1) (by omega) first (by omega))
      simpa only [Nat.add_assoc, Nat.add_comm 1 second] using apart)
    variableTyping constantTyping
  let derived := deriveInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment workDepth temporaryDepth antecedent
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)
    antecedentSorted argumentSorted assignmentSorted workSlots
    (fun offset smaller => temporarySlots offset (by omega)) workFresh equationFresh equationTemporaryFresh
    (by
      intro first firstSmaller second secondSmaller
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    variableTyping constantTyping argumentEquation
  let after := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent
    (instantiate argument body) assignment (workDepth + 1) sourceDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have found := workSlots (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using found)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceSlots offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporarySlots offset (by omega))
    (by
      intro offset smaller
      simp only [instantiate] at smaller
      have independent := workFresh (offset + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using independent)
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceFresh offset (by omega))
    (by intro offset smaller; simp only [instantiate] at smaller; exact temporaryFresh offset (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      have apart := workDisjoint (first + 1) (by omega) second (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using apart)
    (by
      intro first firstSmaller second secondSmaller
      simp only [instantiate] at firstSmaller secondSmaller
      exact Ne.symm (sourceDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceResultSorted := encode_sorted signature context base constant binders baseSorted constantSorted
    (instantiate argument body) assignment sourceDepth assignmentSorted
    (by intro offset smaller; simp only [instantiate] at smaller; exact sourceSlots offset (by omega))
  exact ⟨argumentSorted, sourceResultSorted, argumentTyping, derived, after⟩

def canonicalBeta (signature : Signature sorts terms)
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
    {gamma : Ctx Base} {domain result : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat) (antecedent : Preterm)
    (antecedentSorted : Preterm.HasType terms context antecedent [] signature.ids.wff)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) antecedent)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) antecedent)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) antecedent)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol antecedent
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
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
        (equality signature.symbol (encodeType signature.symbol base result)
          (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (.app (.lam body) argument))
          (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (instantiate argument body))))) := by
  let prepared := deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let lambdaEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.lam body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceLambdaSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workLambdaSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.lam body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  let before := HOLKernelInferenceProofs.Native.applicationFunction signature rules
    (encodeType signature.symbol base domain) (encodeType signature.symbol base result) antecedent
    (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument) _ _
    (encodeType_sorted signature context base baseSorted domain) (encodeType_sorted signature context base baseSorted result)
    antecedentSorted prepared.argumentSorted sourceLambdaSorted workLambdaSorted lambdaEquation prepared.argumentTyping
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  let reduction := HOLKernelBindingProofs.Native.beta signature binding antecedent _ _ (binders workDepth) _ _ _
    antecedentSorted (encodeType_sorted signature context base baseSorted domain)
    (encodeType_sorted signature context base baseSorted result) head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted
    (by simpa only [Nat.add_zero] using workFresh 0 (by omega))
    (encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain)
    (encodeType_independent context _ signature.symbol base (baseIndependent workDepth) result)
    prepared.native.bodyTyping prepared.argumentTyping prepared.native.resultTyping prepared.native.equation
  have sourceApplicationSorted := signature.application context .app _
    (.cons (.regular sourceLambdaSorted) (.cons (.regular prepared.argumentSorted) .nil))
  have workApplicationSorted := signature.application context .app _
    (.cons (.regular workLambdaSorted) (.cons (.regular prepared.argumentSorted) .nil))
  let middle := HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted
    (encodeType_sorted signature context base baseSorted result) sourceApplicationSorted workApplicationSorted
    prepared.native.resultSorted before reduction
  exact HOLKernelInferenceProofs.Native.transitivity signature rules antecedent _ _ _ _ antecedentSorted
    (encodeType_sorted signature context base baseSorted result) sourceApplicationSorted prepared.native.resultSorted
    prepared.sourceResultSorted middle prepared.resultEquation


def canonicalUniversalElimination (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff)
    (logicalFresh : ¬ Preterm.HasVar context (binders workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) scope.formation)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) scope.formation)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) scope.formation)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (universal : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (.all body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth
          (instantiate argument body)))) := by
  let antecedent := scope.formation
  have antecedentSorted := scope.formationSorted
  let formationPrepared := deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let formationQuantifierEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.all body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.all body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have domainIndependent := encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain
  have propositionSorted := signature.application context .bool [] .nil
  let prepared := formationPrepared.promote signature structural scope _ _ _ _ _ _ (binders workDepth)
    domainSorted propositionSorted head
  let quantifierEquation := promoteEquality signature structural scope (boolType signature.symbol) _ _
    propositionSorted sourceQuantifierSorted workQuantifierSorted formationQuantifierEquation

  let universalFresh := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation universal
  let instanceFresh := HOLKernelQuantifierProofs.universalElimination signature abbreviation binding
    scope.logical _ _ _ _ (binders workDepth) scope.logicalSorted domainSorted head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.argumentTyping prepared.native.resultTyping prepared.native.equation universalFresh
  exact HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted prepared.native.resultSorted prepared.sourceResultSorted
    prepared.resultEquation instanceFresh

def canonicalExistentialIntroduction (signature : Signature sorts terms)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (base : Base → Preterm) (constant : ∀ {type}, Const type → Preterm)
    (binders temporary : Nat → Nat)
    (baseSorted : ∀ index, Preterm.HasType terms context (base index) [] signature.ids.type)
    (constantSorted : ∀ {type} (symbol : Const type),
      Preterm.HasType terms context (constant symbol) [] signature.ids.object)
    (bindersInjective : Function.Injective binders) (temporaryInjective : Function.Injective temporary)
    (baseIndependent : ∀ slot index, ¬ Preterm.HasVar context (binders slot) (base index))
    (temporaryIndependent : ∀ slot index, ¬ Preterm.HasVar context (temporary slot) (base index))
    {gamma : Ctx Base} {domain : Ty Base}
    (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) .prop)
    (assignment : Assignment gamma) (sourceDepth workDepth temporaryDepth : Nat)
    (scope : HOLKernelStructuralRules.ProofContext terms definitions theorems context hypotheses
      signature.symbol signature.ids.wff)
    (logicalFresh : ¬ Preterm.HasVar context (binders workDepth) scope.logical)
    (assignmentSorted : ∀ {type} (index : Var gamma type),
      Preterm.HasType terms context (assignment index) [] signature.ids.object)
    (sourceSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (sourceDepth + offset)]? = some (.bound signature.ids.object))
    (workSlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[binders (workDepth + offset)]? = some (.bound signature.ids.object))
    (temporarySlots : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      context[temporary (temporaryDepth + offset)]? = some (.bound signature.ids.object))
    (sourceFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (sourceDepth + offset)) scope.formation)
    (workFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (binders (workDepth + offset)) scope.formation)
    (temporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset)) scope.formation)
    (sourceDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (sourceDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (workDisjoint : ∀ firstOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
      ∀ secondOffset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1,
        binders (workDepth + firstOffset) ≠ temporary (temporaryDepth + secondOffset))
    (equationFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (binders (workDepth + 1 + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (equationTemporaryFresh : ∀ offset < body.binderDepth + Subst.maxBinderDepth (Subst.single argument),
      ¬ Preterm.HasVar context (temporary (temporaryDepth + offset))
        (conjunction signature.symbol scope.formation
          (holds signature.symbol (equality signature.symbol (encodeType signature.symbol base domain)
            (.var (binders workDepth))
            (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth argument)))))
    (variableTyping : ∀ {type} (index : Var gamma type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (assignment index) (encodeType signature.symbol base type)))
    (constantTyping : ∀ {type} (symbol : Const type),
      CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
        (context := context) (hypotheses := hypotheses)
        (typed signature.symbol scope.formation (constant symbol) (encodeType signature.symbol base type)))
    (instanceProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth
          (instantiate argument body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := context) (hypotheses := hypotheses)
      (entails signature.symbol scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol base constant binders assignment sourceDepth (.ex body)))) := by
  let antecedent := scope.formation
  have antecedentSorted := scope.formationSorted
  let formationPrepared := deriveCanonicalInstance signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent argument body
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted sourceSlots workSlots
    temporarySlots sourceFresh workFresh temporaryFresh sourceDisjoint workDisjoint equationFresh equationTemporaryFresh
    variableTyping constantTyping
  let formationQuantifierEquation := HOLKernelAlpha.rebind signature profile structural typing rules binding base constant binders temporary
    baseSorted constantSorted bindersInjective temporaryInjective baseIndependent temporaryIndependent (.ex body)
    assignment sourceDepth workDepth temporaryDepth antecedent antecedentSorted assignmentSorted
    (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporarySlots offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => sourceFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => workFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (fun offset smaller => temporaryFresh offset (by simp only [Term.binderDepth] at smaller; omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact sourceDisjoint first (by omega) second (by omega))
    (by
      intro first firstSmaller second secondSmaller
      simp only [Term.binderDepth] at firstSmaller secondSmaller
      exact Ne.symm (workDisjoint second (by omega) first (by omega)))
    variableTyping constantTyping
  have sourceQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body)
    assignment sourceDepth assignmentSorted (fun offset smaller => sourceSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have workQuantifierSorted := encode_sorted signature context base constant binders baseSorted constantSorted (.ex body)
    assignment workDepth assignmentSorted (fun offset smaller => workSlots offset (by simp only [Term.binderDepth] at smaller; omega))
  have head : context[binders workDepth]? = some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using workSlots 0 (by omega)
  have domainSorted := encodeType_sorted signature context base baseSorted domain
  have domainIndependent := encodeType_independent context _ signature.symbol base (baseIndependent workDepth) domain
  have propositionSorted := signature.application context .bool [] .nil
  let prepared := formationPrepared.promote signature structural scope _ _ _ _ _ _ (binders workDepth)
    domainSorted propositionSorted head
  let quantifierEquation := promoteEquality signature structural scope (boolType signature.symbol) _ _
    propositionSorted sourceQuantifierSorted workQuantifierSorted formationQuantifierEquation

  have boolSorted := signature.application context .bool [] .nil
  let instanceEquation := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    boolSorted scope.logicalSorted prepared.native.resultSorted prepared.sourceResultSorted prepared.resultEquation
  let instanceFresh := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted prepared.sourceResultSorted prepared.native.resultSorted instanceEquation instanceProof
  let existentialFresh := HOLKernelQuantifierProofs.existentialIntroduction signature abbreviation binding
    scope.logical _ _ _ _ (binders workDepth) scope.logicalSorted domainSorted head prepared.argumentSorted
    prepared.native.bodySorted prepared.native.resultSorted logicalFresh domainIndependent
    prepared.native.bodyTyping prepared.argumentTyping prepared.native.equation instanceFresh
  let outputEquation := HOLKernelInferenceProofs.Native.symmetry signature rules (boolType signature.symbol) scope.logical _ _
    boolSorted scope.logicalSorted sourceQuantifierSorted workQuantifierSorted quantifierEquation
  exact HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules
    scope.logical _ _ scope.logicalSorted workQuantifierSorted sourceQuantifierSorted outputEquation existentialFresh


#print axioms InstancePremises.promote
#print axioms CanonicalInstancePremises.promote
#print axioms deriveInstance
#print axioms beta
#print axioms universalElimination
#print axioms existentialIntroduction
#print axioms deriveCanonicalInstance
#print axioms canonicalBeta
#print axioms canonicalUniversalElimination
#print axioms canonicalExistentialIntroduction
end Mettapedia.Languages.MM0.HOLKernelSourceInstantiation

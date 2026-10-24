import Mettapedia.Languages.MM0.HOLKernelProofInstantiation
import Mettapedia.Languages.MM0.HOLKernelExtensionality

/-!
# Extensional HOL equations in an allocated proof environment

The maintained eta rule is applied at an allocated native variable. Constructed
alpha equations restore the original source binders and the original function
encoding. All typing premises are built in the formation context before they
are promoted through the retained assumptions.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofExtensionality
open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTermAssignments
open HOLKernelProofEnvironment HOLKernelProofAllocation
open HOLKernelStructuralRules (CheckedProof)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {hypotheses : List Preterm}
variable {signature : Signature sorts terms} {layout : Layout} {initial : Context}
variable {encoding : Encoding signature layout initial Base Const}
variable {gamma : Ctx Base} {assumptions : List (Formula Const gamma)} {sourceDepth : Nat}
variable {equivalenceReference : Nat}

def eta
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids equivalenceReference)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain result : Ty Base} (function : Term Const gamma (domain ⇒ result))
    (fits : function.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (environment.encode (.eq (.lam (.app (weaken function) (.var .vz))) function)))) := by
  let windows := environment.windows active before
  let inner := windows.bodyWindow function.binderDepth fits
  let etaSource : Term Const gamma (domain ⇒ result) := .lam (.app (weaken function) (.var .vz))
  have etaFits : etaSource.binderDepth ≤ layout.width := by
    simp only [etaSource, Term.binderDepth, weaken, Term.binderDepth_rename, Nat.max_zero]
    exact fits
  have rootBound : (NativeContext signature layout initial)[Layout.names initial (layout.workDepth frame)]? =
      some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
  have domainSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted domain
  have resultSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted result
  have typeSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted (domain ⇒ result)
  let workFunction := encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
    environment.assignment (layout.workDepth frame + 1) function
  have workFunctionSorted := encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted function environment.assignment inner.workDepth environment.assignmentSorted inner.workSlots
  let formationTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing
    encoding.base encoding.constant (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) encoding.baseIndependent function environment.assignment inner.workDepth
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted inner.workSlots inner.workFresh
    environment.variableTyping environment.constantTyping
  let functionTyping := environment.scope.promote signature structural _
    (hasType_sorted signature _ workFunctionSorted typeSorted) formationTyping
  let reduction := HOLKernelBindingProofs.Native.eta signature binding environment.scope.logical _ _
    (Layout.names initial (layout.workDepth frame)) workFunction environment.scope.logicalSorted domainSorted resultSorted
    rootBound workFunctionSorted (environment.logicalIndependent _ before)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) result)
    functionTyping
  let beforeEquation := HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    etaSource environment.assignment environment.scope windows etaFits environment.assignmentSorted
    environment.variableTyping environment.constantTyping
  let afterEquation := HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    function environment.assignment environment.scope inner (Nat.le_refl _) environment.assignmentSorted
    environment.variableTyping environment.constantTyping
  have coherence := encode_rename (delta := domain :: gamma) signature.symbol encoding.base encoding.constant (Layout.names initial) function
    (fun {_} index => Var.vs index)
    (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
    (layout.workDepth frame + 1)
  change encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
      (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
      (layout.workDepth frame + 1) (weaken function) = workFunction at coherence
  have nativeReduction : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol (encodeType signature.symbol encoding.base (domain ⇒ result))
          (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
            environment.assignment (layout.workDepth frame) etaSource) workFunction))) := by
    simpa only [etaSource, encodeWithAssignment, Assignment.extend, coherence, encodeType, HOLKernelTypingRules.functionType] using reduction
  have sourceEtaSorted := environment.encoded_sorted etaSource etaFits active before
  have workEtaSorted := encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted etaSource environment.assignment (layout.workDepth frame) environment.assignmentSorted
    (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller etaFits))
  have sourceFunctionSorted := environment.encoded_sorted function (by omega) active before
  let first := HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workEtaSorted workFunctionSorted beforeEquation nativeReduction
  let last := HOLKernelInferenceProofs.Native.symmetry signature rules _ environment.scope.logical _ _
    typeSorted environment.scope.logicalSorted sourceFunctionSorted workFunctionSorted afterEquation
  exact HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workFunctionSorted sourceFunctionSorted first last

def functionExtensionality
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain result : Ty Base} (first second : Term Const gamma (domain ⇒ result))
    (fits : max first.binderDepth second.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (pointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (environment.encode (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (.eq first second)))) := by
  let windows := environment.windows active before
  let inner := windows.bodyWindow (max first.binderDepth second.binderDepth) fits
  let source : Formula Const gamma := .all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))
  have sourceFit : source.binderDepth ≤ layout.width := by
    simpa only [source, Term.binderDepth, weaken, Term.binderDepth_rename, Nat.max_zero] using fits
  have firstFit : first.binderDepth ≤ max first.binderDepth second.binderDepth := Nat.le_max_left _ _
  have secondFit : second.binderDepth ≤ max first.binderDepth second.binderDepth := Nat.le_max_right _ _
  have quantifiedBound : (NativeContext signature layout initial)[Layout.names initial (layout.workDepth frame)]? =
      some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
  have argumentBound : (NativeContext signature layout initial)[Layout.names initial (layout.temporaryDepth frame)]? =
      some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.temporarySlots initial signature.ids.object active 0 (by omega)
  have domainSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted domain
  have resultSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted result
  have typeSorted := encodeType_sorted signature _ encoding.base encoding.baseSorted (domain ⇒ result)
  let firstWork := encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
    environment.assignment (layout.workDepth frame + 1) first
  let secondWork := encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
    environment.assignment (layout.workDepth frame + 1) second
  have firstWorkSorted := encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted first environment.assignment inner.workDepth environment.assignmentSorted
    (fun offset smaller => inner.workSlots offset (Nat.lt_of_lt_of_le smaller firstFit))
  have secondWorkSorted := encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted second environment.assignment inner.workDepth environment.assignmentSorted
    (fun offset smaller => inner.workSlots offset (Nat.lt_of_lt_of_le smaller secondFit))
  let firstFormationTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing
    encoding.base encoding.constant (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) encoding.baseIndependent first environment.assignment inner.workDepth
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => inner.workSlots offset (Nat.lt_of_lt_of_le smaller firstFit))
    (fun offset smaller => inner.workFresh offset (Nat.lt_of_lt_of_le smaller firstFit))
    environment.variableTyping environment.constantTyping
  let secondFormationTyping := HOLKernelTermTyping.compileWithAssignment signature structural typing
    encoding.base encoding.constant (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) encoding.baseIndependent second environment.assignment inner.workDepth
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => inner.workSlots offset (Nat.lt_of_lt_of_le smaller secondFit))
    (fun offset smaller => inner.workFresh offset (Nat.lt_of_lt_of_le smaller secondFit))
    environment.variableTyping environment.constantTyping
  let firstTyping := environment.scope.promote signature structural _
    (hasType_sorted signature _ firstWorkSorted typeSorted) firstFormationTyping
  let secondTyping := environment.scope.promote signature structural _
    (hasType_sorted signature _ secondWorkSorted typeSorted) secondFormationTyping
  let quantifierEquation := HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    source environment.assignment environment.scope windows sourceFit environment.assignmentSorted
    environment.variableTyping environment.constantTyping
  have workSourceSorted := encode_sorted signature _ encoding.base encoding.constant (Layout.names initial)
    encoding.baseSorted encoding.constantSorted source environment.assignment windows.workDepth environment.assignmentSorted
    (fun offset smaller => windows.workSlots offset (Nat.lt_of_lt_of_le smaller sourceFit))
  let carried := HOLKernelInferenceProofs.booleanEqualityElimination signature abbreviation rules environment.scope.logical _ _
    environment.scope.logicalSorted (environment.encoded_sorted source sourceFit active before) workSourceSorted quantifierEquation pointwise
  have firstCoherence := encode_rename (delta := domain :: gamma) signature.symbol encoding.base encoding.constant (Layout.names initial) first
    (fun {_} index => Var.vs index) (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
    (layout.workDepth frame + 1)
  have secondCoherence := encode_rename (delta := domain :: gamma) signature.symbol encoding.base encoding.constant (Layout.names initial) second
    (fun {_} index => Var.vs index) (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
    (layout.workDepth frame + 1)
  change encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
      (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
      (layout.workDepth frame + 1) (weaken first) = firstWork at firstCoherence
  change encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
      (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
      (layout.workDepth frame + 1) (weaken second) = secondWork at secondCoherence
  have workDepth : windows.workDepth = layout.workDepth frame := rfl
  have nativePointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (applySymbol signature.symbol .allc
        [.var (Layout.names initial (layout.workDepth frame)), encodeType signature.symbol encoding.base domain,
          HOLKernelInferenceRules.equality signature.symbol (encodeType signature.symbol encoding.base result)
            (applySymbol signature.symbol .app [firstWork, .var (Layout.names initial (layout.workDepth frame))])
            (applySymbol signature.symbol .app [secondWork, .var (Layout.names initial (layout.workDepth frame))])]))) := by
    simpa only [source, encodeWithAssignment, workDepth, firstCoherence, secondCoherence, Assignment.extend, HOLKernelInferenceRules.equality] using carried
  let native := HOLKernelExtensionality.functionExtensionality signature abbreviation profile structural typing rules binding
    environment.scope.logical _ _ firstWork secondWork (Layout.names initial (layout.workDepth frame)) (Layout.names initial (layout.temporaryDepth frame))
    environment.scope.logicalSorted domainSorted resultSorted firstWorkSorted secondWorkSorted quantifiedBound argumentBound
    (by intro same; have equal := Layout.names_injective initial same; simp only [Layout.temporaryDepth] at equal; omega)
    (environment.logicalIndependent _ before)
    (environment.logicalIndependent _ (by simp only [Layout.temporaryDepth]; omega))
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) result)
    firstTyping secondTyping nativePointwise
  let firstEquation := HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    first environment.assignment environment.scope inner firstFit environment.assignmentSorted environment.variableTyping environment.constantTyping
  let secondEquation := HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    second environment.assignment environment.scope inner secondFit environment.assignmentSorted environment.variableTyping environment.constantTyping
  have firstSourceSorted := environment.encoded_sorted first (by omega) active before
  have secondSourceSorted := environment.encoded_sorted second (by omega) active before
  let backward := HOLKernelInferenceProofs.Native.symmetry signature rules _ environment.scope.logical _ _ typeSorted
    environment.scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
  let joined := HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted firstSourceSorted firstWorkSorted secondWorkSorted firstEquation native
  exact HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted firstSourceSorted secondWorkSorted secondSourceSorted joined backward

#print axioms eta
#print axioms functionExtensionality
end Mettapedia.Languages.MM0.HOLKernelProofExtensionality

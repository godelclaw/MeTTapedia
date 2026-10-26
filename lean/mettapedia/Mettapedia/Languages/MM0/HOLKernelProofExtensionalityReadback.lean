import Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
import Mettapedia.Languages.MM0.HOLKernelExtensionalityReadback

/-!
# Independent readback of allocated native eta and extensionality receipts

The actual eta proof producer retains its source-to-work rebinding, native eta
application, return rebinding, symmetry and transitivity. Its witness belongs
to the proof-free admission grammar at the exact source equation, with the
logical antecedent and theorem-selection policy preserved. This module proves
admission of that emitted receipt. Function extensionality additionally retains
the actual pointwise certificate in its fresh argument frame; the projection
bound and source-image rebinding laws justify the remaining contextual moves.
Supplying that premise reading for all compiler outputs belongs to the complete
compiler-image induction and is not inferred from arbitrary original-frame
admission.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback HOLKernelProofEnvironment
open HOLKernelTermAssignments HOLKernelProofAllocation HOLKernelJudgment
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms}
variable {layout : Layout}
variable {encoding : Encoding signature layout
  (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol}
variable {gamma : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {depth : Nat}
variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
variable {profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
variable {environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := [])
  encoding gamma assumptions depth} {names : Names gamma}

open HOLKernelStructuralRules (CheckedProof)
theorem Reading.eta_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain result : Ty Unit} (function : Term Symbol gamma (domain ⇒ result))
    (fits : function.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel names
      (HOLKernelProofExtensionality.eta profile structural typing rules binding environment function fits active before).val
      (.imp reading.logical.formula (.eq (.lam (.app (weaken function) (.var .vz))) function))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  let inner := windows.bodyWindow function.binderDepth fits
  let etaSource : Term Symbol gamma (domain ⇒ result) := .lam (.app (weaken function) (.var .vz))
  have etaFits : etaSource.binderDepth ≤ layout.width := by
    simp only [etaSource, Term.binderDepth, weaken, Term.binderDepth_rename, Nat.max_zero]
    exact fits
  have rootBound : (HOLKernelProofEnvironment.NativeContext signature layout initial)[Layout.names initial (layout.workDepth frame)]? =
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
  let nativeReduction : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := HOLKernelProofEnvironment.NativeContext signature layout initial) (hypotheses := [])
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
  have workAfter : depth ≤ layout.workDepth frame := by omega
  have tempAfter : depth ≤ layout.temporaryDepth frame := by simp only [Layout.temporaryDepth]; omega
  have innerAfter : depth ≤ inner.workDepth := by
    change depth ≤ layout.workDepth frame + 1
    omega
  have typeRead : readType signature.symbol
      (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol encoding.base (domain ⇒ result))) = some (domain ⇒ result) := by
    rw [reading.base]
    change readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference
      (encodeType signature.symbol (fun _ : Unit => .var 0) (domain ⇒ result))) = some (domain ⇒ result)
    rw [expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct
      (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective _
  have sourceEtaRead := reading.term_read_at distinct etaSource depth (Nat.le_refl _)
  have sourceFunctionRead := reading.term_read_at distinct function depth (Nat.le_refl _)
  have workEtaRead := reading.term_read_at distinct etaSource (layout.workDepth frame) workAfter
  have workFunctionRead := reading.term_read_at distinct function (layout.workDepth frame + 1) (by omega)
  have etaEquationRead := HOLKernelCongruenceReadback.equation_read signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 names (encodeType signature.symbol encoding.base (domain ⇒ result))
    _ _ etaSource function typeRead workEtaRead workFunctionRead
  have reductionRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol (encodeType signature.symbol encoding.base (domain ⇒ result))
          (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
            environment.assignment (layout.workDepth frame) etaSource) workFunction))) =
      some (.imp reading.logical.formula (.eq etaSource function)) := by
    rw [HOLKernelStructuralReadback.read_entails abbreviation signature.symbol_injective (distinct .im),
      reading.logical_formula, etaEquationRead]
    rfl
  have nativeReductionVal : nativeReduction.val = reduction.val := by
    simp only [nativeReduction]
    exact CheckedProof.val_mpr (fun expression => entails signature.symbol environment.scope.logical
      (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol
        (encodeType signature.symbol encoding.base (domain ⇒ result))
        (applySymbol signature.symbol .lam [.var (Layout.names initial (layout.workDepth frame)),
          encodeType signature.symbol encoding.base domain,
          applySymbol signature.symbol .app [expression, .var (Layout.names initial (layout.workDepth frame))]]) workFunction)))
      coherence reduction
  let reductionTree : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt 1 names nativeReduction.val (.imp reading.logical.formula (.eq etaSource function)) := by
    have accepted := nativeReduction.property.eval
    rw [nativeReductionVal] at accepted
    rw [nativeReductionVal]
    exact AdmittedStep.binding accepted {
      rule := .eta
      selected := bindingSelected .eta
      declared := binding.declared .eta
      conclusion_read := reductionRead
      step := .eta }
  obtain ⟨beforeFuel, ⟨beforeTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding etaSource windows etaFits
    (Nat.le_refl _) workAfter tempAfter ruleAt bindingAt selected structuralSelected (bindingSelected .abstractionRenaming) projection
  obtain ⟨afterFuel, ⟨afterTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding function inner (Nat.le_refl _)
    (Nat.le_refl _) innerAfter tempAfter ruleAt bindingAt selected structuralSelected (bindingSelected .abstractionRenaming) projection
  obtain ⟨firstTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules names environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workEtaSorted workFunctionSorted beforeEquation nativeReduction
    reading.logical etaSource etaSource function reading.logical_read typeRead sourceEtaRead workEtaRead workFunctionRead
    ruleAt bindingAt (selected .transitivity) beforeTree reductionTree
  obtain ⟨lastTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules names _ environment.scope.logical _ _ typeSorted
    environment.scope.logicalSorted sourceFunctionSorted workFunctionSorted afterEquation reading.logical function function
    reading.logical_read typeRead sourceFunctionRead workFunctionRead ruleAt bindingAt (selected .symmetry) afterTree
  refine ⟨max (max beforeFuel 1 + 1) (afterFuel + 1) + 1, ?_⟩
  exact HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules names environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workFunctionSorted sourceFunctionSorted first last
    reading.logical etaSource function function reading.logical_read typeRead sourceEtaRead workFunctionRead sourceFunctionRead
    ruleAt bindingAt (selected .transitivity) firstTree lastTree

#print axioms Reading.eta_admitted
/-- The actual allocated extensionality receipt is admitted when its retained pointwise premise is admitted in the required argument frame. -/
theorem Reading.functionExtensionality_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain result : Ty Unit} (first second : Term Symbol gamma (domain ⇒ result))
    (fits : max first.binderDepth second.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (pointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext (signature := signature) (layout := layout)) (hypotheses := [])
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (environment.encode (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))))))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {pointwiseFuel : Nat}
    (pointwiseAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt pointwiseFuel
      (BinderNames.cons (type := domain) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.temporaryDepth frame)) names)
      pointwise.val (.imp (weaken (σ := domain) reading.logical.formula)
        (.all (.eq (.app (weaken (σ := domain) (weaken (σ := domain) first)) (.var .vz))
          (.app (weaken (σ := domain) (weaken (σ := domain) second)) (.var .vz)))))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofExtensionality.functionExtensionality abbreviation profile structural typing rules binding environment first second fits active before pointwise).val
      (.imp reading.logical.formula (.eq first second))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  let inner := windows.bodyWindow (max first.binderDepth second.binderDepth) fits
  let source : Formula Symbol gamma := .all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))
  have sourceFit : source.binderDepth ≤ layout.width := by
    simpa only [source, Term.binderDepth, weaken, Term.binderDepth_rename, Nat.max_zero] using fits
  have firstFit : first.binderDepth ≤ max first.binderDepth second.binderDepth := Nat.le_max_left _ _
  have secondFit : second.binderDepth ≤ max first.binderDepth second.binderDepth := Nat.le_max_right _ _
  have quantifiedBound : (HOLKernelProofEnvironment.NativeContext signature layout initial)[Layout.names initial (layout.workDepth frame)]? =
      some (.bound signature.ids.object) := by
    simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
  have argumentBound : (HOLKernelProofEnvironment.NativeContext signature layout initial)[Layout.names initial (layout.temporaryDepth frame)]? =
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
  let nativePointwise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := HOLKernelProofEnvironment.NativeContext signature layout initial) (hypotheses := [])
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

  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have workAfter : depth ≤ layout.workDepth frame := by omega
  have tempAfter : depth ≤ layout.temporaryDepth frame := by simp only [Layout.temporaryDepth]; omega
  have fresh (level : Nat) (later : depth ≤ level) : Layout.names initial level ∉ names.toList := by
    intro member
    have upper := (reading.names_in_scope.2 _ member).2
    change 7 + level < 7 + depth at upper
    omega
  have dictionaryFresh (level : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial level) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + level) = none
    rw [Nat.add_comm]
    rfl
  let argumentNames : Names (domain :: gamma) := BinderNames.cons (Layout.names initial (layout.temporaryDepth frame)) names
  let shift : Rename Unit gamma (domain :: gamma) := Rename.weaken
  have argumentLookup : LookupPreserving HOLKernelSetOperationReadback.readConstant shift names argumentNames :=
    LookupPreserving.weaken HOLKernelSetOperationReadback.readConstant names domain _
      (BinderNames.lookup?_none_of_not_mem names (fresh _ tempAfter)) (dictionaryFresh _)
  have argumentNodup : argumentNames.toList.Nodup := List.nodup_cons.mpr ⟨fresh _ tempAfter, reading.names_in_scope.1⟩
  have argumentAbove : ∀ name ∈ argumentNames.toList, 7 ≤ name := by
    intro name member
    rcases List.mem_cons.mp member with rfl | old
    · change 7 ≤ 7 + _; omega
    · exact (reading.names_in_scope.2 _ old).1
  have argumentAssignment : ∀ {type} (index : Var gamma type), environment.assignment index = .var (argumentNames.nameOf (shift index)) := reading.assignment
  have argumentLogicalRead := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ reading.logical reading.logical_read
  have argumentFormationRead := logical_judgment_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ reading.formation reading.formation_read
  have nativeRoom : 7 + layout.workDepth frame ≤ (NativeContext (signature := signature) (layout := layout)).length :=
    Nat.le_of_lt ((List.getElem?_eq_some_iff.mp quantifiedBound).1)
  obtain ⟨projectionAtArgument⟩ := projectionTree.logical_weaken_of_varsBelow profile abbreviation HOLKernelSetOperationReadback.readConstant 7 ruleAt bindingAt
    (7 + layout.workDepth frame) nativeRoom bounded.projection domain (Layout.names initial (layout.temporaryDepth frame))
    (by change 7 + layout.workDepth frame ≤ 7 + layout.temporaryDepth frame; simp only [Layout.temporaryDepth]; omega)
  obtain ⟨quantifierFuel, ⟨quantifierTree⟩⟩ := HOLKernelSourceBindingReadback.rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound encoding.base encoding.constant reading.base reading.constant
    (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent source environment.assignment environment.scope windows sourceFit environment.assignmentSorted
    environment.variableTyping environment.constantTyping shift argumentNames argumentNodup argumentAbove argumentAssignment
    (by intro offset _ type index; exact BinderNames.ne_nameOf_of_not_mem names (fresh _ (by change depth ≤ depth + offset; omega)) index)
    (by intro offset _ type index; exact BinderNames.ne_nameOf_of_not_mem names (fresh _ (by change depth ≤ layout.workDepth frame + offset; omega)) index)
    (by intro offset _ type index; exact BinderNames.ne_nameOf_of_not_mem names (fresh _ (by change depth ≤ layout.temporaryDepth frame + offset; omega)) index)
    (reading.logical.rename shift) (reading.formation.rename shift) argumentLogicalRead argumentFormationRead
    ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming)
    (by simpa only [Judgment.rename_formula, HOL.rename, shift, weaken] using projectionAtArgument)
  have sourceRead := reading.term_read_at distinct source depth (Nat.le_refl _)
  have workSourceRead := reading.term_read_at distinct source (layout.workDepth frame) workAfter
  have sourceReadAtArgument := logical_reader_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ source sourceRead
  have workSourceReadAtArgument := logical_reader_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ source workSourceRead
  have shiftedSource : HOL.rename shift source =
      Term.all (.eq (.app (weaken (σ := domain) (weaken (σ := domain) first)) (.var .vz))
        (.app (weaken (σ := domain) (weaken (σ := domain) second)) (.var .vz))) := by
    have shiftedWeak {type : Ty Unit} (term : Term Symbol gamma type) : HOL.rename (Rename.lift shift) (weaken (σ := domain) term) =
        weaken (σ := domain) (weaken (σ := domain) term) := by
      simp only [weaken, rename_comp]
      exact rename_ext (by intro type index; rfl) term
    simp only [source, HOL.rename, shiftedWeak, Rename.lift]
  obtain ⟨carriedTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules argumentNames environment.scope.logical _ _ environment.scope.logicalSorted
    (environment.encoded_sorted source sourceFit active before) workSourceSorted quantifierEquation pointwise
    (reading.logical.rename shift) (HOL.rename shift source) (HOL.rename shift source) argumentLogicalRead sourceReadAtArgument workSourceReadAtArgument
    ruleAt bindingAt (selected .booleanEqualityElimination) quantifierTree
    (by simpa only [Judgment.rename_formula, shiftedSource, shift, weaken] using pointwiseAdmitted)
  have pointwiseStatement :
      entails signature.symbol environment.scope.logical (holds signature.symbol
        (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial) environment.assignment windows.workDepth source)) =
      entails signature.symbol environment.scope.logical (holds signature.symbol (applySymbol signature.symbol .allc
        [.var (Layout.names initial (layout.workDepth frame)), encodeType signature.symbol encoding.base domain,
          HOLKernelInferenceRules.equality signature.symbol (encodeType signature.symbol encoding.base result)
            (applySymbol signature.symbol .app [firstWork, .var (Layout.names initial (layout.workDepth frame))])
            (applySymbol signature.symbol .app [secondWork, .var (Layout.names initial (layout.workDepth frame))])] )) := by
    simp only [source, encodeWithAssignment, workDepth, firstCoherence, secondCoherence, Assignment.extend, HOLKernelInferenceRules.equality]
  have nativePointwiseVal : nativePointwise.val = carried.val := by
    simp only [nativePointwise]
    exact CheckedProof.val_mpr (fun expression => expression) pointwiseStatement.symm carried
  have nativePointwiseTree : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt
      (max (quantifierFuel + 1) pointwiseFuel + 1) argumentNames nativePointwise.val
      (.imp (weaken (σ := domain) reading.logical.formula)
        (.all (.eq (.app (weaken (σ := domain) (weaken (σ := domain) first)) (.var .vz))
          (.app (weaken (σ := domain) (weaken (σ := domain) second)) (.var .vz))))) := by
    rw [nativePointwiseVal]
    simpa only [Judgment.rename_formula, shiftedSource, shift, weaken] using carriedTree
  have typeRead (type : Ty Unit) : readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference
      (encodeType signature.symbol encoding.base type)) = some type := by
    rw [reading.base]
    change readType signature.symbol (expandEquivalence signature.symbol abbreviation.reference (encodeType signature.symbol (fun _ : Unit => .var 0) type)) = some type
    rw [expandEquivalence_encodeType_of_fixed signature.symbol abbreviation.reference distinct (fun _ : Unit => .var 0) (fun _ => by simp [expandEquivalence])]
    exact readType_encode signature.symbol signature.symbol_injective _
  have firstSourceRead := reading.term_read_at distinct first depth (Nat.le_refl _)
  have secondSourceRead := reading.term_read_at distinct second depth (Nat.le_refl _)
  have firstWorkRead := reading.term_read_at distinct first (layout.workDepth frame + 1) (by omega)
  have secondWorkRead := reading.term_read_at distinct second (layout.workDepth frame + 1) (by omega)
  have freshName (level : Nat) (later : depth ≤ level) : HOLKernelBindingInterpretation.freshName 7 names (Layout.names initial level) = true := by
    have absent := BinderNames.lookup?_none_of_not_mem names (fresh level later)
    simp only [HOLKernelBindingInterpretation.freshName, absent, Option.isNone_none, Bool.and_true, decide_eq_true_eq]
    change 7 ≤ 7 + level
    omega
  obtain ⟨nativeFuel, ⟨nativeTree⟩⟩ := HOLKernelExtensionalityReadback.functionExtensionality_admitted signature abbreviation profile structural typing rules binding
    environment.scope.logical _ _ firstWork secondWork (Layout.names initial (layout.workDepth frame)) (Layout.names initial (layout.temporaryDepth frame))
    environment.scope.logicalSorted domainSorted resultSorted firstWorkSorted secondWorkSorted quantifiedBound argumentBound
    (by intro same; have equal := Layout.names_injective initial same; simp only [Layout.temporaryDepth] at equal; omega)
    (environment.logicalIndependent _ before) (environment.logicalIndependent _ (by simp only [Layout.temporaryDepth]; omega))
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) domain)
    (HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent _) result)
    firstTyping secondTyping nativePointwise distinct HOLKernelSetOperationReadback.readConstant 7 names domain result first second reading.logical
    reading.logical_read (typeRead domain) (typeRead result) firstWorkRead secondWorkRead (freshName _ workAfter) (freshName _ tempAfter)
    (dictionaryFresh _) (dictionaryFresh _) ruleAt bindingAt selected structuralSelected bindingSelected nativePointwiseTree
  obtain ⟨firstFuel, ⟨firstTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding first inner firstFit (Nat.le_refl _)
    (by change depth ≤ layout.workDepth frame + 1; omega) tempAfter ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming) ⟨projectionFuel, ⟨projectionTree⟩⟩
  obtain ⟨secondFuel, ⟨secondTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding second inner secondFit (Nat.le_refl _)
    (by change depth ≤ layout.workDepth frame + 1; omega) tempAfter ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming) ⟨projectionFuel, ⟨projectionTree⟩⟩
  obtain ⟨backwardTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names _ environment.scope.logical _ _ typeSorted environment.scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
    reading.logical second second reading.logical_read (typeRead _) secondSourceRead secondWorkRead ruleAt bindingAt (selected .symmetry) secondTree
  obtain ⟨joinedTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names environment.scope.logical _ _ _ _ environment.scope.logicalSorted typeSorted firstSourceSorted firstWorkSorted secondWorkSorted firstEquation native
    reading.logical first first second reading.logical_read (typeRead _) firstSourceRead firstWorkRead secondWorkRead ruleAt bindingAt (selected .transitivity) firstTree nativeTree
  have finalTree := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names environment.scope.logical _ _ _ _ environment.scope.logicalSorted typeSorted firstSourceSorted secondWorkSorted secondSourceSorted joined backward
    reading.logical first second second reading.logical_read (typeRead _) firstSourceRead secondWorkRead secondSourceRead ruleAt bindingAt (selected .transitivity) joinedTree backwardTree
  exact ⟨_, finalTree⟩

#print axioms Reading.functionExtensionality_admitted

end Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback

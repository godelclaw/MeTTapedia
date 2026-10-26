import Mettapedia.Languages.MM0.HOLKernelContextualReadback
import Mettapedia.Languages.MM0.HOLKernelSourceInstantiationReadback
import Mettapedia.Languages.MM0.HOLKernelExtensionalityReadback

/-!
# Compiler receipt constructors under contextual source readings

The actual rebinding, instantiation, eta, extensionality and binding constructors
preserve independently admitted receipts when the source environment is read
through a typed renaming. The source binder window and work-bank bounds govern
which extra reader variables are allowed. Projections and ordered assumptions
retain their actual native scope bounds.

Function extensionality consumes its pointwise certificate in the fresh
argument frame. The complete compiler induction must construct that premise;
these component laws do not assert arbitrary proof-tree frame transport.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
open HOLKernelRuleReadback HOLKernelProofReadback HOLKernelProofEnvironment
open HOLKernelTermAssignments HOLKernelProofAllocation HOLKernelJudgment
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)
open HOLKernelStructuralRules (CheckedProof)
variable {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {signature : Signature sorts terms} {layout : Layout}
variable {encoding : Encoding signature layout (HOLKernelSetOperationInterpretation.initialContext signature.ids) Unit Symbol}
variable {gamma target : Ctx Unit} {assumptions : List (Formula Symbol gamma)} {depth : Nat}
variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids}
variable {profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature}
variable {environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := []) encoding gamma assumptions depth}
variable {rho : Rename Unit gamma target} {names : Names target}
theorem ContextualReading.rebind_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {type : Ty Unit} (source : Term Symbol gamma type)
    (windows : HOLKernelSourceBinding.RebindingWindows (NativeContext (signature := signature) (layout := layout))
      signature.ids.object environment.scope.formation
      (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
      (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)))
    (fits : source.binderDepth ≤ windows.width)
    (sourceAfter : depth ≤ windows.sourceDepth) (workAfter : depth ≤ windows.workDepth)
    (temporaryAfter : depth ≤ windows.temporaryDepth)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ruleAt (structural.index .syl) = some (.structural .syl))
    (bindingSelected : bindingAt (binding.index .abstractionRenaming) = some .abstractionRenaming)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt fuel names
      (HOLKernelSourceBinding.rebindInContext signature profile structural typing rules binding
        encoding.base encoding.constant
        (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
        (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
        encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
        encoding.baseIndependent encoding.baseIndependent source environment.assignment environment.scope windows fits
        environment.assignmentSorted environment.variableTyping environment.constantTyping).val
      (.imp reading.logical.formula (.eq (HOL.rename rho source) (HOL.rename rho source)))) := by
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, depth ≤ location → ∀ offset {type} (index : Var gamma type),
      Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (location + offset) ≠ names.nameOf (rho index) := by
    intro location afterSource offset type index same
    have upper := reading.source_before index
    change 7 + (location + offset) = names.nameOf (rho index) at same
    omega
  have result := HOLKernelSourceBindingReadback.rebindInContext_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids))
    encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent source environment.assignment environment.scope windows fits
    environment.assignmentSorted environment.variableTyping environment.constantTyping rho names reading.names_distinct
    reading.names_above reading.assignment
    (fun offset _ {_} index => fresh _ sourceAfter offset index)
    (fun offset _ {_} index => fresh _ workAfter offset index)
    (fun offset _ {_} index => fresh _ temporaryAfter offset index) reading.logical reading.formation reading.logical_read reading.formation_read
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
  exact result

#print axioms ContextualReading.rebind_admitted
theorem ContextualReading.universalElimination_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain : Ty Unit} (argument : Term Symbol gamma domain) (body : Formula Symbol (domain :: gamma))
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext (signature := signature) (layout := layout)) (hypotheses := [])
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (.all body)))))
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {premiseFuel : Nat}
    (premiseAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt premiseFuel names
      premise.val (.imp reading.logical.formula (HOL.rename rho (.all body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding environment argument body fits active before premise).val
      (.imp reading.logical.formula (HOL.rename rho (instantiate argument body)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have dictionaryFresh (location : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial location) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + location) = none
    rw [Nat.add_comm]
    rfl
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  let compiled := HOLKernelSourceInstantiation.canonicalUniversalElimination signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise
  have admitted := HOLKernelSourceInstantiationReadback.canonicalUniversalElimination_admitted signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound reading.base reading.constant
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _)
    reading.logical reading.formation reading.logical_read reading.formation_read bounded.projection
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
    (by simpa only [HOL.rename] using premiseAdmitted)
  have witnessEq :
      (HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding environment argument body fits active before premise).val = compiled.val := rfl
  rw [witnessEq]
  simpa only [HOL.rename] using admitted

#print axioms ContextualReading.universalElimination_admitted

theorem ContextualReading.existentialIntroduction_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain : Ty Unit} (argument : Term Symbol gamma domain) (body : Formula Symbol (domain :: gamma))
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext (signature := signature) (layout := layout)) (hypotheses := [])
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (instantiate argument body)))))
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {premiseFuel : Nat}
    (premiseAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt premiseFuel names
      premise.val (.imp reading.logical.formula (HOL.rename rho (instantiate argument body)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding environment argument body fits active before premise).val
      (.imp reading.logical.formula (HOL.rename rho (.ex body)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have dictionaryFresh (location : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial location) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + location) = none
    rw [Nat.add_comm]
    rfl
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  let compiled := HOLKernelSourceInstantiation.canonicalExistentialIntroduction signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise
  have admitted := HOLKernelSourceInstantiationReadback.canonicalExistentialIntroduction_admitted signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound reading.base reading.constant
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _)
    reading.logical reading.formation reading.logical_read reading.formation_read bounded.projection
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
    (by simpa only [HOL.rename] using premiseAdmitted)
  have witnessEq :
      (HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding environment argument body fits active before premise).val = compiled.val := rfl
  rw [witnessEq]
  simpa only [HOL.rename] using admitted

#print axioms ContextualReading.existentialIntroduction_admitted

theorem ContextualReading.beta_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain result : Ty Unit} (argument : Term Symbol gamma domain) (body : Term Symbol (domain :: gamma) result)
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.beta abbreviation profile structural typing rules binding environment argument body fits active before).val
      (.imp reading.logical.formula (HOL.rename rho (.eq (.app (.lam body) argument) (instantiate argument body))))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have dictionaryFresh (location : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial location) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + location) = none
    rw [Nat.add_comm]
    rfl
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  let equation := HOLKernelSourceInstantiation.canonicalBeta signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have resultFit : (Term.eq (.app (.lam body) argument) (instantiate argument body)).binderDepth ≤ layout.width := by
    simp only [Term.binderDepth, instantiate]
    omega
  obtain ⟨equationFuel, ⟨equationTree⟩⟩ := HOLKernelSourceInstantiationReadback.canonicalBeta_admitted signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment depth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => HOLKernelProofInstantiation.work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => HOLKernelProofInstantiation.temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping

    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound reading.base reading.constant
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _) reading.formation reading.formation_read ruleAt bindingAt selected structuralSelected bindingSelected
  have sourceTree : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt equationFuel names equation.val
      (.imp reading.formation.formula (HOL.rename rho (.eq (.app (.lam body) argument) (instantiate argument body)))) := by
    simpa only [HOL.rename] using equationTree
  have promoted := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names ruleAt bindingAt (structuralSelected .syl)
    environment.scope _ (holds_sorted signature _ (environment.encoded_sorted _ resultFit active before)) equation
    reading.logical.formula reading.formation.formula (HOL.rename rho (.eq (.app (.lam body) argument) (instantiate argument body)))
    reading.logical_formula reading.formation_formula (reading.assertion_formula distinct _) projectionTree sourceTree
  exact ⟨_, promoted⟩

#print axioms ContextualReading.beta_admitted

theorem ContextualReading.eta_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
      (.imp reading.logical.formula (HOL.rename rho (.eq (.lam (.app (HOL.weaken function) (.var .vz))) function)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  let inner := windows.bodyWindow function.binderDepth fits
  let etaSource : Term Symbol gamma (domain ⇒ result) := .lam (.app (HOL.weaken function) (.var .vz))
  have etaFits : etaSource.binderDepth ≤ layout.width := by
    simp only [etaSource, Term.binderDepth, HOL.weaken, Term.binderDepth_rename, Nat.max_zero]
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
      (layout.workDepth frame + 1) (HOL.weaken function) = workFunction at coherence
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
    _ _ (HOL.rename rho etaSource) (HOL.rename rho function) typeRead workEtaRead workFunctionRead
  have reductionRead : readFormulaIn abbreviation
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (HOLKernelInferenceRules.equality signature.symbol (encodeType signature.symbol encoding.base (domain ⇒ result))
          (encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
            environment.assignment (layout.workDepth frame) etaSource) workFunction))) =
      some (.imp reading.logical.formula (.eq (HOL.rename rho etaSource) (HOL.rename rho function))) := by
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
  have etaMeaning : HOL.rename rho etaSource =
      Term.lam (.app (HOL.weaken (σ := domain) (HOL.rename rho function)) (.var .vz)) := by
    simp only [etaSource, HOL.rename, ExtDerivation.rename_weaken, Rename.lift]
  let reductionTree : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7)
      7 ruleAt bindingAt 1 names nativeReduction.val (.imp reading.logical.formula (.eq (HOL.rename rho etaSource) (HOL.rename rho function))) := by
    have accepted := nativeReduction.property.eval
    rw [nativeReductionVal] at accepted
    rw [nativeReductionVal, etaMeaning]
    rw [etaMeaning] at reductionRead
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
    reading.logical (HOL.rename rho etaSource) (HOL.rename rho etaSource) (HOL.rename rho function) reading.logical_read typeRead sourceEtaRead workEtaRead workFunctionRead
    ruleAt bindingAt (selected .transitivity) beforeTree reductionTree
  obtain ⟨lastTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules names _ environment.scope.logical _ _ typeSorted
    environment.scope.logicalSorted sourceFunctionSorted workFunctionSorted afterEquation reading.logical (HOL.rename rho function) (HOL.rename rho function)
    reading.logical_read typeRead sourceFunctionRead workFunctionRead ruleAt bindingAt (selected .symmetry) afterTree
  let completed := HOLKernelInferenceProofs.Native.transitivity signature rules environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workFunctionSorted sourceFunctionSorted first last
  have witnessEq : (HOLKernelProofExtensionality.eta profile structural typing rules binding environment function fits active before).val = completed.val := rfl
  rw [witnessEq]
  refine ⟨max (max beforeFuel 1 + 1) (afterFuel + 1) + 1, ?_⟩
  simpa only [etaSource, HOL.rename] using HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules names environment.scope.logical _ _ _ _
    environment.scope.logicalSorted typeSorted sourceEtaSorted workFunctionSorted sourceFunctionSorted first last
    reading.logical (HOL.rename rho etaSource) (HOL.rename rho function) (HOL.rename rho function) reading.logical_read typeRead sourceEtaRead workFunctionRead sourceFunctionRead
    ruleAt bindingAt (selected .transitivity) firstTree lastTree


#print axioms ContextualReading.eta_admitted
theorem ContextualReading.functionExtensionality_admitted (reading : ContextualReading abbreviation profile environment rho names)
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
        (environment.encode (.all (.eq (.app (HOL.weaken first) (.var .vz)) (.app (HOL.weaken second) (.var .vz))))))))
    (scope : InScope 7 names (layout.workDepth frame))
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
      pointwise.val (.imp (HOL.weaken (σ := domain) reading.logical.formula)
        (.all (.eq (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho first))) (.var .vz))
          (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho second))) (.var .vz)))))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofExtensionality.functionExtensionality abbreviation profile structural typing rules binding environment first second fits active before pointwise).val
      (.imp reading.logical.formula (HOL.rename rho (.eq first second)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  let inner := windows.bodyWindow (max first.binderDepth second.binderDepth) fits
  let source : Formula Symbol gamma := .all (.eq (.app (HOL.weaken first) (.var .vz)) (.app (HOL.weaken second) (.var .vz)))
  have sourceFit : source.binderDepth ≤ layout.width := by
    simpa only [source, Term.binderDepth, HOL.weaken, Term.binderDepth_rename, Nat.max_zero] using fits
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
      (layout.workDepth frame + 1) (HOL.weaken first) = firstWork at firstCoherence
  change encodeWithAssignment signature.symbol encoding.base encoding.constant (Layout.names initial)
      (Assignment.extend (.var (Layout.names initial (layout.workDepth frame))) environment.assignment)
      (layout.workDepth frame + 1) (HOL.weaken second) = secondWork at secondCoherence
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
  have tempAfterWork : layout.workDepth frame ≤ layout.temporaryDepth frame := by simp only [Layout.temporaryDepth]; omega
  have fresh (level : Nat) (later : layout.workDepth frame ≤ level) : Layout.names initial level ∉ names.toList := by
    intro member
    have upper := (scope.2 _ member).2
    change 7 + level < 7 + layout.workDepth frame at upper
    omega
  have dictionaryFresh (level : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial level) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + level) = none
    rw [Nat.add_comm]
    rfl
  let argumentNames : Names (domain :: target) := BinderNames.cons (Layout.names initial (layout.temporaryDepth frame)) names
  let shift : Rename Unit target (domain :: target) := Rename.weaken
  let liftedRho : Rename Unit gamma (domain :: target) := fun index => Var.vs (rho index)
  have argumentLookup : LookupPreserving HOLKernelSetOperationReadback.readConstant shift names argumentNames :=
    LookupPreserving.weaken HOLKernelSetOperationReadback.readConstant names domain _
      (BinderNames.lookup?_none_of_not_mem names (fresh _ tempAfterWork)) (dictionaryFresh _)
  have argumentNodup : argumentNames.toList.Nodup := List.nodup_cons.mpr ⟨fresh _ tempAfterWork, reading.names_distinct⟩
  have argumentAbove : ∀ name ∈ argumentNames.toList, 7 ≤ name := by
    intro name member
    rcases List.mem_cons.mp member with rfl | old
    · change 7 ≤ 7 + _; omega
    · exact reading.names_above _ old
  have argumentAssignment : ∀ {type} (index : Var gamma type), environment.assignment index = .var (argumentNames.nameOf (liftedRho index)) := reading.assignment
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
    environment.variableTyping environment.constantTyping liftedRho argumentNames argumentNodup argumentAbove argumentAssignment
    (by intro offset _ type index same; have upper := reading.source_before index; change 7 + (depth + offset) = names.nameOf (rho index) at same; omega)
    (by intro offset _ type index same; have upper := reading.source_before index; change 7 + (layout.workDepth frame + offset) = names.nameOf (rho index) at same; omega)
    (by intro offset _ type index same; have upper := reading.source_before index; change 7 + (layout.temporaryDepth frame + offset) = names.nameOf (rho index) at same; omega)
    (reading.logical.rename shift) (reading.formation.rename shift) argumentLogicalRead argumentFormationRead
    ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming)
    (by simpa only [Judgment.rename_formula, HOL.rename, shift, HOL.weaken] using projectionAtArgument)
  have sourceRead := reading.term_read_at distinct source depth (Nat.le_refl _)
  have workSourceRead := reading.term_read_at distinct source (layout.workDepth frame) workAfter
  have sourceReadAtArgument := logical_reader_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ (HOL.rename rho source) sourceRead
  have workSourceReadAtArgument := logical_reader_rename_of_read profile HOLKernelSetOperationReadback.readConstant 7 names argumentNames shift argumentLookup _ (HOL.rename rho source) workSourceRead
  have shiftedSource : HOL.rename shift (HOL.rename rho source) =
      Term.all (.eq (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho first))) (.var .vz))
        (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho second))) (.var .vz))) := by
    simp only [source, HOL.rename, ExtDerivation.rename_weaken, Rename.lift]
    rfl
  obtain ⟨carriedTree⟩ := HOLKernelCongruenceReadback.booleanEqualityElimination_admitted signature abbreviation profile distinct
    HOLKernelSetOperationReadback.readConstant 7 rules argumentNames environment.scope.logical _ _ environment.scope.logicalSorted
    (environment.encoded_sorted source sourceFit active before) workSourceSorted quantifierEquation pointwise
    (reading.logical.rename shift) (HOL.rename shift (HOL.rename rho source)) (HOL.rename shift (HOL.rename rho source)) argumentLogicalRead sourceReadAtArgument workSourceReadAtArgument
    ruleAt bindingAt (selected .booleanEqualityElimination)
    (by simpa only [rename_comp, liftedRho, shift, Rename.weaken] using quantifierTree)
    (by simpa only [Judgment.rename_formula, shiftedSource, shift, HOL.weaken] using pointwiseAdmitted)
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
      (.imp (HOL.weaken (σ := domain) reading.logical.formula)
        (.all (.eq (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho first))) (.var .vz))
          (.app (HOL.weaken (σ := domain) (HOL.weaken (σ := domain) (HOL.rename rho second))) (.var .vz))))) := by
    rw [nativePointwiseVal]
    simpa only [Judgment.rename_formula, shiftedSource, shift, HOL.weaken] using carriedTree
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
  have freshName (level : Nat) (later : layout.workDepth frame ≤ level) : HOLKernelBindingInterpretation.freshName 7 names (Layout.names initial level) = true := by
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
    firstTyping secondTyping nativePointwise distinct HOLKernelSetOperationReadback.readConstant 7 names domain result (HOL.rename rho first) (HOL.rename rho second) reading.logical
    reading.logical_read (typeRead domain) (typeRead result) firstWorkRead secondWorkRead (freshName _ (Nat.le_refl _)) (freshName _ tempAfterWork)
    (dictionaryFresh _) (dictionaryFresh _) ruleAt bindingAt selected structuralSelected bindingSelected nativePointwiseTree
  obtain ⟨firstFuel, ⟨firstTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding first inner firstFit (Nat.le_refl _)
    (by change depth ≤ layout.workDepth frame + 1; omega) tempAfter ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming) ⟨projectionFuel, ⟨projectionTree⟩⟩
  obtain ⟨secondFuel, ⟨secondTree⟩⟩ := reading.rebind_admitted distinct structural typing rules binding second inner secondFit (Nat.le_refl _)
    (by change depth ≤ layout.workDepth frame + 1; omega) tempAfter ruleAt bindingAt selected (structuralSelected .syl) (bindingSelected .abstractionRenaming) ⟨projectionFuel, ⟨projectionTree⟩⟩
  obtain ⟨backwardTree⟩ := HOLKernelCongruenceReadback.symmetry_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names _ environment.scope.logical _ _ typeSorted environment.scope.logicalSorted secondSourceSorted secondWorkSorted secondEquation
    reading.logical (HOL.rename rho second) (HOL.rename rho second) reading.logical_read (typeRead _) secondSourceRead secondWorkRead ruleAt bindingAt (selected .symmetry) secondTree
  obtain ⟨joinedTree⟩ := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names environment.scope.logical _ _ _ _ environment.scope.logicalSorted typeSorted firstSourceSorted firstWorkSorted secondWorkSorted firstEquation native
    reading.logical (HOL.rename rho first) (HOL.rename rho first) (HOL.rename rho second) reading.logical_read (typeRead _) firstSourceRead firstWorkRead secondWorkRead ruleAt bindingAt (selected .transitivity) firstTree nativeTree
  have finalTree := HOLKernelCongruenceReadback.transitivity_admitted signature abbreviation profile distinct HOLKernelSetOperationReadback.readConstant 7
    rules names environment.scope.logical _ _ _ _ environment.scope.logicalSorted typeSorted firstSourceSorted secondWorkSorted secondSourceSorted joined backward
    reading.logical (HOL.rename rho first) (HOL.rename rho second) (HOL.rename rho second) reading.logical_read (typeRead _) firstSourceRead secondWorkRead secondSourceRead ruleAt bindingAt (selected .transitivity) joinedTree backwardTree
  simpa only [HOL.rename] using (show ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
    (HOLKernelProofExtensionality.functionExtensionality abbreviation profile structural typing rules binding environment first second fits active before pointwise).val
    (.imp reading.logical.formula (.eq (HOL.rename rho first) (HOL.rename rho second)))) from ⟨_, finalTree⟩)


#print axioms ContextualReading.functionExtensionality_admitted
theorem ContextualReading.universalIntroduction_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain : Ty Unit} (body : Formula Symbol (domain :: gamma))
    (fits : body.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (bodyProof : HOLKernelProofCompilation.Conclusion
      (environment.bind abbreviation profile structural typing rules binding domain active before) body)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    {bodyFuel : Nat}
    (bodyAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.workDepth frame)) names)
      bodyProof.val (.imp (.and (HOL.weaken (σ := domain) reading.logical.formula) .top) (HOL.rename (Rename.lift rho) body))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelSourceBinding.universalIntroduction signature abbreviation profile structural typing rules binding
        encoding.base encoding.constant (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) encoding.baseSorted encoding.constantSorted
        (Layout.names_injective _) (Layout.names_injective _) encoding.baseIndependent encoding.baseIndependent
        body environment.assignment environment.scope (environment.windows active before) fits
        (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping bodyProof).val
      (.imp reading.logical.formula (HOL.rename rho (.all body)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have admitted := HOLKernelSourceBindingReadback.universalIntroduction_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant (Layout.names initial) (Layout.names initial)
    encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent
    body environment.assignment environment.scope windows fits (environment.logicalIndependent _ before)
    environment.assignmentSorted environment.variableTyping environment.constantTyping bodyProof rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    reading.logical reading.formation reading.logical_read reading.formation_read
    ruleAt bindingAt selected (structuralSelected .syl) bindingSelected projectionTree bodyAdmitted
  simpa only [HOL.rename] using admitted

#print axioms ContextualReading.universalIntroduction_admitted

theorem ContextualReading.abstractionCongruence_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain result : Ty Unit} (first second : Term Symbol (domain :: gamma) result)
    (fits : max first.binderDepth second.binderDepth + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (bodyProof : HOLKernelProofCompilation.Conclusion
      (environment.bind abbreviation profile structural typing rules binding domain active before) (.eq first second))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    {bodyFuel : Nat}
    (bodyAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.workDepth frame)) names)
      bodyProof.val (.imp (.and (HOL.weaken (σ := domain) reading.logical.formula) .top) (.eq (HOL.rename (Rename.lift rho) first) (HOL.rename (Rename.lift rho) second)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelSourceBinding.abstractionCongruence signature profile structural typing rules binding
        encoding.base encoding.constant (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) encoding.baseSorted encoding.constantSorted
        (Layout.names_injective _) (Layout.names_injective _) encoding.baseIndependent encoding.baseIndependent
        first second environment.assignment environment.scope (environment.windows active before) fits
        (environment.logicalIndependent _ before) environment.assignmentSorted environment.variableTyping environment.constantTyping bodyProof).val
      (.imp reading.logical.formula (HOL.rename rho (.eq (.lam first) (.lam second))))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have admitted := HOLKernelSourceBindingReadback.abstractionCongruence_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant (Layout.names initial) (Layout.names initial)
    encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent
    first second environment.assignment environment.scope windows fits (environment.logicalIndependent _ before)
    environment.assignmentSorted environment.variableTyping environment.constantTyping bodyProof rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    reading.logical reading.formation reading.logical_read reading.formation_read
    ruleAt bindingAt selected (structuralSelected .syl) bindingSelected projectionTree bodyAdmitted
  simpa only [HOL.rename] using admitted

#print axioms ContextualReading.abstractionCongruence_admitted

theorem ContextualReading.existentialElimination_admitted (reading : ContextualReading abbreviation profile environment rho names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain : Ty Unit} (body : Formula Symbol (domain :: gamma)) (result : Formula Symbol gamma)
    (fits : max (body.binderDepth + 1) (result.binderDepth + 1) ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (scope : InScope 7 names (layout.workDepth frame))
    (sourceWindow : ∀ offset < layout.width, 7 + (depth + offset) ∉ names.toList)
    (existsProof : HOLKernelProofCompilation.Conclusion environment (.ex body))
    (bodyProof : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext (signature := signature) (layout := layout)) (hypotheses := [])
      (entails signature.symbol
        (conjunction signature.symbol (environment.bind abbreviation profile structural typing rules binding domain active before).scope.logical
          (holds signature.symbol ((environment.bind abbreviation profile structural typing rules binding domain active before).encode body)))
        (holds signature.symbol ((environment.bind abbreviation profile structural typing rules binding domain active before).encode (HOL.weaken (σ := domain) result)))))
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {existsFuel bodyFuel : Nat}
    (existsAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt existsFuel names
      existsProof.val (.imp reading.logical.formula (HOL.rename rho (.ex body))))
    (bodyAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt bodyFuel
      (BinderNames.cons (type := domain) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids) (layout.workDepth frame)) names)
      bodyProof.val (.imp (.and (.and (HOL.weaken (σ := domain) reading.logical.formula) .top) (HOL.rename (Rename.lift rho) body))
        (HOL.weaken (σ := domain) (HOL.rename rho result)))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelSourceBinding.existentialElimination signature abbreviation profile structural typing rules binding
        encoding.base encoding.constant (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) (Layout.names (HOLKernelSetOperationInterpretation.initialContext signature.ids)) encoding.baseSorted encoding.constantSorted
        (Layout.names_injective _) (Layout.names_injective _) encoding.baseIndependent encoding.baseIndependent
        body result environment.assignment environment.scope (environment.windows active before) fits (environment.logicalIndependent _ before)
        (environment.assignmentIndependent _ (by change depth ≤ layout.workDepth frame; omega)) (encoding.constantIndependent _)
        (by intro offset less same; have equal := Layout.names_injective _ same; change layout.workDepth frame = depth + offset at equal; omega)
        environment.assignmentSorted environment.variableTyping environment.constantTyping existsProof bodyProof).val
      (.imp reading.logical.formula (HOL.rename rho result))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  let windows := environment.windows active before
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, layout.workDepth frame ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (scope.2 _ member).2
    change 7 + (location + offset) < 7 + layout.workDepth frame at upper
    omega
  have bodyFit : body.binderDepth + 1 ≤ layout.width := by omega
  have resultFit : result.binderDepth + 1 ≤ layout.width := by omega
  have admitted := HOLKernelSourceBindingReadback.existentialElimination_admitted signature abbreviation profile structural typing rules binding
    distinct HOLKernelSetOperationReadback.readConstant HOLKernelSetOperationInterpretation.symbolIndex 7
    HOLKernelSetOperationReadback.readConstant_symbol HOLKernelSetOperationReadback.symbolIndex_bound
    encoding.base encoding.constant reading.base reading.constant (Layout.names initial) (Layout.names initial)
    encoding.baseSorted encoding.constantSorted (Layout.names_injective _) (Layout.names_injective _)
    (by intro level; change 7 ≤ 7 + level; omega) (by intro level; change 7 ≤ 7 + level; omega)
    encoding.baseIndependent encoding.baseIndependent
    body result environment.assignment environment.scope windows fits (environment.logicalIndependent _ before)
    (environment.assignmentIndependent _ (by change depth ≤ layout.workDepth frame; omega)) (encoding.constantIndependent _)
    (by intro offset less same; have equal := Layout.names_injective initial same; change layout.workDepth frame = depth + offset at equal; omega)
    environment.assignmentSorted environment.variableTyping environment.constantTyping existsProof bodyProof rho names reading.names_distinct reading.names_above reading.assignment
    (fun offset less => sourceWindow offset (by omega))
    (fun offset _ => fresh (layout.workDepth frame) (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    reading.logical reading.formation reading.logical_read reading.formation_read
    (environment.scope_varsBelow (layout.workDepth frame) before bounded)
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
    (by simpa only [HOL.rename] using existsAdmitted) bodyAdmitted
  exact admitted

#print axioms ContextualReading.existentialElimination_admitted
end Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback

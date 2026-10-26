import Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback
import Mettapedia.Languages.MM0.HOLKernelProofInstantiation
import Mettapedia.Languages.MM0.HOLKernelSourceInstantiationReadback

/-!
# Independent admission of allocated native instantiation receipts

The actual allocated beta, SPEC and EXISTS constructors preserve the exact
source conclusions under the retained logical antecedent. The existing layout
and environment supply both finite binder banks, native occurrence independence,
constant-dictionary separation and source-frame readings. Quantified inference
also retains the raw bound on the environment's projection receipt when moving
that receipt into the fresh binder frame.

The theorems consume independently admitted premise certificates and the actual
formation projection. They specialize the shared canonical instantiation
results without changing the producer or the admission grammar.
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
theorem Reading.universalElimination_admitted (reading : Reading abbreviation profile environment names)
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
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {premiseFuel : Nat}
    (premiseAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt premiseFuel names
      premise.val (.imp reading.logical.formula (.all body))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding environment argument body fits active before premise).val
      (.imp reading.logical.formula (instantiate argument body))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, depth ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (reading.names_in_scope.2 _ member).2
    change 7 + (location + offset) < 7 + depth at upper
    omega
  have dictionaryFresh (location : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial location) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + location) = none
    rw [Nat.add_comm]
    rfl
  have liftedIdentity : (Rename.lift (Rename.id : Rename Unit gamma gamma) : Rename Unit (domain :: gamma) (domain :: gamma)) = @Rename.id Unit (domain :: gamma) := by
    funext type index
    cases index <;> rfl
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
    Rename.id names reading.names_in_scope.1 (fun name member => (reading.names_in_scope.2 name member).1) reading.assignment
    (fun offset _ => fresh depth (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _)
    reading.logical reading.formation reading.logical_read reading.formation_read bounded.projection
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
    (by simpa only [liftedIdentity, rename_id] using premiseAdmitted)
  have witnessEq :
      (HOLKernelProofInstantiation.universalElimination abbreviation profile structural typing rules binding environment argument body fits active before premise).val = compiled.val := rfl
  rw [witnessEq]
  simpa only [rename_id] using admitted

#print axioms Reading.universalElimination_admitted


theorem Reading.existentialIntroduction_admitted (reading : Reading abbreviation profile environment names)
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
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt)
    (bounded : environment.ProofsVarsBelow (7 + layout.workDepth frame))
    {premiseFuel : Nat}
    (premiseAdmitted : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt premiseFuel names
      premise.val (.imp reading.logical.formula (instantiate argument body))) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding environment argument body fits active before premise).val
      (.imp reading.logical.formula (.ex body))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, depth ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (reading.names_in_scope.2 _ member).2
    change 7 + (location + offset) < 7 + depth at upper
    omega
  have dictionaryFresh (location : Nat) : HOLKernelSetOperationReadback.readConstant (Layout.names initial location) = none := by
    change HOLKernelSetOperationReadback.readConstant (7 + location) = none
    rw [Nat.add_comm]
    rfl
  have liftedIdentity : (Rename.lift (Rename.id : Rename Unit gamma gamma) : Rename Unit (domain :: gamma) (domain :: gamma)) = @Rename.id Unit (domain :: gamma) := by
    funext type index
    cases index <;> rfl
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
    Rename.id names reading.names_in_scope.1 (fun name member => (reading.names_in_scope.2 name member).1) reading.assignment
    (fun offset _ => fresh depth (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _)
    reading.logical reading.formation reading.logical_read reading.formation_read bounded.projection
    ruleAt bindingAt selected structuralSelected bindingSelected projectionTree
    (by simpa only [rename_id] using premiseAdmitted)
  have witnessEq :
      (HOLKernelProofInstantiation.existentialIntroduction abbreviation profile structural typing rules binding environment argument body fits active before premise).val = compiled.val := rfl
  rw [witnessEq]
  simpa only [liftedIdentity, rename_id] using admitted

#print axioms Reading.existentialIntroduction_admitted

theorem Reading.beta_admitted (reading : Reading abbreviation profile environment names)
    (distinct : ∀ symbol, signature.symbol symbol ≠ abbreviation.reference)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    {domain result : Ty Unit} (argument : Term Symbol gamma domain) (body : Term Symbol (domain :: gamma) result)
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : depth + layout.width ≤ layout.workDepth frame)
    (ruleAt : Nat → Option Rule) (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (selected : ∀ rule, ruleAt (rules.index rule) = some (.inference rule))
    (structuralSelected : ∀ rule, ruleAt (structural.index rule) = some (.structural rule))
    (bindingSelected : ∀ rule, bindingAt (binding.index rule) = some rule)
    (projection : reading.ProjectionAdmitted ruleAt bindingAt) :
    ∃ fuel, Nonempty (AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt fuel names
      (HOLKernelProofInstantiation.beta abbreviation profile structural typing rules binding environment argument body fits active before).val
      (.imp reading.logical.formula (.eq (.app (.lam body) argument) (instantiate argument body)))) := by
  let initial := HOLKernelSetOperationInterpretation.initialContext signature.ids
  obtain ⟨projectionFuel, ⟨projectionTree⟩⟩ := projection
  have fresh : ∀ location, depth ≤ location → ∀ offset, Layout.names initial (location + offset) ∉ names.toList := by
    intro location later offset member
    have upper := (reading.names_in_scope.2 _ member).2
    change 7 + (location + offset) < 7 + depth at upper
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
    Rename.id names reading.names_in_scope.1 (fun name member => (reading.names_in_scope.2 name member).1) reading.assignment
    (fun offset _ => fresh depth (Nat.le_refl _) offset)
    (fun offset _ => fresh (layout.workDepth frame) (by omega) offset)
    (fun offset _ => fresh (layout.temporaryDepth frame) (by simp only [Layout.temporaryDepth]; omega) offset)
    (fun offset _ => dictionaryFresh _) reading.formation reading.formation_read ruleAt bindingAt selected structuralSelected bindingSelected
  have sourceTree : AdmittedProof abbreviation theorems (NativeContext (signature := signature) (layout := layout))
      (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 ruleAt bindingAt equationFuel names equation.val
      (.imp reading.formation.formula (.eq (.app (.lam body) argument) (instantiate argument body))) := by
    simpa only [rename_id] using equationTree
  have promoted := HOLKernelStructuralReadback.promote_admitted signature abbreviation (distinct .im) structural
    (HOLKernelLogicalFunctionReadback.reader profile HOLKernelSetOperationReadback.readConstant 7) 7 names ruleAt bindingAt (structuralSelected .syl)
    environment.scope _ (holds_sorted signature _ (environment.encoded_sorted _ resultFit active before)) equation
    reading.logical.formula reading.formation.formula (.eq (.app (.lam body) argument) (instantiate argument body))
    reading.logical_formula reading.formation_formula (reading.assertion_formula distinct _) projectionTree sourceTree
  exact ⟨_, promoted⟩

#print axioms Reading.beta_admitted

end Mettapedia.Languages.MM0.HOLKernelEnvironmentReadback

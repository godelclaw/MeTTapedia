import Mettapedia.Languages.MM0.HOLKernelProofEnvironment
import Mettapedia.Languages.MM0.HOLKernelSourceInstantiation

/-!
# Source instantiation in an allocated HOL proof environment

The allocated work root and temporary bank supply the occurrence independence
needed by the maintained SPEC, EXISTS and beta rules. Equations are constructed
in the formation context and then promoted through the retained logical
assumptions. The returned statements use the original source encoding.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelProofInstantiation
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

theorem equation_independent
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain : Ty Base} (argument : Term Const gamma domain) (fits : argument.binderDepth ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (offset : Nat) (later : sourceDepth + layout.width ≤ offset) (different : offset ≠ layout.workDepth frame) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial offset)
      (conjunction signature.symbol environment.scope.formation
        (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol
          (encodeType signature.symbol encoding.base domain) (.var (Layout.names initial (layout.workDepth frame)))
          (environment.encode argument)))) := by
  apply HOLKernelTypeSupport.substitutionContext_independent
  · exact environment.formationIndependent offset (by omega)
  · exact HOLKernelTypeSupport.encodeType_independent _ _ signature.symbol encoding.base (encoding.baseIndependent offset) domain
  · apply HOLKernelTypeSupport.boundVariable_independent _ _ _ signature.ids.object
    · simpa only [Nat.add_zero] using layout.workSlots initial signature.ids.object active 0 (by omega)
    · intro same
      exact different (Layout.names_injective initial same)
  · exact environment.encoded_independent argument fits active before offset later

theorem work_equation_independent
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain : Ty Base} (argument : Term Const gamma domain) (fits : argument.binderDepth ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (offset : Nat) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial (layout.workDepth frame + 1 + offset))
      (conjunction signature.symbol environment.scope.formation
        (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol
          (encodeType signature.symbol encoding.base domain) (.var (Layout.names initial (layout.workDepth frame)))
          (environment.encode argument)))) :=
  equation_independent environment argument fits active before _ (by omega) (by omega)

theorem temporary_equation_independent
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain : Ty Base} (argument : Term Const gamma domain) (fits : argument.binderDepth ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (offset : Nat) :
    ¬ Preterm.HasVar (NativeContext signature layout initial) (Layout.names initial (layout.temporaryDepth frame + offset))
      (conjunction signature.symbol environment.scope.formation
        (holds signature.symbol (HOLKernelInferenceRules.equality signature.symbol
          (encodeType signature.symbol encoding.base domain) (.var (Layout.names initial (layout.workDepth frame)))
          (environment.encode argument)))) :=
  equation_independent environment argument fits active before _
    (by simp only [Layout.temporaryDepth]; omega) (by simp only [Layout.temporaryDepth]; omega)

def universalElimination
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain : Ty Base} (argument : Term Const gamma domain) (body : Formula Const (domain :: gamma))
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (.all body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (instantiate argument body)))) := by
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  exact HOLKernelSourceInstantiation.canonicalUniversalElimination signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment sourceDepth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise

def existentialIntroduction
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain : Ty Base} (argument : Term Const gamma domain) (body : Formula Const (domain :: gamma))
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame)
    (premise : CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (instantiate argument body))))) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol (environment.encode (.ex body)))) := by
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  exact HOLKernelSourceInstantiation.canonicalExistentialIntroduction signature abbreviation profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment sourceDepth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope (environment.logicalIndependent _ before) environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping premise

def beta
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : HOLKernelTypingRules.Rules theorems signature.symbol signature.ids)
    (rules : HOLKernelInferenceRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (binding : HOLKernelBindingRules.Rules theorems signature.symbol signature.ids abbreviation.reference)
    (environment : Environment (definitions := definitions) (theorems := theorems) (hypotheses := hypotheses)
      encoding gamma assumptions sourceDepth)
    {domain result : Ty Base} (argument : Term Const gamma domain) (body : Term Const (domain :: gamma) result)
    (fits : body.binderDepth + Subst.maxBinderDepth (Subst.single argument) + 1 ≤ layout.width)
    {frame : Nat} (active : frame < layout.frames) (before : sourceDepth + layout.width ≤ layout.workDepth frame) :
    CheckedProof (terms := terms) (definitions := definitions) (theorems := theorems)
      (context := NativeContext signature layout initial) (hypotheses := hypotheses)
      (entails signature.symbol environment.scope.logical (holds signature.symbol
        (environment.encode (.eq (.app (.lam body) argument) (instantiate argument body))))) := by
  have argumentHeight := Subst.binderDepth_le_maxBinderDepth (Subst.single argument) .vz
  change argument.binderDepth ≤ Subst.maxBinderDepth (Subst.single argument) at argumentHeight
  have argumentFit : argument.binderDepth ≤ layout.width := by omega
  let windows := environment.windows active before
  let equation := HOLKernelSourceInstantiation.canonicalBeta signature profile structural typing rules binding
    encoding.base encoding.constant (Layout.names initial) (Layout.names initial) encoding.baseSorted encoding.constantSorted
    (Layout.names_injective initial) (Layout.names_injective initial) encoding.baseIndependent encoding.baseIndependent
    argument body environment.assignment sourceDepth (layout.workDepth frame) (layout.temporaryDepth frame)
    environment.scope.formation environment.scope.formationSorted environment.assignmentSorted
    (fun offset smaller => windows.sourceSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workSlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporarySlots offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.sourceFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.workFresh offset (by change offset < layout.width; omega))
    (fun offset smaller => windows.temporaryFresh offset (by change offset < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.sourceDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (by intro first firstSmall second secondSmall; exact windows.workDisjoint first (by change first < layout.width; omega) second (by change second < layout.width; omega))
    (fun offset _ => work_equation_independent environment argument argumentFit active before offset)
    (fun offset _ => temporary_equation_independent environment argument argumentFit active before offset)
    environment.variableTyping environment.constantTyping
  have instanceHeight := Term.binderDepth_subst_le body (Subst.single argument)
  have resultFit : (Term.eq (.app (.lam body) argument) (instantiate argument body)).binderDepth ≤ layout.width := by
    simp only [Term.binderDepth, instantiate]
    omega
  exact environment.scope.promote signature structural _
    (holds_sorted signature _ (environment.encoded_sorted _ resultFit active before)) equation

#print axioms equation_independent
#print axioms work_equation_independent
#print axioms temporary_equation_independent
#print axioms universalElimination
#print axioms existentialIntroduction
#print axioms beta
end Mettapedia.Languages.MM0.HOLKernelProofInstantiation

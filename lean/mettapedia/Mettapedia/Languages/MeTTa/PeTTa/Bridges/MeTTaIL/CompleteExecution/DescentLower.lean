import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Scoped
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentReadout
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMatchingExecution

/-!
# Scoped operations in the descent machine's runtime

The scoped library's proved operations, lifted through the typed sites and the descent library.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding
open Effects (State)
open Eval
open BridgeKit WireKit

theorem descent_context_next_returns (state : State) (context : Context) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:context-next" [encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context)]) state
      (encoded (PremiseOperationsExecution.GeneralExecution.contextTerm context.next)) := by
  metta_lift descent_checked ["context"] (by metta_lift typed_checked ["context"] (context_next_returns state context))

theorem descent_scope_restore_returns (state : State) (parameter : String) (initial final : Assignment) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:scope-restore" [encoded (.string parameter), assignmentValue initial, assignmentValue final])
      state (assignmentValue (restoreParameter parameter initial final)) := by
  metta_lift descent_checked ["parameter", "initial", "final"]
    (by metta_lift typed_checked ["parameter", "initial", "final"]
      (scope_restore_returns state parameter initial final))

theorem descent_append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)]) state
      (encoded (encodeList element (left ++ right))) := by
  metta_lift descent_checked ["left", "right"]
    (by metta_lift typed_checked ["left", "right"] (automata_append_returns element state left right))

theorem descent_length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns descentLibrary.runtime [] state (apply "gslt:automata:length" [encoded (encodeList element items)])
      state (number items.length) := by
  metta_lift descent_checked ["items"] (by metta_lift typed_checked ["items"] (automata_length_returns element state items))

theorem descent_matcher_start_returns (state : State) (request : GeneralScopedMatchMachine.Request) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-matcher-start" [encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm request)])
      state (encoded (RuleInstantiationExecution.GeneralExecution.matcherStateTerm (GeneralScopedMatchMachine.start request))) := by
  metta_lower ["request"]
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Mechanical.start_returns [] state request _
      (by simp))

namespace Lowered

theorem selection (state : State) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:substitution-presentation"
        [encoded (PremiseOperationsExecution.GeneralExecution.reflectionTerm profile),
         encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)]) state
      (encoded (encodeOption InferenceCettaWire.AuthoredRule.reflectivePresentationTerm
        (ReflectiveSubstitution.substitutionPresentationForRule? profile rule))) := by
  metta_lower ["reflection", "rule"]
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers.selection_returns [] state profile rule (PremiseOperationsExecution.GeneralExecution.MatcherFrames.reflectionValue profile) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.ruleValue rule)
      (by simp))

theorem reduct (state : State) (profile : Reflection.ReflectionProfile) (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) (assignment : Assignment) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:rule:scope-reduct"
        [encoded (encodeOption InferenceCettaWire.AuthoredRule.reflectivePresentationTerm
          (ReflectiveSubstitution.substitutionPresentationForRule? profile rule)),
         encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
         encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), WireKit.number ambient,
         CompleteExecution.assignmentValue assignment]) state
      (encoded (encodeOption InferenceCettaWire.encodePattern
        (reductWith? (ScopedReflectiveExecution.binderOperation profile rule) rule spec ambient assignment))) := by
  metta_lower ["operation", "rule", "spec", "ambient", "completed"]
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers.reduct_returns [] state profile rule spec ambient assignment (PremiseOperationsExecution.GeneralExecution.MatcherFrames.selectionValue profile rule) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.ruleValue rule)
      (PremiseOperationsExecution.GeneralExecution.MatcherFrames.specValue spec) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.number ambient) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.assignmentValue assignment)
      (by simp))

theorem sorted (state : State) (language : LanguageDef) (free : List (String × TypeExpr)) (bound : List TypeExpr)
    (type : TypeExpr) (pattern : Pattern) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:open-well-sorted"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typingDeclarationTerm language.terms),
         encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free),
         encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound),
         encoded (InferenceCettaWire.AuthoredRule.typeTerm type), encoded (InferenceCettaWire.encodePattern pattern)])
      state (Effects.boolean (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted language
        (Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.ofList free) bound type pattern)) := by
  metta_lower ["declarations", "free", "bound", "type", "pattern"]
    (PremiseOperationsExecution.GeneralExecution.MatcherFrames.Checkers.sorted_returns [] state language free bound type pattern (PremiseOperationsExecution.GeneralExecution.MatcherFrames.declarationsValue language) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.freeValue free)
      (PremiseOperationsExecution.GeneralExecution.MatcherFrames.boundValue bound) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.typeValue type) (PremiseOperationsExecution.GeneralExecution.MatcherFrames.patternValue pattern)
      (by simp))

end Lowered

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

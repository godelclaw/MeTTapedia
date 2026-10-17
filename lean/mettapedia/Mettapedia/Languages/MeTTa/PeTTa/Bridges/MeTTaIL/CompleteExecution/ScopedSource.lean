import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Positions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Scoped
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution

/-!
# Facts of the rule sources in the complete machine's runtime

The scoped library's runtime holds the scoped source's equations and declarations as they are,
so it agrees with that source on every head. The rule-job readout below it already carries the
proof of finishing a root firing at its site; it is closed under the heads that proof uses and
agrees with the scoped source on them, so its facts move up through the typed, descent and
complete libraries. Filling a context is proved here, in the scoped library.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program)
open Effects (State)
open Eval
open BridgeKit

/-- The scoped library's runtime agrees with the scoped source on every head. -/
theorem scoped_runtime_agreement (allowed : String → Bool) :
    ProgramAgreementOn allowed RuleExecutionProgram.scopedProgram scopedLibrary.runtime :=
  programAgreementOn_of_retained_rows _ _ _ rfl rfl

theorem readout_scoped_agreement : ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
    ScopedRuleJobReadoutExecution.runtime scopedLibrary.runtime :=
  agreement_trans PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
    (scoped_runtime_agreement _)

/-- A scoped-library fact about a call at values holds in the complete machine's runtime. -/
syntax "metta_raise " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_raise [$names,*] $fact) => `(tactic|
      metta_lift complete_checked [$names,*]
        (by metta_lift descent_checked [$names,*] (by metta_lift typed_checked [$names,*] $fact)))

/-- Raise a fact about a call at values from the rule-job readout. -/
syntax "metta_from_readout " " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_from_readout [$names,*] $fact) => `(tactic|
      metta_raise [$names,*]
        (transport_call ScopedRuleJobReadoutExecution.runtime_closed readout_scoped_agreement (by decide +kernel)
          (by decide) (by decide +kernel) (by decide) [$names,*] (by decide) rfl (by decide +kernel) $fact))

open Mettapedia.GSLT.LanguageDef InferenceCettaWire in
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts in
/-- `gslt:rule:scope-fill` fills a context. -/
theorem scoped_fill_returns (state : State) (pattern : Pattern) : ∀ context : OneHoleContext,
    PureReturns scopedLibrary.runtime [] state
      (WireKit.apply "gslt:rule:scope-fill" [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern))
  | .hole => by
    metta_call scoped_checked
    metta_eval unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill]
  | .apply head before inner after => by
    have joined := automata_append_returns encodePattern state before (inner.fill pattern :: after)
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner, joined] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern,
        encodePatterns_eq_encodeList, CettaWire.encodeList]
  | .lambda binder inner => by
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .multiLambda arity binders inner => by
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .substBody inner replacement => by
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .substReplacement body inner => by
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern]
  | .collection kind before inner after rest => by
    have joined := automata_append_returns encodePattern state before (inner.fill pattern :: after)
    metta_call scoped_checked
    metta_eval [scoped_fill_returns state pattern inner, joined] with scoped_checked
      unfolding [contextValue, patternValue, ContextObservation.contextTerm, OneHoleContext.fill, encodePattern,
        encodePatterns_eq_encodeList, CettaWire.encodeList]

open Mettapedia.GSLT.LanguageDef InferenceCettaWire in
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts in
/-- `gslt:rule:scope-fill`, in the complete machine's runtime. -/
theorem complete_fill_returns (state : State) (context : OneHoleContext) (pattern : Pattern) :
    PureReturns runtime [] state
      (WireKit.apply "gslt:rule:scope-fill" [contextValue context, patternValue pattern]) state
      (patternValue (context.fill pattern)) := by
  metta_raise ["context", "pattern"] (scoped_fill_returns state pattern context)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

import Mettapedia.OSLF.Framework.RhoScopeAssayReceipts
import Mettapedia.OSLF.Framework.RhoScopeDecisionControls

/-!
# Actual current-context refutation and a supplied future confirmation

The open name has no output-scope certificate. Substituting the supplied
two-output name changes its verdict and constructs a confirmation receipt.
The actual substitution readout is retained. Current complement guards and
their negative receipts therefore do not supply future-stable negation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeAssayFutureControls

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution
open RhoGeneratedScopeDecision RhoScopeMinimumReceipts RhoScopeAssayReceipts RhoScopeDecisionControls
open Mettapedia.GSLT.Causality.ComplementaryAssay

local instance outputAtomDecision (context : Ctx sig) : DecidablePred (outputAtom (context := context)) :=
  fun process => show Decidable (0 < RhoSourceOutputPredicate.count process) from inferInstance

def currentReceipt : DecisionReceipt outputAtom outputAtom currentName .refute :=
  Eq.mp (congrArg (DecisionReceipt outputAtom outputAtom currentName)
    (congrArg verdictOf current_open_name_rejected)) (decisionReceipt outputAtom outputAtom currentName)

def futureReceipt : DecisionReceipt outputAtom outputAtom futureName .confirm :=
  Eq.mp (congrArg (DecisionReceipt outputAtom outputAtom futureName)
    (congrArg verdictOf future_name_accepted)) (decisionReceipt outputAtom outputAtom futureName)

theorem actual_current_and_future_receipt_presence :
    minimumReceipt? outputAtom outputAtom currentName = none ∧
      (minimumReceipt? outputAtom outputAtom
        (model.substitution.substitute futureEnvironment currentName)).isSome = true := by
  constructor
  · exact (minimumReceipt?_none_iff _ _ _).mpr (decisionReceipt_sound currentReceipt)
  · rw [current_name_substitution]
    exact (minimumReceipt?_presence _ _ _).mpr (certificate_sound (positiveCertificate futureReceipt))

theorem current_exclusion_fails_at_the_supplied_future :
    ¬ generated outputAtom outputAtom currentName ∧
      generated outputAtom outputAtom (model.substitution.substitute futureEnvironment currentName) := by
  rw [current_name_substitution]
  exact ⟨decisionReceipt_sound currentReceipt, certificate_sound (positiveCertificate futureReceipt)⟩

end Mettapedia.OSLF.Framework.RhoScopeAssayFutureControls

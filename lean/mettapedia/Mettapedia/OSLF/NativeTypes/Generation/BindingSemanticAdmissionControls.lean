import Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
import Mettapedia.OSLF.NativeTypes.Generation.BindingArrowCounterexample
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-!
# Semantic parameter admission controls

The original authored presentations pass the same structural admission
algorithm. The ordinary-arrow counterexample passes native formation but is
refused by semantic admission. Mixed-sort nested binders retain their exact
innermost-first context order and complete source metadata.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem original_lambda_admitted :
    check Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language = true := by decide

theorem original_machine_admitted :
    check Mettapedia.Languages.PartrecMachine.partrecMachine = true := by decide

theorem original_letCase_admitted :
    check Mettapedia.OSLF.NativeTypes.Instances.LetCase.language = true := by decide

theorem ordinary_arrow_refused :
    check BindingCarrierSemantics.ArrowCounterexample.language = false := by decide

theorem ordinary_arrow_reason :
    issues BindingCarrierSemantics.ArrowCounterexample.language =
      [⟨0, 0, .simple "function" BindingCarrierSemantics.ArrowCounterexample.higher,
        .ordinaryArrowData⟩] := by decide

theorem mixed_binder_order :
    parameterMeaning? (.abstractionNamed (some "outer") "body"
      (.arrow (.base "Outer") (.arrow (.base "Inner") (.base "Result")))) =
      some (["Inner", "Outer"], "Result") := by decide

theorem higher_order_binder_refused :
    parameterMeaning? (.abstractionNamed (some "function") "body"
      (.arrow (.arrow (.base "A") (.base "A")) (.base "A"))) = none := by decide

theorem case_header_computed :
    headerSlots? Mettapedia.OSLF.NativeTypes.Instances.LetCase.language.terms[4] =
      some [([], "Value"), (["Value", "Value"], "Computation")] := by decide

end Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission.Controls

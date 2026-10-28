import Mettapedia.QuantumTheory.YangMills.ReflectionPositivityGateCanaries

/-!
# Yang-Mills reflection-positivity gate canary regression
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace ReflectionPositivityGateCanariesRegression

theorem functional_and_cone_bool_positive_canary_regression :
    toyYangMillsReflectionFunctionalAndConeAudit.ClearsGate = true :=
  yangMillsReflectionFunctionalAndCone_bool_positive_canary

theorem sample_flag_only_bool_negative_canary_regression :
    toyYangMillsReflectionSampleFlagOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.SampleFlagOnly = true := by
  exact yangMillsReflectionSampleFlagOnly_bool_negative_canary

theorem functional_only_bool_negative_canary_regression :
    toyYangMillsReflectionFunctionalOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionFunctionalOnlyAudit.Blocked = true := by
  exact yangMillsReflectionFunctionalOnly_bool_negative_canary

theorem cone_only_bool_negative_canary_regression :
    toyYangMillsReflectionConeOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionConeOnlyAudit.Blocked = true := by
  exact yangMillsReflectionConeOnly_bool_negative_canary

theorem reflection_positivity_bool_guardrails_regression :
    toyYangMillsReflectionFunctionalAndConeAudit.ClearsGate = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionSampleFlagOnlyAudit.SampleFlagOnly = true ∧
      toyYangMillsReflectionFunctionalOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionFunctionalOnlyAudit.Blocked = true ∧
      toyYangMillsReflectionConeOnlyAudit.ClearsGate = false ∧
      toyYangMillsReflectionConeOnlyAudit.Blocked = true := by
  exact yangMillsReflectionPositivity_bool_guardrails

theorem functional_and_cone_world_interfaces_clears_reflection_regression :
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces.missingFor
      .reflectionPositivity = [] := by
  exact
    toyYangMillsReflectionFunctionalAndConeWorldInterfaces_clears_reflectionPositivity

theorem functional_and_cone_world_interfaces_not_clears_all_regression :
    ¬ toyYangMillsReflectionFunctionalAndConeWorldInterfaces.ClearsAll := by
  exact toyYangMillsReflectionFunctionalAndConeWorldInterfaces_not_clearsAll

theorem functional_only_world_interfaces_missing_reflection_regression :
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveCone] := by
  exact
    toyYangMillsReflectionFunctionalOnlyWorldInterfaces_missing_reflectionPositivity

theorem cone_only_world_interfaces_missing_reflection_regression :
    toyYangMillsReflectionConeOnlyWorldInterfaces.missingFor
      .reflectionPositivity = [.reflectionPositiveFunctional] := by
  exact
    toyYangMillsReflectionConeOnlyWorldInterfaces_missing_reflectionPositivity

theorem reflection_positivity_canary_node_checked_regression :
    yangMillsReflectionPositivityCanaryNode.status = .checked :=
  yangMillsReflectionPositivityCanaryNode_checked

theorem current_reflection_positivity_canary_audit_packet_regression :
    currentYangMillsReflectionPositivityCanaryAuditPacket :=
  currentYangMillsReflectionPositivityCanaryAudit

end ReflectionPositivityGateCanariesRegression
end YangMills
end QuantumTheory
end Mettapedia

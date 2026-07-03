import Mettapedia.Computability.PNP.V13PhaseEScaled

/-!
# Regression checks for the scaled Phase E family
-/

namespace Mettapedia.Computability.PNP

#check phaseEScaledLockedInterface
#check phaseEScaled_seven_combinatorial_obligations
#check phaseEScaled_targetBlindPayloadObserver_hardCore
#check phaseEScaled_boundaryMixing_boundedClass
#check phaseEScaled_safeQSSM_boundedClass
#check phaseEScaled_kernelFlip_exactNeutrality_card
#check phaseEScaled_familyInadmissible_publicTargetTag
#check phaseEScaledObligationMap_length
#check phaseEScaledObligationMap_has_no_failures
#check phaseEScaledObligationMap_all_familyInadmissible
#check phaseEScaled_all_mapped_obligations

theorem phaseEScaledRegression_interface_nonempty (m k : Nat) :
    Nonempty
      (GaugeBufferedLockedInterface
        (PhaseEScaledWorld m k) (PhaseEScaledPublic m k)
        PhaseEScaledNeutral (PhaseEScaledSafe m k) (PhaseEScaledGauge m)
        Unit Unit Unit Unit Unit (PhaseEScaledPayload m k) Unit Unit Unit) := by
  exact ⟨phaseEScaledLockedInterface m k⟩

theorem phaseEScaledRegression_small_fixed_case :
    PhaseEScaledAllMappedObligations 2 3 :=
  phaseEScaled_all_mapped_obligations 2 3

#print axioms phaseEScaled_seven_combinatorial_obligations
#print axioms phaseEScaled_targetBlindPayloadObserver_hardCore
#print axioms phaseEScaled_boundaryMixing_boundedClass
#print axioms phaseEScaled_kernelFlip_exactNeutrality_card
#print axioms phaseEScaled_familyInadmissible_publicTargetTag
#print axioms phaseEScaledObligationMap_has_no_failures
#print axioms phaseEScaledObligationMap_all_familyInadmissible
#print axioms phaseEScaledRegression_interface_nonempty

end Mettapedia.Computability.PNP

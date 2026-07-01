import Mettapedia.Computability.PNP.V13ObserverLadder

/-!
# Regression checks for the Phase E observer ladder
-/

namespace Mettapedia.Computability.PNP

#check phaseEScaled_targetLockObserver_success_eq_one
#check phaseEScaled_noHitDecisionTree_success_eq_half
#check phaseEScaled_targetLockJunta_success_eq_one
#check phaseEScaled_targetBlindJunta_success_eq_half
#check phaseEScaled_targetParity_success_eq_one
#check phaseEScaled_targetBlindParity_success_eq_half
#check phaseEScaled_restriction_seed_residual_queries_zero
#check phaseEScaled_restriction_seed_collapsed_success_eq_half
#check PhaseEScaledSwitchingStatementNeeded
#check phaseEScaled_payloadDomination_iff_starSW
#check phaseEScaled_observer_ladder_mark

theorem phaseEScaledObserverLadderRegression_map_complete :
    phaseEScaledObserverLadderMap.length = 4 ∧
      (∀ row ∈ phaseEScaledObserverLadderMap,
        row.status = .exactHalf ∨ row.status = .checkedCounterexample ∨
          row.status = .pinnedHypothesis ∨ row.status = .iffHardCore) :=
  ⟨phaseEScaledObserverLadderMap_length,
    phaseEScaledObserverLadderMap_has_no_unlabeled_stop⟩

#print axioms phaseEScaled_targetLockObserver_success_eq_one
#print axioms phaseEScaled_noHitDecisionTree_success_eq_half
#print axioms phaseEScaled_targetLockJunta_success_eq_one
#print axioms phaseEScaled_targetBlindJunta_success_eq_half
#print axioms phaseEScaled_targetParity_success_eq_one
#print axioms phaseEScaled_targetBlindParity_success_eq_half
#print axioms phaseEScaled_restriction_seed_residual_queries_zero
#print axioms phaseEScaled_restriction_seed_collapsed_success_eq_half
#print axioms phaseEScaled_payloadDomination_iff_starSW
#print axioms phaseEScaled_observer_ladder_mark

end Mettapedia.Computability.PNP

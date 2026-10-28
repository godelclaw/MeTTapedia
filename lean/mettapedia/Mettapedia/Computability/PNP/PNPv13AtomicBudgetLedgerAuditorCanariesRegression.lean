import Mettapedia.Computability.PNP.PNPv13AtomicBudgetLedgerAuditorCanaries

/-!
# Regression checks for PNP v13 atomic-budget ledger auditor canaries
-/

namespace Mettapedia.Computability.PNP.PNPv13AtomicBudgetLedgerAuditorCanariesRegression

open Mettapedia.Computability.PNP

theorem atomic_budget_ledger_positive_canary_regression :
    atomicBudgetGoodLedger.ClearsAllStructuralChecks ∧
      atomicBudgetGoodLedger.atomBudget = 3 ∧
      atomicBudgetGoodLedger.coordinateSummedCost = 3 := by
  exact atomicBudgetLedger_lab_positive_canary

theorem atomic_budget_ledger_overcharge_negative_canary_regression :
    atomicBudgetOverchargeLedger.overchargedAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      atomicBudgetOverchargeLedger.atomBudget = 1 ∧
      atomicBudgetOverchargeLedger.coordinateSummedCost = 2 ∧
      ¬ atomicBudgetOverchargeLedger.NoDoubleCounting := by
  exact atomicBudgetLedger_overcharge_negative_canary

theorem atomic_budget_ledger_undercharge_negative_canary_regression :
    atomicBudgetUnderchargeLedger.missingPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      atomicBudgetUnderchargeLedger.missingResidualPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      ¬ atomicBudgetUnderchargeLedger.AllPositiveCostAtomsCharged := by
  exact atomicBudgetLedger_undercharge_negative_canary

theorem atomic_budget_ledger_cancellation_negative_canary_regression :
      atomicBudgetCancellationLedger.atomBudget = 2 ∧
      atomicBudgetCancellationLedger.coordinateSummedCost = 2 ∧
      atomicBudgetCancellationLedger.overchargedAtoms =
        [AtomicBudgetLedgerAtom.safeA] ∧
      atomicBudgetCancellationLedger.missingPositiveCostAtoms =
        [AtomicBudgetLedgerAtom.residualA] ∧
      ¬ atomicBudgetCancellationLedger.ClearsAllStructuralChecks := by
  exact atomicBudgetLedger_cancellation_negative_canary

theorem atomic_budget_ledger_stale_gauge_negative_canary_regression :
    atomicBudgetStaleGaugeLedger.staleGaugeCharges =
        [atomicBudgetChargeGaugeA .c0] ∧
      ¬ atomicBudgetStaleGaugeLedger.FreshGaugeOnly := by
  exact atomicBudgetLedger_staleGauge_negative_canary

theorem atomic_budget_ledger_incidence_negative_canary_regression :
    atomicBudgetIncidenceOverflowLedger.incidenceOverflowCoords =
        [AtomicBudgetLedgerCoord.c0] ∧
      ¬ atomicBudgetIncidenceOverflowLedger.BoundedIncidence := by
  exact atomicBudgetLedger_incidence_negative_canary

theorem atomic_budget_ledger_safe_budget_negative_canary_regression :
    atomicBudgetSafeBudgetOverflowLedger.safeBudgetExcess? =
        some ({ limit := 1, total := 2 } : AtomicBudgetSafeBudgetExcess) ∧
      ¬ atomicBudgetSafeBudgetOverflowLedger.SafeBudget := by
  exact atomicBudgetLedger_safeBudget_negative_canary

theorem atomic_budget_ledger_scalar_equality_not_structural_regression :
    atomicBudgetCancellationLedger.atomBudget =
        atomicBudgetCancellationLedger.coordinateSummedCost ∧
      ¬ atomicBudgetCancellationLedger.ClearsAllStructuralChecks := by
  exact
    atomicBudgetLedgerStructuralCanaries_separate_scalarEquality_from_structuralExactness

end Mettapedia.Computability.PNP.PNPv13AtomicBudgetLedgerAuditorCanariesRegression

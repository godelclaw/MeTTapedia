import Mettapedia.Computability.PNP.PNPv13TraceFactorizationCanaries

/-!
# Regression checks for PNP v13 trace-factorization canaries
-/

namespace Mettapedia.Computability.PNP.PNPv13TraceFactorizationCanariesRegression

open Mettapedia.Computability.PNP

theorem trace_factorization_identity_positive_canary_regression :
    traceFactorizationIdentitySurface.CapturesAllBoolObservers ∧
      traceFactorizationIdentitySurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver ∧
      traceFactorizationIdentitySurface.ObserverTraceDecodable
        traceFactorizationConstantObserver := by
  exact traceFactorizationIdentitySurface_lab_positive_canary

theorem trace_factorization_collapsed_conflict_negative_canary_regression :
    traceFactorizationCollapsedSurface.ObserverSameTraceConflict
        traceFactorizationSeparatingObserver ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  exact traceFactorizationCollapsed_conflictingObserver_negative_canary

theorem trace_factorization_collapsed_constant_guard_regression :
    traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationConstantObserver ∧
      ¬ traceFactorizationCollapsedSurface.CapturesAllBoolObservers := by
  exact traceFactorizationCollapsed_constantObserver_guard_canary

theorem trace_factorization_trace_assignment_negative_canary_regression :
    traceFactorizationCollapsedSurface.traceOf .left = .sharedTrace ∧
      traceFactorizationCollapsedSurface.traceOf .right = .sharedTrace ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  exact traceFactorizationCollapsed_traceAssignment_negative_canary

theorem trace_factorization_random_coin_negative_canary_regression :
    traceFactorizationCollapsedSurface.RandomObserverSameTraceConflict
        traceFactorizationRandomSeparatingObserver ∧
      ¬ traceFactorizationCollapsedSurface.RandomObserverTraceDecodable
        traceFactorizationRandomSeparatingObserver := by
  exact traceFactorizationCollapsed_randomCoin_negative_canary

theorem trace_factorization_trace_assignment_not_factorization_regression :
    traceFactorizationCollapsedSurface.traceOf .left = .sharedTrace ∧
      traceFactorizationCollapsedSurface.traceOf .right = .sharedTrace ∧
      traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationConstantObserver ∧
      ¬ traceFactorizationCollapsedSurface.ObserverTraceDecodable
        traceFactorizationSeparatingObserver := by
  exact traceFactorizationCanaries_separate_traceAssignment_from_factorization

end Mettapedia.Computability.PNP.PNPv13TraceFactorizationCanariesRegression

import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceEquationArchiveCompleteness
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceArchiveCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceAdjacencyCoverage
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceAdmissionState

/-!
# Completed executions construct their coverage certificate

Every generated equation and rule job is retained with its drained answer
readout. The reached representatives include the source and both neighbours
of every recorded equation edge. These invariants establish that the actual
certificate checker accepts a completed execution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

theorem completed_checkCertificate {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state)
    (completed : complete request state = true) :
    checkCertificate request state = true := by
  have idle := ((complete_iff request state).mp completed).1
  have root := settled_root_represented admitted reached idle
  have equations := completed_universeJobsChecked admitted reached completed
  have rules := completed_representedJobsChecked reached completed
  have adjacent := settled_adjacency_checked reached idle
  simp only [checkCertificate, completed, decide_eq_true root, equations, rules,
    adjacent, Bool.and_self]

theorem settled_resolved_checkCertificate {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state)
    (idle : settled request state = true) (resolved : state.unresolved = []) :
    checkCertificate request state = true := by
  apply completed_checkCertificate admitted reached
  exact settled_empty_complete
    (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete
      admitted.rootSorted) reached idle resolved

#print axioms completed_checkCertificate
#print axioms settled_resolved_checkCertificate

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

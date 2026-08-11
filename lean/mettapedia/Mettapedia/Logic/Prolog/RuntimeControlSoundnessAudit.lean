import Mettapedia.Logic.Prolog.RuntimeControlSoundness
import Mettapedia.Logic.Prolog.SourceRuntime
import Mettapedia.Logic.LP.RuntimeExceptionSoundness

/-!
# Trusted-base audit for canonical runtime grounding

These commands make the axiom dependencies of the executable conservation and
least-model endpoint visible in ordinary Lean build output.
-/

#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.stepCore_conserves
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.pullCore_conserves
#print axioms Mettapedia.Logic.LP.RuntimeQuery.branchStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.backtrackStep_branch_of_restore
#print axioms Mettapedia.Logic.LP.RuntimeQuery.cutStep_prunes_newest_branch
#print axioms Mettapedia.Logic.LP.RuntimeQuery.ifThenElseStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.emptyCurrentStep_commit_of_depth
#print axioms Mettapedia.Logic.LP.RuntimeQuery.softIfThenElseStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.backtrackStep_softElse_of_restore
#print axioms Mettapedia.Logic.LP.RuntimeQuery.emptyCurrentStep_soft_of_marker
#print axioms Mettapedia.Logic.LP.RuntimeQuery.onceStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.metaCallStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.metaCallStep_error
#print axioms Mettapedia.Logic.LP.RuntimeQuery.stepCoreWithMeta_metaCall_of_dispatch
#print axioms Mettapedia.Logic.LP.RuntimeException.freshIdentity_injective
#print axioms Mettapedia.Logic.LP.RuntimeException.scope_lt_scopeCeiling
#print axioms Mettapedia.Logic.LP.RuntimeException.freshenTerm_scope_range
#print axioms Mettapedia.Logic.LP.RuntimeException.Packet.install_nextScope_mono
#print axioms Mettapedia.Logic.LP.RuntimeException.Packet.install_trail_exact
#print axioms Mettapedia.Logic.LP.RuntimeException.Packet.install_roundtrip
#print axioms Mettapedia.Logic.LP.RuntimeQuery.catchStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.throwStep_of_capture
#print axioms Mettapedia.Logic.LP.RuntimeQuery.throwStep_unbound_override
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.throwStep_conserves
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.throwInstantiationError_term
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.services_unboundThrowError
#print axioms Mettapedia.Logic.LP.RuntimeQuery.findCatchTarget_head
#print axioms Mettapedia.Logic.LP.RuntimeQuery.raiseUnhandled_of_restore
#print axioms Mettapedia.Logic.LP.RuntimeQuery.passException_no_outer
#print axioms Mettapedia.Logic.LP.RuntimeQuery.passException_next_outer
#print axioms Mettapedia.Logic.LP.RuntimeQuery.beginCatchRecovery_of_restore_install
#print axioms Mettapedia.Logic.LP.RuntimeQuery.catchRecoveringStep_success_exact
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.ConvergedAt.readTerm_eq_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.readback_naturality_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_graph_certificate
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_finiteEqual
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.refinementEndpoint_finiteReadback
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.runtimeAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_source_execution

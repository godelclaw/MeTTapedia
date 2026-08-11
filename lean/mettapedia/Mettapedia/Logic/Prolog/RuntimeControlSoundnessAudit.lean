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
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.dispatchActionWith_neg
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.dispatchActionWith_notUnify
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.dispatchActionWith_termTest
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.dispatchActionWith_termIdentity
#print axioms Mettapedia.Logic.LP.RuntimeQuery.softIfThenElseStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.backtrackStep_softElse_of_restore
#print axioms Mettapedia.Logic.LP.RuntimeQuery.emptyCurrentStep_soft_of_marker
#print axioms Mettapedia.Logic.LP.RuntimeQuery.onceStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.termTestStep_accepts
#print axioms Mettapedia.Logic.LP.RuntimeQuery.termTestStep_rejects
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.services_termTest
#print axioms Mettapedia.Logic.LP.RuntimeQuery.termIdentityStep_of_result
#print axioms Mettapedia.Logic.LP.RuntimeQuery.termIdentical_same_of_deref
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.services_termIdentity
#print axioms Mettapedia.Logic.LP.RuntimeQuery.metaCallStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.metaCallStep_error
#print axioms Mettapedia.Logic.LP.RuntimeQuery.stepCoreWithMeta_metaCall_of_dispatch
#print axioms Mettapedia.Logic.LP.RuntimeQuery.recordCollectionChoice_marker
#print axioms Mettapedia.Logic.LP.RuntimeQuery.collectAnswerStep_of_capture
#print axioms Mettapedia.Logic.LP.RuntimeQuery.findallStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.recordCollectionChoice_map
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.collectAnswerStep_conserves
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.finalizeCollectionStep_conserves
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.services_collectionEncoding
#print axioms Mettapedia.Logic.LP.RuntimeQuery.databaseRequestStep_exact
#print axioms Mettapedia.Logic.LP.RuntimeQuery.bindDatabaseReferenceStep_of_allocate
#print axioms Mettapedia.Logic.LP.RuntimeQuery.checkedDatabaseRequestStep_assertzWithReference_unbound
#print axioms Mettapedia.Logic.LP.RuntimeQuery.checkedDatabaseRequestStep_assertzWithReference_bound
#print axioms Mettapedia.Logic.LP.RuntimeQuery.replacementDatabaseClauseChoices_cons
#print axioms Mettapedia.Logic.LP.RuntimeQuery.openClauseStep_of_allocate
#print axioms Mettapedia.Logic.LP.RuntimeQuery.databaseClauseSelectStep_empty
#print axioms Mettapedia.Logic.LP.RuntimeQuery.databaseClauseSelectStep_retract_cons_of_materialize
#print axioms Mettapedia.Logic.LP.RuntimeQuery.databaseClauseSelectStep_inspect_cons_of_materialize_allocate
#print axioms Mettapedia.Logic.LP.RuntimeQuery.backtrackStep_databaseClause_of_restore
#print axioms Mettapedia.Logic.LP.RuntimeQuery.unifyingStep_eraseRef_success
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_asserta_of_decode
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_assertz_of_decode
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_assertaWithReference_of_decode_bind
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_assertzWithReference_of_decode_bind
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_eraseRef_of_some
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.applyDatabaseRequest_eraseRef_of_none
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.stepSession_next_of_stepWith
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Entry.eraseAt_visible_previous
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Entry.eraseAt_not_visible_current
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.ofProgram_visibleClause_values
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.visibleClausesAt_asserta_previous
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.visibleClausesAt_assertz_previous
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.eraseRef_generation
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.eraseRef_preserves_previous
#print axioms Mettapedia.Logic.LP.RuntimeDatabase.Database.eraseRef_nextRef
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.openSessionWith_program
#print axioms Mettapedia.Logic.Prolog.SourceRuntime.services_clauseEncoding
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

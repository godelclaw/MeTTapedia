import Mettapedia.Logic.Prolog.RuntimeControlSoundness

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
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.ConvergedAt.readTerm_eq_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.readback_naturality_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_graph_certificate
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_finiteEqual
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.refinementEndpoint_finiteReadback
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.runtimeAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_source_execution

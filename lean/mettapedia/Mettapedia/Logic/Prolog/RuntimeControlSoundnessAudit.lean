import Mettapedia.Logic.Prolog.RuntimeControlSoundness

/-!
# Trusted-base audit for canonical runtime grounding

These commands make the axiom dependencies of the executable conservation and
least-model endpoint visible in ordinary Lean build output.
-/

#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.stepCore_conserves
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.pullCore_conserves
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.ConvergedAt.readTerm_eq_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.readback_naturality_finite
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_graph_certificate
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.startMany_success_finiteEqual
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.refinementEndpoint_finiteReadback
#print axioms Mettapedia.Logic.LP.RuntimeUnificationSoundness.runtimeAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_finiteReadback_leastModel
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_leastModel

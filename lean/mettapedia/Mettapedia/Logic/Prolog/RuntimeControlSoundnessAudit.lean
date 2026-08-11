import Mettapedia.Logic.Prolog.RuntimeControlSoundness

/-!
# Trusted-base audit for canonical runtime grounding

These commands make the axiom dependencies of the executable conservation and
least-model endpoint visible in ordinary Lean build output.
-/

#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.stepCore_conserves
#print axioms Mettapedia.Logic.LP.RuntimeQuery.Conservation.pullCore_conserves
#print axioms Mettapedia.Logic.Prolog.RuntimeControl.pureCallAnswer_leastModel

import Mettapedia.Computability.PNP.V13FaithfulM4AdaptiveGaugeProduct

/-!
# Bit-fixing obstruction for the current concrete connector

The faithful scaffold has a uniform CNF compiler, but its current XOR connector
does not lock a message. Two satisfying assignments over the same public
formula project to different messages. This counterexample is retained as a
construction test for replacement lock families; it is not a status endpoint.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

def v13M4ConcreteOneMessageWorld : V13M4ConcreteWorld 0 0 where
  neutralToken := false
  z := fun _ => false
  g := fun _ => false
  bufferLeft := fun _ => false
  messageBits := fun _ => true

/-- Appendix I.23's needed single-message property on the concrete formula. -/
def V13M4ConcreteCNFSingleMessage : Prop :=
  forall (Y : V13M4ConcretePublic 0 0)
    (alpha beta : ConcreteCNF.Assignment (V13M4ConcreteCNFVar 0 0)),
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) alpha ->
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) beta ->
    v13M4ConcreteMessageProjection alpha =
      v13M4ConcreteMessageProjection beta

/-- The current connector admits two satisfying assignments with different
message projections. Generic SAT bit-fixing therefore cannot yet be promoted
to a message decoder. -/
theorem v13M4Concrete_bitFixingReadout_obstruction :
    ¬ V13M4ConcreteCNFSingleMessage := by
  intro hsingle
  let W0 := v13M4ConcreteWitnessOfWorld v13M4ConcreteZeroWorld
  let W1 := v13M4ConcreteWitnessOfWorld v13M4ConcreteOneMessageWorld
  let alpha0 := v13M4ConcreteExtendWitness v13M4ConcreteZeroPublic W0
  let alpha1 := v13M4ConcreteExtendWitness v13M4ConcreteZeroPublic W1
  have hvalid0 : v13M4ConcreteVerifier v13M4ConcreteZeroPublic W0 := by
    exact v13M4Concrete_sampler_sound () 0 0 v13M4ConcreteZeroWorld trivial
  have hvalid1 : v13M4ConcreteVerifier v13M4ConcreteZeroPublic W1 := by
    exact v13M4Concrete_sampler_sound () 0 0 v13M4ConcreteOneMessageWorld trivial
  have hsat0 : ConcreteCNF.IsSatFormula
      (v13M4ConcreteFormula v13M4ConcreteZeroPublic) alpha0 :=
    (v13M4Concrete_cnf_complete v13M4ConcreteZeroPublic W0 hvalid0).1
  have hsat1 : ConcreteCNF.IsSatFormula
      (v13M4ConcreteFormula v13M4ConcreteZeroPublic) alpha1 :=
    (v13M4Concrete_cnf_complete v13M4ConcreteZeroPublic W1 hvalid1).1
  have heq := hsingle v13M4ConcreteZeroPublic alpha0 alpha1 hsat0 hsat1
  simp [v13M4ConcreteMessageProjection, alpha0, alpha1,
    v13M4ConcreteExtendWitness, W0, W1, v13M4ConcreteWitnessOfWorld,
    v13M4ConcreteZeroWorld, v13M4ConcreteOneMessageWorld] at heq

#print axioms v13M4Concrete_bitFixingReadout_obstruction

end Mettapedia.Computability.PNP

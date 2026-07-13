import Mettapedia.Computability.PNP.V13FaithfulM4HypothesisBoundary

/-!
# Transfer-or-obstruction matrix for the concrete regioned scaffold

Every row refers to this object.  No legacy carrier fact transfers by analogy.
`proved` means an exact theorem is present below or in an imported construction
module; `obstructed` means an exact counterexample is present; `openExactTarget`
means the faithful record type remains unchanged and no proof is claimed.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

inductive V13M4ConstructionField where
  | samplerSoundness
  | singleMessage
  | groupAction
  | adaptiveProductLaw
  | noPublicTags
  | actualTraceAtomExpansion
  | compatibleCouplings
  | bitFixingReadout
  | fixedClockReadout
deriving DecidableEq, Fintype, Repr

inductive V13M4FieldStatus where
  | proved
  | obstructed
  | openExactTarget
deriving DecidableEq, Repr

/-- The canonical matrix.  This is audit data, not an endpoint wrapper. -/
def v13M4ConcreteTransferMatrix :
    V13M4ConstructionField -> V13M4FieldStatus
  | .samplerSoundness => .proved
  | .singleMessage => .obstructed
  | .groupAction => .proved
  | .adaptiveProductLaw => .openExactTarget
  | .noPublicTags => .proved
  | .actualTraceAtomExpansion => .openExactTarget
  | .compatibleCouplings => .openExactTarget
  | .bitFixingReadout => .obstructed
  | .fixedClockReadout => .openExactTarget

/-! ## The projected-readout obstruction behind two matrix rows -/

def v13M4ConcreteOneMessageWorld : V13M4ConcreteWorld 0 0 where
  neutralToken := false
  z := fun _ => false
  g := fun _ => false
  bufferLeft := fun _ => false
  messageBits := fun _ => true

/-- Appendix I.23's needed property on the concrete formula. -/
def V13M4ConcreteCNFSingleMessage : Prop :=
  forall (Y : V13M4ConcretePublic 0 0)
    (alpha beta : ConcreteCNF.Assignment (V13M4ConcreteCNFVar 0 0)),
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) alpha ->
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) beta ->
    v13M4ConcreteMessageProjection alpha =
      v13M4ConcreteMessageProjection beta

/-- The uniform compiler is mechanically correct, but its two satisfying
assignments can project to different messages.  Therefore generic SAT
bit-fixing cannot yet be promoted to a message decoder. -/
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

/-! ## Row seals -/

theorem v13M4Concrete_matrix_samplerSoundness :
    v13M4ConcreteTransferMatrix .samplerSoundness = .proved := rfl

theorem v13M4Concrete_matrix_singleMessage :
    v13M4ConcreteTransferMatrix .singleMessage = .obstructed := rfl

theorem v13M4Concrete_matrix_groupAction :
    v13M4ConcreteTransferMatrix .groupAction = .proved := rfl

theorem v13M4Concrete_matrix_adaptiveProductLaw :
    v13M4ConcreteTransferMatrix .adaptiveProductLaw = .openExactTarget := rfl

theorem v13M4Concrete_matrix_noPublicTags :
    v13M4ConcreteTransferMatrix .noPublicTags = .proved := rfl

theorem v13M4Concrete_matrix_actualTraceAtomExpansion :
    v13M4ConcreteTransferMatrix .actualTraceAtomExpansion = .openExactTarget := rfl

theorem v13M4Concrete_matrix_compatibleCouplings :
    v13M4ConcreteTransferMatrix .compatibleCouplings = .openExactTarget := rfl

theorem v13M4Concrete_matrix_bitFixingReadout :
    v13M4ConcreteTransferMatrix .bitFixingReadout = .obstructed := rfl

theorem v13M4Concrete_matrix_fixedClockReadout :
    v13M4ConcreteTransferMatrix .fixedClockReadout = .openExactTarget := rfl

end Mettapedia.Computability.PNP

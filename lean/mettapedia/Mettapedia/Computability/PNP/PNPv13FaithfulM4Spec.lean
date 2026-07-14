import Mettapedia.Computability.PNP.V13FaithfulQuantitativeFrontiers

/-!
# PNP v13 faithful Appendix-D/I M4 specification

This module defines the type layer and the open mechanical obligations for the
regioned gauge-buffered locked ensemble of Appendices D and I.  It does not
construct an inhabitant.  In particular D.8, D.30, D.33, compatible couplings,
and every analytic frontier remain visibly named hypotheses.

Appendix D does not supply a concrete locked-clause family to instantiate this
interface.  Definition D.5 leaves `Lock_Y` and `Read_Y` as abstract
conjunctions of bounded-arity predicates, Hypothesis D.8 assumes their
locked-message rigidity, and Proposition D.41 derives the single-message
promise from that hypothesis.  Definition I.16 then generically compiles the
unspecified local predicates; it does not define their truth tables.  Thus a
concrete lock core and its D.8 proof remain construction data, not consequences
of the Appendix-D/I type layer.

The specification is attached to the same `V13QuantitativeEnsemble` used by
the quantitative frontier statements.  A future construction must fill this
record; a linear unit-CNF or two-point carrier is not an inhabitant merely by
sharing some generic SAT/readout lemmas.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f g h i j k l

/-! ## Appendix D.1: regioned geometry -/

/-- The five disjoint regions in Definition D.1. -/
inductive V13M4Region where
  | neutral
  | buffer
  | locked
  | gauge
  | readout
deriving DecidableEq, Fintype, Repr

/-- A finite layered geometry and local scope catalog.  Polynomial bounds are
expressed by explicit cost/bound functions so no complexity claim is hidden in
the word "explicit". -/
structure V13M4LayeredGeometry (E : V13QuantitativeEnsemble) where
  Site : E.Parameter -> Nat -> Nat -> Type w
  siteFintype : forall theta m t, Fintype (Site theta m t)
  siteDecidableEq : forall theta m t, DecidableEq (Site theta m t)
  edge : forall {theta m t}, Site theta m t -> Site theta m t -> Prop
  distance : forall {theta m t}, Site theta m t -> Site theta m t -> Nat
  typeLabel : forall {theta m t}, Site theta m t -> Nat
  region : forall {theta m t}, Site theta m t -> V13M4Region
  maximumDegreeBound : Nat
  localArityBound : Nat
  explicitGeometryCost : E.Parameter -> Nat -> Nat -> Nat
  explicitGeometryPolynomialBound : E.Parameter -> Nat -> Nat -> Nat
  geometry_enumeration_within_bound : forall theta m t,
    explicitGeometryCost theta m t <= explicitGeometryPolynomialBound theta m t
  each_region_nonempty : forall theta m t (r : V13M4Region),
    exists site : Site theta m t, region site = r
  isProtected : forall {theta m t}, Site theta m t -> Prop
  protected_iff : forall {theta m t} (site : Site theta m t),
    isProtected site <->
      region site = .locked ∨ region site = .gauge ∨ region site = .readout

  Scope : E.Parameter -> Nat -> Nat -> Type x
  scopeFintype : forall theta m t, Fintype (Scope theta m t)
  scopeSites : forall {theta m t}, Scope theta m t -> Finset (Site theta m t)
  scope_arity : forall {theta m t} (scope : Scope theta m t),
    (scopeSites scope).card <= localArityBound

/-! ## Appendices D.2--D.4: quotient, lock, buffer, probes -/

/-- Type layer for quotient/gauge coordinates, locked/readout data, the buffer
law, and the safe-probe catalog. -/
structure V13M4LocalComponents
    (E : V13QuantitativeEnsemble) (G : V13M4LayeredGeometry E) where
  GaugeIndex : E.Parameter -> Nat -> Nat -> Type y
  gaugeIndexFintype : forall theta m t, Fintype (GaugeIndex theta m t)
  gaugeIndexDecidableEq : forall theta m t, DecidableEq (GaugeIndex theta m t)
  gaugePlacement : forall {theta m t}, GaugeIndex theta m t -> G.Site theta m t
  gaugePlacement_lands_in_gauge : forall {theta m t} (v : GaugeIndex theta m t),
    G.region (gaugePlacement v) = .gauge

  LockPublic : E.Parameter -> Nat -> Nat -> Type z
  LockAux : E.Parameter -> Nat -> Nat -> Type a
  BufferPublic : E.Parameter -> Nat -> Nat -> Type b
  BufferAux : E.Parameter -> Nat -> Nat -> Type c
  LocalAux : E.Parameter -> Nat -> Nat -> Type d
  lockPublicOf : forall {theta m t}, E.Public theta m t -> LockPublic theta m t
  bufferPublicOf : forall {theta m t}, E.Public theta m t -> BufferPublic theta m t

  xCoord : forall {theta m t}, E.Witness theta m t -> GaugeIndex theta m t -> Bool
  gCoord : forall {theta m t}, E.Witness theta m t -> GaugeIndex theta m t -> Bool
  zCoord : forall {theta m t}, E.Witness theta m t -> GaugeIndex theta m t -> Bool
  lockAux : forall {theta m t}, E.Witness theta m t -> LockAux theta m t
  bufferAux : forall {theta m t}, E.Witness theta m t -> BufferAux theta m t
  localAux : forall {theta m t}, E.Witness theta m t -> LocalAux theta m t

  messageLength : E.Parameter -> Nat -> Nat -> Nat
  messageLinearConstant : Real
  messageLinearConstant_positive : 0 < messageLinearConstant
  message_length_lower : forall (theta : E.Parameter) (m t : Nat),
    messageLinearConstant * (t : Real) <= (messageLength theta m t : Real)
  witness_message_length : forall {theta m t} (W : E.Witness theta m t),
    (E.message W).length = messageLength theta m t

  lockPredicate : forall {theta m t},
    LockPublic theta m t ->
    (GaugeIndex theta m t -> Bool) -> LockAux theta m t -> List Bool -> Prop
  readoutPredicate : forall {theta m t},
    LockPublic theta m t ->
    (GaugeIndex theta m t -> Bool) -> LockAux theta m t -> List Bool -> Prop
  bufferPredicate : forall {theta m t},
    BufferPublic theta m t ->
    (GaugeIndex theta m t -> Bool) -> BufferAux theta m t -> Prop
  auxiliaryPredicate : forall {theta m t},
    E.Public theta m t -> E.Witness theta m t -> Prop

  bufferMass : forall {theta m t},
    BufferPublic theta m t -> (GaugeIndex theta m t -> Bool) ->
      BufferAux theta m t -> Real
  bufferMass_nonnegative : forall {theta m t}
    (Ybuf : BufferPublic theta m t) (z : GaugeIndex theta m t -> Bool)
    (xi : BufferAux theta m t),
    0 <= bufferMass Ybuf z xi
  buffer_strictly_positive_on_admissible : forall {theta m t}
    (Ybuf : BufferPublic theta m t) (z : GaugeIndex theta m t -> Bool)
    (xi : BufferAux theta m t),
    bufferPredicate Ybuf z xi -> 0 < bufferMass Ybuf z xi
  buffer_mass_supported_on_acceptance : forall {theta m t}
    (Ybuf : BufferPublic theta m t) (z : GaugeIndex theta m t -> Bool)
    (xi : BufferAux theta m t),
    0 < bufferMass Ybuf z xi -> bufferPredicate Ybuf z xi

  Probe : E.Parameter -> Nat -> Nat -> Type e
  probeFintype : forall theta m t, Fintype (Probe theta m t)
  probeSupport : forall {theta m t}, Probe theta m t -> Finset (G.Site theta m t)
  probe_support_in_buffer : forall {theta m t} (q : Probe theta m t)
    (site : G.Site theta m t),
    site ∈ probeSupport q -> G.region site = .buffer
  probe_arity : forall {theta m t} (q : Probe theta m t),
    (probeSupport q).card <= G.localArityBound
  legalProbe : forall {theta m t}, E.Prefix theta m t -> Probe theta m t -> Prop
  legal_probe_protected_distance : forall {theta m t}
    (pref : E.Prefix theta m t) (q : Probe theta m t),
    legalProbe pref q ->
      forall site, site ∈ probeSupport q -> forall protectedSite,
        G.isProtected protectedSite ->
          E.safeRadius theta m t <= G.distance site protectedSite

/-! ## Quotient equations and vector gauge lift -/

namespace V13M4LocalComponents

variable {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
variable (C : V13M4LocalComponents E G)

def GaugeVector (theta : E.Parameter) (m t : Nat) : Type _ :=
  C.GaugeIndex theta m t -> Bool

/-- Definition D.14, coordinate by coordinate. -/
def QuotientEquations {theta : E.Parameter} {m t : Nat}
    (W : E.Witness theta m t) : Prop :=
  forall v, C.zCoord W v = xor (C.xCoord W v) (C.gCoord W v)

/-- Definition D.15's vector action on the `x,g,z` coordinates. -/
def GaugeVectorActionSpec {theta : E.Parameter} {m t : Nat}
    (s : C.GaugeVector theta m t)
    (W W' : E.Witness theta m t) : Prop :=
  (forall v, C.xCoord W' v = xor (C.xCoord W v) (s v)) ∧
  (forall v, C.gCoord W' v = xor (C.gCoord W v) (s v)) ∧
  (forall v, C.zCoord W' v = C.zCoord W v) ∧
  C.lockAux W' = C.lockAux W ∧
  C.bufferAux W' = C.bufferAux W ∧
  C.localAux W' = C.localAux W ∧
  E.message W' = E.message W

/-- Definition D.38's conjunction, without proving that the verifier has this
form. -/
def ComponentWitnessRelation {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (W : E.Witness theta m t) : Prop :=
  C.lockPredicate (C.lockPublicOf Y) (C.zCoord W) (C.lockAux W) (E.message W) ∧
  C.readoutPredicate (C.lockPublicOf Y) (C.zCoord W) (C.lockAux W) (E.message W) ∧
  C.QuotientEquations W ∧
  C.bufferPredicate (C.bufferPublicOf Y) (C.zCoord W) (C.bufferAux W) ∧
  C.auxiliaryPredicate Y W

end V13M4LocalComponents

/-! ## Exact named Appendix-D hypotheses -/

/-- Hypothesis D.8 exactly: any two accepted locked completions over the same
supported public lock syntax carry the same message.  This is an explicit
manuscript hypothesis, not a theorem obtained from bounded arity or from the
generic Appendix-I truth-table compiler. -/
structure V13D8LockedMessageRigidity
    (E : V13QuantitativeEnsemble) (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G) : Prop where
  locked_message_rigidity :
    forall theta m t (Y : E.Public theta m t)
      (z z' : C.GaugeVector theta m t)
      (xi xi' : C.LockAux theta m t) (M M' : List Bool),
      (exists omega : E.World theta m t,
        E.supported omega ∧ E.publicInput omega = Y) ->
      C.lockPredicate (C.lockPublicOf Y) z xi M ->
      C.readoutPredicate (C.lockPublicOf Y) z xi M ->
      C.lockPredicate (C.lockPublicOf Y) z' xi' M' ->
      C.readoutPredicate (C.lockPublicOf Y) z' xi' M' ->
      M = M'

/-- Hypothesis D.30, carried under its manuscript name.  The referenced record
checks the complete public primitive catalog and forbids raw target/message,
phase, witness, gauge, or target-gadget payloads and uncharged recovery maps. -/
structure V13D30NoPublicTargetTags (E : V13QuantitativeEnsemble) : Prop where
  full_public_syntax : V13FullPublicSyntaxCoverage E

/-- The three normalized primitive classes of Definition D.32. -/
inductive V13M4NormalizedAtomClass where
  | neutral
  | safeBuffer
  | gauge
deriving DecidableEq, Repr

/-- Hypothesis D.33 exactly at the observer boundary: every generated
target-relevant normalized primitive has one of the N/S/G classes.  Quotient
uses additionally expose their raw gauge support. -/
structure V13D33AtomCompleteness
    (E : V13QuantitativeEnsemble) (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G)
    (NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type f) where
  observerGeneratedTargetRelevant : forall {theta m t},
    NormalizedPrimitive theta m t -> Prop
  atomClass : forall {theta m t},
    NormalizedPrimitive theta m t -> V13M4NormalizedAtomClass
  gaugeSupport : forall {theta m t},
    NormalizedPrimitive theta m t -> Finset (C.GaugeIndex theta m t)
  every_generated_primitive_is_N_S_or_G :
    forall theta m t (atom : NormalizedPrimitive theta m t),
      observerGeneratedTargetRelevant atom ->
      atomClass atom = .neutral ∨ atomClass atom = .safeBuffer ∨
        atomClass atom = .gauge
  quotient_use_exposes_raw_support :
    forall theta m t (atom : NormalizedPrimitive theta m t),
      observerGeneratedTargetRelevant atom ->
      atomClass atom = .gauge -> (gaugeSupport atom).Nonempty

/-! ## D.17--D.20: uniform gauge lift -/

/-- Open construction target for the uniform gauge lift.  It states the
quotient equations almost surely and the exact conditional subvector law
`P[g_J=gamma | z] = 2^(-|J|)` for every finite `J`. -/
structure V13M4UniformGaugeLift
    (E : V13QuantitativeEnsemble) (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G) : Prop where
  quotient_equations_on_support :
    forall theta m t (omega : E.World theta m t),
      E.supported omega -> C.QuotientEquations (E.witnessOfWorld omega)
  uniform_subvector_conditioned_on_quotient :
    forall theta m t (z : C.GaugeVector theta m t)
      (J : Finset (C.GaugeIndex theta m t))
      (gamma : (v : {v // v ∈ J}) -> Bool),
      E.conditionDefinedAt theta m t
        (fun omega => C.zCoord (E.witnessOfWorld omega) = z) ->
      E.conditionalProbabilityAt theta m t
        (fun omega => forall v, forall hv : v ∈ J,
          C.gCoord (E.witnessOfWorld omega) v = gamma ⟨v, hv⟩)
        (fun omega => C.zCoord (E.witnessOfWorld omega) = z) =
          1 / (2 : Real) ^ J.card

/-! ## D.47--D.48: compatible message-opposite couplings -/

/-- A finite coupling mass on two copies of one world type. -/
structure V13FiniteCoupling (Omega : Type u) [Fintype Omega] where
  mass : Omega -> Omega -> Real
  mass_nonnegative : forall omega0 omega1, 0 <= mass omega0 omega1
  mass_sum_one : Finset.univ.sum (fun omega0 =>
    Finset.univ.sum (fun omega1 => mass omega0 omega1)) = 1

namespace V13FiniteCoupling

variable {Omega : Type u} [Fintype Omega]

noncomputable def probability (Gamma : V13FiniteCoupling Omega)
    (event : Omega -> Omega -> Prop) : Real := by
  classical
  exact Finset.univ.sum fun omega0 =>
    (Finset.univ.filter fun omega1 => event omega0 omega1).sum
      (Gamma.mass omega0)

noncomputable def leftProbability (Gamma : V13FiniteCoupling Omega)
    (event : Omega -> Prop) : Real :=
  Gamma.probability fun omega0 _ => event omega0

noncomputable def rightProbability (Gamma : V13FiniteCoupling Omega)
    (event : Omega -> Prop) : Real :=
  Gamma.probability fun _ omega1 => event omega1

def conditionDefined (Gamma : V13FiniteCoupling Omega)
    (condition : Omega -> Omega -> Prop) : Prop :=
  0 < Gamma.probability condition

noncomputable def conditionalProbability (Gamma : V13FiniteCoupling Omega)
    (event condition : Omega -> Omega -> Prop) : Real :=
  Gamma.probability
      (fun omega0 omega1 => event omega0 omega1 ∧ condition omega0 omega1) /
    Gamma.probability condition

end V13FiniteCoupling

/-- Hypothesis D.48 with D.47's four compatibility clauses kept separately
visible.  The marginal equations are literal finite conditional laws.  The
final fields are conditional-probability obligations for the buffer coupling
and unsupported gauge marginals; they cannot be filled by an unrelated truth
pin. -/
structure V13D48CompatibleCouplings
    (E : V13QuantitativeEnsemble) (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G) where
  coupling : forall theta m t (_j : E.TargetCoord theta m t),
    @V13FiniteCoupling (E.World theta m t) (E.worldFintype theta m t)
  left_phase_marginal :
    forall theta m t (j : E.TargetCoord theta m t)
      (event : E.World theta m t -> Prop),
      let Gamma := coupling theta m t j
      @V13FiniteCoupling.leftProbability (E.World theta m t)
        (E.worldFintype theta m t) Gamma event =
      E.conditionalProbabilityAt theta m t event
        (fun omega => E.targetBit omega j = false)
  right_phase_marginal :
    forall theta m t (j : E.TargetCoord theta m t)
      (event : E.World theta m t -> Prop),
      let Gamma := coupling theta m t j
      @V13FiniteCoupling.rightProbability (E.World theta m t)
        (E.worldFintype theta m t) Gamma event =
      E.conditionalProbabilityAt theta m t event
        (fun omega => E.targetBit omega j = true)
  neutral_skeleton_matched :
    forall theta m t (j : E.TargetCoord theta m t),
      let Gamma := coupling theta m t j
      @V13FiniteCoupling.probability (E.World theta m t)
        (E.worldFintype theta m t) Gamma
        (fun omega0 omega1 =>
          forall primitive : E.PublicPrimitive theta m t,
            primitive ∈ E.fullPublicSyntax theta m t ->
            E.declaredNeutralPrimitive primitive ->
            E.primitiveValue primitive omega0 = E.primitiveValue primitive omega1) = 1
  couplingLeakageBound : E.Parameter -> Nat -> Nat -> Real
  couplingLeakageBound_nonnegative : forall theta m t,
    0 <= couplingLeakageBound theta m t
  buffer_max_qSSM_coupling_compatible :
    forall theta m t (j : E.TargetCoord theta m t)
      (Y0 Y1 : E.Public theta m t)
      (pref0 pref1 : E.Prefix theta m t) (q : E.Probe theta m t),
      E.legalPrefix Y0 pref0 -> E.legalPrefix Y1 pref1 ->
      E.legalSafeProbe Y0 pref0 q -> E.legalSafeProbe Y1 pref1 q ->
      let Gamma := coupling theta m t j
      let condition := fun omega0 omega1 =>
        E.publicPrefixCondition Y0 pref0 omega0 ∧
          E.publicPrefixCondition Y1 pref1 omega1
      @V13FiniteCoupling.conditionDefined (E.World theta m t)
        (E.worldFintype theta m t) Gamma condition ->
      @V13FiniteCoupling.conditionalProbability (E.World theta m t)
        (E.worldFintype theta m t) Gamma
        (fun omega0 omega1 => E.probeValue q omega0 ≠ E.probeValue q omega1)
        condition <= Real.exp (couplingLeakageBound theta m t) - 1
  unsupported_gauge_coupled_product_fair :
    forall theta m t (j : E.TargetCoord theta m t)
      (Y0 Y1 : E.Public theta m t)
      (pref0 pref1 : E.Prefix theta m t)
      (J : Finset (E.GaugeCoord theta m t))
      (gamma : E.gaugeAssignment J),
      (forall v, v ∈ J -> v ∉ E.gaugeSupport pref0) ->
      (forall v, v ∈ J -> v ∉ E.gaugeSupport pref1) ->
      let Gamma := coupling theta m t j
      let condition := fun omega0 omega1 =>
        E.publicPrefixCondition Y0 pref0 omega0 ∧
          E.publicPrefixCondition Y1 pref1 omega1
      @V13FiniteCoupling.conditionDefined (E.World theta m t)
        (E.worldFintype theta m t) Gamma condition ->
      (@V13FiniteCoupling.conditionalProbability (E.World theta m t)
          (E.worldFintype theta m t) Gamma
          (fun omega0 _ => forall v, forall hv : v ∈ J,
            E.gaugeValue omega0 v = gamma ⟨v, hv⟩) condition =
        1 / (2 : Real) ^ J.card) ∧
      (@V13FiniteCoupling.conditionalProbability (E.World theta m t)
          (E.worldFintype theta m t) Gamma
          (fun _ omega1 => forall v, forall hv : v ∈ J,
            E.gaugeValue omega1 v = gamma ⟨v, hv⟩) condition =
        1 / (2 : Real) ^ J.card)

/-! ## Appendix I: uniform CNF compilation and fixed projection -/

/-- Appendix-I compilation interface.  Soundness, completeness, fixed message
projection, polynomial size, and uniform compilation cost are separate fields.
No CNF fact is obtained by defining the verifier to assert the desired message. -/
structure V13M4UniformCNFCompilation
    (E : V13QuantitativeEnsemble)
    (CNFVar : E.Parameter -> Nat -> Nat -> Type g) where
  cnfVarDecidableEq : forall theta m t, DecidableEq (CNFVar theta m t)
  formula : forall {theta m t},
    E.Public theta m t -> ConcreteCNF.Formula (CNFVar theta m t)
  extractWitness : forall {theta m t},
    ConcreteCNF.Assignment (CNFVar theta m t) -> E.Witness theta m t
  extendWitness : forall {theta m t},
    E.Public theta m t -> E.Witness theta m t ->
      ConcreteCNF.Assignment (CNFVar theta m t)
  messageProjection : forall {theta m t},
    ConcreteCNF.Assignment (CNFVar theta m t) -> List Bool
  cnf_sound : forall {theta m t} (Y : E.Public theta m t)
    (alpha : ConcreteCNF.Assignment (CNFVar theta m t)),
    ConcreteCNF.IsSatFormula (formula Y) alpha ->
      E.verifier Y (extractWitness alpha)
  cnf_complete : forall {theta m t} (Y : E.Public theta m t)
    (W : E.Witness theta m t),
    E.verifier Y W ->
      ConcreteCNF.IsSatFormula (formula Y) (extendWitness Y W) ∧
        extractWitness (extendWitness Y W) = W
  fixed_projection_reads_message : forall {theta m t}
    (Y : E.Public theta m t)
    (alpha : ConcreteCNF.Assignment (CNFVar theta m t)),
    ConcreteCNF.IsSatFormula (formula Y) alpha ->
      messageProjection alpha = E.message (extractWitness alpha)
  compileCost : E.Parameter -> Nat -> Nat -> Nat
  compilePolynomialBound : E.Parameter -> Nat -> Nat -> Nat
  formulaSizePolynomialBound : E.Parameter -> Nat -> Nat -> Nat
  compilation_uniform : forall theta m t,
    compileCost theta m t <= compilePolynomialBound theta m t
  formula_polynomial_size : forall {theta m t} (Y : E.Public theta m t),
    (formula Y).length <= formulaSizePolynomialBound theta m t

/-! ## The open mechanical construction target -/

/-- Complete faithful mechanical target on one quantitative ensemble.  An
inhabitant is the next milestone, not an output of this statement-only layer. -/
structure V13M4OpenConstructionObligations
    (E : V13QuantitativeEnsemble)
    (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G)
    (NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type f)
    (CNFVar : E.Parameter -> Nat -> Nat -> Type g) where
  witness_relation_is_component_conjunction :
    forall theta m t (Y : E.Public theta m t) (W : E.Witness theta m t),
      E.verifier Y W <-> C.ComponentWitnessRelation Y W
  sampler_support_is_positive_mass :
    forall theta m t (omega : E.World theta m t),
      E.supported omega <->
        0 < @V13FiniteLaw.mass (E.World theta m t)
          (E.worldFintype theta m t) (E.law theta m t) omega
  sampler_sound :
    forall theta m t (omega : E.World theta m t),
      E.supported omega -> E.verifier (E.publicInput omega) (E.witnessOfWorld omega)
  lock_satisfiable_D7 :
    forall theta m t (Y : E.Public theta m t),
      (exists omega : E.World theta m t,
        E.supported omega ∧ E.publicInput omega = Y) ->
      exists z xi M,
        C.lockPredicate (C.lockPublicOf Y) z xi M ∧
          C.readoutPredicate (C.lockPublicOf Y) z xi M
  buffer_satisfiable_D23 :
    forall theta m t (Y : E.Public theta m t)
      (z : C.GaugeVector theta m t),
      (exists omega : E.World theta m t,
        E.supported omega ∧ E.publicInput omega = Y ∧
          C.zCoord (E.witnessOfWorld omega) = z) ->
      exists xi, C.bufferPredicate (C.bufferPublicOf Y) z xi
  quotientAndUniformGaugeLift : V13M4UniformGaugeLift E G C
  finiteGaugeGroup :
    V13FaithfulGaugeInterface E (fun theta m t => C.GaugeVector theta m t)
  D8_lockedMessageRigidity : V13D8LockedMessageRigidity E G C
  D30_noPublicTargetTags : V13D30NoPublicTargetTags E
  D33_atomCompleteness : V13D33AtomCompleteness E G C NormalizedPrimitive
  D48_compatibleCouplings : V13D48CompatibleCouplings E G C
  cnfCompilation : V13M4UniformCNFCompilation E CNFVar

end Mettapedia.Computability.PNP

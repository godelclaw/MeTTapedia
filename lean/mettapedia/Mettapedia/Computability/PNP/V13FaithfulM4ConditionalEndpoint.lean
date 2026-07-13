import Mettapedia.Computability.PNP.V13FaithfulM4PhaseA
import Mettapedia.Computability.PNP.V13FaithfulM4AdaptiveGaugeProduct

/-!
# One faithful M4 conditional endpoint

This module seals the same-object lower/upper contradiction at the fixed clock
chosen by the Section-11 premise.  It neither proves nor reconstructs any of
the analytic inputs.  In particular, the global fixed-clock incompressibility
frontier is the named conclusion that the preceding qSSM, incidence/budget,
and boundary-mixing packages are intended to establish.

The accompanying audit expands the residual mechanical record field by field
and then lists every analytic and upper-side premise. The quotient-conditioned
and legal-prefix adaptive gauge laws are construction theorems on this
scaffold, so they are no longer endpoint hypotheses. The audit therefore has
exactly sixteen rows.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f g

/-! ## Residual same-object mechanical socket -/

/-- The ten mechanical inputs still required on the concrete scaffold after
the two faithful gauge packages have been constructed. No field weakens its
counterpart in V13M4OpenConstructionObligations. -/
structure V13M4ConcreteRemainingMechanicalInputs where
  witness_relation_is_component_conjunction :
    forall theta m t (Y : V13M4ConcreteE.Public theta m t)
      (W : V13M4ConcreteE.Witness theta m t),
      V13M4ConcreteE.verifier Y W <->
        V13M4ConcreteC.ComponentWitnessRelation Y W
  sampler_support_is_positive_mass :
    forall theta m t (omega : V13M4ConcreteE.World theta m t),
      V13M4ConcreteE.supported omega <->
        0 < @V13FiniteLaw.mass (V13M4ConcreteE.World theta m t)
          (V13M4ConcreteE.worldFintype theta m t)
          (V13M4ConcreteE.law theta m t) omega
  sampler_sound :
    forall theta m t (omega : V13M4ConcreteE.World theta m t),
      V13M4ConcreteE.supported omega ->
        V13M4ConcreteE.verifier (V13M4ConcreteE.publicInput omega)
          (V13M4ConcreteE.witnessOfWorld omega)
  lock_satisfiable_D7 :
    forall theta m t (Y : V13M4ConcreteE.Public theta m t),
      (exists omega : V13M4ConcreteE.World theta m t,
        V13M4ConcreteE.supported omega ∧
          V13M4ConcreteE.publicInput omega = Y) ->
      exists z xi M,
        V13M4ConcreteC.lockPredicate (V13M4ConcreteC.lockPublicOf Y) z xi M ∧
          V13M4ConcreteC.readoutPredicate
            (V13M4ConcreteC.lockPublicOf Y) z xi M
  buffer_satisfiable_D23 :
    forall theta m t (Y : V13M4ConcreteE.Public theta m t)
      (z : V13M4ConcreteC.GaugeVector theta m t),
      (exists omega : V13M4ConcreteE.World theta m t,
        V13M4ConcreteE.supported omega ∧
          V13M4ConcreteE.publicInput omega = Y ∧
          V13M4ConcreteC.zCoord
            (V13M4ConcreteE.witnessOfWorld omega) = z) ->
      exists xi,
        V13M4ConcreteC.bufferPredicate
          (V13M4ConcreteC.bufferPublicOf Y) z xi
  D8_lockedMessageRigidity :
    V13D8LockedMessageRigidity
      V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
  D30_noPublicTargetTags : V13D30NoPublicTargetTags V13M4ConcreteE
  D33_atomCompleteness :
    V13D33AtomCompleteness
      V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
      (fun _ m t => V13M4ConcreteNormalizedPrimitive m t)
  D48_compatibleCouplings :
    V13D48CompatibleCouplings
      V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
  cnfCompilation :
    V13M4UniformCNFCompilation V13M4ConcreteE
      (fun _ m t => V13M4ConcreteCNFVar m t)

/-- Assembly seal: the residual socket plus the two constructed gauge
packages inhabits the original faithful mechanical record. -/
noncomputable def V13M4ConcreteRemainingMechanicalInputs.complete
    (mechanical : V13M4ConcreteRemainingMechanicalInputs) :
    V13M4OpenConstructionObligations
      V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC
      (fun _ m t => V13M4ConcreteNormalizedPrimitive m t)
      (fun _ m t => V13M4ConcreteCNFVar m t) where
  witness_relation_is_component_conjunction :=
    mechanical.witness_relation_is_component_conjunction
  sampler_support_is_positive_mass :=
    mechanical.sampler_support_is_positive_mass
  sampler_sound := mechanical.sampler_sound
  lock_satisfiable_D7 := mechanical.lock_satisfiable_D7
  buffer_satisfiable_D23 := mechanical.buffer_satisfiable_D23
  quotientAndUniformGaugeLift := v13M4ConcreteUniformGaugeLift
  finiteGaugeGroup := v13M4ConcreteFaithfulGaugeInterface
  D8_lockedMessageRigidity := mechanical.D8_lockedMessageRigidity
  D30_noPublicTargetTags := mechanical.D30_noPublicTargetTags
  D33_atomCompleteness := mechanical.D33_atomCompleteness
  D48_compatibleCouplings := mechanical.D48_compatibleCouplings
  cnfCompilation := mechanical.cnfCompilation

/-! ## Machine-readable hypothesis audit -/

/-- Every field consumed through the endpoint's mechanical record, followed
by each separately named analytic or upper-side premise. -/
inductive V13M4FaithfulEndpointPremise where
  | componentConjunction
  | samplerPositiveSupport
  | samplerSoundness
  | D7LockSatisfiable
  | D23BufferSatisfiable
  | D8LockedMessageRigidity
  | D30FullPublicSyntaxCoverage
  | D33ObserverAtomCompleteness
  | D48CompatibleCouplings
  | uniformCNFCompilation
  | maxQSSM
  | boundedGaugeIncidence
  | atomicEvidenceBudget
  | conditionalBoundaryMixing
  | fixedClockIncompressibility
  | section11SameObjectUpper
  deriving DecidableEq, Repr

/-- Audit classification.  `provedOnScaffold` means the concrete regioned
scaffold supplies the field.  The other three constructors are hypotheses at
the endpoint boundary, not proofs. -/
inductive V13M4FaithfulEndpointPremiseStatus where
  | provedOnScaffold
  | openMechanical
  | openAnalytic
  | section11UpperPremise
  deriving DecidableEq, Repr

structure V13M4FaithfulEndpointAuditRow where
  premise : V13M4FaithfulEndpointPremise
  status : V13M4FaithfulEndpointPremiseStatus
  note : String
  deriving Repr

/-- Pure audit data.  Exact count, order, absence of duplicates, and coverage
are checked by the compile-time guards immediately below its unique value. -/
structure V13M4FaithfulEndpointHypothesisAudit where
  rows : List V13M4FaithfulEndpointAuditRow

/-- The unique machine-readable sixteen-hypothesis audit beside the endpoint.
The open mechanical categories are D.8, the residual D.33 observer theorem,
and D.48. The quotient-conditioned and adaptive gauge packages are absent
because the assembly seal supplies their proved concrete values. -/
def v13M4FaithfulEndpointHypothesisAudit :
    V13M4FaithfulEndpointHypothesisAudit :=
  { rows :=
      [ ⟨.componentConjunction, .provedOnScaffold,
          "verifier is the conjunction of the visible component relations"⟩
      , ⟨.samplerPositiveSupport, .provedOnScaffold,
          "support is exactly positive sampler mass"⟩
      , ⟨.samplerSoundness, .provedOnScaffold,
          "every supported sampled world verifies"⟩
      , ⟨.D7LockSatisfiable, .provedOnScaffold,
          "the scaffold connector is satisfiable but does not prove rigidity"⟩
      , ⟨.D23BufferSatisfiable, .provedOnScaffold,
          "the strictly positive buffer relation has a completion"⟩
      , ⟨.D8LockedMessageRigidity, .openMechanical,
          "requires a concrete locked-CSP clause family not supplied by the scaffold"⟩
      , ⟨.D30FullPublicSyntaxCoverage, .provedOnScaffold,
          "every visible public primitive is classified"⟩
      , ⟨.D33ObserverAtomCompleteness, .openMechanical,
          "scaffold executions expand; arbitrary polynomial-time observer executions remain open"⟩
      , ⟨.D48CompatibleCouplings, .openMechanical,
          "the manuscript-compatible coupling family remains open"⟩
      , ⟨.uniformCNFCompilation, .provedOnScaffold,
          "the concrete verifier has a uniform CNF compilation"⟩
      , ⟨.maxQSSM, .openAnalytic,
          "safe conditional max-divergence frontier"⟩
      , ⟨.boundedGaugeIncidence, .openAnalytic,
          "finite switched-set incidence frontier"⟩
      , ⟨.atomicEvidenceBudget, .openAnalytic,
          "simultaneous high-probability Atomic Evidence Budget"⟩
      , ⟨.conditionalBoundaryMixing, .openAnalytic,
          "conditional boundary-mixing frontier"⟩
      , ⟨.fixedClockIncompressibility, .openAnalytic,
          "Theorem-10.9-shaped fixed-clock incompressibility frontier"⟩
      , ⟨.section11SameObjectUpper, .section11UpperPremise,
          "Section-11 upper bound on the same object and fixed clock"⟩ ] }

#guard v13M4FaithfulEndpointHypothesisAudit.rows.length == 16
#guard v13M4FaithfulEndpointHypothesisAudit.rows.map (fun row => row.premise) ==
  [ .componentConjunction
  , .samplerPositiveSupport
  , .samplerSoundness
  , .D7LockSatisfiable
  , .D23BufferSatisfiable
  , .D8LockedMessageRigidity
  , .D30FullPublicSyntaxCoverage
  , .D33ObserverAtomCompleteness
  , .D48CompatibleCouplings
  , .uniformCNFCompilation
  , .maxQSSM
  , .boundedGaugeIncidence
  , .atomicEvidenceBudget
  , .conditionalBoundaryMixing
  , .fixedClockIncompressibility
  , .section11SameObjectUpper ]

/-! ## The single endpoint -/

/-- For the faithful regioned scaffold, the complete v13 separation
architecture is machine-checked as one implication from exactly these sixteen
named inputs on the same concrete object: component conjunction, positive
sampler support, sampler soundness, D.7 lock satisfiability, D.23 buffer
satisfiability, D.8 locked-message rigidity, D.30 full-public-syntax coverage,
the D.33 residual observer theorem, D.48 compatible couplings, uniform CNF
compilation, max-qSSM, bounded gauge incidence, the Atomic Evidence Budget,
conditional boundary mixing, fixed-clock incompressibility, and the Section-11
same-object upper premise at that fixed clock.

The quotient-conditioned uniform gauge lift and the legal-prefix adaptive
hidden-gauge product law are not hypotheses: the concrete assembly seal supplies
their proved values. This is NOT a proof of P != NP; the open inputs are open
mathematics, and D.8 additionally awaits a concrete locked-CSP family absent
from Appendix D as written.

The contradiction uses the last analytic frontier and the upper premise
directly.  The other analytic packages remain explicit because the manuscript
uses them to derive that frontier; this theorem does not silently claim that
derivation. -/
theorem v13M4Faithful_fixedClock_upperLowerClash
    (mechanical : V13M4ConcreteRemainingMechanicalInputs)
    (safeQSSM : V13SafeQSSMFrontier V13M4ConcreteE)
    (boundedGaugeIncidence :
      V13BoundedGaugeIncidenceFrontier V13M4ConcreteE)
    (atomicEvidenceBudget :
      V13AtomicEvidenceBudgetFrontier
        V13M4ConcreteE safeQSSM boundedGaugeIncidence)
    (conditionalBoundaryMixing :
      V13BoundaryMixingFrontier V13M4ConcreteE)
    (fixedClockIncompressibility :
      V13GlobalMessageIncompressibilityFrontier V13M4ConcreteE)
    (section11SameObjectUpper :
      V13Section11SameObjectUpper
        V13M4ConcreteE fixedClockIncompressibility) : False := by
  let fullMechanical := mechanical.complete
  let _analyticSeal := (atomicEvidenceBudget, conditionalBoundaryMixing)
  let D := section11SameObjectUpper.Dstar
  have heta : 0 < fixedClockIncompressibility.eta D :=
    fixedClockIncompressibility.eta_positive D
  have hkappa : 0 < fixedClockIncompressibility.kappa D :=
    fixedClockIncompressibility.kappa_positive D
  obtain ⟨t, ht⟩ := exists_nat_gt
    (max (fixedClockIncompressibility.threshold D : Real)
      ((section11SameObjectUpper.constantProgramCost : Real) /
        fixedClockIncompressibility.eta D))
  have hthreshold_lt :
      (fixedClockIncompressibility.threshold D : Real) < t :=
    (le_max_left _ _).trans_lt ht
  have hthreshold : fixedClockIncompressibility.threshold D <= t := by
    exact Nat.le_of_lt (Nat.cast_lt.mp hthreshold_lt)
  have ht_positive : 0 < (t : Real) :=
    lt_of_le_of_lt (Nat.cast_nonneg _) hthreshold_lt
  have hcost_div :
      (section11SameObjectUpper.constantProgramCost : Real) /
          fixedClockIncompressibility.eta D < t :=
    (le_max_right _ _).trans_lt ht
  have hcost_lt :
      (section11SameObjectUpper.constantProgramCost : Real) <
        fixedClockIncompressibility.eta D * t := by
    have := (div_lt_iff₀ heta).mp hcost_div
    nlinarith
  let theta := fixedClockIncompressibility.parameterAtClock D
  let m := V13M4ConcreteE.sizeAtMessageScale theta t
  let event : V13M4ConcreteE.World theta m t -> Prop := fun omega =>
    (fixedClockIncompressibility.eta D * t : Real) <=
      V13M4ConcreteE.clockedKpoly D omega
  have hprob_lower :
      V13M4ConcreteE.probabilityAt theta m t event >=
        1 - Real.exp
          (-(fixedClockIncompressibility.kappa D * t) * Real.log 2) := by
    simpa [D, theta, m, event] using
      fixedClockIncompressibility.global_message_incompressibility D t hthreshold
  have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexponent_negative :
      -(fixedClockIncompressibility.kappa D * t) * Real.log 2 < 0 := by
    have hproduct :
        0 < fixedClockIncompressibility.kappa D * (t : Real) :=
      mul_pos hkappa ht_positive
    nlinarith
  have hexp_lt_one :
      Real.exp (-(fixedClockIncompressibility.kappa D * t) * Real.log 2) < 1 :=
    Real.exp_lt_one_iff.mpr hexponent_negative
  have hprob_positive :
      0 < V13M4ConcreteE.probabilityAt theta m t event := by
    linarith
  letI := V13M4ConcreteE.worldFintype theta m t
  have hsum_positive :
      0 < (Finset.univ.filter event).sum
        (V13M4ConcreteE.law theta m t).mass := by
    simpa [V13QuantitativeEnsemble.probabilityAt,
      V13FiniteLaw.probability] using hprob_positive
  have hmass_nonnegative :
      forall omega : V13M4ConcreteE.World theta m t,
      omega ∈ Finset.univ.filter event ->
        0 <= (V13M4ConcreteE.law theta m t).mass omega := by
    intro omega _
    exact (V13M4ConcreteE.law theta m t).mass_nonnegative omega
  obtain ⟨omega, homega_mem, homega_mass⟩ :=
    (Finset.sum_pos_iff_of_nonneg hmass_nonnegative).mp hsum_positive
  have homega_event : event omega := (Finset.mem_filter.mp homega_mem).2
  have homega_supported : V13M4ConcreteE.supported omega :=
    (fullMechanical.sampler_support_is_positive_mass theta m t omega).2
      homega_mass
  have hupper_nat :
      V13M4ConcreteE.clockedKpoly D omega <=
        section11SameObjectUpper.constantProgramCost := by
    simpa [D, theta, m] using
      section11SameObjectUpper.clocked_self_reduction_upper t omega homega_supported
  have hupper_real :
      (V13M4ConcreteE.clockedKpoly D omega : Real) <=
        section11SameObjectUpper.constantProgramCost := by
    exact Nat.cast_le.mpr hupper_nat
  exact (not_lt_of_ge (homega_event.trans hupper_real)) hcost_lt

#print axioms v13M4FaithfulEndpointHypothesisAudit
#print axioms V13M4ConcreteRemainingMechanicalInputs.complete
#print axioms v13M4Faithful_fixedClock_upperLowerClash

end Mettapedia.Computability.PNP

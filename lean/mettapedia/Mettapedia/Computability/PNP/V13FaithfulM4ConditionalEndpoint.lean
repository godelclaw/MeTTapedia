import Mettapedia.Computability.PNP.V13FaithfulM4PhaseA

/-!
# One faithful M4 conditional endpoint

This module seals the same-object lower/upper contradiction at the fixed clock
chosen by the Section-11 premise.  It neither proves nor reconstructs any of
the analytic inputs.  In particular, the global fixed-clock incompressibility
frontier is the named conclusion that the preceding qSSM, incidence/budget,
and boundary-mixing packages are intended to establish.

The accompanying audit expands the mechanical record field by field and then
lists every analytic and upper-side premise.  It distinguishes scaffold
theorems from four categories of residual mechanical content and the open
analytic mathematics.  The conditional gauge-product category occupies two
record rows: quotient-conditioned uniformity and legal-prefix adaptive
uniformity.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f g

/-! ## Machine-readable hypothesis audit -/

/-- Every field consumed through the endpoint's mechanical record, followed
by each separately named analytic or upper-side premise. -/
inductive V13M4FaithfulEndpointPremise where
  | componentConjunction
  | samplerPositiveSupport
  | samplerSoundness
  | D7LockSatisfiable
  | D23BufferSatisfiable
  | quotientAndUniformGaugeLift
  | finiteGaugeGroup
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

/-- The unique machine-readable audit beside the endpoint.  The four open
mechanical categories are D.8, the conditional gauge-product package, the
residual D.33 observer theorem, and D.48.  The gauge-product package occupies
two rows because the faithful construction record separately asks for the
quotient-conditioned subvector law and the legal-prefix adaptive law. -/
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
      , ⟨.quotientAndUniformGaugeLift, .openMechanical,
          "quotient equations are proved; quotient-conditioned subvector uniformity remains open"⟩
      , ⟨.finiteGaugeGroup, .openMechanical,
          "positive-rank free action laws are proved; legal-prefix adaptive product-uniformity remains open"⟩
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

#guard v13M4FaithfulEndpointHypothesisAudit.rows.length == 18
#guard v13M4FaithfulEndpointHypothesisAudit.rows.map (fun row => row.premise) ==
  [ .componentConjunction
  , .samplerPositiveSupport
  , .samplerSoundness
  , .D7LockSatisfiable
  , .D23BufferSatisfiable
  , .quotientAndUniformGaugeLift
  , .finiteGaugeGroup
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
architecture is machine-checked as one implication from exactly the mechanical
construction record (including the named open D.8, conditional gauge-product
package, D.33-residual, and D.48 fields), max-qSSM, bounded incidence, the Atomic
Evidence Budget, conditional boundary mixing, fixed-clock incompressibility,
and the Section-11 same-object upper premise at that fixed clock. This is NOT a
proof of P != NP; the open inputs are open mathematics, and D.8 additionally
awaits a concrete locked-CSP family absent from Appendix D as written.

The contradiction uses the last analytic frontier and the upper premise
directly.  The other analytic packages remain explicit because the manuscript
uses them to derive that frontier; this theorem does not silently claim that
derivation. -/
theorem v13M4Faithful_fixedClock_upperLowerClash
    (E : V13QuantitativeEnsemble)
    (G : V13M4LayeredGeometry E)
    (C : V13M4LocalComponents E G)
    (NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type f)
    (CNFVar : E.Parameter -> Nat -> Nat -> Type g)
    (mechanical :
      V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    (safeQSSM : V13SafeQSSMFrontier E)
    (boundedGaugeIncidence : V13BoundedGaugeIncidenceFrontier E)
    (atomicEvidenceBudget :
      V13AtomicEvidenceBudgetFrontier E safeQSSM boundedGaugeIncidence)
    (conditionalBoundaryMixing : V13BoundaryMixingFrontier E)
    (fixedClockIncompressibility :
      V13GlobalMessageIncompressibilityFrontier E)
    (section11SameObjectUpper :
      V13Section11SameObjectUpper E fixedClockIncompressibility) : False := by
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
  let m := E.sizeAtMessageScale theta t
  let event : E.World theta m t -> Prop := fun omega =>
    (fixedClockIncompressibility.eta D * t : Real) <= E.clockedKpoly D omega
  have hprob_lower :
      E.probabilityAt theta m t event >=
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
  have hprob_positive : 0 < E.probabilityAt theta m t event := by
    linarith
  letI := E.worldFintype theta m t
  have hsum_positive :
      0 < (Finset.univ.filter event).sum
        (E.law theta m t).mass := by
    simpa [V13QuantitativeEnsemble.probabilityAt,
      V13FiniteLaw.probability] using hprob_positive
  have hmass_nonnegative : forall omega : E.World theta m t,
      omega ∈ Finset.univ.filter event ->
        0 <= (E.law theta m t).mass omega := by
    intro omega _
    exact (E.law theta m t).mass_nonnegative omega
  obtain ⟨omega, homega_mem, homega_mass⟩ :=
    (Finset.sum_pos_iff_of_nonneg hmass_nonnegative).mp hsum_positive
  have homega_event : event omega := (Finset.mem_filter.mp homega_mem).2
  have homega_supported : E.supported omega :=
    (mechanical.sampler_support_is_positive_mass theta m t omega).2 homega_mass
  have hupper_nat :
      E.clockedKpoly D omega <= section11SameObjectUpper.constantProgramCost := by
    simpa [D, theta, m] using
      section11SameObjectUpper.clocked_self_reduction_upper t omega homega_supported
  have hupper_real :
      (E.clockedKpoly D omega : Real) <=
        section11SameObjectUpper.constantProgramCost := by
    exact Nat.cast_le.mpr hupper_nat
  exact (not_lt_of_ge (homega_event.trans hupper_real)) hcost_lt

#print axioms v13M4FaithfulEndpointHypothesisAudit
#print axioms v13M4Faithful_fixedClock_upperLowerClash

end Mettapedia.Computability.PNP

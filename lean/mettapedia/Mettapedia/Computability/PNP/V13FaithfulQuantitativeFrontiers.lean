import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Computability.PNP.V15RealEnsembleSpine

/-!
# PNP v13 faithful quantitative frontier statements

This module is a statement layer, not a proof of the manuscript's analytic
inputs.  It keeps one size-indexed finite ensemble object beneath the hidden
gauge product law, soft-buffer max-qSSM, bounded incidence and Atomic Evidence
Budget, conditional boundary mixing, global clocked incompressibility, and the
Section-11 upper side.

The finite formalization uses real-valued mass functions on finite world
types.  Thus conditional probabilities are literal finite sums.  Boolean
primitive values and natural size/clock indices are the only representational
simplifications; all manuscript quantifier order and displayed inequalities
remain visible.  Every structure ending in `Frontier` or `Target` is an open
hypothesis to be established on a future Appendix-D/I construction.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v w x y z a b c d e f g h i j k l

/-! ## Finite probability space -/

/-- A finite real-valued probability mass function. -/
structure V13FiniteLaw (Omega : Type u) [Fintype Omega] where
  mass : Omega -> Real
  mass_nonnegative : forall omega, 0 <= mass omega
  mass_sum_one : Finset.univ.sum mass = 1

namespace V13FiniteLaw

variable {Omega : Type u} [Fintype Omega]

/-- Literal finite probability of an event. -/
noncomputable def probability (mu : V13FiniteLaw Omega)
    (event : Omega -> Prop) : Real := by
  classical
  exact (Finset.univ.filter event).sum mu.mass

/-- A conditioning event has a defined conditional law exactly when it has
positive mass. -/
def conditionDefined (mu : V13FiniteLaw Omega)
    (condition : Omega -> Prop) : Prop :=
  0 < mu.probability condition

/-- Literal finite conditional probability. -/
noncomputable def conditionalProbability (mu : V13FiniteLaw Omega)
    (event condition : Omega -> Prop) : Real :=
  mu.probability (fun omega => event omega ∧ condition omega) /
    mu.probability condition

/-- Conditional law of a finite-valued observable. -/
noncomputable def conditionalLaw {Alpha : Type v}
    (mu : V13FiniteLaw Omega) (observable : Omega -> Alpha)
    (condition : Omega -> Prop) (value : Alpha) : Real :=
  mu.conditionalProbability (fun omega => observable omega = value) condition

end V13FiniteLaw

/-- Finite max-divergence
`D_infinity(P || Q) = log sup_{a:Q(a)>0} P(a)/Q(a)`.

The `sSup` presentation is total even before the frontier supplies its strict
positivity/common-support obligation. -/
noncomputable def v13FiniteMaxDivergence {Alpha : Type u}
    (P Q : Alpha -> Real) : Real :=
  sSup (Set.range fun a : {a : Alpha // 0 < Q a} =>
    Real.log (P a / Q a))

/-! ## One common size-indexed ensemble object -/

/-- Common finite object on which every faithful v13 construction and analytic
statement is indexed.  The parameter `theta` records the ensemble choices made
after a clock exponent is fixed; `m` is the public size and `t` the message
scale.

The record deliberately contains raw observables and catalogs, not any of the
desired analytic inequalities. -/
structure V13QuantitativeEnsemble where
  Parameter : Type u
  parameterNonempty : Nonempty Parameter
  World : Parameter -> Nat -> Nat -> Type v
  worldFintype : forall theta m t, Fintype (World theta m t)
  law : forall theta m t,
    @V13FiniteLaw (World theta m t) (worldFintype theta m t)

  Public : Parameter -> Nat -> Nat -> Type w
  Witness : Parameter -> Nat -> Nat -> Type x
  publicInput : forall {theta m t}, World theta m t -> Public theta m t
  witnessOfWorld : forall {theta m t}, World theta m t -> Witness theta m t
  verifier : forall {theta m t}, Public theta m t -> Witness theta m t -> Prop
  message : forall {theta m t}, Witness theta m t -> List Bool
  supported : forall {theta m t}, World theta m t -> Prop

  Prefix : Parameter -> Nat -> Nat -> Type y
  legalPrefix : forall {theta m t}, Public theta m t -> Prefix theta m t -> Prop
  prefixConsistent : forall {theta m t},
    Prefix theta m t -> World theta m t -> Prop

  GaugeCoord : Parameter -> Nat -> Nat -> Type z
  gaugeCoordDecidableEq : forall theta m t, DecidableEq (GaugeCoord theta m t)
  gaugeCoords : forall theta m t, Finset (GaugeCoord theta m t)
  gaugeValue : forall {theta m t},
    World theta m t -> GaugeCoord theta m t -> Bool
  gaugeSupport : forall {theta m t},
    Prefix theta m t -> Finset (GaugeCoord theta m t)

  Probe : Parameter -> Nat -> Nat -> Type a
  ProbeValue : Parameter -> Nat -> Nat -> Type b
  probeValue : forall {theta m t},
    Probe theta m t -> World theta m t -> ProbeValue theta m t
  legalSafeProbe : forall {theta m t},
    Public theta m t -> Prefix theta m t -> Probe theta m t -> Prop
  probeArity : forall {theta m t}, Probe theta m t -> Nat
  safeRadius : Parameter -> Nat -> Nat -> Nat
  chargedGaugeSupportSize : forall {theta m t}, Prefix theta m t -> Nat

  HiddenCondition : Parameter -> Nat -> Nat -> Type c
  HiddenValue : Parameter -> Nat -> Nat -> Type d
  hiddenConditionHolds : forall {theta m t},
    HiddenCondition theta m t -> HiddenValue theta m t ->
      World theta m t -> Prop
  hiddenConditionFarFromProbe : forall {theta m t},
    HiddenCondition theta m t -> Probe theta m t -> Nat -> Prop

  TargetCoord : Parameter -> Nat -> Nat -> Type e
  targetCoordDecidableEq : forall theta m t,
    DecidableEq (TargetCoord theta m t)
  switchedSet : forall theta m t, Finset (TargetCoord theta m t)
  targetBit : forall {theta m t},
    World theta m t -> TargetCoord theta m t -> Bool
  gaugeSetCanSeparate : forall {theta m t},
    Finset (GaugeCoord theta m t) -> TargetCoord theta m t -> Prop
  gaugeSetCanSeparateDecidable : forall {theta m t}
    (U : Finset (GaugeCoord theta m t)) (j : TargetCoord theta m t),
    Decidable (gaugeSetCanSeparate U j)

  Program : Type f
  programLength : Program -> Nat
  deterministicPolynomialObserver : Program -> Prop
  neutralCoherent : forall {theta m t}, Program -> World theta m t -> Prop
  safeCompatible : forall {theta m t}, Program -> World theta m t -> Prop
  safeChargedOccurrences : forall {theta m t},
    Program -> Finset (TargetCoord theta m t) -> World theta m t -> Nat
  cumulativeSafeLeakage : forall {theta m t},
    Program -> Finset (TargetCoord theta m t) -> World theta m t -> Real
  coordinateGap : forall {theta m t},
    Program -> TargetCoord theta m t -> World theta m t -> Real

  History : Parameter -> Nat -> Nat -> Type g
  historyConsistent : forall {theta m t},
    History theta m t -> World theta m t -> Prop
  admissibleHistory : forall {theta m t},
    TargetCoord theta m t -> History theta m t -> Prop
  PivotSummary : Parameter -> Nat -> Nat -> Type h
  pivotSummary : forall {theta m t},
    Nat -> TargetCoord theta m t -> World theta m t -> PivotSummary theta m t

  PublicPrimitive : Parameter -> Nat -> Nat -> Type i
  publicPrimitiveDecidableEq : forall theta m t,
    DecidableEq (PublicPrimitive theta m t)
  fullPublicSyntax : forall theta m t, Finset (PublicPrimitive theta m t)
  primitiveValue : forall {theta m t},
    PublicPrimitive theta m t -> World theta m t -> Bool
  declaredNeutralPrimitive : forall {theta m t},
    PublicPrimitive theta m t -> Prop
  chargedPrimitiveExpansion : forall {theta m t},
    PublicPrimitive theta m t -> Prop
  forbiddenRawPayload : forall {theta m t},
    PublicPrimitive theta m t -> Prop
  recoversForbiddenWithoutCharge : forall {theta m t},
    PublicPrimitive theta m t -> Prop
  oppositePair : forall {theta m t},
    TargetCoord theta m t -> World theta m t -> World theta m t -> Prop

  sameGaugeFiber : forall {theta m t},
    World theta m t -> World theta m t -> Prop
  parametersAdmissibleForClock : Parameter -> Nat -> Prop
  sizeAtMessageScale : Parameter -> Nat -> Nat
  /-- Raw numeric slot for `Kpoly_D(M(Y)|Y)`.  A final manuscript-facing
  construction must additionally provide `V13ClockedKpolySemantics`, which
  ties this value to a fuel-bounded prefix-program minimum. -/
  clockedKpoly : forall {theta m t}, Nat -> World theta m t -> Nat

/-- The manuscript clock `(encoded public length + 2)^D`. -/
def v13PolynomialClockFuel (encodedPublic : List Bool) (D : Nat) : Nat :=
  (encodedPublic.length + 2) ^ D

/-- Operational meaning of the raw `clockedKpoly` slot.  Programs have
self-delimiting binary descriptions, the programs below any length bound are
explicitly and finitely enumerable with the manuscript's exponential counting
bound, evaluation is step-bounded, and the sublevel equivalence gives the exact
minimum-description semantics.  The additive `programCountingConstant` is the
fixed universal-machine overhead used by the prefix-program union bound. -/
structure V13ClockedKpolySemantics (E : V13QuantitativeEnsemble) where
  encodePublic : forall {theta m t}, E.Public theta m t -> List Bool
  programCode : E.Program -> List Bool
  programCode_injective : Function.Injective programCode
  programCode_prefixFree : forall {p q : E.Program} {suffix : List Bool},
    programCode q = programCode p ++ suffix -> p = q
  programLength_eq_codeLength : forall p,
    E.programLength p = (programCode p).length
  programsUpToLength : Nat -> List E.Program
  programsUpToLength_nodup : forall a,
    (programsUpToLength a).Nodup
  programsUpToLength_spec : forall a p,
    p ∈ programsUpToLength a <-> E.programLength p <= a
  programCountingConstant : Nat
  programsUpToLength_card_bound : forall a,
    (programsUpToLength a).length <=
      2 ^ (a + programCountingConstant)
  evalWithinSteps : E.Program -> List Bool -> Nat -> Option (List Bool)
  eval_fuel_mono : forall {p input fuel output},
    evalWithinSteps p input fuel = some output ->
      forall {fuel'}, fuel <= fuel' ->
        evalWithinSteps p input fuel' = some output
  clockedKpoly_le_iff :
    forall {theta m t} (D : Nat) (omega : E.World theta m t) (a : Nat),
      E.clockedKpoly D omega <= a <->
        exists p : E.Program,
          E.programLength p <= a ∧
            evalWithinSteps p (encodePublic (E.publicInput omega))
                (v13PolynomialClockFuel
                  (encodePublic (E.publicInput omega)) D) =
              some (E.message (E.witnessOfWorld omega))

namespace V13QuantitativeEnsemble

variable (E : V13QuantitativeEnsemble)

noncomputable def probabilityAt (theta : E.Parameter) (m t : Nat)
    (event : E.World theta m t -> Prop) : Real := by
  letI := E.worldFintype theta m t
  exact (E.law theta m t).probability event

noncomputable def conditionalProbabilityAt
    (theta : E.Parameter) (m t : Nat)
    (event condition : E.World theta m t -> Prop) : Real := by
  letI := E.worldFintype theta m t
  exact (E.law theta m t).conditionalProbability event condition

def conditionDefinedAt (theta : E.Parameter) (m t : Nat)
    (condition : E.World theta m t -> Prop) : Prop := by
  letI := E.worldFintype theta m t
  exact (E.law theta m t).conditionDefined condition

def publicPrefixCondition {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (pref : E.Prefix theta m t)
    (omega : E.World theta m t) : Prop :=
  E.publicInput omega = Y ∧ E.prefixConsistent pref omega

def publicHistoryCondition {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (history : E.History theta m t)
    (omega : E.World theta m t) : Prop :=
  E.publicInput omega = Y ∧ E.historyConsistent history omega

def gaugeAssignment {theta : E.Parameter} {m t : Nat}
    (J : Finset (E.GaugeCoord theta m t)) : Type _ :=
  (v : {v // v ∈ J}) -> Bool

noncomputable def conditionalGaugeProbability
    {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (pref : E.Prefix theta m t)
    (J : Finset (E.GaugeCoord theta m t))
    (gamma : E.gaugeAssignment J) : Real :=
  E.conditionalProbabilityAt theta m t
    (fun omega => forall v, forall hv : v ∈ J,
      E.gaugeValue omega v = gamma ⟨v, hv⟩)
    (E.publicPrefixCondition Y pref)

noncomputable def conditionalProbeLaw
    {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (pref : E.Prefix theta m t)
    (q : E.Probe theta m t) (extra : E.World theta m t -> Prop)
    (value : E.ProbeValue theta m t) : Real :=
  E.conditionalProbabilityAt theta m t
    (fun omega => E.probeValue q omega = value)
    (fun omega => E.publicPrefixCondition Y pref omega ∧ extra omega)

noncomputable def conditionalProbeMaxDivergence
    {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (pref : E.Prefix theta m t)
    (q : E.Probe theta m t)
    (C : E.HiddenCondition theta m t) (c : E.HiddenValue theta m t) : Real :=
  v13FiniteMaxDivergence
    (E.conditionalProbeLaw Y pref q
      (E.hiddenConditionHolds C c))
    (E.conditionalProbeLaw Y pref q (fun _ => True))

noncomputable def conditionalPredictorSuccess
    {theta : E.Parameter} {m t : Nat}
    (Y : E.Public theta m t) (history : E.History theta m t)
    (depth : Nat) (j : E.TargetCoord theta m t)
    (predictor : E.PivotSummary theta m t -> Bool) : Real :=
  E.conditionalProbabilityAt theta m t
    (fun omega => predictor (E.pivotSummary depth j omega) =
      E.targetBit omega j)
    (E.publicHistoryCondition Y history)

noncomputable def gapSum {theta : E.Parameter} {m t : Nat}
    (P : E.Program) (S : Finset (E.TargetCoord theta m t))
    (omega : E.World theta m t) : Real :=
  S.sum fun j => E.coordinateGap P j omega

def separationIndicator {theta : E.Parameter} {m t : Nat}
    (U : Finset (E.GaugeCoord theta m t))
    (j : E.TargetCoord theta m t) : Nat := by
  letI := E.gaugeSetCanSeparateDecidable U j
  exact if E.gaugeSetCanSeparate U j then 1 else 0

end V13QuantitativeEnsemble

/-! ## Critical 3: genuine gauge action and product law -/

/-- Hypothesis 4.17 in finite form: after conditioning on the same public
instance and any legal prefix, every finite unsupported coordinate set is
exactly uniform, `P[g_J = gamma | Y,h] = 2^(-|J|)`.

This is an open construction/measure hypothesis, not the legacy universally
true gauge predicate. -/
structure V13HiddenGaugeProductFrontier (E : V13QuantitativeEnsemble) : Prop where
  product_uniform :
    forall theta m t (Y : E.Public theta m t) (pref : E.Prefix theta m t),
      E.legalPrefix Y pref ->
      E.conditionDefinedAt theta m t (E.publicPrefixCondition Y pref) ->
      forall (J : Finset (E.GaugeCoord theta m t))
        (gamma : E.gaugeAssignment J),
        (forall v, v ∈ J -> v ∉ E.gaugeSupport pref) ->
        E.conditionalGaugeProbability Y pref J gamma =
          1 / (2 : Real) ^ J.card

/-- Indexed finite gauge group/action required by Theorem 4.31(v).  The action
preserves the public instance, verifier relation, and message, and its orbits
are exactly the declared gauge fibers.  Freeness records the orbit/fiber
cardinality fact needed for gauge-rank entropy. -/
structure V13FiniteGaugeGroupAction (E : V13QuantitativeEnsemble)
    (GaugeElement : E.Parameter -> Nat -> Nat -> Type u) where
  gaugeElementFintype : forall theta m t, Fintype (GaugeElement theta m t)
  one : forall {theta m t}, GaugeElement theta m t
  mul : forall {theta m t},
    GaugeElement theta m t -> GaugeElement theta m t -> GaugeElement theta m t
  inv : forall {theta m t}, GaugeElement theta m t -> GaugeElement theta m t
  mul_assoc : forall {theta m t} (r s q : GaugeElement theta m t),
    mul (mul r s) q = mul r (mul s q)
  one_mul : forall {theta m t} (s : GaugeElement theta m t), mul one s = s
  mul_one : forall {theta m t} (s : GaugeElement theta m t), mul s one = s
  inv_mul : forall {theta m t} (s : GaugeElement theta m t), mul (inv s) s = one

  actWorld : forall {theta m t},
    GaugeElement theta m t -> E.World theta m t -> E.World theta m t
  actWitness : forall {theta m t},
    GaugeElement theta m t -> E.Witness theta m t -> E.Witness theta m t
  one_act_world : forall {theta m t} (omega : E.World theta m t),
    actWorld one omega = omega
  mul_act_world : forall {theta m t} (r s : GaugeElement theta m t)
    (omega : E.World theta m t),
    actWorld (mul r s) omega = actWorld r (actWorld s omega)
  one_act_witness : forall {theta m t} (W : E.Witness theta m t),
    actWitness one W = W
  mul_act_witness : forall {theta m t} (r s : GaugeElement theta m t)
    (W : E.Witness theta m t),
    actWitness (mul r s) W = actWitness r (actWitness s W)

  public_invariant : forall {theta m t} (s : GaugeElement theta m t)
    (omega : E.World theta m t),
    E.publicInput (actWorld s omega) = E.publicInput omega
  verifier_invariant : forall {theta m t} (s : GaugeElement theta m t)
    (Y : E.Public theta m t) (W : E.Witness theta m t),
    E.verifier Y (actWitness s W) <-> E.verifier Y W
  message_invariant : forall {theta m t} (s : GaugeElement theta m t)
    (W : E.Witness theta m t),
    E.message (actWitness s W) = E.message W
  worldWitness_equivariant : forall {theta m t}
    (s : GaugeElement theta m t) (omega : E.World theta m t),
    E.witnessOfWorld (actWorld s omega) = actWitness s (E.witnessOfWorld omega)

  worldAction_free : forall {theta m t} (s r : GaugeElement theta m t)
    (omega : E.World theta m t),
    actWorld s omega = actWorld r omega -> s = r
  sameFiber_iff_orbit : forall {theta m t}
    (omega omega' : E.World theta m t),
    E.sameGaugeFiber omega omega' <->
      exists s : GaugeElement theta m t, actWorld s omega = omega'
  gaugeRank : E.Parameter -> Nat -> Nat -> Nat
  rank_eq_coordinate_card : forall theta m t,
    gaugeRank theta m t = (E.gaugeCoords theta m t).card

namespace V13FiniteGaugeGroupAction

/-- Manuscript-facing M4 requires positive gauge rank and an actually moving
orbit.  This guard excludes the legacy identity-action adapter. -/
def ManuscriptFacing {E : V13QuantitativeEnsemble}
    {GaugeElement : E.Parameter -> Nat -> Nat -> Type u}
    (G : V13FiniteGaugeGroupAction E GaugeElement) : Prop :=
  (forall theta m t, 0 < G.gaugeRank theta m t) ∧
    forall theta m t, exists (s : GaugeElement theta m t)
      (omega : E.World theta m t), G.actWorld s omega ≠ omega

/-- A universally identity world action cannot inhabit the manuscript-facing
M4 action guard. -/
theorem identityGaugeAction_not_manuscriptFacing
    {E : V13QuantitativeEnsemble}
    {GaugeElement : E.Parameter -> Nat -> Nat -> Type u}
    (G : V13FiniteGaugeGroupAction E GaugeElement)
    (identityAction : forall theta m t (s : GaugeElement theta m t)
      (omega : E.World theta m t), G.actWorld s omega = omega) :
    ¬ G.ManuscriptFacing := by
  intro h
  rcases E.parameterNonempty with ⟨theta⟩
  rcases h.2 theta 0 0 with ⟨s, omega, hmoves⟩
  exact hmoves (identityAction theta 0 0 s omega)

end V13FiniteGaugeGroupAction

/-- Faithful gauge interface: algebraic action, nontrivial rank/orbits, and the
conditional product-uniform law are separate visible obligations. -/
structure V13FaithfulGaugeInterface (E : V13QuantitativeEnsemble)
    (GaugeElement : E.Parameter -> Nat -> Nat -> Type u) where
  action : V13FiniteGaugeGroupAction E GaugeElement
  manuscriptFacing : action.ManuscriptFacing
  hiddenGaugeProduct : V13HiddenGaugeProductFrontier E

/-! ## Critical 5: declared-neutral pairs versus full public coverage -/

/-- Pair-neutrality of only the explicitly declared neutral sublanguage.  This
does not claim that the full public syntax satisfies Hypothesis 4.21. -/
structure V13DeclaredNeutralPairNeutrality (E : V13QuantitativeEnsemble) : Prop where
  pair_neutral :
    forall theta m t (j : E.TargetCoord theta m t)
      (primitive : E.PublicPrimitive theta m t)
      (omega0 omega1 : E.World theta m t),
      E.declaredNeutralPrimitive primitive ->
      E.oppositePair j omega0 omega1 ->
      E.primitiveValue primitive omega0 = E.primitiveValue primitive omega1

/-- Full-public-syntax form of Hypothesis 4.21.  Every visible primitive is
cataloged and is either declared neutral or has a charged normalization;
raw message/target/phase/witness/gauge payloads and any uncharged recovery of
such payloads are forbidden.  All quantifiers range over the full catalog,
not a selected neutral skeleton. -/
structure V13FullPublicSyntaxCoverage (E : V13QuantitativeEnsemble) : Prop where
  every_primitive_classified :
    forall theta m t (primitive : E.PublicPrimitive theta m t),
      primitive ∈ E.fullPublicSyntax theta m t ->
      E.declaredNeutralPrimitive primitive ∨
        E.chargedPrimitiveExpansion primitive
  no_forbidden_raw_payload :
    forall theta m t (primitive : E.PublicPrimitive theta m t),
      primitive ∈ E.fullPublicSyntax theta m t ->
      ¬ E.forbiddenRawPayload primitive
  no_uncharged_forbidden_recovery :
    forall theta m t (primitive : E.PublicPrimitive theta m t),
      primitive ∈ E.fullPublicSyntax theta m t ->
      ¬ E.recoversForbiddenWithoutCharge primitive

/-- Semantic target-hiding test for an entire public syntax object.  It is a
necessary consequence of full-public coverage and is useful for naming
concrete counterexamples. -/
def V13FullPublicSyntaxTargetHiding
    {Omega : Type u} {Syntax : Type v}
    (target : Omega -> Bool) (fullSyntax : Omega -> Syntax) : Prop :=
  ¬ exists recover : Syntax -> Bool,
    forall omega, target omega = recover (fullSyntax omega)

/-- Readout-hiding test for every verifier-valid witness over an entire public
syntax object. -/
def V13FullPublicSyntaxReadoutHiding
    {Public : Type u} {Witness : Type v} {Syntax : Type w}
    (verifier : Public -> Witness -> Prop) (readout : Witness -> Bool)
    (fullSyntax : Public -> Syntax) : Prop :=
  ¬ exists recover : Syntax -> Bool,
    forall Y W, verifier Y W -> readout W = recover (fullSyntax Y)

/-! ## Critical 2: the quantitative analytic frontiers -/

/-- Theorem 4.29 in full finite conditional form.  It quantifies over legal
adaptive prefixes, protected hidden conditions, values of those conditions,
and the polynomial charged-support regime.  The displayed inequality is
`D_infinity <= C_rho rho^R_safe + tau_geo(m)`.

Strict positivity/common support is an explicit hypothesis, never supplied by
the definition of max-divergence. -/
structure V13SafeQSSMFrontier (E : V13QuantitativeEnsemble) where
  C_rho : Real
  rho : Real
  tau_geo : Nat -> Real
  arityBound : Nat
  C_rho_finite_nonnegative : 0 <= C_rho
  rho_positive : 0 < rho
  rho_lt_one : rho < 1
  tau_geo_nonnegative : forall m, 0 <= tau_geo m
  strictPositiveCommonSupport :
    forall theta m t (Y : E.Public theta m t) (pref : E.Prefix theta m t)
      (q : E.Probe theta m t) (C : E.HiddenCondition theta m t)
      (c : E.HiddenValue theta m t),
      E.legalPrefix Y pref -> E.legalSafeProbe Y pref q ->
      E.hiddenConditionFarFromProbe C q (E.safeRadius theta m t) ->
      E.conditionDefinedAt theta m t
        (fun omega => E.publicPrefixCondition Y pref omega ∧
          E.hiddenConditionHolds C c omega) ->
      forall value,
        0 < E.conditionalProbeLaw Y pref q (fun _ => True) value
  softBuffer_max_qSSM :
    forall D theta m t (Y : E.Public theta m t)
      (pref : E.Prefix theta m t) (q : E.Probe theta m t)
      (C : E.HiddenCondition theta m t) (c : E.HiddenValue theta m t),
      E.parametersAdmissibleForClock theta D ->
      E.legalPrefix Y pref ->
      E.legalSafeProbe Y pref q ->
      E.probeArity q <= arityBound ->
      E.chargedGaugeSupportSize pref <= m ^ D ->
      E.hiddenConditionFarFromProbe C q (E.safeRadius theta m t) ->
      E.conditionDefinedAt theta m t
        (fun omega => E.publicPrefixCondition Y pref omega ∧
          E.hiddenConditionHolds C c omega) ->
      E.conditionalProbeMaxDivergence Y pref q C c <=
        C_rho * rho ^ E.safeRadius theta m t + tau_geo m

namespace V13SafeQSSMFrontier

def epsilonStep {E : V13QuantitativeEnsemble}
    (Q : V13SafeQSSMFrontier E) (theta : E.Parameter) (m t : Nat) : Real :=
  Q.C_rho * Q.rho ^ E.safeRadius theta m t + Q.tau_geo m

end V13SafeQSSMFrontier

/-- Hypothesis 7.14 verbatim in finite switched-set form: for every finite
gauge set `U`, the switched-target separation indicator sum is bounded by
`Delta_G * |U|`. -/
structure V13BoundedGaugeIncidenceFrontier
    (E : V13QuantitativeEnsemble) where
  Delta_G : Nat
  bounded_incidence :
    forall theta m t (U : Finset (E.GaugeCoord theta m t)),
      (E.switchedSet theta m t).sum (E.separationIndicator U) <=
      Delta_G * U.card

/-- Theorem 7.23 as a simultaneous high-probability statement for every
program of length at most `L`.  Finite-world probability replaces measure
notation, `log_2 m` is written as `log m / log 2`, and the manuscript's
`O(1)` prefix-coding term is the explicit constant `prefixOverhead`.

No budget conclusion is proved here; this is the named open target that must
follow from normalization, compatible couplings, qSSM, and gauge entropy. -/
structure V13AtomicEvidenceBudgetFrontier
    (E : V13QuantitativeEnsemble) (Q : V13SafeQSSMFrontier E)
    (I : V13BoundedGaugeIncidenceFrontier E) where
  prefixOverhead : Real
  prefixOverhead_nonnegative : 0 <= prefixOverhead
  simultaneous_atomic_budget :
    forall theta m t (A L Qtot : Nat),
      0 < A -> 1 < m ->
      E.probabilityAt theta m t (fun omega =>
        forall P : E.Program,
          E.programLength P <= L ->
          E.deterministicPolynomialObserver P ->
          E.neutralCoherent P omega ->
          E.safeCompatible P omega ->
          E.safeChargedOccurrences P (E.switchedSet theta m t) omega <= Qtot ->
          E.gapSum P (E.switchedSet theta m t) omega <=
            (1 / 2 : Real) *
              (Qtot * Q.epsilonStep theta m t +
                I.Delta_G *
                  (L +
                    E.cumulativeSafeLeakage P (E.switchedSet theta m t) omega /
                      Real.log 2 +
                    A * (Real.log m / Real.log 2) + prefixOverhead))) >=
        1 - 1 / (m : Real) ^ A

/-- Hypothesis 8.5 and Corollary 8.14 in their conditional form.  Every
switched coordinate, every admissible history, and every pivot-visible
predictor are quantified.  The error is definitionally exposed as
`C_mix rho_mix^L + tau_tree(m)`. -/
structure V13BoundaryMixingFrontier (E : V13QuantitativeEnsemble) where
  C_mix : Real
  rho_mix : Real
  tau_tree : Nat -> Real
  C_mix_nonnegative : 0 <= C_mix
  rho_mix_positive : 0 < rho_mix
  rho_mix_lt_one : rho_mix < 1
  tau_tree_nonnegative : forall m, 0 <= tau_tree m
  conditional_boundary_mixing :
    forall theta m t (Y : E.Public theta m t)
      (j : E.TargetCoord theta m t) (history : E.History theta m t)
      (L : Nat) (predictor : E.PivotSummary theta m t -> Bool),
      j ∈ E.switchedSet theta m t ->
      E.admissibleHistory j history ->
      E.conditionDefinedAt theta m t (E.publicHistoryCondition Y history) ->
      E.conditionalPredictorSuccess Y history L j predictor <=
        (1 / 2 : Real) + (C_mix * rho_mix ^ L + tau_tree m)

namespace V13BoundaryMixingFrontier

def epsilonMix {E : V13QuantitativeEnsemble}
    (B : V13BoundaryMixingFrontier E) (m L : Nat) : Real :=
  B.C_mix * B.rho_mix ^ L + B.tau_tree m

end V13BoundaryMixingFrontier

/-- Theorem 10.9 with the manuscript's quantifier order: for every fixed clock
`D`, choose parameters first, then positive `eta,kappa`; for all sufficiently
large `t`, the message has `D`-clocked complexity at least `eta*t` with
probability at least `1 - 2^(-kappa*t)`.

`Real.exp (-(kappa*t)*log 2)` is exactly `2^(-kappa*t)`. -/
structure V13GlobalMessageIncompressibilityFrontier
    (E : V13QuantitativeEnsemble) where
  /-- The numeric complexity observable has the manuscript's operational
  minimum-program meaning; it is not freely chosen analytic data. -/
  clockedKpolySemantics : V13ClockedKpolySemantics E
  parameterAtClock : Nat -> E.Parameter
  eta : Nat -> Real
  kappa : Nat -> Real
  threshold : Nat -> Nat
  parameters_chosen_after_clock : forall D,
    E.parametersAdmissibleForClock (parameterAtClock D) D
  eta_positive : forall D, 0 < eta D
  kappa_positive : forall D, 0 < kappa D
  global_message_incompressibility :
    forall D t, threshold D <= t ->
      let theta := parameterAtClock D
      let m := E.sizeAtMessageScale theta t
      E.probabilityAt theta m t
        (fun omega => (eta D * t : Real) <= E.clockedKpoly D omega) >=
          1 - Real.exp (-(kappa D * t) * Real.log 2)

/-- Section 11 on the **same** parameterized object selected by Theorem 10.9
at `Dstar`.  The constant program bound is uniform in `m,t,Y`, and the object
index is syntactically `lower.parameterAtClock Dstar`, preventing a silent
change of ensemble between lower and upper sides. -/
structure V13Section11SameObjectUpper
    (E : V13QuantitativeEnsemble)
    (lower : V13GlobalMessageIncompressibilityFrontier E) where
  Dstar : Nat
  constantProgramCost : Nat
  clocked_self_reduction_upper :
    forall t,
      let theta := lower.parameterAtClock Dstar
      let m := E.sizeAtMessageScale theta t
      forall omega : E.World theta m t,
        E.supported omega ->
        E.clockedKpoly Dstar omega <= constantProgramCost

/-- The four open quantitative mathematics packages on one ensemble: safe
qSSM, incidence plus the Atomic Evidence Budget, boundary mixing, and clocked
global message incompressibility.  Hidden-gauge product and the group action
remain explicit mechanical/probabilistic construction obligations outside
this four-field analytic bundle. -/
structure V13FaithfulAnalyticFrontiers (E : V13QuantitativeEnsemble) where
  safeQSSM : V13SafeQSSMFrontier E
  boundedGaugeIncidence : V13BoundedGaugeIncidenceFrontier E
  atomicEvidenceBudget :
    V13AtomicEvidenceBudgetFrontier E safeQSSM boundedGaugeIncidence
  boundaryMixing : V13BoundaryMixingFrontier E
  compressionStarSWHardness : V13GlobalMessageIncompressibilityFrontier E

end Mettapedia.Computability.PNP

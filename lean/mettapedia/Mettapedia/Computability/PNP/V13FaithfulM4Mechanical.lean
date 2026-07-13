import Mathlib.Data.List.GetD
import Mettapedia.Computability.PNP.V13FaithfulM4ConcreteObject

/-!
# Mechanical facts for the concrete regioned M4 scaffold

This module attaches the concrete five-band object to
`V13QuantitativeEnsemble`, `V13M4LayeredGeometry`, and
`V13M4LocalComponents`.  It proves sampler soundness, explicit support,
quotient equations, a positive-rank free gauge action, and the local
bounded-arity geometry facts.

The exact adaptive product law is not asserted in this mechanical base module.
The downstream adaptive-gauge module proves its faithful record from the
reconciled execution prefix, rather than replacing the prefix by a vacuous
unit type.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## The common quantitative ensemble -/

noncomputable def v13M4ConcreteEnsemble : V13QuantitativeEnsemble where
  Parameter := Unit
  parameterNonempty := ⟨()⟩
  World _ m t := V13M4ConcreteWorld m t
  worldFintype _ _ _ := inferInstance
  law _ m t := v13UniformFiniteLaw (V13M4ConcreteWorld m t)

  Public _ m t := V13M4ConcretePublic m t
  Witness _ m t := V13M4ConcreteWitness m t
  publicInput := v13M4ConcretePublicInput
  witnessOfWorld := v13M4ConcreteWitnessOfWorld
  verifier := v13M4ConcreteVerifier
  message := v13M4ConcreteMessage
  supported := fun _ => True

  Prefix _ m _ := V13M4ConcretePrefix m
  legalPrefix := fun _ pref => v13M4ConcreteLegalPrefix pref
  prefixConsistent := v13M4ConcretePrefixConsistent

  GaugeCoord _ m _ := V13M4ConcreteGaugeIndex m
  gaugeCoordDecidableEq := fun _ _ _ => inferInstance
  gaugeCoords := fun _ _ _ => Finset.univ
  gaugeValue := fun omega v => omega.g v
  gaugeSupport := v13M4ConcreteGaugeSupport

  Probe _ m _ := V13M4ConcreteGaugeIndex m
  ProbeValue _ _ _ := Bool
  probeValue := fun q omega => omega.bufferLeft q
  legalSafeProbe := fun _ pref q => q ∉ pref.bufferVisited
  probeArity := fun _ => 1
  safeRadius := fun _ _ _ => 1
  chargedGaugeSupportSize := fun pref =>
    (v13M4ConcreteGaugeSupport pref).card

  HiddenCondition _ _ _ := Unit
  HiddenValue _ _ _ := Unit
  hiddenConditionHolds := fun _ _ _ => True
  hiddenConditionFarFromProbe := fun _ _ _ => True

  TargetCoord _ _ t := V13M4ConcreteMessageIndex t
  targetCoordDecidableEq := fun _ _ _ => inferInstance
  switchedSet := fun _ _ _ => Finset.univ
  targetBit := fun omega j => omega.messageBits j
  gaugeSetCanSeparate := fun U j =>
    v13M4ConcreteMessageGaugeIndex j ∈ U
  gaugeSetCanSeparateDecidable := fun _ _ => inferInstance

  Program := Unit
  programLength := fun _ => 0
  deterministicPolynomialObserver := fun _ => True
  neutralCoherent := fun _ _ => True
  safeCompatible := fun _ _ => True
  safeChargedOccurrences := fun _ _ _ => 0
  cumulativeSafeLeakage := fun _ _ _ => 0
  coordinateGap := fun _ _ _ => 0

  History _ _ _ := Unit
  historyConsistent := fun _ _ => True
  admissibleHistory := fun _ _ => True
  PivotSummary _ _ _ := Unit
  pivotSummary := fun _ _ _ => ()

  PublicPrimitive _ m t := V13M4ConcretePublicPrimitive m t
  publicPrimitiveDecidableEq := fun _ _ _ => inferInstance
  fullPublicSyntax := fun _ _ _ => Finset.univ
  primitiveValue := v13M4ConcretePrimitiveValue
  declaredNeutralPrimitive := v13M4ConcreteDeclaredNeutral
  chargedPrimitiveExpansion := v13M4ConcreteChargedExpansion
  forbiddenRawPayload := fun _ => False
  recoversForbiddenWithoutCharge := v13M4ConcreteRecoversTargetWithoutCharge
  oppositePair := fun j omega0 omega1 =>
    omega0.messageBits j ≠ omega1.messageBits j

  sameGaugeFiber := v13M4ConcreteSameGaugeFiber
  parametersAdmissibleForClock := fun _ _ => True
  sizeAtMessageScale := fun _ t => t
  clockedKpoly := fun _ _ => 0

noncomputable abbrev V13M4ConcreteE := v13M4ConcreteEnsemble

/-! ## Layered path geometry -/

noncomputable def v13M4ConcreteGeometry : V13M4LayeredGeometry V13M4ConcreteE where
  Site _ m t := V13M4ConcreteSite m t
  siteFintype := fun _ _ _ => inferInstance
  siteDecidableEq := fun _ _ _ => inferInstance
  edge := v13M4ConcreteEdge
  distance := v13M4ConcreteDistance
  typeLabel := v13M4ConcreteSiteCode
  region := v13M4ConcreteRegion
  maximumDegreeBound := 2
  localArityBound := 3
  explicitGeometryCost := fun _ m t => 3 + 2 * (m + 1) + 2 * (t + 1)
  explicitGeometryPolynomialBound := fun _ m t =>
    3 + 2 * (m + 1) + 2 * (t + 1)
  geometry_enumeration_within_bound := by intro _ m t; rfl
  each_region_nonempty := by
    intro _ m t r
    cases r with
    | neutral => exact ⟨.neutral, rfl⟩
    | buffer => exact ⟨.buffer 0, rfl⟩
    | locked => exact ⟨.locked 0, rfl⟩
    | gauge => exact ⟨.gauge 0, rfl⟩
    | readout => exact ⟨.readout 0, rfl⟩
  isProtected := fun site =>
    v13M4ConcreteRegion site = .locked ∨
      v13M4ConcreteRegion site = .gauge ∨
        v13M4ConcreteRegion site = .readout
  protected_iff := by intro _ m t site; rfl
  Scope _ m t := V13M4ConcreteScope m t
  scopeFintype := fun _ _ _ => inferInstance
  scopeSites := v13M4ConcreteScopeSites
  scope_arity := by
    intro _ _ _ scope
    cases scope <;> simp [v13M4ConcreteScopeSites]

noncomputable abbrev V13M4ConcreteG := v13M4ConcreteGeometry

/-! ## Local components and the positive buffer law -/

noncomputable def v13M4ConcreteBufferMass {m t : Nat}
    (Y : V13M4ConcretePublic m t) (z : V13M4ConcreteGaugeVector m)
    (xi : V13M4ConcreteBufferAux m) : Real := by
  classical
  exact if v13M4ConcreteBufferPredicate Y z xi then
      1 / (2 : Real) ^ (m + 1)
    else 0

theorem v13M4Concrete_buffer_distance_protected {m t : Nat}
    (q : V13M4ConcreteGaugeIndex m) (site : V13M4ConcreteSite m t)
    (hprotected :
      v13M4ConcreteRegion site = .locked ∨
        v13M4ConcreteRegion site = .gauge ∨
          v13M4ConcreteRegion site = .readout) :
    1 <= v13M4ConcreteDistance (.buffer q) site := by
  cases site with
  | neutral => simp [v13M4ConcreteRegion] at hprotected
  | buffer v => simp [v13M4ConcreteRegion] at hprotected
  | locked i =>
      have hpos : 0 < Nat.dist (1 + q.val) (1 + (m + 1) + i.val) := by
        apply Nat.dist_pos_of_ne
        omega
      exact hpos
  | gauge v =>
      have hpos : 0 < Nat.dist (1 + q.val)
          (1 + (m + 1) + (t + 1) + v.val) := by
        apply Nat.dist_pos_of_ne
        omega
      exact hpos
  | readout i =>
      have hpos : 0 < Nat.dist (1 + q.val)
          (1 + (m + 1) + (t + 1) + (m + 1) + i.val) := by
        apply Nat.dist_pos_of_ne
        omega
      exact hpos

noncomputable def v13M4ConcreteComponents :
    V13M4LocalComponents V13M4ConcreteE V13M4ConcreteG where
  GaugeIndex _ m _ := V13M4ConcreteGaugeIndex m
  gaugeIndexFintype := fun _ _ _ => inferInstance
  gaugeIndexDecidableEq := fun _ _ _ => inferInstance
  gaugePlacement := fun v => .gauge v
  gaugePlacement_lands_in_gauge := by intro _ m t v; rfl

  LockPublic _ m t := V13M4ConcretePublic m t
  LockAux _ _ t := V13M4ConcreteMessageVector t
  BufferPublic _ m t := V13M4ConcretePublic m t
  BufferAux _ m _ := V13M4ConcreteBufferAux m
  LocalAux _ _ _ := Unit
  lockPublicOf := id
  bufferPublicOf := id

  xCoord := fun W => W.x
  gCoord := fun W => W.g
  zCoord := fun W => W.z
  lockAux := fun W => W.lockAux
  bufferAux := fun W => W.bufferAux
  localAux := fun W => W.localAux

  messageLength := fun _ _ t => t + 1
  messageLinearConstant := 1
  messageLinearConstant_positive := by norm_num
  message_length_lower := by
    intro _ _ t
    norm_num
  witness_message_length := by
    intro _ _ t W
    change (List.ofFn W.messageBits).length = t + 1
    exact List.length_ofFn

  lockPredicate := v13M4ConcreteLockPredicate
  readoutPredicate := v13M4ConcreteReadoutPredicate
  bufferPredicate := v13M4ConcreteBufferPredicate
  auxiliaryPredicate := fun _ _ => True

  bufferMass := v13M4ConcreteBufferMass
  bufferMass_nonnegative := by
    classical
    intro _ m t Y z xi
    rw [v13M4ConcreteBufferMass]
    split_ifs <;> positivity
  buffer_strictly_positive_on_admissible := by
    classical
    intro _ m t Y z xi hxi
    rw [v13M4ConcreteBufferMass]
    simp only [if_pos hxi]
    positivity
  buffer_mass_supported_on_acceptance := by
    classical
    intro _ m t Y z xi hmass
    by_contra hxi
    rw [v13M4ConcreteBufferMass] at hmass
    simp only [if_neg hxi] at hmass
    exact (lt_irrefl 0) hmass

  Probe _ m _ := V13M4ConcreteGaugeIndex m
  probeFintype := fun _ _ _ => inferInstance
  probeSupport := fun q => {.buffer q}
  probe_support_in_buffer := by
    intro _ _ _ q site hsite
    have hsiteEq : site = V13M4ConcreteSite.buffer q :=
      Finset.mem_singleton.mp hsite
    subst site
    rfl
  probe_arity := by intro _ _ _ q; norm_num [v13M4ConcreteGeometry]
  legalProbe := fun pref q => q ∉ pref.bufferVisited
  legal_probe_protected_distance := by
    intro _ m t pref q _ site hsite protectedSite hprotected
    have hsiteEq : site = V13M4ConcreteSite.buffer q := by simpa using hsite
    subst site
    change 1 <= v13M4ConcreteDistance (.buffer q) protectedSite
    exact v13M4Concrete_buffer_distance_protected q protectedSite hprotected

noncomputable abbrev V13M4ConcreteC := v13M4ConcreteComponents

/-! ## Sampler and component-conjunction facts -/

@[simp] theorem v13M4Concrete_message_length {m t : Nat}
    (W : V13M4ConcreteWitness m t) :
    (v13M4ConcreteMessage W).length = t + 1 := by
  simp [v13M4ConcreteMessage]

@[simp] theorem v13M4Concrete_message_getD {m t : Nat}
    (W : V13M4ConcreteWitness m t) (i : V13M4ConcreteMessageIndex t) :
    (v13M4ConcreteMessage W).getD i.val false = W.messageBits i := by
  rw [List.getD_eq_getElem]
  · simpa [v13M4ConcreteMessage] using
      (List.getElem_ofFn (f := W.messageBits) (i := i.val)
        (by simpa using i.isLt))
  · simpa [v13M4ConcreteMessage] using i.isLt

theorem v13M4Concrete_witnessOfWorld_lock {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteLockPredicate (v13M4ConcretePublicInput omega)
      omega.z (v13M4ConcreteWitnessOfWorld omega).lockAux
      (v13M4ConcreteMessage (v13M4ConcreteWitnessOfWorld omega)) := by
  constructor
  · simp [v13M4ConcreteMessage]
  · intro i
    rw [v13M4Concrete_message_getD]
    simp [v13M4ConcreteWitnessOfWorld]

theorem v13M4Concrete_witnessOfWorld_readout {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteReadoutPredicate (v13M4ConcretePublicInput omega)
      omega.z (v13M4ConcreteWitnessOfWorld omega).lockAux
      (v13M4ConcreteMessage (v13M4ConcreteWitnessOfWorld omega)) := by
  constructor
  · simp [v13M4ConcreteMessage]
  · intro i
    rw [v13M4Concrete_message_getD]
    simp [v13M4ConcreteWitnessOfWorld]

theorem v13M4Concrete_witnessOfWorld_quotient {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteQuotientEquations (v13M4ConcreteWitnessOfWorld omega) := by
  intro v
  simp [v13M4ConcreteWitnessOfWorld]

theorem v13M4Concrete_witnessOfWorld_buffer {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteBufferPredicate (v13M4ConcretePublicInput omega)
      omega.z (v13M4ConcreteWitnessOfWorld omega).bufferAux := by
  intro v
  simp [v13M4ConcreteWitnessOfWorld]

/-- Construction D.39/D.40 for the concrete sampled support. -/
theorem v13M4Concrete_sampler_sound
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (omega : V13M4ConcreteE.World theta m t) :
    V13M4ConcreteE.supported omega ->
      V13M4ConcreteE.verifier (V13M4ConcreteE.publicInput omega)
        (V13M4ConcreteE.witnessOfWorld omega) := by
  intro _
  exact ⟨v13M4Concrete_witnessOfWorld_lock omega,
    v13M4Concrete_witnessOfWorld_readout omega,
    v13M4Concrete_witnessOfWorld_quotient omega,
    v13M4Concrete_witnessOfWorld_buffer omega, trivial⟩

/-- The declared support is exactly the positive-mass support of the explicit
uniform sampler. -/
theorem v13M4Concrete_support_iff_positive_mass
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (omega : V13M4ConcreteE.World theta m t) :
    V13M4ConcreteE.supported omega <->
      0 < @V13FiniteLaw.mass (V13M4ConcreteE.World () m t)
        (V13M4ConcreteE.worldFintype () m t)
        (V13M4ConcreteE.law () m t) omega := by
  change True <-> 0 < 1 / (Fintype.card (V13M4ConcreteWorld m t) : Real)
  constructor
  · intro _
    positivity
  · intro _
    trivial

theorem v13M4Concrete_verifier_iff_componentRelation (m t : Nat)
    (Y : V13M4ConcreteE.Public () m t)
    (W : V13M4ConcreteE.Witness () m t) :
    V13M4ConcreteE.verifier Y W <->
      V13M4ConcreteC.ComponentWitnessRelation Y W := by
  rfl

/-- Exact D.7 field for the sampled public support. -/
theorem v13M4Concrete_lock_satisfiable_D7
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (Y : V13M4ConcreteE.Public theta m t)
    (hY : exists omega : V13M4ConcreteE.World theta m t,
      V13M4ConcreteE.supported omega ∧ V13M4ConcreteE.publicInput omega = Y) :
    exists z xi M,
      V13M4ConcreteC.lockPredicate (V13M4ConcreteC.lockPublicOf Y) z xi M ∧
        V13M4ConcreteC.readoutPredicate (V13M4ConcreteC.lockPublicOf Y) z xi M := by
  rcases hY with ⟨omega, _, rfl⟩
  exact ⟨omega.z, (v13M4ConcreteWitnessOfWorld omega).lockAux,
    v13M4ConcreteMessage (v13M4ConcreteWitnessOfWorld omega),
    v13M4Concrete_witnessOfWorld_lock omega,
    v13M4Concrete_witnessOfWorld_readout omega⟩

/-- Exact D.23 field for quotient assignments occurring in the sampler. -/
theorem v13M4Concrete_buffer_satisfiable_D23
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (Y : V13M4ConcreteE.Public theta m t)
    (z : V13M4ConcreteC.GaugeVector theta m t)
    (hYz : exists omega : V13M4ConcreteE.World theta m t,
      V13M4ConcreteE.supported omega ∧ V13M4ConcreteE.publicInput omega = Y ∧
        V13M4ConcreteC.zCoord (V13M4ConcreteE.witnessOfWorld omega) = z) :
    exists xi, V13M4ConcreteC.bufferPredicate
      (V13M4ConcreteC.bufferPublicOf Y) z xi := by
  rcases hYz with ⟨omega, _, rfl, hz⟩
  refine ⟨(v13M4ConcreteWitnessOfWorld omega).bufferAux, ?_⟩
  change v13M4ConcreteBufferPredicate (v13M4ConcretePublicInput omega) z
    (v13M4ConcreteWitnessOfWorld omega).bufferAux
  rw [← hz]
  exact v13M4Concrete_witnessOfWorld_buffer omega

/-- The almost-sure quotient half of `V13M4UniformGaugeLift`; the downstream
adaptive-gauge module proves the conditional subvector probability half. -/
theorem v13M4Concrete_quotient_equations_on_support
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (omega : V13M4ConcreteE.World theta m t) :
    V13M4ConcreteE.supported omega ->
      V13M4ConcreteC.QuotientEquations (V13M4ConcreteE.witnessOfWorld omega) := by
  intro _
  exact v13M4Concrete_witnessOfWorld_quotient omega

/-- Uniform sampler mass is invariant under every concrete gauge-vector
translation.  This is the finite static symmetry fact; it is not the adaptive
conditional product law through a partial evidence prefix. -/
theorem v13M4Concrete_sampler_mass_gauge_invariant
    (theta : V13M4ConcreteE.Parameter) (m t : Nat)
    (s : V13M4ConcreteGaugeVector m)
    (omega : V13M4ConcreteE.World theta m t) :
    @V13FiniteLaw.mass (V13M4ConcreteE.World theta m t)
        (V13M4ConcreteE.worldFintype theta m t) (V13M4ConcreteE.law theta m t)
        (v13M4ConcreteWorldGaugeAction s omega) =
      @V13FiniteLaw.mass (V13M4ConcreteE.World theta m t)
        (V13M4ConcreteE.worldFintype theta m t) (V13M4ConcreteE.law theta m t)
        omega := by
  rfl

/-! ## Positive-rank free gauge action -/

def v13M4ConcreteGaugeMul {m : Nat}
    (s r : V13M4ConcreteGaugeVector m) : V13M4ConcreteGaugeVector m :=
  fun v => xor (s v) (r v)

def v13M4ConcreteGaugeOne {m : Nat} : V13M4ConcreteGaugeVector m :=
  fun _ => false

theorem v13Bool_xor_assoc (a b c : Bool) :
    xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem v13Bool_xor_comm (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

theorem v13Bool_xor_self_left (a b : Bool) :
    xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

theorem v13Bool_xor_self_right (a b : Bool) :
    xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem v13Bool_simultaneous_xor (x g s : Bool) :
    xor (xor x s) (xor g s) = xor x g := by
  cases x <;> cases g <;> cases s <;> rfl

theorem v13Bool_xor_left_cancel {a b c : Bool}
    (h : xor a b = xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

@[ext] theorem V13M4ConcreteWorld.ext {m t : Nat}
    {omega omega' : V13M4ConcreteWorld m t}
    (htoken : omega.neutralToken = omega'.neutralToken)
    (hz : omega.z = omega'.z) (hg : omega.g = omega'.g)
    (hleft : omega.bufferLeft = omega'.bufferLeft)
    (hmessage : omega.messageBits = omega'.messageBits) :
    omega = omega' := by
  cases omega
  cases omega'
  simp_all

@[ext] theorem V13M4ConcreteWitness.ext {m t : Nat}
    {W W' : V13M4ConcreteWitness m t}
    (hx : W.x = W'.x) (hg : W.g = W'.g) (hz : W.z = W'.z)
    (hlock : W.lockAux = W'.lockAux)
    (hbuffer : W.bufferAux = W'.bufferAux)
    (hlocal : W.localAux = W'.localAux)
    (hmessage : W.messageBits = W'.messageBits) :
    W = W' := by
  cases W
  cases W'
  simp_all

theorem v13M4Concrete_quotient_action_iff {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) (W : V13M4ConcreteWitness m t) :
    v13M4ConcreteQuotientEquations (v13M4ConcreteWitnessGaugeAction s W) <->
      v13M4ConcreteQuotientEquations W := by
  constructor <;> intro h v
  · have hv := h v
    change W.z v = xor (xor (W.x v) (s v)) (xor (W.g v) (s v)) at hv
    rw [v13Bool_simultaneous_xor] at hv
    exact hv
  · have hv := h v
    change W.z v = xor (xor (W.x v) (s v)) (xor (W.g v) (s v))
    rw [v13Bool_simultaneous_xor]
    exact hv

theorem v13M4Concrete_verifier_gauge_invariant {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) (Y : V13M4ConcretePublic m t)
    (W : V13M4ConcreteWitness m t) :
    v13M4ConcreteVerifier Y (v13M4ConcreteWitnessGaugeAction s W) <->
      v13M4ConcreteVerifier Y W := by
  simp only [v13M4ConcreteVerifier, v13M4ConcreteWitnessGaugeAction,
    v13M4ConcreteMessage]
  constructor <;> rintro ⟨hlock, hread, hquot, hbuf, _⟩
  · exact ⟨hlock, hread,
      (v13M4Concrete_quotient_action_iff s W).mp hquot, hbuf, trivial⟩
  · exact ⟨hlock, hread,
      (v13M4Concrete_quotient_action_iff s W).mpr hquot, hbuf, trivial⟩

theorem v13M4ConcreteWorldGaugeAction_one {m t : Nat}
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteWorldGaugeAction v13M4ConcreteGaugeOne omega = omega := by
  apply V13M4ConcreteWorld.ext
  · rfl
  · rfl
  · funext v
    change xor (omega.g v) false = omega.g v
    cases omega.g v <;> rfl
  · rfl
  · rfl

theorem v13M4ConcreteWorldGaugeAction_mul {m t : Nat}
    (r s : V13M4ConcreteGaugeVector m) (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteWorldGaugeAction (v13M4ConcreteGaugeMul r s) omega =
      v13M4ConcreteWorldGaugeAction r
        (v13M4ConcreteWorldGaugeAction s omega) := by
  apply V13M4ConcreteWorld.ext
  · rfl
  · rfl
  · funext v
    change xor (omega.g v) (xor (r v) (s v)) =
      xor (xor (omega.g v) (s v)) (r v)
    rw [v13Bool_xor_assoc]
    congr 1
    exact v13Bool_xor_comm (r v) (s v)
  · rfl
  · rfl

theorem v13M4ConcreteWitnessGaugeAction_one {m t : Nat}
    (W : V13M4ConcreteWitness m t) :
    v13M4ConcreteWitnessGaugeAction v13M4ConcreteGaugeOne W = W := by
  apply V13M4ConcreteWitness.ext
  · funext v
    change xor (W.x v) false = W.x v
    cases W.x v <;> rfl
  · funext v
    change xor (W.g v) false = W.g v
    cases W.g v <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem v13M4ConcreteWitnessGaugeAction_mul {m t : Nat}
    (r s : V13M4ConcreteGaugeVector m) (W : V13M4ConcreteWitness m t) :
    v13M4ConcreteWitnessGaugeAction (v13M4ConcreteGaugeMul r s) W =
      v13M4ConcreteWitnessGaugeAction r
        (v13M4ConcreteWitnessGaugeAction s W) := by
  apply V13M4ConcreteWitness.ext
  · funext v
    change xor (W.x v) (xor (r v) (s v)) =
      xor (xor (W.x v) (s v)) (r v)
    rw [v13Bool_xor_assoc]
    congr 1
    exact v13Bool_xor_comm (r v) (s v)
  · funext v
    change xor (W.g v) (xor (r v) (s v)) =
      xor (xor (W.g v) (s v)) (r v)
    rw [v13Bool_xor_assoc]
    congr 1
    exact v13Bool_xor_comm (r v) (s v)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem v13M4Concrete_worldWitness_equivariant {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteWitnessOfWorld (v13M4ConcreteWorldGaugeAction s omega) =
      v13M4ConcreteWitnessGaugeAction s
        (v13M4ConcreteWitnessOfWorld omega) := by
  apply V13M4ConcreteWitness.ext
  · funext v
    change xor (omega.z v) (xor (omega.g v) (s v)) =
      xor (xor (omega.z v) (omega.g v)) (s v)
    exact (v13Bool_xor_assoc (omega.z v) (omega.g v) (s v)).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem v13M4Concrete_worldAction_free {m t : Nat}
    (s r : V13M4ConcreteGaugeVector m) (omega : V13M4ConcreteWorld m t)
    (hact : v13M4ConcreteWorldGaugeAction s omega =
      v13M4ConcreteWorldGaugeAction r omega) :
    s = r := by
  funext v
  have hv := congrFun (congrArg V13M4ConcreteWorld.g hact) v
  change xor (omega.g v) (s v) = xor (omega.g v) (r v) at hv
  exact v13Bool_xor_left_cancel hv

theorem v13M4Concrete_sameFiber_iff_orbit {m t : Nat}
    (omega omega' : V13M4ConcreteWorld m t) :
    v13M4ConcreteSameGaugeFiber omega omega' <->
      exists s : V13M4ConcreteGaugeVector m,
        v13M4ConcreteWorldGaugeAction s omega = omega' := by
  constructor
  · rintro ⟨htoken, hz, hleft, hmessage⟩
    let s : V13M4ConcreteGaugeVector m :=
      fun v => xor (omega.g v) (omega'.g v)
    refine ⟨s, ?_⟩
    apply V13M4ConcreteWorld.ext
    · exact htoken
    · exact hz
    · funext v
      change xor (omega.g v) (xor (omega.g v) (omega'.g v)) = omega'.g v
      exact v13Bool_xor_self_left (omega.g v) (omega'.g v)
    · exact hleft
    · exact hmessage
  · rintro ⟨s, hact⟩
    rw [← hact]
    exact ⟨rfl, rfl, rfl, rfl⟩

noncomputable def v13M4ConcreteGaugeAction :
    V13FiniteGaugeGroupAction V13M4ConcreteE
      (fun _ m _ => V13M4ConcreteGaugeVector m) where
  gaugeElementFintype := fun _ _ _ => inferInstance
  one := v13M4ConcreteGaugeOne
  mul := v13M4ConcreteGaugeMul
  inv := id
  mul_assoc := by
    intro _ _ _ r s q
    funext v
    exact v13Bool_xor_assoc (r v) (s v) (q v)
  one_mul := by
    intro _ _ _ s
    funext v
    change xor false (s v) = s v
    cases s v <;> rfl
  mul_one := by
    intro _ _ _ s
    funext v
    change xor (s v) false = s v
    cases s v <;> rfl
  inv_mul := by
    intro _ _ _ s
    funext v
    change xor (s v) (s v) = false
    cases s v <;> rfl

  actWorld := v13M4ConcreteWorldGaugeAction
  actWitness := v13M4ConcreteWitnessGaugeAction
  one_act_world := by
    intro _ _ _ omega
    exact v13M4ConcreteWorldGaugeAction_one omega
  mul_act_world := by
    intro _ _ _ r s omega
    exact v13M4ConcreteWorldGaugeAction_mul r s omega
  one_act_witness := by
    intro _ _ _ W
    exact v13M4ConcreteWitnessGaugeAction_one W
  mul_act_witness := by
    intro _ _ _ r s W
    exact v13M4ConcreteWitnessGaugeAction_mul r s W

  public_invariant := by intro _ _ _ _ _; rfl
  verifier_invariant := by
    intro _ m t s Y W
    exact v13M4Concrete_verifier_gauge_invariant s Y W
  message_invariant := by intro _ _ _ _ _; rfl
  worldWitness_equivariant := by
    intro _ _ _ s omega
    exact v13M4Concrete_worldWitness_equivariant s omega

  worldAction_free := by
    intro _ _ _ s r omega
    exact v13M4Concrete_worldAction_free s r omega
  sameFiber_iff_orbit := by
    intro _ _ _ omega omega'
    exact v13M4Concrete_sameFiber_iff_orbit omega omega'
  gaugeRank := fun _ m _ => m + 1
  rank_eq_coordinate_card := by
    intro _ m t
    change m + 1 = (Finset.univ : Finset (Fin (m + 1))).card
    simp

/-- The vector action has positive rank and an actually moving orbit at every
size, including `m = 0`. -/
theorem v13M4ConcreteGaugeAction_manuscriptFacing :
    v13M4ConcreteGaugeAction.ManuscriptFacing := by
  constructor
  · intro _ m _
    change 0 < m + 1
    omega
  · intro _ m t
    let s : V13M4ConcreteGaugeVector m := fun _ => true
    let omega : V13M4ConcreteWorld m t :=
      { neutralToken := false
        z := fun _ => false
        g := fun _ => false
        bufferLeft := fun _ => false
        messageBits := fun _ => false }
    refine ⟨s, omega, ?_⟩
    intro hfixed
    have hv := congrFun (congrArg V13M4ConcreteWorld.g hfixed)
      (0 : V13M4ConcreteGaugeIndex m)
    change true = false at hv
    contradiction

/-! ## Appendix-I local truth-table CNF compilation -/

/-- The visible CNF variable blocks from Appendix I.15. -/
inductive V13M4ConcreteCNFVar (m t : Nat) where
  | x : V13M4ConcreteGaugeIndex m -> V13M4ConcreteCNFVar m t
  | g : V13M4ConcreteGaugeIndex m -> V13M4ConcreteCNFVar m t
  | z : V13M4ConcreteGaugeIndex m -> V13M4ConcreteCNFVar m t
  | lockAux : V13M4ConcreteMessageIndex t -> V13M4ConcreteCNFVar m t
  | bufferLeft : V13M4ConcreteGaugeIndex m -> V13M4ConcreteCNFVar m t
  | bufferRight : V13M4ConcreteGaugeIndex m -> V13M4ConcreteCNFVar m t
  | message : V13M4ConcreteMessageIndex t -> V13M4ConcreteCNFVar m t
deriving DecidableEq, Repr

/-- The four forbidden-pattern clauses for `c = a XOR b`. -/
def v13M4ConcreteXorCNF {Var : Type}
    (a b c : Var) : ConcreteCNF.Formula Var :=
  [ [ .pos a, .pos b, .neg c ],
    [ .pos a, .neg b, .pos c ],
    [ .neg a, .pos b, .pos c ],
    [ .neg a, .neg b, .neg c ] ]

theorem v13M4ConcreteXorCNF_sat_iff {Var : Type}
    (a b c : Var) (alpha : ConcreteCNF.Assignment Var) :
    ConcreteCNF.IsSatFormula (v13M4ConcreteXorCNF a b c) alpha <->
      alpha c = xor (alpha a) (alpha b) := by
  cases ha : alpha a <;> cases hb : alpha b <;> cases hc : alpha c <;>
    simp [v13M4ConcreteXorCNF, ConcreteCNF.IsSatFormula,
      ConcreteCNF.IsSatClause, ConcreteCNF.Literal.eval, ha, hb, hc]

theorem v13M4Concrete_isSatFormula_flatMap_iff
    {Index Var : Type} (indices : List Index)
    (formula : Index -> ConcreteCNF.Formula Var)
    (alpha : ConcreteCNF.Assignment Var) :
    ConcreteCNF.IsSatFormula (indices.flatMap formula) alpha <->
      forall index, index ∈ indices ->
        ConcreteCNF.IsSatFormula (formula index) alpha := by
  constructor
  · intro h index hindex clause hclause
    exact h clause (List.mem_flatMap.mpr ⟨index, hindex, hclause⟩)
  · intro h clause hclause
    rcases List.mem_flatMap.mp hclause with ⟨index, hindex, hclause⟩
    exact h index hindex clause hclause

def v13M4ConcreteQuotientCNF {m t : Nat} :
    ConcreteCNF.Formula (V13M4ConcreteCNFVar m t) :=
  (List.ofFn fun v : V13M4ConcreteGaugeIndex m => v).flatMap fun v =>
    v13M4ConcreteXorCNF (.x v) (.g v) (.z v)

def v13M4ConcreteLockCNF {m t : Nat} :
    ConcreteCNF.Formula (V13M4ConcreteCNFVar m t) :=
  (List.ofFn fun i : V13M4ConcreteMessageIndex t => i).flatMap fun i =>
    v13M4ConcreteXorCNF (.message i)
      (.z (v13M4ConcreteMessageGaugeIndex i)) (.lockAux i)

def v13M4ConcreteBufferCNF {m t : Nat} :
    ConcreteCNF.Formula (V13M4ConcreteCNFVar m t) :=
  (List.ofFn fun v : V13M4ConcreteGaugeIndex m => v).flatMap fun v =>
    v13M4ConcreteXorCNF (.bufferLeft v) (.bufferRight v) (.z v)

/-- Appendix-I.16 local list: quotient, lock/readout connector, and buffer
families.  The formula is independent of the neutral public token. -/
def v13M4ConcreteFormula {m t : Nat}
    (_Y : V13M4ConcretePublic m t) :
    ConcreteCNF.Formula (V13M4ConcreteCNFVar m t) :=
  v13M4ConcreteQuotientCNF ++ v13M4ConcreteLockCNF ++
    v13M4ConcreteBufferCNF

def v13M4ConcreteExtractWitness {m t : Nat}
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) :
    V13M4ConcreteWitness m t where
  x v := alpha (.x v)
  g v := alpha (.g v)
  z v := alpha (.z v)
  lockAux i := alpha (.lockAux i)
  bufferAux v := (alpha (.bufferLeft v), alpha (.bufferRight v))
  localAux := ()
  messageBits i := alpha (.message i)

def v13M4ConcreteExtendWitness {m t : Nat}
    (_Y : V13M4ConcretePublic m t) (W : V13M4ConcreteWitness m t) :
    ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)
  | .x v => W.x v
  | .g v => W.g v
  | .z v => W.z v
  | .lockAux i => W.lockAux i
  | .bufferLeft v => (W.bufferAux v).1
  | .bufferRight v => (W.bufferAux v).2
  | .message i => W.messageBits i

def v13M4ConcreteMessageProjection {m t : Nat}
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) : List Bool :=
  List.ofFn fun i : V13M4ConcreteMessageIndex t => alpha (.message i)

theorem v13M4ConcreteQuotientCNF_sat_iff {m t : Nat}
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) :
    ConcreteCNF.IsSatFormula v13M4ConcreteQuotientCNF alpha <->
      forall v : V13M4ConcreteGaugeIndex m,
        alpha (.z v) = xor (alpha (.x v)) (alpha (.g v)) := by
  rw [v13M4ConcreteQuotientCNF,
    v13M4Concrete_isSatFormula_flatMap_iff]
  constructor
  · intro h v
    exact (v13M4ConcreteXorCNF_sat_iff (.x v) (.g v) (.z v) alpha).mp
      (h v (List.mem_ofFn.mpr ⟨v, rfl⟩))
  · intro h v _
    exact (v13M4ConcreteXorCNF_sat_iff (.x v) (.g v) (.z v) alpha).mpr
      (h v)

theorem v13M4ConcreteLockCNF_sat_iff {m t : Nat}
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) :
    ConcreteCNF.IsSatFormula v13M4ConcreteLockCNF alpha <->
      forall i : V13M4ConcreteMessageIndex t,
        alpha (.lockAux i) = xor (alpha (.message i))
          (alpha (.z (v13M4ConcreteMessageGaugeIndex i))) := by
  rw [v13M4ConcreteLockCNF, v13M4Concrete_isSatFormula_flatMap_iff]
  constructor
  · intro h i
    exact (v13M4ConcreteXorCNF_sat_iff (.message i)
      (.z (v13M4ConcreteMessageGaugeIndex i)) (.lockAux i) alpha).mp
        (h i (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro h i _
    exact (v13M4ConcreteXorCNF_sat_iff (.message i)
      (.z (v13M4ConcreteMessageGaugeIndex i)) (.lockAux i) alpha).mpr (h i)

theorem v13M4ConcreteBufferCNF_sat_iff {m t : Nat}
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) :
    ConcreteCNF.IsSatFormula v13M4ConcreteBufferCNF alpha <->
      forall v : V13M4ConcreteGaugeIndex m,
        alpha (.z v) = xor (alpha (.bufferLeft v)) (alpha (.bufferRight v)) := by
  rw [v13M4ConcreteBufferCNF, v13M4Concrete_isSatFormula_flatMap_iff]
  constructor
  · intro h v
    exact (v13M4ConcreteXorCNF_sat_iff (.bufferLeft v) (.bufferRight v)
      (.z v) alpha).mp (h v (List.mem_ofFn.mpr ⟨v, rfl⟩))
  · intro h v _
    exact (v13M4ConcreteXorCNF_sat_iff (.bufferLeft v) (.bufferRight v)
      (.z v) alpha).mpr (h v)

theorem v13M4ConcreteFormula_sat_iff {m t : Nat}
    (Y : V13M4ConcretePublic m t)
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t)) :
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) alpha <->
      (forall v : V13M4ConcreteGaugeIndex m,
        alpha (.z v) = xor (alpha (.x v)) (alpha (.g v))) ∧
      (forall i : V13M4ConcreteMessageIndex t,
        alpha (.lockAux i) = xor (alpha (.message i))
          (alpha (.z (v13M4ConcreteMessageGaugeIndex i)))) ∧
      (forall v : V13M4ConcreteGaugeIndex m,
        alpha (.z v) = xor (alpha (.bufferLeft v)) (alpha (.bufferRight v))) := by
  rw [v13M4ConcreteFormula, ConcreteCNF.isSatFormula_append_iff,
    ConcreteCNF.isSatFormula_append_iff, v13M4ConcreteQuotientCNF_sat_iff,
    v13M4ConcreteLockCNF_sat_iff, v13M4ConcreteBufferCNF_sat_iff]
  tauto

theorem v13M4Concrete_extract_extend {m t : Nat}
    (Y : V13M4ConcretePublic m t) (W : V13M4ConcreteWitness m t) :
    v13M4ConcreteExtractWitness (v13M4ConcreteExtendWitness Y W) = W := by
  apply V13M4ConcreteWitness.ext <;> rfl

theorem v13M4Concrete_cnf_sound {m t : Nat}
    (Y : V13M4ConcretePublic m t)
    (alpha : ConcreteCNF.Assignment (V13M4ConcreteCNFVar m t))
    (hsat : ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y) alpha) :
    v13M4ConcreteVerifier Y (v13M4ConcreteExtractWitness alpha) := by
  rcases (v13M4ConcreteFormula_sat_iff Y alpha).mp hsat with
    ⟨hquot, hlock, hbuffer⟩
  refine ⟨?_, ?_, hquot, hbuffer, trivial⟩
  · constructor
    · simp [v13M4ConcreteMessage]
    · intro i
      rw [v13M4Concrete_message_getD]
      exact hlock i
  · constructor
    · simp [v13M4ConcreteMessage]
    · intro i
      rw [v13M4Concrete_message_getD]
      have hi := hlock i
      change alpha (.message i) =
        xor (alpha (.lockAux i))
          (alpha (.z (v13M4ConcreteMessageGaugeIndex i)))
      rw [hi]
      exact (v13Bool_xor_self_right _ _).symm

theorem v13M4Concrete_cnf_complete {m t : Nat}
    (Y : V13M4ConcretePublic m t) (W : V13M4ConcreteWitness m t)
    (hvalid : v13M4ConcreteVerifier Y W) :
    ConcreteCNF.IsSatFormula (v13M4ConcreteFormula Y)
        (v13M4ConcreteExtendWitness Y W) ∧
      v13M4ConcreteExtractWitness (v13M4ConcreteExtendWitness Y W) = W := by
  refine ⟨(v13M4ConcreteFormula_sat_iff Y _).mpr ?_,
    v13M4Concrete_extract_extend Y W⟩
  rcases hvalid with ⟨hlock, _, hquot, hbuffer, _⟩
  refine ⟨hquot, ?_, hbuffer⟩
  intro i
  change W.lockAux i = xor (W.messageBits i)
    (W.z (v13M4ConcreteMessageGaugeIndex i))
  have hi := hlock.2 i
  rw [v13M4Concrete_message_getD] at hi
  exact hi

theorem v13M4Concrete_formula_length {m t : Nat}
    (Y : V13M4ConcretePublic m t) :
    (v13M4ConcreteFormula Y).length =
      4 * (2 * (m + 1) + (t + 1)) := by
  simp [v13M4ConcreteFormula, v13M4ConcreteQuotientCNF,
    v13M4ConcreteLockCNF, v13M4ConcreteBufferCNF,
    v13M4ConcreteXorCNF, List.ofFn_const, Function.comp_def]
  omega

def v13M4ConcreteCNFSizeBound (_ : Unit) (m t : Nat) : Nat :=
  4 * (2 * (m + 1) + (t + 1))

noncomputable def v13M4ConcreteCNFCompilation :
    V13M4UniformCNFCompilation V13M4ConcreteE
      (fun _ m t => V13M4ConcreteCNFVar m t) where
  cnfVarDecidableEq := fun _ _ _ => inferInstance
  formula := v13M4ConcreteFormula
  extractWitness := v13M4ConcreteExtractWitness
  extendWitness := v13M4ConcreteExtendWitness
  messageProjection := v13M4ConcreteMessageProjection
  cnf_sound := by
    intro _ _ _ Y alpha
    exact v13M4Concrete_cnf_sound Y alpha
  cnf_complete := by
    intro _ _ _ Y W
    exact v13M4Concrete_cnf_complete Y W
  fixed_projection_reads_message := by
    intro _ m t Y alpha _
    rfl
  compileCost := v13M4ConcreteCNFSizeBound
  compilePolynomialBound := v13M4ConcreteCNFSizeBound
  formulaSizePolynomialBound := v13M4ConcreteCNFSizeBound
  compilation_uniform := by intro _ m t; rfl
  formula_polynomial_size := by
    intro _ m t Y
    rw [v13M4Concrete_formula_length]
    rfl

end Mettapedia.Computability.PNP

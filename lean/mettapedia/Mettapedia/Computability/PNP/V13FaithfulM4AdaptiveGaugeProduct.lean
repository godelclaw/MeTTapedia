import Mettapedia.Computability.PNP.V13FaithfulM4ExecutionTrace

/-!
# Adaptive hidden-gauge product law on the faithful M4 scaffold

The concrete prefix used here is the reconciled move-4a execution prefix.  It
records public-instance conditioning separately, every legal safe-buffer
outcome, every raw-gauge outcome, every quotient outcome, and the exact charged
gauge support.  The quantitative `legalPrefix`, `prefixConsistent`, and
`gaugeSupport` fields are those same definitions.

The counting argument uses the subgroup of XOR gauge translations supported on
a finite fresh set `J`.  A legal prefix is invariant under this subgroup when
`J` is disjoint from its charged support.  Translation gives bijections between
all assignments on `J`; those events partition the conditioning event.  Since
the sampler mass is translation-invariant, every assignment has conditional
probability exactly `2^(-|J|)`.

All probabilities are the faithful record's finite real-valued probabilities.
There is no asymptotic, rational, or unconditional simplification.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Gauge assignment events and supported translations -/

abbrev V13M4ConcreteGaugeAssignment {m : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m)) :=
  (v : {v // v ∈ J}) -> Bool

def v13M4ConcreteGaugeEvent {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (gamma : V13M4ConcreteGaugeAssignment J)
    (omega : V13M4ConcreteWorld m t) : Prop :=
  forall v, forall hv : v ∈ J, omega.g v = gamma ⟨v, hv⟩

def v13M4ConcreteGaugeRestriction {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (omega : V13M4ConcreteWorld m t) :
    V13M4ConcreteGaugeAssignment J :=
  fun v => omega.g v.1

theorem v13M4ConcreteGaugeEvent_iff {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (gamma : V13M4ConcreteGaugeAssignment J)
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteGaugeEvent J gamma omega <->
      gamma = v13M4ConcreteGaugeRestriction J omega := by
  constructor
  · intro h
    funext v
    exact (h v v.property).symm
  · intro h v hv
    exact congrFun h ⟨v, hv⟩ |>.symm

def v13M4ConcreteGaugeAssignmentToggle {m : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (gamma delta : V13M4ConcreteGaugeAssignment J) :
    V13M4ConcreteGaugeVector m :=
  fun v => if hv : v ∈ J then
    xor (gamma ⟨v, hv⟩) (delta ⟨v, hv⟩)
  else false

def v13M4ConcreteWorldGaugeEquiv {m t : Nat}
    (s : V13M4ConcreteGaugeVector m) :
    V13M4ConcreteWorld m t ≃ V13M4ConcreteWorld m t where
  toFun := v13M4ConcreteWorldGaugeAction s
  invFun := v13M4ConcreteWorldGaugeAction s
  left_inv := by
    intro omega
    apply V13M4ConcreteWorld.ext <;> try rfl
    funext v
    exact v13Bool_xor_self_right (omega.g v) (s v)
  right_inv := by
    intro omega
    apply V13M4ConcreteWorld.ext <;> try rfl
    funext v
    exact v13Bool_xor_self_right (omega.g v) (s v)

theorem v13M4ConcreteGaugeEvent_toggle_iff {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (gamma delta : V13M4ConcreteGaugeAssignment J)
    (omega : V13M4ConcreteWorld m t) :
    v13M4ConcreteGaugeEvent J delta
        (v13M4ConcreteWorldGaugeAction
          (v13M4ConcreteGaugeAssignmentToggle J gamma delta) omega) <->
      v13M4ConcreteGaugeEvent J gamma omega := by
  constructor
  · intro h v hv
    have hvalue := h v hv
    change xor (omega.g v)
      (v13M4ConcreteGaugeAssignmentToggle J gamma delta v) =
        delta ⟨v, hv⟩ at hvalue
    simp only [v13M4ConcreteGaugeAssignmentToggle, dif_pos hv] at hvalue
    cases homega : omega.g v <;>
      cases hgamma : gamma ⟨v, hv⟩ <;>
      cases hdelta : delta ⟨v, hv⟩ <;> simp_all
  · intro h v hv
    have hvalue := h v hv
    change xor (omega.g v)
      (v13M4ConcreteGaugeAssignmentToggle J gamma delta v) =
        delta ⟨v, hv⟩
    simp only [v13M4ConcreteGaugeAssignmentToggle, dif_pos hv]
    rw [hvalue]
    exact v13Bool_xor_self_left _ _

/-! ## Finite orbit counting -/

theorem v13FiniteLaw_probability_eq_indicator {Omega : Type}
    [Fintype Omega] (mu : V13FiniteLaw Omega) (event : Omega -> Prop)
    [DecidablePred event] :
    mu.probability event =
      Finset.univ.sum (fun omega => if event omega then mu.mass omega else 0) := by
  classical
  unfold V13FiniteLaw.probability
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr
  · ext omega
    simp
  · intro omega _
    rfl

theorem v13M4Concrete_jointGaugeProbability_assignment_sum {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (condition : V13M4ConcreteWorld m t -> Prop) :
    let mu : V13FiniteLaw (V13M4ConcreteWorld m t) :=
      v13UniformFiniteLaw (V13M4ConcreteWorld m t)
    Finset.univ.sum (fun gamma : V13M4ConcreteGaugeAssignment J =>
      mu.probability (fun omega =>
        v13M4ConcreteGaugeEvent J gamma omega ∧ condition omega)) =
      mu.probability condition := by
  classical
  dsimp only
  rw [v13FiniteLaw_probability_eq_indicator]
  simp_rw [v13FiniteLaw_probability_eq_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hcondition : condition omega
  · simp only [hcondition, and_true, if_true]
    simp_rw [v13M4ConcreteGaugeEvent_iff]
    simp
  · simp [hcondition]

/-- Orbit-counting core.  Any positive conditioning event invariant under the
XOR translations supported on `J` leaves `g_J` exactly product-uniform. -/
theorem v13M4Concrete_conditionalGaugeProduct_of_invariant {m t : Nat}
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (condition : V13M4ConcreteWorld m t -> Prop)
    (hcondition :
      V13M4ConcreteE.conditionDefinedAt () m t condition)
    (hinvariant : forall
      (gamma delta : V13M4ConcreteGaugeAssignment J)
      (omega : V13M4ConcreteWorld m t),
      condition
          (v13M4ConcreteWorldGaugeAction
            (v13M4ConcreteGaugeAssignmentToggle J gamma delta) omega) <->
        condition omega)
    (gamma : V13M4ConcreteGaugeAssignment J) :
    V13M4ConcreteE.conditionalProbabilityAt () m t
        (v13M4ConcreteGaugeEvent J gamma) condition =
      1 / (2 : Real) ^ J.card := by
  classical
  let mu : V13FiniteLaw (V13M4ConcreteWorld m t) :=
    v13UniformFiniteLaw (V13M4ConcreteWorld m t)
  let joint : V13M4ConcreteGaugeAssignment J -> Real := fun delta =>
    mu.probability (fun omega =>
      v13M4ConcreteGaugeEvent J delta omega ∧ condition omega)
  have hjoint_equal : forall delta, joint delta = joint gamma := by
    intro delta
    dsimp only [joint]
    rw [v13FiniteLaw_probability_eq_indicator,
      v13FiniteLaw_probability_eq_indicator]
    let e := v13M4ConcreteWorldGaugeEquiv
      (m := m) (t := t) (v13M4ConcreteGaugeAssignmentToggle J delta gamma)
    calc
      Finset.univ.sum (fun omega =>
          if v13M4ConcreteGaugeEvent J delta omega ∧ condition omega then
            mu.mass omega else 0) =
        Finset.univ.sum (fun omega =>
          if v13M4ConcreteGaugeEvent J gamma (e omega) ∧ condition (e omega)
          then mu.mass (e omega) else 0) := by
            apply Finset.sum_congr rfl
            intro omega _
            change (if v13M4ConcreteGaugeEvent J delta omega ∧ condition omega
              then mu.mass omega else 0) =
              if v13M4ConcreteGaugeEvent J gamma
                  (v13M4ConcreteWorldGaugeAction
                    (v13M4ConcreteGaugeAssignmentToggle J delta gamma) omega) ∧
                  condition
                    (v13M4ConcreteWorldGaugeAction
                      (v13M4ConcreteGaugeAssignmentToggle J delta gamma) omega)
              then mu.mass
                (v13M4ConcreteWorldGaugeAction
                  (v13M4ConcreteGaugeAssignmentToggle J delta gamma) omega)
              else 0
            rw [v13M4ConcreteGaugeEvent_toggle_iff, hinvariant]
            rfl
      _ = Finset.univ.sum (fun omega =>
          if v13M4ConcreteGaugeEvent J gamma omega ∧ condition omega then
            mu.mass omega else 0) := by
            let f : V13M4ConcreteWorld m t -> Real := fun omega =>
              if v13M4ConcreteGaugeEvent J gamma omega ∧ condition omega then
                mu.mass omega else 0
            change Finset.univ.sum (fun omega => f (e omega)) =
              Finset.univ.sum f
            exact e.sum_comp f
  have hpartition : Finset.univ.sum joint = mu.probability condition := by
    exact v13M4Concrete_jointGaugeProbability_assignment_sum J condition
  have hcard : Fintype.card (V13M4ConcreteGaugeAssignment J) = 2 ^ J.card := by
    simp [V13M4ConcreteGaugeAssignment]
  have hjoint_mul :
      ((2 : Nat) ^ J.card : Real) * joint gamma = mu.probability condition := by
    rw [← hpartition]
    simp_rw [hjoint_equal]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    norm_num
  have hden_positive : 0 < mu.probability condition := by
    exact hcondition
  have hpow_positive : 0 < ((2 : Nat) ^ J.card : Real) := by positivity
  have hjoint_positive : 0 < joint gamma := by
    nlinarith
  change joint gamma / mu.probability condition = 1 / (2 : Real) ^ J.card
  rw [← hjoint_mul]
  norm_num
  field_simp

/-! ## Legal-prefix invariance -/

theorem v13M4ConcretePrefixConsistent_gaugeAction_iff {m t : Nat}
    (pref : V13M4ConcretePrefix m) (omega : V13M4ConcreteWorld m t)
    (s : V13M4ConcreteGaugeVector m)
    (hs : forall v b, pref.gaugeObservation v = some b -> s v = false) :
    v13M4ConcretePrefixConsistent pref
        (v13M4ConcreteWorldGaugeAction s omega) <->
      v13M4ConcretePrefixConsistent pref omega := by
  constructor
  · rintro ⟨hgauge, hquotient, hbuffer⟩
    refine ⟨?_, hquotient, hbuffer⟩
    intro v b hobserved
    have hvalue := hgauge v b hobserved
    change xor (omega.g v) (s v) = b at hvalue
    rw [hs v b hobserved] at hvalue
    simpa using hvalue
  · rintro ⟨hgauge, hquotient, hbuffer⟩
    refine ⟨?_, hquotient, hbuffer⟩
    intro v b hobserved
    change xor (omega.g v) (s v) = b
    rw [hs v b hobserved]
    simpa using hgauge v b hobserved

/-- The reconciled legal prefix is invariant under every gauge translation
whose support lies in a finite set disjoint from the prefix's exact charged
support. Public syntax is already fixed by Y; quotient and safe-buffer
outcomes are invariant because the concrete gauge action changes only g. -/
theorem v13M4Concrete_publicPrefixCondition_toggle_iff {m t : Nat}
    (Y : V13M4ConcretePublic m t) (pref : V13M4ConcretePrefix m)
    (hlegal : v13M4ConcreteLegalPrefix pref)
    (J : Finset (V13M4ConcreteGaugeIndex m))
    (hunsupported : forall v, v ∈ J ->
      v ∉ v13M4ConcreteGaugeSupport pref)
    (gamma delta : V13M4ConcreteGaugeAssignment J)
    (omega : V13M4ConcreteWorld m t) :
    @V13M4ConcreteE.publicPrefixCondition () m t Y pref
        (v13M4ConcreteWorldGaugeAction
          (v13M4ConcreteGaugeAssignmentToggle J gamma delta) omega) <->
      @V13M4ConcreteE.publicPrefixCondition () m t Y pref omega := by
  have hs : forall v b, pref.gaugeObservation v = some b ->
      v13M4ConcreteGaugeAssignmentToggle J gamma delta v = false := by
    intro v b hobserved
    by_cases hvJ : v ∈ J
    · have hvObserved :
          v ∈ v13M4ConcreteObservedSupport pref.gaugeObservation := by
        simp [hobserved]
      have hvCharged : v ∈ v13M4ConcreteGaugeSupport pref := by
        rw [v13M4ConcreteGaugeSupport, hlegal.2]
        exact Finset.mem_union_left _ hvObserved
      exact (hunsupported v hvJ hvCharged).elim
    · simp [v13M4ConcreteGaugeAssignmentToggle, hvJ]
  constructor
  · rintro ⟨hpublic, hpref⟩
    refine ⟨hpublic, ?_⟩
    exact (v13M4ConcretePrefixConsistent_gaugeAction_iff
      pref omega _ hs).mp hpref
  · rintro ⟨hpublic, hpref⟩
    refine ⟨hpublic, ?_⟩
    exact (v13M4ConcretePrefixConsistent_gaugeAction_iff
      pref omega _ hs).mpr hpref

/-! ## Faithful product and uniform-lift records -/

/-- The exact p.34 adaptive hidden-gauge product package on the concrete
regioned scaffold. It quantifies over every size, clock, public instance,
legal prefix with positive conditioning mass, finite unsupported J, and
assignment gamma, exactly as V13HiddenGaugeProductFrontier requires. -/
noncomputable def v13M4ConcreteHiddenGaugeProduct :
    V13HiddenGaugeProductFrontier V13M4ConcreteE where
  product_uniform := by
    intro theta m t Y pref hlegal hdefined J gamma hunsupported
    cases theta
    change V13M4ConcreteE.conditionalProbabilityAt () m t
        (v13M4ConcreteGaugeEvent J gamma)
        (V13M4ConcreteE.publicPrefixCondition Y pref) =
      1 / (2 : Real) ^ J.card
    exact v13M4Concrete_conditionalGaugeProduct_of_invariant
      J (V13M4ConcreteE.publicPrefixCondition Y pref) hdefined
      (fun gamma delta omega =>
        v13M4Concrete_publicPrefixCondition_toggle_iff
          Y pref hlegal J hunsupported gamma delta omega)
      gamma

/-- The static quotient-conditioned product law is the same orbit count with
the fixed-z condition. Together with the already proved quotient equations,
this closes both fields of the faithful uniform gauge-lift record. -/
noncomputable def v13M4ConcreteUniformGaugeLift :
    V13M4UniformGaugeLift V13M4ConcreteE V13M4ConcreteG V13M4ConcreteC where
  quotient_equations_on_support :=
    v13M4Concrete_quotient_equations_on_support
  uniform_subvector_conditioned_on_quotient := by
    intro theta m t z J gamma hdefined
    cases theta
    change V13M4ConcreteE.conditionalProbabilityAt () m t
        (v13M4ConcreteGaugeEvent J gamma)
        (fun omega : V13M4ConcreteWorld m t => omega.z = z) =
      1 / (2 : Real) ^ J.card
    exact v13M4Concrete_conditionalGaugeProduct_of_invariant
      J (fun omega : V13M4ConcreteWorld m t => omega.z = z) hdefined
      (fun _ _ _ => Iff.rfl) gamma

/-- Manuscript-facing gauge interface on the concrete scaffold: the existing
positive-rank free action plus the now-proved adaptive product law. -/
noncomputable def v13M4ConcreteFaithfulGaugeInterface :
    V13FaithfulGaugeInterface V13M4ConcreteE
      (fun _ m _ => V13M4ConcreteGaugeVector m) where
  action := v13M4ConcreteGaugeAction
  manuscriptFacing := v13M4ConcreteGaugeAction_manuscriptFacing
  hiddenGaugeProduct := v13M4ConcreteHiddenGaugeProduct

#print axioms v13M4Concrete_conditionalGaugeProduct_of_invariant
#print axioms v13M4Concrete_publicPrefixCondition_toggle_iff
#print axioms v13M4ConcreteHiddenGaugeProduct
#print axioms v13M4ConcreteUniformGaugeLift
#print axioms v13M4ConcreteFaithfulGaugeInterface

end Mettapedia.Computability.PNP

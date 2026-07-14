import Mettapedia.Computability.PNP.PNPv13FaithfulM4Spec

/-!
# PNP v13: neutral public syntax versus opposite-phase couplings

Appendix D.31 says that every primitive obtained solely from public template
syntax normalizes to neutral evidence.  A tempting strengthening of D.47(ii)
would ask the opposite-target coupling to match the *complete* neutral
skeleton almost surely.  That strengthening is not what the manuscript says:
D.47(ii) says "whenever possible", while Proposition D.50 only concerns
relations whose pairs already agree on the public instance.

If complete primitive valuations determine the public instance and the target
is rigid over a public instance, the global strengthening is impossible: an
almost-sure matched pair has equal targets, while the two marginals force its
targets to be false and true.  This module proves that boundary and thereby
guards the faithful D.48 record against silently restoring the stronger field.

The theorem below isolates the exact escape sockets.  A construction cannot
combine D.8 target rigidity with the global matching strengthening when its
complete public syntax is all neutral and determines its public object.  The
faithful D.50 same-public-relation condition remains compatible.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

universe u v

namespace V13FiniteLaw

variable {Omega : Type u} [Fintype Omega]

/-- A zero-mass atom has zero conditional singleton probability under every
conditioning event, including an undefined zero-mass condition. -/
theorem conditionalProbability_singleton_eq_zero_of_mass_eq_zero
    (mu : V13FiniteLaw Omega) (condition : Omega -> Prop) (omega : Omega)
    (hzero : mu.mass omega = 0) :
    mu.conditionalProbability (fun omega' => omega' = omega) condition = 0 := by
  classical
  have hnumerator :
      mu.probability (fun omega' => omega' = omega ∧ condition omega') = 0 := by
    rw [probability]
    apply Finset.sum_eq_zero
    intro omega' hmem
    have heq : omega' = omega := by
      have hcondition : omega' = omega ∧ condition omega' := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      exact hcondition.1
    subst omega'
    exact hzero
  rw [conditionalProbability, hnumerator]
  simp

end V13FiniteLaw

namespace V13FiniteCoupling

variable {Omega : Type u} [Fintype Omega]

/-- An event and its complement partition the total coupling mass. -/
theorem probability_add_probability_not
    (Gamma : V13FiniteCoupling Omega) (event : Omega -> Omega -> Prop) :
    Gamma.probability event +
        Gamma.probability (fun omega0 omega1 => ¬ event omega0 omega1) = 1 := by
  classical
  simp only [probability, ← Finset.sum_add_distrib]
  calc
    (Finset.univ.sum fun omega0 =>
        (Finset.univ.filter fun omega1 => event omega0 omega1).sum
            (Gamma.mass omega0) +
          (Finset.univ.filter fun omega1 => ¬ event omega0 omega1).sum
            (Gamma.mass omega0)) =
        Finset.univ.sum (fun omega0 =>
          Finset.univ.sum (Gamma.mass omega0)) := by
      apply Finset.sum_congr rfl
      intro omega0 _
      exact Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun omega1 => event omega0 omega1) (Gamma.mass omega0)
    _ = 1 := Gamma.mass_sum_one

/-- Every event probability dominates each mass atom belonging to it. -/
theorem mass_le_probability_of_event
    (Gamma : V13FiniteCoupling Omega) {event : Omega -> Omega -> Prop}
    {omega0 omega1 : Omega} (hevent : event omega0 omega1) :
    Gamma.mass omega0 omega1 <= Gamma.probability event := by
  classical
  rw [probability]
  calc
    Gamma.mass omega0 omega1 <=
        (Finset.univ.filter fun omega1' => event omega0 omega1').sum
          (Gamma.mass omega0) := by
      apply Finset.single_le_sum
      · intro b _
        exact Gamma.mass_nonnegative omega0 b
      · simp [hevent]
    _ <= Finset.univ.sum (fun omega0' =>
        (Finset.univ.filter fun omega1' => event omega0' omega1').sum
          (Gamma.mass omega0')) := by
      have hnonnegative : forall a,
          a ∈ (Finset.univ : Finset Omega) ->
            0 <= (Finset.univ.filter fun b => event a b).sum
              (Gamma.mass a) := by
        intro a _
        apply Finset.sum_nonneg
        intro b _
        exact Gamma.mass_nonnegative a b
      have hmem : omega0 ∈ (Finset.univ : Finset Omega) := Finset.mem_univ _
      exact Finset.single_le_sum hnonnegative hmem

/-- A probability-one event contains every positive coupling-mass atom. -/
theorem event_of_probability_one_of_mass_pos
    (Gamma : V13FiniteCoupling Omega) {event : Omega -> Omega -> Prop}
    (hone : Gamma.probability event = 1)
    {omega0 omega1 : Omega} (hmass : 0 < Gamma.mass omega0 omega1) :
    event omega0 omega1 := by
  by_contra hnot
  have hle := Gamma.mass_le_probability_of_event
    (event := fun a b => ¬ event a b) hnot
  have hpartition := Gamma.probability_add_probability_not event
  have hcomplement :
      Gamma.probability (fun a b => ¬ event a b) = 0 := by
    linarith
  rw [hcomplement] at hle
  linarith

/-- A probability coupling has at least one positive-mass atom. -/
theorem exists_mass_pos (Gamma : V13FiniteCoupling Omega) :
    exists omega0 omega1, 0 < Gamma.mass omega0 omega1 := by
  classical
  by_contra hnot
  simp only [not_exists, not_lt] at hnot
  have hzero : forall omega0 omega1, Gamma.mass omega0 omega1 = 0 := by
    intro omega0 omega1
    exact le_antisymm (hnot omega0 omega1)
      (Gamma.mass_nonnegative omega0 omega1)
  have hsum := Gamma.mass_sum_one
  simp [hzero] at hsum

/-- A probability-one event transfers to any pointwise larger event. -/
theorem probability_eq_one_of_probability_one_of_imp
    (Gamma : V13FiniteCoupling Omega)
    {event₁ event₂ : Omega -> Omega -> Prop}
    (hone : Gamma.probability event₁ = 1)
    (himp : forall omega0 omega1,
      event₁ omega0 omega1 -> event₂ omega0 omega1) :
    Gamma.probability event₂ = 1 := by
  classical
  have hcomplement :
      Gamma.probability (fun omega0 omega1 => ¬ event₂ omega0 omega1) = 0 := by
    rw [probability]
    apply Finset.sum_eq_zero
    intro omega0 _
    apply Finset.sum_eq_zero
    intro omega1 hmem
    have hnot₂ : ¬ event₂ omega0 omega1 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    by_contra hmass_ne
    have hmass_pos : 0 < Gamma.mass omega0 omega1 :=
      lt_of_le_of_ne (Gamma.mass_nonnegative omega0 omega1)
        (Ne.symm hmass_ne)
    have hevent₁ := Gamma.event_of_probability_one_of_mass_pos hone hmass_pos
    exact hnot₂ (himp omega0 omega1 hevent₁)
  have hpartition := Gamma.probability_add_probability_not event₂
  rw [hcomplement] at hpartition
  linarith

/-- Exact opposite-phase marginals force the two target bits to differ with
coupling probability one. -/
theorem target_mismatch_probability_one_of_opposite_phase_marginals
    (Gamma : V13FiniteCoupling Omega) (target : Omega -> Bool)
    (hleftTrue : Gamma.leftProbability (fun omega => target omega = true) = 0)
    (hrightFalse : Gamma.rightProbability (fun omega => target omega = false) = 0) :
    Gamma.probability (fun omega0 omega1 =>
      target omega0 ≠ target omega1) = 1 := by
  classical
  have hequal_zero :
      Gamma.probability (fun omega0 omega1 =>
        target omega0 = target omega1) = 0 := by
    rw [probability]
    apply Finset.sum_eq_zero
    intro omega0 _
    apply Finset.sum_eq_zero
    intro omega1 hmem
    have hequal : target omega0 = target omega1 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    cases htarget0 : target omega0 with
    | false =>
        have htarget1 : target omega1 = false := by
          rw [← hequal]
          exact htarget0
        have hle := Gamma.mass_le_probability_of_event
          (event := fun _ b => target b = false)
          (omega0 := omega0) htarget1
        change Gamma.mass omega0 omega1 <=
          Gamma.rightProbability (fun b => target b = false) at hle
        rw [hrightFalse] at hle
        exact le_antisymm hle (Gamma.mass_nonnegative omega0 omega1)
    | true =>
        have hle := Gamma.mass_le_probability_of_event
          (event := fun a _ => target a = true)
          (omega1 := omega1) htarget0
        change Gamma.mass omega0 omega1 <=
          Gamma.leftProbability (fun a => target a = true) at hle
        rw [hleftTrue] at hle
        exact le_antisymm hle (Gamma.mass_nonnegative omega0 omega1)
  have hpartition := Gamma.probability_add_probability_not
    (fun omega0 omega1 => target omega0 ≠ target omega1)
  simpa [hequal_zero] using hpartition

/-- No coupling can both match a target-rigid relation almost surely and have
left-false/right-true phase marginals. -/
theorem no_rigid_match_with_opposite_phase_marginals
    (Gamma : V13FiniteCoupling Omega) (target : Omega -> Bool)
    (matched : Omega -> Omega -> Prop)
    (hmatched : Gamma.probability matched = 1)
    (hrigid : forall omega0 omega1,
      matched omega0 omega1 -> target omega0 = target omega1)
    (hleftTrue : Gamma.leftProbability (fun omega => target omega = true) = 0)
    (hrightFalse : Gamma.rightProbability (fun omega => target omega = false) = 0) :
    False := by
  rcases Gamma.exists_mass_pos with ⟨omega0, omega1, hmass⟩
  have hpair := Gamma.event_of_probability_one_of_mass_pos hmatched hmass
  have hleft : target omega0 = false := by
    cases h : target omega0 with
    | false => rfl
    | true =>
        have hle := Gamma.mass_le_probability_of_event
          (event := fun a _ => target a = true)
          (omega1 := omega1) h
        change Gamma.mass omega0 omega1 <=
          Gamma.leftProbability (fun a => target a = true) at hle
        rw [hleftTrue] at hle
        linarith
  have hright : target omega1 = true := by
    cases h : target omega1 with
    | false =>
        have hle := Gamma.mass_le_probability_of_event
          (event := fun _ b => target b = false)
          (omega0 := omega0) h
        change Gamma.mass omega0 omega1 <=
          Gamma.rightProbability (fun b => target b = false) at hle
        rw [hrightFalse] at hle
        linarith
    | true => rfl
  have heq := hrigid omega0 omega1 hpair
  rw [hleft, hright] at heq
  contradiction

end V13FiniteCoupling

namespace V13D48CompatibleCouplings

/-- Every positive coupling atom has a positive-mass left endpoint in the
original ensemble law.  This follows from the exact conditional marginal, not
from an extra support hypothesis. -/
theorem left_law_mass_pos_of_coupling_mass_pos
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    {theta : E.Parameter} {m t : Nat} (j : E.TargetCoord theta m t)
    {omega0 omega1 : E.World theta m t}
    (hmass : 0 < @V13FiniteCoupling.mass (E.World theta m t)
      (E.worldFintype theta m t) (D48.coupling theta m t j)
      omega0 omega1) :
    0 < @V13FiniteLaw.mass (E.World theta m t)
      (E.worldFintype theta m t) (E.law theta m t) omega0 := by
  letI := E.worldFintype theta m t
  let Gamma := D48.coupling theta m t j
  have hle := Gamma.mass_le_probability_of_event
    (event := fun a _ => a = omega0) (omega1 := omega1) rfl
  change Gamma.mass omega0 omega1 <=
    Gamma.leftProbability (fun a => a = omega0) at hle
  rw [D48.left_phase_marginal theta m t j
    (fun a => a = omega0)] at hle
  change Gamma.mass omega0 omega1 <=
    (E.law theta m t).conditionalProbability
      (fun a => a = omega0)
      (fun omega => E.targetBit omega j = false) at hle
  by_contra hnot
  have hlaw_zero : (E.law theta m t).mass omega0 = 0 := by
    exact le_antisymm (not_lt.mp hnot)
      ((E.law theta m t).mass_nonnegative omega0)
  rw [V13FiniteLaw.conditionalProbability_singleton_eq_zero_of_mass_eq_zero
    (E.law theta m t)
    (fun omega => E.targetBit omega j = false) omega0 hlaw_zero] at hle
  linarith

/-- Every positive coupling atom has a positive-mass right endpoint in the
original ensemble law. -/
theorem right_law_mass_pos_of_coupling_mass_pos
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    {theta : E.Parameter} {m t : Nat} (j : E.TargetCoord theta m t)
    {omega0 omega1 : E.World theta m t}
    (hmass : 0 < @V13FiniteCoupling.mass (E.World theta m t)
      (E.worldFintype theta m t) (D48.coupling theta m t j)
      omega0 omega1) :
    0 < @V13FiniteLaw.mass (E.World theta m t)
      (E.worldFintype theta m t) (E.law theta m t) omega1 := by
  letI := E.worldFintype theta m t
  let Gamma := D48.coupling theta m t j
  have hle := Gamma.mass_le_probability_of_event
    (event := fun _ b => b = omega1) (omega0 := omega0) rfl
  change Gamma.mass omega0 omega1 <=
    Gamma.rightProbability (fun b => b = omega1) at hle
  rw [D48.right_phase_marginal theta m t j
    (fun b => b = omega1)] at hle
  change Gamma.mass omega0 omega1 <=
    (E.law theta m t).conditionalProbability
      (fun b => b = omega1)
      (fun omega => E.targetBit omega j = true) at hle
  by_contra hnot
  have hlaw_zero : (E.law theta m t).mass omega1 = 0 := by
    exact le_antisymm (not_lt.mp hnot)
      ((E.law theta m t).mass_nonnegative omega1)
  rw [V13FiniteLaw.conditionalProbability_singleton_eq_zero_of_mass_eq_zero
    (E.law theta m t)
    (fun omega => E.targetBit omega j = true) omega1 hlaw_zero] at hle
  linarith

end V13D48CompatibleCouplings

/-- D.8 gives target-bit rigidity on every supported public fiber once the
verifier is the Appendix-D component conjunction and the target/message
coordinate wire is present. -/
theorem V13M4OpenConstructionObligations.targetBit_rigid_on_supported_publicFiber
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v}
    (O : V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    {theta : E.Parameter} {m t : Nat} (j : E.TargetCoord theta m t)
    (omega0 omega1 : E.World theta m t)
    (hsupported0 : E.supported omega0) (hsupported1 : E.supported omega1)
    (hpublic : E.publicInput omega0 = E.publicInput omega1) :
    E.targetBit omega0 j = E.targetBit omega1 j := by
  have hverifier0 := O.sampler_sound theta m t omega0 hsupported0
  have hverifier1 := O.sampler_sound theta m t omega1 hsupported1
  have hcomponents0 :=
    (O.witness_relation_is_component_conjunction theta m t
      (E.publicInput omega0) (E.witnessOfWorld omega0)).mp hverifier0
  have hcomponents1 :=
    (O.witness_relation_is_component_conjunction theta m t
      (E.publicInput omega1) (E.witnessOfWorld omega1)).mp hverifier1
  have hmessage :
      E.message (E.witnessOfWorld omega0) =
        E.message (E.witnessOfWorld omega1) := by
    apply O.D8_lockedMessageRigidity.locked_message_rigidity
      theta m t (E.publicInput omega0)
      (C.zCoord (E.witnessOfWorld omega0))
      (C.zCoord (E.witnessOfWorld omega1))
      (C.lockAux (E.witnessOfWorld omega0))
      (C.lockAux (E.witnessOfWorld omega1))
    · exact ⟨omega0, hsupported0, rfl⟩
    · exact hcomponents0.1
    · exact hcomponents0.2.1
    · simpa [hpublic] using hcomponents1.1
    · simpa [hpublic] using hcomponents1.2.1
  rw [C.targetBit_reads_witness_message omega0 j,
    C.targetBit_reads_witness_message omega1 j, hmessage]

/-- D.8 target rigidity applies to every positive D.48 coupling atom: exact
marginals place both endpoints in positive sampler support. -/
theorem V13M4OpenConstructionObligations.targetBit_rigid_on_couplingSupport
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v}
    (O : V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    {theta : E.Parameter} {m t : Nat} (j : E.TargetCoord theta m t)
    (omega0 omega1 : E.World theta m t)
    (hmass : 0 < @V13FiniteCoupling.mass (E.World theta m t)
      (E.worldFintype theta m t)
      (O.D48_compatibleCouplings.coupling theta m t j) omega0 omega1)
    (hpublic : E.publicInput omega0 = E.publicInput omega1) :
    E.targetBit omega0 j = E.targetBit omega1 j := by
  apply O.targetBit_rigid_on_supported_publicFiber j omega0 omega1
  · exact (O.sampler_support_is_positive_mass theta m t omega0).mpr
      (O.D48_compatibleCouplings.left_law_mass_pos_of_coupling_mass_pos j hmass)
  · exact (O.sampler_support_is_positive_mass theta m t omega1).mpr
      (O.D48_compatibleCouplings.right_law_mass_pos_of_coupling_mass_pos j hmass)
  · exact hpublic

/-- The deliberately rejected global-neutral-matching strengthening of
D.47(ii).  This is not a field of the faithful D.48 record. -/
def V13D48GlobalNeutralSkeletonMatching
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t) : Prop :=
  let Gamma := D48.coupling theta m t j
  @V13FiniteCoupling.probability (E.World theta m t)
    (E.worldFintype theta m t) Gamma
    (fun omega0 omega1 =>
      forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
        E.declaredNeutralPrimitive primitive ->
        E.primitiveValue primitive omega0 =
          E.primitiveValue primitive omega1) = 1

/-- Exact obstruction to strengthening D.47(ii) to global matching.  If every
visible primitive is D.31-neutral, equality of the complete primitive
valuation determines the public instance, and a target is rigid on public
fibers, then the global matching property contradicts the opposite-phase
marginals.  This does not refute the manuscript's guarded D.50 statement. -/
theorem v13D48GlobalNeutralSkeletonMatching_false_of_publicTargetRigidity
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t)
    (allPublicSyntaxNeutral :
      forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.declaredNeutralPrimitive primitive)
    (publicInput_ext : forall omega0 omega1 : E.World theta m t,
      (forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.primitiveValue primitive omega0 =
            E.primitiveValue primitive omega1) ->
      E.publicInput omega0 = E.publicInput omega1)
    (targetRigidOnPublicFiber : forall omega0 omega1 : E.World theta m t,
      E.publicInput omega0 = E.publicInput omega1 ->
        E.targetBit omega0 j = E.targetBit omega1 j)
    (hglobal : V13D48GlobalNeutralSkeletonMatching D48 theta m t j) :
    False := by
  letI := E.worldFintype theta m t
  let Gamma := D48.coupling theta m t j
  let target := fun omega : E.World theta m t => E.targetBit omega j
  let matched := fun omega0 omega1 : E.World theta m t =>
    forall primitive : E.PublicPrimitive theta m t,
      primitive ∈ E.fullPublicSyntax theta m t ->
      E.declaredNeutralPrimitive primitive ->
        E.primitiveValue primitive omega0 = E.primitiveValue primitive omega1
  have hmatched : Gamma.probability matched = 1 := by
    exact hglobal
  have hrigid : forall omega0 omega1,
      matched omega0 omega1 -> target omega0 = target omega1 := by
    intro omega0 omega1 hmatch
    apply targetRigidOnPublicFiber
    apply publicInput_ext
    intro primitive hprimitive
    exact hmatch primitive hprimitive
      (allPublicSyntaxNeutral primitive hprimitive)
  have hleftTrue :
      Gamma.leftProbability (fun omega => target omega = true) = 0 := by
    have h := D48.left_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = true)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hrightFalse :
      Gamma.rightProbability (fun omega => target omega = false) = 0 := by
    have h := D48.right_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = false)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  exact Gamma.no_rigid_match_with_opposite_phase_marginals target matched
    hmatched hrigid hleftTrue hrightFalse

/-- Strong form of the D.8/D.31/D.48 boundary.  Under exact opposite-phase
marginals, public-fiber target rigidity, and a complete all-neutral valuation
that determines the public instance, the complete neutral valuation differs
with coupling probability exactly one.  Thus Proposition D.50's zero
derivative on *same-public* relations cannot be promoted to global neutral
cancellation on the Phase-A coupling. -/
theorem v13D48_completeNeutralSyntax_mismatch_probability_one_of_publicTargetRigidity
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    (D48 : V13D48CompatibleCouplings E G C)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t)
    (allPublicSyntaxNeutral :
      forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.declaredNeutralPrimitive primitive)
    (publicInput_ext : forall omega0 omega1 : E.World theta m t,
      (forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.primitiveValue primitive omega0 =
            E.primitiveValue primitive omega1) ->
      E.publicInput omega0 = E.publicInput omega1)
    (targetRigidOnPublicFiber : forall omega0 omega1 : E.World theta m t,
      E.publicInput omega0 = E.publicInput omega1 ->
        E.targetBit omega0 j = E.targetBit omega1 j) :
    let Gamma := D48.coupling theta m t j
    @V13FiniteCoupling.probability (E.World theta m t)
      (E.worldFintype theta m t) Gamma
      (fun omega0 omega1 =>
        ¬ forall primitive : E.PublicPrimitive theta m t,
          primitive ∈ E.fullPublicSyntax theta m t ->
          E.declaredNeutralPrimitive primitive ->
            E.primitiveValue primitive omega0 =
              E.primitiveValue primitive omega1) = 1 := by
  letI := E.worldFintype theta m t
  let Gamma := D48.coupling theta m t j
  let target := fun omega : E.World theta m t => E.targetBit omega j
  have hleftTrue :
      Gamma.leftProbability (fun omega => target omega = true) = 0 := by
    have h := D48.left_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = true)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hrightFalse :
      Gamma.rightProbability (fun omega => target omega = false) = 0 := by
    have h := D48.right_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = false)
    simpa [Gamma, target, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have htarget : Gamma.probability (fun omega0 omega1 =>
      target omega0 ≠ target omega1) = 1 :=
    Gamma.target_mismatch_probability_one_of_opposite_phase_marginals
      target hleftTrue hrightFalse
  apply Gamma.probability_eq_one_of_probability_one_of_imp htarget
  intro omega0 omega1 htarget_ne hmatch
  apply htarget_ne
  apply targetRigidOnPublicFiber
  apply publicInput_ext
  intro primitive hprimitive
  exact hmatch primitive hprimitive
    (allPublicSyntaxNeutral primitive hprimitive)

/-- The open construction rejects global complete-neutral matching.  On the
finite support world type of D.39, D.8 and opposite-phase marginals contradict
that strengthening when the all-neutral public valuation determines the
public instance.  The faithful D.50 guarded field is not rejected. -/
theorem v13OpenConstruction_rejects_D48GlobalNeutralSkeletonMatching
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v}
    (O : V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t)
    (worldTypeIsSamplerSupport : forall omega : E.World theta m t,
      E.supported omega)
    (allPublicSyntaxNeutral :
      forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.declaredNeutralPrimitive primitive)
    (publicInput_ext : forall omega0 omega1 : E.World theta m t,
      (forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.primitiveValue primitive omega0 =
            E.primitiveValue primitive omega1) ->
      E.publicInput omega0 = E.publicInput omega1)
    (hglobal : V13D48GlobalNeutralSkeletonMatching
      O.D48_compatibleCouplings theta m t j) :
    False := by
  apply v13D48GlobalNeutralSkeletonMatching_false_of_publicTargetRigidity
    O.D48_compatibleCouplings theta m t j allPublicSyntaxNeutral publicInput_ext
  · intro omega0 omega1 hpublic
    exact O.targetBit_rigid_on_supported_publicFiber j omega0 omega1
      (worldTypeIsSamplerSupport omega0) (worldTypeIsSamplerSupport omega1) hpublic
  · exact hglobal

/-- Route-level incompatibility between D.8, D.31, D.48's exact opposite-phase
marginals, and Definition 7.4.  If the complete public primitive valuation
determines the public instance and every public primitive is D.31-neutral,
Definition 7.4 makes every positive coupling atom have equal public inputs.
D.8 then makes its target bits equal, contradicting the opposite-phase
marginals.

This theorem uses no analytic frontier.  A faithful route can escape only by
rejecting at least one displayed premise: incomplete public observability,
all-public D.31 neutrality, D.8 public-fiber rigidity, exact opposite-phase
marginals, or Definition 7.4 support-wide neutral coherence. -/
theorem v13OpenConstruction_incompatible_with_definition7_completePublicNeutrality
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v}
    (O : V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    (neutralCoherence : V13Definition7NeutralPairCoherence
      E G C O.D48_compatibleCouplings)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t)
    (allPublicSyntaxNeutral :
      forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.declaredNeutralPrimitive primitive)
    (publicInput_ext : forall omega0 omega1 : E.World theta m t,
      (forall primitive : E.PublicPrimitive theta m t,
        primitive ∈ E.fullPublicSyntax theta m t ->
          E.primitiveValue primitive omega0 =
            E.primitiveValue primitive omega1) ->
      E.publicInput omega0 = E.publicInput omega1) :
    False := by
  letI := E.worldFintype theta m t
  let Gamma := O.D48_compatibleCouplings.coupling theta m t j
  rcases Gamma.exists_mass_pos with ⟨omega0, omega1, hmass⟩
  have hpublic : E.publicInput omega0 = E.publicInput omega1 := by
    apply publicInput_ext
    intro primitive hprimitive
    exact neutralCoherence.pair_neutral_on_coupling_support
      theta m t j primitive hprimitive
      (allPublicSyntaxNeutral primitive hprimitive) omega0 omega1 hmass
  have htarget_eq := O.targetBit_rigid_on_couplingSupport
    j omega0 omega1 hmass hpublic
  have hleftTrue :
      Gamma.leftProbability (fun omega => E.targetBit omega j = true) = 0 := by
    have h := O.D48_compatibleCouplings.left_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = true)
    simpa [Gamma, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hrightFalse :
      Gamma.rightProbability (fun omega => E.targetBit omega j = false) = 0 := by
    have h := O.D48_compatibleCouplings.right_phase_marginal theta m t j
      (fun omega => E.targetBit omega j = false)
    simpa [Gamma, V13QuantitativeEnsemble.conditionalProbabilityAt,
      V13FiniteLaw.conditionalProbability, V13FiniteLaw.probability] using h
  have hmismatch_one :=
    Gamma.target_mismatch_probability_one_of_opposite_phase_marginals
      (fun omega => E.targetBit omega j) hleftTrue hrightFalse
  have hmismatch := Gamma.event_of_probability_one_of_mass_pos
    hmismatch_one hmass
  exact hmismatch htarget_eq

/-- Record-level no-go theorem for the exact manuscript combination.  A
construction with D.8 and D.48 cannot simultaneously have an extensionally
complete public catalog, D.31 neutrality for that whole catalog, and
Definition 7.4 support-wide pair neutrality at any target coordinate.

The obstruction is already finite and mechanical; qSSM, incidence, mixing,
and Kpoly assumptions play no role. -/
theorem v13OpenConstruction_D31_definition7_fullPublicSyntax_noGo
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v}
    (O : V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar)
    (D31 : V13D31PublicSyntaxNeutrality E)
    (fullSyntax : V13FullPublicSyntaxObservability E)
    (neutralCoherence : V13Definition7NeutralPairCoherence
      E G C O.D48_compatibleCouplings)
    (theta : E.Parameter) (m t : Nat) (j : E.TargetCoord theta m t) :
    False := by
  exact v13OpenConstruction_incompatible_with_definition7_completePublicNeutrality
    O neutralCoherence theta m t j
    (D31.every_public_template_primitive_neutral theta m t)
    (fullSyntax.publicInput_ext theta m t)

/-- The complete faithful mechanical target is uninhabited.  Its nonempty
switched-target guard supplies a target at message scale one, while its exact
D.31, full-public observability, Definition 7.4, D.8, and D.48 fields trigger
the route-level no-go theorem above.

This is not a P != NP theorem.  It proves that the displayed v13 mechanical
interface cannot be the premise of a non-vacuous separation proof without
revising at least one of those manuscript requirements. -/
theorem v13M4OpenConstructionObligations_uninhabited
    {E : V13QuantitativeEnsemble} {G : V13M4LayeredGeometry E}
    {C : V13M4LocalComponents E G}
    {NormalizedPrimitive : E.Parameter -> Nat -> Nat -> Type u}
    {CNFVar : E.Parameter -> Nat -> Nat -> Type v} :
    ¬ Nonempty
      (V13M4OpenConstructionObligations E G C NormalizedPrimitive CNFVar) := by
  rintro ⟨O⟩
  rcases E.parameterNonempty with ⟨theta⟩
  rcases O.switched_targets_nonempty theta 0 1 (by decide) with ⟨j, _hj⟩
  exact v13OpenConstruction_D31_definition7_fullPublicSyntax_noGo
    O O.D31_publicSyntaxNeutrality O.fullPublicSyntaxObservability
    O.definition7_neutralPairCoherence theta 0 1 j

end Mettapedia.Computability.PNP

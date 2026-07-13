import Mettapedia.Computability.PNP.V13EvidenceSpine
import Mettapedia.Computability.PNP.V13FaithfulM4ExecutionTrace

/-!
# Faithful Phase A on the regioned scaffold

The scaffold world is reparameterized exactly as a phase bit paired with all
remaining sampler coordinates.  The phase bit is one chosen message
coordinate.  This gives a normalized coupling whose left and right marginals
are literally the uniform laws conditioned on the two message phases.

A one-step refinement keeps pairs with equal executed transcripts and charges
each separated pair by its coupling weight.  Its derivative identity is a
finite partition of the normalized coupling mass, not an assumed numerical
certificate.

The inhabited `V13FaithfulPhaseACaptureTarget` below uses an actual scaffold
request trace but the constant-false observer bit.  Its capture inequality is
therefore a genuine zero-gap theorem.  Capture for arbitrary polynomial-time
observer output, and identification of its trace with the manuscript trace,
remain outside this scaffold result; they are not smuggled into the coupling
or refinement definitions.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Exact phase reparameterization of scaffold worlds -/

structure V13M4ScaffoldPhaseBase (m t : Nat)
    (j : V13M4ConcreteMessageIndex t) where
  neutralToken : Bool
  z : V13M4ConcreteGaugeVector m
  g : V13M4ConcreteGaugeVector m
  bufferLeft : V13M4ConcreteGaugeVector m
  otherMessageBits : {i : V13M4ConcreteMessageIndex t // i ≠ j} -> Bool

@[ext] theorem V13M4ScaffoldPhaseBase.ext {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    {base base' : V13M4ScaffoldPhaseBase m t j}
    (htoken : base.neutralToken = base'.neutralToken)
    (hz : base.z = base'.z) (hg : base.g = base'.g)
    (hbuffer : base.bufferLeft = base'.bufferLeft)
    (hmessage : base.otherMessageBits = base'.otherMessageBits) :
    base = base' := by
  cases base
  cases base'
  simp_all

noncomputable instance (m t : Nat) (j : V13M4ConcreteMessageIndex t) :
    Fintype (V13M4ScaffoldPhaseBase m t j) := by
  let tupleEquiv : V13M4ScaffoldPhaseBase m t j ≃
      Bool × V13M4ConcreteGaugeVector m × V13M4ConcreteGaugeVector m ×
        V13M4ConcreteGaugeVector m ×
          ({i : V13M4ConcreteMessageIndex t // i ≠ j} -> Bool) :=
    { toFun := fun base =>
        (base.neutralToken, base.z, base.g, base.bufferLeft,
          base.otherMessageBits)
      invFun := fun data =>
        { neutralToken := data.1
          z := data.2.1
          g := data.2.2.1
          bufferLeft := data.2.2.2.1
          otherMessageBits := data.2.2.2.2 }
      left_inv := by intro base; cases base; rfl
      right_inv := by
        intro data
        rcases data with ⟨token, z, g, buffer, other⟩
        rfl }
  exact Fintype.ofEquiv _ tupleEquiv.symm

instance (m t : Nat) (j : V13M4ConcreteMessageIndex t) :
    Nonempty (V13M4ScaffoldPhaseBase m t j) :=
  ⟨{
    neutralToken := false
    z := fun _ => false
    g := fun _ => false
    bufferLeft := fun _ => false
    otherMessageBits := fun _ => false
  }⟩

noncomputable def v13M4ScaffoldWorldPhaseEquiv (m t : Nat)
    (j : V13M4ConcreteMessageIndex t) :
    V13M4ConcreteWorld m t ≃ Bool × V13M4ScaffoldPhaseBase m t j where
  toFun omega :=
    (omega.messageBits j,
      { neutralToken := omega.neutralToken
        z := omega.z
        g := omega.g
        bufferLeft := omega.bufferLeft
        otherMessageBits := fun i => omega.messageBits i.1 })
  invFun data :=
    { neutralToken := data.2.neutralToken
      z := data.2.z
      g := data.2.g
      bufferLeft := data.2.bufferLeft
      messageBits := fun i =>
        if h : i = j then data.1 else data.2.otherMessageBits ⟨i, h⟩ }
  left_inv := by
    intro omega
    apply V13M4ConcreteWorld.ext
    · rfl
    · rfl
    · rfl
    · rfl
    · funext i
      by_cases h : i = j
      · subst i
        simp
      · simp [h]
  right_inv := by
    intro data
    rcases data with ⟨phase, base⟩
    apply Prod.ext
    · simp
    · apply V13M4ScaffoldPhaseBase.ext <;> try rfl
      funext i
      simp [i.property]

abbrev V13M4ScaffoldPhaseOmega (m t : Nat)
    (j : V13M4ConcreteMessageIndex t) :=
  Bool × V13M4ScaffoldPhaseBase m t j

def v13M4ScaffoldPhaseBit {m t : Nat} {j : V13M4ConcreteMessageIndex t}
    (omega : V13M4ScaffoldPhaseOmega m t j) : Bool :=
  omega.1

noncomputable def v13M4ScaffoldPhaseWorld {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (omega : V13M4ScaffoldPhaseOmega m t j) : V13M4ConcreteWorld m t :=
  (v13M4ScaffoldWorldPhaseEquiv m t j).symm omega

theorem v13M4ScaffoldPhaseWorld_targetBit {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (omega : V13M4ScaffoldPhaseOmega m t j) :
    (v13M4ScaffoldPhaseWorld omega).messageBits j = omega.1 := by
  rcases omega with ⟨phase, base⟩
  simp [v13M4ScaffoldPhaseWorld, v13M4ScaffoldWorldPhaseEquiv]

/-! ## Uniform rational law and exact conditioned coupling -/

noncomputable def v13UniformFiniteRationalLaw
    (Omega : Type) [Fintype Omega] [Nonempty Omega] :
    FiniteRationalLaw Omega where
  weight _ := 1 / (Fintype.card Omega : Rat)
  nonnegative := by intro omega; positivity
  total_weight := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card Omega : Rat) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [nsmul_eq_mul, hcard]

noncomputable def v13M4ScaffoldPhaseLaw (m t : Nat)
    (j : V13M4ConcreteMessageIndex t) :
    FiniteRationalLaw (V13M4ScaffoldPhaseOmega m t j) :=
  v13UniformFiniteRationalLaw _

theorem v13M4ScaffoldPhaseLaw_conditional
    (m t : Nat) (j : V13M4ConcreteMessageIndex t)
    (phase : Bool)
    (event : V13M4ScaffoldPhaseOmega m t j -> Bool) :
    (v13M4ScaffoldPhaseLaw m t j).conditionalProb
        v13M4ScaffoldPhaseBit phase (fun omega => event omega = true) =
      Finset.univ.sum (fun base : V13M4ScaffoldPhaseBase m t j =>
        if event (phase, base) then
          1 / (Fintype.card (V13M4ScaffoldPhaseBase m t j) : Rat)
        else 0) := by
  classical
  let card : Rat := Fintype.card (V13M4ScaffoldPhaseBase m t j)
  have hcard : card ≠ 0 := by
    dsimp [card]
    exact_mod_cast Fintype.card_ne_zero
  have hnum :
      (v13M4ScaffoldPhaseLaw m t j).eventWeight
          (fun omega => v13M4ScaffoldPhaseBit omega = phase ∧
            event omega = true) =
        (Finset.univ.sum (fun base : V13M4ScaffoldPhaseBase m t j =>
          if event (phase, base) then 1 / card else 0)) / 2 := by
    rw [FiniteRationalLaw.eventWeight, Fintype.sum_prod_type]
    cases phase <;>
      simp [v13M4ScaffoldPhaseLaw, v13UniformFiniteRationalLaw,
        v13M4ScaffoldPhaseBit, Fintype.card_prod, card,
        Finset.sum_div] <;>
      apply Finset.sum_congr rfl <;>
      intro base _ <;>
      split <;> ring
  have hden :
      (v13M4ScaffoldPhaseLaw m t j).eventWeight
          (fun omega => v13M4ScaffoldPhaseBit omega = phase) = 1 / 2 := by
    rw [FiniteRationalLaw.eventWeight, Fintype.sum_prod_type]
    cases phase <;>
      simp [v13M4ScaffoldPhaseLaw, v13UniformFiniteRationalLaw,
        v13M4ScaffoldPhaseBit, Fintype.card_prod, card,
        Finset.sum_const, nsmul_eq_mul, hcard]
  rw [FiniteRationalLaw.conditionalProb, hnum, hden]
  change
    ((Finset.univ.sum (fun base : V13M4ScaffoldPhaseBase m t j =>
      if event (phase, base) then 1 / card else 0)) / 2) / (1 / 2) =
      Finset.univ.sum (fun base : V13M4ScaffoldPhaseBase m t j =>
        if event (phase, base) then 1 / card else 0)
  ring

noncomputable def v13M4ScaffoldPhaseCoupling (m t : Nat)
    (j : V13M4ConcreteMessageIndex t) :
    FaithfulStaticPairwiseCoupling (v13M4ScaffoldPhaseLaw m t j)
      v13M4ScaffoldPhaseBit (V13M4ScaffoldPhaseBase m t j) where
  pairWeight _ := 1 / (Fintype.card (V13M4ScaffoldPhaseBase m t j) : Rat)
  pairNonnegative := by intro base; positivity
  normalized := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card (V13M4ScaffoldPhaseBase m t j) : Rat) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [nsmul_eq_mul, hcard]
  left := fun base => (false, base)
  right := fun base => (true, base)
  opposite := by intro base; exact ⟨rfl, rfl⟩
  left_exact_phase_marginal := by
    classical
    intro event
    exact (v13M4ScaffoldPhaseLaw_conditional m t j false event).symm
  right_exact_phase_marginal := by
    classical
    intro event
    exact (v13M4ScaffoldPhaseLaw_conditional m t j true event).symm

/-! ## Executed transcripts and the one-step refinement -/

noncomputable def v13M4ScaffoldPhaseTranscript {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t))
    (omega : V13M4ScaffoldPhaseOmega m t j) :
    List (V13M4ScaffoldObservation m t) :=
  let trace : V13M4ScaffoldExecutionTrace m t :=
    { world := v13M4ScaffoldPhaseWorld omega
      initial := v13M4ScaffoldEmptyExecutionState m
      requests := requests }
  trace.occurrences.map V13M4ScaffoldPrimitiveOccurrence.observation

noncomputable def v13M4ScaffoldOneStepFinalWeight {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t)) : Rat :=
  let coupling := v13M4ScaffoldPhaseCoupling m t j
  let transcript := v13M4ScaffoldPhaseTranscript (j := j) requests
  Finset.univ.sum fun base =>
    if transcript (coupling.left base) = transcript (coupling.right base)
      then coupling.pairWeight base else 0

noncomputable def v13M4ScaffoldOneStepDerivative {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t))
    (base : V13M4ScaffoldPhaseBase m t j) : Rat :=
  let coupling := v13M4ScaffoldPhaseCoupling m t j
  let transcript := v13M4ScaffoldPhaseTranscript (j := j) requests
  if transcript (coupling.left base) = transcript (coupling.right base)
    then 0 else coupling.pairWeight base

theorem v13M4ScaffoldOneStep_partition {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t)) :
    1 - v13M4ScaffoldOneStepFinalWeight (j := j) requests =
      Finset.univ.sum (v13M4ScaffoldOneStepDerivative (j := j) requests) := by
  rw [← (v13M4ScaffoldPhaseCoupling m t j).normalized]
  simp only [v13M4ScaffoldOneStepFinalWeight,
    v13M4ScaffoldOneStepDerivative]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro base _
  by_cases hEq : v13M4ScaffoldPhaseTranscript (j := j) requests
      ((v13M4ScaffoldPhaseCoupling m t j).left base) =
    v13M4ScaffoldPhaseTranscript (j := j) requests
      ((v13M4ScaffoldPhaseCoupling m t j).right base)
  · simp [hEq]
  · simp [hEq]

noncomputable def v13M4ScaffoldOneStepTelescoping {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t)) :
    DerivativeTelescoping Unit (V13M4ScaffoldPhaseBase m t j) := by
  exact
    { stageFinite := inferInstance
      branchFinite := inferInstance
      finalWeight := v13M4ScaffoldOneStepFinalWeight (j := j) requests
      derivative := fun _ base =>
        v13M4ScaffoldOneStepDerivative (j := j) requests base
      derivativeNonnegative := by
        intro stage base
        simp only [v13M4ScaffoldOneStepDerivative]
        split
        · norm_num
        · exact (v13M4ScaffoldPhaseCoupling m t j).pairNonnegative base
      telescopes := by
        simpa using v13M4ScaffoldOneStep_partition (j := j) requests }

theorem v13M4ScaffoldOneStep_separation_eq_derivativeSum {m t : Nat}
    {j : V13M4ConcreteMessageIndex t}
    (requests : List (V13M4ScaffoldRequest m t)) :
    couplingSepMass (v13M4ScaffoldPhaseTranscript (j := j) requests)
        (v13M4ScaffoldPhaseCoupling m t j).pairWeight
        (v13M4ScaffoldPhaseCoupling m t j).left
        (v13M4ScaffoldPhaseCoupling m t j).right =
      (v13M4ScaffoldOneStepTelescoping (j := j) requests).derivativeSum := by
  simp [couplingSepMass, v13M4ScaffoldOneStepTelescoping,
    v13M4ScaffoldOneStepDerivative, DerivativeTelescoping.derivativeSum]
  rfl

/-- Faithful Phase-A target for a real scaffold execution and the constant
observer.  This closes structural marginals and refinement accounting without
claiming arbitrary-observer trace capture. -/
noncomputable def v13M4ScaffoldFaithfulPhaseA {m t : Nat}
    (j : V13M4ConcreteMessageIndex t)
    (requests : List (V13M4ScaffoldRequest m t)) :
    V13FaithfulPhaseACaptureTarget (v13M4ScaffoldPhaseLaw m t j)
      v13M4ScaffoldPhaseBit
      (v13M4ScaffoldPhaseTranscript (j := j) requests) (fun _ => false)
      (V13M4ScaffoldPhaseBase m t j) Unit
      (V13M4ScaffoldPhaseBase m t j) where
  coupling := v13M4ScaffoldPhaseCoupling m t j
  captures_actual_trace := by
    have hgap : Gap (v13M4ScaffoldPhaseLaw m t j)
        v13M4ScaffoldPhaseBit
        (v13M4ScaffoldPhaseTranscript (j := j) requests)
        (fun _ => false) = 0 := by
      simp [Gap, halfAbsDiff, FiniteRationalLaw.conditionalProb,
        FiniteRationalLaw.eventWeight]
    rw [hgap]
    apply mul_nonneg
    · norm_num
    · apply Finset.sum_nonneg
      intro base _
      split
      · norm_num
      · exact (v13M4ScaffoldPhaseCoupling m t j).pairNonnegative base
  telescoping := v13M4ScaffoldOneStepTelescoping (j := j) requests
  separation_le_derivative_sum := by
    rw [v13M4ScaffoldOneStep_separation_eq_derivativeSum]

end Mettapedia.Computability.PNP

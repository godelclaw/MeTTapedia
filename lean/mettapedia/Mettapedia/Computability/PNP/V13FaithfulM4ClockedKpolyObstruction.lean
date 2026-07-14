import Mettapedia.Computability.PNP.V13ClockedKpolySemantics
import Mettapedia.Computability.PNP.V13FaithfulM4Mechanical

/-!
# PNP v13: the scaffold's clocked-Kpoly obstruction

The regioned scaffold currently uses a placeholder quantitative observer
surface: its program type is `Unit` and its `clockedKpoly` observable is
identically zero.  This is harmless for the gauge and local-CSP lemmas, but it
makes the positive-rate global incompressibility statement of Theorem 10.9
mathematically impossible on this ensemble.

Consequently a locked core cannot be promoted to the final faithful object by
changing only the lock/readout predicates.  The final object must also replace
this placeholder by the manuscript's minimum clocked program length for
recovering `M(Y)` from `Y`.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

def v13M4ConcreteClockedKpolyZeroMessageWorld : V13M4ConcreteWorld 0 0 where
  neutralToken := false
  z := fun _ => false
  g := fun _ => false
  bufferLeft := fun _ => false
  messageBits := fun _ => false

def v13M4ConcreteClockedKpolyOneMessageWorld : V13M4ConcreteWorld 0 0 where
  neutralToken := false
  z := fun _ => false
  g := fun _ => false
  bufferLeft := fun _ => false
  messageBits := fun _ => true

/-- The zero/one witness pair has identical public syntax and different global
messages, while the scaffold assigns both raw clocked complexity zero. -/
theorem v13M4Concrete_not_clockedKpolySemantics :
    ¬ Nonempty (V13ClockedKpolySemantics V13M4ConcreteE) := by
  apply
    V13ClockedKpolySemantics.not_nonempty_of_samePublic_distinctMessage_clockedKpoly_zero
      (E := V13M4ConcreteE) (parameter := ()) (m := 0) (t := 0) 0
      v13M4ConcreteClockedKpolyZeroMessageWorld
      v13M4ConcreteClockedKpolyOneMessageWorld
  · rfl
  · simp [V13M4ConcreteE, v13M4ConcreteEnsemble,
      v13M4ConcreteMessage, v13M4ConcreteWitnessOfWorld,
      v13M4ConcreteClockedKpolyZeroMessageWorld,
      v13M4ConcreteClockedKpolyOneMessageWorld]
  · rfl
  · rfl

/-- The current scaffold cannot inhabit Theorem 10.9's positive-rate frontier,
because its `clockedKpoly` field is definitionally zero on every world. -/
theorem v13M4Concrete_not_globalMessageIncompressibility :
    ¬ Nonempty (V13GlobalMessageIncompressibilityFrontier V13M4ConcreteE) := by
  rintro ⟨lower⟩
  let D : Nat := 0
  let t : Nat := max (lower.threshold D) 1
  have ht : lower.threshold D <= t := Nat.le_max_left _ _
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  have heta : 0 < lower.eta D := lower.eta_positive D
  have hkappa : 0 < lower.kappa D := lower.kappa_positive D
  have htReal : (0 : Real) < t := by exact_mod_cast htpos
  have hrate : 0 < lower.eta D * (t : Real) := mul_pos heta htReal
  have hbound := lower.global_message_incompressibility D t ht
  have hevent :
      (fun omega : V13M4ConcreteE.World (lower.parameterAtClock D) t t =>
        (lower.eta D * t : Real) <= V13M4ConcreteE.clockedKpoly D omega) =
        (fun _ => False) := by
    funext omega
    apply propext
    apply iff_false_intro
    simpa [V13M4ConcreteE, v13M4ConcreteEnsemble] using
      (not_le_of_gt hrate)
  have hprobabilityZero :
      V13M4ConcreteE.probabilityAt (lower.parameterAtClock D) t t
        (fun _ => False) = 0 := by
    simp [V13QuantitativeEnsemble.probabilityAt, V13FiniteLaw.probability]
  change
    V13M4ConcreteE.probabilityAt (lower.parameterAtClock D) t t
        (fun omega =>
          (lower.eta D * t : Real) <= V13M4ConcreteE.clockedKpoly D omega) >=
      1 - Real.exp (-(lower.kappa D * t) * Real.log 2) at hbound
  rw [hevent, hprobabilityZero] at hbound
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexponent : -(lower.kappa D * (t : Real)) * Real.log 2 < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hkappa htReal)) hlog
  have hexp :
      Real.exp (-(lower.kappa D * (t : Real)) * Real.log 2) < 1 :=
    Real.exp_lt_one_iff.mpr hexponent
  linarith

end Mettapedia.Computability.PNP

import Mettapedia.GSLT.Weighting.ConfiguredFunding

/-!
# Weighted coefficients use the actual funding admission

The existing weighting gate is supplied by the exact price comparison. Its
admission is equivalent to a paid occurrence path retaining the original
event and input map. With nonzero key and geometric factors, a coefficient
is nonzero exactly when that history is fundable. Zero coefficients alone
are insufficient to diagnose resource exhaustion.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting.ConfiguredFunding

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

universe uTerm uSite uEvent uKey uCtx uR

variable {theory : GSLT.{uTerm}} {P : InteractionPresentation.{uSite, uEvent} theory}
  {K : Keyed.{uTerm, uSite, uEvent, uKey} P} {R : Type uR}
  (A : Augmented.{uTerm, uSite, uEvent, uKey, uCtx, uR} K R)

def firingOf (weights : WeightMap K R) {source : theory.Term} (event : P.Enabled source) :
    Firing K R event.site := ⟨source, event.target, event.evidence, weights⟩

def Affordable (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    (weights : WeightMap K R) (amount : Nat) {source : theory.Term} (event : P.Enabled source) : Prop :=
  profile (Augmented.keyOf (K := K) event.evidence) weights ≤ amount

instance affordableDecidable (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    (weights : WeightMap K R) (amount : Nat) {source : theory.Term} (event : P.Enabled source) :
    Decidable (Affordable profile weights amount event) := inferInstanceAs (Decidable (_ ≤ _))

noncomputable section

theorem affordable_iff_paid_history
    (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    (weights : WeightMap K R) (amount : Nat) {source : theory.Term} (event : P.Enabled source) :
    Affordable profile weights amount event ↔
      Nonempty (PaidHistory A profile (firingOf weights event) amount) :=
  (paid_history_iff A profile (firingOf weights event) amount).symm

variable [Semiring R]

def fundedRate (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    (weights : WeightMap K R) (amount : Nat) {source : theory.Term} (event : P.Enabled source) : R :=
  A.redexWeight (Affordable profile weights amount) weights event

theorem fundedRate_of_paid
    {profile : (Σ site, K.Key site) → WeightMap K R → Nat}
    {weights : WeightMap K R} {amount : Nat} {source : theory.Term} {event : P.Enabled source}
    (funding : PaidHistory A profile (firingOf weights event) amount) :
    fundedRate A profile weights amount event =
      weights (Augmented.keyOf (K := K) event.evidence) * A.geometricFactor event.evidence :=
  A.redexWeight_of_funded _ _ _
    ((affordable_iff_paid_history A profile weights amount event).mpr ⟨funding⟩)

theorem fundedRate_of_unfunded
    {profile : (Σ site, K.Key site) → WeightMap K R → Nat}
    {weights : WeightMap K R} {amount : Nat} {source : theory.Term} {event : P.Enabled source}
    (unfunded : ¬ Nonempty (PaidHistory A profile (firingOf weights event) amount)) :
    fundedRate A profile weights amount event = 0 :=
  A.redexWeight_of_unfunded _ _ _
    (fun affordable => unfunded
      ((affordable_iff_paid_history A profile weights amount event).mp affordable))

theorem fundedRate_nonzero_iff [NoZeroDivisors R]
    (profile : (Σ site, K.Key site) → WeightMap K R → Nat)
    (weights : WeightMap K R) (amount : Nat) {source : theory.Term} (event : P.Enabled source) :
    fundedRate A profile weights amount event ≠ 0 ↔
      Nonempty (PaidHistory A profile (firingOf weights event) amount) ∧
      weights (Augmented.keyOf (K := K) event.evidence) ≠ 0 ∧ A.geometricFactor event.evidence ≠ 0 := by
  by_cases affordable : Affordable profile weights amount event
  · obtain ⟨funding⟩ := (affordable_iff_paid_history A profile weights amount event).mp affordable
    rw [fundedRate_of_paid A funding, mul_ne_zero_iff]
    exact (and_iff_right (show Nonempty (PaidHistory A profile (firingOf weights event) amount)
      from ⟨funding⟩)).symm
  · have unfunded : ¬ Nonempty (PaidHistory A profile (firingOf weights event) amount) :=
      fun supplied => affordable ((affordable_iff_paid_history A profile weights amount event).mpr supplied)
    rw [fundedRate_of_unfunded A unfunded]
    simp only [ne_self_iff_false, unfunded, false_and]

end

end Mettapedia.GSLT.Weighting.ConfiguredFunding

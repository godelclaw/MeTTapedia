import Mettapedia.Computability.PNP.V13PhaseEScaled

/-!
# PNP v13 Phase E observer ladder

This module climbs the observer ladder on the scaled locked family.  The first
checked rung records the exact obstruction exposed by the scaled public
surface: a one-query observer that reads the public target lock succeeds with
probability one.  Target-blind/no-hit observers still have exact half success.
-/

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

/-! ## Shared finite success lemmas -/

def selfCorrectEquiv {Phi : Type*} (x : Phi -> Bool) :
    {phi : Phi // x phi = x phi} ≃ Phi where
  toFun phi := phi.val
  invFun phi := ⟨phi, rfl⟩
  left_inv := by
    intro phi
    rfl
  right_inv := by
    intro phi
    rfl

theorem globalDecoderSuccess_self_eq_one
    {Phi : Type*} [Fintype Phi] [Nonempty Phi] (x : Phi -> Bool) :
    globalDecoderSuccess x x = 1 := by
  classical
  have hcard :
      Fintype.card {phi : Phi // x phi = x phi} = Fintype.card Phi := by
    exact Fintype.card_congr (selfCorrectEquiv x)
  have hnonzero : ((Fintype.card Phi : Nat) : Rat) ≠ 0 := by
    have hpos : 0 < Fintype.card Phi := Fintype.card_pos_iff.mpr ‹Nonempty Phi›
    exact_mod_cast Nat.ne_of_gt hpos
  unfold globalDecoderSuccess
  rw [hcard]
  field_simp [hnonzero]

/-! ## Rung 1: bounded-query observers -/

inductive PhaseEScaledCoordinate (m k : Nat) where
  | targetLock
  | tail : Fin m -> PhaseEScaledCoordinate m k
  | rowSalt : Fin k -> PhaseEScaledCoordinate m k
  | gauge : Fin (m + 1) -> PhaseEScaledCoordinate m k
  | vvRhs : Fin k -> PhaseEScaledCoordinate m k
deriving DecidableEq, Repr

def phaseEScaledCoordinateRead {m k : Nat} :
    PhaseEScaledCoordinate m k -> PhaseEScaledWorld m k -> Bool
  | .targetLock, omega => (phaseEScaledPublicInput omega).targetLock
  | .tail i, omega => (phaseEScaledPublicInput omega).tailLock i
  | .rowSalt r, omega => omega.rowSalt r
  | .gauge i, omega => omega.gaugeMask i
  | .vvRhs r, omega => (phaseEScaledPublicInput omega).vvRhs r

structure PhaseEScaledDecisionTreeObserver (m k q : Nat) where
  readSet : Finset (PhaseEScaledCoordinate m k)
  decide : PhaseEScaledWorld m k -> Bool
  readBudget : readSet.card ≤ q
  factorsThrough :
    ∀ w0 w1 : PhaseEScaledWorld m k,
      (∀ c ∈ readSet,
        phaseEScaledCoordinateRead c w0 = phaseEScaledCoordinateRead c w1) ->
        decide w0 = decide w1

def phaseEScaledTargetLockObserver (m k : Nat) :
    PhaseEScaledDecisionTreeObserver m k 1 where
  readSet := {PhaseEScaledCoordinate.targetLock}
  decide := phaseEScaledTarget
  readBudget := by
    simp
  factorsThrough := by
    intro w0 w1 hsame
    exact hsame PhaseEScaledCoordinate.targetLock (by simp)

theorem phaseEScaled_targetLockObserver_success_eq_one (m k : Nat) :
    globalDecoderSuccess
        (phaseEScaledTargetLockObserver m k).decide
        (@phaseEScaledTarget m k) =
      1 := by
  exact globalDecoderSuccess_self_eq_one (@phaseEScaledTarget m k)

theorem phaseEScaled_targetLockObserver_reads_one_coordinate (m k : Nat) :
    (phaseEScaledTargetLockObserver m k).readSet.card = 1 := by
  simp [phaseEScaledTargetLockObserver]

def PhaseEScaledNoHitDecisionTreeObserver (m k : Nat) :=
  PhaseEScaledPayload m k -> Bool

theorem phaseEScaled_noHitDecisionTree_success_eq_half (m k : Nat)
    (observer : PhaseEScaledNoHitDecisionTreeObserver m k) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget =
      (1 : Rat) / 2 :=
  phaseEScaled_payloadObserver_success_eq_half m k observer

def phaseEScaledRung1Epsilon (_q m k : Nat) : Rat :=
  if 0 < m + k + 1 then (1 : Rat) / 2 else 1 / 2

theorem phaseEScaled_rung1_targetLock_tight_bound (m k : Nat) :
    globalDecoderSuccess
        (phaseEScaledTargetLockObserver m k).decide
        (@phaseEScaledTarget m k) ≤
      (1 : Rat) / 2 + phaseEScaledRung1Epsilon 1 m k := by
  rw [phaseEScaled_targetLockObserver_success_eq_one]
  simp [phaseEScaledRung1Epsilon]
  norm_num

theorem phaseEScaled_rung1_noHit_exact_bound (m k : Nat)
    (observer : PhaseEScaledNoHitDecisionTreeObserver m k) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget ≤
      (1 : Rat) / 2 + 0 := by
  rw [phaseEScaled_noHitDecisionTree_success_eq_half]
  norm_num

def PhaseEScaledRung1Finding : String :=
  "Rung 1 stops for unrestricted full-coordinate observers: one query to the public target lock has success one; no-hit target-blind observers remain exactly half."

/-! ## Rung 2: juntas and parities -/

abbrev PhaseEScaledJuntaObserver (m k j : Nat) :=
  PhaseEScaledDecisionTreeObserver m k j

def phaseEScaledTargetLockJunta (m k : Nat) :
    PhaseEScaledJuntaObserver m k 1 :=
  phaseEScaledTargetLockObserver m k

theorem phaseEScaled_targetLockJunta_success_eq_one (m k : Nat) :
    globalDecoderSuccess
        (phaseEScaledTargetLockJunta m k).decide
        (@phaseEScaledTarget m k) =
      1 :=
  phaseEScaled_targetLockObserver_success_eq_one m k

theorem phaseEScaled_targetLockJunta_support_card (m k : Nat) :
    (phaseEScaledTargetLockJunta m k).readSet.card = 1 :=
  phaseEScaled_targetLockObserver_reads_one_coordinate m k

structure PhaseEScaledTargetBlindJuntaObserver (m k j : Nat) where
  support : Finset (PhaseEScaledCoordinate m k)
  supportBudget : support.card ≤ j
  noTargetLock : PhaseEScaledCoordinate.targetLock ∉ support
  decidePayload : PhaseEScaledPayload m k -> Bool

theorem phaseEScaled_targetBlindJunta_success_eq_half (m k j : Nat)
    (observer : PhaseEScaledTargetBlindJuntaObserver m k j) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer.decidePayload (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget =
      (1 : Rat) / 2 :=
  phaseEScaled_payloadObserver_success_eq_half m k observer.decidePayload

def phaseEScaledTargetParity (m k : Nat) :
    PhaseEScaledWorld m k -> Bool :=
  phaseEScaledTarget

theorem phaseEScaled_targetParity_success_eq_one (m k : Nat) :
    globalDecoderSuccess (phaseEScaledTargetParity m k)
        (@phaseEScaledTarget m k) =
      1 := by
  exact globalDecoderSuccess_self_eq_one (@phaseEScaledTarget m k)

structure PhaseEScaledTargetBlindParityObserver (m k : Nat) where
  support : Finset (PhaseEScaledCoordinate m k)
  noTargetLock : PhaseEScaledCoordinate.targetLock ∉ support
  parityPayload : PhaseEScaledPayload m k -> Bool

theorem phaseEScaled_targetBlindParity_success_eq_half (m k : Nat)
    (observer : PhaseEScaledTargetBlindParityObserver m k) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer.parityPayload (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget =
      (1 : Rat) / 2 :=
  phaseEScaled_payloadObserver_success_eq_half m k observer.parityPayload

def phaseEScaledRung2JuntaEpsilon (j : Nat) : Rat :=
  if 0 < j then (1 : Rat) / 2 else 0

theorem phaseEScaled_rung2_targetLockJunta_tight_bound (m k : Nat) :
    globalDecoderSuccess
        (phaseEScaledTargetLockJunta m k).decide
        (@phaseEScaledTarget m k) ≤
      (1 : Rat) / 2 + phaseEScaledRung2JuntaEpsilon 1 := by
  rw [phaseEScaled_targetLockJunta_success_eq_one]
  simp [phaseEScaledRung2JuntaEpsilon]
  norm_num

theorem phaseEScaled_rung2_targetBlindJunta_exact_bound (m k j : Nat)
    (observer : PhaseEScaledTargetBlindJuntaObserver m k j) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer.decidePayload (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget ≤
      (1 : Rat) / 2 + 0 := by
  rw [phaseEScaled_targetBlindJunta_success_eq_half]
  norm_num

theorem phaseEScaled_rung2_targetBlindParity_exact_bound (m k : Nat)
    (observer : PhaseEScaledTargetBlindParityObserver m k) :
    globalDecoderSuccess
        (fun omega : PhaseEScaledWorld m k =>
          observer.parityPayload (phaseEScaledPayloadSummary omega))
        phaseEScaledTarget ≤
      (1 : Rat) / 2 + 0 := by
  rw [phaseEScaled_targetBlindParity_success_eq_half]
  norm_num

def PhaseEScaledRung2Finding : String :=
  "Rung 2 has the same public-lock stop: a one-coordinate junta/parity on targetLock succeeds with probability one; target-blind juntas and parities remain exactly half."

end Mettapedia.Computability.PNP

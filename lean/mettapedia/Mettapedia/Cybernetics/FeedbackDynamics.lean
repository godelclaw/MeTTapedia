import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Componentwise feedback and environmental forcing

A finite positive network propagates independently named quantities.  The
coordinate type is arbitrary: no addition of pain, suffering, joy, happiness,
agency, or recipients into one welfare score is imposed.  A uniform numerical
envelope is a bound on every coordinate, not a replacement for the vector.

The recurrence separates incoming environmental forcing from internal
propagation.  Nonnegative coefficients, a row-sum bound, and bounded forcing
give finite-time bounds and a closed invariant region.  Coupling two locally
quiescent components can create persistent or amplifying feedback, so local
attenuation does not establish attenuation of their composition.

This is reusable discrete dynamics.  Interpreting a coordinate as experiential
pain, recurrent amplification, or another quantity is an additional model
choice; the relational predicates of `ReflexiveValence` remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.FeedbackDynamics

universe u

section General

variable {Coordinate : Type u} [Fintype Coordinate]

/-- Positive propagation between explicitly retained coordinates. -/
structure Network (Coordinate : Type u) where
  coefficient : Coordinate → Coordinate → ℚ
  nonnegative : ∀ target source, 0 ≤ coefficient target source

namespace Network

/-- One simultaneous propagation round, including the external input. -/
def step (network : Network Coordinate) (forcing state : Coordinate → ℚ) :
    Coordinate → ℚ :=
  fun target => (∑ source, network.coefficient target source * state source) + forcing target

/-- An actual chronological execution under a time-indexed environment. -/
def run (network : Network Coordinate) (forcing : Nat → Coordinate → ℚ)
    (initial : Coordinate → ℚ) : Nat → Coordinate → ℚ
  | 0 => initial
  | time + 1 => network.step (forcing time) (network.run forcing initial time)

@[simp] theorem run_zero (network : Network Coordinate)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ) :
    network.run forcing initial 0 = initial := rfl

@[simp] theorem run_succ (network : Network Coordinate)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ) (time : Nat) :
    network.run forcing initial (time + 1) =
      network.step (forcing time) (network.run forcing initial time) := rfl

theorem step_nonnegative (network : Network Coordinate)
    {forcing state : Coordinate → ℚ}
    (environment : ∀ coordinate, 0 ≤ forcing coordinate)
    (current : ∀ coordinate, 0 ≤ state coordinate) (target : Coordinate) :
    0 ≤ network.step forcing state target := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun source _ =>
      mul_nonneg (network.nonnegative target source) (current source)
  · exact environment target

theorem run_nonnegative (network : Network Coordinate)
    {forcing : Nat → Coordinate → ℚ} {initial : Coordinate → ℚ}
    (environment : ∀ time coordinate, 0 ≤ forcing time coordinate)
    (current : ∀ coordinate, 0 ≤ initial coordinate) :
    ∀ time coordinate, 0 ≤ network.run forcing initial time coordinate := by
  intro time
  induction time with
  | zero => exact current
  | succ time inductionHypothesis =>
      exact network.step_nonnegative (environment time) inductionHypothesis

/-- Increasing an input or a current coordinate cannot reduce a positive
network's next coordinate. -/
theorem step_mono (network : Network Coordinate)
    {firstInput secondInput firstState secondState : Coordinate → ℚ}
    (inputOrder : ∀ coordinate, firstInput coordinate ≤ secondInput coordinate)
    (stateOrder : ∀ coordinate, firstState coordinate ≤ secondState coordinate)
    (target : Coordinate) :
    network.step firstInput firstState target ≤
      network.step secondInput secondState target := by
  apply add_le_add
  · exact Finset.sum_le_sum fun source _ =>
      mul_le_mul_of_nonneg_left (stateOrder source) (network.nonnegative target source)
  · exact inputOrder target

/-- A row-sum envelope bounds propagation without identifying coordinates. -/
theorem step_le_envelope (network : Network Coordinate) {gain bound : ℚ}
    (boundNonnegative : 0 ≤ bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    {forcing state : Coordinate → ℚ}
    (current : ∀ coordinate, state coordinate ≤ bound) (target : Coordinate) :
    network.step forcing state target ≤ gain * bound + forcing target := by
  unfold step
  apply add_le_add _ (le_refl (forcing target))
  calc
    ∑ source, network.coefficient target source * state source ≤
        ∑ source, network.coefficient target source * bound :=
      Finset.sum_le_sum fun source _ =>
        mul_le_mul_of_nonneg_left (current source) (network.nonnegative target source)
    _ = (∑ source, network.coefficient target source) * bound :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ gain * bound := mul_le_mul_of_nonneg_right (rows target) boundNonnegative

/-- A bounded environment fits inside the available per-round attenuation. -/
theorem step_preserves_envelope (network : Network Coordinate) {gain bound : ℚ}
    (boundNonnegative : 0 ≤ bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    {forcing state : Coordinate → ℚ}
    (environment : ∀ coordinate, forcing coordinate ≤ (1 - gain) * bound)
    (current : ∀ coordinate, state coordinate ≤ bound) (target : Coordinate) :
    network.step forcing state target ≤ bound := by
  have propagated := network.step_le_envelope (forcing := forcing)
    boundNonnegative rows current target
  have incoming := environment target
  nlinarith

theorem run_preserves_envelope (network : Network Coordinate) {gain bound : ℚ}
    (boundNonnegative : 0 ≤ bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    {forcing : Nat → Coordinate → ℚ} {initial : Coordinate → ℚ}
    (environment : ∀ time coordinate, forcing time coordinate ≤ (1 - gain) * bound)
    (current : ∀ coordinate, initial coordinate ≤ bound) :
    ∀ time coordinate, network.run forcing initial time coordinate ≤ bound := by
  intro time
  induction time with
  | zero => exact current
  | succ time inductionHypothesis =>
      exact network.step_preserves_envelope boundNonnegative rows
        (environment time) inductionHypothesis

/-- With no external forcing, each coordinate obeys a geometric upper bound.
Decay follows when the independently checked gain is less than one. -/
theorem run_unforced_le_geometric (network : Network Coordinate) {gain bound : ℚ}
    (gainNonnegative : 0 ≤ gain) (boundNonnegative : 0 ≤ bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    {initial : Coordinate → ℚ} (current : ∀ coordinate, initial coordinate ≤ bound) :
    ∀ time coordinate,
      network.run (fun _ _ => 0) initial time coordinate ≤ gain ^ time * bound := by
  intro time
  induction time with
  | zero => simpa using current
  | succ time inductionHypothesis =>
      intro coordinate
      have next := network.step_le_envelope (forcing := fun _ => 0)
        (mul_nonneg (pow_nonneg gainNonnegative time) boundNonnegative)
        rows inductionHypothesis coordinate
      simpa [run, pow_succ, mul_assoc, mul_left_comm, mul_comm] using next

/-- Restarting an execution retains its actual intermediate state and
shifts the environment, instead of restarting from the original baseline. -/
theorem run_add (network : Network Coordinate) (forcing : Nat → Coordinate → ℚ)
    (initial : Coordinate → ℚ) (first second : Nat) :
    network.run forcing initial (first + second) =
      network.run (fun time => forcing (first + time))
        (network.run forcing initial first) second := by
  induction second with
  | zero => simp
  | succ second inductionHypothesis =>
      simp only [Nat.add_succ, run_succ, inductionHypothesis]

/-- A strictly attenuating network eventually falls below any positive
envelope in every coordinate, when the external input is absent. -/
theorem eventually_below (network : Network Coordinate) {gain bound : ℚ}
    (gainNonnegative : 0 ≤ gain) (gainLessThanOne : gain < 1)
    (boundPositive : 0 < bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    {initial : Coordinate → ℚ} (current : ∀ coordinate, initial coordinate ≤ bound)
    {threshold : ℚ} (thresholdPositive : 0 < threshold) :
    ∃ time, ∀ coordinate,
      network.run (fun _ _ => 0) initial time coordinate < threshold := by
  obtain ⟨time, small⟩ := exists_pow_lt_of_lt_one
    (div_pos thresholdPositive boundPositive) gainLessThanOne
  refine ⟨time, fun coordinate => ?_⟩
  have upper := network.run_unforced_le_geometric gainNonnegative boundPositive.le
    rows current time coordinate
  have below : gain ^ time * bound < threshold :=
    (lt_div_iff₀ boundPositive).mp small
  exact lt_of_le_of_lt upper below

/-- Removing environmental forcing after an actual prefix gives the same
eventual attenuation result from that prefix's endpoint. -/
theorem eventually_below_after_forcing_stops (network : Network Coordinate)
    {forcing : Nat → Coordinate → ℚ} {initial : Coordinate → ℚ}
    (cutoff : Nat) {gain bound : ℚ}
    (gainNonnegative : 0 ≤ gain) (gainLessThanOne : gain < 1)
    (boundPositive : 0 < bound)
    (rows : ∀ target, (∑ source, network.coefficient target source) ≤ gain)
    (current : ∀ coordinate, network.run forcing initial cutoff coordinate ≤ bound)
    (stopped : ∀ time coordinate, forcing (cutoff + time) coordinate = 0)
    {threshold : ℚ} (thresholdPositive : 0 < threshold) :
    ∃ time, ∀ coordinate,
      network.run forcing initial (cutoff + time) coordinate < threshold := by
  obtain ⟨time, attenuated⟩ := network.eventually_below gainNonnegative gainLessThanOne
    boundPositive rows current thresholdPositive
  refine ⟨time, fun coordinate => ?_⟩
  rw [network.run_add forcing initial cutoff time]
  have zeroEnvironment : (fun time => forcing (cutoff + time)) = fun _ _ => 0 := by
    funext time coordinate
    exact stopped time coordinate
  rw [zeroEnvironment]
  exact attenuated coordinate

/-- Change the propagation mechanism at a declared time, retaining the entire
prefix and its actual endpoint.  This models a developmental reconfiguration,
not a reset to a preferred baseline. -/
def reconfiguredRun (before after : Network Coordinate)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ)
    (cutoff time : Nat) : Coordinate → ℚ :=
  if time < cutoff then before.run forcing initial time else
    after.run (fun elapsed => forcing (cutoff + elapsed))
      (before.run forcing initial cutoff) (time - cutoff)

/-- The new mechanism begins at the source execution's exact endpoint. -/
theorem reconfiguredRun_after (before after : Network Coordinate)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ)
    (cutoff elapsed : Nat) :
    before.reconfiguredRun after forcing initial cutoff (cutoff + elapsed) =
      after.run (fun elapsed => forcing (cutoff + elapsed))
        (before.run forcing initial cutoff) elapsed := by
  simp [reconfiguredRun]

/-- Earlier states, including the reconfiguration boundary, are preserved. -/
theorem reconfiguredRun_before (before after : Network Coordinate)
    (forcing : Nat → Coordinate → ℚ) (initial : Coordinate → ℚ)
    {cutoff time : Nat} (earlier : time ≤ cutoff) :
    before.reconfiguredRun after forcing initial cutoff time =
      before.run forcing initial time := by
  by_cases strict : time < cutoff
  · simp [reconfiguredRun, strict]
  · have same : time = cutoff := le_antisymm earlier (Nat.le_of_not_gt strict)
    subst time
    simp [reconfiguredRun]

/-- A developmental reconfiguration into a strictly attenuating mechanism
gives eventual componentwise relief when later forcing is absent.  Nothing
asserts that learning supplies this reconfiguration automatically. -/
theorem reconfiguration_eventually_below (before after : Network Coordinate)
    {forcing : Nat → Coordinate → ℚ} {initial : Coordinate → ℚ}
    (cutoff : Nat) {gain bound : ℚ}
    (gainNonnegative : 0 ≤ gain) (gainLessThanOne : gain < 1)
    (boundPositive : 0 < bound)
    (rows : ∀ target, (∑ source, after.coefficient target source) ≤ gain)
    (current : ∀ coordinate, before.run forcing initial cutoff coordinate ≤ bound)
    (stopped : ∀ elapsed coordinate, forcing (cutoff + elapsed) coordinate = 0)
    {threshold : ℚ} (thresholdPositive : 0 < threshold) :
    ∃ elapsed, ∀ coordinate,
      before.reconfiguredRun after forcing initial cutoff (cutoff + elapsed)
        coordinate < threshold := by
  obtain ⟨elapsed, attenuated⟩ := after.eventually_below gainNonnegative gainLessThanOne
    boundPositive rows current thresholdPositive
  refine ⟨elapsed, fun coordinate => ?_⟩
  rw [reconfiguredRun_after]
  have zeroEnvironment : (fun elapsed => forcing (cutoff + elapsed)) = fun _ _ => 0 := by
    funext elapsed coordinate
    exact stopped elapsed coordinate
  rw [zeroEnvironment]
  exact attenuated coordinate

end Network

end General

/-! ## Independent coordinates and recurrence controls -/

namespace Canary

inductive Coordinate where
  | signal
  | recurrence
  deriving DecidableEq

instance coordinateFintype : Fintype Coordinate where
  elems := {.signal, .recurrence}
  complete := by intro coordinate; cases coordinate <;> simp

/-- These coordinates can be interpreted as pain and sustained amplification,
but that interpretation is separate from their arithmetic. -/
def coupled (gain : ℚ) (nonnegative : 0 ≤ gain) : Network Coordinate where
  coefficient target source := if target = source then 0 else gain
  nonnegative := by
    intro target source
    split
    · norm_num
    · exact nonnegative

def uniform (amount : ℚ) : Coordinate → ℚ := fun _ => amount

theorem coupled_step_uniform (gain : ℚ) (nonnegative : 0 ≤ gain) (amount : ℚ) :
    (coupled gain nonnegative).step (uniform 0) (uniform amount) =
      uniform (gain * amount) := by
  funext coordinate
  cases coordinate <;>
    simp [Network.step, coupled, uniform, Finset.univ, Fintype.elems]

theorem coupled_run_uniform (gain : ℚ) (nonnegative : 0 ≤ gain) (amount : ℚ)
    (time : Nat) :
    (coupled gain nonnegative).run (fun _ => uniform 0) (uniform amount) time =
      uniform (gain ^ time * amount) := by
  induction time with
  | zero => simp
  | succ time inductionHypothesis =>
      rw [Network.run_succ, inductionHypothesis, coupled_step_uniform]
      simp [pow_succ, mul_left_comm, mul_comm]

/-- Both self-couplings vanish, yet a cross-component loop persists. -/
theorem locally_quiescent_but_persistent :
    (∀ coordinate, (coupled 1 (by norm_num)).coefficient coordinate coordinate = 0) ∧
      ∀ time coordinate,
        (coupled 1 (by norm_num)).run (fun _ => uniform 0) (uniform 1) time coordinate = 1 := by
  constructor
  · intro coordinate
    simp [coupled]
  · intro time coordinate
    rw [coupled_run_uniform]
    simp [uniform]

/-- Cross-component propagation can amplify despite zero self-coupling. -/
theorem locally_quiescent_but_amplifying :
    (∀ coordinate, (coupled 2 (by norm_num)).coefficient coordinate coordinate = 0) ∧
      (coupled 2 (by norm_num)).run (fun _ => uniform 0) (uniform 1) 1 .signal > 1 := by
  constructor
  · intro coordinate
    simp [coupled]
  · rw [coupled_run_uniform]
    norm_num [uniform]

/-- The attenuation case uses the same nonzero recurrent topology. -/
theorem coupled_half_attenuates (time : Nat) (coordinate : Coordinate) :
    (coupled (1 / 2) (by norm_num)).run (fun _ => uniform 0) (uniform 1) time coordinate =
      (1 / 2 : ℚ) ^ time := by
  rw [coupled_run_uniform]
  simp [uniform]

/-- A concrete developmental control first amplifies and then changes the
couplings to attenuation, preserving both component identities and their
values at the change boundary. -/
def regulated (cutoff time : Nat) : Coordinate → ℚ :=
  (coupled 2 (by norm_num)).reconfiguredRun (coupled (1 / 2) (by norm_num))
    (fun _ => uniform 0) (uniform 1) cutoff time

theorem regulated_after (cutoff elapsed : Nat) (coordinate : Coordinate) :
    regulated cutoff (cutoff + elapsed) coordinate =
      (1 / 2 : ℚ) ^ elapsed * 2 ^ cutoff := by
  unfold regulated
  rw [Network.reconfiguredRun_after, coupled_run_uniform]
  simp only [mul_one]
  rw [coupled_run_uniform]
  rfl

/-- This selected developmental dynamics has a finite peak at its mechanism
change.  It proves no historical forecast about actual subjects. -/
theorem regulated_has_peak (cutoff time : Nat) (coordinate : Coordinate) :
    regulated cutoff time coordinate ≤ regulated cutoff cutoff coordinate := by
  have boundary : regulated cutoff cutoff coordinate = (2 : ℚ) ^ cutoff := by
    simpa using regulated_after cutoff 0 coordinate
  rw [boundary]
  by_cases earlier : time ≤ cutoff
  · unfold regulated
    rw [Network.reconfiguredRun_before _ _ _ _ earlier, coupled_run_uniform]
    simp only [uniform, mul_one]
    exact pow_le_pow_right₀ (by norm_num) earlier
  · have later : time = cutoff + (time - cutoff) := by omega
    rw [later, regulated_after]
    have attenuated : (1 / 2 : ℚ) ^ (time - cutoff) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    simpa using mul_le_mul_of_nonneg_right attenuated
      (pow_nonneg (show 0 ≤ (2 : ℚ) by norm_num) cutoff)

/-- With the same initial recurrent topology, retaining amplification
continues increasing after every finite time and supplies no finite peak. -/
theorem unregulated_keeps_increasing (time : Nat) (coordinate : Coordinate) :
    (coupled 2 (by norm_num)).run (fun _ => uniform 0) (uniform 1) time coordinate <
      (coupled 2 (by norm_num)).run (fun _ => uniform 0) (uniform 1)
        (time + 1) coordinate := by
  rw [coupled_run_uniform, coupled_run_uniform]
  simp only [uniform, mul_one, pow_succ]
  have positive : 0 < (2 : ℚ) ^ time := pow_pos (by norm_num) time
  linarith

/-- Environmental input alone can sustain a component with no internal
propagation. -/
def driven : Network Coordinate where
  coefficient _ _ := 0
  nonnegative := by intros; norm_num

theorem external_forcing_persists (time : Nat) (coordinate : Coordinate) :
    driven.run (fun _ => uniform 1) (uniform 0) (time + 1) coordinate = 1 := by
  simp [Network.run, Network.step, driven, uniform]

/-- A total projection cannot recover the independently retained signal. -/
theorem sum_projection_loses_signal :
    ¬ ∃ recover : ℚ → ℚ, ∀ state : Coordinate → ℚ,
      recover (state .signal + state .recurrence) = state .signal := by
  rintro ⟨recover, exactReadout⟩
  have first := exactReadout (fun coordinate => if coordinate = .signal then 1 else 0)
  have second := exactReadout (fun coordinate => if coordinate = .signal then 0 else 1)
  simp at first second
  linarith

end Canary

end Mettapedia.Cybernetics.FeedbackDynamics

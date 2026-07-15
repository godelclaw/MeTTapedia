import Mettapedia.GraphTheory.FourColor.GoertzelV24EarlyFalsifiers

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorPumping

open GoertzelV24EarlyFalsifiers

/-- Exact-length reachability for a deterministic corridor transfer. -/
def ExactDeterministicTransfer
    {Profile : Type*} (step : Profile → Profile)
    (length : Nat) (start finish : Profile) : Prop :=
  (step^[length]) start = finish

/-- An exact-length path in a possibly branching corridor transfer. -/
inductive ExactRelationalTransfer
    {Profile : Type*} (oneStep : Profile → Profile → Prop) :
    Nat → Profile → Profile → Prop where
  | zero (profile : Profile) : ExactRelationalTransfer oneStep 0 profile profile
  | succ {length : Nat} {start next finish : Profile} :
      oneStep start next →
      ExactRelationalTransfer oneStep length next finish →
      ExactRelationalTransfer oneStep (length + 1) start finish

/-- Every live transfer state has a live one-step continuation. -/
def LiveTransferIsSerial
    {Profile : Type*} (isAliveRelevant : Profile → Prop)
    (oneStep : Profile → Profile → Prop) : Prop :=
  ∀ profile, isAliveRelevant profile →
    ∃ next, isAliveRelevant next ∧ oneStep profile next

/-- Exact relational paths concatenate and their lengths add. -/
theorem ExactRelationalTransfer.comp
    {Profile : Type*} {oneStep : Profile → Profile → Prop}
    {firstLength secondLength : Nat} {start middle finish : Profile}
    (hfirst : ExactRelationalTransfer oneStep firstLength start middle)
    (hsecond : ExactRelationalTransfer oneStep secondLength middle finish) :
    ExactRelationalTransfer oneStep (firstLength + secondLength) start finish := by
  induction hfirst with
  | zero => simpa using hsecond
  | @succ length start next middle hstep htail ih =>
      have hpath := ExactRelationalTransfer.succ hstep (ih hsecond)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpath

/-- A positive exact return can be traversed any number of whole periods. -/
theorem ExactRelationalTransfer.repeat
    {Profile : Type*} {oneStep : Profile → Profile → Prop}
    {period : Nat} {cycleEntry : Profile}
    (hreturn : ExactRelationalTransfer oneStep period cycleEntry cycleEntry) :
    ∀ repetitions : Nat,
      ExactRelationalTransfer oneStep (repetitions * period)
        cycleEntry cycleEntry := by
  intro repetitions
  induction repetitions with
  | zero => simpa using ExactRelationalTransfer.zero (oneStep := oneStep) cycleEntry
  | succ repetitions ih =>
      have hpath := hreturn.comp ih
      simpa [Nat.succ_mul, Nat.add_comm] using hpath

/-- Once an exact prefix reaches a positive-period return, concatenation
proves every length in that prefix-plus-period congruence class. -/
theorem exactRelationalTransfer_periodicPadding
    {Profile : Type*} {oneStep : Profile → Profile → Prop}
    {start cycleEntry : Profile} {preperiod period : Nat}
    (hprefix : ExactRelationalTransfer oneStep preperiod start cycleEntry)
    (hreturn : ExactRelationalTransfer oneStep period cycleEntry cycleEntry) :
    ∀ repetitions : Nat,
      ExactRelationalTransfer oneStep (preperiod + repetitions * period)
        start cycleEntry := by
  intro repetitions
  exact hprefix.comp (hreturn.repeat repetitions)

/-- The finite-orbit certificate needed for congruence-correct corridor
pumping. The recurrent state remains in the live class, its period is
positive, and every whole-period padding of the prefix reaches that state. -/
def FiniteDeterministicOrbitCertificate
    {Profile : Type*} (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop) (start : Profile) : Prop :=
  ∃ cycleEntry : Profile, ∃ preperiod period : Nat,
    0 < period ∧
    isAliveRelevant cycleEntry ∧
    (step^[preperiod]) start = cycleEntry ∧
    (step^[period]) cycleEntry = cycleEntry ∧
    ∀ repetitions : Nat,
      (step^[preperiod + repetitions * period]) start = cycleEntry

private theorem iterate_preserves
    {Profile : Type*} {step : Profile → Profile}
    {isAliveRelevant : Profile → Prop}
    (hstep : ∀ profile, isAliveRelevant profile → isAliveRelevant (step profile))
    {start : Profile} (hstart : isAliveRelevant start) :
    ∀ length : Nat, isAliveRelevant ((step^[length]) start) := by
  intro length
  induction length generalizing start with
  | zero => simpa
  | succ length ih =>
      rw [Function.iterate_succ_apply]
      exact ih (hstep start hstart)

private theorem iterate_period_mul_eq
    {Profile : Type*} (step : Profile → Profile)
    (cycleEntry : Profile) (period : Nat)
    (hreturn : (step^[period]) cycleEntry = cycleEntry) :
    ∀ repetitions : Nat,
      (step^[repetitions * period]) cycleEntry = cycleEntry := by
  intro repetitions
  induction repetitions with
  | zero => simp
  | succ repetitions ih =>
      have hexponent :
          (repetitions + 1) * period = period + repetitions * period := by
        simp [Nat.add_mul, Nat.add_comm]
      calc
        (step^[(repetitions + 1) * period]) cycleEntry =
            (step^[period + repetitions * period]) cycleEntry := by rw [hexponent]
        _ = (step^[period]) ((step^[repetitions * period]) cycleEntry) :=
              Function.iterate_add_apply step period (repetitions * period) cycleEntry
        _ = (step^[period]) cycleEntry := by rw [ih]
        _ = cycleEntry := hreturn

private theorem orbitCertificate_of_collision
    {Profile : Type*} (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop)
    (hstep : ∀ profile, isAliveRelevant profile → isAliveRelevant (step profile))
    (start : Profile) (hstart : isAliveRelevant start)
    (first second : Nat) (hlt : first < second)
    (hcollision : (step^[first]) start = (step^[second]) start) :
    FiniteDeterministicOrbitCertificate step isAliveRelevant start := by
  let cycleEntry := (step^[first]) start
  let period := second - first
  have hperiod_pos : 0 < period := by
    dsimp [period]
    omega
  have hreturn : (step^[period]) cycleEntry = cycleEntry := by
    calc
      (step^[period]) cycleEntry =
          (step^[(second - first) + first]) start := by
            rw [Function.iterate_add_apply]
      _ = (step^[second]) start := by
            rw [Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      _ = (step^[first]) start := hcollision.symm
      _ = cycleEntry := rfl
  have hperiodic : ∀ repetitions : Nat,
      (step^[repetitions * period]) cycleEntry = cycleEntry :=
    iterate_period_mul_eq step cycleEntry period hreturn
  exact ⟨cycleEntry, first, period, hperiod_pos,
    iterate_preserves hstep hstart first, rfl, hreturn, by
      intro repetitions
      calc
        (step^[first + repetitions * period]) start =
            (step^[repetitions * period + first]) start := by
              rw [Nat.add_comm]
        _ = (step^[repetitions * period]) ((step^[first]) start) :=
              Function.iterate_add_apply step (repetitions * period) first start
        _ = (step^[repetitions * period]) cycleEntry := rfl
        _ = cycleEntry := hperiodic repetitions
    ⟩

/-- Every orbit of a live-preserving deterministic transfer on a finite
profile space eventually reaches a live recurrent state with positive period.
The certificate also proves the exact admissible padding congruence. -/
theorem finiteDeterministicTransfer_periodicOrbit
    {Profile : Type*} [Fintype Profile]
    (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop)
    (hstep : ∀ profile, isAliveRelevant profile → isAliveRelevant (step profile))
    (start : Profile) (hstart : isAliveRelevant start) :
    FiniteDeterministicOrbitCertificate step isAliveRelevant start := by
  classical
  let orbit : Fin (Fintype.card Profile + 1) → Profile :=
    fun index => (step^[index.val]) start
  have hcard : Fintype.card Profile < Fintype.card (Fin (Fintype.card Profile + 1)) := by
    simp
  obtain ⟨first, second, hne, hcollision⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt orbit hcard
  have hval_ne : first.val ≠ second.val := by
    intro hval
    exact hne (Fin.ext hval)
  rcases Nat.lt_or_gt_of_ne hval_ne with hlt | hgt
  · exact orbitCertificate_of_collision step isAliveRelevant hstep start hstart
      first.val second.val hlt hcollision
  · exact orbitCertificate_of_collision step isAliveRelevant hstep start hstart
      second.val first.val hgt hcollision.symm

/-- Finite deterministic recurrence proves the corrected L2 pumping statement:
padding is available precisely along a positive-period congruence class, not
at every sufficiently large length. -/
theorem finiteDeterministicTransfer_periodicCorridorPumpingWithCongruence
    {Profile : Type*} [Fintype Profile]
    (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop)
    (hstep : ∀ profile, isAliveRelevant profile → isAliveRelevant (step profile)) :
    PeriodicCorridorPumpingWithCongruence isAliveRelevant
      (ExactDeterministicTransfer step) := by
  intro start hstart
  obtain ⟨cycleEntry, preperiod, period, hperiod_pos, _hcycleEntry_alive,
      hprefix, hreturn, hpadded⟩ :=
    finiteDeterministicTransfer_periodicOrbit
      step isAliveRelevant hstep start hstart
  exact ⟨cycleEntry, preperiod, period, hperiod_pos, hprefix, hreturn, by
      intro length hlength
      obtain ⟨repetitions, rfl⟩ := hlength
      exact hpadded repetitions⟩

private theorem exactRelationalTransfer_iterate
    {Profile : Type*} (oneStep : Profile → Profile → Prop)
    (next : Profile → Profile)
    (isAliveRelevant : Profile → Prop)
    (hnext_alive : ∀ profile,
      isAliveRelevant profile → isAliveRelevant (next profile))
    (hnext_step : ∀ profile,
      isAliveRelevant profile → oneStep profile (next profile)) :
    ∀ length start, isAliveRelevant start →
      ExactRelationalTransfer oneStep length start ((next^[length]) start) := by
  intro length
  induction length with
  | zero =>
      intro start _hstart
      exact ExactRelationalTransfer.zero start
  | succ length ih =>
      intro start hstart
      rw [Function.iterate_succ_apply]
      exact ExactRelationalTransfer.succ
        (hnext_step start hstart)
        (ih (next start) (hnext_alive start hstart))

/-- Corrected finite-state L2 engine for a branching corridor transfer. If
every live profile has a live successor, choose one such successor at each
profile and apply finite-orbit recurrence. The resulting exact relational
paths include a positive return and every whole-period padding of the prefix.
No determinism or one-step self-loop is assumed. -/
theorem finiteSerialTransfer_periodicCorridorPumpingWithCongruence
    {Profile : Type*} [Fintype Profile]
    (isAliveRelevant : Profile → Prop)
    (oneStep : Profile → Profile → Prop)
    (hserial : LiveTransferIsSerial isAliveRelevant oneStep) :
    PeriodicCorridorPumpingWithCongruence isAliveRelevant
      (ExactRelationalTransfer oneStep) := by
  classical
  intro start hstart
  let next : Profile → Profile := fun profile =>
    if hprofile : isAliveRelevant profile then
      Classical.choose (hserial profile hprofile)
    else
      start
  have hnext_alive : ∀ profile,
      isAliveRelevant profile → isAliveRelevant (next profile) := by
    intro profile hprofile
    simp only [next, dif_pos hprofile]
    exact (Classical.choose_spec (hserial profile hprofile)).1
  have hnext_step_of_alive : ∀ profile,
      isAliveRelevant profile → oneStep profile (next profile) := by
    intro profile hprofile
    simp only [next, dif_pos hprofile]
    exact (Classical.choose_spec (hserial profile hprofile)).2
  obtain ⟨cycleEntry, preperiod, period, hperiod_pos, hcycleEntry_alive,
      hprefix, hreturn, hpadded⟩ :=
    finiteDeterministicTransfer_periodicOrbit
      next isAliveRelevant hnext_alive start hstart
  have hprefix_path :
      ExactRelationalTransfer oneStep preperiod start cycleEntry := by
    have hpath := exactRelationalTransfer_iterate oneStep next
      isAliveRelevant hnext_alive hnext_step_of_alive preperiod start hstart
    rwa [hprefix] at hpath
  have hreturn_path :
      ExactRelationalTransfer oneStep period cycleEntry cycleEntry := by
    have hpath := exactRelationalTransfer_iterate oneStep next
      isAliveRelevant hnext_alive hnext_step_of_alive
      period cycleEntry hcycleEntry_alive
    rwa [hreturn] at hpath
  exact ⟨cycleEntry, preperiod, period, hperiod_pos,
    hprefix_path, hreturn_path, by
      intro length hlength
      obtain ⟨repetitions, rfl⟩ := hlength
      have hpath := exactRelationalTransfer_iterate oneStep next
        isAliveRelevant hnext_alive hnext_step_of_alive
        (preperiod + repetitions * period) start hstart
      rw [hpadded repetitions] at hpath
      exact hpath⟩

end GoertzelV24CorridorPumping

end Mettapedia.GraphTheory.FourColor

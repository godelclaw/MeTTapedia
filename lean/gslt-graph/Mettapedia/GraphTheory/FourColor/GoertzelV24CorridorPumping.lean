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
    {Profile : Type*} [Fintype Profile] (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop) (start : Profile) : Prop :=
  ∃ cycleEntry : Profile, ∃ preperiod period : Nat,
    0 < period ∧
    preperiod < Fintype.card Profile + 1 ∧
    period ≤ Fintype.card Profile ∧
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
    {Profile : Type*} [Fintype Profile] (step : Profile → Profile)
    (isAliveRelevant : Profile → Prop)
    (hstep : ∀ profile, isAliveRelevant profile → isAliveRelevant (step profile))
    (start : Profile) (hstart : isAliveRelevant start)
    (first second : Nat) (hlt : first < second)
    (hsecond : second < Fintype.card Profile + 1)
    (hcollision : (step^[first]) start = (step^[second]) start) :
    FiniteDeterministicOrbitCertificate step isAliveRelevant start := by
  let cycleEntry := (step^[first]) start
  let period := second - first
  have hperiod_pos : 0 < period := by
    dsimp [period]
    omega
  have hpreperiod_bound : first < Fintype.card Profile + 1 :=
    lt_trans hlt hsecond
  have hperiod_bound : period ≤ Fintype.card Profile := by
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
    hpreperiod_bound, hperiod_bound,
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
      first.val second.val hlt second.isLt hcollision
  · exact orbitCertificate_of_collision step isAliveRelevant hstep start hstart
      second.val first.val hgt first.isLt hcollision.symm

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
  obtain ⟨cycleEntry, preperiod, period, hperiod_pos,
      _hpreperiod_bound, _hperiod_bound, _hcycleEntry_alive,
      hprefix, hreturn, hpadded⟩ :=
    finiteDeterministicTransfer_periodicOrbit
      step isAliveRelevant hstep start hstart
  exact ⟨cycleEntry, preperiod, period, hperiod_pos, hprefix, hreturn, by
      intro length hlength
      obtain ⟨repetitions, rfl⟩ := hlength
      exact hpadded repetitions⟩

/-- The full eventual-periodicity statement for a deterministic map. After
the preperiod, every offset is invariant under adding whole periods. -/
def EventuallyPeriodicIterates
    {State : Type*} (step : State → State) (start : State) : Prop :=
  ∃ preperiod period : Nat, 0 < period ∧
    ∀ offset repetitions : Nat,
      (step^[preperiod + offset + repetitions * period]) start =
        (step^[preperiod + offset]) start

/-- Every orbit on a finite state space is eventually periodic at all future
offsets, with preperiod and period bounded by the state-space cardinality. -/
theorem finiteDeterministicTransfer_eventuallyPeriodicIteratesWithBounds
    {State : Type*} [Fintype State]
    (step : State → State) (start : State) :
    ∃ preperiod period : Nat,
      preperiod < Fintype.card State + 1 ∧
      0 < period ∧
      period ≤ Fintype.card State ∧
      ∀ offset repetitions : Nat,
        (step^[preperiod + offset + repetitions * period]) start =
          (step^[preperiod + offset]) start := by
  obtain ⟨cycleEntry, preperiod, period, hperiod_pos,
      hpreperiod_bound, hperiod_bound, _hcycleEntry_alive,
      hprefix, hreturn, _hpadded⟩ :=
    finiteDeterministicTransfer_periodicOrbit
      step (fun _ : State => True) (fun _ _ => True.intro) start True.intro
  have hperiodic : ∀ repetitions : Nat,
      (step^[repetitions * period]) cycleEntry = cycleEntry :=
    iterate_period_mul_eq step cycleEntry period hreturn
  exact ⟨preperiod, period, hpreperiod_bound, hperiod_pos, hperiod_bound, by
    intro offset repetitions
    calc
      (step^[preperiod + offset + repetitions * period]) start =
          (step^[(offset + repetitions * period) + preperiod]) start := by
            apply congrArg (fun exponent => (step^[exponent]) start)
            ac_rfl
      _ = (step^[offset + repetitions * period])
          ((step^[preperiod]) start) :=
            Function.iterate_add_apply step
              (offset + repetitions * period) preperiod start
      _ = (step^[offset + repetitions * period]) cycleEntry := by rw [hprefix]
      _ = (step^[offset]) ((step^[repetitions * period]) cycleEntry) :=
            Function.iterate_add_apply step offset
              (repetitions * period) cycleEntry
      _ = (step^[offset]) cycleEntry := by rw [hperiodic repetitions]
      _ = (step^[offset]) ((step^[preperiod]) start) := by rw [hprefix]
      _ = (step^[offset + preperiod]) start :=
            (Function.iterate_add_apply step offset preperiod start).symm
      _ = (step^[preperiod + offset]) start := by
            apply congrArg (fun exponent => (step^[exponent]) start)
            ac_rfl⟩

/-- Bound-free interface to finite deterministic eventual periodicity. -/
theorem finiteDeterministicTransfer_eventuallyPeriodicIterates
    {State : Type*} [Fintype State]
    (step : State → State) (start : State) :
    EventuallyPeriodicIterates step start := by
  obtain ⟨preperiod, period, _hpreperiod_bound, hperiod_pos,
      _hperiod_bound, hperiodic⟩ :=
    finiteDeterministicTransfer_eventuallyPeriodicIteratesWithBounds step start
  exact ⟨preperiod, period, hperiod_pos, hperiodic⟩

/-- One-step image of a finite set of profiles under a branching transfer. -/
def relationalTransferPost
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (states : Finset Profile) : Finset Profile :=
  Finset.univ.filter fun target =>
    ∃ source ∈ states, oneStep source target

theorem mem_relationalTransferPost_iff
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (states : Finset Profile) (target : Profile) :
    target ∈ relationalTransferPost oneStep states ↔
      ∃ source ∈ states, oneStep source target := by
  simp [relationalTransferPost]

/-- Profiles reachable after exactly `length` steps from any initial profile. -/
def reachableProfilesAfter
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (length : Nat) : Finset Profile :=
  ((relationalTransferPost oneStep)^[length]) initial

theorem mem_reachableProfilesAfter_iff
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (length : Nat) (finish : Profile) :
    finish ∈ reachableProfilesAfter oneStep initial length ↔
      ∃ start ∈ initial,
        ExactRelationalTransfer oneStep length start finish := by
  induction length generalizing initial with
  | zero =>
      constructor
      · intro hfinish
        exact ⟨finish, by simpa [reachableProfilesAfter] using hfinish,
          ExactRelationalTransfer.zero finish⟩
      · rintro ⟨start, hstart, hpath⟩
        cases hpath
        simpa [reachableProfilesAfter] using hstart
  | succ length ih =>
      rw [show reachableProfilesAfter oneStep initial (length + 1) =
          reachableProfilesAfter oneStep
            (relationalTransferPost oneStep initial) length by
        simp [reachableProfilesAfter, Function.iterate_succ_apply]]
      rw [ih]
      constructor
      · rintro ⟨next, hnext, htail⟩
        rcases (mem_relationalTransferPost_iff oneStep initial next).mp hnext with
          ⟨start, hstart, hstep⟩
        exact ⟨start, hstart, ExactRelationalTransfer.succ hstep htail⟩
      · rintro ⟨start, hstart, hpath⟩
        cases hpath with
        | succ hstep htail =>
            exact ⟨_, (mem_relationalTransferPost_iff oneStep initial _).mpr
              ⟨start, hstart, hstep⟩, htail⟩

/-- Acceptance at an exact corridor length, computed from the complete
reachable-profile set rather than one selected orbit. -/
def TransferAcceptsInExactly
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (length : Nat) : Prop :=
  ∃ finish ∈ reachableProfilesAfter oneStep initial length,
    isAccepting finish

/-- Corrected language-level L2 theorem. For every finite branching transfer,
exact-length acceptance is eventually periodic. Thus both acceptance and
rejection are preserved after adding whole periods in the correct congruence
class; no self-loop or live-continuation premise is required. -/
theorem finiteRelationalTransfer_acceptanceEventuallyPeriodic
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    ∃ preperiod period : Nat, 0 < period ∧
      ∀ offset repetitions : Nat,
        (TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset + repetitions * period) ↔
          TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset)) := by
  obtain ⟨preperiod, period, hperiod_pos, hperiodic⟩ :=
    finiteDeterministicTransfer_eventuallyPeriodicIterates
      (relationalTransferPost oneStep) initial
  exact ⟨preperiod, period, hperiod_pos, by
    intro offset repetitions
    unfold TransferAcceptsInExactly reachableProfilesAfter
    rw [hperiodic offset repetitions]⟩

/-- Effective form of language-level L2. The deterministic state is the whole
reachable-profile set, so the bounds are those of the finite powerset
`Finset Profile`. -/
theorem finiteRelationalTransfer_acceptanceEventuallyPeriodicWithBounds
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    ∃ preperiod period : Nat,
      preperiod < Fintype.card (Finset Profile) + 1 ∧
      0 < period ∧
      period ≤ Fintype.card (Finset Profile) ∧
      ∀ offset repetitions : Nat,
        (TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset + repetitions * period) ↔
          TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset)) := by
  obtain ⟨preperiod, period, hpreperiod_bound, hperiod_pos,
      hperiod_bound, hperiodic⟩ :=
    finiteDeterministicTransfer_eventuallyPeriodicIteratesWithBounds
      (relationalTransferPost oneStep) initial
  exact ⟨preperiod, period, hpreperiod_bound, hperiod_pos, hperiod_bound, by
    intro offset repetitions
    unfold TransferAcceptsInExactly reachableProfilesAfter
    rw [hperiodic offset repetitions]⟩

/-- Rejection has the same eventual congruence law. This is the polarity used
when a minimal-counterexample argument starts from a zero accepted-path count. -/
theorem finiteRelationalTransfer_rejectionEventuallyPeriodic
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    ∃ preperiod period : Nat, 0 < period ∧
      ∀ offset repetitions : Nat,
        (¬ TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset + repetitions * period) ↔
          ¬ TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset)) := by
  obtain ⟨preperiod, period, hperiod_pos, hperiodic⟩ :=
    finiteRelationalTransfer_acceptanceEventuallyPeriodic
      oneStep initial isAccepting
  exact ⟨preperiod, period, hperiod_pos, by
    intro offset repetitions
    exact not_congr (hperiodic offset repetitions)⟩

/-- Effective rejection form used by finite-base descent. -/
theorem finiteRelationalTransfer_rejectionEventuallyPeriodicWithBounds
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    ∃ preperiod period : Nat,
      preperiod < Fintype.card (Finset Profile) + 1 ∧
      0 < period ∧
      period ≤ Fintype.card (Finset Profile) ∧
      ∀ offset repetitions : Nat,
        (¬ TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset + repetitions * period) ↔
          ¬ TransferAcceptsInExactly oneStep initial isAccepting
            (preperiod + offset)) := by
  obtain ⟨preperiod, period, hpreperiod_bound, hperiod_pos,
      hperiod_bound, hperiodic⟩ :=
    finiteRelationalTransfer_acceptanceEventuallyPeriodicWithBounds
      oneStep initial isAccepting
  exact ⟨preperiod, period, hpreperiod_bound, hperiod_pos, hperiod_bound, by
    intro offset repetitions
    exact not_congr (hperiodic offset repetitions)⟩

/-- Arithmetic core of congruence-correct descent. A rejected length beyond
one full period above the preperiod has a strictly smaller rejected
representative in the same eventual residue class. -/
theorem exists_strictlySmaller_rejection_of_periodic
    (accepts : Nat → Prop) (preperiod period : Nat)
    (hperiod_pos : 0 < period)
    (hperiodic : ∀ offset repetitions : Nat,
      (accepts (preperiod + offset + repetitions * period) ↔
        accepts (preperiod + offset)))
    (length : Nat) (hlength : preperiod + period ≤ length)
    (hreject : ¬ accepts length) :
    ∃ shorter : Nat,
      preperiod ≤ shorter ∧ shorter < length ∧ ¬ accepts shorter := by
  let delta := length - preperiod
  let offset := delta % period
  let repetitions := delta / period
  have hpreperiod_le : preperiod ≤ length := by omega
  have hperiod_le_delta : period ≤ delta := by
    dsimp [delta]
    omega
  have hrepetitions_pos : 0 < repetitions := by
    exact Nat.div_pos hperiod_le_delta hperiod_pos
  have hdelta_decomposition : delta = offset + repetitions * period := by
    dsimp [offset, repetitions]
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div delta period).symm
  have hlength_decomposition :
      length = preperiod + offset + repetitions * period := by
    have hprefix := Nat.add_sub_of_le hpreperiod_le
    dsimp [delta] at hdelta_decomposition
    omega
  have hreject_decomposition :
      ¬ accepts (preperiod + offset + repetitions * period) := by
    simpa only [← hlength_decomposition] using hreject
  have hreject_short : ¬ accepts (preperiod + offset) :=
    (not_congr (hperiodic offset repetitions)).mp hreject_decomposition
  exact ⟨preperiod + offset, Nat.le_add_right _ _, by
    have hproduct_pos : 0 < repetitions * period :=
      Nat.mul_pos hrepetitions_pos hperiod_pos
    omega, hreject_short⟩

/-- Effective corrected L2 descent for a finite branching corridor transfer.
Every rejected length beyond the finite reachable-set threshold descends to a
strictly smaller rejected length in its eventual congruence class. -/
theorem finiteRelationalTransfer_rejectionDescentWithBounds
    {Profile : Type*} [Fintype Profile] [DecidableEq Profile]
    (oneStep : Profile → Profile → Prop) [DecidableRel oneStep]
    (initial : Finset Profile) (isAccepting : Profile → Prop) :
    ∃ preperiod period : Nat,
      preperiod < Fintype.card (Finset Profile) + 1 ∧
      0 < period ∧
      period ≤ Fintype.card (Finset Profile) ∧
      ∀ length : Nat,
        preperiod + period ≤ length →
        ¬ TransferAcceptsInExactly oneStep initial isAccepting length →
        ∃ shorter : Nat,
          preperiod ≤ shorter ∧ shorter < length ∧
          ¬ TransferAcceptsInExactly oneStep initial isAccepting shorter := by
  obtain ⟨preperiod, period, hpreperiod_bound, hperiod_pos,
      hperiod_bound, hperiodic⟩ :=
    finiteRelationalTransfer_acceptanceEventuallyPeriodicWithBounds
      oneStep initial isAccepting
  exact ⟨preperiod, period, hpreperiod_bound, hperiod_pos, hperiod_bound, by
    intro length hlength hreject
    exact exists_strictlySmaller_rejection_of_periodic
      (TransferAcceptsInExactly oneStep initial isAccepting)
      preperiod period hperiod_pos
      hperiodic
      length hlength hreject⟩

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
  obtain ⟨cycleEntry, preperiod, period, hperiod_pos,
      _hpreperiod_bound, _hperiod_bound, hcycleEntry_alive,
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

import Mettapedia.GSLT.LanguageDef.CertificateGSLTBuchiAuthority

/-!
# Exact finite evidence for recurrence from a selected root

A controller chooses one successor at each state.  The claim certified here is
that its execution from the selected root stays in the admitted region, uses
legal transitions, and visits accepting states beyond every finite prefix.

The certificate gives a finite invariant region and a natural-number progress
rank.  Only the certified region is checked.  An unreachable bad component in
the controller's original active region therefore does not invalidate a true
root claim.  Completeness constructs the reachable region and first-acceptance
ranks from the independently defined infinite-run meaning.

This is an exact certificate authority for a fixed deterministic controller on
a finite carrier.  It does not decide arbitrary S1S or S2S formulas, synthesize
a controller, or establish recurrence for unselected nondeterministic choices.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uState uAction uAuthority

theorem ControlledExecution.state_eq_iterate
    {State : Type uState} {Action : Type uAction}
    {controller : MemorylessController State Action} {root : State}
    (execution : ControlledExecution controller root) (index : Nat) :
    execution.state index = controller.next^[index] root := by
  induction index with
  | zero => exact execution.starts
  | succ index inductionHypothesis =>
      rw [execution.follows, inductionHypothesis,
        Function.iterate_succ_apply']

/-- Recurrence can equivalently be stated on the canonical execution; every
execution of this deterministic controller has exactly that sequence. -/
theorem MemorylessController.buchi_iff_canonical
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (controller : MemorylessController State Action) (root : State) :
    controller.BuchiWinning system root ↔
      InfinitelyOftenAccepting system (fun n => controller.next^[n] root) := by
  constructor
  · intro winning
    exact winning (controller.canonicalExecution root)
  · intro recurrent execution lowerBound
    obtain ⟨visit, after, accepting⟩ := recurrent lowerBound
    exact ⟨visit, after, by rwa [execution.state_eq_iterate]⟩

/-- Changing an admission mask does not change a controller's selected path.
Legality remains a separate obligation. -/
theorem MemorylessController.buchi_congr_next
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    {left right : MemorylessController State Action}
    (sameNext : left.next = right.next) (root : State) :
    left.BuchiWinning system root ↔ right.BuchiWinning system root := by
  rw [left.buchi_iff_canonical, right.buchi_iff_canonical, sameNext]

theorem MemorylessController.buchi_at_iterate
    {State : Type uState} {Action : Type uAction}
    {system : LabeledSystem State Action}
    {controller : MemorylessController State Action} {root : State}
    (winning : controller.BuchiWinning system root) (offset : Nat) :
    controller.BuchiWinning system (controller.next^[offset] root) := by
  rw [controller.buchi_iff_canonical] at winning ⊢
  intro lowerBound
  obtain ⟨visit, after, accepting⟩ := winning (lowerBound + offset)
  refine ⟨visit - offset, by omega, ?_⟩
  change system.accepting (controller.next^[visit - offset]
    (controller.next^[offset] root)) = true
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  exact accepting

/-- The standard infinite-run meaning: all selected steps are legal and
admitted, and accepting states occur infinitely often from this root. -/
def BuchiControllerClaim.RootMeaning
    {State : Type uState} {Action : Type uAction}
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action) : Prop :=
  (∀ index,
    claim.controller.active (claim.controller.next^[index] claim.root) = true ∧
      system.step (claim.controller.next^[index] claim.root)
        (claim.controller.action (claim.controller.next^[index] claim.root))
        (claim.controller.next (claim.controller.next^[index] claim.root)) = true) ∧
    claim.controller.BuchiWinning system claim.root

/-- On a finite carrier these two functions are finite tables. -/
structure RootBuchiCertificate (State : Type uState) where
  region : State → Bool
  progress : ProgressMeasure State

/-- A proposed invariant can narrow the admitted region but cannot authorize
a state excluded by the original controller. -/
def RootBuchiCertificate.restrict
    {State : Type uState} {Action : Type uAction}
    (certificate : RootBuchiCertificate State)
    (controller : MemorylessController State Action) :
    MemorylessController State Action where
  active state := certificate.region state && controller.active state
  action := controller.action
  next := controller.next

/-- Replay the existing finite progress checker on the proposed subregion. -/
def RootBuchiCertificate.check
    {State : Type uState} {Action : Type uAction} [Fintype State]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action)
    (certificate : RootBuchiCertificate State) : Bool :=
  certificate.progress.check system (certificate.restrict claim.controller)
    claim.root

theorem RootBuchiCertificate.check_sound
    {State : Type uState} {Action : Type uAction} [Fintype State]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    {certificate : RootBuchiCertificate State}
    (accepted : certificate.check system claim = true) :
    claim.RootMeaning system := by
  have valid := (ProgressMeasure.check_eq_true_iff system
    (certificate.restrict claim.controller) certificate.progress claim.root).mp accepted
  have covered : ∀ index,
      (certificate.restrict claim.controller).active
        (claim.controller.next^[index] claim.root) = true := by
    intro index
    induction index with
    | zero => exact valid.1.1
    | succ index inductionHypothesis =>
        rw [Function.iterate_succ_apply']
        exact (valid.1.2 _ inductionHypothesis).2
  constructor
  · intro index
    exact ⟨(Bool.and_eq_true_iff.mp (covered index)).2,
      (valid.1.2 _ (covered index)).1⟩
  · exact (MemorylessController.buchi_congr_next system
      (left := certificate.restrict claim.controller)
      (right := claim.controller) rfl claim.root).mp
      (ProgressMeasure.buchi_sound valid)

private noncomputable def rootRegion
    {State : Type uState} {Action : Type uAction}
    (claim : BuchiControllerClaim State Action) (state : State) : Bool := by
  classical
  exact decide (∃ index, claim.controller.next^[index] claim.root = state)

private theorem rootRegion_eq_true_iff
    {State : Type uState} {Action : Type uAction}
    (claim : BuchiControllerClaim State Action) (state : State) :
    rootRegion claim state = true ↔
      ∃ index, claim.controller.next^[index] claim.root = state := by
  classical
  simp [rootRegion]

/-- Every semantically legal recurrent root has finite region/rank evidence.
The proof uses actual reachability and first acceptance, rather than assuming
that the desired certificate already exists. -/
theorem RootBuchiCertificate.exists_of_meaning
    {State : Type uState} {Action : Type uAction} [Fintype State]
    {system : LabeledSystem State Action}
    {claim : BuchiControllerClaim State Action}
    (meaning : claim.RootMeaning system) :
    ∃ certificate : RootBuchiCertificate State,
      certificate.check system claim = true := by
  let seed : RootBuchiCertificate State :=
    ⟨rootRegion claim, ⟨fun _ => 0⟩⟩
  have localValidity : (seed.restrict claim.controller).LocallyValid system claim.root := by
    constructor
    · change (rootRegion claim claim.root && claim.controller.active claim.root) = true
      apply Bool.and_eq_true_iff.mpr
      exact ⟨(rootRegion_eq_true_iff claim claim.root).mpr ⟨0, rfl⟩, (meaning.1 0).1⟩
    · intro state active
      have reached := (rootRegion_eq_true_iff claim state).mp
        (Bool.and_eq_true_iff.mp active).1
      obtain ⟨index, rfl⟩ := reached
      refine ⟨(meaning.1 index).2, ?_⟩
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply (rootRegion_eq_true_iff claim _).mpr
        exact ⟨index + 1, Function.iterate_succ_apply' _ _ _⟩
      · simpa [RootBuchiCertificate.restrict, Function.iterate_succ_apply']
          using (meaning.1 (index + 1)).1
  have uniform : (seed.restrict claim.controller).UniformBuchiWinning system claim.root := by
    refine ⟨localValidity, ?_⟩
    intro state active
    obtain ⟨index, rfl⟩ := (rootRegion_eq_true_iff claim state).mp
      (Bool.and_eq_true_iff.mp active).1
    apply (MemorylessController.buchi_congr_next system
      (left := seed.restrict claim.controller)
      (right := claim.controller) rfl _).mpr
    exact MemorylessController.buchi_at_iterate meaning.2 index
  obtain ⟨progress, valid⟩ := ProgressMeasure.exists_valid_of_uniformBuchi uniform
  refine ⟨⟨rootRegion claim, progress⟩, ?_⟩
  exact (ProgressMeasure.check_eq_true_iff system
    (seed.restrict claim.controller) progress claim.root).mpr valid

/-- Exact scope is root legality and root recurrence, including controllers
with unrelated bad components elsewhere in their admitted state space. -/
theorem RootBuchiCertificate.exists_iff_meaning
    {State : Type uState} {Action : Type uAction} [Fintype State]
    (system : LabeledSystem State Action)
    (claim : BuchiControllerClaim State Action) :
    (∃ certificate : RootBuchiCertificate State,
      certificate.check system claim = true) ↔ claim.RootMeaning system := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact certificate.check_sound accepted
  · exact RootBuchiCertificate.exists_of_meaning

/-- Standard root recurrence as a named semantic authority. -/
def rootBuchiAuthority
    {AuthorityId : Type uAuthority} {State : Type uState} {Action : Type uAction}
    [Fintype State] (authorityId : AuthorityId)
    (system : LabeledSystem State Action) :
    SemanticAuthority AuthorityId (BuchiControllerClaim State Action) where
  id := authorityId
  Certificate := RootBuchiCertificate State
  check := fun claim certificate => certificate.check system claim
  Meaning := BuchiControllerClaim.RootMeaning system
  sound := RootBuchiCertificate.check_sound

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

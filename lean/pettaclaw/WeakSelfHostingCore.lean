/-!
# WeakSelfHostingCore — a permissive protected-plasticity seed

This model separates two very different operations.

* Ordinary self-programming supplies an arbitrary extension.  The protected
  runner converts its invocation into either a serialized success or failure.
  Every successful boundary is admitted; failure is a stuttering step.
* Replacement of the tiny runner itself is staged separately.  A staged
  candidate cannot affect the live or last-known-good image.  Promotion
  requires an external approval predicate and changes the live and recovery
  images atomically.

The model intentionally knows nothing about channels, tools, memories,
contexts, modes, receipts, duplicate detection, or stuckness.  Those may all
be implemented by freely replaceable extensions.

“Weakest” is relative to the stated root-replacement safety contract.  A gate
is weaker when it admits every promotion admitted by the other gate.  The
canonical gate requires exactly two facts—selection of the staged candidate
and external approval—and is proved to be the weakest sound gate for that
contract.
-/

namespace WeakSelfHostingCore

/-! ## Failure-transactional arbitrary extensions -/

/-- The protected runner observes only a serializable success or failure.
The implementation may obtain this result from an isolated child process. -/
inductive Outcome (Boundary : Type)
  | success (next : Boundary)
  | failure

/-- Commit every successful developmental result, while a failed extension is
a stuttering step.  There is no semantic filter on successful boundaries. -/
def resolve {Boundary : Type} (before : Boundary) : Outcome Boundary → Boundary
  | .success next => next
  | .failure => before

theorem failed_extension_is_transactional {Boundary : Type}
    (before : Boundary) :
    resolve before (.failure : Outcome Boundary) = before := by
  rfl

theorem every_successful_boundary_is_admitted {Boundary : Type}
    (before target : Boundary) :
    resolve before (.success target) = target := by
  rfl

/-- An extension can realize an arbitrary developmental boundary.  This is
the plasticity theorem: the protected runner imposes no catalogue of allowed
changes. -/
def developTo {Boundary : Type} (target : Boundary) :
    Boundary → Outcome Boundary :=
  fun _ => .success target

def hostTransformation {Boundary : Type} (transformation : Boundary → Boundary) :
    Boundary → Outcome Boundary :=
  fun before => .success (transformation before)

theorem arbitrary_development_is_expressible {Boundary : Type}
    (before target : Boundary) :
    resolve before (developTo target before) = target := by
  rfl

/-- Every boundary transformation is hostable without extending the protected
runner.  Feature-specific transformations belong in an adequacy library, not
in this core. -/
theorem every_transformation_is_expressible {Boundary : Type}
    (transformation : Boundary → Boundary) (before : Boundary) :
    resolve before (hostTransformation transformation before) =
      transformation before := by
  rfl

/-! ## Replacement of the protected runner -/

/-- The root supervisor retains one live image, one recovery image, and at
most one staged replacement.  `Program` is opaque: the core neither inspects
nor restricts candidate behavior. -/
structure Host (Program : Type) where
  live : Program
  lastKnownGood : Program
  staged : Option Program

/-- Staging is deliberately unconditional. -/
def stage {Program : Type} (host : Host Program) (candidate : Program) :
    Host Program :=
  { host with staged := some candidate }

/-- Rejecting a candidate clears only the staging slot. -/
def reject {Program : Type} (host : Host Program) : Host Program :=
  { host with staged := none }

/-- Recovery discards the candidate and selects the retained recovery image. -/
def recover {Program : Type} (host : Host Program) : Host Program :=
  { live := host.lastKnownGood
    lastKnownGood := host.lastKnownGood
    staged := none }

theorem arbitrary_candidate_is_stageable {Program : Type}
    (host : Host Program) (candidate : Program) :
    (stage host candidate).staged = some candidate := by
  rfl

/-- Merely writing arbitrary candidate bytes cannot change either executable
image. -/
theorem staging_noninterference {Program : Type}
    (host : Host Program) (candidate : Program) :
    (stage host candidate).live = host.live ∧
      (stage host candidate).lastKnownGood = host.lastKnownGood := by
  exact ⟨rfl, rfl⟩

theorem rejection_preserves_live_and_recovery {Program : Type}
    (host : Host Program) :
    (reject host).live = host.live ∧
      (reject host).lastKnownGood = host.lastKnownGood := by
  exact ⟨rfl, rfl⟩

theorem failed_candidate_trial_is_live_stutter {Program : Type}
    (host : Host Program) (candidate : Program) :
    let next := reject (stage host candidate)
    next.live = host.live ∧ next.lastKnownGood = host.lastKnownGood := by
  exact ⟨rfl, rfl⟩

theorem recovery_selects_last_known_good {Program : Type}
    (host : Host Program) :
    (recover host).live = host.lastKnownGood ∧
      (recover host).lastKnownGood = host.lastKnownGood ∧
      (recover host).staged = none := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## The weakest sound root-promotion gate -/

/-- `Approved` is supplied by an authority outside the candidate.  The core
does not prescribe tests, values, governance, or a capability catalogue. -/
def PromotionSafe {Program : Type} (Approved : Program → Prop)
    (host : Host Program) (candidate : Program) : Prop :=
  host.staged = some candidate ∧ Approved candidate

abbrev Gate (Program : Type) := Host Program → Program → Prop

def Sound {Program : Type} (Approved : Program → Prop)
    (gate : Gate Program) : Prop :=
  ∀ host candidate, gate host candidate →
    PromotionSafe Approved host candidate

/-- `left` is weaker (more permissive) when it admits every transition that
`right` admits. -/
def WeakerThan {Program : Type} (left right : Gate Program) : Prop :=
  ∀ host candidate, right host candidate → left host candidate

def promote {Program : Type} (Approved : Program → Prop)
    (host : Host Program) (candidate : Program)
    (_ : PromotionSafe Approved host candidate) : Host Program :=
  { live := candidate
    lastKnownGood := candidate
    staged := none }

theorem canonical_promotion_gate_is_sound {Program : Type}
    (Approved : Program → Prop) :
    Sound Approved (PromotionSafe Approved) := by
  intro host candidate safe
  exact safe

/-- No sound gate for the same contract can admit a promotion rejected by the
canonical gate.  The canonical gate adds no policy beyond exact staging and
external approval. -/
theorem canonical_promotion_gate_is_weakest_sound {Program : Type}
    (Approved : Program → Prop) (gate : Gate Program)
    (sound : Sound Approved gate) :
    WeakerThan (PromotionSafe Approved) gate := by
  intro host candidate accepted
  exact sound host candidate accepted

/-- Every externally approved program can become live, regardless of its
internal structure. -/
theorem every_approved_candidate_can_become_live {Program : Type}
    (Approved : Program → Prop) (host : Host Program) (candidate : Program)
    (approved : Approved candidate) :
    let staged := stage host candidate
    let next := promote Approved staged candidate ⟨rfl, approved⟩
    next.live = candidate ∧
      next.lastKnownGood = candidate ∧ next.staged = none := by
  exact ⟨rfl, rfl, rfl⟩

/-- Atomic promotion exposes no state in which the new live image and its
recovery image disagree. -/
theorem atomic_promotion_preserves_recoverability {Program : Type}
    (Approved : Program → Prop) (host : Host Program) (candidate : Program)
    (safe : PromotionSafe Approved host candidate) :
    (promote Approved host candidate safe).live =
      (promote Approved host candidate safe).lastKnownGood := by
  rfl

/-! ## Three erasure witnesses -/

/-! ### 1. Erasing the last-known-good coordinate -/

structure SingleImage (Program : Type) where
  live : Option Program

def crashSingle {Program : Type} (_ : SingleImage Program) :
    SingleImage Program :=
  ⟨none⟩

def Alive {Program : Type} (host : SingleImage Program) : Prop :=
  ∃ program, host.live = some program

theorem last_known_good_erasure_permits_death {Program : Type}
    (program : Program) :
    ¬ Alive (crashSingle (SingleImage.mk (some program))) := by
  intro alive
  rcases alive with ⟨candidate, impossible⟩
  cases impossible

/-! ### 2. Erasing external selection -/

/-- The candidate is installed merely because it is present. -/
def unguardedPromote {Program : Type} (_host : Host Program)
    (candidate : Program) : Host Program :=
  { live := candidate
    lastKnownGood := candidate
    staged := none }

theorem external_selection_erasure_accepts_unapproved_candidate
    {Program : Type} (Approved : Program → Prop) (host : Host Program)
    (candidate : Program) (denied : ¬ Approved candidate) :
    let staged := stage host candidate
    (unguardedPromote staged candidate).live = candidate ∧
      ¬ PromotionSafe Approved staged candidate := by
  constructor
  · rfl
  · intro safe
    exact denied safe.2

/-! ### 3. Erasing atomic promotion -/

/-- First half of a non-atomic replacement: the live pointer changes while
the recovery pointer still names the old image. -/
def beginNonAtomicPromotion {Program : Type} (host : Host Program)
    (candidate : Program) : Host Program :=
  { host with live := candidate }

theorem non_atomic_promotion_exposes_torn_state {Program : Type}
    (old candidate : Program) (different : candidate ≠ old) :
    let host : Host Program :=
      { live := old, lastKnownGood := old, staged := some candidate }
    (beginNonAtomicPromotion host candidate).live ≠
      (beginNonAtomicPromotion host candidate).lastKnownGood := by
  exact different

end WeakSelfHostingCore

/-! ## Axiom audit -/

#print axioms WeakSelfHostingCore.failed_extension_is_transactional
#print axioms WeakSelfHostingCore.arbitrary_development_is_expressible
#print axioms WeakSelfHostingCore.staging_noninterference
#print axioms WeakSelfHostingCore.failed_candidate_trial_is_live_stutter
#print axioms WeakSelfHostingCore.recovery_selects_last_known_good
#print axioms WeakSelfHostingCore.canonical_promotion_gate_is_weakest_sound
#print axioms WeakSelfHostingCore.every_approved_candidate_can_become_live
#print axioms WeakSelfHostingCore.last_known_good_erasure_permits_death
#print axioms WeakSelfHostingCore.external_selection_erasure_accepts_unapproved_candidate
#print axioms WeakSelfHostingCore.non_atomic_promotion_exposes_torn_state

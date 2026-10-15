import Mettapedia.GSLT.Core.StepFree
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Distinction.Probabilistic.Semiring
import Mettapedia.GSLT.Dynamics.JoinAggregation
import Mettapedia.Logic.HostingStyles.ProofNodes

/-!
# Weight preservation is a fibre sum

A translation may send one source event to several target matches. Hosting
says that no distinction of the source is lost. It does not say that weights
are kept.

`WeightedSystem` is the weighted transition system already in the tree. The
new notion is a map between two of them. Weights live in a commutative
semiring. The map is weight-preserving when each source event's weight equals
`groupSum` of the target weights on its fibre. Duplicating every match `k`
times multiplies that sum by `k`.

Each event has `k` derivations. One term sends every derivation to itself,
and that function is the term at both existing congruences. The fibre of an
event is the image of its derivations under that term. For `k = 1` the fibre
keeps the source weight. For `k > 1` the fibre sum is `k` times the source
weight, so the map is hosting and is not weight-preserving. Those hosting
facts do not determine `k`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.Dynamics.JoinAggregation
open Mettapedia.GSLT.GradedSupport
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Logic.HostingStyles
open Mettapedia.Logic.HostingStyles.RuleSignature

/-! ## The two systems -/

/-- Outcomes and a silent start, with no rewrite. -/
def quiet : GSLT :=
  GSLT.stepFree (Option Bool)

/-- One source event, copied once for each index below `k`. -/
def fanSpace (k : ℕ) : GSLT :=
  GSLT.stepFree (Option (Bool × Fin k))

theorem quiet_refl (term : quiet.Term) : quiet.Equiv term term := rfl

theorem quiet_no_step (left right : quiet.Term) : ¬ quiet.Step left right :=
  fun step => step

/-- Coefficient of a source outcome. The start carries none. -/
def outcomeCoeff {K : Type*} [Zero K] (w : K) : Option Bool → K
  | none => 0
  | some _ => w

/-- The source step: both outcomes carry `w`, and nothing else does. -/
noncomputable def outcomeKernel {K : Type*} [AddCommMonoid K] (w : K) : Option Bool →₀ K :=
  Finsupp.onFinset {some true, some false} (outcomeCoeff w) fun term nonzero => by
    cases term with
    | none => exact absurd rfl nonzero
    | some b =>
      cases b
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact Finset.mem_insert_self _ _

theorem outcomeKernel_some {K : Type*} [AddCommMonoid K] (w : K) (b : Bool) :
    outcomeKernel w (some b) = w := by
  unfold outcomeKernel
  rw [Finsupp.onFinset_apply]
  rfl

/-- Coefficient of one copied match. -/
def fanCoeff {K : Type*} [Zero K] {k : ℕ} (w : K) : Option (Bool × Fin k) → K
  | none => 0
  | some _ => w

/-- The target step: each of the `k` copies of each outcome carries `w`. -/
noncomputable def fanKernel {K : Type*} [AddCommMonoid K] (k : ℕ) (w : K) :
    Option (Bool × Fin k) →₀ K :=
  Finsupp.onFinset (Finset.univ.map ⟨some, Option.some_injective _⟩) (fanCoeff w)
    fun term nonzero => by
      cases term with
      | none => exact absurd rfl nonzero
      | some p => exact Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩

theorem fanKernel_some {K : Type*} [AddCommMonoid K] (k : ℕ) (w : K) (p : Bool × Fin k) :
    fanKernel k w (some p) = w := by
  unfold fanKernel
  rw [Finsupp.onFinset_apply]
  rfl

noncomputable def outcomeStep {K : Type*} [AddCommMonoid K] (w : K) :
    Option Bool → Option Bool →₀ K
  | none => outcomeKernel w
  | some _ => 0

noncomputable def fanStep {K : Type*} [AddCommMonoid K] (k : ℕ) (w : K) :
    Option (Bool × Fin k) → Option (Bool × Fin k) →₀ K
  | none => fanKernel k w
  | some _ => 0

/-- The source weighted system, weight `w` on each outcome. -/
noncomputable def outcomeSystem {K : Type*} [CommSemiring K] (w : K) : WeightedSystem quiet K where
  Atom := Bool
  observes atom term := term = some atom
  observes_resp := by
    intro _ _ _ same
    cases same
    rfl
  Label := Unit
  kernel := fun _ => outcomeStep w
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

/-- The target weighted system, weight `w` on each of the `k` copies. -/
noncomputable def fanSystem {K : Type*} [CommSemiring K] (k : ℕ) (w : K) :
    WeightedSystem (fanSpace k) K where
  Atom := Bool
  observes atom term := ∃ index : Fin k, term = some (atom, index)
  observes_resp := by
    intro _ _ _ same
    cases same
    rfl
  Label := Unit
  kernel := fun _ => fanStep k w
  kernel_resp := by
    intro _ _ _ same _ _
    cases same
    rfl

theorem outcomeSystem_coeff {K : Type*} [CommSemiring K] (w : K) (b : Bool) :
    (outcomeSystem w).kernel () none (some b) = w := by
  show outcomeStep w none (some b) = w
  rw [outcomeStep, outcomeKernel_some]

theorem fanSystem_coeff {K : Type*} [CommSemiring K] (k : ℕ) (w : K) (p : Bool × Fin k) :
    (fanSystem k w).kernel () none (some p) = w := by
  show fanStep k w none (some p) = w
  rw [fanStep, fanKernel_some]

/-! ## Fibres -/

/-- Both outcomes, each copied `k` times. -/
def bothCopies (k : ℕ) : List (Bool × Fin k) :=
  (List.ofFn fun i => (true, i)) ++ (List.ofFn fun i => (false, i))

theorem groupSum_append {α Y K : Type*} [DecidableEq Y] [AddCommMonoid K]
    (key : α → Y) (weight : α → K) (left right : List α) (y : Y) :
    groupSum key weight (left ++ right) y =
      groupSum key weight left y + groupSum key weight right y := by
  simp [groupSum, List.filter_append, List.map_append, List.sum_append]

theorem groupSum_one_copy {K : Type*} [CommSemiring K] (k : ℕ) (w : K) (b : Bool) :
    groupSum (fun p : Bool × Fin k => p.1) (fun _ => w)
      (List.ofFn fun i : Fin k => (b, i)) b = (k : K) * w := by
  unfold groupSum
  have filtered :
      List.filter (fun p : Bool × Fin k => p.1 = b) (List.ofFn fun i => (b, i)) =
        List.ofFn fun i => (b, i) := by
    refine List.filter_eq_self.mpr ?_
    intro p member
    obtain ⟨_, rfl⟩ := List.mem_ofFn.mp member
    exact decide_eq_true rfl
  rw [filtered]
  have mapped :
      (List.ofFn fun i : Fin k => (b, i)).map (fun _ => w) = List.ofFn fun _ : Fin k => w := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem groupSum_mismatch {K : Type*} [CommSemiring K] (k : ℕ) (w : K) {left right : Bool}
    (distinct : left ≠ right) :
    groupSum (fun p : Bool × Fin k => p.1) (fun _ => w)
      (List.ofFn fun i : Fin k => (right, i)) left = 0 := by
  refine groupSum_eq_zero _ ?_
  intro p member
  obtain ⟨_, rfl⟩ := List.mem_ofFn.mp member
  exact distinct.symm

/-- Each source event owns `k` target matches, and the fibre sum is `k * w`. -/
theorem fibre_sum_mul {K : Type*} [CommSemiring K] (k : ℕ) (w : K) (b : Bool) :
    groupSum (fun p : Bool × Fin k => p.1) (fun _ => w) (bothCopies k) b = (k : K) * w := by
  cases b with
  | false =>
    rw [bothCopies, groupSum_append,
      groupSum_mismatch k w (left := false) (right := true) (by decide), zero_add,
      groupSum_one_copy]
  | true =>
    rw [bothCopies, groupSum_append, groupSum_one_copy,
      groupSum_mismatch k w (left := true) (right := false) (by decide), add_zero]

theorem fibre_sum_of_kernel {K : Type*} [CommSemiring K] (k : ℕ) (w : K) (b : Bool) :
    groupSum (fun p : Bool × Fin k => p.1)
      (fun p => (fanSystem k w).kernel () none (some p)) (bothCopies k) b =
        (k : K) * (outcomeSystem w).kernel () none (some b) := by
  have weights :
      (fun p : Bool × Fin k => (fanSystem k w).kernel () none (some p)) = fun _ => w := by
    funext p
    exact fanSystem_coeff k w p
  rw [weights, fibre_sum_mul, outcomeSystem_coeff]

theorem each_event_has_k_matches (k : ℕ) (b : Bool) :
    (bothCopies k).countP (fun p => p.1 = b) = k := by
  have counted :=
    groupSum_one (K := ℕ) (fun p : Bool × Fin k => p.1) (bothCopies k) b
  rw [fibre_sum_mul] at counted
  have : ((bothCopies k).countP fun p => p.1 = b) = k * 1 := by
    exact counted.symm
  simpa using this

/-! ## Weight preservation -/

/-- A map between two weighted transition systems sends target matches to the
source event they witness. `Event` and `Copy` are parameters so a fibre over
`Bool` is `Bool` before instance search. -/
structure WeightedTranslation (K : Type) [CommSemiring K] (Event Copy : Type) where
  sourceSpace : GSLT.{0}
  targetSpace : GSLT.{0}
  source : WeightedSystem.{0, 0, 0, 0} sourceSpace K
  target : WeightedSystem.{0, 0, 0, 0} targetSpace K
  key : Copy → Event
  copies : List Copy
  sourceWeight : Event → K
  targetWeight : Copy → K

/-- **Weight-preserving**: the weight of each source event is the sum of the
weights of the target events in its fibre. -/
def weightPreserving {K Event Copy : Type*} [CommSemiring K] [DecidableEq Event]
    (sourceWeight : Event → K) (key : Copy → Event) (targetWeight : Copy → K)
    (copies : List Copy) : Prop :=
  ∀ event, sourceWeight event = groupSum key targetWeight copies event

/-- The duplication translation read off the two kernels. -/
noncomputable def duplication (k : ℕ) (w : ℕ) :
    WeightedTranslation ℕ Bool (Bool × Fin k) where
  sourceSpace := quiet
  targetSpace := fanSpace k
  source := outcomeSystem w
  target := fanSystem k w
  key := Prod.fst
  copies := bothCopies k
  sourceWeight := fun b => (outcomeSystem w).kernel () none (some b)
  targetWeight := fun p => (fanSystem k w).kernel () none (some p)

/-- **Positive.** One match per event keeps the kernel weight. -/
theorem duplication_one_weightPreserving (w : ℕ) :
    weightPreserving (duplication 1 w).sourceWeight (duplication 1 w).key
      (duplication 1 w).targetWeight (duplication 1 w).copies := by
  intro b
  unfold duplication
  rw [fibre_sum_of_kernel, outcomeSystem_coeff]
  exact (Nat.one_mul w).symm

theorem duplication_source_coeff (k : ℕ) (b : Bool) :
    (duplication k 1).sourceWeight b = 1 := by
  show (outcomeSystem (1 : ℕ)).kernel () none (some b) = 1
  exact outcomeSystem_coeff 1 b

theorem duplication_two_fibre (b : Bool) :
    groupSum (duplication 2 1).key (duplication 2 1).targetWeight
      (duplication 2 1).copies b = 2 := by
  show groupSum (fun p : Bool × Fin 2 => p.1)
      (fun p => (fanSystem 2 (1 : ℕ)).kernel () none (some p)) (bothCopies 2) b = 2
  rw [fibre_sum_of_kernel, outcomeSystem_coeff]
  simp

/-- **Negative.** Two matches per event do not keep the kernel weight. -/
theorem duplication_two_not_weightPreserving :
    ¬ weightPreserving (duplication 2 1).sourceWeight (duplication 2 1).key
        (duplication 2 1).targetWeight (duplication 2 1).copies := by
  intro preserves
  have doubled := preserves true
  rw [duplication_source_coeff, duplication_two_fibre] at doubled
  exact absurd doubled (by decide)

/-- The duplicated fibre is a real extra weight: `k` and `w` nonzero cannot cancel. -/
theorem duplicated_weight_nonzero (b : Bool) :
    groupSum (fun p : Bool × Fin 2 => p.1)
      (fun p => (fanSystem 2 (1 : ℕ)).kernel () none (some p)) (bothCopies 2) b ≠ 0 := by
  rw [fibre_sum_of_kernel, outcomeSystem_coeff]
  intro zero
  rcases nat_noCancellation.mul_eq_zero _ _ zero with hk | hw
  · cases hk
  · cases hw

/-! ## One term, k derivations of each event -/

/-- The judgment whose axioms are the matches `(event, index)`. -/
def matchSignature (k : ℕ) : RuleSignature Unit where
  Shape := fun _ _ => Bool × Fin k
  Position := fun _ => Empty
  next := fun _ position => position.elim

/-- The derivation that is one match. -/
def matchProof (k : ℕ) (copy : Bool × Fin k) : (matchSignature k).Proof () :=
  (matchSignature k).node copy fun position => position.elim

/-- **Positive.** Distinct events stay distinct as derivations. -/
theorem matchProof_distinguishes_events (k : ℕ) (hk : 0 < k) :
    matchProof k (true, ⟨0, hk⟩) ≠ matchProof k (false, ⟨0, hk⟩) := by
  intro same
  have root (copy : Bool × Fin k) :
      (matchSignature k).rootShape (matchProof k copy) = copy := by
    unfold matchProof
    rfl
  have shapes := congrArg (matchSignature k).rootShape same
  rw [root, root] at shapes
  have bools : true = false := congrArg Prod.fst shapes
  cases bools

/-- **Negative.** Two indices of one event are two derivations. -/
theorem matchProof_distinguishes_matches (b : Bool) :
    matchProof 2 (b, 0) ≠ matchProof 2 (b, 1) := by
  intro same
  have root (copy : Bool × Fin 2) :
      (matchSignature 2).rootShape (matchProof 2 copy) = copy := by
    unfold matchProof
    rfl
  have shapes := congrArg (matchSignature 2).rootShape same
  rw [root, root] at shapes
  have indices : (0 : ℕ) = 1 := congrArg Fin.val (congrArg Prod.snd shapes)
  cases indices

/-- The one term at both congruences: a derivation is sent to itself. -/
def carryMatch {k : ℕ} {j : Unit} (proof : (matchSignature k).Proof j) :
    (matchSignature k).Proof j :=
  proof

/-- **Positive.** The term keeps the event of a match. -/
theorem carry_event (k : ℕ) (copy : Bool × Fin k) :
    ((matchSignature k).rootShape (carryMatch (matchProof k copy))).1 = copy.1 := by
  unfold carryMatch matchProof
  rfl

/-- **Negative.** The term does not identify two indices of one event. -/
theorem carry_keeps_matches_apart (b : Bool) :
    carryMatch (matchProof 2 (b, 0)) ≠ carryMatch (matchProof 2 (b, 1)) := by
  intro same
  exact matchProof_distinguishes_matches b same

/-- The event named by a carried derivation. -/
def matchEvent (k : ℕ) (proof : (matchSignature k).Proof ()) : Bool :=
  ((matchSignature k).rootShape proof).1

theorem matchEvent_carry (k : ℕ) (copy : Bool × Fin k) :
    matchEvent k (carryMatch (matchProof k copy)) = copy.1 := by
  unfold matchEvent
  exact carry_event k copy

/-- The `k` derivations of one event. -/
def eventDerivations (k : ℕ) (b : Bool) : List ((matchSignature k).Proof ()) :=
  List.ofFn fun i : Fin k => matchProof k (b, i)

/-- The fibre of an event: the image of its derivations under the one term. -/
def eventFibre (k : ℕ) (b : Bool) : List ((matchSignature k).Proof ()) :=
  (eventDerivations k b).map carryMatch

/-- Every derivation, event by event. -/
def allDerivations (k : ℕ) : List ((matchSignature k).Proof ()) :=
  eventDerivations k true ++ eventDerivations k false

/-- The copy list of the translation: the image of every derivation. -/
def matchFibre (k : ℕ) : List ((matchSignature k).Proof ()) :=
  allDerivations k |>.map carryMatch

theorem eventFibre_length (k : ℕ) (b : Bool) : (eventFibre k b).length = k := by
  unfold eventFibre eventDerivations
  rw [List.length_map, List.length_ofFn]

theorem groupSum_eventFibre (k : ℕ) (b : Bool) :
    groupSum (matchEvent k) (fun _ => (1 : ℕ)) (eventFibre k b) b = k := by
  unfold eventFibre eventDerivations groupSum
  have mapped :
      ((List.ofFn fun i : Fin k => matchProof k (b, i)).map carryMatch) =
        List.ofFn fun i : Fin k => carryMatch (matchProof k (b, i)) := by
    rw [List.map_ofFn]
    rfl
  rw [mapped]
  have filtered :
      List.filter (fun proof => matchEvent k proof = b)
          (List.ofFn fun i : Fin k => carryMatch (matchProof k (b, i))) =
        List.ofFn fun i => carryMatch (matchProof k (b, i)) := by
    refine List.filter_eq_self.mpr ?_
    intro proof member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    rw [matchEvent_carry]
    exact decide_eq_true rfl
  rw [filtered]
  have weights :
      (List.ofFn fun i : Fin k => carryMatch (matchProof k (b, i))).map (fun _ => (1 : ℕ)) =
        List.ofFn fun _ : Fin k => (1 : ℕ) := by
    rw [List.map_ofFn]
    rfl
  rw [weights, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.mul_one]
  exact Nat.cast_id k

theorem groupSum_eventFibre_other (k : ℕ) {left right : Bool} (distinct : left ≠ right) :
    groupSum (matchEvent k) (fun _ => (1 : ℕ)) (eventFibre k right) left = 0 := by
  refine groupSum_eq_zero _ ?_
  intro proof member
  unfold eventFibre eventDerivations at member
  rw [List.mem_map] at member
  obtain ⟨_raw, rawMember, rfl⟩ := member
  rw [List.mem_ofFn] at rawMember
  obtain ⟨_i, rfl⟩ := rawMember
  rw [matchEvent_carry]
  exact distinct.symm

theorem matchFibre_append (k : ℕ) :
    matchFibre k = eventFibre k true ++ eventFibre k false := by
  unfold matchFibre allDerivations eventFibre
  rw [List.map_append]

theorem groupSum_matchFibre (k : ℕ) (b : Bool) :
    groupSum (matchEvent k) (fun _ => (1 : ℕ)) (matchFibre k) b = k := by
  cases b with
  | true =>
    rw [matchFibre_append, groupSum_append, groupSum_eventFibre,
      groupSum_eventFibre_other k (by decide : (true : Bool) ≠ false), add_zero]
  | false =>
    rw [matchFibre_append, groupSum_append,
      groupSum_eventFibre_other k (by decide : (false : Bool) ≠ true), zero_add,
      groupSum_eventFibre]

/-- The term, read where derivations are kept apart. -/
noncomputable def matchIdentity (k : ℕ) :
    ContextMap
      ((matchSignature k).proofTheory (ProofCongruence.identity (matchSignature k)))
      ((matchSignature k).proofTheory (ProofCongruence.identity (matchSignature k))) where
  interface := fun j => j
  term := fun proof => carryMatch proof
  context := fun context => context
  term_resp := by
    intro _ first second related
    cases related
    rfl
  equivariant := fun _ _ => rfl

/-- The same term, read where only provability is kept. -/
noncomputable def matchTotal (k : ℕ) :
    ContextMap
      ((matchSignature k).proofTheory (ProofCongruence.total (matchSignature k)))
      ((matchSignature k).proofTheory (ProofCongruence.total (matchSignature k))) where
  interface := fun j => j
  term := fun proof => carryMatch proof
  context := fun context => context
  term_resp := fun _ => trivial
  equivariant := fun _ _ => trivial

theorem matchIdentity_hosting (k : ℕ) : (matchIdentity k).Hosting := by
  rw [(matchSignature k).hosting_iff_static (ProofCongruence.identity (matchSignature k))
    (matchIdentity k) (fun _ _ step => step)]
  intro _ first second images
  unfold matchIdentity carryMatch at images
  exact images

theorem matchTotal_hosting (k : ℕ) : (matchTotal k).Hosting := by
  rw [(matchSignature k).hosting_iff_static (ProofCongruence.total (matchSignature k))
    (matchTotal k) (fun _ _ step => step)]
  intro _ _ _ _
  exact trivial

/-- **Positive.** One derivation per event: the image fibre keeps the weight. -/
theorem one_derivation_keeps_weight :
    (matchIdentity 1).Hosting ∧
      (matchTotal 1).Hosting ∧
      (∀ b, eventFibre 1 b =
        (eventDerivations 1 b).map (fun proof => (matchIdentity 1).term proof)) ∧
      (∀ b, (eventFibre 1 b).length = 1) ∧
      weightPreserving (fun _ : Bool => (1 : ℕ)) (matchEvent 1) (fun _ => (1 : ℕ))
        (matchFibre 1) := by
  refine ⟨matchIdentity_hosting 1, matchTotal_hosting 1, ?_, ?_, ?_⟩
  · intro b
    unfold eventFibre matchIdentity carryMatch
    rfl
  · intro b
    exact eventFibre_length 1 b
  · intro b
    rw [groupSum_matchFibre]

/-- **The gap.** One term is hosting at both levels. Its image list is the
fibre: each event contributes `k` matches, the group sum is `k` times the
source weight, and that list is not weight-preserving. -/
theorem hosting_fibre_multiplies_weight (k : ℕ) (hk : 1 < k) :
    (matchIdentity k).Hosting ∧
      (matchTotal k).Hosting ∧
      (∀ b, eventFibre k b =
        (eventDerivations k b).map (fun proof => (matchIdentity k).term proof)) ∧
      (∀ b, eventFibre k b =
        (eventDerivations k b).map (fun proof => (matchTotal k).term proof)) ∧
      matchFibre k =
        (allDerivations k).map (fun proof => (matchIdentity k).term proof) ∧
      (∀ b, (eventFibre k b).length = k) ∧
      (∀ b, groupSum (matchEvent k) (fun _ => (1 : ℕ)) (matchFibre k) b =
        k * (fun _ : Bool => (1 : ℕ)) b) ∧
      ¬ weightPreserving (fun _ : Bool => (1 : ℕ)) (matchEvent k) (fun _ => (1 : ℕ))
          (matchFibre k) := by
  refine ⟨matchIdentity_hosting k, matchTotal_hosting k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    unfold eventFibre matchIdentity carryMatch
    rfl
  · intro b
    unfold eventFibre matchTotal carryMatch
    rfl
  · unfold matchFibre matchIdentity carryMatch
    rfl
  · intro b
    exact eventFibre_length k b
  · intro b
    exact (groupSum_matchFibre k b).trans (Nat.mul_one k).symm
  · intro keeps
    have summed := keeps true
    rw [groupSum_matchFibre] at summed
    exact absurd summed (Nat.ne_of_lt hk)

/-- **Positive.** The fibre sum determines the multiplicity. -/
theorem fibre_sum_recovers_factor :
    Factors (fun k : ℕ =>
      groupSum (matchEvent k) (fun _ => (1 : ℕ)) (matchFibre k) true) (fun k : ℕ => k) :=
  ⟨id, fun k => groupSum_matchFibre k true⟩

/-- **Negative.** Hosting at the two levels does not determine the multiplicity.
The fibre sum does, by `fibre_sum_recovers_factor`. -/
theorem hosting_does_not_detect_factor :
    ¬ Factors (fun k : ℕ => (matchIdentity k).Hosting ∧ (matchTotal k).Hosting)
        (fun k : ℕ => k) :=
  NonTrivialFiber.not_factors
    { left := 1
      right := 2
      sameShadow := propext ⟨
        fun _ => ⟨matchIdentity_hosting 2, matchTotal_hosting 2⟩,
        fun _ => ⟨matchIdentity_hosting 1, matchTotal_hosting 1⟩⟩
      differentValue := by decide }

/-- Provability identifies two derivations of one event, so it does not refine
the congruence that keeps derivations apart. Coarsening along that refinement
is therefore not hosting. -/
theorem provability_does_not_refine_matches :
    ¬ (ProofCongruence.total (matchSignature 2)).Refines
        (ProofCongruence.identity (matchSignature 2)) := by
  intro back
  have hosting :=
    ((matchSignature 2).coarsen_hosting_iff
      (ProofCongruence.refines_total (ProofCongruence.identity (matchSignature 2)))).mpr back
  exact ContextMap.not_hosting_of_identifies
    ((matchSignature 2).coarsen
      (ProofCongruence.refines_total (ProofCongruence.identity (matchSignature 2))))
    (matchProof_distinguishes_matches true) trivial hosting

end Mettapedia.Logic.HostingStyles.Weighted

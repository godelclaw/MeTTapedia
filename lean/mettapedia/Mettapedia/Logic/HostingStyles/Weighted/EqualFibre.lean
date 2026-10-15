import Mettapedia.Logic.HostingStyles.Weighted.CountEvidence
import Mettapedia.Logic.HostingStyles.Weighted.OccurrenceLevel
import Mettapedia.Logic.HostingStyles.Weighted.SupportHosting
import Mettapedia.Logic.HostingStyles.Weighted.TwoBody

/-!
# Equal fibres, and a candidate that hosts weighted theories

When every match in a read-back fibre carries the same weight, that common
weight preserves the source row exactly when it is the quotient supplied by
`Splits` and an event with no match carries weight zero. A fibre of two or
more matches still has a preserving assignment whose weights are not equal.
A candidate hosts a weighted theory when some map into it is hosting on
supports and preserves closed sums. Doubling every natural weight keeps the
support steps and preserves no closed sum.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Classical
open Mettapedia.GSLT
open Mettapedia.GSLT.Distinction.Probabilistic
open Mettapedia.GSLT.Dynamics.JoinAggregation
open Mettapedia.GSLT.GradedSupport
open Mettapedia.Logic.HostingStyles.RuleSignature

/-! ## Equal weights on a fibre -/

/-- Every two matches of one event carry the same weight. -/
def UniformFibre {Event Copy : Type*} [DecidableEq Event] {K : Type*}
    (key : Copy → Event) (weight : Copy → K) (copies : List Copy) : Prop :=
  ∀ ⦃left right : Copy⦄, left ∈ copies → right ∈ copies →
    key left = key right → weight left = weight right

/-- **Positive.** One weight on every copy is uniform. -/
theorem constant_uniformFibre {Event Copy : Type*} [DecidableEq Event] {K : Type*}
    (key : Copy → Event) (copies : List Copy) (weight : K) :
    UniformFibre key (fun _ : Copy => weight) copies :=
  fun _ _ _ _ _ => rfl

/-- Put the whole source weight on the first match of each event, and zero
on every later match. -/
def tilt {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy] {K : Type*}
    [CommSemiring K] (key : Copy → Event) (copies : List Copy) (sourceWeight : Event → K)
    (copy : Copy) : K :=
  if copies.find? (fun other => key other = key copy) = some copy then sourceWeight (key copy)
  else 0

theorem countP_cons_match {Event Copy : Type*} [DecidableEq Event] (key : Copy → Event)
    (head : Copy) (tail : List Copy) (event : Event) (hit : key head = event) :
    (head :: tail).countP (fun copy => key copy = event) =
      tail.countP (fun copy => key copy = event) + 1 :=
  List.countP_cons_of_pos (p := fun copy => decide (key copy = event)) (decide_eq_true hit)

theorem countP_cons_miss {Event Copy : Type*} [DecidableEq Event] (key : Copy → Event)
    (head : Copy) (tail : List Copy) (event : Event) (miss : key head ≠ event) :
    (head :: tail).countP (fun copy => key copy = event) =
      tail.countP (fun copy => key copy = event) :=
  List.countP_cons_of_neg (p := fun copy => decide (key copy = event))
    (by simpa [decide_eq_true_iff] using miss)

theorem find_cons_match {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    (key : Copy → Event) (head copy : Copy) (tail : List Copy) (hit : key head = key copy) :
    (head :: tail).find? (fun other => key other = key copy) = some head :=
  List.find?_cons_of_pos (p := fun other => decide (key other = key copy)) (decide_eq_true hit)

theorem find_cons_miss {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    (key : Copy → Event) (head copy : Copy) (tail : List Copy) (miss : key head ≠ key copy) :
    (head :: tail).find? (fun other => key other = key copy) =
      tail.find? (fun other => key other = key copy) :=
  List.find?_cons_of_neg (p := fun other => decide (key other = key copy))
    (by simpa [decide_eq_true_iff] using miss)

theorem find_cons_match_event {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    (key : Copy → Event) (head : Copy) (tail : List Copy) (event : Event)
    (hit : key head = event) :
    (head :: tail).find? (fun copy => key copy = event) = some head :=
  List.find?_cons_of_pos (p := fun copy => decide (key copy = event)) (decide_eq_true hit)

theorem find_cons_miss_event {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    (key : Copy → Event) (head : Copy) (tail : List Copy) (event : Event)
    (miss : key head ≠ event) :
    (head :: tail).find? (fun copy => key copy = event) =
      tail.find? (fun copy => key copy = event) :=
  List.find?_cons_of_neg (p := fun copy => decide (key copy = event))
    (by simpa [decide_eq_true_iff] using miss)

theorem groupSum_of_zero_weights {Event Copy : Type*} [DecidableEq Event] {K : Type*}
    [AddCommMonoid K] (key : Copy → Event) (weight : Copy → K) (copies : List Copy)
    (event : Event) (zero : ∀ copy ∈ copies, key copy = event → weight copy = 0) :
    groupSum key weight copies event = 0 := by
  induction copies with
  | nil => simp [groupSum]
  | cons head tail tailSum =>
      rw [groupSum_cons]
      by_cases hit : key head = event
      · rw [if_pos hit, zero head ((List.mem_cons_self : head ∈ head :: tail)) hit, zero_add]
        exact tailSum fun copy member keyEq =>
          zero copy (List.mem_cons_of_mem head member) keyEq
      · rw [if_neg hit, zero_add]
        exact tailSum fun copy member keyEq =>
          zero copy (List.mem_cons_of_mem head member) keyEq

theorem groupSum_of_constant_fibre {Event Copy : Type*} [DecidableEq Event] {K : Type*}
    [CommSemiring K] (key : Copy → Event) (weight : Copy → K) (copies : List Copy)
    (event : Event) (common : K)
    (same : ∀ copy ∈ copies, key copy = event → weight copy = common) :
    groupSum key weight copies event =
      (copies.countP (fun copy => key copy = event) : K) * common := by
  induction copies with
  | nil => simp [groupSum]
  | cons head tail tailSum =>
      rw [groupSum_cons]
      have tailSame : ∀ copy ∈ tail, key copy = event → weight copy = common :=
        fun copy member keyEq => same copy (List.mem_cons_of_mem head member) keyEq
      by_cases hit : key head = event
      · have headWeight : weight head = common := same head ((List.mem_cons_self : head ∈ head :: tail)) hit
        rw [if_pos hit, headWeight, tailSum tailSame, countP_cons_match key head tail event hit,
          Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
      · rw [if_neg hit, zero_add, tailSum tailSame, countP_cons_miss key head tail event hit]

theorem tilt_find_head {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    {K : Type*} [CommSemiring K] (key : Copy → Event) (head : Copy) (tail : List Copy)
    (sourceWeight : Event → K) :
    tilt key (head :: tail) sourceWeight head = sourceWeight (key head) := by
  rw [tilt, find_cons_match key head head tail rfl, if_pos rfl]

theorem tilt_skip_head {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    {K : Type*} [CommSemiring K] (key : Copy → Event) (head : Copy) (tail : List Copy)
    (sourceWeight : Event → K) (copy : Copy) (different : key head ≠ key copy) :
    tilt key (head :: tail) sourceWeight copy = tilt key tail sourceWeight copy := by
  rw [tilt, tilt, find_cons_miss key head copy tail different]

theorem groupSum_congr_on_fibre {Event Copy : Type*} [DecidableEq Event] {K : Type*}
    [AddCommMonoid K] (key : Copy → Event) (first second : Copy → K) (copies : List Copy)
    (event : Event)
    (agree : ∀ copy ∈ copies, key copy = event → first copy = second copy) :
    groupSum key first copies event = groupSum key second copies event := by
  induction copies with
  | nil => simp [groupSum]
  | cons head tail tailSum =>
      rw [groupSum_cons, groupSum_cons]
      by_cases hit : key head = event
      · rw [if_pos hit, if_pos hit, agree head ((List.mem_cons_self : head ∈ head :: tail)) hit]
        exact congrArg (fun value => second head + value)
          (tailSum fun copy member keyEq =>
            agree copy (List.mem_cons_of_mem head member) keyEq)
      · rw [if_neg hit, if_neg hit, zero_add, zero_add]
        exact tailSum fun copy member keyEq =>
          agree copy (List.mem_cons_of_mem head member) keyEq

theorem groupSum_tilt {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    {K : Type*} [CommSemiring K] (key : Copy → Event) (copies : List Copy)
    (sourceWeight : Event → K) (event : Event) (nodup : copies.Nodup) :
    groupSum key (tilt key copies sourceWeight) copies event =
      if copies.countP (fun copy => key copy = event) = 0 then 0 else sourceWeight event := by
  induction copies with
  | nil => simp [groupSum]
  | cons head tail tailSum =>
      rw [groupSum_cons]
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      by_cases hit : key head = event
      · rw [if_pos hit, tilt_find_head, hit]
        have laterZero :
            groupSum key (tilt key (head :: tail) sourceWeight) tail event = 0 := by
          apply groupSum_of_zero_weights
          intro copy member keyEq
          have distinct : copy ≠ head := by
            intro same
            exact (List.nodup_cons.mp nodup).1 (same ▸ member)
          have keyHead : key head = key copy := hit.trans keyEq.symm
          rw [tilt, find_cons_match key head copy tail keyHead]
          exact if_neg fun same => distinct (Option.some_injective Copy same).symm
        rw [laterZero, add_zero, countP_cons_match key head tail event hit,
          if_neg (Nat.succ_ne_zero _)]
      · rw [if_neg hit, zero_add]
        have agree :
            groupSum key (tilt key (head :: tail) sourceWeight) tail event =
              groupSum key (tilt key tail sourceWeight) tail event :=
          groupSum_congr_on_fibre key _ _ tail event fun copy _member keyEq =>
            tilt_skip_head key head tail sourceWeight copy fun same => hit (same.trans keyEq)
        rw [agree, tailSum tailNodup, countP_cons_miss key head tail event hit]

/-- **The correction preserves.** Least hypotheses: the match list has no
duplicate value, and an event of nonzero weight has a match. One match may
carry the whole weight, so the weights may still be equal. -/
theorem tilt_preserves {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) (key : Copy → Event)
    (copies : List Copy) (nodup : copies.Nodup)
    (covered : ∀ event, sourceWeight event ≠ 0 →
      copies.countP (fun copy => key copy = event) ≠ 0) :
    weightPreserving sourceWeight key (tilt key copies sourceWeight) copies := by
  intro event
  rw [groupSum_tilt key copies sourceWeight event nodup]
  by_cases empty : copies.countP (fun copy => key copy = event) = 0
  · have zeroWeight : sourceWeight event = 0 := by
      by_contra nonzero
      exact covered event nonzero empty
    simp [empty, zeroWeight]
  · simp [empty]

theorem exists_two_matches {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    (key : Copy → Event) (copies : List Copy) (event : Event) (nodup : copies.Nodup)
    (wide : 2 ≤ copies.countP (fun copy => key copy = event)) :
    ∃ first second : Copy, first ∈ copies ∧ second ∈ copies ∧ first ≠ second ∧
      key first = event ∧ key second = event ∧
      copies.find? (fun copy => key copy = event) = some first := by
  induction copies with
  | nil =>
      simp at wide
  | cons head tail tailMatches =>
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      by_cases hit : key head = event
      · have findHead :
            (head :: tail).find? (fun copy => key copy = event) = some head :=
          find_cons_match_event key head tail event hit
        have tailWide : 1 ≤ tail.countP (fun copy => key copy = event) := by
          rw [countP_cons_match key head tail event hit] at wide
          omega
        obtain ⟨second, member, keyBool⟩ := List.countP_pos_iff.mp tailWide
        have keySecond : key second = event := of_decide_eq_true keyBool
        refine ⟨head, second, (List.mem_cons_self : head ∈ head :: tail),
          List.mem_cons_of_mem head member, ?_, hit, keySecond, findHead⟩
        intro same
        exact (List.nodup_cons.mp nodup).1 (same ▸ member)
      · have tailWide : 2 ≤ tail.countP (fun copy => key copy = event) := by
          rw [countP_cons_miss key head tail event hit] at wide
          exact wide
        obtain ⟨first, second, firstMem, secondMem, distinct, keyFirst, keySecond, found⟩ :=
          tailMatches tailNodup tailWide
        refine ⟨first, second, List.mem_cons_of_mem head firstMem,
          List.mem_cons_of_mem head secondMem, distinct, keyFirst, keySecond, ?_⟩
        rw [find_cons_miss_event key head tail event hit]
        exact found

/-- **Negative.** A fibre of size at least two, and a nonzero source weight,
make the concentrated correction unequal. These two hypotheses are the least
ones: a single match has only one weight, and weight zero is equal on every match. -/
theorem tilt_not_uniformFibre {Event Copy : Type*} [DecidableEq Event] [DecidableEq Copy]
    {K : Type*} [CommSemiring K] (key : Copy → Event) (copies : List Copy)
    (sourceWeight : Event → K) (event : Event) (nodup : copies.Nodup)
    (wide : 2 ≤ copies.countP (fun copy => key copy = event))
    (nonzero : sourceWeight event ≠ 0) :
    ¬ UniformFibre key (tilt key copies sourceWeight) copies := by
  intro uniform
  obtain ⟨first, second, firstMem, secondMem, distinct, keyFirst, keySecond, found⟩ :=
    exists_two_matches key copies event nodup wide
  have firstWeight : tilt key copies sourceWeight first = sourceWeight event := by
    rw [tilt, keyFirst, found, if_pos rfl]
  have secondWeight : tilt key copies sourceWeight second = 0 := by
    have foundSecond :
        copies.find? (fun copy => key copy = key second) = some first := by
      simpa [keySecond] using found
    rw [tilt, foundSecond]
    exact if_neg fun same => distinct (Option.some_injective Copy same)
  have same := uniform firstMem secondMem (keyFirst.trans keySecond.symm)
  rw [firstWeight, secondWeight] at same
  exact nonzero same

/-- **Equal fibres.** With one weight on each fibre, preservation holds exactly
when that weight is the quotient of a `Splits` and an event with no match has
weight zero. -/
theorem uniformFibre_weightPreserving_iff {Event Copy : Type*} [DecidableEq Event]
    {K : Type*} [CommSemiring K] (sourceWeight : Event → K) (key : Copy → Event)
    (weight : Copy → K) (copies : List Copy)
    (uniform : UniformFibre key weight copies) :
    weightPreserving sourceWeight key weight copies ↔
      (∀ event, copies.countP (fun copy => key copy = event) = 0 → sourceWeight event = 0) ∧
        ∀ event, copies.countP (fun copy => key copy = event) ≠ 0 →
          ∃ split : Splits K (copies.countP (fun copy => key copy = event)) (sourceWeight event),
            ∀ copy ∈ copies, key copy = event → weight copy = split.quotient := by
  constructor
  · intro preserves
    constructor
    · intro event empty
      have noMatch : ∀ copy ∈ copies, key copy ≠ event := by
        intro copy member keyEq
        exact (List.countP_eq_zero.mp empty) copy member (decide_eq_true keyEq)
      rw [preserves event, groupSum_eq_zero weight noMatch]
    · intro event nonempty
      obtain ⟨copy, member, keyBool⟩ :=
        List.countP_pos_iff.mp (Nat.pos_of_ne_zero nonempty)
      have keyEq : key copy = event := of_decide_eq_true keyBool
      refine ⟨
        { nonzero := nonempty
          quotient := weight copy
          equation := ?_ },
        ?_⟩
      · have same : ∀ other ∈ copies, key other = event → weight other = weight copy := by
          intro other otherMem otherKey
          exact uniform otherMem member (otherKey.trans keyEq.symm)
        exact (groupSum_of_constant_fibre key weight copies event (weight copy) same).symm.trans
          (preserves event).symm
      · intro other otherMem otherKey
        exact uniform otherMem member (otherKey.trans keyEq.symm)
  · intro ⟨unmatched, splitFibre⟩ event
    by_cases empty : copies.countP (fun copy => key copy = event) = 0
    · rw [unmatched event empty]
      exact (groupSum_eq_zero weight fun copy member keyEq =>
        (List.countP_eq_zero.mp empty) copy member (decide_eq_true keyEq)).symm
    · obtain ⟨split, same⟩ := splitFibre event empty
      rw [groupSum_of_constant_fibre key weight copies event split.quotient same, split.equation]

/-! ## The two-body fibre -/

theorem twoBodyCandidates_nodup : twoBodyCandidates.Nodup := by
  unfold twoBodyCandidates twoBodyMultiplicity twoBodyMatrixCount
  decide

theorem twoBody_count :
    twoBodyCandidates.countP (fun _ : Fin twoBodyMultiplicity => () = ()) = twoBodyMultiplicity := by
  unfold twoBodyCandidates
  rw [List.countP_eq_length_filter]
  have kept :
      ((List.ofFn fun index : Fin twoBodyMultiplicity => index).filter
        (fun _ => () = ())) =
        List.ofFn fun index : Fin twoBodyMultiplicity => index := by
    refine List.filter_eq_self.mpr ?_
    intro _ _
    decide
  rw [kept, List.length_ofFn]

/-- **Positive.** The two-body quotient from `Splits` preserves the unit event. -/
theorem twoBody_split_preserves {K : Type*} [CommSemiring K] (w : K)
    (split : Splits K twoBodyMultiplicity w) :
    weightPreserving (fun _ : Unit => w) (fun _ : Fin twoBodyMultiplicity => ())
      (fun _ => split.quotient) twoBodyCandidates := by
  intro event
  cases event
  exact (corrected_two_body w split).symm

/-- **Negative.** The undivided unit weight is uniform on the two-body fibre and
its group sum is the multiplicity, not the unit. -/
theorem twoBody_unit_not_preserving :
    UniformFibre (fun _ : Fin twoBodyMultiplicity => ()) (fun _ => (1 : ℕ)) twoBodyCandidates ∧
      ¬ weightPreserving (fun _ : Unit => (1 : ℕ)) (fun _ => ()) (fun _ => (1 : ℕ))
          twoBodyCandidates := by
  refine ⟨constant_uniformFibre _ _ _, ?_⟩
  intro preserves
  have summed := preserves ()
  rw [const_fibre_sum, twoBodyMultiplicity_eq] at summed
  exact absurd summed (by decide : (1 : ℕ) ≠ 2 * 1)

/-- The uniform unit is not a common quotient: `ℕ` has no such `Splits`. -/
theorem twoBody_unit_not_quotient :
    ¬ (∀ (_event : Unit),
        twoBodyCandidates.countP (fun _ : Fin twoBodyMultiplicity => () = ()) ≠ 0 →
        ∃ split : Splits ℕ
          (twoBodyCandidates.countP (fun _ : Fin twoBodyMultiplicity => () = ())) 1,
          ∀ copy ∈ twoBodyCandidates, (1 : ℕ) = split.quotient) := by
  intro fibre
  have nonempty : twoBodyCandidates.countP (fun _ : Fin twoBodyMultiplicity => () = ()) ≠ 0 := by
    rw [twoBody_count]
    exact twoBodyMultiplicity_eq.symm ▸ Nat.succ_ne_zero 1
  obtain ⟨split, _⟩ := fibre () nonempty
  have countIsTwo :
      twoBodyCandidates.countP (fun _ : Fin twoBodyMultiplicity => () = ()) = 2 := by
    rw [twoBody_count, twoBodyMultiplicity_eq]
  have doubled : (2 : ℕ) * split.quotient = 1 :=
    (congrArg (fun n : ℕ => n * split.quotient) (congrArg Nat.cast countIsTwo)).symm.trans
      split.equation
  exact nat_two_body_not_split ⟨{
    nonzero := by decide
    quotient := split.quotient
    equation := doubled
  }⟩

/-- One stored observation has the successor-occurrence size as its fibre, and
that size does not split the observation in `ℕ`. -/
theorem succ_observation_not_split :
    size occFinitary succAx = twoBodyMultiplicity ∧
      oneObservation.observational.pos = 1 ∧
      ¬ Nonempty (Splits ℕ (size occFinitary succAx) oneObservation.observational.pos) := by
  refine ⟨?_, (duplication_turns_one_into_two).2, ?_⟩
  · rw [size_succAx, twoBodyMultiplicity_eq]
  · rw [size_succAx, (duplication_turns_one_into_two).2]
    exact nat_one_not_split_by_two

/-- **Positive correction on the two-body fibre.** The whole weight sits on the
first candidate. -/
theorem twoBody_tilt_preserves {K : Type*} [CommSemiring K] (w : K) :
    weightPreserving (fun _ : Unit => w) (fun _ : Fin twoBodyMultiplicity => ())
      (tilt (fun _ => ()) twoBodyCandidates (fun _ => w)) twoBodyCandidates :=
  tilt_preserves (fun _ => w) (fun _ => ()) twoBodyCandidates twoBodyCandidates_nodup
    fun event _ => by
      cases event
      rw [twoBody_count]
      exact twoBodyMultiplicity_eq.symm ▸ Nat.succ_ne_zero 1

/-- **Negative correction.** For a nonzero weight the two candidates do not agree. -/
theorem twoBody_tilt_not_uniform {K : Type*} [CommSemiring K] (w : K) (nonzero : w ≠ 0) :
    ¬ UniformFibre (fun _ : Fin twoBodyMultiplicity => ())
        (tilt (fun _ => ()) twoBodyCandidates (fun _ => w)) twoBodyCandidates :=
  tilt_not_uniformFibre (fun _ => ()) twoBodyCandidates (fun _ => w) () twoBodyCandidates_nodup
    (by
      rw [twoBody_count, twoBodyMultiplicity_eq])
    nonzero

/-! ## Hosting a weighted theory -/

/-- A candidate hosts a weighted source when some map into the candidate, with
a read-back, preserves closed sums and is hosting on every support row. -/
def HostsWeighted {K : Type*} [Semiring K] {sourceSpace candidateSpace : GSLT}
    (candidate : WeightedSystem candidateSpace K)
    (source : WeightedSystem sourceSpace K) (noCancelSource : NoCancellation K) : Prop :=
  ∃ (term : sourceSpace.Term → candidateSpace.Term)
    (labelMap : source.Label → candidate.Label)
    (readBack : candidateSpace.Term → sourceSpace.Term)
    (resp : ∀ {left right : candidateSpace.Term}, candidateSpace.Equiv left right →
      sourceSpace.Equiv (readBack left) (readBack right))
    (termResp : ∀ {first second : sourceSpace.Term}, sourceSpace.Equiv first second →
      candidateSpace.Equiv (term first) (term second)),
    KernelPreserving
        ({ source := source, target := candidate, term := term, labelMap := labelMap,
            readBack := readBack, readBack_resp := resp } :
          KernelMap K sourceSpace candidateSpace) ∧
      ∀ label,
        (supportOfTerms
            ({ source := source, target := candidate, term := term, labelMap := labelMap,
                readBack := readBack, readBack_resp := resp } :
              KernelMap K sourceSpace candidateSpace)
            noCancelSource label termResp).Hosting

/-- **Positive.** The identity hosts a weighted system: it preserves every closed
sum and is hosting on the support. -/
theorem identity_hostsWeighted :
    HostsWeighted (outcomeSystem (1 : ℕ))
      (outcomeSystem (1 : ℕ)) nat_noCancellation := by
  refine ⟨id, id, id, fun equivalent => equivalent, fun equivalent => equivalent,
    kernelId_preserving (outcomeSystem (1 : ℕ)), ?_⟩
  intro label
  cases label
  exact identity_support_hosting

theorem outcome_singleton_one :
    closedSum ((outcomeSystem (1 : ℕ)).kernel () none) (fun t => t = some true) = 1 := by
  show closedSum (outcomeStep (1 : ℕ) none) (fun t => t = some true) = 1
  rw [outcomeStep, closedSum_outcomeKernel]
  simp

theorem outcomeKernel_doubled_trichotomy (present : Option Bool → Prop) :
    closedSum (outcomeKernel (2 * 1 : ℕ)) present = 0 ∨
      closedSum (outcomeKernel (2 * 1 : ℕ)) present = 2 ∨
        closedSum (outcomeKernel (2 * 1 : ℕ)) present = 4 := by
  rw [closedSum_outcomeKernel]
  split_ifs <;> decide

theorem outcome_doubled_from_start (present : quiet.Term → Prop) :
    closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () none) present = 0 ∨
      closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () none) present = 2 ∨
        closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () none) present = 4 :=
  outcomeKernel_doubled_trichotomy present

theorem outcome_doubled_from_some (b : Bool) (present : quiet.Term → Prop) :
    closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () (some b)) present = 0 := by
  show closedSum (outcomeStep (2 * 1 : ℕ) (some b)) present = 0
  have zeroRow : outcomeStep (2 * 1 : ℕ) (some b) = 0 := rfl
  exact zeroRow ▸ closedSum_zero present

theorem outcome_doubled_trichotomy (s : quiet.Term) (present : quiet.Term → Prop) :
    closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () s) present = 0 ∨
      closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () s) present = 2 ∨
        closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () s) present = 4 := by
  rcases quiet_cases s with start | ⟨b, someTerm⟩
  · rw [start]
    exact outcome_doubled_from_start present
  · rw [someTerm]
    exact Or.inl (outcome_doubled_from_some b present)

/-- **Negative.** Doubling every natural weight hosts the source on supports.
No map into the doubled system, for any read-back, preserves closed sums:
every doubled row sums to `0`, `2`, or `4`, and the source singleton sums to `1`. -/
theorem doubledNatural_supportHosting_not_weight :
    (ContextMap.ofTerms (source := supportGSLT (outcomeSystem (1 : ℕ)) nat_noCancellation ())
      (target := (supportGSLT (outcomeSystem (2 * 1 : ℕ)) nat_noCancellation ()).termsAlone)
      PUnit.unit id (fun equivalent => equivalent)).Hosting ∧
      ¬ ∃ (term : quiet.Term → quiet.Term) (labelMap : Unit → Unit)
          (readBack : quiet.Term → quiet.Term)
          (resp : ∀ {left right : quiet.Term}, quiet.Equiv left right →
            quiet.Equiv (readBack left) (readBack right)),
          KernelPreserving
            ({ source := outcomeSystem (1 : ℕ), target := outcomeSystem (2 * 1 : ℕ),
                term := term, labelMap := labelMap, readBack := readBack,
                readBack_resp := resp } : KernelMap ℕ quiet quiet) := by
  refine ⟨scale_hosting, ?_⟩
  intro ⟨term, _labelMap, readBack, _resp, preserves⟩
  have preserved := preserves () none (fun t => t = some true) quiet_true_closed
  have sourceOne :
      closedSum ((outcomeSystem (1 : ℕ)).kernel () none) (fun t => t = some true) = 1 :=
    outcome_singleton_one
  have targetShape :=
    outcome_doubled_trichotomy (term none) (fun t => readBack t = some true)
  have bridge :
      closedSum ((outcomeSystem (1 : ℕ)).kernel () none) (fun t => t = some true) =
        closedSum ((outcomeSystem (2 * 1 : ℕ)).kernel () (term none))
          (fun t => readBack t = some true) := preserved
  rcases targetShape with zero | two | four
  · exact absurd (sourceOne.symm.trans (bridge.trans zero)) (by decide)
  · exact absurd (sourceOne.symm.trans (bridge.trans two)) (by decide)
  · exact absurd (sourceOne.symm.trans (bridge.trans four)) (by decide)

end Mettapedia.Logic.HostingStyles.Weighted

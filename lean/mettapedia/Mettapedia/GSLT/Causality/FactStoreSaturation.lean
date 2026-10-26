import Mettapedia.GSLT.Causality.FactLinearResources
import Mettapedia.GSLT.OpenEnded.ChaoticIteration

/-!
# Facts in a set store: keep-only rules saturate, and once-per-match firing is needed only for bags

Over a bag store, a keep-only rule that produces anything stays enabled forever and no run rests
(`keepOnly_never_quiescent`). Three remedies are in use: an idempotent (set) store; firing each rule instance
once (a consumed activation, as MM2 consumes its `exec` atoms); and a history of the matches already fired, as
Constraint Handling Rules keeps for its propagation rules. This file compares them.

## A set store needs no history

Read over a set store, a rule instance adds its production when all its reads are present (`setRule`). Its
firings are chaotic iteration of monotone rules, so:
* the store's closure above a seed is the least set containing the seed and closed under every rule
  (`saturation_isLeast`);
* every fair schedule reaches it and stays there, and any two fair schedules agree from some point on
  (`fair_run_reaches_saturation`, `fair_schedules_agree`);
* along any schedule at most one firing per atom changes the store (`effectiveSteps_bounded`);
* firing at the closure changes nothing (`setRule_le_saturation`).

The support of every keep-only bag run stays inside the closure (`support_le_saturation`).

## Firing each instance once, keyed by the instance

Give every catalogued instance one firing (`OnceStep`). Every step uses one up (`onceStep_pending_lt`), so every
run ends (`onceStep_wellFounded`, `exists_quiescent`). When the reads have no repeated atom, the bag reached when
nothing more can fire has exactly the closure as its support (`once_quiescent_support_eq_saturation`). Firing each
instance once, keyed by the instance, therefore computes the set store's closure.

## A history keyed by occurrences does not end

A history keyed by the identities of the occurrences a match used, as Constraint Handling Rules keys its
propagation history, does not stop a rule that reproduces what it reads: each firing creates a new occurrence,
which is a new match. For the rule that reads `p` and produces `p`, every reachable state can fire again and the
number of copies grows without bound (`occurrenceHistory_never_quiescent`). Keyed by the value matched, the same
rule fires once (`valueHistory_quiescent`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT.OpenEnded.ChaoticIteration

universe uRes uRule

namespace System

variable {R : Type uRes} (S : System.{uRes, uRule} R)

/-! ## The set store -/

/-- **A rule instance read over a set store**: when all its reads are present, it adds its production. -/
def setRule {site : S.Site} (i : S.Instance site) : Set R →o Set R where
  toFun X := {r | (∀ a ∈ S.read i, a ∈ X) ∧ r ∈ S.produce i}
  monotone' _ _ le _ member := ⟨fun a inRead => le (member.1 a inRead), member.2⟩

/-- **The closure of a set store** above a seed, under a catalogue of instances. -/
def saturation (catalogue : Set S.Entry) (seed : Set R) : Set R :=
  target (fun entry : catalogue => S.setRule entry.1.2) seed

/-- **The closure is the least set containing the seed and closed under every catalogued rule.** -/
theorem saturation_isLeast (catalogue : Set S.Entry) (seed : Set R) :
    IsLeast {X | seed ≤ X ∧ ∀ entry : catalogue, S.setRule entry.1.2 X ≤ X}
      (S.saturation catalogue seed) :=
  isLeast_target _ seed

/-- **Firing at the closure changes nothing.** -/
theorem setRule_le_saturation (catalogue : Set S.Entry) (seed : Set R) (entry : catalogue) :
    S.setRule entry.1.2 (S.saturation catalogue seed) ≤ S.saturation catalogue seed :=
  (S.saturation_isLeast catalogue seed).1.2 entry

/-- **Every fair schedule reaches the closure and stays there.** -/
theorem fair_run_reaches_saturation [Finite R] (catalogue : Set S.Entry) (seed : Set R)
    {schedule : ℕ → catalogue} (fair : Fair schedule) :
    ∃ N, ∀ n, N ≤ n →
      run (fun entry : catalogue => S.setRule entry.1.2) seed schedule n =
        S.saturation catalogue seed :=
  run_eventually_eq_target _ seed fair

/-- **Two fair schedules agree from some point on.** -/
theorem fair_schedules_agree [Finite R] (catalogue : Set S.Entry) (seed : Set R)
    {first second : ℕ → catalogue} (fairFirst : Fair first) (fairSecond : Fair second) :
    ∃ N, ∀ n, N ≤ n →
      run (fun entry : catalogue => S.setRule entry.1.2) seed first n =
        run (fun entry : catalogue => S.setRule entry.1.2) seed second n :=
  schedule_independent _ seed fairFirst fairSecond

/-- **At most one firing per atom changes the store**, along any schedule. -/
theorem effectiveSteps_bounded [Finite R] (catalogue : Set S.Entry) (seed : Set R)
    (schedule : ℕ → catalogue) (n : ℕ) :
    effectiveSteps (fun entry : catalogue => S.setRule entry.1.2) seed schedule n ≤ Nat.card R :=
  effectiveSteps_le_card _ seed schedule n

variable [DecidableEq R]

/-- **The support of every keep-only bag run stays inside the closure** of its starting support. -/
theorem support_le_saturation (catalogue : List S.Entry) {M N : Multiset R}
    (run : Relation.ReflTransGen (S.CatalogueStep catalogue) M N) :
    {r | r ∈ N} ⊆ S.saturation {entry | entry ∈ catalogue} {r | r ∈ M} := by
  have least := S.saturation_isLeast {entry | entry ∈ catalogue} {r | r ∈ M}
  induction run with
  | refl => exact least.1.1
  | tail _ step previous =>
      obtain ⟨entry, member, enabled, rfl⟩ := step
      intro r inFired
      rcases Multiset.mem_add.mp inFired with inRest | produced
      · exact previous (Multiset.mem_of_le (Multiset.sub_le_self _ _) inRest)
      · have readsIn : ∀ a ∈ S.read entry.2, a ∈ S.saturation {entry | entry ∈ catalogue} {r | r ∈ M} :=
          fun a inRead => previous (Multiset.mem_of_le (le_trans (Multiset.le_add_left _ _) enabled) inRead)
        exact least.1.2 ⟨entry, member⟩ ⟨readsIn, produced⟩

/-! ## Firing each catalogued instance once -/

variable [DecidableEq S.Entry]

/-- A state of once-per-instance firing: the bag, and the catalogued instances not yet fired. -/
abbrev OnceState := Multiset R × List S.Entry

/-- **Fire a pending instance once**: it is enabled; it fires, and it leaves the pending list. -/
def OnceStep (source target : S.OnceState) : Prop :=
  ∃ entry ∈ source.2, S.Enables source.1 entry.2 ∧ target = (S.fire source.1 entry.2, source.2.erase entry)

/-- Nothing pending can fire. -/
def OnceQuiescent (state : S.OnceState) : Prop :=
  ∀ entry ∈ state.2, ¬ S.Enables state.1 entry.2

/-- **Every step uses up one pending instance.** -/
theorem onceStep_pending_lt {source target : S.OnceState} (step : S.OnceStep source target) :
    target.2.length < source.2.length := by
  obtain ⟨entry, member, -, rfl⟩ := step
  rw [List.length_erase_of_mem member]
  exact Nat.sub_lt (List.length_pos_of_mem member) Nat.one_pos

/-- **Every run of once-per-instance firing ends.** -/
theorem onceStep_wellFounded : WellFounded fun target source => S.OnceStep source target :=
  Subrelation.wf (fun step => S.onceStep_pending_lt step)
    (InvImage.wf (fun state : S.OnceState => state.2.length) Nat.lt_wfRel.wf)

/-- **From every state some run reaches a state where nothing can fire.** -/
theorem exists_quiescent (state : S.OnceState) :
    ∃ last, Relation.ReflTransGen S.OnceStep state last ∧ S.OnceQuiescent last := by
  induction state using (S.onceStep_wellFounded).induction with
  | _ state ih =>
      by_cases quiet : S.OnceQuiescent state
      · exact ⟨state, .refl, quiet⟩
      · simp only [OnceQuiescent, not_forall, not_not] at quiet
        obtain ⟨entry, member, enabled⟩ := quiet
        have step : S.OnceStep state (S.fire state.1 entry.2, state.2.erase entry) :=
          ⟨entry, member, enabled, rfl⟩
        obtain ⟨last, reach, lastQuiet⟩ := ih _ step
        exact ⟨last, Relation.ReflTransGen.head step reach, lastQuiet⟩

/-- What once-per-instance firing keeps true along a run from `(M₀, catalogue)`. -/
structure OnceInvariant (catalogue : List S.Entry) (M₀ : Multiset R) (state : S.OnceState) : Prop where
  grows : M₀ ≤ state.1
  pendingCatalogued : ∀ entry ∈ state.2, entry ∈ catalogue
  firedProduced : ∀ entry ∈ catalogue, entry ∉ state.2 → S.produce entry.2 ≤ state.1
  sound : {r | r ∈ state.1} ⊆ S.saturation {entry | entry ∈ catalogue} {r | r ∈ M₀}

theorem onceInvariant_of_run (keep : S.KeepOnly) {catalogue : List S.Entry} {M₀ : Multiset R}
    {state : S.OnceState} (run : Relation.ReflTransGen S.OnceStep (M₀, catalogue) state) :
    S.OnceInvariant catalogue M₀ state := by
  have least := S.saturation_isLeast {entry | entry ∈ catalogue} {r | r ∈ M₀}
  induction run with
  | refl =>
      exact ⟨le_rfl, fun _ member => member, fun _ member absent => absurd member absent, least.1.1⟩
  | @tail mid _ _ step previous =>
      obtain ⟨entry, member, enabled, rfl⟩ := step
      obtain ⟨grows, catalogued, produced, sound⟩ := previous
      have fireEq : S.fire mid.1 entry.2 = mid.1 + S.produce entry.2 := by
        rw [fire, keep entry.2, tsub_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [fireEq]
        exact le_trans grows (Multiset.le_add_right _ _)
      · exact fun other inErased => catalogued other (List.mem_of_mem_erase inErased)
      · intro other inCatalogue notPending
        rw [fireEq]
        by_cases same : other = entry
        · subst same
          exact Multiset.le_add_left _ _
        · have wasFired : other ∉ mid.2 := fun inPending =>
            notPending ((List.mem_erase_of_ne same).mpr inPending)
          exact le_trans (produced other inCatalogue wasFired) (Multiset.le_add_right _ _)
      · intro r inFired
        rw [fireEq] at inFired
        rcases Multiset.mem_add.mp inFired with inRest | inProduced
        · exact sound inRest
        · have readsIn : ∀ a ∈ S.read entry.2,
              a ∈ S.saturation {entry | entry ∈ catalogue} {r | r ∈ M₀} := fun a inRead =>
            sound (Multiset.mem_of_le (le_trans (Multiset.le_add_left _ _) enabled) inRead)
          exact least.1.2 ⟨entry, catalogued entry member⟩ ⟨readsIn, inProduced⟩

/-- **Once-per-instance firing computes the closure.** For keep-only rules whose reads repeat no atom, the bag
reached when nothing more can fire has the closure of the starting support as its support. -/
theorem once_quiescent_support_eq_saturation (keep : S.KeepOnly) {catalogue : List S.Entry}
    (readsNodup : ∀ entry ∈ catalogue, (S.read entry.2).Nodup) {M₀ : Multiset R} {state : S.OnceState}
    (run : Relation.ReflTransGen S.OnceStep (M₀, catalogue) state) (quiet : S.OnceQuiescent state) :
    {r | r ∈ state.1} = S.saturation {entry | entry ∈ catalogue} {r | r ∈ M₀} := by
  obtain ⟨grows, catalogued, produced, sound⟩ := S.onceInvariant_of_run keep run
  refine le_antisymm sound ((S.saturation_isLeast _ _).2 ⟨fun r inSeed => Multiset.mem_of_le grows inSeed, ?_⟩)
  rintro ⟨entry, inCatalogue⟩ r ⟨readsIn, inProduced⟩
  by_cases pending : entry ∈ state.2
  · have enabled : S.Enables state.1 entry.2 := by
      unfold Enables
      rw [keep entry.2, zero_add, Multiset.le_iff_subset (readsNodup entry inCatalogue)]
      exact fun a inRead => readsIn a inRead
    exact absurd enabled (quiet entry pending)
  · exact Multiset.mem_of_le (produced entry inCatalogue pending) inProduced

end System

/-! ## Histories keyed by occurrences or by values -/

namespace HistoryControls

/-- **A history keyed by occurrences**, for the rule that reads `p` and produces `p`: `copies` occurrences of `p`
with identities `0, …, copies - 1`, and the identities a firing has already used. -/
structure OccurrenceState where
  copies : ℕ
  used : Finset ℕ

/-- A firing uses an occurrence not used before and creates a new one. -/
def OccurrenceStep (source target : OccurrenceState) : Prop :=
  ∃ k < source.copies, k ∉ source.used ∧ target = ⟨source.copies + 1, insert k source.used⟩

/-- The start: one occurrence, nothing fired. -/
def occurrenceStart : OccurrenceState := ⟨1, ∅⟩

theorem occurrence_invariant {state : OccurrenceState}
    (run : Relation.ReflTransGen OccurrenceStep occurrenceStart state) :
    1 ≤ state.copies ∧ state.used ⊆ Finset.range (state.copies - 1) := by
  induction run with
  | refl => exact ⟨le_rfl, by simp [occurrenceStart]⟩
  | tail _ step previous =>
      obtain ⟨k, below, fresh, rfl⟩ := step
      obtain ⟨atLeast, within⟩ := previous
      dsimp only
      refine ⟨by omega, ?_⟩
      intro m member
      rcases Finset.mem_insert.mp member with rfl | old
      · simp only [Finset.mem_range]
        omega
      · have := Finset.mem_range.mp (within old)
        simp only [Finset.mem_range]
        omega

/-- **Keyed by occurrences, the history never lets the rule rest**: every reachable state can fire again. -/
theorem occurrenceHistory_never_quiescent {state : OccurrenceState}
    (run : Relation.ReflTransGen OccurrenceStep occurrenceStart state) :
    ∃ next, OccurrenceStep state next := by
  obtain ⟨atLeast, within⟩ := occurrence_invariant run
  refine ⟨_, state.copies - 1, by omega, fun used => ?_, rfl⟩
  have := Finset.mem_range.mp (within used)
  omega

/-- **Keyed by occurrences, the copies grow without bound.** -/
theorem occurrenceHistory_unbounded (n : ℕ) :
    ∃ state, Relation.ReflTransGen OccurrenceStep occurrenceStart state ∧ n ≤ state.copies := by
  induction n with
  | zero => exact ⟨occurrenceStart, .refl, Nat.zero_le _⟩
  | succ n ih =>
      obtain ⟨state, run, atLeast⟩ := ih
      obtain ⟨next, step⟩ := occurrenceHistory_never_quiescent run
      obtain ⟨k, below, fresh, rfl⟩ := step
      exact ⟨_, run.tail ⟨k, below, fresh, rfl⟩, by dsimp only; omega⟩

/-- **A history keyed by the value matched**: the copies of `p`, and whether the match on the value `p` has
fired. -/
structure ValueState where
  copies : ℕ
  fired : Bool

def ValueStep (source target : ValueState) : Prop :=
  source.fired = false ∧ target = ⟨source.copies + 1, true⟩

/-- **Keyed by the value, the same rule fires once and rests.** -/
theorem valueHistory_quiescent {state : ValueState}
    (run : Relation.ReflTransGen ValueStep ⟨1, false⟩ state) :
    state = ⟨1, false⟩ ∨ (state = ⟨2, true⟩ ∧ ∀ next, ¬ ValueStep state next) := by
  induction run with
  | refl => exact Or.inl rfl
  | tail _ step previous =>
      obtain ⟨notFired, rfl⟩ := step
      rcases previous with rfl | ⟨rfl, -⟩
      · exact Or.inr ⟨rfl, fun next ⟨fired, _⟩ => by simp at fired⟩
      · simp at notFired

end HistoryControls

end Mettapedia.GSLT.Causality.ResourceInteraction

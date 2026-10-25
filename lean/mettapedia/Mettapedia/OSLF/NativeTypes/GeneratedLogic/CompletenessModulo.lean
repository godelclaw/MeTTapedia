import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Completeness

/-!
# The front door is complete modulo equations on finite canonical regions

Given canonical forms, take a term whose canonical closure is finite. That is a finite list that
contains the term's canonical form and the canonical forms of the listed successors of each of its
states, where the fuel lists every state's steps completely. Then:

- **Rounds stop adding** (`iterate_stable`), for any listing function, from a start without repetition:
  each round adds new terms or nothing, and stays inside the closure.
- **The grown canonical region closes** within as many rounds as the closure has terms
  (`growCanonical_closed`).
- **So every behavioural formula is decided** (`decideCanonical_complete`), and `ask`, given the canonical
  forms, answers proved or refuted, never open (`ask_decides_modulo`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! ## Rounds of adding new terms -/

/-- Rounds of adding, without repetition, what a function lists for each term so far. -/
def iterate (next : Pattern → List Pattern) (start : List Pattern) : ℕ → List Pattern
  | 0 => start
  | rounds + 1 => addNew (iterate next start rounds) ((iterate next start rounds).flatMap next)

variable {next : Pattern → List Pattern} {start closure : List Pattern}

theorem iterate_succ (rounds : ℕ) :
    iterate next start (rounds + 1) = addNew (iterate next start rounds) ((iterate next start rounds).flatMap next) :=
  rfl

theorem iterate_nodup (distinct : start.Nodup) : ∀ rounds, (iterate next start rounds).Nodup
  | 0 => distinct
  | rounds + 1 => by
    rw [iterate_succ]
    exact addNew_nodup (iterate_nodup distinct rounds)

/-- A term of a round started there or was listed for some term. -/
theorem mem_iterate : ∀ {rounds : ℕ} {other : Pattern}, other ∈ iterate next start rounds →
    other ∈ start ∨ ∃ source, other ∈ next source
  | 0, _, inside => Or.inl inside
  | rounds + 1, other, inside => by
    rw [iterate_succ] at inside
    rcases mem_addNew.mp inside with inside | inside
    · exact mem_iterate inside
    · obtain ⟨source, -, listed⟩ := List.mem_flatMap.mp inside
      exact Or.inr ⟨source, listed⟩

theorem iterate_subset (starts : ∀ other ∈ start, other ∈ closure)
    (closed : ∀ source ∈ closure, ∀ other ∈ next source, other ∈ closure) :
    ∀ rounds, ∀ other ∈ iterate next start rounds, other ∈ closure
  | 0, other, inside => starts other inside
  | rounds + 1, other, inside => by
    rw [iterate_succ] at inside
    rcases mem_addNew.mp inside with inside | inside
    · exact iterate_subset starts closed rounds other inside
    · obtain ⟨source, member, listed⟩ := List.mem_flatMap.mp inside
      exact closed source (iterate_subset starts closed rounds source member) other listed

/-- A round that adds nothing is a fixed point. -/
theorem iterate_stays {rounds : ℕ} (still : iterate next start (rounds + 1) = iterate next start rounds) :
    ∀ extra, iterate next start (rounds + extra) = iterate next start rounds
  | 0 => rfl
  | extra + 1 => by
    rw [← Nat.add_assoc, iterate_succ, iterate_stays still extra, ← iterate_succ, still]

/-- Each round adds a term or adds nothing. -/
theorem iterate_grows_or_stays (rounds : ℕ) :
    iterate next start (rounds + 1) = iterate next start rounds ∨
      (iterate next start rounds).length < (iterate next start (rounds + 1)).length := by
  obtain ⟨extra, same⟩ := addNew_extends (iterate next start rounds) ((iterate next start rounds).flatMap next)
  rw [iterate_succ, same]
  cases extra with
  | nil => exact Or.inl (List.append_nil _)
  | cons first rest => exact Or.inr (by simp)

/-- If no round up to this one stopped, the list has gained a term in each. -/
theorem iterate_length_of_growing : ∀ rounds,
    (∀ earlier < rounds, iterate next start (earlier + 1) ≠ iterate next start earlier) →
      rounds + start.length ≤ (iterate next start rounds).length
  | 0, _ => by rw [Nat.zero_add]; exact Nat.le_refl _
  | rounds + 1, growing => by
    have previous := iterate_length_of_growing rounds fun earlier below => growing earlier (by omega)
    rcases iterate_grows_or_stays (next := next) (start := start) rounds with still | longer
    · exact absurd still (growing rounds (by omega))
    · omega

/-- **Rounds stop adding** before as many rounds as the closure has terms, from a nonempty start without
repetition. -/
theorem iterate_stable (nonempty : start ≠ []) (distinct : start.Nodup) (starts : ∀ other ∈ start, other ∈ closure)
    (closed : ∀ source ∈ closure, ∀ other ∈ next source, other ∈ closure) :
    ∃ rounds < closure.length, iterate next start (rounds + 1) = iterate next start rounds := by
  by_contra never
  simp only [not_exists, not_and] at never
  have long := iterate_length_of_growing (next := next) (start := start) closure.length
    fun earlier below => never earlier below
  have short := ((iterate_nodup distinct closure.length).subperm fun other inside =>
    iterate_subset starts closed closure.length other inside).length_le
  have positive : 0 < start.length := List.length_pos_of_ne_nil nonempty
  omega

/-- **After enough rounds nothing new is listed.** -/
theorem iterate_closed (nonempty : start ≠ []) (distinct : start.Nodup) (starts : ∀ other ∈ start, other ∈ closure)
    (closed : ∀ source ∈ closure, ∀ other ∈ next source, other ∈ closure) {rounds : ℕ}
    (enoughRounds : closure.length ≤ rounds) :
    ∀ source ∈ iterate next start rounds, ∀ other ∈ next source, other ∈ iterate next start rounds := by
  obtain ⟨stable, below, still⟩ := iterate_stable nonempty distinct starts closed
  have same := iterate_stays still (rounds - stable)
  rw [show stable + (rounds - stable) = rounds by omega] at same
  rw [same]
  have inside := subset_of_addNew_eq (by rw [← iterate_succ]; exact still)
  exact fun source member other listed => inside other (List.mem_flatMap.mpr ⟨source, member, listed⟩)

/-! ## Canonical regions -/

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ} {canon : Pattern → Pattern} {domain : Pattern → Bool}

theorem growCanonical_eq_iterate (term : Pattern) : ∀ rounds,
    growCanonical relEnv language fuel canon term rounds =
      iterate (nextCanonical relEnv language fuel canon) [canon term] rounds
  | 0 => rfl
  | rounds + 1 => by
    rw [iterate_succ, ← growCanonical_eq_iterate term rounds]
    rfl

/-- **A canonical closure of a term**: a list of admitted terms that contains the term's canonical form and
the canonical forms of the listed successors of each of its states, where every state's steps are listed
completely. -/
structure CanonicalClosure (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (canon : Pattern → Pattern)
    (domain : Pattern → Bool) (term : Pattern) (closure : List Pattern) : Prop where
  start : canon term ∈ closure
  admitted : ∀ state ∈ closure, domain state = true
  closed : ∀ state ∈ closure, isStateBool state = true → ∀ entry ∈ stepsAt relEnv language fuel state,
    canon entry.2 ∈ closure
  listed : ∀ state ∈ closure, isStateBool state = true → enough relEnv language fuel state = true

/-- **The grown canonical region closes** once the rounds reach the closure's size. -/
theorem growCanonical_closed (canonical : Canonical relEnv language canon domain) {term : Pattern}
    {closure : List Pattern} (bounded : CanonicalClosure relEnv language fuel canon domain term closure) {rounds : ℕ}
    (enoughRounds : closure.length ≤ rounds) :
    canonicalRegion relEnv language fuel canon domain (growCanonical relEnv language fuel canon term rounds) = true := by
  rw [growCanonical_eq_iterate]
  have starts : ∀ other ∈ [canon term], other ∈ closure := fun other inside => by
    rw [List.mem_singleton] at inside
    exact inside ▸ bounded.start
  have closedNext : ∀ source ∈ closure, ∀ other ∈ nextCanonical relEnv language fuel canon source,
      other ∈ closure := by
    intro source member other listed
    by_cases isState : isStateBool source = true
    · rw [nextCanonical, if_pos isState] at listed
      obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp listed
      exact bounded.closed source member isState entry entryMember
    · rw [nextCanonical, if_neg isState] at listed
      cases listed
  have still := iterate_closed (List.cons_ne_nil _ _) (List.nodup_singleton _) starts closedNext enoughRounds
  simp only [canonicalRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  have stateAdmitted : ∀ state, state ∈ iterate (nextCanonical relEnv language fuel canon) [canon term] rounds →
      domain state = true := fun state member =>
    bounded.admitted state (iterate_subset starts closedNext rounds state member)
  refine ⟨iterate_nodup (List.nodup_singleton _) rounds, fun state member => ⟨⟨stateAdmitted state member, ?_⟩, ?_⟩⟩
  · rcases mem_iterate member with inside | ⟨source, listed⟩
    · rw [List.mem_singleton] at inside
      rw [inside]
      refine canonical.idempotent ?_
      rw [← canonical.determined]
      exact bounded.admitted _ bounded.start
    · by_cases isState : isStateBool source = true
      · rw [nextCanonical, if_pos isState] at listed
        obtain ⟨entry, -, rfl⟩ := List.mem_map.mp listed
        refine canonical.idempotent ?_
        rw [← canonical.determined]
        exact stateAdmitted _ member
      · rw [nextCanonical, if_neg isState] at listed
        cases listed
  · by_cases isState : isStateBool state = true
    · exact Or.inr ⟨bounded.listed state (iterate_subset starts closedNext rounds state member) isState,
        fun entry entryMember => still state member _
          (by rw [nextCanonical, if_pos isState]; exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩)⟩
    · exact Or.inl (by simpa using isState)

/-- **Every behavioural formula is decided** modulo the equations, and the verdict is the truth. -/
theorem decideCanonical_complete {admissible : StepLabel → Bool} (canonical : Canonical relEnv language canon domain)
    (coherent : CoherentOn relEnv language fuel canon domain admissible) {term : Pattern} {closure : List Pattern}
    (bounded : CanonicalClosure relEnv language fuel canon domain term closure) {formula : Formula 0}
    (behavioural : formula.behaviouralIn admissible = true) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds) :
    ∃ verdict, decideCanonical relEnv language fuel canon domain formula term rounds = some verdict ∧
      (verdict = true ↔ (referenceStructure relEnv language).sat Env.closed formula term) := by
  have closed := growCanonical_closed canonical bounded enoughRounds
  have decided : decideCanonical relEnv language fuel canon domain formula term rounds =
      some ((canonicalExploration relEnv language fuel canon domain
        (growCanonical relEnv language fuel canon term rounds)).check
        formula ⟨0, growCanonical_length_pos relEnv language fuel canon term rounds⟩) := by
    unfold decideCanonical
    rw [if_pos closed]
  exact ⟨_, decided, decideCanonical_sound_on canonical coherent behavioural decided⟩

variable {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature}

/-- **`ask` decides modulo the equations**: given canonical forms, on a finite canonical closure it answers
proved or refuted, never open. -/
theorem ask_decides_modulo (forms : CanonicalForms relEnv language fuel) {term : Pattern} {closure : List Pattern}
    (bounded : CanonicalClosure relEnv language fuel forms.canon forms.domain term closure) {formula : Formula 0}
    (behavioural : formula.behaviouralIn forms.labels = true) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds)
    (hint : Option CertificateCandidate) :
    ∃ evidence, ask relEnv signature language fuel formula term hint rounds (some forms) = .proved evidence ∨
      ask relEnv signature language fuel formula term hint rounds (some forms) = .refuted evidence := by
  obtain ⟨verdict, decided, -⟩ :=
    decideCanonical_complete forms.canonical forms.coherent bounded behavioural enoughRounds
  have member : Evidence.canonicalRegion rounds ∈ gathered signature language formula term hint rounds := by
    simp [gathered]
  unfold ask
  split
  · rename_i evidence _
    exact ⟨evidence, Or.inl rfl⟩
  · rename_i none
    split
    · rename_i evidence _
      exact ⟨evidence, Or.inr rfl⟩
    · rename_i noRefutation
      exfalso
      have notEstablished := List.find?_eq_none.mp none _ member
      have notRefuted := List.find?_eq_none.mp noRefutation _ member
      simp only [Evidence.establishes, Evidence.refutes, behavioural, decided, Bool.true_and, beq_iff_eq,
        Option.some.injEq] at notEstablished notRefuted
      cases verdict
      · exact notRefuted rfl
      · exact notEstablished rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

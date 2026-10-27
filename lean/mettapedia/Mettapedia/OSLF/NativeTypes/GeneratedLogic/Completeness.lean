import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# The front door is complete on finite regions

`ask` is exact on an admitted decidable fragment. Take an equation-free language, a premise fuel, and a
term whose closure under steps and parts is finite (a finite list that contains the term and is closed
under the listed successors of its states and the parts of its terms), and where the fuel lists every
state's steps completely. Then:

- **Growing stabilizes** (`grow_stable`). The region grown from the term never repeats a term
  (`grow_nodup`) and stays inside the closure (`grow_subset`), so its length is bounded. It grows in
  every round until it stops, and once it stops it stays.
- **The grown region closes** within as many rounds as the closure has terms (`grow_closed`).
- **So every forward formula is decided** (`decideFrom_complete`), and `ask` answers proved or refuted,
  never open (`ask_decides`). With `ask_proved` and `ask_refuted`, the answer is the truth.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-! ## Adding new terms -/

theorem mem_addNew : ∀ {seen terms : List Pattern} {term : Pattern},
    term ∈ addNew seen terms ↔ term ∈ seen ∨ term ∈ terms
  | seen, [], term => by simp [addNew]
  | seen, first :: rest, term => by
    unfold addNew
    split
    · rename_i known
      rw [mem_addNew]
      constructor
      · rintro (inside | inside)
        · exact Or.inl inside
        · exact Or.inr (List.mem_cons_of_mem _ inside)
      · rintro (inside | inside)
        · exact Or.inl inside
        · rcases List.mem_cons.mp inside with rfl | inside
          · exact Or.inl known
          · exact Or.inr inside
    · rw [mem_addNew]
      simp only [List.mem_append, List.mem_cons]
      tauto

theorem addNew_nodup : ∀ {seen terms : List Pattern}, seen.Nodup → (addNew seen terms).Nodup
  | _, [], distinct => distinct
  | seen, first :: rest, distinct => by
    unfold addNew
    split
    · exact addNew_nodup distinct
    · rename_i fresh
      exact addNew_nodup (List.nodup_append.mpr ⟨distinct, List.nodup_singleton _,
        fun other inside other' inside' same => fresh (by
          rw [List.mem_singleton] at inside'
          subst inside' same
          exact inside)⟩)

/-- Adding nothing new means every term was seen. -/
theorem subset_of_addNew_eq {seen terms : List Pattern} (same : addNew seen terms = seen) :
    ∀ term ∈ terms, term ∈ seen := fun _ inside => same ▸ mem_addNew.mpr (Or.inr inside)

/-! ## Growing a region -/

variable {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ}

/-- What a term adds to a region: its listed successors when it is a state, and its parts. -/
abbrev nextTerms (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (state : Pattern) : List Pattern :=
  (if isStateBool state then (stepsAt relEnv language fuel state).map (·.2) else []) ++ shapeParts state

theorem grow_succ (term : Pattern) (rounds : ℕ) :
    grow relEnv language fuel term (rounds + 1) =
      addNew (grow relEnv language fuel term rounds)
        ((grow relEnv language fuel term rounds).flatMap (nextTerms relEnv language fuel)) :=
  rfl

theorem grow_nodup (term : Pattern) : ∀ rounds, (grow relEnv language fuel term rounds).Nodup
  | 0 => List.nodup_singleton term
  | rounds + 1 => by
    rw [grow_succ]
    exact addNew_nodup (grow_nodup term rounds)

/-- **A closure of a term**: a list that contains it, the listed successors of each of its states, and the
parts of each of its terms. -/
structure Closure (relEnv : RelationEnv) (language : LanguageDef) (fuel : ℕ) (term : Pattern)
    (closure : List Pattern) : Prop where
  start : term ∈ closure
  closed : ∀ state ∈ closure, ∀ other ∈ nextTerms relEnv language fuel state, other ∈ closure
  listed : ∀ state ∈ closure, isStateBool state = true → enough relEnv language fuel state = true

variable {term : Pattern} {closure : List Pattern}

theorem grow_subset (bounded : Closure relEnv language fuel term closure) :
    ∀ rounds, ∀ other ∈ grow relEnv language fuel term rounds, other ∈ closure
  | 0, other, inside => by
    rw [show grow relEnv language fuel term 0 = [term] from rfl, List.mem_singleton] at inside
    exact inside ▸ bounded.start
  | rounds + 1, other, inside => by
    rw [grow_succ, mem_addNew] at inside
    rcases inside with inside | inside
    · exact grow_subset bounded rounds other inside
    · obtain ⟨state, member, next⟩ := List.mem_flatMap.mp inside
      exact bounded.closed state (grow_subset bounded rounds state member) other next

theorem grow_length_le (bounded : Closure relEnv language fuel term closure) (rounds : ℕ) :
    (grow relEnv language fuel term rounds).length ≤ closure.length :=
  ((grow_nodup term rounds).subperm fun other inside => grow_subset bounded rounds other inside).length_le

/-- A round that adds nothing is a fixed point: the next rounds add nothing either. -/
theorem grow_stays {rounds : ℕ}
    (still : grow relEnv language fuel term (rounds + 1) = grow relEnv language fuel term rounds) :
    ∀ extra, grow relEnv language fuel term (rounds + extra) = grow relEnv language fuel term rounds
  | 0 => rfl
  | extra + 1 => by
    rw [← Nat.add_assoc, grow_succ, grow_stays still extra, ← grow_succ, still]

/-- Each round adds a term or adds nothing. -/
theorem grow_grows_or_stays (term : Pattern) (rounds : ℕ) :
    grow relEnv language fuel term (rounds + 1) = grow relEnv language fuel term rounds ∨
      (grow relEnv language fuel term rounds).length < (grow relEnv language fuel term (rounds + 1)).length := by
  obtain ⟨extra, same⟩ := addNew_extends (grow relEnv language fuel term rounds)
    ((grow relEnv language fuel term rounds).flatMap (nextTerms relEnv language fuel))
  rw [grow_succ, same]
  cases extra with
  | nil => exact Or.inl (List.append_nil _)
  | cons first rest => exact Or.inr (by simp)

/-- If no round up to this one stopped, the region has more terms than rounds. -/
theorem grow_length_of_growing (term : Pattern) : ∀ rounds,
    (∀ earlier < rounds, grow relEnv language fuel term (earlier + 1) ≠ grow relEnv language fuel term earlier) →
      rounds + 1 ≤ (grow relEnv language fuel term rounds).length
  | 0, _ => Nat.succ_le_of_lt (grow_length_pos relEnv language fuel term 0)
  | rounds + 1, growing => by
    have previous := grow_length_of_growing term rounds fun earlier below => growing earlier (by omega)
    rcases grow_grows_or_stays (relEnv := relEnv) (language := language) (fuel := fuel) term rounds with
      still | longer
    · exact absurd still (growing rounds (by omega))
    · omega

/-- **Growing stabilizes** before as many rounds as the closure has terms. -/
theorem grow_stable (bounded : Closure relEnv language fuel term closure) :
    ∃ rounds < closure.length,
      grow relEnv language fuel term (rounds + 1) = grow relEnv language fuel term rounds := by
  by_contra never
  simp only [not_exists, not_and] at never
  have long := grow_length_of_growing (relEnv := relEnv) (language := language) (fuel := fuel) term closure.length
    fun earlier below => never earlier below
  have short := grow_length_le bounded closure.length
  omega

/-- A region that adds nothing in a round, inside a closure, is closed. -/
theorem closedRegion_of_still (bounded : Closure relEnv language fuel term closure) {rounds : ℕ}
    (still : grow relEnv language fuel term (rounds + 1) = grow relEnv language fuel term rounds) :
    closedRegion relEnv language fuel (grow relEnv language fuel term rounds) = true := by
  have inside := subset_of_addNew_eq (by rw [← grow_succ]; exact still)
  simp only [closedRegion, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨grow_nodup term rounds, fun state member => ⟨?_, fun part partMember => ?_⟩⟩
  · by_cases isState : isStateBool state = true
    · refine Or.inr ⟨bounded.listed state (grow_subset bounded rounds state member) isState, fun entry entryMember => ?_⟩
      exact inside entry.2 (List.mem_flatMap.mpr ⟨state, member,
        List.mem_append_left _ (by rw [if_pos isState]; exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩)⟩)
    · exact Or.inl (by simpa using isState)
  · exact inside part (List.mem_flatMap.mpr ⟨state, member, List.mem_append_right _ partMember⟩)

/-- **The grown region closes** once the rounds reach the closure's size. -/
theorem grow_closed (bounded : Closure relEnv language fuel term closure) {rounds : ℕ}
    (enoughRounds : closure.length ≤ rounds) :
    closedRegion relEnv language fuel (grow relEnv language fuel term rounds) = true := by
  obtain ⟨stable, below, still⟩ := grow_stable bounded
  have same := grow_stays still (rounds - stable)
  rw [show stable + (rounds - stable) = rounds by omega] at same
  rw [same]
  exact closedRegion_of_still bounded still

/-- **Every forward formula is decided**, and the verdict is the truth. -/
theorem decideFrom_complete (free : language.isEquationFree = true) (bounded : Closure relEnv language fuel term closure)
    {formula : Formula 0} (forward : formula.forward = true) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds) :
    ∃ verdict, decideFrom relEnv language fuel formula term rounds = some verdict ∧
      (verdict = true ↔ (referenceStructure relEnv language).sat Env.closed formula term) := by
  have closed := grow_closed bounded enoughRounds
  have decided : decideFrom relEnv language fuel formula term rounds =
      some ((exploration relEnv language fuel (grow relEnv language fuel term rounds)).check formula
        ⟨0, grow_length_pos relEnv language fuel term rounds⟩) := by
    unfold decideFrom
    rw [if_pos closed]
  exact ⟨_, decided, decideFrom_sound free forward decided⟩

variable {signature : Mettapedia.OSLF.Framework.FiniteModels.Signature}

/-- **`ask` decides**: on a finite region it answers proved or refuted, never open. -/
theorem ask_decides (free : language.isEquationFree = true) (bounded : Closure relEnv language fuel term closure)
    {formula : Formula 0} (forward : formula.forward = true) {rounds : ℕ} (enoughRounds : closure.length ≤ rounds)
    (hint : Option CertificateCandidate) :
    ∃ evidence, ask relEnv signature language fuel formula term hint rounds = .proved evidence ∨
      ask relEnv signature language fuel formula term hint rounds = .refuted evidence := by
  obtain ⟨verdict, decided, -⟩ := decideFrom_complete free bounded forward enoughRounds
  have member : Evidence.closedRegion rounds ∈ gathered signature language formula term hint rounds := by
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
      simp only [Evidence.establishes, Evidence.refutes, free, forward, decided] at notEstablished notRefuted
      cases verdict
      · exact notRefuted rfl
      · exact notEstablished rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic

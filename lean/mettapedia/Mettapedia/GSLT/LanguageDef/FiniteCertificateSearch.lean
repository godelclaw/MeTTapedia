import Mettapedia.GSLT.LanguageDef.ProofSystems

/-!
# Finite certificate search and proof-length transport

`words` explicitly enumerates all binary certificates up to a length bound.
Search calls the submitted checker on this finite collection. A negative
result excludes only this collection, unless a separately proved sufficient
proof-length bound is available.

The search space has exactly `2^(bound+1)-1` candidates. This is a count of
candidate checks, not a bound on the machine time of one candidate check.
Size simulation transports sufficient search bounds, but does not make the
search polynomial or compute a shortest compressed proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FiniteCertificateSearch

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Polynomial

/-- All binary words of length at most the supplied bound. -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: ((words n).map (false :: ·) ++ (words n).map (true :: ·))

theorem mem_words (word : List Bool) (bound : Nat) :
    word ∈ words bound ↔ word.length ≤ bound := by
  induction bound generalizing word with
  | zero => simp [words]
  | succ bound ih =>
      cases word with
      | nil => simp [words]
      | cons bit rest =>
          cases bit <;> simp [words, ih]

theorem words_count (bound : Nat) : (words bound).length + 1 = 2 ^ (bound + 1) := by
  induction bound with
  | zero => simp [words]
  | succ bound ih =>
      simp only [words, List.length_cons, List.length_append, List.length_map]
      rw [Nat.pow_succ]
      omega

variable {Claim : Type*}

def search (checker : Checker Claim (List Bool)) (claim : Claim) (bound : Nat) :
    Option (List Bool) :=
  (words bound).find? (checker.check claim)

theorem found_checked (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) (word : List Bool)
    (found : search checker claim bound = some word) : checker.check claim word = true :=
  List.find?_some found

theorem found_size (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) (word : List Bool)
    (found : search checker claim bound = some word) : word.length ≤ bound :=
  (mem_words word bound).mp (List.mem_of_find?_eq_some found)

theorem search_isSome_iff (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) :
    (search checker claim bound).isSome = true ↔
      ∃ word, word.length ≤ bound ∧ checker.check claim word = true := by
  simp only [search, List.find?_isSome, mem_words]

theorem search_none_iff (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) : search checker claim bound = none ↔
      ∀ word, word.length ≤ bound → checker.check claim word = false := by
  simp [search, List.find?_eq_none, mem_words]

theorem search_monotone (checker : Checker Claim (List Bool)) (claim : Claim)
    {first second : Nat} (larger : first ≤ second)
    (found : (search checker claim first).isSome = true) :
    (search checker claim second).isSome = true := by
  obtain ⟨word, size, checked⟩ := (search_isSome_iff checker claim first).mp found
  exact (search_isSome_iff checker claim second).mpr ⟨word, size.trans larger, checked⟩

/-- Exhaustion is only a length-bounded exclusion. -/
theorem larger_certificate_survives (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) (word : List Bool)
    (empty : search checker claim bound = none) (checked : checker.check claim word = true) :
    bound < word.length := by
  by_contra small
  have refused := (search_none_iff checker claim bound).mp empty word (by omega)
  rw [checked] at refused
  cases refused

theorem eventual_search_iff (checker : Checker Claim (List Bool)) (claim : Claim) :
    (∃ bound, (search checker claim bound).isSome = true) ↔
      ∃ word, checker.check claim word = true := by
  constructor
  · rintro ⟨bound, found⟩
    obtain ⟨word, _, checked⟩ := (search_isSome_iff checker claim bound).mp found
    exact ⟨word, checked⟩
  · rintro ⟨word, checked⟩
    exact ⟨word.length,
      (search_isSome_iff checker claim word.length).mpr ⟨word, le_rfl, checked⟩⟩

/-- A sufficient bound is additional evidence about a specific checker and
claim; soundness or existence of proofs alone does not provide it. -/
def SufficientBound (checker : Checker Claim (List Bool)) (claim : Claim) (bound : Nat) : Prop :=
  (∃ word, checker.check claim word = true) →
    ∃ word, word.length ≤ bound ∧ checker.check claim word = true

theorem sufficient_search_exact (checker : Checker Claim (List Bool))
    (claim : Claim) (bound : Nat) (sufficient : SufficientBound checker claim bound) :
    (search checker claim bound).isSome = true ↔
      ∃ word, checker.check claim word = true := by
  rw [search_isSome_iff]
  exact ⟨fun ⟨word, _, checked⟩ => ⟨word, checked⟩, sufficient⟩

/-- Once a sufficient bound and exact replay for derivability are proved,
finite exhaustion really can establish underivability of that claim. -/
theorem sufficient_refusal (checker : Checker Claim (List Bool))
    (Derivable : Claim → Prop) (authority : checker.Authority Derivable)
    (claim : Claim) (bound : Nat) (sufficient : SufficientBound checker claim bound)
    (empty : search checker claim bound = none) : ¬ Derivable claim := by
  intro derivable
  have found := (sufficient_search_exact checker claim bound sufficient).mpr
    (authority.complete claim derivable)
  simp [empty] at found

section Simulation

variable {OtherCertificate : Type*}

/-- Polynomial certificate expansion supplies an explicit target search
radius. It does not bound the number of target candidates polynomially. -/
theorem sizeSimulation_search_bound
    {target : SizedChecker Claim (List Bool)}
    {source : SizedChecker Claim OtherCertificate}
    (simulation : SizeSimulation target source)
    (wordSize : target.certificateSize = List.length) :
    ∃ polynomial : ℕ[X], ∀ claim certificate,
      source.check claim certificate = true →
        (search target.toChecker claim
          (polynomial.eval (source.inputSize (claim, certificate)))).isSome = true := by
  obtain ⟨polynomial, bound⟩ := simulation.sizeBound
  refine ⟨polynomial, fun claim certificate accepted => ?_⟩
  apply (search_isSome_iff _ _ _).mpr
  refine ⟨simulation.translate claim certificate, ?_, simulation.preserves _ _ accepted⟩
  simpa only [← wordSize] using bound (claim, certificate)

end Simulation

namespace Controls

/-- This checker has a unique one-bit proof. -/
def oneBitChecker : Checker Bool (List Bool) where
  check claim word := decide (word = [claim])

theorem positive : search oneBitChecker true 1 = some [true] := by decide

theorem exhausted_but_provable :
    search oneBitChecker true 0 = none ∧ oneBitChecker.check true [true] = true := by decide

theorem wrong_bit_refused : oneBitChecker.check true [false] = false := by decide

theorem two_bit_search_count : (words 2).length = 7 := by decide

end Controls


/-! ## Retained discovery of complete certificate articles

Each slot computes a finite proposal list. The checker revalidates every
new proposal, and equality deduplicates only whole certificate articles.
Neither a search slot nor an emitted article denotes an operational firing.
The retained cursor prevents a resumed run from replaying earlier slots.
-/
namespace Retained

variable {Certificate : Type*} [DecidableEq Certificate]

structure State (Certificate : Type*) where
  cursor : Nat
  articles : List Certificate
  deriving Repr

def initial : State Certificate := ⟨0, []⟩

def step (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) : State Certificate :=
  ⟨state.cursor + 1,
    (state.articles ++ (propose state.cursor).filter (checker.check claim)).eraseDups⟩

def run (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) : Nat → State Certificate → State Certificate
  | 0, state => state
  | budget + 1, state => run checker propose claim budget (step checker propose claim state)

def search (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) : State Certificate :=
  run checker propose claim budget initial

theorem run_add (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (first second : Nat) (state : State Certificate) :
    run checker propose claim (first + second) state =
      run checker propose claim second (run checker propose claim first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simp only [Nat.succ_add, run, ih]

theorem run_cursor (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (state : State Certificate) :
    (run checker propose claim budget state).cursor = state.cursor + budget := by
  induction budget generalizing state with
  | zero => simp only [run, Nat.add_zero]
  | succ budget ih => simp only [run, ih, step, Nat.add_assoc, Nat.add_comm 1 budget]

theorem mem_step (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) (article : Certificate) :
    article ∈ (step checker propose claim state).articles ↔
      article ∈ state.articles ∨ article ∈ propose state.cursor ∧ checker.check claim article = true := by
  simp only [step, List.mem_eraseDups, List.mem_append, List.mem_filter]

private theorem eraseDups_distinct (values : List Certificate) : values.eraseDups.Nodup := by
  cases values with
  | nil => exact .nil
  | cons value values =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups, List.mem_filter]
      · exact eraseDups_distinct _
termination_by values.length
decreasing_by
  have shorter := List.length_filter_le (fun element : Certificate => !element == value) values
  simp only [List.length_cons]
  omega

theorem step_nodup (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) :
    (step checker propose claim state).articles.Nodup := eraseDups_distinct _

theorem run_nodup (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (state : State Certificate) (distinct : state.articles.Nodup) :
    (run checker propose claim budget state).articles.Nodup := by
  induction budget generalizing state with
  | zero => exact distinct
  | succ budget ih => exact ih _ (step_nodup checker propose claim state)

/-- Exact bounded discovery, including every earlier retained article. -/
theorem mem_run (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (state : State Certificate) (article : Certificate) :
    article ∈ (run checker propose claim budget state).articles ↔
      article ∈ state.articles ∨ ∃ offset, offset < budget ∧
        article ∈ propose (state.cursor + offset) ∧ checker.check claim article = true := by
  induction budget generalizing state with
  | zero => simp only [run, Nat.not_lt_zero, false_and, exists_false, or_false]
  | succ budget ih =>
      rw [run, ih, mem_step]
      constructor
      · rintro ((old | ⟨proposed, checked⟩) | ⟨offset, small, proposed, checked⟩)
        · exact Or.inl old
        · exact Or.inr ⟨0, by omega, by simpa only [Nat.add_zero] using proposed, checked⟩
        · exact Or.inr ⟨offset + 1, by omega, by
            simpa only [step, Nat.add_assoc, Nat.add_comm 1 offset] using proposed, checked⟩
      · rintro (old | ⟨offset, small, proposed, checked⟩)
        · exact Or.inl (Or.inl old)
        · cases offset with
          | zero => exact Or.inl (Or.inr ⟨by simpa only [Nat.add_zero] using proposed, checked⟩)
          | succ offset => exact Or.inr ⟨offset, by omega, by
              simpa only [step, Nat.add_assoc, Nat.add_comm 1 offset] using proposed, checked⟩

theorem mem_search (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (article : Certificate) :
    article ∈ (search checker propose claim budget).articles ↔
      ∃ position, position < budget ∧ article ∈ propose position ∧ checker.check claim article = true := by
  simp only [search, mem_run, initial, List.not_mem_nil, false_or, Nat.zero_add]

/-- A caller-supplied stream does not receive a semantic completeness field;
coverage follows from a concrete proposed slot for the particular article. -/
theorem discovered_at (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (article : Certificate) (position : Nat)
    (proposed : article ∈ propose position) (checked : checker.check claim article = true) :
    article ∈ (search checker propose claim (position + 1)).articles :=
  (mem_search checker propose claim _ article).mpr ⟨position, by omega, proposed, checked⟩

theorem run_sound (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (state : State Certificate)
    (valid : ∀ article ∈ state.articles, checker.check claim article = true) :
    ∀ article ∈ (run checker propose claim budget state).articles, checker.check claim article = true := by
  intro article found
  rcases (mem_run checker propose claim budget state article).mp found with old | ⟨_, _, _, checked⟩
  · exact valid article old
  · exact checked

theorem search_sound (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) :
    ∀ article ∈ (search checker propose claim budget).articles, checker.check claim article = true :=
  run_sound checker propose claim budget initial (by intro article missing; cases missing)


/-- Reachability is generated by actual search transitions, independently
of any semantic assertion about the discovered articles. -/
inductive Reachable (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) : State Certificate → Prop where
  | initial : Reachable checker propose claim initial
  | step {state : State Certificate} : Reachable checker propose claim state →
      Reachable checker propose claim (step checker propose claim state)

theorem run_reachable (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (budget : Nat) (state : State Certificate)
    (reached : Reachable checker propose claim state) :
    Reachable checker propose claim (run checker propose claim budget state) := by
  induction budget generalizing state with
  | zero => exact reached
  | succ budget ih => exact ih _ (.step reached)

/-- The same retained cursor identifies the original computed search prefix;
forged cursors cannot be justified by a valid article list alone. -/
theorem reachable_eq_search (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) (reached : Reachable checker propose claim state) :
    state = search checker propose claim state.cursor := by
  induction reached with
  | initial => rfl
  | @step state reached ih =>
      change step checker propose claim state =
        run checker propose claim (state.cursor + 1) initial
      rw [run_add]
      change step checker propose claim state = step checker propose claim (search checker propose claim state.cursor)
      rw [← ih]

theorem reachable_sound (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) (reached : Reachable checker propose claim state) :
    ∀ article ∈ state.articles, checker.check claim article = true := by
  rw [reachable_eq_search checker propose claim state reached]
  exact search_sound checker propose claim state.cursor

theorem reachable_nodup (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (state : State Certificate) (reached : Reachable checker propose claim state) :
    state.articles.Nodup := by
  rw [reachable_eq_search checker propose claim state reached]
  exact run_nodup checker propose claim state.cursor initial .nil

theorem search_monotone (checker : Checker Claim Certificate) (propose : Nat → List Certificate)
    (claim : Claim) (first second : Nat) (larger : first ≤ second) :
    (search checker propose claim first).articles ⊆ (search checker propose claim second).articles := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le larger
  intro article found
  change article ∈ (run checker propose claim (first + extra) initial).articles
  rw [run_add]
  exact (mem_run checker propose claim extra _ article).mpr (Or.inl found)

end Retained

end Mettapedia.GSLT.LanguageDef.FiniteCertificateSearch

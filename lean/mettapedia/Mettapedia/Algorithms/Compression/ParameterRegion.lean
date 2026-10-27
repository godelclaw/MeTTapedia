import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mettapedia.Algorithms.Compression.CostedArtifact

/-!
# Finite parameter regions with resumable traversal

Each domain is an ordered list of typed alternatives. Equal alternatives are
separate occurrences. The frontier expands one frame per tick rather than
materializing the Cartesian product at preparation. A simple product supplies
an independent specification of emitted order and remaining work.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ParameterRegion

variable {α : Type*}

def product : List (List α) → List (List α)
  | [] => [[]]
  | choices :: rest => choices.flatMap fun choice => (product rest).map (choice :: ·)

abbrev Frame (α : Type*) := List α × List (List α)
abbrev Frontier (α : Type*) := List (Frame α)

def values (frontier : Frontier α) : List (List α) :=
  frontier.flatMap fun frame => (product frame.2).map (frame.1 ++ ·)

def children (chosen : List α) (choices : List α) (remaining : List (List α)) : Frontier α :=
  choices.map fun choice => (chosen ++ [choice], remaining)

inductive Tick (α : Type*) where
  | done
  | pending (next : Frontier α)
  | yield (answer : List α) (next : Frontier α)

def tick : Frontier α → Tick α
  | [] => .done
  | (chosen, []) :: rest => .yield chosen rest
  | (chosen, choices :: remaining) :: rest => .pending (children chosen choices remaining ++ rest)

theorem values_children (chosen choices : List α) (remaining : List (List α)) :
    values (children chosen choices remaining) =
      (product (choices :: remaining)).map (chosen ++ ·) := by
  simp only [values, children, List.flatMap_map, product, List.map_flatMap, List.map_map]
  simp only [Function.comp_def, List.append_assoc, List.singleton_append]

theorem pending_preserves {before after : Frontier α} (found : tick before = .pending after) :
    values after = values before := by
  cases before with
  | nil => simp [tick] at found
  | cons frame rest =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => simp [tick] at found
      | cons choices remaining =>
          cases found
          simp only [values, List.flatMap_append, List.flatMap_cons]
          exact congrArg (· ++ values rest) (values_children chosen choices remaining)

theorem yield_preserves {before after : Frontier α} {answer : List α}
    (found : tick before = .yield answer after) :
    values before = answer :: values after := by
  cases before with
  | nil => simp [tick] at found
  | cons frame rest =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => cases found; simp [values, product]
      | cons choices remaining => simp [tick] at found

theorem done_iff (frontier : Frontier α) : tick frontier = .done ↔ frontier = [] := by
  cases frontier with
  | nil => simp [tick]
  | cons frame rest =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains <;> simp [tick]

def size : List (List α) → Nat
  | [] => 1
  | choices :: remaining => 1 + choices.length * size remaining

def work : Frontier α → Nat
  | [] => 0
  | frame :: rest => size frame.2 + work rest

theorem size_positive (domains : List (List α)) : 0 < size domains := by
  cases domains <;> simp [size]

theorem work_append (first second : Frontier α) : work (first ++ second) = work first + work second := by
  induction first with
  | nil => simp [work]
  | cons frame rest ih => simp [work, ih, Nat.add_assoc]

theorem work_children (chosen choices : List α) (remaining : List (List α)) :
    work (children chosen choices remaining) = choices.length * size remaining := by
  induction choices with
  | nil => simp [children, work]
  | cons head rest ih =>
      change size remaining + work (children chosen rest remaining) =
        (rest.length + 1) * size remaining
      rw [ih, Nat.add_mul]
      omega

theorem work_eq_zero_iff (frontier : Frontier α) : work frontier = 0 ↔ frontier = [] := by
  cases frontier with
  | nil => simp [work]
  | cons frame rest =>
      have positive := size_positive frame.2
      constructor
      · intro empty
        simp only [work] at empty
        omega
      · intro empty
        cases empty

theorem pending_decreases {before after : Frontier α} (found : tick before = .pending after) :
    work after < work before := by
  cases before with
  | nil => simp [tick] at found
  | cons frame rest =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => simp [tick] at found
      | cons choices remaining =>
          cases found
          rw [work_append, work_children, work, size]
          omega

theorem yield_decreases {before after : Frontier α} {answer : List α}
    (found : tick before = .yield answer after) : work after < work before := by
  cases before with
  | nil => simp [tick] at found
  | cons frame rest =>
      obtain ⟨chosen, domains⟩ := frame
      cases domains with
      | nil => cases found; simp [work, size]
      | cons choices remaining => simp [tick] at found

def run : Nat → Frontier α → List (List α) × Frontier α
  | 0, frontier => ([], frontier)
  | fuel + 1, frontier =>
      match tick frontier with
      | .done => ([], [])
      | .pending next => run fuel next
      | .yield answer next =>
          let later := run fuel next
          (answer :: later.1, later.2)

theorem run_empty (fuel : Nat) : run fuel ([] : Frontier α) = ([], []) := by
  cases fuel <;> rfl

theorem run_conserves (fuel : Nat) (frontier : Frontier α) :
    (run fuel frontier).1 ++ values (run fuel frontier).2 = values frontier := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
      cases found : tick frontier with
      | done =>
          have empty := (done_iff frontier).mp found
          subst frontier
          simp [run, tick, values]
      | pending next => simpa [run, found, pending_preserves found] using ih next
      | yield answer next =>
          rw [yield_preserves found]
          simpa [run, found] using congrArg (answer :: ·) (ih next)

theorem run_complete (fuel : Nat) (frontier : Frontier α) (enough : work frontier ≤ fuel) :
    (run fuel frontier).2 = [] := by
  induction fuel generalizing frontier with
  | zero =>
      have empty := (work_eq_zero_iff frontier).mp (by omega)
      subst frontier
      rfl
  | succ fuel ih =>
      cases found : tick frontier with
      | done => simp [run, found]
      | pending next =>
          have smaller := pending_decreases found
          simpa [run, found] using ih next (by omega)
      | yield answer next =>
          have smaller := yield_decreases found
          simpa [run, found] using ih next (by omega)

theorem complete_order (frontier : Frontier α) :
    (run (work frontier) frontier).1 = values frontier := by
  have conserved := run_conserves (work frontier) frontier
  rw [run_complete _ _ (Nat.le_refl _)] at conserved
  simpa [values] using conserved

theorem run_resume (first second : Nat) (frontier : Frontier α) :
    run (first + second) frontier =
      let before := run first frontier
      let after := run second before.2
      (before.1 ++ after.1, after.2) := by
  induction first generalizing frontier with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add]
      cases found : tick frontier with
      | done => simp [run, found, run_empty]
      | pending next => simpa [run, found] using ih next
      | yield answer next =>
          have equality := congrArg
            (fun result : List (List α) × Frontier α => (answer :: result.1, result.2)) (ih next)
          simpa [run, found] using equality

theorem complete_product (domains : List (List α)) :
    (run (work [([], domains)]) [([], domains)]).1 = product domains := by
  rw [complete_order]
  simp [values]

def fit {Artifact : Type} (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (propose : List α → Artifact) (fuel : Nat) (frontier : Frontier α) : Artifact :=
  CostedArtifact.refine valid cost current ((run fuel frontier).1.map propose)

theorem fit_preserves {Artifact : Type} (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (propose : List α → Artifact) (fuel : Nat) (frontier : Frontier α)
    (admitted : valid current = true) :
    valid (fit valid cost current propose fuel frontier) = true ∧
      cost (fit valid cost current propose fuel frontier) ≤ cost current :=
  CostedArtifact.refine_preserves valid cost current _ admitted

theorem fit_resume {Artifact : Type} (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (propose : List α → Artifact) (first second : Nat) (frontier : Frontier α) :
    fit valid cost current propose (first + second) frontier =
      fit valid cost (fit valid cost current propose first frontier) propose second
        (run first frontier).2 := by
  have emitted := congrArg Prod.fst (run_resume first second frontier)
  simp only at emitted
  simp only [fit, emitted, List.map_append, CostedArtifact.refine_append]

theorem fit_complete_optimal {Artifact : Type} (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (propose : List α → Artifact) (domains : List (List α))
    (admitted : valid current = true) (assignment : List α)
    (present : assignment ∈ product domains) (checked : valid (propose assignment) = true) :
    cost (fit valid cost current propose (work [([], domains)]) [([], domains)]) ≤
      cost (propose assignment) := by
  unfold fit
  rw [complete_product]
  exact CostedArtifact.refine_optimal_in_region valid cost current _ admitted
    (propose assignment) (List.mem_map.mpr ⟨assignment, present, rfl⟩) checked

theorem duplicate_alternatives_are_occurrences (a b : α) :
    (run (work [([], [[a, a], [b, b]])]) [([], [[a, a], [b, b]])]).1 =
      [[a, b], [a, b], [a, b], [a, b]] := by
  rw [complete_order]
  rfl

theorem empty_domain_is_not_an_answer :
    (run (work [([], [([] : List α)])]) [([], [([] : List α)])]).1 = [] := by
  rw [complete_order]
  rfl

theorem no_domains_has_one_empty_assignment :
    (run (α := α) (work (α := α) [([], [])]) [([], [])]).1 = [[]] := rfl

theorem zero_budget_is_not_exhaustion (a : α) :
    (run 0 [([], [[a]])]).2 ≠ [] := by simp [run]

end Mettapedia.Algorithms.Compression.ParameterRegion

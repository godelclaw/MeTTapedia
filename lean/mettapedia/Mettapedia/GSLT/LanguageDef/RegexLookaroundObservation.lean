import Mettapedia.GSLT.LanguageDef.RegexDependentObservation

/-!
# Completed local observations and variable-length lookbehind

An assertion selects its local answer before returning to its caller. Positive
assertions export that selected capture state without consuming caller input;
negative assertions export nothing and require closed local absence. Forward
lookbehind compares ordinary written-order priorities over all starts ending
at the assertion point. Reverse lookbehind is a separately named observer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexDependentObservation

open Mettapedia.Computability.RegularLanguages
open RegexSelectionCorrespondence (Action)

structure Winner (states groups length : Nat) where
  configuration : Configuration states groups length
  choices : List Bool
  start : Fin (length + 1)

def sufficientFuel (states groups length : Nat) : Nat :=
  Fintype.card (OrderedGraphSearch.Point (Configuration states groups length) 0) + 2

/-- This is the actual proved finite-state driver, with an earned closure
bound. The bound is not exposed as a policy limiting admitted patterns. -/
def complete {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) : Option (Winner states groups length) :=
  match result : run step eligible (sufficientFuel states groups length) first with
  | .found last _ => some ⟨last.point.1, last.choices, first.position⟩
  | .absent _ => none
  | .incomplete => False.elim (run_ne_incomplete step eligible first
      (sufficientFuel states groups length) (by simp [sufficientFuel]) result)

theorem complete_none_iff {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) :
    complete step eligible first = none ↔
      ¬ ∃ code points last tag,
        RegexSelectionCorrespondence.Trace (graph step) probe (fun thread => eligible thread.point.1)
          (initial first) code points last tag := by
  have absent := run_absent_iff step eligible first (sufficientFuel states groups length)
    (by simp [sufficientFuel])
  have terminated := run_ne_incomplete step eligible first (sufficientFuel states groups length)
    (by simp [sufficientFuel])
  unfold complete
  split
  · simp_all
  · simp_all
  · contradiction

theorem complete_some_iff {states groups length : Nat}
    (step : Configuration states groups length → Action (Configuration states groups length) Unit)
    (eligible : Configuration states groups length → Bool)
    (first : Configuration states groups length) (winner : Winner states groups length) :
    complete step eligible first = some winner ↔
      ∃ last : RegexTaggedGraph.Thread (Configuration states groups length) 0,
        RegexSelectionCorrespondence.LeastSimple (graph step) probe
          (fun thread => eligible thread.point.1) (initial first) last ∧
        RegexPikeVM.terminal (graph step) last = some () ∧
        winner = ⟨last.point.1, last.choices, first.position⟩ := by
  have terminated := run_ne_incomplete step eligible first (sufficientFuel states groups length)
    (by simp [sufficientFuel])
  constructor
  · intro completed
    unfold complete at completed
    split at completed
    · rename_i last tag returned
      cases tag
      have selected := (run_selected_iff step eligible first last
        (sufficientFuel states groups length) (by simp [sufficientFuel])).mp returned
      exact ⟨last, selected.1, selected.2, (Option.some.inj completed).symm⟩
    · contradiction
    · contradiction
  · rintro ⟨last, selected, terminal, rfl⟩
    have returned := (run_selected_iff step eligible first last
      (sufficientFuel states groups length) (by simp [sufficientFuel])).mpr ⟨selected, terminal⟩
    unfold complete
    split
    · rename_i other tag result
      have same := result.symm.trans returned
      cases same
      rfl
    · rename_i seen result
      cases result.symm.trans returned
    · contradiction

/-- Strict lexicographic branch priority, with shorter equal prefixes first. -/
def codeBefore : List Bool → List Bool → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | first :: left, second :: right =>
      if first = second then codeBefore left right else !first && second

theorem codeBefore_iff (first second : List Bool) : codeBefore first second = true ↔ first < second := by
  induction first generalizing second with
  | nil => cases second <;> simp [codeBefore]
  | cons first rest ih =>
      cases second with
      | nil => simp [codeBefore]
      | cons second tail =>
          cases first <;> cases second <;> simp [codeBefore, List.cons_lt_cons_iff, ih]

def preferred {states groups length : Nat} (first second : Winner states groups length) : Bool :=
  codeBefore first.choices second.choices ||
    (first.choices == second.choices && second.start.val < first.start.val)

def choose {states groups length : Nat} (first second : Winner states groups length) : Winner states groups length :=
  if preferred first second then first else second

theorem choose_is_candidate {states groups length : Nat} (first second : Winner states groups length) :
    choose first second = first ∨ choose first second = second := by
  unfold choose
  split <;> simp

def best {states groups length : Nat} : List (Winner states groups length) → Option (Winner states groups length)
  | [] => none
  | first :: rest => some (rest.foldl choose first)

theorem fold_choose_member {states groups length : Nat} (first : Winner states groups length)
    (rest : List (Winner states groups length)) : rest.foldl choose first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons next rest ih =>
      have member := ih (choose first next)
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with same | tail
      · rw [same]
        rcases choose_is_candidate first next with same | same <;> simp [same]
      · simp [tail]

theorem best_present {states groups length : Nat} (candidates : List (Winner states groups length))
    (winner : Winner states groups length) (selected : best candidates = some winner) : winner ∈ candidates := by
  cases candidates with
  | nil => simp [best] at selected
  | cons first rest =>
      simp only [best, Option.some.injEq] at selected
      subst winner
      exact fold_choose_member first rest

theorem best_none_iff {states groups length : Nat} (candidates : List (Winner states groups length)) :
    best candidates = none ↔ candidates = [] := by cases candidates <;> simp [best]

def Precedes {states groups length : Nat} (first second : Winner states groups length) : Prop :=
  first.choices < second.choices ∨ first.choices = second.choices ∧ second.start ≤ first.start

theorem precedes_refl {states groups length : Nat} (winner : Winner states groups length) : Precedes winner winner :=
  Or.inr ⟨rfl, le_refl _⟩

theorem precedes_trans {states groups length : Nat} {first middle last : Winner states groups length}
    (before : Precedes first middle) (after : Precedes middle last) : Precedes first last := by
  rcases before with before | ⟨same, starts⟩
  · rcases after with after | ⟨same, _⟩
    · exact Or.inl (lt_trans before after)
    · exact Or.inl (same ▸ before)
  · rcases after with after | ⟨other, starts'⟩
    · exact Or.inl (same.symm ▸ after)
    · exact Or.inr ⟨same.trans other, starts'.trans starts⟩

theorem choose_precedes {states groups length : Nat} (first second : Winner states groups length) :
    Precedes (choose first second) first ∧ Precedes (choose first second) second := by
  have preferred_iff : preferred first second = true ↔
      first.choices < second.choices ∨ first.choices = second.choices ∧ second.start < first.start := by
    simp only [preferred, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, codeBefore_iff]
    rfl
  by_cases chosen : preferred first second = true
  · simp only [choose, chosen, if_true]
    refine ⟨precedes_refl _, ?_⟩
    rcases preferred_iff.mp chosen with before | ⟨same, starts⟩
    · exact Or.inl before
    · exact Or.inr ⟨same, le_of_lt starts⟩
  · simp only [choose, chosen, Bool.false_eq_true, if_false]
    refine ⟨?_, precedes_refl _⟩
    have notBefore := mt preferred_iff.mpr chosen
    rcases lt_trichotomy first.choices second.choices with before | same | after
    · exact False.elim (notBefore (Or.inl before))
    · exact Or.inr ⟨same.symm, by
        have starts : ¬ second.start < first.start := fun starts => notBefore (Or.inr ⟨same, starts⟩)
        exact le_of_not_gt starts⟩
    · exact Or.inl after

theorem fold_choose_precedes {states groups length : Nat} (first : Winner states groups length)
    (rest : List (Winner states groups length)) :
    ∀ candidate ∈ first :: rest, Precedes (rest.foldl choose first) candidate := by
  induction rest generalizing first with
  | nil =>
      intro candidate member
      have same : candidate = first := by simpa using member
      subst candidate
      exact precedes_refl first
  | cons next rest ih =>
      intro candidate member
      have folded := ih (choose first next)
      have before := folded _ List.mem_cons_self
      have chosen := choose_precedes first next
      rcases List.mem_cons.mp member with same | member
      · subst candidate; exact precedes_trans before chosen.1
      · rcases List.mem_cons.mp member with same | tail
        · subst candidate; exact precedes_trans before chosen.2
        · exact folded candidate (List.mem_cons_of_mem _ tail)

theorem best_minimal {states groups length : Nat} (candidates : List (Winner states groups length))
    (winner : Winner states groups length) (selected : best candidates = some winner) :
    ∀ candidate ∈ candidates, Precedes winner candidate := by
  cases candidates with
  | nil => simp [best] at selected
  | cons first rest =>
      simp only [best, Option.some.injEq] at selected
      subst winner
      exact fold_choose_precedes first rest

abbrev Evaluator (states groups length : Nat) :=
  Direction → (Configuration states groups length → Bool) →
    Configuration states groups length → Option (Winner states groups length)

def behindCandidates {states groups length : Nat} (evaluate : Evaluator states groups length)
    (entry : Fin states) (caller : Configuration states groups length) : List (Winner states groups length) :=
  ((List.finRange (length + 1)).filter fun position => position ≤ caller.position).filterMap fun position =>
    evaluate .forward (fun last => last.position == caller.position)
      { caller with pc := entry, position := position }

def bodyWinner {states groups length : Nat} (evaluate : Evaluator states groups length)
    (kind : LookKind) (entry : Fin states) (caller : Configuration states groups length) :
    Option (Winner states groups length) :=
  match kind with
  | .ahead | .notAhead => evaluate .forward (fun _ => true) { caller with pc := entry }
  | .behind | .notBehind => best (behindCandidates evaluate entry caller)
  | .reverseBehind | .reverseNotBehind => evaluate .reverse (fun _ => true) { caller with pc := entry }

theorem forward_behind_none_iff {states groups length : Nat}
    (evaluate : Evaluator states groups length) (entry : Fin states)
    (caller : Configuration states groups length) :
    bodyWinner evaluate .behind entry caller = none ↔
      ∀ position : Fin (length + 1), position ≤ caller.position →
        evaluate .forward (fun last => last.position == caller.position)
          { caller with pc := entry, position := position } = none := by
  simp only [bodyWinner, best_none_iff, behindCandidates, List.filterMap_eq_nil_iff,
    List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

theorem negative_behind_requires_every_start {states groups length : Nat}
    (evaluate : Evaluator states groups length) (entry : Fin states)
    (caller : Configuration states groups length)
    (absent : bodyWinner evaluate .notBehind entry caller = none) :
    ∀ position : Fin (length + 1), position ≤ caller.position →
      evaluate .forward (fun last => last.position == caller.position)
        { caller with pc := entry, position := position } = none :=
  (forward_behind_none_iff evaluate entry caller).mp absent

/-- Control-only erasure of local priority words. This is not the selected
lookbehind reference: `RegexObservationTrace.rankedEvaluator` retains those
words. Each natural index counts assertion nesting, not execution work. -/
def rankedControlEvaluator {states groups length : Nat}
    (interpretation : Interpretation) (input : Fin length → Nat)
    (program : RankedProgram states groups) : Nat → Evaluator states groups length
  | 0 => fun _ _ _ => none
  | depth + 1 => fun direction eligible first =>
      let body : BodyObservation states groups length := fun kind entry caller =>
        (bodyWinner (rankedControlEvaluator interpretation input program depth) kind entry caller).map Winner.configuration
      complete (fun configuration =>
        if program.rank configuration.pc < depth + 1 then
          action interpretation input direction program.instruction body configuration
        else .dead) eligible first

theorem ranked_observation_uses_smaller_core {states groups : Nat}
    (program : RankedProgram states groups) (pc entry next : Fin states) (kind : LookKind)
    (instruction : program.instruction pc = .look kind entry next) (depth : Nat)
    (admitted : program.rank pc < depth + 1) : program.rank entry < depth := by
  have lower := program.body pc kind entry next instruction
  omega

namespace Controls

private def sample (choices : List Bool) (start : Fin 5) : Winner 1 0 4 :=
  ⟨⟨0, 4, Fin.elim0⟩, choices, start⟩

theorem written_priority_precedes_start_distance :
    (choose (sample [false] 0) (sample [true] 3)).start = 0 := by decide

theorem equal_priority_prefers_nearest_start :
    (choose (sample [false] 0) (sample [false] 3)).start = 3 := by decide

theorem later_start_cannot_override_better_written_branch :
    (choose (sample [true] 3) (sample [false] 0)).choices ≠ [true] := by decide

end Controls

end Mettapedia.GSLT.LanguageDef.RegexDependentObservation

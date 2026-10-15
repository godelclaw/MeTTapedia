import Mettapedia.GSLT.LanguageDef.SubtermMatching
import Mettapedia.GSLT.LanguageDef.BottomUpMatchAutomaton

/-!
# Top-down position derivatives for shared matching

Compiled patterns are finite lists of constructor obligations. A derivative
consumes one shared position observation, refuses a conflicting obligation,
and removes obligations satisfied by that observation. The remaining
obligations are a finite control state; the candidate root is a position
register. This realization uses a fixed preorder scan. It does not implement
the paper's partition-and-lift normalization and independent-task scheduling.

The source structural matcher is used only in the correctness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TopDownMatchDerivatives

open OrderedPatternMatrixCompilation SubtermMatching

universe u
variable {Head : Type u}

structure Obligation (Head : Type u) where
  position : Position
  key : ConstructorKey Head
deriving DecidableEq, Repr

abbrev Observation (Head : Type u) := Obligation Head

def key (subject : Subject Head) : ConstructorKey Head :=
  match subject with | .node h cs => ⟨h, cs.length⟩

def keyAt (subject : Subject Head) (position : Position) : Option (ConstructorKey Head) :=
  (project position subject).map key

mutual
  /-- Compile every rigid pattern node to a position obligation. Wildcards
  introduce no constructor obligation. -/
  def compile : Pattern Head → List (Obligation Head)
    | .wildcard => []
    | .node h cs => ⟨[], ⟨h, cs.length⟩⟩ :: compileChildren 0 cs

  def compileChildren : Nat → List (Pattern Head) → List (Obligation Head)
    | _, [] => []
    | next, p :: ps =>
        (compile p).map (fun o => ⟨next :: o.position, o.key⟩) ++
          compileChildren (next + 1) ps
end

section
variable [DecidableEq Head]

/-- Independent semantics of a finite obligation vector. -/
def valid (read : Position → Option (ConstructorKey Head))
    (obligations : List (Obligation Head)) : Bool :=
  obligations.all (fun o => decide (read o.position = some o.key))

theorem valid_prefix (read : Position → Option (ConstructorKey Head))
    (next : Nat) (obligations : List (Obligation Head)) :
    valid read (obligations.map (fun o => ⟨next :: o.position, o.key⟩)) =
      valid (fun path => read (next :: path)) obligations := by
  simp [valid, List.all_map, Function.comp_def]

/-- Arity disagreement rejects the direct structural vector matcher. -/
theorem structuralMatchList_length (patterns : List (Pattern Head))
    (subjects : List (Subject Head)) (different : patterns.length ≠ subjects.length) :
    structuralMatchList patterns subjects = false := by
  induction patterns generalizing subjects with
  | nil => cases subjects <;> simp_all [structuralMatchList]
  | cons p ps ih =>
      cases subjects with
      | nil => rfl
      | cons s ss =>
          simp only [structuralMatchList]
          rw [ih ss (by simpa using different)]
          simp

mutual
  theorem valid_compile (pattern : Pattern Head) (subject : Subject Head) :
      valid (keyAt subject) (compile pattern) = structuralMatch pattern subject := by
    cases pattern with
    | wildcard => rfl
    | node expected patterns =>
        cases subject with
        | node actual subjects =>
            simp only [compile, valid, List.all_cons, keyAt, project, Option.map_some, key,
              structuralMatch]
            by_cases sameHead : expected = actual
            · subst actual
              by_cases sameLength : patterns.length = subjects.length
              · simp only [sameLength, decide_true, Bool.true_and]
                exact valid_compileChildren expected patterns subjects [] sameLength
              · have mismatch : (⟨expected, subjects.length⟩ : ConstructorKey Head) ≠
                    ⟨expected, patterns.length⟩ := by
                  intro h
                  have := congrArg ConstructorKey.arity h
                  exact sameLength this.symm
                have failed := structuralMatchList_length patterns subjects sameLength
                simp [mismatch, failed]
            · have mismatch : (⟨actual, subjects.length⟩ : ConstructorKey Head) ≠
                  ⟨expected, patterns.length⟩ := by
                intro h
                have := congrArg ConstructorKey.head h
                exact sameHead this.symm
              simp [sameHead, mismatch]

  theorem valid_compileChildren (head : Head) (patterns : List (Pattern Head))
      (subjects initialChildren : List (Subject Head))
      (sameLength : patterns.length = subjects.length) :
      valid (keyAt (.node head (initialChildren ++ subjects)))
        (compileChildren initialChildren.length patterns) = structuralMatchList patterns subjects := by
    cases patterns with
    | nil =>
        cases subjects with
        | nil => rfl
        | cons s ss => simp at sameLength
    | cons p ps =>
        cases subjects with
        | nil => simp at sameLength
        | cons s ss =>
            simp only [compileChildren, valid, List.all_append]
            rw [← valid, valid_prefix]
            have projected : (fun path => keyAt
                (.node head (initialChildren ++ s :: ss))
                (initialChildren.length :: path)) = keyAt s := by
              funext path
              simp [keyAt, project]
            rw [projected, valid_compile]
            have tail := valid_compileChildren head ps ss (initialChildren ++ [s])
              (by simpa using sameLength)
            simpa [List.append_assoc, valid, keyAt, project, structuralMatchList] using
              congrArg (fun b => structuralMatch p s && b) tail

end

/-- Consume one position observation. A conflict refuses the candidate;
successful consumption removes exactly the obligations at that position. -/
def derive (observation : Observation Head) :
    List (Obligation Head) → Option (List (Obligation Head))
  | [] => some []
  | o :: os =>
      if o.position = observation.position then
        if o.key = observation.key then derive observation os else none
      else
        (derive observation os).map (o :: ·)

/-- First observation at a position is authoritative. Repeated observations
therefore cannot override an earlier refusal. -/
def lookup : List (Observation Head) → Position → Option (ConstructorKey Head)
  | [], _ => none
  | o :: os, position =>
      if position = o.position then some o.key else lookup os position

def finish : List (Observation Head) → List (Obligation Head) → Bool
  | [], obligations => obligations.isEmpty
  | observation :: observations, obligations =>
      match derive observation obligations with
      | none => false
      | some residual => finish observations residual

theorem derive_valid (observation : Observation Head) (observations : List (Observation Head))
    (obligations : List (Obligation Head)) :
    valid (lookup (observation :: observations)) obligations =
      match derive observation obligations with
      | none => false
      | some residual => valid (lookup observations) residual := by
  induction obligations with
  | nil => rfl
  | cons o os ih =>
      by_cases samePosition : o.position = observation.position
      · by_cases sameKey : o.key = observation.key
        · simp only [valid, List.all_cons, lookup, samePosition, if_true,
            sameKey, decide_true, Bool.true_and, derive]
          exact ih
        · have different : observation.key ≠ o.key := Ne.symm sameKey
          simp [valid, lookup, derive, samePosition, sameKey, different]
      · simp only [valid, List.all_cons, lookup, samePosition, if_false, derive]
        change (decide (lookup observations o.position = some o.key) &&
          valid (lookup (observation :: observations)) os) = _
        rw [ih]
        cases remaining : derive observation os <;> simp [valid]

/-- Derivative execution equals finite-obligation semantics, for every
observation stream, including incomplete and conflicting streams. -/
theorem finish_eq_valid (observations : List (Observation Head))
    (obligations : List (Obligation Head)) :
    finish observations obligations = valid (lookup observations) obligations := by
  induction observations generalizing obligations with
  | nil => cases obligations <;> simp [finish, valid, lookup]
  | cons observation observations ih =>
      rw [finish, derive_valid]
      cases remaining : derive observation obligations with
      | none => rfl
      | some residual => exact ih residual

/-- No derivative invents an obligation or changes its key. -/
theorem derive_sublist (observation : Observation Head) (obligations residual : List (Obligation Head))
    (computed : derive observation obligations = some residual) : residual.Sublist obligations := by
  induction obligations generalizing residual with
  | nil => simp [derive] at computed; subst residual; exact List.Sublist.refl _
  | cons o os ih =>
      by_cases samePosition : o.position = observation.position
      · by_cases sameKey : o.key = observation.key
        · simp only [derive, samePosition, sameKey, if_true] at computed
          exact (ih residual computed).cons _
        · simp [derive, samePosition, sameKey] at computed
      · cases remaining : derive observation os with
        | none => simp [derive, samePosition, remaining] at computed
        | some rs =>
            simp [derive, samePosition, remaining] at computed
            subst residual
            exact (ih rs remaining).cons_cons _

end

/-- Lift relative obligations into a candidate's root position. -/
def shift (root : Position) (obligations : List (Obligation Head)) : List (Obligation Head) :=
  obligations.map (fun o => ⟨root ++ o.position, o.key⟩)

theorem lookup_append (left right : List (Observation Head)) (position : Position) :
    lookup (left ++ right) position = (lookup left position).or (lookup right position) := by
  induction left with
  | nil => rfl
  | cons o os ih =>
      by_cases same : position = o.position <;> simp [lookup, same, ih]

theorem lookup_shift_same (observations : List (Observation Head))
    (root path : Position) : lookup (shift root observations) (root ++ path) = lookup observations path := by
  induction observations with
  | nil => rfl
  | cons o os ih =>
      change (if root ++ path = root ++ o.position then some o.key
        else lookup (shift root os) (root ++ path)) = _
      simp only [List.append_cancel_left_eq, ih, lookup]

theorem lookup_shift_other (observations : List (Observation Head))
    (i j : Nat) (path : Position) (different : i ≠ j) :
    lookup (shift [i] observations) (j :: path) = none := by
  induction observations with
  | nil => rfl
  | cons o os ih =>
      have unequal : j :: path ≠ i :: o.position := by
        intro h; have := List.cons.inj h; exact different this.1.symm
      change (if j :: path = i :: o.position then some o.key
        else lookup (shift [i] os) (j :: path)) = none
      simp only [unequal, if_false, ih]

mutual
  /-- Read the subject top-down once, producing immutable position observations. -/
  def observe : Subject Head → List (Observation Head)
    | .node h cs => ⟨[], ⟨h, cs.length⟩⟩ :: observeChildren 0 cs

  def observeChildren : Nat → List (Subject Head) → List (Observation Head)
    | _, [] => []
    | next, s :: ss => shift [next] (observe s) ++ observeChildren (next + 1) ss
end

theorem lookup_observeChildren_root (next : Nat) (subjects : List (Subject Head)) :
    lookup (observeChildren next subjects) [] = none := by
  induction subjects generalizing next with
  | nil => rfl
  | cons s ss ih =>
      rw [observeChildren, lookup_append, ih]
      have missing : lookup (shift [next] (observe s)) [] = none := by
        generalize observe s = observations
        induction observations with
        | nil => rfl
        | cons o os ih =>
            change (if [] = next :: o.position then some o.key
              else lookup (shift [next] os) []) = none
            simp only [ih]
            simp
      simp [missing]

theorem lookup_observeChildren_before (next i : Nat) (subjects : List (Subject Head))
    (path : Position) (before : i < next) :
    lookup (observeChildren next subjects) (i :: path) = none := by
  induction subjects generalizing next with
  | nil => rfl
  | cons s ss ih =>
      rw [observeChildren, lookup_append,
        lookup_shift_other (observe s) next i path (by omega), ih (next + 1) (by omega)]
      rfl

mutual
  theorem lookup_observe (subject : Subject Head) (path : Position) :
      lookup (observe subject) path = keyAt subject path := by
    cases subject with
    | node h cs =>
        cases path with
        | nil => simp [observe, lookup, keyAt, project, key]
        | cons i path =>
            simp only [observe, lookup, List.cons_ne_nil, if_false, keyAt, project]
            simpa [keyAt, Option.bind_map] using lookup_observeChildren 0 i cs path (by omega)

  theorem lookup_observeChildren (next i : Nat) (subjects : List (Subject Head))
      (path : Position) (after : next ≤ i) :
      lookup (observeChildren next subjects) (i :: path) =
        (subjects[i - next]?).bind (fun s => keyAt s path) := by
    cases subjects with
    | nil => simp [observeChildren, lookup]
    | cons s ss =>
        rw [observeChildren, lookup_append]
        by_cases same : i = next
        · subst i
          rw [lookup_observeChildren_before (next + 1) next ss path (by omega)]
          simpa only [Nat.sub_self, List.getElem?_cons_zero, Option.bind_some,
            Option.or_none, List.cons_append, List.nil_append] using lookup_shift_same (observe s) [next] path |>.trans
              (lookup_observe s path)
        · rw [lookup_shift_other (observe s) next i path (by omega)]
          simp only [Option.none_or]
          rw [lookup_observeChildren (next + 1) i ss path (by omega)]
          have index : i - next = (i - (next + 1)) + 1 := by omega
          simp only [index, List.getElem?_cons_succ]
end

mutual
  theorem observe_eq_positions (subject : Subject Head) :
      observe subject = (positions subject).map (fun entry => ⟨entry.1, key entry.2⟩) := by
    cases subject with
    | node h cs =>
        simp only [observe, positions, List.map_cons, key]
        rw [observeChildren_eq_positionsList]
        rfl

  theorem observeChildren_eq_positionsList (next : Nat) (subjects : List (Subject Head)) :
      observeChildren next subjects =
        (positionsList next subjects).map (fun entry => ⟨entry.1, key entry.2⟩) := by
    cases subjects with
    | nil => rfl
    | cons s ss =>
        simp only [observeChildren, positionsList, List.map_append, List.map_map, shift]
        rw [observe_eq_positions, observeChildren_eq_positionsList]
        simp only [List.map_map, Function.comp_def, List.cons_append, List.nil_append]
end

section
variable [DecidableEq Head]

theorem valid_shift (read : Position → Option (ConstructorKey Head))
    (root : Position) (obligations : List (Obligation Head)) :
    valid read (shift root obligations) = valid (fun path => read (root ++ path)) obligations := by
  simp [valid, shift, List.all_map, Function.comp_def]

theorem finish_at_position (patterns : Pattern Head) (subject focused : Subject Head)
    (root : Position) (found : project root subject = some focused) :
    finish (observe subject) (shift root (compile patterns)) = structuralMatch patterns focused := by
  rw [finish_eq_valid, valid_shift]
  have reads : (fun path => lookup (observe subject) (root ++ path)) = keyAt focused := by
    funext path
    rw [lookup_observe]
    simp [keyAt, project_append, found]
  rw [reads, valid_compile]

structure Goal (Head : Type u) where
  location : Location
  pending : List (Obligation Head)
deriving Repr

/-- One shared observation drives every live candidate. No candidate reads
the subject independently. -/
def deriveGoals (observation : Observation Head) (goals : List (Goal Head)) : List (Goal Head) :=
  goals.filterMap fun goal => (derive observation goal.pending).map
    (fun residual => ⟨goal.location, residual⟩)

def execute : List (Observation Head) → List (Goal Head) → List (Goal Head)
  | [], goals => goals
  | o :: os, goals => execute os (deriveGoals o goals)

def completed (goals : List (Goal Head)) : List Location :=
  goals.filterMap fun goal => if goal.pending.isEmpty then some goal.location else none

theorem completed_execute (observations : List (Observation Head)) (goals : List (Goal Head)) :
    completed (execute observations goals) =
      goals.filterMap (fun goal => if finish observations goal.pending then some goal.location else none) := by
  induction observations generalizing goals with
  | nil => rfl
  | cons o os ih =>
      rw [execute, ih]
      simp only [deriveGoals, List.filterMap_filterMap]
      apply List.filterMap_congr
      intro goal _
      cases residual : derive o goal.pending <;> simp [finish, residual]

/-- Instantiate finite compiled controls at one root, retaining every row. -/
def seed (root : Position) : Nat → List (List (Obligation Head)) → List (Goal Head)
  | _, [] => []
  | next, obligations :: rest =>
      ⟨⟨root, next⟩, shift root obligations⟩ :: seed root (next + 1) rest

theorem filter_seed (observations : List (Observation Head)) (root : Position)
    (next : Nat) (patterns : List (Pattern Head)) :
    (seed root next (patterns.map compile)).filterMap
        (fun goal => if finish observations goal.pending then some goal.location else none) =
      (select (fun p => finish observations (shift root (compile p))) next patterns).map
        (fun occurrence => (⟨root, occurrence⟩ : Location)) := by
  induction patterns generalizing next with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, seed, List.filterMap_cons, select]
      rw [ih]
      split <;> simp_all

/-- Compile once, read constructors once, and run the shared derivative stream.
Output is normalized to source preorder and occurrence order by retaining the
seed order throughout execution. -/
def run (patterns : List (Pattern Head)) (subject : Subject Head) : List Location :=
  let programs := patterns.map compile
  let observations := observe subject
  completed (execute observations
    (observations.flatMap (fun o => seed o.position 0 programs)))

theorem run_eq_reference (patterns : List (Pattern Head)) (subject : Subject Head) :
    run patterns subject = reference patterns subject := by
  rw [run, completed_execute, List.filterMap_flatMap]
  simp only [filter_seed]
  rw [observe_eq_positions, List.flatMap_map]
  unfold reference
  apply List.flatMap_congr
  intro entry member
  congr 1
  apply select_congr
  intro p _
  simpa only [observe_eq_positions] using
    finish_at_position p subject entry.2 entry.1 (positions_sound subject entry member)

/-- Independent machines have identical ordered structural observations. -/
theorem run_eq_bottomUp (patterns : List (Pattern Head)) (subject : Subject Head) :
    run patterns subject = BottomUpMatchAutomaton.run patterns subject := by
  rw [run_eq_reference, BottomUpMatchAutomaton.run_eq_reference]

/-- Count live-candidate dispatches during the actual shared stream execution.
This exposes work hidden by the constructor-read count alone. -/
def executeCounted : List (Observation Head) → List (Goal Head) → List (Goal Head) × Nat
  | [], goals => (goals, 0)
  | o :: os, goals =>
      let after := executeCounted os (deriveGoals o goals)
      (after.1, goals.length + after.2)

theorem executeCounted_result (observations : List (Observation Head)) (goals : List (Goal Head)) :
    (executeCounted observations goals).1 = execute observations goals := by
  induction observations generalizing goals with
  | nil => rfl
  | cons o os ih => simpa only [executeCounted, execute] using ih (deriveGoals o goals)

end

mutual
  /-- Each emitted observation records one source constructor read. -/
  theorem observe_length (subject : Subject Head) :
      (observe subject).length = BottomUpMatchAutomaton.nodeCount subject := by
    cases subject with
    | node h cs =>
        simp only [observe, List.length_cons, BottomUpMatchAutomaton.nodeCount]
        rw [observeChildren_length]
        omega

  theorem observeChildren_length (next : Nat) (subjects : List (Subject Head)) :
      (observeChildren next subjects).length = BottomUpMatchAutomaton.nodesCount subjects := by
    cases subjects with
    | nil => rfl
    | cons s ss =>
        simp only [observeChildren, List.length_append, shift, List.length_map,
          BottomUpMatchAutomaton.nodesCount]
        rw [observe_length, observeChildren_length]
end

section
variable [DecidableEq Head]

theorem executed_goal_origin (observations : List (Observation Head))
    (goals : List (Goal Head)) (goal : Goal Head) (present : goal ∈ execute observations goals) :
    ∃ original ∈ goals, goal.location = original.location ∧ goal.pending.Sublist original.pending := by
  induction observations generalizing goals with
  | nil => exact ⟨goal, present, rfl, List.Sublist.refl _⟩
  | cons observation observations ih =>
      obtain ⟨prior, member, same, residual⟩ := ih (deriveGoals observation goals) present
      obtain ⟨original, originalMember, computed⟩ := List.mem_filterMap.mp member
      cases remaining : derive observation original.pending with
      | none => simp [remaining] at computed
      | some pending =>
          simp only [remaining, Option.map_some, Option.some.injEq] at computed
          subst prior
          exact ⟨original, originalMember, same,
            residual.trans (derive_sublist observation original.pending pending remaining)⟩

/-- Each candidate's residual control is drawn from the finite sublists of
its compiled obligations. Runtime root positions are explicit registers. -/
theorem executed_goal_finite_control (observations : List (Observation Head))
    (goals : List (Goal Head)) (goal : Goal Head) (present : goal ∈ execute observations goals) :
    ∃ original ∈ goals, goal.location = original.location ∧
      goal.pending ∈ original.pending.sublists := by
  obtain ⟨original, member, same, sublist⟩ := executed_goal_origin observations goals goal present
  exact ⟨original, member, same, List.mem_sublists.mpr sublist⟩

#print axioms valid_compile
#print axioms finish_eq_valid
#print axioms run_eq_reference
#print axioms run_eq_bottomUp
#print axioms executed_goal_origin

end

end Mettapedia.GSLT.LanguageDef.TopDownMatchDerivatives

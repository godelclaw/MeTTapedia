import Mettapedia.Computability.RegularLanguages.RegexSelectionCorrespondence

/-!+# Global point-memoized depth-first regex search

The search retains failed visited points across alternatives. Its proof uses a
negative-reachability invariant relative to the current ancestor barrier. This
is separate from the ordered Pike frontier machine and does not identify the
two evaluation schedules.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch

open RegexTaggedGraph RegexSelectionCorrespondence
open OrderedGraphSearch (Point Probe)
open RegexMatchObservations (HigherPriority)

universe u v w z

section Reachability

variable {Key : Type u}

/-- Finite goal reachability avoiding a supplied barrier, independently of
the search algorithm and its visited set. Cycles are permitted in this relation. -/
inductive Reaches (children : Key → List Key) (goal : Key → Bool) (barrier : Finset Key) : Key → Prop
  | done {point} : point ∉ barrier → goal point = true → Reaches children goal barrier point
  | step {point target} : point ∉ barrier → target ∈ children point →
      Reaches children goal barrier target → Reaches children goal barrier point

theorem Reaches.not_blocked {children : Key → List Key} {goal : Key → Bool} {barrier : Finset Key}
    {point : Key} (reached : Reaches children goal barrier point) : point ∉ barrier := by
  cases reached <;> assumption

theorem Reaches.weaken {children : Key → List Key} {goal : Key → Bool} {small large : Finset Key}
    (included : small ⊆ large) {point : Key} (reached : Reaches children goal large point) :
    Reaches children goal small point := by
  induction reached with
  | done outside accepted => exact .done (fun member => outside (included member)) accepted
  | step outside edge _ ih => exact .step (fun member => outside (included member)) edge ih

/-- Cut a finite path at its final departure from one distinguished point.
This is the cycle-removal fact needed when a completed DFS call drops an
ancestor barrier. No enumeration of simple paths is used. -/
theorem Reaches.cut [DecidableEq Key] {children : Key → List Key} {goal : Key → Bool}
    {barrier : Finset Key} (pivot : Key) {point : Key}
    (reached : Reaches children goal barrier point) :
    Reaches children goal (insert pivot barrier) point ∨
      goal pivot = true ∨ ∃ target ∈ children pivot, Reaches children goal (insert pivot barrier) target := by
  induction reached with
  | @done point outside accepted =>
      by_cases same : point = pivot
      · subst point; exact Or.inr (Or.inl accepted)
      · exact Or.inl (.done (by simp [same, outside]) accepted)
  | @step point target outside edge tail ih =>
      rcases ih with avoids | escaped
      · by_cases same : point = pivot
        · subst point; exact Or.inr (Or.inr ⟨target, edge, avoids⟩)
        · exact Or.inl (.step (by simp [same, outside]) edge avoids)
      · exact Or.inr escaped

theorem Reaches.escape [DecidableEq Key] {children : Key → List Key} {goal : Key → Bool}
    {barrier : Finset Key} {point : Key} (reached : Reaches children goal barrier point) :
    goal point = true ∨ ∃ target ∈ children point, Reaches children goal (insert point barrier) target := by
  rcases reached.cut point with blocked | escaped
  · exact False.elim (blocked.not_blocked (Finset.mem_insert_self point barrier))
  · exact escaped

theorem Reaches.avoid_dead [DecidableEq Key] {children : Key → List Key} {goal : Key → Bool}
    {barrier : Finset Key} {pivot point : Key}
    (dead : ¬ Reaches children goal barrier pivot) (reached : Reaches children goal barrier point) :
    Reaches children goal (insert pivot barrier) point := by
  induction reached with
  | @done point outside accepted =>
      have different : point ≠ pivot := fun same => dead (same ▸ Reaches.done outside accepted)
      exact .done (by simp [different, outside]) accepted
  | @step point target outside edge tail ih =>
      have different : point ≠ pivot := fun same => dead (same ▸ Reaches.step outside edge tail)
      exact .step (by simp [different, outside]) edge ih

def Safe (children : Key → List Key) (goal : Key → Bool) (barrier seen : Finset Key) : Prop :=
  ∀ point ∈ seen, ¬ Reaches children goal barrier point

theorem safe_enlarge [DecidableEq Key] {children : Key → List Key} {goal : Key → Bool}
    {barrier seen : Finset Key} (safe : Safe children goal barrier seen) (pivot : Key) :
    Safe children goal (insert pivot barrier) (insert pivot seen) := by
  intro point member reached
  rcases Finset.mem_insert.mp member with same | member
  · subst point; exact reached.not_blocked (Finset.mem_insert_self pivot barrier)
  · exact safe point member (reached.weaken (Finset.subset_insert pivot barrier))

theorem safe_drop_barrier [DecidableEq Key] {children : Key → List Key} {goal : Key → Bool}
    {barrier seen : Finset Key} {pivot : Key}
    (dead : ¬ Reaches children goal barrier pivot)
    (safe : Safe children goal (insert pivot barrier) seen) : Safe children goal barrier seen := by
  intro point member reached
  exact safe point member (reached.avoid_dead dead)

end Reachability

inductive Result (α : Type u) (Tag : Type v) (Key : Type w) where
  | incomplete
  | found (value : α) (tag : Tag)
  | absent (seen : Finset Key)

/-- A short-circuiting global-memo DFS. Every first visit marks its control
point before following an edge; a failed preferred branch passes all its
visited points to its sibling. It never materializes an all-path relation. -/
def search {α : Type u} {Tag : Type v} {Key : Type w} [DecidableEq Key]
    (key : α → Key) (step : α → Action α Tag) (eligible : Key → Bool) :
    Nat → Finset Key → α → Result α Tag Key
  | 0, _, _ => .incomplete
  | fuel + 1, seen, first =>
      if key first ∈ seen then .absent seen
      else
        let marked := insert (key first) seen
        match step first with
        | .accept tag => if eligible (key first) then .found first tag else .absent marked
        | .dead => .absent marked
        | .next target => search key step eligible fuel marked target
        | .branch left right =>
            match search key step eligible fuel marked left with
            | .incomplete => .incomplete
            | .found value tag => .found value tag
            | .absent after => search key step eligible fuel after right

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def children (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length) :
    Point State length → List (Point State length) :=
  OrderedGraphSearch.expand (fun state => eraseNode (graph state)) probe

def goal (graph : State → Node State Class Assertion Tag) (eligible : Point State length → Bool)
    (point : Point State length) : Bool :=
  (OrderedGraphSearch.acceptedTag (eraseNode (graph point.1))).isSome && eligible point

def actionChildren {α : Type u} {Tag : Type v} : Action α Tag → List α
  | .accept _ | .dead => []
  | .next target => [target]
  | .branch left right => [left, right]

theorem action_children (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (first : Thread State length) :
    (actionChildren (action graph probe first)).map Thread.point = children graph probe first.point := by
  unfold children
  rw [← edges_erase graph probe first]
  congr 1
  cases node : graph first.point.1 with
  | accept _ | dead | jump _ | choice _ _ | save _ _ => simp [action, edges, node, actionChildren]
  | consume class_ target =>
      cases contains : probe.contains class_ first.point.2 <;>
        simp only [action, edges, node, contains, Bool.false_eq_true, ↓reduceIte]
      · rfl
      · cases OrderedGraphSearch.successor first.point.2 <;> rfl
  | assertion assertion_ target =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [action, edges, node, holds, actionChildren]

theorem action_goal (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length) :
    goal graph eligible first.point =
      match action graph probe first with
      | .accept _ => eligible first.point
      | _ => false := by
  cases node : graph first.point.1 with
  | accept _ | dead | jump _ | choice _ _ | save _ _ =>
      simp [goal, action, node, eraseNode, OrderedGraphSearch.acceptedTag]
  | consume class_ target =>
      cases contains : probe.contains class_ first.point.2 with
      | false => simp [goal, action, node, eraseNode, OrderedGraphSearch.acceptedTag, contains]
      | true =>
          simp only [goal, action, node, eraseNode, OrderedGraphSearch.acceptedTag, Option.isSome,
            Bool.false_and, contains, ↓reduceIte]
          cases OrderedGraphSearch.successor first.point.2 <;> rfl
  | assertion assertion_ target =>
      cases holds : probe.holds assertion_ first.point.2 <;>
        simp [goal, action, node, holds, eraseNode, OrderedGraphSearch.acceptedTag]

def Avoids (barrier : Finset (Point State length)) (points : List (Point State length)) : Prop :=
  ∀ point ∈ points, point ∉ barrier

theorem admissible_tail [DecidableEq State] {barrier : Finset (Point State length)}
    {point : Point State length} {points : List (Point State length)}
    (simple : Simple (point :: points)) (avoids : Avoids barrier (point :: points)) :
    Simple points ∧ Avoids (insert point barrier) points := by
  have pair : point ∉ points ∧ points.Nodup := List.nodup_cons.mp simple
  refine ⟨pair.2, ?_⟩
  intro target member blocked
  rcases Finset.mem_insert.mp blocked with same | blocked
  · subst target; exact pair.1 member
  · exact avoids target (by simp [member]) blocked

theorem admissible_cons [DecidableEq State] {barrier : Finset (Point State length)}
    {point : Point State length} {points : List (Point State length)}
    (outside : point ∉ barrier) (simple : Simple points) (avoids : Avoids (insert point barrier) points) :
    Simple (point :: points) ∧ Avoids barrier (point :: points) := by
  constructor
  · exact List.nodup_cons.mpr ⟨fun member => avoids point member (Finset.mem_insert_self point barrier), simple⟩
  · intro target member blocked
    rcases List.mem_cons.mp member with same | member
    · subst target; exact outside blocked
    · exact avoids target member (Finset.mem_insert_of_mem blocked)

theorem trace_reaches {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {first last : Thread State length}
    {code : List Bool} {points : List (Point State length)} {tag : Tag}
    (trace : Trace graph probe (fun thread => eligible thread.point) first code points last tag)
    (barrier : Finset (Point State length)) (avoids : Avoids barrier points) :
    Reaches (children graph probe) (goal graph eligible) barrier first.point := by
  induction trace with
  | done accepted allowed =>
      apply Reaches.done (avoids _ (by simp))
      rw [action_goal graph probe eligible, accepted]
      exact allowed
  | next step tail ih =>
      apply Reaches.step (avoids _ (by simp)) ?_ (ih (fun point member => avoids point (by simp [member])))
      rw [← action_children graph probe, step]
      simp [actionChildren]
  | left step tail ih =>
      apply Reaches.step (avoids _ (by simp)) ?_ (ih (fun point member => avoids point (by simp [member])))
      rw [← action_children graph probe, step]
      simp [actionChildren]
  | right step tail ih =>
      apply Reaches.step (avoids _ (by simp)) ?_ (ih (fun point member => avoids point (by simp [member])))
      rw [← action_children graph probe, step]
      simp [actionChildren]

/-- Least accepting trace among all simple traces avoiding the current ancestor
barrier. The visited set does not occur in this independent specification. -/
def LeastAvoiding (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (barrier : Finset (Point State length))
    (first last : Thread State length) (tag : Tag) : Prop :=
  ∃ code points, Trace graph probe (fun thread => eligible thread.point) first code points last tag ∧
    Simple points ∧ Avoids barrier points ∧
    ∀ otherCode otherPoints otherLast otherTag,
      Trace graph probe (fun thread => eligible thread.point) first otherCode otherPoints otherLast otherTag →
      Simple otherPoints → Avoids barrier otherPoints → code = otherCode ∨ HigherPriority code otherCode

theorem leastAvoiding_empty {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {first last : Thread State length} {tag : Tag}
    (least : LeastAvoiding graph probe eligible ∅ first last tag) :
    LeastSimple graph probe (fun thread => eligible thread.point) first last := by
  obtain ⟨code, points, trace, simple, avoids, minimal⟩ := least
  exact ⟨code, points, tag, trace, simple, fun _ _ _ _ other otherSimple =>
    minimal _ _ _ _ other otherSimple (by simp [Avoids])⟩

theorem priority_cons (bit : Bool) {first second : List Bool}
    (comparison : first = second ∨ HigherPriority first second) :
    bit :: first = bit :: second ∨ HigherPriority (bit :: first) (bit :: second) :=
  comparison.imp (congrArg (List.cons bit)) (HigherPriority.prefix bit)

theorem least_done {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {barrier : Finset (Point State length)}
    {first : Thread State length} {tag : Tag}
    (accepted : action graph probe first = .accept tag) (allowed : eligible first.point = true)
    (outside : first.point ∉ barrier) : LeastAvoiding graph probe eligible barrier first first tag := by
  refine ⟨[], [first.point], .done accepted allowed, by simp [Simple], ?_, ?_⟩
  · simpa [Avoids] using outside
  · intro otherCode otherPoints otherLast otherTag other _ _
    cases other <;> simp_all

theorem least_next [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {barrier : Finset (Point State length)}
    {first target last : Thread State length} {tag : Tag}
    (step : action graph probe first = .next target) (outside : first.point ∉ barrier)
    (least : LeastAvoiding graph probe eligible (insert first.point barrier) target last tag) :
    LeastAvoiding graph probe eligible barrier first last tag := by
  obtain ⟨code, points, trace, simple, avoids, minimal⟩ := least
  have admissible := admissible_cons outside simple avoids
  refine ⟨code, first.point :: points, .next step trace, admissible.1, admissible.2, ?_⟩
  intro otherCode otherPoints otherLast otherTag other otherSimple otherAvoids
  cases other <;> simp_all
  have tail := admissible_tail otherSimple otherAvoids
  exact minimal _ _ _ _ (by assumption) tail.1 tail.2

theorem least_left [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {barrier : Finset (Point State length)}
    {first left right last : Thread State length} {tag : Tag}
    (step : action graph probe first = .branch left right) (outside : first.point ∉ barrier)
    (least : LeastAvoiding graph probe eligible (insert first.point barrier) left last tag) :
    LeastAvoiding graph probe eligible barrier first last tag := by
  obtain ⟨code, points, trace, simple, avoids, minimal⟩ := least
  have admissible := admissible_cons outside simple avoids
  refine ⟨false :: code, first.point :: points, .left step trace, admissible.1, admissible.2, ?_⟩
  intro otherCode otherPoints otherLast otherTag other otherSimple otherAvoids
  cases other with
  | done otherStep _ => simp_all
  | next otherStep _ => simp_all
  | left otherStep otherTrace =>
      have equal := Action.branch.inj (step.symm.trans otherStep)
      rcases equal with ⟨rfl, rfl⟩
      have tail := admissible_tail otherSimple otherAvoids
      exact priority_cons false (minimal _ _ _ _ otherTrace tail.1 tail.2)
  | right otherStep otherTrace => exact Or.inr (.branch _ _)

theorem least_right [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {barrier : Finset (Point State length)}
    {first left right last : Thread State length} {tag : Tag}
    (step : action graph probe first = .branch left right) (outside : first.point ∉ barrier)
    (leftDead : ¬ Reaches (children graph probe) (goal graph eligible) (insert first.point barrier) left.point)
    (least : LeastAvoiding graph probe eligible (insert first.point barrier) right last tag) :
    LeastAvoiding graph probe eligible barrier first last tag := by
  obtain ⟨code, points, trace, simple, avoids, minimal⟩ := least
  have admissible := admissible_cons outside simple avoids
  refine ⟨true :: code, first.point :: points, .right step trace, admissible.1, admissible.2, ?_⟩
  intro otherCode otherPoints otherLast otherTag other otherSimple otherAvoids
  cases other with
  | done otherStep _ => simp_all
  | next otherStep _ => simp_all
  | left otherStep otherTrace =>
      have equal := Action.branch.inj (step.symm.trans otherStep)
      rcases equal with ⟨rfl, rfl⟩
      exact False.elim (leftDead (trace_reaches otherTrace _ (admissible_tail otherSimple otherAvoids).2))
  | right otherStep otherTrace =>
      have equal := Action.branch.inj (step.symm.trans otherStep)
      rcases equal with ⟨rfl, rfl⟩
      have tail := admissible_tail otherSimple otherAvoids
      exact priority_cons true (minimal _ _ _ _ otherTrace tail.1 tail.2)

theorem no_reach_when_children_dead [DecidableEq State]
    {graph : State → Node State Class Assertion Tag} {probe : Probe Class Assertion length}
    {eligible : Point State length → Bool} {barrier : Finset (Point State length)}
    {first : Thread State length} (notGoal : goal graph eligible first.point = false)
    (dead : ∀ target ∈ children graph probe first.point,
      ¬ Reaches (children graph probe) (goal graph eligible) (insert first.point barrier) target) :
    ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point := by
  intro reached
  rcases reached.escape with accepted | ⟨target, member, tail⟩
  · simp [notGoal] at accepted
  · exact dead target member tail

def Contract (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (barrier seen : Finset (Point State length))
    (first : Thread State length) : Result (Thread State length) Tag (Point State length) → Prop
  | .incomplete => False
  | .found last tag => LeastAvoiding graph probe eligible barrier first last tag
  | .absent after => seen ⊆ after ∧ Safe (children graph probe) (goal graph eligible) barrier after ∧
      ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point

/-- The global seen-set invariant proves both least-path selection and honest
closed absence. Its ancestor barrier is proof state only, not an additional
search filter or a restriction on the accepted source patterns. -/
theorem search_contract [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (fuel : Nat) :
    ∀ (seen barrier : Finset (Point State length)) (first : Thread State length),
      barrier ⊆ seen → Safe (children graph probe) (goal graph eligible) barrier seen →
      Fintype.card (Point State length) - seen.card + 1 < fuel →
      Contract graph probe eligible barrier seen first
        (search Thread.point (action graph probe) eligible fuel seen first) := by
  induction fuel with
  | zero => intro seen barrier first included safe enough; omega
  | succ fuel ih =>
      intro seen barrier first included safe enough
      by_cases visited : first.point ∈ seen
      · simp only [search, visited, ↓reduceIte, Contract]
        exact ⟨Finset.Subset.refl _, safe, safe first.point visited⟩
      · have outside : first.point ∉ barrier := fun blocked => visited (included blocked)
        have childSafe := safe_enlarge safe first.point
        have childIncluded : insert first.point barrier ⊆ insert first.point seen :=
          Finset.insert_subset_insert first.point included
        have childEnough : Fintype.card (Point State length) - (insert first.point seen).card + 1 < fuel := by
          have card := Finset.card_le_univ (insert first.point seen)
          rw [Finset.card_insert_of_notMem visited] at card ⊢
          omega
        cases step : action graph probe first with
        | accept tag =>
            cases allowed : eligible first.point with
            | true =>
                simp only [search, visited, ↓reduceIte, step, allowed, Contract]
                exact least_done step allowed outside
            | false =>
                have dead : ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point := by
                  apply no_reach_when_children_dead (by simpa [step, allowed] using action_goal graph probe eligible first)
                  intro target member
                  rw [← action_children graph probe first, step] at member
                  simp [actionChildren] at member
                simp only [search, visited, ↓reduceIte, step, allowed, Bool.false_eq_true, Contract]
                exact ⟨Finset.subset_insert _ _, safe_drop_barrier dead childSafe, dead⟩
        | dead =>
            have dead : ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point := by
              apply no_reach_when_children_dead (by simpa [step] using action_goal graph probe eligible first)
              intro target member
              rw [← action_children graph probe first, step] at member
              simp [actionChildren] at member
            simp only [search, visited, ↓reduceIte, step, Contract]
            exact ⟨Finset.subset_insert _ _, safe_drop_barrier dead childSafe, dead⟩
        | next target =>
            have child := ih (insert first.point seen) (insert first.point barrier) target
              childIncluded childSafe childEnough
            cases result : search Thread.point (action graph probe) eligible fuel (insert first.point seen) target with
            | incomplete => simp [Contract, result] at child
            | found last tag =>
                simp only [Contract, result] at child
                simp only [search, visited, ↓reduceIte, step, result, Contract]
                exact least_next step outside child
            | absent after =>
                simp only [Contract, result] at child
                have dead : ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point := by
                  apply no_reach_when_children_dead (by simpa [step] using action_goal graph probe eligible first)
                  intro point member
                  rw [← action_children graph probe first, step] at member
                  simp only [actionChildren, List.map_singleton, List.mem_singleton] at member
                  subst point
                  exact child.2.2
                simp only [search, visited, ↓reduceIte, step, result, Contract]
                exact ⟨(Finset.subset_insert _ _).trans child.1,
                  safe_drop_barrier dead child.2.1, dead⟩
        | branch left right =>
            have leftContract := ih (insert first.point seen) (insert first.point barrier) left
              childIncluded childSafe childEnough
            cases leftResult : search Thread.point (action graph probe) eligible fuel (insert first.point seen) left with
            | incomplete => simp [Contract, leftResult] at leftContract
            | found last tag =>
                simp only [Contract, leftResult] at leftContract
                simp only [search, visited, ↓reduceIte, step, leftResult, Contract]
                exact least_left step outside leftContract
            | absent middle =>
                simp only [Contract, leftResult] at leftContract
                have rightEnough : Fintype.card (Point State length) - middle.card + 1 < fuel := by
                  have size := Finset.card_le_card leftContract.1
                  omega
                have rightContract := ih middle (insert first.point barrier) right
                  (childIncluded.trans leftContract.1) leftContract.2.1 rightEnough
                cases rightResult : search Thread.point (action graph probe) eligible fuel middle right with
                | incomplete => simp [Contract, rightResult] at rightContract
                | found last tag =>
                    simp only [Contract, rightResult] at rightContract
                    simp only [search, visited, ↓reduceIte, step, leftResult, rightResult, Contract]
                    exact least_right step outside leftContract.2.2 rightContract
                | absent after =>
                    simp only [Contract, rightResult] at rightContract
                    have dead : ¬ Reaches (children graph probe) (goal graph eligible) barrier first.point := by
                      apply no_reach_when_children_dead (by simpa [step] using action_goal graph probe eligible first)
                      intro point member
                      rw [← action_children graph probe first, step] at member
                      simp only [actionChildren, List.map_cons, List.map_nil,
                        List.mem_cons, List.not_mem_nil, or_false] at member
                      rcases member with same | same
                      · subst point; exact leftContract.2.2
                      · subst point; exact rightContract.2.2
                    simp only [search, visited, ↓reduceIte, step, leftResult, rightResult, Contract]
                    exact ⟨(Finset.subset_insert _ _).trans (leftContract.1.trans rightContract.1),
                      safe_drop_barrier dead rightContract.2.1, dead⟩

def taggedSearch [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Point State length → Bool)
    (fuel : Nat) (first : Thread State length) : Result (Thread State length) Tag (Point State length) :=
  search Thread.point (action graph probe) eligible fuel ∅ first

theorem taggedSearch_contract [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel) :
    Contract graph probe eligible ∅ ∅ first (taggedSearch graph probe eligible fuel first) := by
  apply search_contract graph probe eligible fuel ∅ ∅ first (by simp) (by simp [Safe])
  simpa using enough

theorem taggedSearch_ne_incomplete [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel) :
    taggedSearch graph probe eligible fuel first ≠ .incomplete := by
  intro incomplete
  have checked := taggedSearch_contract graph probe eligible first fuel enough
  simp [incomplete, Contract] at checked

/-- Two-sided selected-capture adequacy for the actual global point-memo DFS.
The right-hand side quantifies over independently specified finite simple
paths. Eligibility depends only on control points, not capture contents. -/
theorem taggedSearch_leastSimple [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first last : Thread State length) (tag : Tag)
    (fuel : Nat) (enough : Fintype.card (Point State length) + 1 < fuel) :
    taggedSearch graph probe eligible fuel first = .found last tag ↔
      LeastSimple graph probe (fun thread => eligible thread.point) first last ∧
        RegexPikeVM.terminal graph last = some tag := by
  have checked := taggedSearch_contract graph probe eligible first fuel enough
  constructor
  · intro found
    rw [found] at checked
    have least : LeastAvoiding graph probe eligible ∅ first last tag := checked
    obtain ⟨code, points, trace, _, _, _⟩ := least
    exact ⟨leastAvoiding_empty checked, trace.sound.2.1⟩
  · rintro ⟨least, terminal⟩
    cases result : taggedSearch graph probe eligible fuel first with
    | incomplete => simp [Contract, result] at checked
    | absent after =>
        simp only [Contract, result] at checked
        obtain ⟨code, points, someTag, trace, _, _⟩ := least
        exact False.elim (checked.2.2 (trace_reaches trace ∅ (by simp [Avoids])))
    | found selected selectedTag =>
        simp only [Contract, result] at checked
        have same := leastSimple_unique graph probe (fun thread => eligible thread.point)
          first selected last (leastAvoiding_empty checked) least
        subst selected
        obtain ⟨code, points, trace, _, _, _⟩ := checked
        have sameTag : selectedTag = tag := Option.some.inj (trace.sound.2.1.symm.trans terminal)
        subst selectedTag
        rfl

/-- Completed absence excludes every finite accepting trace, not only simple
ones. Exhaustion is a different constructor and is ruled out by earned fuel. -/
theorem taggedSearch_absent_iff [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Point State length → Bool) (first : Thread State length) (fuel : Nat)
    (enough : Fintype.card (Point State length) + 1 < fuel) :
    (∃ after, taggedSearch graph probe eligible fuel first = .absent after) ↔
      ¬ ∃ code points last tag,
        Trace graph probe (fun thread => eligible thread.point) first code points last tag := by
  have checked := taggedSearch_contract graph probe eligible first fuel enough
  constructor
  · rintro ⟨after, absent⟩ ⟨code, points, last, tag, trace⟩
    rw [absent] at checked
    exact checked.2.2 (trace_reaches trace ∅ (by simp [Avoids]))
  · intro noTrace
    cases result : taggedSearch graph probe eligible fuel first with
    | incomplete => simp [Contract, result] at checked
    | absent after => exact ⟨after, rfl⟩
    | found last tag =>
        simp only [Contract, result] at checked
        obtain ⟨code, points, trace, _, _, _⟩ := checked
        exact False.elim (noTrace ⟨code, points, last, tag, trace⟩)

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {count : Nat} (state : Fin count) (length : Nat) : Thread (Fin count) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def observed {State : Type} {Tag : Type} {Key : Type} {length : Nat} :
    Result (Thread State length) Tag Key → Option (Nat × Option Nat × List Bool)
  | .incomplete | .absent _ => none
  | .found thread _ => some (thread.point.2.val, (thread.registers 0).map Fin.val, thread.choices)

private def nullableRotation : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .choice 3 4
  | 3 => .jump 1
  | _ => .accept ()

theorem nullable_rotation_selects_the_simple_capture_path :
    observed (taggedSearch nullableRotation (probe 0) (fun _ => true) 8 (initial 0 0)) =
      some (0, some 0, [false, true]) := by decide

private def failedSharing : Fin 7 → Node (Fin 7) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .choice 2 3
  | 2 => .jump 3
  | 3 => .dead
  | 4 => .choice 3 5
  | 5 => .save 0 6
  | _ => .accept ()

theorem failed_preferred_branch_reuses_its_global_memo_without_losing_captures :
    observed (taggedSearch failedSharing (probe 0) (fun _ => true) 10 (initial 0 0)) =
      some (0, some 0, [true, true]) := by decide

private def consumingReentry : Fin 5 → Node (Fin 5) Unit Unit Unit := fun state =>
  match state.val with
  | 0 => .choice 1 4
  | 1 => .save 0 2
  | 2 => .choice 3 4
  | 3 => .consume () 1
  | _ => .accept ()

theorem a_different_position_is_not_a_repeated_point :
    observed (taggedSearch consumingReentry (probe 2) (fun point => point.2.val == 2) 18 (initial 0 2)) =
      some (2, some 2, [false, false, false, true]) := by decide

private def fullAction (thread : Thread (Fin 5) 2) : Action (Thread (Fin 5) 2) Unit :=
  match action consumingReentry (probe 2) thread with
  | .accept tag => if thread.point.2.val == 2 then .accept tag else .dead
  | other => other

theorem node_only_memoization_loses_the_full_match :
    let wrong := search (fun thread : Thread (Fin 5) 2 => thread.point.1)
      fullAction (fun _ => true) 18 ∅ (initial 0 2)
    (match wrong with
      | .incomplete => false
      | .found _ _ => false
      | .absent _ => true) = true ∧
    observed (search Thread.point fullAction (fun _ => true) 18 ∅ (initial 0 2)) =
      some (2, some 2, [false, false, false, true]) := by decide

theorem explicit_budget_exhaustion_is_not_completed_absence :
    taggedSearch consumingReentry (probe 2) (fun point => point.2.val == 2) 0 (initial 0 2) = .incomplete := rfl

end Controls

#print axioms Reaches.cut
#print axioms safe_drop_barrier
#print axioms search_contract
#print axioms taggedSearch_leastSimple
#print axioms taggedSearch_absent_iff

end Mettapedia.Computability.RegularLanguages.RegexMemoizedSearch

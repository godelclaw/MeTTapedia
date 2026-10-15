import Mettapedia.Machines.Cursor.OccurrenceMerge
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Refutation indexes at term paths

An ordinary finite structural term may have a variable on a queried path.
That row stays in a separate uncertain posting list. A rigid key on the path
goes in its key's posting list; a structural clash goes in neither.

The two posting lists denote exactly the candidate positions, and a genuine
unifier is never refuted. Filtering candidates by the original matcher keeps
the source occurrence list. Coordinates identify occurrences independently
of equal payloads. The common occurrence-merge provider supplies ordered
delivery; a physical dictionary must refine the posting-list contents.

This fragment has rigid uninterpreted keys and ordinary expressions. Private
carriers and promoted numeric equality need an uncertain projection in the
native adapter. Hash-probe costs and native resource ownership are not proved
by these structural laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.TermPathPosting

inductive Term
  | key (value : Nat)
  | var (name : Nat)
  | node (children : List Term)
  deriving Repr

def subst (environment : Nat → Term) : Term → Term
  | .key value => .key value
  | .var name => environment name
  | .node children => .node (children.map (subst environment))

inductive Projection
  | absent
  | uncertain
  | key (value : Nat)
  deriving DecidableEq, Repr

def project : Term → List Nat → Projection
  | .var _, _ => .uncertain
  | .key value, [] => .key value
  | .node _, [] => .absent
  | .key _, _ :: _ => .absent
  | .node children, position :: path =>
      match children[position]? with
      | none => .absent
      | some child => project child path

theorem rigid_subst (environment : Nat → Term) (term : Term)
    (path : List Nat) (key : Nat) (rigid : project term path = .key key) :
    project (subst environment term) path = .key key := by
  induction path generalizing term with
  | nil => cases term <;> simp_all [project, subst]
  | cons position path inductionHypothesis =>
    cases term with
    | key value => simp [project] at rigid
    | var name => simp [project] at rigid
    | node children =>
      cases child : children[position]? with
      | none => simp [project, child] at rigid
      | some selected =>
        have projected : project selected path = .key key := by
          simpa [project, child] using rigid
        simpa [project, subst, List.getElem?_map, child] using
          inductionHypothesis selected projected

theorem absent_subst (environment : Nat → Term) (term : Term)
    (path : List Nat) (absent : project term path = .absent) :
    project (subst environment term) path = .absent := by
  induction path generalizing term with
  | nil => cases term <;> simp_all [project, subst]
  | cons position path inductionHypothesis =>
    cases term with
    | key value => simp [project, subst]
    | var name => simp [project] at absent
    | node children =>
      cases child : children[position]? with
      | none => simp [project, subst, List.getElem?_map, child]
      | some selected =>
        have projected : project selected path = .absent := by
          simpa [project, child] using absent
        simpa [project, subst, List.getElem?_map, child] using
          inductionHypothesis selected projected

def accepts (key : Nat) : Projection → Bool
  | .absent => false
  | .uncertain => true
  | .key value => value == key

theorem unifier_not_refuted (environment : Nat → Term)
    (query row : Term) (path : List Nat) (key : Nat)
    (queryKey : project query path = .key key)
    (unifier : subst environment query = subst environment row) :
    accepts key (project row path) = true := by
  have queryProjection := rigid_subst environment query path key queryKey
  rw [unifier] at queryProjection
  cases rowProjection : project row path with
  | uncertain => rfl
  | absent =>
    have clash := absent_subst environment row path rowProjection
    rw [clash] at queryProjection
    cases queryProjection
  | key value =>
    have equal := rigid_subst environment row path value rowProjection
    rw [equal] at queryProjection
    have : value = key := Projection.key.inj queryProjection
    simp [accepts, this]

/-- Separate known and uncertain occurrence positions. The same payload may
occur at arbitrarily many different source positions. -/
def postings (path : List Nat) (key : Nat)
    (occurrences : List (Nat × Term)) : List Nat :=
  occurrences.filterMap fun occurrence =>
    if project occurrence.2 path = .key key then some occurrence.1 else none

def uncertain (path : List Nat) (occurrences : List (Nat × Term)) : List Nat :=
  occurrences.filterMap fun occurrence =>
    if project occurrence.2 path = .uncertain then some occurrence.1 else none

theorem postings_complete (path : List Nat) (key : Nat)
    (occurrences : List (Nat × Term)) :
    OccurrenceMerge.rows [postings path key occurrences, uncertain path occurrences] =
      ((occurrences.filter fun occurrence => accepts key (project occurrence.2 path)).map
        Prod.fst).toFinset := by
  ext position
  simp only [OccurrenceMerge.rows, Finset.union_empty, Finset.mem_union,
    List.mem_toFinset, postings, uncertain, List.mem_filterMap, List.mem_map,
    List.mem_filter]
  constructor
  · rintro (⟨occurrence, member, selected⟩ | ⟨occurrence, member, selected⟩)
    · split_ifs at selected with projection
      cases selected
      exact ⟨occurrence, ⟨member, by simp [accepts, projection]⟩, rfl⟩
    · split_ifs at selected with projection
      cases selected
      exact ⟨occurrence, ⟨member, by simp [accepts, projection]⟩, rfl⟩
  · rintro ⟨occurrence, ⟨member, accepted⟩, equal⟩
    cases projection : project occurrence.2 path with
    | absent => simp [accepts, projection] at accepted
    | uncertain =>
      exact Or.inr ⟨occurrence, member, by simp [projection, equal]⟩
    | key value =>
      have valueKey : value = key := by simpa [accepts, projection] using accepted
      exact Or.inl ⟨occurrence, member, by simp [projection, valueKey, equal]⟩

theorem exact_occurrences (environment : Nat → Term) (query : Term)
    (path : List Nat) (key : Nat) (queryKey : project query path = .key key)
    (occurrences : List (Nat × Term)) :
    (occurrences.filter fun occurrence => accepts key (project occurrence.2 path)).filter
        (fun occurrence => by classical exact decide (subst environment query = subst environment occurrence.2)) =
      occurrences.filter
        (fun occurrence => by classical exact decide (subst environment query = subst environment occurrence.2)) := by
  classical
  rw [List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  by_cases unifier : subst environment query = subst environment occurrence.2
  · have accepted := unifier_not_refuted environment query occurrence.2 path key queryKey unifier
    simp [accepted, unifier]
  · simp [unifier]

/-- Query and stored variables may be freshened into separate environments.
A rigid query path still cannot unify with a row refuted by that path. -/
theorem separate_unifier_not_refuted (queryEnvironment rowEnvironment : Nat → Term)
    (query row : Term) (path : List Nat) (key : Nat)
    (queryKey : project query path = .key key)
    (unifier : subst queryEnvironment query = subst rowEnvironment row) :
    accepts key (project row path) = true := by
  have queryProjection := rigid_subst queryEnvironment query path key queryKey
  rw [unifier] at queryProjection
  cases rowProjection : project row path with
  | uncertain => rfl
  | absent =>
    have clash := absent_subst rowEnvironment row path rowProjection
    rw [clash] at queryProjection
    cases queryProjection
  | key value =>
    have equal := rigid_subst rowEnvironment row path value rowProjection
    rw [equal] at queryProjection
    have : value = key := Projection.key.inj queryProjection
    simp [accepts, this]

/-- Deciding unifiability only on nonrefuted candidates gives the same
retained occurrence sequence as testing every row. False-positive candidates
still require the matcher; duplicates and the order of survivors are exact.
This concerns the row transformation, not matcher implementation or update
cost: a physical contraction may still traverse the whole source array. -/
theorem candidate_removal_exact (query : Term) (path : List Nat) (key : Nat)
    (queryKey : project query path = .key key) (occurrences : List (Nat × Term)) :
    (occurrences.filter fun occurrence => by
      classical
      exact !(accepts key (project occurrence.2 path) &&
        decide (∃ queryEnvironment rowEnvironment,
          subst queryEnvironment query = subst rowEnvironment occurrence.2))) =
    (occurrences.filter fun occurrence => by
      classical
      exact !decide (∃ queryEnvironment rowEnvironment,
        subst queryEnvironment query = subst rowEnvironment occurrence.2)) := by
  classical
  apply List.filter_congr
  intro occurrence _
  by_cases unifiable : ∃ queryEnvironment rowEnvironment,
      subst queryEnvironment query = subst rowEnvironment occurrence.2
  · obtain ⟨queryEnvironment, rowEnvironment, equal⟩ := unifiable
    have accepted := separate_unifier_not_refuted queryEnvironment rowEnvironment
      query occurrence.2 path key queryKey equal
    simp [accepted]
  · simp [unifiable]

/-- Equal facts at two positions remain two delivered occurrences. -/
example : postings [1] 7 [(0, .node [.var 0, .key 7]),
    (1, .node [.var 0, .key 7])] = [0, 1] := by decide

/-- A candidate need not unify: the selected path may agree while another
coordinate clashes. Removing every candidate would delete this row. -/
example : accepts 7 (project (.node [.key 2, .key 7]) [1]) = true ∧
    ∀ queryEnvironment rowEnvironment : Nat → Term,
      subst queryEnvironment (.node [.key 1, .key 7]) ≠
        subst rowEnvironment (.node [.key 2, .key 7]) := by
  simp [accepts, project, subst]

/-- A variable on an ancestor path can become the queried rigid subtree. -/
example : project (.node [.var 0]) [0, 1] = .uncertain ∧
    project (subst (fun _ => .node [.key 4, .key 7]) (.node [.var 0])) [0, 1] = .key 7 :=
  by simp [project, subst]

/-- Dropping uncertain rows would reject this actual unifier. -/
example : subst (fun _ => .key 7) (.key 7) =
    subst (fun _ => .key 7) (.var 0) ∧ postings [] 7 [(0, .var 0)] = [] ∧
    uncertain [] [(0, .var 0)] = [0] := by simp [subst, postings, uncertain, project]

end Mettapedia.Machines.Cursor.TermPathPosting

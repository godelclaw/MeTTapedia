import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceAdjacencyTracking

/-!
# Complete bidirectional equation adjacency after saturation

The queue invariant accounts for edges published before or after their source
representatives are visited. Draining the actual queue discharges the pending
neighbors and earns the adjacency part of the retained certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

def AdjacencyTracked (request : Request) (state : State request) : Prop :=
  ∀ edge ∈ state.edges,
    (edge.source ∈ representedPatterns request state → PatternTracked request state edge.receipt.target) ∧
    (edge.receipt.target ∈ representedPatterns request state → PatternTracked request state edge.source)

theorem expand_visit_origin (request : Request) (state : State request) (task : Task request)
    (representative : Representative request) (member : representative ∈ (expand request state task).visits) :
    task = .visit representative := by
  cases task with
  | visit actual =>
      simp only [expand] at member
      split at member
      · simp only [List.not_mem_nil] at member
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        subst representative
        rfl
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at member
      | cons edge tail =>
          by_cases backward : representative.pattern = edge.receipt.target
          · simp only [expand, dif_pos backward, List.not_mem_nil] at member
          · by_cases forward : representative.pattern = edge.source
            · simp only [expand, dif_neg backward, dif_pos forward, List.not_mem_nil] at member
            · simp only [expand, dif_neg backward, dif_neg forward, List.not_mem_nil] at member
  | «universe» => simp only [expand, List.not_mem_nil] at member
  | scanUniverse patterns => cases patterns <;> simp only [expand, List.not_mem_nil] at member
  | equation frame =>
      simp only [expand, expandEquation] at member
      split at member
      · split at member <;> simp only [List.not_mem_nil] at member
      · simp only [List.not_mem_nil] at member
  | rule frame =>
      simp only [expand, expandRule] at member
      split at member
      · split at member <;> simp only [List.not_mem_nil] at member
      · simp only [List.not_mem_nil] at member

theorem added_visit_tracks_neighbor (request : Request) (state : State request) (task : Task request)
    (remaining : List (Task request)) (agenda : state.agenda = task :: remaining)
    (representative : Representative request) (added : representative ∈ (expand request state task).visits)
    (edge : Edge request) (present : edge ∈ state.edges) (pattern : Syntax.Pattern)
    (joins : (representative.pattern = edge.source ∧ pattern = edge.receipt.target) ∨
      (representative.pattern = edge.receipt.target ∧ pattern = edge.source)) :
    PatternTracked request (tick request state) pattern := by
  have selected := expand_visit_origin request state task representative added
  subst task
  right
  refine ⟨.incoming representative state.edges, ?_, edge, present, joins⟩
  simp only [expand] at added
  split at added
  · simp only [List.not_mem_nil] at added
  · rename_i fresh
    simp only [tick, agenda, expand, if_neg fresh, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl (Or.inr True.intro)

theorem expand_edge_origin (request : Request) (state : State request) (task : Task request)
    (edge : Edge request) (member : edge ∈ (expand request state task).edges) :
    ∃ frame : EquationFrame request, task = .equation frame ∧
      ∃ answer : GeneralEquationJobExecution.Answer (equationRequest request frame.source frame.job),
        frame.state.answers[frame.cursor]? = some answer ∧ edge = ⟨frame.source, answer.val, answer.property⟩ := by
  cases task with
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases closed : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found closed] at member
            simp only [List.not_mem_nil] at member
          · rw [expand, expandEquation_pending request state frame found closed] at member
            simp only [List.not_mem_nil] at member
      | some answer =>
          rw [expand, expandEquation_found request state frame answer found] at member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          exact ⟨frame, rfl, answer, found, member⟩
  | visit representative => simp only [expand] at member; split at member <;> simp_all
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at member
      | cons edge tail =>
          by_cases backward : representative.pattern = edge.receipt.target
          · simp only [expand, dif_pos backward, List.not_mem_nil] at member
          · by_cases forward : representative.pattern = edge.source
            · simp only [expand, dif_neg backward, dif_pos forward, List.not_mem_nil] at member
            · simp only [expand, dif_neg backward, dif_neg forward, List.not_mem_nil] at member
  | «universe» => simp only [expand, List.not_mem_nil] at member
  | scanUniverse patterns => cases patterns <;> simp only [expand, List.not_mem_nil] at member
  | rule frame =>
      simp only [expand, expandRule] at member
      split at member
      · split at member <;> simp only [List.not_mem_nil] at member
      · simp only [List.not_mem_nil] at member

theorem new_edge_neighbors_tracked (request : Request) (state : State request) (task : Task request)
    (remaining : List (Task request)) (agenda : state.agenda = task :: remaining)
    (edge : Edge request) (member : edge ∈ (expand request state task).edges) :
    (edge.source ∈ representedPatterns request (tick request state) →
      PatternTracked request (tick request state) edge.receipt.target) ∧
    (edge.receipt.target ∈ representedPatterns request (tick request state) →
      PatternTracked request (tick request state) edge.source) := by
  obtain ⟨frame, selected, answer, found, same⟩ := expand_edge_origin request state task edge member
  subst task
  subst edge
  have visits : (tick request state).visited = state.visited := by
    simp only [tick, agenda, expand]
    rw [expandEquation_found request state frame answer found]
    simp only [List.append_nil]
  constructor
  · intro seen
    rw [representedPatterns, visits] at seen
    obtain ⟨next, present, promised⟩ := edgeDiscoveries_forward request state
      ⟨frame.source, answer.val, answer.property⟩ seen
    right
    refine ⟨next, ?_, promised⟩
    simp only [tick, agenda, expand]
    rw [expandEquation_found request state frame answer found]
    exact List.mem_append_left _ (List.mem_append_left _ present)
  · intro seen
    rw [representedPatterns, visits] at seen
    obtain ⟨next, present, promised⟩ := edgeDiscoveries_reverse request state
      ⟨frame.source, answer.val, answer.property⟩ seen
    right
    refine ⟨next, ?_, promised⟩
    simp only [tick, agenda, expand]
    rw [expandEquation_found request state frame answer found]
    exact List.mem_append_left _ (List.mem_append_left _ present)

theorem adjacencyTracked_tick {request : Request} {state : State request}
    (tracked : AdjacencyTracked request state) : AdjacencyTracked request (tick request state) := by
  intro edge member
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using tracked edge (by simpa only [tick, agenda] using member)
  | cons task remaining =>
      simp only [tick, agenda, List.mem_append] at member
      rcases member with prior | added
      · constructor
        · intro seen
          simp only [representedPatterns, tick, agenda, List.map_append, List.mem_append] at seen
          rcases seen with old | new
          · exact patternTracked_tick request state _ ((tracked edge prior).1 old)
          · obtain ⟨representative, added, same⟩ := List.mem_map.mp new
            exact added_visit_tracks_neighbor request state task remaining agenda representative added edge prior
              edge.receipt.target (Or.inl ⟨same, rfl⟩)
        · intro seen
          simp only [representedPatterns, tick, agenda, List.map_append, List.mem_append] at seen
          rcases seen with old | new
          · exact patternTracked_tick request state _ ((tracked edge prior).2 old)
          · obtain ⟨representative, added, same⟩ := List.mem_map.mp new
            exact added_visit_tracks_neighbor request state task remaining agenda representative added edge prior
              edge.source (Or.inr ⟨same, rfl⟩)
      · exact new_edge_neighbors_tracked request state task remaining agenda edge added

theorem adjacencyTracked_start (request : Request) : AdjacencyTracked request (start request) := by
  intro edge member
  simp only [start] at member
  split at member <;> simp only [List.not_mem_nil] at member

theorem reachable_adjacencyTracked {request : Request} {state : State request}
    (reached : Reachable request state) : AdjacencyTracked request state := by
  induction reached with
  | start => exact adjacencyTracked_start request
  | tick reached ih => exact adjacencyTracked_tick ih

theorem settled_adjacency_checked {request : Request} {state : State request}
    (reached : Reachable request state) (idle : state.agenda = []) : adjacencyChecked request state = true := by
  apply List.all_eq_true.mpr
  intro edge present
  apply decide_eq_true_eq.mpr
  have tracked := reachable_adjacencyTracked reached edge present
  exact ⟨fun source => tracked_when_settled (tracked.1 source) idle,
    fun target => tracked_when_settled (tracked.2 target) idle⟩

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

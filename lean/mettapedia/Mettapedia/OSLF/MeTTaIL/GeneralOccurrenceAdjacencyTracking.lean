import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceStepReadouts
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificate

/-!
# Retained visits of both equation-edge endpoints

A newly recorded edge schedules its neighbors at already visited endpoints.
A later representative visit scans earlier edges in both directions. Pending
visits and edge scans therefore retain every required neighbor through pauses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax

def TaskPatternPromise (request : Request) (pattern : Pattern) : Task request → Prop
  | .visit representative => representative.pattern = pattern
  | .incoming representative edges =>
      ∃ edge ∈ edges,
        (representative.pattern = edge.source ∧ pattern = edge.receipt.target) ∨
        (representative.pattern = edge.receipt.target ∧ pattern = edge.source)
  | _ => False

def PatternTracked (request : Request) (state : State request) (pattern : Pattern) : Prop :=
  pattern ∈ representedPatterns request state ∨
    ∃ task ∈ state.agenda, TaskPatternPromise request pattern task

theorem represented_tick_mono (request : Request) (state : State request) :
    ∀ pattern ∈ representedPatterns request state,
      pattern ∈ representedPatterns request (tick request state) := by
  intro pattern member
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using member
  | cons task remaining =>
      simp only [representedPatterns, tick, agenda, List.map_append, List.mem_append]
      exact Or.inl member

theorem visitedAt_found (request : Request) (state : State request) (pattern : Pattern)
    (member : pattern ∈ representedPatterns request state) :
    ∃ representative, visitedAt request state pattern = some representative := by
  obtain ⟨representative, present, same⟩ := List.mem_map.mp member
  cases found : state.visited.attach.find? (fun item => item.val.pattern == pattern) with
  | none =>
      have absent := (List.find?_eq_none.mp found) ⟨representative, present⟩ (List.mem_attach _ _)
      have succeeds : representative.pattern == pattern := by rw [same]; exact beq_self_eq_true _
      exact False.elim (absent succeeds)
  | some item =>
      have same : item.val.pattern = pattern := by
        simpa only [beq_iff_eq] using List.find?_some found
      exact ⟨⟨item.val, same⟩, by simp only [visitedAt, found, Option.bind_some, dif_pos same]⟩

theorem edgeDiscoveries_forward (request : Request) (state : State request) (edge : Edge request)
    (visited : edge.source ∈ representedPatterns request state) :
    ∃ task ∈ edgeDiscoveries request state edge, TaskPatternPromise request edge.receipt.target task := by
  obtain ⟨found, present⟩ := visitedAt_found request state edge.source visited
  refine ⟨.visit (edge.forward request found.val found.property), ?_, rfl⟩
  simp only [edgeDiscoveries, present, List.mem_append]
  exact Or.inl List.mem_cons_self

theorem edgeDiscoveries_reverse (request : Request) (state : State request) (edge : Edge request)
    (visited : edge.receipt.target ∈ representedPatterns request state) :
    ∃ task ∈ edgeDiscoveries request state edge, TaskPatternPromise request edge.source task := by
  obtain ⟨found, present⟩ := visitedAt_found request state edge.receipt.target visited
  refine ⟨.visit (edge.reverse request found.val found.property), ?_, rfl⟩
  simp only [edgeDiscoveries, present, List.mem_append]
  exact Or.inr List.mem_cons_self

theorem patternTracked_tick (request : Request) (state : State request) (pattern : Pattern)
    (tracked : PatternTracked request state pattern) : PatternTracked request (tick request state) pattern := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using tracked
  | cons task remaining =>
      rcases tracked with represented | ⟨pending, member, promise⟩
      · exact Or.inl (represented_tick_mono request state pattern represented)
      · rw [agenda, List.mem_cons] at member
        rcases member with current | later
        · subst pending
          cases task with
          | visit representative =>
              left
              by_cases seen : (state.visited.map Representative.pattern).contains representative.pattern = true
              · have represented : representative.pattern ∈ representedPatterns request state := by
                  simpa only [representedPatterns, List.contains_iff_mem] using seen
                exact represented_tick_mono request state pattern (promise ▸ represented)
              · simp only [representedPatterns, tick, agenda, expand, if_neg seen, List.map_append,
                  List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                exact Or.inr promise.symm
          | incoming representative edges =>
              obtain ⟨edge, present, joins⟩ := promise
              cases edges with
              | nil => exact False.elim (List.not_mem_nil present)
              | cons first tail =>
                  rw [List.mem_cons] at present
                  rcases present with same | later
                  · subst edge
                    right
                    by_cases backward : representative.pattern = first.receipt.target
                    · refine ⟨.visit (first.reverse request representative backward), ?_, ?_⟩
                      · simp only [tick, agenda, expand, dif_pos backward, List.mem_append,
                          List.mem_cons, List.not_mem_nil, or_false]
                        exact Or.inl (Or.inl True.intro)
                      · rcases joins with ⟨forward, target⟩ | ⟨_, source⟩
                        · exact forward.symm.trans backward |>.trans target.symm
                        · exact source.symm
                    · rcases joins with ⟨forward, target⟩ | ⟨impossible, _⟩
                      · refine ⟨.visit (first.forward request representative forward), ?_, target.symm⟩
                        simp only [tick, agenda, expand, dif_neg backward, dif_pos forward,
                          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                        exact Or.inl (Or.inl True.intro)
                      · exact False.elim (backward impossible)
                  · right
                    refine ⟨.incoming representative tail, ?_, edge, later, joins⟩
                    by_cases backward : representative.pattern = first.receipt.target
                    · simp only [tick, agenda, expand, dif_pos backward, List.mem_append,
                        List.mem_cons, List.not_mem_nil, or_false]
                      exact Or.inl (Or.inr True.intro)
                    · by_cases forward : representative.pattern = first.source
                      · simp only [tick, agenda, expand, dif_neg backward, dif_pos forward,
                          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                        exact Or.inl (Or.inr True.intro)
                      · simp only [tick, agenda, expand, dif_neg backward, dif_neg forward,
                          List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                        exact Or.inl True.intro
          | «universe» | scanUniverse _ | equation _ | rule _ => exact False.elim promise
        · right
          exact ⟨pending, by simp only [tick, agenda, List.mem_append]; exact Or.inr later, promise⟩

theorem tracked_when_settled {request : Request} {state : State request} {pattern : Pattern}
    (tracked : PatternTracked request state pattern) (idle : state.agenda = []) :
    pattern ∈ representedPatterns request state := by
  rcases tracked with represented | ⟨task, member, _⟩
  · exact represented
  · simp only [idle, List.not_mem_nil] at member

theorem root_tracked_start {request : Request} (admitted : Admitted request) :
    PatternTracked request (start request) request.root := by
  right
  refine ⟨.visit ⟨request.root, [], .nil _⟩, ?_, rfl⟩
  simp [start, Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete admitted.rootSorted]

theorem reachable_root_tracked {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) : PatternTracked request state request.root := by
  induction reached with
  | start => exact root_tracked_start admitted
  | tick reached ih => exact patternTracked_tick request _ _ ih

theorem settled_root_represented {request : Request} (admitted : Admitted request)
    {state : State request} (reached : Reachable request state) (idle : state.agenda = []) :
    request.root ∈ representedPatterns request state := tracked_when_settled (reachable_root_tracked admitted reached) idle

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

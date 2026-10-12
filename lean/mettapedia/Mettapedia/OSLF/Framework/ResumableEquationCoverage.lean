import Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier
import Mettapedia.OSLF.Framework.FiniteEquationCoverage

/-!
# Equation and primitive-occurrence coverage earned by queue traversal

The queue invariant records every discovered equation target, every enumerated
primitive occurrence and every unresolved provider obligation. Quiescence then
supplies a finite equation certificate and complete primitive readouts. Semantic
coverage additionally requires independent one-step provider comparisons.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ResumableEquationCoverage

open ResumableEquationOccurrenceFrontier

universe u v w z

variable {Node : Type u} {EquationOrigin : Type v}
  {Occurrence : Type w} {Obligation : Type z}

/-- A discovered representative remains either scheduled or already visited. -/
def Covered (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (node : Node) : Prop :=
  node ∈ snapshot.visited.map Entry.state ∨ node ∈ snapshot.pending.map Entry.state

/-- Queue traversal retains all one-step work and full indexed firing readouts. -/
structure Invariant (model : Model Node EquationOrigin Occurrence Obligation)
    (source : Node) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) : Prop where
  source : Covered snapshot source
  neighbors : ∀ entry ∈ snapshot.visited, ∀ edge ∈ (model.equations entry.state).answers,
    Covered snapshot edge.2
  readouts : ∀ entry ∈ snapshot.visited,
    ∀ receipt ∈ readouts entry (model.firings entry.state).answers,
      receipt ∈ snapshot.receipts
  equationObligations : ∀ entry ∈ snapshot.visited,
    ∀ reason ∈ (model.equations entry.state).unresolved,
      (⟨entry, .equation, reason⟩ : Parked Node EquationOrigin Obligation) ∈ snapshot.parked
  firingObligations : ∀ entry ∈ snapshot.visited,
    ∀ reason ∈ (model.firings entry.state).unresolved,
      (⟨entry, .firing, reason⟩ : Parked Node EquationOrigin Obligation) ∈ snapshot.parked

theorem initial_invariant (model : Model Node EquationOrigin Occurrence Obligation)
    (source : Node) : Invariant model source (initial source) := by
  constructor
  · exact Or.inr (by simp [initial])
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem tick_visited_mono [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (entry : Entry Node EquationOrigin) (member : entry ∈ snapshot.visited) :
    entry ∈ (tick model snapshot).visited := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using member
  | cons head rest =>
    by_cases seen : head.state ∈ snapshot.visited.map Entry.state
    · simpa [tick, pending, seen] using member
    · simp [tick, pending, seen, member]

theorem tick_parked_mono [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (entry : Parked Node EquationOrigin Obligation) (member : entry ∈ snapshot.parked) :
    entry ∈ (tick model snapshot).parked := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using member
  | cons head rest =>
    by_cases seen : head.state ∈ snapshot.visited.map Entry.state
    · simpa [tick, pending, seen] using member
    · simp [tick, pending, seen, member]

theorem tick_receipts_mono [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (receipt : Receipt Node EquationOrigin Occurrence) (member : receipt ∈ snapshot.receipts) :
    receipt ∈ (tick model snapshot).receipts := by
  obtain ⟨added, equal⟩ := tick_receipts_extend model snapshot
  rw [equal]
  exact List.mem_append_left added member

/-- Removing a scheduled head never loses its state: it is retained as visited. -/
theorem tick_covers_old [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) (node : Node)
    (covered : Covered snapshot node) : Covered (tick model snapshot) node := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using covered
  | cons head rest =>
    rcases covered with visited | scheduled
    · obtain ⟨entry, member, equal⟩ := List.mem_map.mp visited
      exact Or.inl (List.mem_map.mpr ⟨entry, tick_visited_mono model snapshot entry member, equal⟩)
    · simp only [pending, List.map_cons, List.mem_cons] at scheduled
      by_cases seen : head.state ∈ snapshot.visited.map Entry.state
      · rcases scheduled with equal | member
        · subst node
          exact Or.inl (by simp [tick, pending, seen])
        · exact Or.inr (by simpa [tick, pending, seen] using member)
      · rcases scheduled with equal | member
        · subst node
          exact Or.inl (by simp [tick, pending, seen])
        · exact Or.inr (by simp [tick, pending, seen, member])

/-- Every fresh equation neighbor is retained even when duplicate-state
suppression prevents adding another queue entry. -/
theorem tick_covers_neighbor [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (head : Entry Node EquationOrigin) (rest : List (Entry Node EquationOrigin))
    (pending : snapshot.pending = head :: rest)
    (fresh : head.state ∉ snapshot.visited.map Entry.state)
    (edge : EquationOrigin × Node) (member : edge ∈ (model.equations head.state).answers) :
    Covered (tick model snapshot) edge.2 := by
  let known := head.state :: (snapshot.visited.map Entry.state ++ rest.map Entry.state)
  by_cases already : edge.2 ∈ known
  · simp only [known, List.mem_cons, List.mem_append] at already
    rcases already with equal | visited | scheduled
    · exact Or.inl (by simp [tick, pending, fresh, equal])
    · exact Or.inl (by simp [tick, pending, fresh, visited])
    · exact Or.inr (by simp [tick, pending, fresh, scheduled])
  · apply Or.inr
    simp only [tick, pending, fresh, if_false]
    apply List.mem_map.mpr
    refine ⟨head.extend edge, List.mem_append_right _ ?_, rfl⟩
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_map.mpr ⟨edge, member, rfl⟩
    · simpa [Entry.extend, known] using already

/-- The traversal invariant covers equation alternatives, all indexed primitive
readouts and every parked provider obligation. -/
theorem tick_invariant [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : Invariant model source snapshot) : Invariant model source (tick model snapshot) := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using before
  | cons head rest =>
    by_cases seen : head.state ∈ snapshot.visited.map Entry.state
    · constructor
      · exact tick_covers_old model snapshot source before.source
      · intro entry member edge edgeMember
        have old : entry ∈ snapshot.visited := by simpa [tick, pending, seen] using member
        exact tick_covers_old model snapshot edge.2 (before.neighbors entry old edge edgeMember)
      · intro entry member receipt receiptMember
        have old : entry ∈ snapshot.visited := by simpa [tick, pending, seen] using member
        exact tick_receipts_mono model snapshot receipt (before.readouts entry old receipt receiptMember)
      · intro entry member reason reasonMember
        have old : entry ∈ snapshot.visited := by simpa [tick, pending, seen] using member
        exact tick_parked_mono model snapshot _ (before.equationObligations entry old reason reasonMember)
      · intro entry member reason reasonMember
        have old : entry ∈ snapshot.visited := by simpa [tick, pending, seen] using member
        exact tick_parked_mono model snapshot _ (before.firingObligations entry old reason reasonMember)
    · constructor
      · exact tick_covers_old model snapshot source before.source
      · intro entry member edge edgeMember
        have split : entry ∈ snapshot.visited ∨ entry = head := by
          simpa [tick, pending, seen] using member
        rcases split with old | equal
        · exact tick_covers_old model snapshot edge.2 (before.neighbors entry old edge edgeMember)
        · subst entry
          exact tick_covers_neighbor model snapshot head rest pending seen edge edgeMember
      · intro entry member receipt receiptMember
        have split : entry ∈ snapshot.visited ∨ entry = head := by
          simpa [tick, pending, seen] using member
        rcases split with old | equal
        · exact tick_receipts_mono model snapshot receipt (before.readouts entry old receipt receiptMember)
        · subst entry
          simpa only [tick, pending, seen, if_false] using
            (List.mem_append_right snapshot.receipts receiptMember)
      · intro entry member reason reasonMember
        have split : entry ∈ snapshot.visited ∨ entry = head := by
          simpa [tick, pending, seen] using member
        rcases split with old | equal
        · exact tick_parked_mono model snapshot _ (before.equationObligations entry old reason reasonMember)
        · subst entry
          change (⟨head, .equation, reason⟩ : Parked Node EquationOrigin Obligation) ∈
            (tick model snapshot).parked
          simp only [tick, pending, seen, if_false]
          exact List.mem_append_right _ (List.mem_append_left _
            (List.mem_map.mpr ⟨reason, reasonMember, rfl⟩))
      · intro entry member reason reasonMember
        have split : entry ∈ snapshot.visited ∨ entry = head := by
          simpa [tick, pending, seen] using member
        rcases split with old | equal
        · exact tick_parked_mono model snapshot _ (before.firingObligations entry old reason reasonMember)
        · subst entry
          change (⟨head, .firing, reason⟩ : Parked Node EquationOrigin Obligation) ∈
            (tick model snapshot).parked
          simp only [tick, pending, seen, if_false]
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_map.mpr ⟨reason, reasonMember, rfl⟩))

theorem run_invariant [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (fuel : Nat) (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : Invariant model source snapshot) :
    Invariant model source (run model fuel snapshot) := by
  induction fuel generalizing snapshot with
  | zero => exact before
  | succ fuel ih => exact ih (tick model snapshot) (tick_invariant model source snapshot before)

/-- At a quiescent state every previously discovered target has been visited. -/
theorem covered_visited_of_quiescent
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (quiet : quiescent snapshot = true) (node : Node) (covered : Covered snapshot node) :
    node ∈ snapshot.visited.map Entry.state := by
  rcases covered with visited | pending
  · exact visited
  · simp [(quiescent_iff snapshot).mp quiet |>.1] at pending

/-- A visited provider cannot retain an unresolved equation obligation when the
whole search is quiescent. -/
theorem equation_provider_complete_of_quiescent
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (invariant : Invariant model source snapshot) (quiet : quiescent snapshot = true)
    (entry : Entry Node EquationOrigin) (member : entry ∈ snapshot.visited) :
    (model.equations entry.state).unresolved = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reason reasonMember
  have parked := invariant.equationObligations entry member reason reasonMember
  simp [(quiescent_iff snapshot).mp quiet |>.2] at parked

theorem firing_provider_complete_of_quiescent
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (invariant : Invariant model source snapshot) (quiet : quiescent snapshot = true)
    (entry : Entry Node EquationOrigin) (member : entry ∈ snapshot.visited) :
    (model.firings entry.state).unresolved = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reason reasonMember
  have parked := invariant.firingObligations entry member reason reasonMember
  simp [(quiescent_iff snapshot).mp quiet |>.2] at parked

/-- The executable equation-neighbor readout retains each target of the current
provider. Its independent meaning is a separate one-step contract. -/
def equationNeighbors (model : Model Node EquationOrigin Occurrence Obligation)
    (node : Node) : List Node := (model.equations node).answers.map Prod.snd

/-- The concrete certificate is extracted from the actual visited histories. -/
def coverageCertificate (snapshot : Snapshot Node EquationOrigin Occurrence Obligation) :
    FiniteEquationCoverage.Certificate Node where
  walks := snapshot.visited.map (fun entry => entry.conversions.map Prod.snd)

def EnumeratedEquation (model : Model Node EquationOrigin Occurrence Obligation)
    (origin : EquationOrigin) (source target : Node) : Prop :=
  (origin, target) ∈ (model.equations source).answers

def EnumeratedFiring (model : Model Node EquationOrigin Occurrence Obligation)
    (source : Node) (origin : Occurrence) (target : Node) : Prop :=
  (origin, target) ∈ (model.firings source).answers

/-- Projecting an actual provider trace gives a valid executable equation walk
whose endpoint is the retained representative. -/
theorem trace_walk_checked [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (source target : Node) (trace : List (EquationOrigin × Node))
    (valid : TraceValid (EnumeratedEquation model) source trace target) :
    FiniteEquationCoverage.checkWalk (equationNeighbors model) source (trace.map Prod.snd) = true ∧
      FiniteEquationCoverage.walkEnd source (trace.map Prod.snd) = target := by
  induction trace generalizing source with
  | nil => exact ⟨rfl, valid⟩
  | cons edge rest ih =>
    have next := ih edge.2 valid.2
    have member : edge.2 ∈ equationNeighbors model source :=
      List.mem_map.mpr ⟨edge, valid.1, rfl⟩
    exact ⟨by simpa [FiniteEquationCoverage.checkWalk, member] using next.1, next.2⟩

/-- Internal path provenance is proved directly from traversal. This theorem
does not assert that a provider's answers define the intended semantics. -/
theorem run_enumerated_valid [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node) (fuel : Nat) :
    (run model fuel (initial source)).Valid
      (EnumeratedEquation model) (EnumeratedFiring model) source := by
  exact run_valid model (EnumeratedEquation model) (EnumeratedFiring model)
    (fun _ _ member => member) (fun _ _ member => member) source fuel (initial source)
    (initial_valid (EnumeratedEquation model) (EnumeratedFiring model) source)

/-- Certificate representatives are exactly the source plus the actually
visited states, independently of duplicate conversion histories. -/
theorem certificate_representatives_spec [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (valid : snapshot.Valid (EnumeratedEquation model) (EnumeratedFiring model) source)
    (node : Node) :
    node ∈ (coverageCertificate snapshot).representatives source ↔
      node = source ∨ node ∈ snapshot.visited.map Entry.state := by
  simp only [FiniteEquationCoverage.Certificate.representatives, List.mem_cons,
    List.mem_map, coverageCertificate]
  constructor
  · rintro (equal | ⟨walk, ⟨entry, member, rfl⟩, endEqual⟩)
    · exact Or.inl equal
    · have endpoint := (trace_walk_checked model source entry.state entry.conversions
        (valid.visited entry member)).2
      exact Or.inr ⟨entry, member, endpoint.symm.trans endEqual⟩
  · rintro (equal | ⟨entry, member, equal⟩)
    · exact Or.inl equal
    · have endpoint := (trace_walk_checked model source entry.state entry.conversions
        (valid.visited entry member)).2
      exact Or.inr ⟨entry.conversions.map Prod.snd, ⟨entry, member, rfl⟩,
        endpoint.trans equal⟩

/-- Queue quiescence earns, rather than assumes, the executable equation-class
closure check for the extracted finite certificate. -/
theorem quiescent_certificate_checked [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (invariant : Invariant model source snapshot)
    (valid : snapshot.Valid (EnumeratedEquation model) (EnumeratedFiring model) source)
    (quiet : quiescent snapshot = true) :
    (coverageCertificate snapshot).check (equationNeighbors model) source = true := by
  apply (FiniteEquationCoverage.check_spec _ _ _).mpr
  constructor
  · intro walk member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    exact (trace_walk_checked model source entry.state entry.conversions
      (valid.visited entry entryMember)).1
  · intro representative represented next neighbor
    have visited : representative ∈ snapshot.visited.map Entry.state := by
      rcases (certificate_representatives_spec model source snapshot valid representative).mp
        represented with equal | visited
      · subst representative
        exact covered_visited_of_quiescent snapshot quiet source invariant.source
      · exact visited
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp visited
    subst representative
    obtain ⟨edge, edgeMember, edgeEqual⟩ := List.mem_map.mp neighbor
    have covered := invariant.neighbors entry entryMember edge edgeMember
    apply (certificate_representatives_spec model source snapshot valid next).mpr
    apply Or.inr
    exact edgeEqual ▸ covered_visited_of_quiescent snapshot quiet edge.2 covered

/-- No additional finite-closure hypothesis is needed for an actual quiescent
run: the queue invariant supplies the whole executable check. -/
theorem quiescent_run_certificate_checked [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) :
    (coverageCertificate (run model fuel (initial source))).check
      (equationNeighbors model) source = true := by
  exact quiescent_certificate_checked model source (run model fuel (initial source))
    (run_invariant model source fuel (initial source) (initial_invariant model source))
    (run_enumerated_valid model source fuel) quiet

/-- Every enumeration ordinal, not merely each returned target, is retained. -/
theorem run_covers_indexed_firing [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node) (fuel : Nat)
    (entry : Entry Node EquationOrigin)
    (visited : entry ∈ (run model fuel (initial source)).visited)
    (answer : Occurrence × Node) (index : Nat)
    (selected : (answer, index) ∈ (model.firings entry.state).answers.zipIdx) :
    (⟨entry, index, answer.1, answer.2⟩ : Receipt Node EquationOrigin Occurrence) ∈
      (run model fuel (initial source)).receipts := by
  have invariant := run_invariant model source fuel (initial source) (initial_invariant model source)
  exact invariant.readouts entry visited _ (List.mem_map.mpr ⟨(answer, index), selected, rfl⟩)

/-- Each representative is expanded once; its entire ordered firing list is
appended once. Equation conversions do not append primitive readouts. -/
theorem tick_receipts_exact [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : snapshot.receipts = snapshot.visited.flatMap
      (fun entry => readouts entry (model.firings entry.state).answers)) :
    (tick model snapshot).receipts = (tick model snapshot).visited.flatMap
      (fun entry => readouts entry (model.firings entry.state).answers) := by
  cases pending : snapshot.pending with
  | nil => simpa [tick, pending] using before
  | cons head rest =>
    by_cases seen : head.state ∈ snapshot.visited.map Entry.state
    · simpa [tick, pending, seen] using before
    · simp [tick, pending, seen, before]

theorem run_receipts_exact [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (fuel : Nat)
    (snapshot : Snapshot Node EquationOrigin Occurrence Obligation)
    (before : snapshot.receipts = snapshot.visited.flatMap
      (fun entry => readouts entry (model.firings entry.state).answers)) :
    (run model fuel snapshot).receipts = (run model fuel snapshot).visited.flatMap
      (fun entry => readouts entry (model.firings entry.state).answers) := by
  induction fuel generalizing snapshot with
  | zero => exact before
  | succ fuel ih => exact ih (tick model snapshot) (tick_receipts_exact model snapshot before)

/-- Exact receipt coverage includes authored answers and their enumeration
ordinals. Target membership alone would not establish this statement. -/
theorem run_receipt_spec [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation) (source : Node) (fuel : Nat)
    (receipt : Receipt Node EquationOrigin Occurrence) :
    receipt ∈ (run model fuel (initial source)).receipts ↔
      ∃ entry ∈ (run model fuel (initial source)).visited,
        ∃ answerIndex ∈ (model.firings entry.state).answers.zipIdx,
          (⟨entry, answerIndex.2, answerIndex.1.1, answerIndex.1.2⟩ :
            Receipt Node EquationOrigin Occurrence) = receipt := by
  rw [run_receipts_exact model fuel (initial source) (by simp [initial])]
  simp [List.mem_flatMap, readouts, List.mem_map]

/-- Selecting a finite firing answer supplies its actual enumeration ordinal. -/
theorem exists_answer_ordinal (answers : List (Occurrence × Node))
    (answer : Occurrence × Node) (member : answer ∈ answers) :
    ∃ index, (answer, index) ∈ answers.zipIdx := by
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
  exact ⟨index, List.mk_mem_zipIdx_iff_getElem?.mpr selected⟩

section Semantics

variable [DecidableEq Node]
    (model : Model Node EquationOrigin Occurrence Obligation)
    (equation : Node → Node → Prop)
    (equations_sound : ∀ node next, next ∈ equationNeighbors model node →
      equation node next ∨ equation next node)
    (equations_complete : ∀ node, (model.equations node).unresolved = [] →
      ∀ next, equation node next ∨ equation next node → next ∈ equationNeighbors model node)
    (firing : Node → Occurrence → Node → Prop)
    (firings_sound : ∀ node answer, answer ∈ (model.firings node).answers →
      firing node answer.1 answer.2)
    (firings_complete : ∀ node, (model.firings node).unresolved = [] →
      ∀ origin target, firing node origin target →
        (origin, target) ∈ (model.firings node).answers)

include equations_sound equations_complete

/-- Quiescence turns the earned finite checker into full coverage of the
independently specified equation class. Completeness is only needed at visited
states, where the absence of unresolved obligations has already been proved. -/
theorem quiescent_visited_iff_equivalent (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) (node : Node) :
    node ∈ (run model fuel (initial source)).visited.map Entry.state ↔
      Relation.EqvGen equation source node := by
  let snapshot := run model fuel (initial source)
  have invariant := run_invariant model source fuel (initial source) (initial_invariant model source)
  have valid := run_enumerated_valid model source fuel
  have rootVisited := covered_visited_of_quiescent snapshot quiet source invariant.source
  have represented := certificate_representatives_spec model source snapshot valid node
  have localComplete : ∀ representative ∈ (coverageCertificate snapshot).representatives source,
      ∀ next, equation representative next ∨ equation next representative →
        next ∈ equationNeighbors model representative := by
    intro representative member next edge
    have visited : representative ∈ snapshot.visited.map Entry.state := by
      rcases (certificate_representatives_spec model source snapshot valid representative).mp member with
        equal | visited
      · simpa only [equal] using rootVisited
      · exact visited
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp visited
    have complete := equation_provider_complete_of_quiescent model source snapshot invariant
      quiet entry entryMember
    exact equations_complete representative (equal ▸ complete) next edge
  have classes := FiniteEquationCoverage.representatives_spec_of_local_complete equation
    (equationNeighbors model) equations_sound (coverageCertificate snapshot) source
    (quiescent_run_certificate_checked model source fuel quiet) localComplete node
  constructor
  · intro visited
    exact classes.mp (represented.mpr (Or.inr visited))
  · intro equivalent
    rcases represented.mp (classes.mpr equivalent) with equal | visited
    · simpa only [equal] using rootVisited
    · exact visited

omit equations_complete
include firings_sound

/-- Partial execution receipts are sound independently of frontier exhaustion. -/
theorem actual_receipt_sound (source : Node) (fuel : Nat)
    (receipt : Receipt Node EquationOrigin Occurrence)
    (member : receipt ∈ (run model fuel (initial source)).receipts) :
    Relation.EqvGen equation source receipt.representative.state ∧
      firing receipt.representative.state receipt.origin receipt.target := by
  have valid := (run_enumerated_valid model source fuel).receipts receipt member
  have trace := trace_walk_checked model source receipt.representative.state
    receipt.representative.conversions valid.1
  have equivalent := FiniteEquationCoverage.checkWalk_sound equation
    (equationNeighbors model) equations_sound source (receipt.representative.conversions.map Prod.snd)
    trace.1
  exact ⟨trace.2 ▸ equivalent, firings_sound _ _ valid.2⟩

omit firings_sound
include equations_complete firings_complete

/-- An independently admitted primitive firing at an equation-equivalent source
is represented by a complete actual receipt, including its enumeration ordinal. -/
theorem actual_firing_coverage (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true)
    (representative : Node) (origin : Occurrence) (target : Node)
    (before : Relation.EqvGen equation source representative)
    (fire : firing representative origin target) :
    ∃ entry index, entry ∈ (run model fuel (initial source)).visited ∧
      entry.state = representative ∧
      ((origin, target), index) ∈ (model.firings representative).answers.zipIdx ∧
      (⟨entry, index, origin, target⟩ : Receipt Node EquationOrigin Occurrence) ∈
        (run model fuel (initial source)).receipts := by
  have visited := (quiescent_visited_iff_equivalent model equation equations_sound
    equations_complete source fuel quiet representative).mpr before
  obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp visited
  have invariant := run_invariant model source fuel (initial source) (initial_invariant model source)
  have complete := firing_provider_complete_of_quiescent model source _ invariant quiet entry entryMember
  have answer := firings_complete representative (equal ▸ complete) origin target fire
  obtain ⟨index, selected⟩ := exists_answer_ordinal _ (origin, target) answer
  refine ⟨entry, index, entryMember, equal, selected, ?_⟩
  apply run_covers_indexed_firing model source fuel entry entryMember (origin, target) index
  simpa only [equal] using selected

include firings_sound

/-- The actual returned receipts cover exactly the outgoing successor classes
of the independently specified equation-saturated operational semantics. -/
theorem actual_endpoint_coverage (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) (next : Node) :
    (∃ receipt ∈ (run model fuel (initial source)).receipts,
      Relation.EqvGen equation receipt.target next) ↔
        FiniteEquationCoverage.ModuloStep equation
          (fun state (answer : Occurrence × Node) => firing state answer.1 answer.2)
          Prod.snd source next := by
  constructor
  · rintro ⟨receipt, member, after⟩
    have sound := actual_receipt_sound model equation equations_sound firing firings_sound
      source fuel receipt member
    exact ⟨receipt.representative.state, (receipt.origin, receipt.target), sound.1, sound.2, after⟩
  · rintro ⟨representative, ⟨origin, target⟩, before, fire, after⟩
    obtain ⟨entry, index, _, _, _, member⟩ := actual_firing_coverage model equation
      equations_sound equations_complete firing firings_complete source fuel quiet
      representative origin target before fire
    exact ⟨⟨entry, index, origin, target⟩, member, after⟩

/-- Endpoint observations of the actual retained receipt list. -/
def actualTargets (source : Node) (fuel : Nat) : List Node :=
  (run model fuel (initial source)).receipts.map Receipt.target

/-- Actual quotient endpoints retain the separately available complete receipts. -/
def actualClasses (source : Node) (fuel : Nat) :
    List (Quotient (Relation.EqvGen.setoid equation)) :=
  (run model fuel (initial source)).receipts.map
    (fun receipt => Quotient.mk (Relation.EqvGen.setoid equation) receipt.target)

/-- The actual queue executor computes precisely the outgoing quotient classes. -/
theorem actual_class_coverage (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) (next : Node) :
    Quotient.mk (Relation.EqvGen.setoid equation) next ∈ actualClasses model equation source fuel ↔
      FiniteEquationCoverage.ModuloStep equation
        (fun state (answer : Occurrence × Node) => firing state answer.1 answer.2)
        Prod.snd source next := by
  rw [← actual_endpoint_coverage model equation equations_sound equations_complete
    firing firings_sound firings_complete source fuel quiet next]
  simp only [actualClasses, List.mem_map]
  constructor
  · rintro ⟨receipt, member, equal⟩
    exact ⟨receipt, member, Quotient.exact equal⟩
  · rintro ⟨receipt, member, equivalent⟩
    exact ⟨receipt, member, Quotient.sound equivalent⟩

/-- Executable diamond readout from the actual returned endpoints. -/
theorem actual_any_iff_diamond (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) (test : Node → Bool)
    (invariant : ∀ initial next, Relation.EqvGen equation initial next → test initial = test next) :
    (actualTargets model source fuel).any test = true ↔
      ∃ next, FiniteEquationCoverage.ModuloStep equation
        (fun state (answer : Occurrence × Node) => firing state answer.1 answer.2)
        Prod.snd source next ∧ test next = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨next, member, succeeds⟩
    obtain ⟨receipt, receiptMember, rfl⟩ := List.mem_map.mp member
    have sound := actual_receipt_sound model equation equations_sound firing firings_sound
      source fuel receipt receiptMember
    exact ⟨receipt.target,
      ⟨receipt.representative.state, (receipt.origin, receipt.target), sound.1, sound.2, .refl _⟩,
      succeeds⟩
  · rintro ⟨next, step, succeeds⟩
    obtain ⟨receipt, member, after⟩ := (actual_endpoint_coverage model equation
      equations_sound equations_complete firing firings_sound firings_complete
      source fuel quiet next).mpr step
    exact ⟨receipt.target, List.mem_map.mpr ⟨receipt, member, rfl⟩,
      (invariant _ _ after).trans succeeds⟩

/-- This universal observation quantifies over outgoing successors. No incoming
predecessor completeness is asserted by the equation frontier. -/
theorem actual_all_iff_outgoingUniversal (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) (test : Node → Bool)
    (invariant : ∀ initial next, Relation.EqvGen equation initial next → test initial = test next) :
    (actualTargets model source fuel).all test = true ↔
      ∀ next, FiniteEquationCoverage.ModuloStep equation
        (fun state (answer : Occurrence × Node) => firing state answer.1 answer.2)
        Prod.snd source next → test next = true := by
  rw [List.all_eq_true]
  constructor
  · intro universal next step
    obtain ⟨receipt, member, after⟩ := (actual_endpoint_coverage model equation
      equations_sound equations_complete firing firings_sound firings_complete
      source fuel quiet next).mpr step
    exact (invariant _ _ after).symm.trans
      (universal _ (List.mem_map.mpr ⟨receipt, member, rfl⟩))
  · intro universal next member
    obtain ⟨receipt, receiptMember, rfl⟩ := List.mem_map.mp member
    have sound := actual_receipt_sound model equation equations_sound firing firings_sound
      source fuel receipt receiptMember
    exact universal receipt.target
      ⟨receipt.representative.state, (receipt.origin, receipt.target), sound.1, sound.2, .refl _⟩

/-- An empty quiescent receipt list establishes semantic absence. Empty partial
lists are excluded by the explicit quiescence and provider comparisons. -/
theorem actual_empty_iff_no_step (source : Node) (fuel : Nat)
    (quiet : quiescent (run model fuel (initial source)) = true) :
    (run model fuel (initial source)).receipts = [] ↔
      ¬ ∃ next, FiniteEquationCoverage.ModuloStep equation
        (fun state (answer : Occurrence × Node) => firing state answer.1 answer.2)
        Prod.snd source next := by
  constructor
  · intro empty ⟨next, step⟩
    obtain ⟨receipt, member, _⟩ := (actual_endpoint_coverage model equation
      equations_sound equations_complete firing firings_sound firings_complete
      source fuel quiet next).mpr step
    simp [empty] at member
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro receipt member
    have sound := actual_receipt_sound model equation equations_sound firing firings_sound
      source fuel receipt member
    exact absent ⟨receipt.target,
      ⟨receipt.representative.state, (receipt.origin, receipt.target), sound.1, sound.2, .refl _⟩⟩

end Semantics

end Mettapedia.OSLF.Framework.ResumableEquationCoverage

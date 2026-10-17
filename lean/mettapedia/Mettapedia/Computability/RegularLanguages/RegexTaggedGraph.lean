import Mettapedia.Computability.RegularLanguages.OrderedGraphSearch
import Mettapedia.Computability.RegularLanguages.RegexMatchObservations

/-!
# Tagged regex transitions and first-visit epsilon closure

Raw derivations independently follow graph edges, including capture saves and
branch decisions. Erasing capture saves to jumps preserves and reflects raw
reachability. The executable epsilon closure uses a separate, finite first-visit
policy, per program counter and input position. Capture registers do not affect
control; their erasure commutes with this policy, not merely with acceptance.

These statements do not establish that a surface compiler realizes Rust's
nullable/capture semantics. Raw derivations and cycle-suppressed closure are
different objects. In particular, not every raw capture history survives the
first-visit policy.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexTaggedGraph

open OrderedGraphSearch (Point Probe successor)

universe u v w z

inductive Node (State : Type u) (Class : Type v) (Assertion : Type w) (Tag : Type z) where
  | accept (tag : Tag)
  | dead
  | jump (next : State)
  | choice (first second : State)
  | consume (class_ : Class) (next : State)
  | assertion (assertion_ : Assertion) (next : State)
  | save (slot : Nat) (next : State)

abbrev Registers (length : Nat) := Nat → Option (Fin (length + 1))

structure Thread (State : Type u) (length : Nat) where
  point : Point State length
  registers : Registers length
  choices : List Bool

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def write (registers : Registers length) (slot : Nat) (position : Fin (length + 1)) :
    Registers length :=
  fun other => if other = slot then some position else registers other

theorem write_same (registers : Registers length) (slot : Nat) (position : Fin (length + 1)) :
    write registers slot position slot = some position := by simp [write]

theorem write_other (registers : Registers length) (slot other : Nat)
    (position : Fin (length + 1)) (different : other ≠ slot) :
    write registers slot position other = registers other := by simp [write, different]

theorem write_overwrites (registers : Registers length) (slot : Nat)
    (earlier later : Fin (length + 1)) :
    write (write registers slot earlier) slot later = write registers slot later := by
  funext other
  by_cases same : other = slot <;> simp [write, same]

def Thread.at (thread : Thread State length) (state : State) : Thread State length :=
  { thread with point := (state, thread.point.2) }

def Thread.branch (thread : Thread State length) (state : State) (bit : Bool) : Thread State length :=
  { thread.at state with choices := thread.choices ++ [bit] }

def Thread.saved (thread : Thread State length) (state : State) (slot : Nat) : Thread State length :=
  { thread.at state with registers := write thread.registers slot thread.point.2 }

def edges (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (thread : Thread State length) : List (Thread State length) :=
  match graph thread.point.1 with
  | .accept _ | .dead => []
  | .jump next => [thread.at next]
  | .choice first second => [thread.branch first false, thread.branch second true]
  | .save slot next => [thread.saved next slot]
  | .consume class_ next =>
      if probe.contains class_ thread.point.2 then
        match successor thread.point.2 with
        | some after => [{ thread with point := (next, after) }]
        | none => []
      else []
  | .assertion assertion_ next =>
      if probe.holds assertion_ thread.point.2 then [thread.at next] else []

def eraseNode : Node State Class Assertion Tag → OrderedGraphSearch.Node State Class Assertion Tag
  | .accept tag => .accept tag
  | .dead => .dead
  | .jump next => .jump next
  | .choice first second => .choice first second
  | .consume class_ next => .consume class_ next
  | .assertion assertion_ next => .assertion assertion_ next
  | .save _ next => .jump next

/-- This is an equation between independent tagged and untagged transitions.
Assertions are retained; a failed assertion cannot become a jump. -/
theorem edges_erase (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (thread : Thread State length) :
    (edges graph probe thread).map Thread.point =
      OrderedGraphSearch.expand (fun state => eraseNode (graph state)) probe thread.point := by
  cases node : graph thread.point.1 with
  | accept tag => simp [edges, node, eraseNode, OrderedGraphSearch.expand]
  | dead => simp [edges, node, eraseNode, OrderedGraphSearch.expand]
  | jump next => simp [edges, node, eraseNode, OrderedGraphSearch.expand, Thread.at]
  | choice first second => simp [edges, node, eraseNode, OrderedGraphSearch.expand, Thread.branch, Thread.at]
  | save slot next => simp [edges, node, eraseNode, OrderedGraphSearch.expand, Thread.saved, Thread.at]
  | consume class_ next =>
      simp only [edges, node, OrderedGraphSearch.expand, eraseNode]
      split
      · cases successor thread.point.2 <;> rfl
      · rfl
  | assertion assertion_ next =>
      simp only [edges, node, OrderedGraphSearch.expand, eraseNode]
      split <;> rfl

def Derives (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (first last : Thread State length) : Prop :=
  Relation.ReflTransGen (fun source target => target ∈ edges graph probe source) first last

theorem derives_erase (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) {first last : Thread State length}
    (derived : Derives graph probe first last) :
    OrderedGraphSearch.reachable (fun state => eraseNode (graph state)) probe first.point last.point := by
  induction derived with
  | refl => exact .refl
  | @tail middle last path edge ih =>
      apply ih.tail
      rw [← edges_erase graph probe middle]
      exact List.mem_map.mpr ⟨last, edge, rfl⟩

/-- Every untagged derivation lifts from any supplied initial register state.
The lifted captures are computed by actual saves along that derivation. -/
theorem reachable_lifts (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) (point : Point State length)
    (path : OrderedGraphSearch.reachable (fun state => eraseNode (graph state)) probe first.point point) :
    ∃ last : Thread State length, last.point = point ∧ Derives graph probe first last := by
  induction path with
  | refl => exact ⟨first, rfl, .refl⟩
  | @tail middle last path edge ih =>
      obtain ⟨thread, same, derived⟩ := ih
      rw [← same, ← edges_erase graph probe thread] at edge
      obtain ⟨next, member, equal⟩ := List.mem_map.mp edge
      exact ⟨next, equal, derived.tail member⟩

theorem raw_recognition_erasure_iff (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (first : Thread State length) (point : Point State length) :
    OrderedGraphSearch.reachable (fun state => eraseNode (graph state)) probe first.point point ↔
      ∃ last : Thread State length, last.point = point ∧ Derives graph probe first last := by
  constructor
  · exact reachable_lifts graph probe first point
  · rintro ⟨last, same, derived⟩
    simpa [same] using derives_erase graph probe derived

/-- A finite scheduler, independent of regex syntax. A key is visited once;
children are scheduled before pending alternatives, and emitted occurrences
remain in scheduling order. Fuel exhaustion is not an empty frontier. -/
def firstVisits {α : Type u} {Key : Type v} [DecidableEq Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool) :
    Nat → List α → Finset Key → Option (List α)
  | 0, _, _ => none
  | _ + 1, [], _ => some []
  | fuel + 1, current :: rest, seen =>
      if key current ∈ seen then firstVisits key children emit fuel rest seen
      else (firstVisits key children emit fuel (children current ++ rest) (insert (key current) seen)).map
        (fun later => if emit current then current :: later else later)

/-- A concrete change of data representation commutes with first-visit
scheduling when keys, emitted sites and outgoing children are preserved. -/
theorem firstVisits_map {α : Type u} {β : Type w} {Key : Type v} [DecidableEq Key]
    (f : α → β) (sourceKey : α → Key) (targetKey : β → Key)
    (sourceChildren : α → List α) (targetChildren : β → List β)
    (sourceEmit : α → Bool) (targetEmit : β → Bool)
    (keys : ∀ value, targetKey (f value) = sourceKey value)
    (children : ∀ value, (sourceChildren value).map f = targetChildren (f value))
    (emits : ∀ value, targetEmit (f value) = sourceEmit value) (fuel : Nat) :
    ∀ pending seen,
      firstVisits targetKey targetChildren targetEmit fuel (pending.map f) seen =
        (firstVisits sourceKey sourceChildren sourceEmit fuel pending seen).map (List.map f) := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro pending seen
      cases pending with
      | nil => rfl
      | cons current rest =>
          simp only [List.map_cons, firstVisits, keys]
          by_cases visited : sourceKey current ∈ seen
          · simp only [visited, ↓reduceIte]
            exact ih rest seen
          · simp only [visited, ↓reduceIte]
            rw [← children, ← List.map_append, ih]
            cases firstVisits sourceKey sourceChildren sourceEmit fuel
                (sourceChildren current ++ rest) (insert (sourceKey current) seen) with
            | none => rfl
            | some later =>
                simp only [Option.map_some, emits]
                cases sourceEmit current <;> rfl

theorem firstVisits_sound {α : Type u} {Key : Type v} [DecidableEq Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool) (valid : α → Prop)
    (closed : ∀ source, valid source → ∀ target ∈ children source, valid target) (fuel : Nat) :
    ∀ pending seen result,
      (∀ value ∈ pending, valid value) →
      firstVisits key children emit fuel pending seen = some result →
      ∀ value ∈ result, valid value ∧ emit value = true := by
  induction fuel with
  | zero => simp [firstVisits]
  | succ fuel ih =>
      intro pending seen result initial finished value member
      cases pending with
      | nil => simp [firstVisits] at finished; subst result; simp at member
      | cons current rest =>
          have currentValid := initial current (by simp)
          have restValid : ∀ value ∈ rest, valid value := fun value member => initial value (by simp [member])
          by_cases visited : key current ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            exact ih rest seen result restValid finished value member
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            cases advanced : firstVisits key children emit fuel (children current ++ rest)
                (insert (key current) seen) with
            | none => simp [advanced] at finished
            | some later =>
                have nextValid : ∀ value ∈ children current ++ rest, valid value := by
                  intro value member
                  rcases List.mem_append.mp member with edge | earlier
                  · exact closed current currentValid value edge
                  · exact restValid value earlier
                have laterValid := ih (children current ++ rest) (insert (key current) seen)
                  later nextValid advanced
                simp only [advanced, Option.map_some, Option.some.injEq] at finished
                subst result
                by_cases emitted : emit current = true
                · simp only [emitted, ↓reduceIte, List.mem_cons] at member
                  rcases member with same | member
                  · subst value; exact ⟨currentValid, emitted⟩
                  · exact laterValid value member
                · have notEmitted : emit current = false := Bool.eq_false_iff.mpr emitted
                  simp only [notEmitted, Bool.false_eq_true, ↓reduceIte] at member
                  exact laterValid value member

def closureRank {α : Type u} {Key : Type v} [Fintype Key]
    (pending : List α) (seen : Finset Key) : Nat :=
  2 * (Fintype.card Key - seen.card) + pending.length

/-- Emitted keys are new relative to the initial visited set. This records
actual suppression, not just reachability of the surviving threads. -/
theorem firstVisits_fresh {α : Type u} {Key : Type v} [DecidableEq Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool) (fuel : Nat) :
    ∀ pending seen result, firstVisits key children emit fuel pending seen = some result →
      ∀ value ∈ result, key value ∉ seen := by
  induction fuel with
  | zero => simp [firstVisits]
  | succ fuel ih =>
      intro pending seen result finished value member
      cases pending with
      | nil => simp [firstVisits] at finished; subst result; simp at member
      | cons current rest =>
          by_cases visited : key current ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            exact ih rest seen result finished value member
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            cases advanced : firstVisits key children emit fuel (children current ++ rest)
                (insert (key current) seen) with
            | none => simp [advanced] at finished
            | some later =>
                simp only [advanced, Option.map_some, Option.some.injEq] at finished
                subst result
                have fresh := ih _ _ _ advanced
                cases emitted : emit current with
                | false =>
                    simp only [emitted, Bool.false_eq_true, ↓reduceIte] at member
                    exact fun old => fresh value member (Finset.mem_insert_of_mem old)
                | true =>
                    simp only [emitted, ↓reduceIte, List.mem_cons] at member
                    rcases member with same | member
                    · subst value; exact visited
                    · exact fun old => fresh value member (Finset.mem_insert_of_mem old)

/-- A completed first-visit frontier contains at most one occurrence of each
control key, even when different incoming threads carry different captures. -/
theorem firstVisits_keys_nodup {α : Type u} {Key : Type v} [DecidableEq Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool) (fuel : Nat) :
    ∀ pending seen result, firstVisits key children emit fuel pending seen = some result →
      (result.map key).Nodup := by
  induction fuel with
  | zero => simp [firstVisits]
  | succ fuel ih =>
      intro pending seen result finished
      cases pending with
      | nil => simp [firstVisits] at finished; subst result; simp
      | cons current rest =>
          by_cases visited : key current ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            exact ih rest seen result finished
          · simp only [firstVisits, visited, ↓reduceIte] at finished
            cases advanced : firstVisits key children emit fuel (children current ++ rest)
                (insert (key current) seen) with
            | none => simp [advanced] at finished
            | some later =>
                simp only [advanced, Option.map_some, Option.some.injEq] at finished
                subst result
                have unique := ih _ _ _ advanced
                cases emitted : emit current with
                | false => simpa [emitted] using unique
                | true =>
                    simp only [↓reduceIte, List.map_cons, List.nodup_cons]
                    refine ⟨?_, unique⟩
                    intro member
                    obtain ⟨value, member, same⟩ := List.mem_map.mp member
                    exact firstVisits_fresh key children emit fuel _ _ _ advanced value member
                      (by simp [same])

theorem firstVisits_length_bound {α : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool)
    (fuel : Nat) (pending : List α) (seen : Finset Key) (result : List α)
    (finished : firstVisits key children emit fuel pending seen = some result) :
    result.length ≤ Fintype.card Key := by
  have unique := firstVisits_keys_nodup key children emit fuel pending seen result finished
  have bound := Finset.card_le_univ ((result.map key).toFinset)
  simpa [List.toFinset_card_of_nodup unique] using bound

/-- Binary branching and a finite program supply a sufficient closure work
bound. Capture values need not have a finite type to establish termination. -/
theorem firstVisits_sufficient {α : Type u} {Key : Type v} [DecidableEq Key] [Fintype Key]
    (key : α → Key) (children : α → List α) (emit : α → Bool)
    (binary : ∀ value, (children value).length ≤ 2) (fuel : Nat) :
    ∀ pending seen, closureRank pending seen < fuel →
      firstVisits key children emit fuel pending seen ≠ none := by
  induction fuel with
  | zero => intro pending seen enough; omega
  | succ fuel ih =>
      intro pending seen enough
      cases pending with
      | nil => simp [firstVisits]
      | cons current rest =>
          by_cases visited : key current ∈ seen
          · simp only [firstVisits, visited, ↓reduceIte]
            apply ih rest seen
            simp only [closureRank, List.length_cons] at enough ⊢
            omega
          · simp only [firstVisits, visited, ↓reduceIte]
            have size := binary current
            have card := Finset.card_le_univ (insert (key current) seen)
            rw [Finset.card_insert_of_notMem visited] at card
            have smaller : closureRank (children current ++ rest) (insert (key current) seen) < fuel := by
              simp only [closureRank, List.length_cons] at enough
              simp only [closureRank, List.length_append, Finset.card_insert_of_notMem visited]
              omega
            cases result : firstVisits key children emit fuel
                (children current ++ rest) (insert (key current) seen) with
            | none => exact False.elim (ih _ _ smaller result)
            | some later => simp

def epsilonChildren (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (thread : Thread State length) : List (Thread State length) :=
  match graph thread.point.1 with
  | .accept _ | .consume _ _ => []
  | _ => edges graph probe thread

def isFrontier : Node State Class Assertion Tag → Bool
  | .accept _ | .consume _ _ => true
  | _ => false

def close [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (fuel : Nat) (pending : List (Thread State length)) :
    Option (List (Thread State length)) :=
  firstVisits (fun thread => thread.point.1) (epsilonChildren graph probe)
    (fun thread => isFrontier (graph thread.point.1)) fuel pending ∅

theorem edges_length (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (thread : Thread State length) :
    (edges graph probe thread).length ≤ 2 := by
  cases node : graph thread.point.1 with
  | consume class_ next =>
      simp only [edges, node]
      split
      · cases successor thread.point.2 <;> simp
      · simp
  | assertion assertion_ next => simp only [edges, node]; split <;> simp
  | _ => simp [edges, node]

theorem close_work_bound [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (pending : List (Thread State length)) :
    close graph probe (2 * Fintype.card State + pending.length + 1) pending ≠ none := by
  apply firstVisits_sufficient
  · intro thread
    cases node : graph thread.point.1 <;>
      simp only [epsilonChildren, node, List.length_nil, Nat.zero_le] <;>
      exact edges_length graph probe thread
  · simp [closureRank]

def untaggedEpsilonChildren (graph : State → OrderedGraphSearch.Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (point : Point State length) : List (Point State length) :=
  match graph point.1 with
  | .accept _ | .consume _ _ => []
  | _ => OrderedGraphSearch.expand graph probe point

def untaggedIsFrontier : OrderedGraphSearch.Node State Class Assertion Tag → Bool
  | .accept _ | .consume _ _ => true
  | _ => false

theorem epsilonChildren_erase (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (thread : Thread State length) :
    (epsilonChildren graph probe thread).map Thread.point =
      untaggedEpsilonChildren (fun state => eraseNode (graph state)) probe thread.point := by
  cases node : graph thread.point.1 <;>
    simp only [epsilonChildren, node, untaggedEpsilonChildren, eraseNode, List.map_nil] <;>
    exact edges_erase graph probe thread

/-- Capture writes and choice histories cannot alter the ordered control
frontier of a capture-independent graph, including nullable-cycle suppression. -/
theorem close_erase [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (fuel : Nat) (pending : List (Thread State length)) :
    firstVisits Prod.fst
        (untaggedEpsilonChildren (fun state => eraseNode (graph state)) probe)
        (fun point => untaggedIsFrontier (eraseNode (graph point.1))) fuel
        (pending.map Thread.point) ∅ =
      (close graph probe fuel pending).map (List.map Thread.point) := by
  apply firstVisits_map
  · intro thread; rfl
  · exact epsilonChildren_erase graph probe
  · intro thread; cases graph thread.point.1 <;> rfl

theorem close_derives [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (fuel : Nat) (first : Thread State length)
    (result : List (Thread State length)) (finished : close graph probe fuel [first] = some result) :
    ∀ last ∈ result, Derives graph probe first last ∧ isFrontier (graph last.point.1) = true := by
  unfold close at finished
  apply firstVisits_sound (fun thread : Thread State length => thread.point.1) (epsilonChildren graph probe)
    (fun thread => isFrontier (graph thread.point.1)) (Derives graph probe first) ?_ fuel
    [first] ∅ result ?_ finished
  · intro source reached target edge
    have member : target ∈ edges graph probe source := by
      cases node : graph source.point.1 <;> simp_all [epsilonChildren]
    exact reached.tail member
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact .refl

theorem epsilonChildren_same_position (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (source target : Thread State length)
    (edge : target ∈ epsilonChildren graph probe source) :
    target.point.2 = source.point.2 := by
  cases node : graph source.point.1 with
  | accept tag => simp [epsilonChildren, node] at edge
  | consume class_ next => simp [epsilonChildren, node] at edge
  | dead => simp [epsilonChildren, edges, node] at edge
  | jump next =>
      simp only [epsilonChildren, node, edges, List.mem_singleton] at edge
      subst target; rfl
  | save slot next =>
      simp only [epsilonChildren, node, edges, List.mem_singleton] at edge
      subst target; rfl
  | choice first second =>
      simp only [epsilonChildren, node, edges, List.mem_cons, List.not_mem_nil, or_false] at edge
      rcases edge with same | same <;> subst target <;> rfl
  | assertion assertion_ next =>
      simp only [epsilonChildren, node, edges] at edge
      split at edge
      · simp only [List.mem_singleton] at edge
        subst target; rfl
      · simp at edge

/-- Every closure invocation remains at its single input position, so its
visited-program-counter key does not conflate different input positions. -/
theorem close_same_position [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (fuel : Nat) (position : Fin (length + 1))
    (pending result : List (Thread State length))
    (synchronous : ∀ thread ∈ pending, thread.point.2 = position)
    (finished : close graph probe fuel pending = some result) :
    ∀ thread ∈ result, thread.point.2 = position := by
  unfold close at finished
  have sound := firstVisits_sound (fun thread : Thread State length => thread.point.1)
    (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
    (fun thread => thread.point.2 = position)
    (fun source valid target edge => (epsilonChildren_same_position graph probe source target edge).trans valid)
    fuel pending ∅ result synchronous finished
  exact fun thread member => (sound thread member).1

theorem consume_advances (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (source target : Thread State length)
    (class_ : Class) (next : State) (node : graph source.point.1 = .consume class_ next)
    (edge : target ∈ edges graph probe source) :
    target.point.2.val = source.point.2.val + 1 := by
  simp only [edges, node] at edge
  split at edge
  · cases advanced : successor source.point.2 with
    | none => simp [advanced] at edge
    | some after =>
        simp only [advanced, List.mem_singleton] at edge
        subst target
        exact (OrderedGraphSearch.successor_advances advanced).1
  · simp at edge

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {n : Nat} (state : Fin n) (length : Nat) : Thread (Fin n) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def savedAlternative : Fin 5 → Node (Fin 5) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 3
    | 1 => .save 0 2
    | 2 => .dead
    | 3 => .save 1 4
    | _ => .accept ()

/-- The capture in the failed preferred branch does not leak into its sibling. -/
theorem failed_branch_rollback :
    let result := close savedAlternative (probe 0) 20 [initial 0 0]
    (result.map (fun threads => threads.map (fun thread => thread.registers 0))) = some [none] ∧
    (result.map (fun threads => threads.map (fun thread => thread.registers 1))) = some [some 0] := by
  decide

private def collision : Fin 4 → Node (Fin 4) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 2
    | 1 => .save 0 3
    | 2 => .save 1 3
    | _ => .accept ()

/-- At a shared program counter the first arrival wins, with its own registers. -/
theorem first_visit_retains_preferred_captures :
    let result := close collision (probe 0) 20 [initial 0 0]
    (result.map (fun threads => threads.map (fun thread => thread.registers 0))) = some [some 0] ∧
    (result.map (fun threads => threads.map (fun thread => thread.registers 1))) = some [none] := by
  decide

private def nullable : Fin 3 → Node (Fin 3) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 2
    | 1 => .save 0 0
    | _ => .accept ()

/-- A save on a suppressed nullable cycle is not copied into the exit branch. -/
theorem nullable_cycle_snapshot :
    let result := close nullable (probe 0) 12 [initial 0 0]
    (result.map (fun threads => threads.map (fun thread => thread.registers 0))) = some [none] := by
  decide

theorem exhausted_is_not_empty_frontier :
    (close collision (probe 0) 0 [initial 0 0]).isSome = false ∧
    (close (fun _ : Fin 1 => (Node.dead : Node (Fin 1) Unit Unit Unit))
      (probe 0) 4 [initial 0 0]).map List.length = some 0 := by decide

end Controls

#print axioms write_overwrites
#print axioms edges_erase
#print axioms raw_recognition_erasure_iff
#print axioms firstVisits_map
#print axioms firstVisits_sound
#print axioms firstVisits_sufficient
#print axioms close_work_bound
#print axioms close_erase
#print axioms close_derives
#print axioms epsilonChildren_same_position
#print axioms close_same_position
#print axioms consume_advances

end Mettapedia.Computability.RegularLanguages.RegexTaggedGraph

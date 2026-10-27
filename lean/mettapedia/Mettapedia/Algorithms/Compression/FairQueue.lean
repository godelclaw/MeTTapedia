import Mettapedia.GSLT.Core.BranchingTemporal

/-!
# Cost priority with an age service every eighth turn

An occurrence receives a fresh ticket each time it is enqueued. The pending
list retains ticket order. Seven turns select the least cost, keeping the first
occurrence on ties; the eighth selects the oldest occurrence. Successors append
after pending work. Equal payloads remain distinct occurrences.

The branching system supplies a finite successor list for each completed
cooperative slice. An infinite producer can return a continuation of itself;
the scheduler does not require its entire inverse relation to terminate.
-/

namespace Mettapedia.Algorithms.Compression.FairQueue

open Mettapedia.GSLT.Core.BranchingTemporal

universe u
variable {Node : Type u}

structure Entry (Node : Type u) where
  ticket : Nat
  value : Node
  deriving Repr

structure Queue (Node : Type u) where
  pending : List (Entry Node)
  nextTicket : Nat
  phase : Fin 8

def Valid (queue : Queue Node) : Prop :=
  queue.pending.Pairwise (fun left right => left.ticket < right.ticket) ∧
    ∀ entry ∈ queue.pending, entry.ticket < queue.nextTicket

def numbered (start : Nat) : List Node → List (Entry Node)
  | [] => []
  | node :: rest => ⟨start, node⟩ :: numbered (start + 1) rest

def initial (nodes : List Node) : Queue Node := ⟨numbered 0 nodes, nodes.length, 0⟩

def minimum (cost : Node → Nat) (head : Entry Node) : List (Entry Node) →
    Entry Node × List (Entry Node)
  | [] => (head, [])
  | next :: rest =>
      let choice := minimum cost next rest
      if cost head.value ≤ cost choice.1.value then (head, next :: rest)
      else (choice.1, head :: choice.2)

def pop (cost : Node → Nat) (queue : Queue Node) : Option (Entry Node × List (Entry Node)) :=
  match queue.pending with
  | [] => none
  | head :: rest => some (if queue.phase.val = 7 then (head, rest) else minimum cost head rest)

def after (successors : Node → List Node) (queue : Queue Node)
    (selected : Entry Node) (remaining : List (Entry Node)) : Queue Node :=
  { pending := remaining ++ numbered queue.nextTicket (successors selected.value)
    nextTicket := queue.nextTicket + (successors selected.value).length
    phase := ⟨(queue.phase.val + 1) % 8, Nat.mod_lt _ (by decide)⟩ }

def tick (cost : Node → Nat) (successors : Node → List Node) (queue : Queue Node) :
    Option (Entry Node × Queue Node) :=
  (pop cost queue).map fun (selected, remaining) =>
    (selected, after successors queue selected remaining)

def run (cost : Node → Nat) (successors : Node → List Node) :
    Nat → Queue Node → List (Entry Node) × Queue Node
  | 0, queue => ([], queue)
  | fuel + 1, queue =>
      match tick cost successors queue with
      | none => ([], queue)
      | some (selected, next) =>
          let rest := run cost successors fuel next
          (selected :: rest.1, rest.2)

theorem minimum_sublist (cost : Node → Nat) (head : Entry Node) (rest : List (Entry Node)) :
    (minimum cost head rest).2.Sublist (head :: rest) := by
  induction rest generalizing head with
  | nil => simp [minimum]
  | cons next rest ih =>
      simp only [minimum]
      split
      · exact List.Sublist.cons _ (.refl _)
      · exact List.Sublist.cons_cons _ (ih next)

theorem minimum_perm (cost : Node → Nat) (head : Entry Node) (rest : List (Entry Node)) :
    ((minimum cost head rest).1 :: (minimum cost head rest).2).Perm (head :: rest) := by
  induction rest generalizing head with
  | nil => exact .refl _
  | cons next rest ih =>
      simp only [minimum]
      split
      · exact .refl _
      · exact (List.Perm.swap _ _ _).trans (.cons _ (ih next))

theorem minimum_cost (cost : Node → Nat) (head : Entry Node) (rest : List (Entry Node)) :
    ∀ entry ∈ head :: rest, cost (minimum cost head rest).1.value ≤ cost entry.value := by
  induction rest generalizing head with
  | nil => simp [minimum]
  | cons next rest ih =>
      simp only [minimum]
      split
      · rename_i smaller
        intro entry member
        rcases List.mem_cons.mp member with rfl | later
        · exact Nat.le_refl _
        · exact smaller.trans (ih next entry later)
      · rename_i smaller
        intro entry member
        rcases List.mem_cons.mp member with rfl | later
        · exact Nat.le_of_lt (Nat.lt_of_not_ge smaller)
        · exact ih next entry later

theorem numbered_bounds (start : Nat) (nodes : List Node) :
    ∀ entry ∈ numbered start nodes, start ≤ entry.ticket ∧ entry.ticket < start + nodes.length := by
  induction nodes generalizing start with
  | nil => simp [numbered]
  | cons node rest ih =>
      intro entry member
      simp only [numbered, List.mem_cons] at member
      rcases member with rfl | later
      · simp
      · have bounds := ih (start + 1) entry later
        simp only [List.length_cons]
        omega

theorem numbered_ordered (start : Nat) (nodes : List Node) :
    (numbered start nodes).Pairwise (fun left right => left.ticket < right.ticket) := by
  induction nodes generalizing start with
  | nil => simp [numbered]
  | cons node rest ih =>
      rw [numbered, List.pairwise_cons]
      exact ⟨fun entry member => by
        have bounds := numbered_bounds (start + 1) rest entry member
        simp only
        omega, ih _⟩

theorem initial_valid (nodes : List Node) : Valid (initial nodes) := by
  exact ⟨numbered_ordered 0 nodes, fun entry member => by
    simpa [initial] using (numbered_bounds 0 nodes entry member).2⟩

theorem pop_sublist (cost : Node → Nat) (queue : Queue Node)
    {selected : Entry Node} {remaining : List (Entry Node)}
    (found : pop cost queue = some (selected, remaining)) : remaining.Sublist queue.pending := by
  cases pending : queue.pending with
  | nil => simp [pop, pending] at found
  | cons head rest =>
      simp only [pop, pending, Option.some.injEq] at found
      split at found
      · cases found
        exact List.Sublist.cons _ (.refl _)
      · have equal : (minimum cost head rest).2 = remaining := congrArg Prod.snd found
        rw [← equal]
        exact minimum_sublist cost head rest

theorem pop_perm (cost : Node → Nat) (queue : Queue Node)
    {selected : Entry Node} {remaining : List (Entry Node)}
    (found : pop cost queue = some (selected, remaining)) :
    (selected :: remaining).Perm queue.pending := by
  cases pending : queue.pending with
  | nil => simp [pop, pending] at found
  | cons head rest =>
      simp only [pop, pending, Option.some.injEq] at found
      split at found
      · cases found
        exact .refl _
      · have equalHead : (minimum cost head rest).1 = selected := congrArg Prod.fst found
        have equalRest : (minimum cost head rest).2 = remaining := congrArg Prod.snd found
        rw [← equalHead, ← equalRest]
        exact minimum_perm cost head rest

theorem after_valid (cost : Node → Nat) (successors : Node → List Node) (queue : Queue Node)
    {selected : Entry Node} {remaining : List (Entry Node)}
    (valid : Valid queue) (found : pop cost queue = some (selected, remaining)) :
    Valid (after successors queue selected remaining) := by
  have sub := pop_sublist cost queue found
  constructor
  · change (remaining ++ numbered queue.nextTicket (successors selected.value)).Pairwise _
    rw [List.pairwise_append]
    refine ⟨valid.1.sublist sub, numbered_ordered _ _, ?_⟩
    intro old oldMember fresh freshMember
    have older := valid.2 old (sub.subset oldMember)
    have newer := (numbered_bounds queue.nextTicket (successors selected.value) fresh freshMember).1
    omega
  · intro entry member
    simp only [after, List.mem_append] at member
    rcases member with old | fresh
    · have bounded := valid.2 entry (sub.subset old)
      simp only [after]
      omega
    · exact (numbered_bounds _ _ entry fresh).2

def HasTicket (ticket : Nat) (queue : Queue Node) : Prop :=
  ∃ entry ∈ queue.pending, entry.ticket = ticket

def olderCount (ticket : Nat) (entries : List (Entry Node)) : Nat :=
  (entries.filter (fun entry => decide (entry.ticket < ticket))).length

/-- At most this many slices are needed to service a currently live ticket. -/
def waitBound (ticket : Nat) (queue : Queue Node) : Nat :=
  8 * olderCount ticket queue.pending + (8 - queue.phase.val)

theorem waitBound_positive (ticket : Nat) (queue : Queue Node) : 0 < waitBound ticket queue := by
  have phase := queue.phase.isLt
  unfold waitBound
  omega

theorem olderCount_sublist (ticket : Nat) {small large : List (Entry Node)}
    (sub : small.Sublist large) : olderCount ticket small ≤ olderCount ticket large :=
  (sub.filter _).length_le

theorem numbered_no_older (start ticket : Nat) (nodes : List Node) (bounded : ticket < start) :
    (numbered start nodes).filter (fun entry => decide (entry.ticket < ticket)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry member
  have newer := (numbered_bounds start nodes entry member).1
  have notBefore : ¬ entry.ticket < ticket := by omega
  simpa using notBefore

theorem after_olderCount (successors : Node → List Node) (queue : Queue Node)
    (selected : Entry Node) (remaining : List (Entry Node)) (ticket : Nat)
    (bounded : ticket < queue.nextTicket) :
    olderCount ticket (after successors queue selected remaining).pending = olderCount ticket remaining := by
  simp [olderCount, after, List.filter_append, numbered_no_older _ _ _ bounded]

theorem ticket_bound (queue : Queue Node) (ticket : Nat) (valid : Valid queue)
    (present : HasTicket ticket queue) : ticket < queue.nextTicket := by
  obtain ⟨entry, member, same⟩ := present
  simpa [same] using valid.2 entry member

theorem ticket_retained (cost : Node → Nat) (successors : Node → List Node) (queue : Queue Node)
    {selected : Entry Node} {remaining : List (Entry Node)} (ticket : Nat)
    (present : HasTicket ticket queue) (found : pop cost queue = some (selected, remaining))
    (different : selected.ticket ≠ ticket) :
    HasTicket ticket (after successors queue selected remaining) := by
  obtain ⟨entry, member, same⟩ := present
  have moved := (pop_perm cost queue found).mem_iff.mpr member
  rcases List.mem_cons.mp moved with equal | later
  · subst entry
    exact False.elim (different same)
  · exact ⟨entry, List.mem_append_left _ later, same⟩

theorem age_removes_older (cost : Node → Nat) (queue : Queue Node)
    {selected : Entry Node} {remaining : List (Entry Node)} (ticket : Nat)
    (valid : Valid queue) (present : HasTicket ticket queue)
    (found : pop cost queue = some (selected, remaining))
    (age : queue.phase.val = 7) (different : selected.ticket ≠ ticket) :
    olderCount ticket remaining < olderCount ticket queue.pending := by
  cases pending : queue.pending with
  | nil => simp [HasTicket, pending] at present
  | cons head rest =>
      have equal : (head, rest) = (selected, remaining) := by
        simpa [pop, pending, age] using found
      cases equal
      obtain ⟨entry, member, same⟩ := present
      rw [pending] at member
      rcases List.mem_cons.mp member with equal | later
      · subst entry
        exact False.elim (different same)
      · have older := (List.pairwise_cons.mp (pending ▸ valid.1)).1 entry later
        have before : selected.ticket < ticket := by simpa [same] using older
        simp [olderCount, before]

/-- Every unserved slice decreases a natural-valued deadline, even when
new, cheaper work arrives on every turn. Fresh work cannot get ahead in age. -/
theorem deadline_decreases (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) {selected : Entry Node} {remaining : List (Entry Node)} (ticket : Nat)
    (valid : Valid queue) (present : HasTicket ticket queue)
    (found : pop cost queue = some (selected, remaining))
    (different : selected.ticket ≠ ticket) :
    waitBound ticket (after successors queue selected remaining) < waitBound ticket queue := by
  have bounded := ticket_bound queue ticket valid present
  have nonincrease := olderCount_sublist ticket (pop_sublist cost queue found)
  have phase := queue.phase.isLt
  unfold waitBound
  rw [after_olderCount successors queue selected remaining ticket bounded]
  simp only [after]
  by_cases age : queue.phase.val = 7
  · have older := age_removes_older cost queue ticket valid present found age different
    omega
  · omega

theorem serviced_within (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) (ticket : Nat) (valid : Valid queue) (present : HasTicket ticket queue) :
    ∃ fuel ≤ waitBound ticket queue,
      ticket ∈ ((run cost successors fuel queue).1.map Entry.ticket) := by
  have bounded : ∀ bound, ∀ q : Queue Node, waitBound ticket q = bound →
      Valid q → HasTicket ticket q → ∃ fuel ≤ bound,
        ticket ∈ ((run cost successors fuel q).1.map Entry.ticket) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro q equal valid present
        obtain ⟨selected, remaining, popped⟩ :
            ∃ selected remaining, pop cost q = some (selected, remaining) := by
          cases pending : q.pending with
          | nil => simp [HasTicket, pending] at present
          | cons head rest =>
              by_cases age : q.phase.val = 7
              · exact ⟨head, rest, by simp [pop, pending, age]⟩
              · cases choice : minimum cost head rest with
                | mk selected remaining =>
                    exact ⟨selected, remaining, by simp [pop, pending, age, choice]⟩
        have advanced : tick cost successors q =
            some (selected, after successors q selected remaining) := by simp [tick, popped]
        by_cases same : selected.ticket = ticket
        · refine ⟨1, ?_, ?_⟩
          · have positive := waitBound_positive ticket q
            omega
          · simp [run, advanced, same]
        · have smaller := deadline_decreases cost successors q ticket valid present popped same
          have validNext := after_valid cost successors q valid popped
          have liveNext := ticket_retained cost successors q ticket present popped same
          obtain ⟨fuel, allowance, served⟩ := ih _ (by omega) _ rfl validNext liveNext
          exact ⟨fuel + 1, by omega, by simp [run, advanced, served]⟩
  exact bounded _ queue rfl valid present

theorem run_empty (cost : Node → Nat) (successors : Node → List Node)
    (queue : Queue Node) (empty : queue.pending = []) (fuel : Nat) :
    run cost successors fuel queue = ([], queue) := by
  cases fuel <;> simp [run, tick, pop, empty]

/-- Slicing and resuming keeps exactly the same service trace and residual
queue as one uninterrupted request with the combined allowance. -/
theorem run_add (cost : Node → Nat) (successors : Node → List Node)
    (first second : Nat) (queue : Queue Node) :
    run cost successors (first + second) queue =
      let left := run cost successors first queue
      let right := run cost successors second left.2
      (left.1 ++ right.1, right.2) := by
  induction first generalizing queue with
  | zero => simp [run]
  | succ first ih =>
      cases stepped : tick cost successors queue with
      | none =>
          have empty : queue.pending = [] := by
            cases pending : queue.pending with
            | nil => rfl
            | cons head tail => simp [tick, pop, pending] at stepped
          simp [run_empty cost successors queue empty]
      | some next =>
          rcases next with ⟨selected, later⟩
          simp only [Nat.succ_add, run, stepped]
          rw [ih later]
          simp

namespace Controls

def zeroCostLoop : Nat → List Nat
  | 0 => [0]
  | _ => []

example : ((run id zeroCostLoop 7 (initial [0, 1])).1.map Entry.value) =
    [0, 0, 0, 0, 0, 0, 0] := by decide

example : ((run id zeroCostLoop 8 (initial [0, 1])).1.map Entry.value) =
    [0, 0, 0, 0, 0, 0, 0, 1] := by decide

example : ((run (fun _ : Nat => 0) (fun _ => []) 2 (initial [3, 3])).1.map Entry.ticket) =
    [0, 1] := by decide

end Controls

end Mettapedia.Algorithms.Compression.FairQueue

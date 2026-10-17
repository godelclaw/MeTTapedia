import Mettapedia.Computability.RegularLanguages.RegexTaggedGraph

/-!
# Ordered frontier execution for capture-independent tagged graphs

At each input position, first-visit epsilon closure retains the preferred
register snapshot at each program counter. A successful terminal removes only
lower-priority frontier threads; higher-priority consuming threads may replace
that candidate later. Full coverage is an eligibility condition at terminals,
not a filter on an already selected prefix.

The executable reference and its independent raw-derivation soundness theorem
are about concrete graphs. They do not prove a source lowering or native C
adequacy. Unanchored search can be supplied by a separately justified graph
prefix; this driver does not silently restart each possible input position.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.RegexPikeVM

open RegexTaggedGraph
open OrderedGraphSearch (Probe)

universe u v w z

inductive Result (α : Type u) (Tag : Type v) where
  | incomplete
  | finished (selected : Option (α × Tag))

def Result.map {α : Type u} {β : Type v} {Tag : Type w} (f : α → β) : Result α Tag → Result β Tag
  | .incomplete => .incomplete
  | .finished selected => .finished (selected.map (fun pair => (f pair.1, pair.2)))

variable {State : Type u} {Class : Type v} {Assertion : Type w} {Tag : Type z} {length : Nat}

def terminal (graph : State → Node State Class Assertion Tag) (thread : Thread State length) : Option Tag :=
  match graph thread.point.1 with
  | .accept tag => some tag
  | _ => none

/-- Keep consuming threads preceding the first eligible terminal. Ineligible
terminals do not suppress a later full-covering alternative. -/
def candidates {α : Type u} {Tag : Type v} (accepts : α → Option Tag) (eligible : α → Bool) :
    List α → List α × Option (α × Tag)
  | [] => ([], none)
  | first :: rest =>
      match accepts first with
      | some tag =>
          if eligible first then ([], some (first, tag))
          else candidates accepts eligible rest
      | none =>
          let after := candidates accepts eligible rest
          (first :: after.1, after.2)

/-- The executable frontier observer implements earliest eligible terminal
selection over the finite ordered frontier, specified independently in
`RegexMatchObservations.Selected`. It does not minimize arbitrary raw paths. -/
theorem candidates_observer {α : Type u} {Tag : Type v}
    (accepts : α → Option Tag) (eligible : α → Bool) (frontier : List α) :
    (candidates accepts eligible frontier).2 =
      (RegexMatchObservations.select (fun value => (accepts value).isSome && eligible value) frontier).bind
        (fun value => (accepts value).map (fun tag => (value, tag))) := by
  induction frontier with
  | nil => rfl
  | cons first rest ih =>
      cases accepted : accepts first with
      | none => simp [candidates, RegexMatchObservations.select, accepted, ih]
      | some tag =>
          cases allowed : eligible first <;>
            simp [candidates, RegexMatchObservations.select, accepted, allowed, ih]

theorem candidates_map {α : Type u} {β : Type v} {Tag : Type w}
    (f : α → β) (sourceAccepts : α → Option Tag) (targetAccepts : β → Option Tag)
    (sourceEligible : α → Bool) (targetEligible : β → Bool)
    (accepts : ∀ value, targetAccepts (f value) = sourceAccepts value)
    (eligible : ∀ value, targetEligible (f value) = sourceEligible value) (frontier : List α) :
    candidates targetAccepts targetEligible (frontier.map f) =
      ((candidates sourceAccepts sourceEligible frontier).1.map f,
        (candidates sourceAccepts sourceEligible frontier).2.map (fun pair => (f pair.1, pair.2))) := by
  induction frontier with
  | nil => rfl
  | cons first rest ih =>
      cases accepted : sourceAccepts first with
      | none => simp [candidates, accepts, accepted, ih]
      | some tag =>
          cases allowed : sourceEligible first <;> simp [candidates, accepts, accepted, eligible, allowed, ih]

theorem candidates_active_mem {α : Type u} {Tag : Type v}
    (accepts : α → Option Tag) (eligible : α → Bool) (frontier : List α) :
    ∀ value ∈ (candidates accepts eligible frontier).1,
      value ∈ frontier ∧ accepts value = none := by
  induction frontier with
  | nil => simp [candidates]
  | cons first rest ih =>
      intro value member
      cases accepted : accepts first with
      | some tag =>
          simp only [candidates, accepted] at member
          split at member
          · simp at member
          · have later := ih value member
            exact ⟨by simp [later.1], later.2⟩
      | none =>
          simp only [candidates, accepted, List.mem_cons] at member
          rcases member with same | member
          · subst value; exact ⟨by simp, accepted⟩
          · have later := ih value member
            exact ⟨by simp [later.1], later.2⟩

theorem candidates_selected_sound {α : Type u} {Tag : Type v}
    (accepts : α → Option Tag) (eligible : α → Bool) (frontier : List α)
    (value : α) (tag : Tag) (selected : (candidates accepts eligible frontier).2 = some (value, tag)) :
    value ∈ frontier ∧ accepts value = some tag ∧ eligible value = true := by
  induction frontier with
  | nil => simp [candidates] at selected
  | cons first rest ih =>
      cases accepted : accepts first with
      | some found =>
          simp only [candidates, accepted] at selected
          split at selected
          · simp only [Option.some.injEq, Prod.mk.injEq] at selected
            obtain ⟨rfl, rfl⟩ := selected
            exact ⟨by simp, accepted, by assumption⟩
          · have later := ih selected
            exact ⟨by simp [later.1], later.2⟩
      | none =>
          simp only [candidates, accepted] at selected
          have later := ih selected
          exact ⟨by simp [later.1], later.2⟩

/-- A reference driver with separately supplied epsilon-closure and consuming
steps. Exhaustion never returns the candidate as a completed answer. -/
def execute {α : Type u} {Key : Type v} {Tag : Type w} [DecidableEq Key]
    (key : α → Key) (epsilon : α → List α) (emit : α → Bool)
    (consume : α → List α) (accepts : α → Option Tag) (eligible : α → Bool)
    (closureFuel : Nat) : Nat → List α → Option (α × Tag) → Result α Tag
  | 0, _, _ => .incomplete
  | fuel + 1, pending, previous =>
      match firstVisits key epsilon emit closureFuel pending ∅ with
      | none => .incomplete
      | some frontier =>
          let next := candidates accepts eligible frontier
          let selected := next.2.or previous
          let advancing := next.1.flatMap consume
          if advancing.isEmpty then .finished selected
          else execute key epsilon emit consume accepts eligible closureFuel fuel advancing selected

/-- Any representation change preserving concrete control decisions commutes
with the entire ordered frontier driver, not only with returned membership. -/
theorem execute_map {α : Type u} {β : Type v} {Key : Type w} {Tag : Type z} [DecidableEq Key]
    (f : α → β) (sourceKey : α → Key) (targetKey : β → Key)
    (sourceEpsilon : α → List α) (targetEpsilon : β → List β)
    (sourceEmit : α → Bool) (targetEmit : β → Bool)
    (sourceConsume : α → List α) (targetConsume : β → List β)
    (sourceAccepts : α → Option Tag) (targetAccepts : β → Option Tag)
    (sourceEligible : α → Bool) (targetEligible : β → Bool)
    (keys : ∀ value, targetKey (f value) = sourceKey value)
    (epsilon : ∀ value, (sourceEpsilon value).map f = targetEpsilon (f value))
    (emits : ∀ value, targetEmit (f value) = sourceEmit value)
    (consumes : ∀ value, (sourceConsume value).map f = targetConsume (f value))
    (accepts : ∀ value, targetAccepts (f value) = sourceAccepts value)
    (eligible : ∀ value, targetEligible (f value) = sourceEligible value)
    (closureFuel fuel : Nat) :
    ∀ pending previous,
      execute targetKey targetEpsilon targetEmit targetConsume targetAccepts targetEligible closureFuel fuel
        (pending.map f) (previous.map (fun pair => (f pair.1, pair.2))) =
      (execute sourceKey sourceEpsilon sourceEmit sourceConsume sourceAccepts sourceEligible closureFuel fuel
        pending previous).map f := by
  have flatMap : ∀ values : List α,
      (values.map f).flatMap targetConsume = (values.flatMap sourceConsume).map f := by
    intro values
    induction values with
    | nil => rfl
    | cons first rest ih => simp [← consumes, ih]
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
      intro pending previous
      simp only [execute,
        firstVisits_map f sourceKey targetKey sourceEpsilon targetEpsilon sourceEmit targetEmit
          keys epsilon emits]
      cases closed : firstVisits sourceKey sourceEpsilon sourceEmit closureFuel pending ∅ with
      | none => rfl
      | some frontier =>
          simp only [Option.map_some, candidates_map f sourceAccepts targetAccepts
            sourceEligible targetEligible accepts eligible, flatMap, List.isEmpty_map]
          have combine :
              ((candidates sourceAccepts sourceEligible frontier).2.map (fun pair => (f pair.1, pair.2))).or
                (previous.map (fun pair => (f pair.1, pair.2))) =
              ((candidates sourceAccepts sourceEligible frontier).2.or previous).map
                (fun pair => (f pair.1, pair.2)) := by
            cases (candidates sourceAccepts sourceEligible frontier).2 <;> rfl
          rw [combine]
          split
          · rfl
          · exact ih _ _

def run [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (closureFuel inputFuel : Nat) (pending : List (Thread State length)) : Result (Thread State length) Tag :=
  execute (fun thread => thread.point.1) (epsilonChildren graph probe)
    (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
    (terminal graph) eligible closureFuel inputFuel pending none

/-- End eligibility for an anchored entry. If the graph instead includes an
unanchored-search prefix, its selected start must also be checked separately. -/
def atInputEnd (thread : Thread State length) : Bool := thread.point.2.val == length

def untaggedRun [DecidableEq State]
    (graph : State → OrderedGraphSearch.Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : OrderedGraphSearch.Point State length → Bool)
    (closureFuel inputFuel : Nat) (pending : List (OrderedGraphSearch.Point State length)) :
    Result (OrderedGraphSearch.Point State length) Tag :=
  execute Prod.fst (untaggedEpsilonChildren graph probe)
    (fun point => untaggedIsFrontier (graph point.1)) (OrderedGraphSearch.expand graph probe)
    (fun point => OrderedGraphSearch.acceptedTag (graph point.1)) eligible closureFuel inputFuel pending none

/-- Saving capture boundaries cannot change selected endpoints, priorities
implicit in frontier order, tags, or incomplete execution of this graph. -/
theorem run_erase [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : OrderedGraphSearch.Point State length → Bool)
    (closureFuel inputFuel : Nat) (pending : List (Thread State length)) :
    untaggedRun (fun state => eraseNode (graph state)) probe eligible closureFuel inputFuel
        (pending.map Thread.point) =
      (run graph probe (fun thread => eligible thread.point) closureFuel inputFuel pending).map Thread.point := by
  unfold untaggedRun run
  refine execute_map Thread.point (fun thread : Thread State length => thread.point.1) Prod.fst
    (epsilonChildren graph probe)
    (untaggedEpsilonChildren (fun state => eraseNode (graph state)) probe)
    (fun thread => isFrontier (graph thread.point.1))
    (fun point => untaggedIsFrontier (eraseNode (graph point.1)))
    (edges graph probe) (OrderedGraphSearch.expand (fun state => eraseNode (graph state)) probe)
    (terminal graph) (fun point => OrderedGraphSearch.acceptedTag (eraseNode (graph point.1)))
    (fun thread => eligible thread.point) eligible ?_ ?_ ?_ ?_ ?_ ?_
    closureFuel inputFuel pending none
  · intro value; rfl
  · exact epsilonChildren_erase graph probe
  · intro thread; cases graph thread.point.1 <;> rfl
  · exact edges_erase graph probe
  · intro thread; unfold terminal; cases graph thread.point.1 <;> rfl
  · intro thread; rfl

/-- Every completed selected result was computed by real transitions and an
eligible terminal. This is not a completeness theorem for suppressed raw paths. -/
theorem execute_sound {α : Type u} {Key : Type v} {Tag : Type w} [DecidableEq Key]
    (key : α → Key) (epsilon : α → List α) (emit : α → Bool)
    (consume : α → List α) (accepts : α → Option Tag) (eligible : α → Bool)
    (valid : α → Prop)
    (epsilonClosed : ∀ source, valid source → ∀ target ∈ epsilon source, valid target)
    (consumeClosed : ∀ source, valid source → ∀ target ∈ consume source, valid target)
    (closureFuel fuel : Nat) :
    ∀ pending previous result tag,
      (∀ value ∈ pending, valid value) →
      (∀ value tag, previous = some (value, tag) →
        valid value ∧ accepts value = some tag ∧ eligible value = true) →
      execute key epsilon emit consume accepts eligible closureFuel fuel pending previous =
        .finished (some (result, tag)) →
      valid result ∧ accepts result = some tag ∧ eligible result = true := by
  induction fuel with
  | zero => simp [execute]
  | succ fuel ih =>
      intro pending previous result tag pendingValid previousValid finished
      cases closed : firstVisits key epsilon emit closureFuel pending ∅ with
      | none => simp [execute, closed] at finished
      | some frontier =>
          have frontierValid := firstVisits_sound key epsilon emit valid epsilonClosed closureFuel
            pending ∅ frontier pendingValid closed
          have nextValid : ∀ value tag,
              (candidates accepts eligible frontier).2.or previous = some (value, tag) →
                valid value ∧ accepts value = some tag ∧ eligible value = true := by
            intro value tag selected
            cases found : (candidates accepts eligible frontier).2 with
            | none => simp only [found, Option.none_or] at selected; exact previousValid value tag selected
            | some pair =>
                simp only [found, Option.some_or, Option.some.injEq] at selected
                subst pair
                have sound := candidates_selected_sound accepts eligible frontier value tag found
                exact ⟨(frontierValid value sound.1).1, sound.2⟩
          have advancingValid : ∀ value ∈ (candidates accepts eligible frontier).1.flatMap consume,
              valid value := by
            intro value member
            obtain ⟨source, sourceMember, edge⟩ := List.mem_flatMap.mp member
            have member := (candidates_active_mem accepts eligible frontier source sourceMember).1
            exact consumeClosed source (frontierValid source member).1 value edge
          simp only [execute, closed] at finished
          split at finished
          · simp only [Result.finished.injEq] at finished
            exact nextValid result tag finished
          · exact ih _ _ _ _ advancingValid nextValid finished

theorem run_match_sound [DecidableEq State] (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (closureFuel inputFuel : Nat) (first last : Thread State length) (tag : Tag)
    (finished : run graph probe eligible closureFuel inputFuel [first] = .finished (some (last, tag))) :
    Derives graph probe first last ∧ terminal graph last = some tag ∧ eligible last = true := by
  unfold run at finished
  apply execute_sound (fun thread : Thread State length => thread.point.1) (epsilonChildren graph probe)
    (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
    (terminal graph) eligible (Derives graph probe first) ?_ ?_ closureFuel inputFuel
    [first] none last tag ?_ ?_ finished
  · intro source reached target edge
    have member : target ∈ edges graph probe source := by
      cases node : graph source.point.1 <;> simp_all [epsilonChildren]
    exact reached.tail member
  · intro source reached target edge
    exact reached.tail edge
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact .refl
  · simp

theorem candidates_active_length {α : Type u} {Tag : Type v}
    (accepts : α → Option Tag) (eligible : α → Bool) (frontier : List α) :
    (candidates accepts eligible frontier).1.length ≤ frontier.length := by
  induction frontier with
  | nil => simp [candidates]
  | cons first rest ih =>
      cases accepted : accepts first with
      | none => simpa [candidates, accepted] using Nat.succ_le_succ ih
      | some tag =>
          cases allowed : eligible first with
          | false => simpa [candidates, accepted, allowed] using Nat.le_succ_of_le ih
          | true => simp [candidates, accepted, allowed]

/-- Active frontier threads are consuming instructions. In particular their
next step cannot branch or remain at the current input position. -/
theorem active_consume_bounds (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (source : Thread State length)
    (frontier : isFrontier (graph source.point.1) = true)
    (notTerminal : terminal graph source = none) :
    (edges graph probe source).length ≤ 1 ∧
      ∀ target ∈ edges graph probe source, target.point.2.val = source.point.2.val + 1 := by
  cases node : graph source.point.1 with
  | accept tag => simp [terminal, node] at notTerminal
  | dead | jump _ | choice _ _ | assertion _ _ | save _ _ => simp [node, isFrontier] at frontier
  | consume class_ next =>
      constructor
      · simp only [edges, node]
        split
        · cases OrderedGraphSearch.successor source.point.2 <;> simp
        · simp
      · intro target edge
        exact consume_advances graph probe source target class_ next node edge

theorem active_advancing_length (graph : State → Node State Class Assertion Tag)
    (probe : Probe Class Assertion length) (eligible : Thread State length → Bool)
    (frontier : List (Thread State length))
    (valid : ∀ source ∈ frontier, isFrontier (graph source.point.1) = true) :
    ((candidates (terminal graph) eligible frontier).1.flatMap (edges graph probe)).length ≤
      frontier.length := by
  have activeBound : ∀ active : List (Thread State length),
      (∀ source ∈ active, source ∈ frontier ∧ terminal graph source = none) →
      (active.flatMap (edges graph probe)).length ≤ active.length := by
    intro active
    induction active with
    | nil => simp
    | cons first rest ih =>
        intro members
        have firstMember := members first (by simp)
        have one := (active_consume_bounds graph probe first (valid first firstMember.1) firstMember.2).1
        have later := ih (fun source member => members source (by simp [member]))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
  exact (activeBound _ (candidates_active_mem _ _ _)).trans (candidates_active_length _ _ _)

/-- A finite graph and finite input give sufficient explicit budgets for the
whole driver, not just one epsilon closure. Captures do not enter the bound.
This is an abstract work/round bound, not a native physical-clock theorem. -/
theorem execute_sufficient [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (closureFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel) (fuel : Nat) :
    ∀ pending previous,
      0 < fuel → pending.length ≤ Fintype.card State →
      (∀ thread ∈ pending, length < thread.point.2.val + fuel) →
      execute (fun thread => thread.point.1) (epsilonChildren graph probe)
        (fun thread => isFrontier (graph thread.point.1)) (edges graph probe)
        (terminal graph) eligible closureFuel fuel pending previous ≠ .incomplete := by
  induction fuel with
  | zero => intro pending previous positive; omega
  | succ fuel ih =>
      intro pending previous positive pendingBound enough
      have closureDone : close graph probe closureFuel pending ≠ none := by
        unfold close
        apply firstVisits_sufficient
        · intro thread
          cases node : graph thread.point.1 <;>
            simp only [epsilonChildren, node, List.length_nil, Nat.zero_le] <;>
            exact edges_length graph probe thread
        · simp only [closureRank, Finset.card_empty, Nat.sub_zero]
          omega
      obtain ⟨frontier, closed⟩ := Option.ne_none_iff_exists'.mp closureDone
      have frontierValid : ∀ thread ∈ frontier,
          length < thread.point.2.val + (fuel + 1) ∧ isFrontier (graph thread.point.1) = true := by
        apply firstVisits_sound (fun thread : Thread State length => thread.point.1)
          (epsilonChildren graph probe) (fun thread => isFrontier (graph thread.point.1))
          (fun thread => length < thread.point.2.val + (fuel + 1)) ?_ closureFuel
          pending ∅ frontier enough closed
        intro source valid target edge
        simpa [(epsilonChildren_same_position graph probe source target edge)] using valid
      have frontierBound : frontier.length ≤ Fintype.card State :=
        firstVisits_length_bound _ _ _ _ _ _ _ closed
      have advancingBound :
          ((candidates (terminal graph) eligible frontier).1.flatMap (edges graph probe)).length ≤
            Fintype.card State :=
        (active_advancing_length graph probe eligible frontier
          (fun thread member => (frontierValid thread member).2)).trans frontierBound
      have advancingEnough : ∀ target ∈
          (candidates (terminal graph) eligible frontier).1.flatMap (edges graph probe),
          length < target.point.2.val + fuel := by
        intro target member
        obtain ⟨source, active, edge⟩ := List.mem_flatMap.mp member
        have sourceMember := candidates_active_mem (terminal graph) eligible frontier source active
        have valid := frontierValid source sourceMember.1
        have advanced := (active_consume_bounds graph probe source valid.2 sourceMember.2).2 target edge
        omega
      simp only [execute, show firstVisits _ _ _ closureFuel pending ∅ = some frontier from closed]
      split
      · intro impossible; cases impossible
      · apply ih _ _ ?_ advancingBound advancingEnough
        have existsTarget : ∃ target,
            target ∈ (candidates (terminal graph) eligible frontier).1.flatMap (edges graph probe) := by
          apply List.exists_mem_of_ne_nil
          intro empty
          simp [empty] at *
        obtain ⟨target, member⟩ := existsTarget
        have positive := advancingEnough target member
        have upper := target.point.2.isLt
        omega

theorem run_ne_incomplete [DecidableEq State] [Fintype State]
    (graph : State → Node State Class Assertion Tag) (probe : Probe Class Assertion length)
    (eligible : Thread State length → Bool) (first : Thread State length)
    (closureFuel inputFuel : Nat)
    (closureEnough : 3 * Fintype.card State + 1 ≤ closureFuel)
    (inputEnough : length + 1 ≤ inputFuel) :
    run graph probe eligible closureFuel inputFuel [first] ≠ .incomplete := by
  apply execute_sufficient graph probe eligible closureFuel closureEnough inputFuel [first] none
  · omega
  · have positive := Fintype.card_pos_iff.mpr (Nonempty.intro first.point.1)
    simpa only [List.length_singleton] using (Nat.succ_le_iff.mpr positive)
  · intro thread member
    simp only [List.mem_singleton] at member
    subst thread
    omega

namespace Controls

private def probe (length : Nat) : Probe Unit Unit length :=
  ⟨fun _ position => position.val < length, fun _ _ => false⟩

private def initial {n : Nat} (state : Fin n) (length : Nat) : Thread (Fin n) length :=
  ⟨(state, 0), fun _ => none, []⟩

private def selectedEnd {State : Type} {Tag : Type} {length : Nat} :
    Result (Thread State length) Tag → Option Nat
  | .finished (some (thread, _)) => some thread.point.2.val
  | _ => none

private def slot {State : Type} {Tag : Type} {length : Nat} (index : Nat) :
    Result (Thread State length) Tag → Option (Option Nat)
  | .finished (some (thread, _)) => some ((thread.registers index).map Fin.val)
  | _ => none

private def preferredPrefix : Fin 5 → Node (Fin 5) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 3
    | 1 => .consume () 2
    | 2 => .accept ()
    | 3 => .consume () 4
    | _ => .consume () 2

theorem fullmatch_selects_later_complete_path :
    selectedEnd (run preferredPrefix (probe 2) (fun _ => true) 20 4 [initial 0 2]) = some 1 ∧
    selectedEnd (run preferredPrefix (probe 2) atInputEnd 20 4 [initial 0 2]) = some 2 := by
  decide

private def greedyCapture (lazy_ : Bool) : Fin 5 → Node (Fin 5) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .save 0 1
    | 1 => if lazy_ then .choice 3 2 else .choice 2 3
    | 2 => .consume () 1
    | 3 => .save 1 4
    | _ => .accept ()

theorem greedy_candidate_can_be_replaced :
    let result := run (greedyCapture false) (probe 3) (fun _ => true) 24 5 [initial 0 3]
    selectedEnd result = some 3 ∧ slot 0 result = some (some 0) ∧ slot 1 result = some (some 3) := by
  decide

theorem lazy_candidate_retains_shortest_preference :
    let result := run (greedyCapture true) (probe 3) (fun _ => true) 24 5 [initial 0 3]
    selectedEnd result = some 0 ∧ slot 0 result = some (some 0) ∧ slot 1 result = some (some 0) := by
  decide

theorem fullmatch_does_not_inherit_lazy_prefix :
    selectedEnd (run (greedyCapture true) (probe 3) atInputEnd 24 5 [initial 0 3]) = some 3 := by
  decide

/-- Entry and loop choices are distinct, implementing a nullable body as
one-or-more inside an optional choice. The raw self-loop is not equivalent. -/
private def normalizedNullableCapture : Fin 7 → Node (Fin 7) Unit Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 6
    | 1 => .save 0 2
    | 2 => .choice 3 4
    | 3 => .consume () 4
    | 4 => .save 1 5
    | 5 => .choice 1 6
    | _ => .accept ()

theorem normalized_nullable_empty_iteration_participates :
    let result := run normalizedNullableCapture (probe 0) (fun _ => true) 30 2 [initial 0 0]
    selectedEnd result = some 0 ∧ slot 0 result = some (some 0) ∧ slot 1 result = some (some 0) := by
  decide

theorem normalized_nullable_consuming_capture_persists :
    let result := run normalizedNullableCapture (probe 2) (fun _ => true) 30 4 [initial 0 2]
    selectedEnd result = some 2 ∧ slot 0 result = some (some 1) ∧ slot 1 result = some (some 2) := by
  decide

private def onlyFirstBranchCaptured : Fin 7 → Node (Fin 7) Bool Unit Unit :=
  fun state => match state.val with
    | 0 => .choice 1 4
    | 1 => .save 0 2
    | 2 => .consume false 3
    | 3 => .save 1 5
    | 4 => .consume true 5
    | 5 => .choice 0 6
    | _ => .accept ()

/-- `(?:(a)|b)+` on `ab`: the later `b` iteration does not clear the earlier
participating `a` group. Capture slots record writes, not iteration-local scope. -/
theorem capture_persists_across_noncapturing_iteration :
    let ab : Probe Bool Unit 2 := ⟨fun class_ position =>
      if position.val = 0 then !class_ else if position.val = 1 then class_ else false,
      fun _ _ => false⟩
    let result := run onlyFirstBranchCaptured ab (fun _ => true) 30 4 [initial 0 2]
    selectedEnd result = some 2 ∧ slot 0 result = some (some 0) ∧ slot 1 result = some (some 1) := by
  decide

end Controls

#print axioms candidates_active_mem
#print axioms candidates_selected_sound
#print axioms candidates_observer
#print axioms execute_map
#print axioms run_erase
#print axioms execute_sound
#print axioms run_match_sound
#print axioms Controls.normalized_nullable_empty_iteration_participates
#print axioms Controls.normalized_nullable_consuming_capture_persists
#print axioms Controls.capture_persists_across_noncapturing_iteration

end Mettapedia.Computability.RegularLanguages.RegexPikeVM

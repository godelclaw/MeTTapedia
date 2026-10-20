import Mettapedia.OSLF.MeTTaIL.CollectionSelection

/-!
# Retained decision traces for collection allocation

Indices refer to the current residual, not to an unordered value alone. A set
decision also records whether its selected member was retained. The trace can
be replayed without repeating search. Erasing traces gives exactly the finite
allocator, preserving repeated bag answers rather than deduplicating them.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

universe u
variable {α : Type u}

structure Decision where
  selected : Nat
  retained : Bool
  deriving DecidableEq, Repr

structure Allocation (α : Type u) where
  values : List α
  residual : List α
  decisions : List Decision
  deriving DecidableEq, Repr

def Allocation.erase (allocation : Allocation α) : List α × List α :=
  (allocation.values, allocation.residual)

def Allocation.prepend (choice : Choice α) (allocation : Allocation α) : Allocation α :=
  { values := choice.value :: allocation.values
    residual := allocation.residual
    decisions := ⟨choice.selected, choice.retained⟩ :: allocation.decisions }

def tracedAllocations (idempotent : Bool) : Nat → List α → List (Allocation α)
  | 0, items => [⟨[], items, []⟩]
  | count + 1, items =>
      (choices idempotent items).flatMap fun choice =>
        (tracedAllocations idempotent count choice.residual).map (Allocation.prepend choice)

/-- Evidence replay follows only the supplied in-range choices. Bag receipts
cannot authorize retention. -/
def replay (idempotent : Bool) : List α → List Decision → Option (List α × List α)
  | items, [] => some ([], items)
  | items, decision :: decisions => do
      let value ← items[decision.selected]?
      if decision.retained && !idempotent then none
      else
        let rest := if decision.retained then items else items.eraseIdx decision.selected
        let (values, final) ← replay idempotent rest decisions
        some (value :: values, final)

theorem tracedAllocations_erase (idempotent : Bool) (count : Nat) (items : List α) :
    (tracedAllocations idempotent count items).map Allocation.erase =
      allocations idempotent count items := by
  induction count generalizing items with
  | zero => rfl
  | succ count ih =>
      simp only [tracedAllocations, allocations, choices, List.map_flatMap, List.flatMap_assoc]
      apply List.flatMap_congr
      intro pair _
      rcases pair with ⟨value, index⟩
      cases idempotent <;>
        simp only [Bool.false_eq_true, ↓reduceIte, residuals, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.map_map]
      · change
          (tracedAllocations false count (items.eraseIdx index)).map
            (fun allocation => (value :: allocation.values, allocation.residual)) = _
        have mapped := congrArg (List.map (fun pair : List α × List α => (value :: pair.1, pair.2)))
          (ih (items.eraseIdx index))
        simpa only [List.map_map, Function.comp_def, Allocation.erase] using mapped
      · have consumed := congrArg (List.map (fun pair : List α × List α => (value :: pair.1, pair.2)))
          (ih (items.eraseIdx index))
        have retained := congrArg (List.map (fun pair : List α × List α => (value :: pair.1, pair.2)))
          (ih items)
        exact congrArg₂ List.append
          (by simpa only [List.map_map, Function.comp_def, Allocation.erase, Allocation.prepend] using consumed)
          (by simpa only [List.map_map, Function.comp_def, Allocation.erase, Allocation.prepend] using retained)

theorem choice_valid {idempotent : Bool} {items : List α} {choice : Choice α}
    (member : choice ∈ choices idempotent items) :
    items[choice.selected]? = some choice.value ∧
      (choice.retained = true → idempotent = true) ∧
      choice.residual = if choice.retained then items else items.eraseIdx choice.selected := by
  simp only [choices, List.mem_flatMap] at member
  obtain ⟨⟨value, index⟩, listed, member⟩ := member
  have found := List.mk_mem_zipIdx_iff_getElem?.mp listed
  cases idempotent <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
  · subst choice
    exact ⟨found, by simp, rfl⟩
  · rcases member with rfl | rfl
    · exact ⟨found, by simp, rfl⟩
    · exact ⟨found, fun _ => rfl, rfl⟩

/-- Every emitted decision trace independently replays to its exact ordered
selected values and final residual. -/
theorem tracedAllocations_replay {idempotent : Bool} {count : Nat}
    {items : List α} {allocation : Allocation α}
    (member : allocation ∈ tracedAllocations idempotent count items) :
    replay idempotent items allocation.decisions = some allocation.erase := by
  induction count generalizing items allocation with
  | zero =>
      simp only [tracedAllocations, List.mem_singleton] at member
      subst allocation
      rfl
  | succ count ih =>
      simp only [tracedAllocations, List.mem_flatMap, List.mem_map] at member
      obtain ⟨choice, selected, tail, allocated, rfl⟩ := member
      obtain ⟨found, allowed, residual⟩ := choice_valid selected
      have continued := ih allocated
      have accepted : (choice.retained && !idempotent) = false := by
        cases kept : choice.retained <;> cases mode : idempotent <;> simp_all
      simp only [Allocation.prepend, replay, found, accepted, Bool.false_eq_true,
        ↓reduceIte, ← residual, continued, Allocation.erase]
      rfl

theorem choice_complete {idempotent : Bool} {items : List α}
    {decision : Decision} {value : α}
    (found : items[decision.selected]? = some value)
    (allowed : decision.retained = true → idempotent = true) :
    (⟨decision.selected, value,
      if decision.retained then items else items.eraseIdx decision.selected,
      decision.retained⟩ : Choice α) ∈ choices idempotent items := by
  have listed : (value, decision.selected) ∈ items.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr found
  apply List.mem_flatMap.mpr
  refine ⟨(value, decision.selected), listed, ?_⟩
  cases kept : decision.retained <;> cases mode : idempotent <;> simp_all

/-- Accepted replay has no extra choices beyond the independently enumerated
allocation relation. Thus altered retention bits and indices must describe a
real allocation, not merely have the expected packet shape. -/
theorem replay_complete {idempotent : Bool} {items values rest : List α}
    {decisions : List Decision}
    (accepted : replay idempotent items decisions = some (values, rest)) :
    (⟨values, rest, decisions⟩ : Allocation α) ∈
      tracedAllocations idempotent decisions.length items := by
  induction decisions generalizing items values rest with
  | nil =>
      have same : ([], items) = (values, rest) := Option.some.inj accepted
      cases same
      exact List.mem_singleton_self _
  | cons decision decisions ih =>
      cases found : items[decision.selected]? with
      | none => simp [replay, found] at accepted
      | some value =>
          have allowed : decision.retained = true → idempotent = true := by
            intro kept
            cases mode : idempotent with
            | false => simp [replay, found, kept, mode] at accepted
            | true => rfl
          have check : (decision.retained && !idempotent) = false := by
            cases kept : decision.retained <;> cases mode : idempotent <;> simp_all
          let residual := if decision.retained then items else items.eraseIdx decision.selected
          cases continued : replay idempotent residual decisions with
          | none => simp [replay, found, check, residual, continued] at accepted
          | some pair =>
              rcases pair with ⟨tail, final⟩
              have continued' :
                  replay idempotent
                    (if decision.retained then items else items.eraseIdx decision.selected)
                    decisions = some (tail, final) := continued
              have same : (value :: tail, final) = (values, rest) := by
                simpa [replay, found, check, continued'] using accepted
              rcases Prod.mk.inj same.symm with ⟨rfl, rfl⟩
              have selected := choice_complete found allowed
              have allocated := ih continued
              apply List.mem_flatMap.mpr
              refine ⟨⟨decision.selected, value, residual, decision.retained⟩, selected, ?_⟩
              exact List.mem_map.mpr ⟨_, allocated, rfl⟩

theorem replay_exact (idempotent : Bool) (items values rest : List α)
    (decisions : List Decision) :
    replay idempotent items decisions = some (values, rest) ↔
      (⟨values, rest, decisions⟩ : Allocation α) ∈
        tracedAllocations idempotent decisions.length items :=
  ⟨replay_complete, tracedAllocations_replay⟩

theorem tracedAllocations_length {idempotent : Bool} {count : Nat}
    {items : List α} {allocation : Allocation α}
    (member : allocation ∈ tracedAllocations idempotent count items) :
    allocation.decisions.length = count := by
  induction count generalizing items allocation with
  | zero =>
      simp only [tracedAllocations, List.mem_singleton] at member
      subst allocation
      rfl
  | succ count ih =>
      simp only [tracedAllocations, List.mem_flatMap, List.mem_map] at member
      obtain ⟨choice, _, tail, allocated, rfl⟩ := member
      simpa only [Allocation.prepend, List.length_cons] using congrArg Nat.succ (ih allocated)

/-- Value equality does not erase distinct bag origins. -/
example :
    (tracedAllocations false 1 [7, 7]).map Allocation.erase =
      [([7], [7]), ([7], [7])] := by decide

example :
    (tracedAllocations false 1 [7, 7]).map (·.decisions) =
      [[⟨0, false⟩], [⟨1, false⟩]] := by decide

/-- The retained set copy is explicit in the accepted trace. -/
example : replay true [7] [⟨0, true⟩, ⟨0, false⟩] = some ([7, 7], []) := by decide

/-- The same retention claim is invalid for a bag. -/
example : replay false [7] [⟨0, true⟩] = none := by decide

/-- An out-of-range receipt is rejected independently of its claimed value. -/
example : replay true [7] [⟨1, false⟩] = none := by decide

end Mettapedia.OSLF.MeTTaIL.CollectionSelection

import Mettapedia.Machines.BranchLocalNeed.FrontierLaws

/-!
# Runs of the reference Need machine that return to a stack bottom

The reference machine's transition never inspects the part of the control
stack below the frames it pushed itself. `step_below` states this: appending
frames below the stack commutes with `step`, except at the one control that
returns to the empty stack. A computation can therefore be run in isolation
with an empty stack and placed under any continuation afterwards.

`Returns spec bottom n ms leaves` runs a worklist of machines depth-first, each
until it returns to the stack `bottom`; `leaves` are those returned machines in
order, with multiplicity, and `n` counts the transitions taken. The order is
the order of the machine's own frontier: `frontier_eq_haltOf` states that the
bounded frontier of a completed run is eventually its halted leaves, and
`returns_of_frontier_halted` that a frontier that halts at some fuel comes from
such a run.

* `Returns.append`, `Returns.split`: worklists concatenate.
* `Returns.deterministic`: a worklist has one run.
* `Returns.seq_iff`: a run under an extra frame `f` is a run to `f` followed by
  the runs that pop `f`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.NeedReturningRuns

open NeedReference

variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type*}

/-- Append frames below a control stack. -/
def extendControl (rest : List (Frame Resume)) :
    Control Local Resume Value StableFault RetryableFault →
      Control Local Resume Value StableFault RetryableFault
  | .force cell stack => .force cell (stack ++ rest)
  | .run state stack => .run state (stack ++ rest)
  | .returned outcome stack => .returned outcome (stack ++ rest)
  | .halted outcome => .halted outcome

/-- Place a machine above the frames `rest`. -/
def below (rest : List (Frame Resume))
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  { m with control := extendControl rest m.control }

@[simp] theorem below_world (rest : List (Frame Resume))
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (below rest m).world = m.world := rfl

@[simp] theorem below_work (rest : List (Frame Resume))
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (below rest m).work = m.work := rfl

@[simp] theorem below_control (rest : List (Frame Resume))
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    (below rest m).control = extendControl rest m.control := rfl

theorem below_nil
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    below ([] : List (Frame Resume)) m = m := by
  rcases m with ⟨world, control, work⟩
  cases control <;> simp [below, extendControl]

theorem below_below (rest rest' : List (Frame Resume))
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    below rest' (below rest m) = below (rest ++ rest') m := by
  rcases m with ⟨world, control, work⟩
  cases control <;> simp [below, extendControl]

theorem branchAlternatives_below
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (owner : EvaluatorId)
    (stack rest : List (Frame Resume)) (index : Nat) (alternatives : List (Rule × Local)) :
    branchAlternatives (below rest machine) base cell record owner (stack ++ rest) index
        alternatives =
      (branchAlternatives machine base cell record owner stack index alternatives).map
        (below rest) := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨rule, state⟩ := head
      simp only [branchAlternatives, List.map_cons, ih]
      rfl

/-- **Stack parametricity.** Appending frames below the stack commutes with a
transition, except when the machine returns to the empty stack. -/
theorem step_below
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (rest : List (Frame Resume))
    (notReturned : ∀ o, m.control ≠ .returned o []) :
    step spec (below rest m) = (step spec m).map (below rest) := by
  rcases m with ⟨world, control, work⟩
  cases control with
  | halted outcome => rfl
  | force cell stack =>
      simp only [below, extendControl, step]
      cases hl : world.heap.lookup cell with
      | none => rfl
      | some record =>
          simp only
          cases hc : record.cache with
          | value v => rfl
          | stableFault f => rfl
          | evaluating o => rfl
          | suspended =>
              simp only
              cases ha : spec.alternatives record.origin with
              | nil => rfl
              | cons a as =>
                  simp only
                  exact branchAlternatives_below
                    ({ world := world, control := .force cell stack, work := work } :
                      Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
                    { world with nextEvaluator := world.nextEvaluator + 1 }
                    cell record world.nextEvaluator stack rest 0 (a :: as)
  | run state stack =>
      simp only [below, extendControl, step]
      cases ha : spec.action state with
      | done outcome => rfl
      | demand cell resume => rfl
      | allocate origin resume =>
          simp only
          cases hw : world.allocate? origin with
          | none => rfl
          | some p => rfl
      | resample source resume =>
          simp only
          cases hl : world.heap.lookup source with
          | none => rfl
          | some record =>
              simp only
              cases hw : world.allocate? record.origin (source.generation + 1) with
              | none => rfl
              | some p => rfl
      | perform effect next => rfl
  | returned outcome stack =>
      cases stack with
      | nil => exact absurd rfl (notReturned outcome)
      | cons frame stack =>
          simp only [below, extendControl, step, List.cons_append]
          cases frame with
          | resume token => rfl
          | commit cell owner =>
              simp only
              cases hl : world.heap.lookup cell with
              | none => rfl
              | some record =>
                  simp only
                  cases hc : record.cache with
                  | evaluating actual =>
                      simp only
                      by_cases hown : actual = owner
                      · simp only [hown, dite_true]
                        cases outcome with
                        | value v => rfl
                        | stableFault f => rfl
                        | retryableFault r => rfl
                      · simp only [hown, dite_false]
                        rfl
                  | suspended => rfl
                  | value v => rfl
                  | stableFault f => rfl

/-! ## Returning runs -/

/-- Depth-first runs of a worklist, each machine until it returns to `bottom`.
The leaves are the returned machines in order; `n` counts transitions. -/
inductive Returns
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (bottom : List (Frame Resume)) :
    Nat → List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) →
      List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) → Prop where
  | nil : Returns spec bottom 0 [] []
  | leaf {n : Nat}
      {m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
      {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
      (outcome : Produced Value StableFault RetryableFault)
      (returned : m.control = .returned outcome bottom) :
      Returns spec bottom n ms leaves → Returns spec bottom n (m :: ms) (m :: leaves)
  | move {n : Nat}
      {m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
      {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
      (notReturned : ∀ o, m.control ≠ .returned o bottom)
      (moves : step spec m ≠ []) :
      Returns spec bottom n (step spec m ++ ms) leaves →
      Returns spec bottom (n + 1) (m :: ms) leaves

variable {spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect}

namespace Returns

theorem append {bottom : List (Frame Resume)} {n₁ n₂ : Nat}
    {ms₁ ms₂ leaves₁ leaves₂ :
      List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h₁ : Returns spec bottom n₁ ms₁ leaves₁) (h₂ : Returns spec bottom n₂ ms₂ leaves₂) :
    Returns spec bottom (n₁ + n₂) (ms₁ ++ ms₂) (leaves₁ ++ leaves₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | leaf outcome returned _ ih => exact .leaf outcome returned ih
  | move notReturned moves _ ih =>
      rw [Nat.add_right_comm]
      exact .move notReturned moves (by simpa [List.append_assoc] using ih)

theorem split {bottom : List (Frame Resume)} {n : Nat}
    {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h : Returns spec bottom n ms leaves) :
    ∀ ms₁ ms₂, ms = ms₁ ++ ms₂ →
      ∃ n₁ n₂ leaves₁ leaves₂, n = n₁ + n₂ ∧ leaves = leaves₁ ++ leaves₂ ∧
        Returns spec bottom n₁ ms₁ leaves₁ ∧ Returns spec bottom n₂ ms₂ leaves₂ := by
  induction h with
  | nil =>
      intro ms₁ ms₂ hms
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hms.symm
      exact ⟨0, 0, [], [], rfl, rfl, .nil, .nil⟩
  | @leaf n m ms leaves outcome returned rest ih =>
      intro ms₁ ms₂ hms
      cases ms₁ with
      | nil =>
          simp only [List.nil_append] at hms
          subst hms
          exact ⟨0, n, [], m :: leaves, by simp, rfl, .nil, .leaf outcome returned rest⟩
      | cons m' ms₁ =>
          simp only [List.cons_append, List.cons.injEq] at hms
          obtain ⟨rfl, rfl⟩ := hms
          obtain ⟨n₁, n₂, l₁, l₂, hn, hl, r₁, r₂⟩ := ih ms₁ ms₂ rfl
          exact ⟨n₁, n₂, m :: l₁, l₂, hn, by simp [hl], .leaf outcome returned r₁, r₂⟩
  | @move n m ms leaves notReturned moves rest ih =>
      intro ms₁ ms₂ hms
      cases ms₁ with
      | nil =>
          simp only [List.nil_append] at hms
          subst hms
          exact ⟨0, n + 1, [], leaves, by simp, rfl, .nil, .move notReturned moves rest⟩
      | cons m' ms₁ =>
          simp only [List.cons_append, List.cons.injEq] at hms
          obtain ⟨rfl, rfl⟩ := hms
          obtain ⟨n₁, n₂, l₁, l₂, hn, hl, r₁, r₂⟩ :=
            ih (NeedReference.step spec m ++ ms₁) ms₂ (by simp)
          exact ⟨n₁ + 1, n₂, l₁, l₂, by omega, hl, .move notReturned moves r₁, r₂⟩

theorem deterministic {bottom : List (Frame Resume)} {n₁ n₂ : Nat}
    {ms leaves₁ leaves₂ :
      List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h₁ : Returns spec bottom n₁ ms leaves₁) (h₂ : Returns spec bottom n₂ ms leaves₂) :
    n₁ = n₂ ∧ leaves₁ = leaves₂ := by
  induction h₁ generalizing n₂ leaves₂ with
  | nil => cases h₂; exact ⟨rfl, rfl⟩
  | leaf outcome returned _ ih =>
      cases h₂ with
      | leaf _ _ rest =>
          obtain ⟨rfl, rfl⟩ := ih rest
          exact ⟨rfl, rfl⟩
      | move notReturned _ _ => exact absurd returned (notReturned outcome)
  | move notReturned _ _ ih =>
      cases h₂ with
      | leaf outcome returned _ => exact absurd returned (notReturned outcome)
      | move _ _ rest =>
          obtain ⟨rfl, rfl⟩ := ih rest
          exact ⟨rfl, rfl⟩

theorem singleton_step {bottom : List (Frame Resume)} {n : Nat}
    {m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (notReturned : ∀ o, m.control ≠ .returned o bottom)
    (h : Returns spec bottom n [m] leaves) :
    ∃ n', n = n' + 1 ∧ Returns spec bottom n' (NeedReference.step spec m) leaves := by
  cases h with
  | leaf outcome returned _ => exact absurd returned (notReturned outcome)
  | @move n' _ _ _ _ _ rest => exact ⟨n', rfl, by simpa using rest⟩

theorem of_step {bottom : List (Frame Resume)} {n : Nat}
    {m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    {leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (notReturned : ∀ o, m.control ≠ .returned o bottom)
    (moves : NeedReference.step spec m ≠ [])
    (h : Returns spec bottom n (NeedReference.step spec m) leaves) :
    Returns spec bottom (n + 1) [m] leaves :=
  .move notReturned moves (by simpa using h)

theorem single_leaf {bottom : List (Frame Resume)}
    {m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect}
    (outcome : Produced Value StableFault RetryableFault)
    (returned : m.control = .returned outcome bottom) :
    Returns spec bottom 0 [m] [m] :=
  .leaf outcome returned .nil

theorem leaves_returned {bottom : List (Frame Resume)} {n : Nat}
    {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h : Returns spec bottom n ms leaves) :
    ∀ l ∈ leaves, ∃ o, l.control = .returned o bottom := by
  induction h with
  | nil => simp
  | leaf outcome returned _ ih =>
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨outcome, returned⟩
      · exact ih l hl
  | move _ _ _ ih => exact ih

end Returns

/-! ## Sequencing under a frame -/

theorem extendControl_returned_ne {rest : List (Frame Resume)} {f : Frame Resume}
    {c : Control Local Resume Value StableFault RetryableFault}
    {o : Produced Value StableFault RetryableFault} :
    extendControl (f :: rest) c ≠ .returned o rest := by
  intro h
  cases c with
  | force cell stack => simp [extendControl] at h
  | run state stack => simp [extendControl] at h
  | halted outcome => simp [extendControl] at h
  | returned outcome stack =>
      simp only [extendControl, Control.returned.injEq] at h
      have := congrArg List.length h.2
      simp at this
      omega

/-- Splitting a run under a frame `f`: first the runs to `f`, then the runs
that pop `f` and continue to `rest`. -/
theorem seq_split {rest : List (Frame Resume)} {f : Frame Resume} {n : Nat}
    {W leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h : Returns spec rest n W leaves) :
    ∀ (C ms : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)),
      W = C ++ ms.map (below (f :: rest)) →
      ∃ nC n₁ n₂ leavesC inner leaves₂,
        n = nC + n₁ + n₂ ∧ leaves = leavesC ++ leaves₂ ∧
        Returns spec rest nC C leavesC ∧ Returns spec [] n₁ ms inner ∧
        Returns spec rest n₂ (inner.map (below (f :: rest))) leaves₂ := by
  induction h with
  | nil =>
      intro C ms hW
      obtain ⟨rfl, hms⟩ := List.append_eq_nil_iff.mp hW.symm
      have : ms = [] := List.map_eq_nil_iff.mp hms
      subst this
      exact ⟨0, 0, 0, [], [], [], rfl, rfl, .nil, .nil, .nil⟩
  | @leaf n m W' leaves outcome returned rest' ih =>
      intro C ms hW
      cases C with
      | nil =>
          cases ms with
          | nil => simp at hW
          | cons m₀ ms =>
              simp only [List.nil_append, List.map_cons, List.cons.injEq] at hW
              obtain ⟨rfl, -⟩ := hW
              exact absurd returned extendControl_returned_ne
      | cons c C =>
          simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, rfl⟩ := hW
          obtain ⟨nC, n₁, n₂, lC, inner, l₂, hn, hl, rC, r₁, r₂⟩ := ih C ms rfl
          exact ⟨nC, n₁, n₂, m :: lC, inner, l₂, hn, by simp [hl],
            .leaf outcome returned rC, r₁, r₂⟩
  | @move n m W' leaves notReturned moves rest' ih =>
      intro C ms hW
      cases C with
      | nil =>
          cases ms with
          | nil => simp at hW
          | cons m₀ ms =>
              simp only [List.nil_append, List.map_cons, List.cons.injEq] at hW
              obtain ⟨rfl, rfl⟩ := hW
              by_cases hret : ∃ o, m₀.control = .returned o []
              · -- `m₀` is an inner leaf: its next step pops `f`.
                obtain ⟨o, ho⟩ := hret
                obtain ⟨nC, n₁, n₂, lC, inner, l₂, hn, hl, rC, r₁, r₂⟩ :=
                  ih (step spec (below (f :: rest) m₀)) ms (by simp)
                refine ⟨0, n₁, nC + 1 + n₂, [], m₀ :: inner, lC ++ l₂, by omega,
                  by simp [hl], .nil, .leaf o ho r₁, ?_⟩
                have first : Returns spec rest (nC + 1) [below (f :: rest) m₀] lC :=
                  .move notReturned moves (by simpa using rC)
                simpa [Nat.add_assoc] using first.append r₂
              · have notRet : ∀ o, m₀.control ≠ .returned o [] := fun o h => hret ⟨o, h⟩
                have hs := step_below spec m₀ (f :: rest) notRet
                rw [hs] at rest' moves ih
                have moves₀ : step spec m₀ ≠ [] := by
                  intro h0; rw [h0] at moves; exact moves rfl
                obtain ⟨nC, n₁, n₂, lC, inner, l₂, hn, hl, rC, r₁, r₂⟩ :=
                  ih [] (step spec m₀ ++ ms) (by simp)
                cases rC
                refine ⟨0, n₁ + 1, n₂, [], inner, l₂, by omega, by simp [hl], .nil, ?_, r₂⟩
                exact .move notRet moves₀ r₁
      | cons c C =>
          simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, rfl⟩ := hW
          obtain ⟨nC, n₁, n₂, lC, inner, l₂, hn, hl, rC, r₁, r₂⟩ :=
            ih (NeedReference.step spec m ++ C) ms (by simp)
          exact ⟨nC + 1, n₁, n₂, lC, inner, l₂, by omega, hl,
            .move notReturned moves (by simpa using rC), r₁, r₂⟩

/-- Joining runs under a frame `f`. -/
theorem seq_join {rest : List (Frame Resume)} {f : Frame Resume} {n₁ : Nat}
    {ms inner : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h₁ : Returns spec [] n₁ ms inner) :
    ∀ {n₂ : Nat} {leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault
        Effect)},
      Returns spec rest n₂ (inner.map (below (f :: rest))) leaves →
      Returns spec rest (n₁ + n₂) (ms.map (below (f :: rest))) leaves := by
  induction h₁ with
  | nil => intro n₂ leaves h₂; simpa using h₂
  | @leaf n m ms inner' outcome returned rest' ih =>
      intro n₂ leaves h₂
      simp only [List.map_cons] at h₂ ⊢
      obtain ⟨k₁, k₂, l₁, l₂, hk, hl, r₁, r₂⟩ := h₂.split [below (f :: rest) m] _ rfl
      have r₂' := ih r₂
      subst hl hk
      have := r₁.append r₂'
      simpa [Nat.add_left_comm, Nat.add_assoc, Nat.add_comm] using this
  | @move n m ms inner' notReturned moves rest' ih =>
      intro n₂ leaves h₂
      have hs := step_below spec m (f :: rest) notReturned
      have := ih h₂
      simp only [List.map_append] at this
      simp only [List.map_cons]
      have notRet' : ∀ o, (below (f :: rest) m).control ≠ .returned o rest :=
        fun o => extendControl_returned_ne
      have moves' : step spec (below (f :: rest) m) ≠ [] := by
        rw [hs]; simpa using moves
      rw [Nat.add_right_comm]
      exact .move notRet' moves' (by rw [hs]; exact this)

theorem seq_iff {rest : List (Frame Resume)} {f : Frame Resume} {n : Nat}
    {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)} :
    Returns spec rest n (ms.map (below (f :: rest))) leaves ↔
      ∃ n₁ n₂ inner, n = n₁ + n₂ ∧ Returns spec [] n₁ ms inner ∧
        Returns spec rest n₂ (inner.map (below (f :: rest))) leaves := by
  constructor
  · intro h
    obtain ⟨nC, n₁, n₂, lC, inner, l₂, hn, hl, rC, r₁, r₂⟩ := seq_split (f := f) h [] ms (by simp)
    cases rC
    exact ⟨n₁, n₂, inner, by omega, r₁, by simpa using hl ▸ r₂⟩
  · rintro ⟨n₁, n₂, inner, rfl, r₁, r₂⟩
    exact seq_join r₁ r₂

/-! ## Frontiers of completed runs -/

/-- The halting transition of a machine that returned to the empty stack. -/
def haltOf (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    Machine Origin Local Resume Rule Value StableFault RetryableFault Effect :=
  match m.control with
  | .returned outcome [] => finished m m.world (.halted outcome) 0 0 0 0
  | _ => m

theorem step_returned_nil
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (h : m.control = .returned outcome []) :
    step spec m = [haltOf m] := by
  rcases m with ⟨world, control, work⟩
  simp only at h
  subst h
  rfl

theorem haltOf_isHalted
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (h : m.control = .returned outcome []) :
    isHalted (haltOf m) = true := by
  rcases m with ⟨world, control, work⟩
  simp only at h
  subst h
  rfl

theorem haltedOutcome_haltOf
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (outcome : Produced Value StableFault RetryableFault)
    (h : m.control = .returned outcome []) :
    haltedOutcome (haltOf m) = some outcome := by
  rcases m with ⟨world, control, work⟩
  simp only at h
  subst h
  rfl

theorem frontier_add
    (fuel more : Nat)
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect) :
    NeedFrontierLaws.frontier spec (fuel + more) m = (NeedFrontierLaws.frontier spec fuel m).flatMap (NeedFrontierLaws.frontier spec more) := by
  induction fuel generalizing m with
  | zero => simp [NeedFrontierLaws.frontier]
  | succ fuel ih =>
      rw [show fuel + 1 + more = (fuel + more) + 1 by omega]
      simp only [NeedFrontierLaws.frontier, List.flatMap_assoc]
      exact List.flatMap_congr (fun x _ => ih x)

theorem frontier_stable_of_halted
    (fuel more : Nat)
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (halted : ∀ x ∈ NeedFrontierLaws.frontier spec fuel m, isHalted x = true) :
    NeedFrontierLaws.frontier spec (fuel + more) m = NeedFrontierLaws.frontier spec fuel m := by
  rw [frontier_add]
  have hfix : ∀ x ∈ NeedFrontierLaws.frontier spec fuel m, NeedFrontierLaws.frontier spec more x = [x] :=
    fun x hx => NeedFrontierLaws.frontier_halted spec more x (halted x hx)
  calc (NeedFrontierLaws.frontier spec fuel m).flatMap (NeedFrontierLaws.frontier spec more)
        = (NeedFrontierLaws.frontier spec fuel m).flatMap (fun x => [x]) := List.flatMap_congr hfix
    _ = NeedFrontierLaws.frontier spec fuel m := by simp

/-- **Completed runs are eventual frontiers**: from some fuel on, the bounded
frontier of a completed worklist is exactly its halted leaves, in order. -/
theorem frontier_eq_haltOf {n : Nat}
    {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h : Returns spec [] n ms leaves) :
    ∃ N, ∀ fuel, N ≤ fuel → ms.flatMap (NeedFrontierLaws.frontier spec fuel) = leaves.map haltOf := by
  induction h with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | @leaf n m ms leaves outcome returned _ ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + 1, fun fuel hfuel => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hm : NeedFrontierLaws.frontier spec (k + 1) m = [haltOf m] := by
        have hadv : advance spec m = [haltOf m] := by
          simp [advance, step_returned_nil m outcome returned]
        simp only [NeedFrontierLaws.frontier, hadv, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact NeedFrontierLaws.frontier_halted spec k _ (haltOf_isHalted m outcome returned)
      simp only [List.flatMap_cons, hm, hN (k + 1) (by omega), List.map_cons]
      rfl
  | @move n m ms leaves notReturned moves rest' ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + 1, fun fuel hfuel => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have running : isHalted m = false := by
        cases hc : isHalted m with
        | false => rfl
        | true =>
            exact absurd ((NeedFrontierLaws.step_empty_iff spec m).mpr hc) moves
      have hk := hN k (by omega)
      have allHalted : ∀ x ∈ (NeedReference.step spec m ++ ms).flatMap
          (NeedFrontierLaws.frontier spec k), isHalted x = true := by
        rw [hk]
        intro x hx
        obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp hx
        obtain ⟨o, ho⟩ := rest'.leaves_returned leaf hleaf
        exact haltOf_isHalted leaf o ho
      have stableMs : ms.flatMap (NeedFrontierLaws.frontier spec (k + 1)) =
          ms.flatMap (NeedFrontierLaws.frontier spec k) := by
        apply List.flatMap_congr
        intro x hx
        apply frontier_stable_of_halted k 1 x
        intro y hy
        apply allHalted
        simp only [List.flatMap_append, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨x, hx, hy⟩
      have hm : NeedFrontierLaws.frontier spec (k + 1) m =
          (NeedReference.step spec m).flatMap (NeedFrontierLaws.frontier spec k) := by
        simp [NeedFrontierLaws.frontier, NeedFrontierLaws.advance_running spec m running]
      calc (m :: ms).flatMap (NeedFrontierLaws.frontier spec (k + 1))
          = NeedFrontierLaws.frontier spec (k + 1) m ++
              ms.flatMap (NeedFrontierLaws.frontier spec (k + 1)) := by simp
        _ = (NeedReference.step spec m).flatMap (NeedFrontierLaws.frontier spec k) ++
              ms.flatMap (NeedFrontierLaws.frontier spec k) := by rw [hm, stableMs]
        _ = (NeedReference.step spec m ++ ms).flatMap (NeedFrontierLaws.frontier spec k) := by
              simp [List.flatMap_append]
        _ = leaves.map haltOf := hk

/-! ## Frontiers that halt come from completed runs -/

theorem branchAlternatives_not_halted
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (base : World Origin Rule Value StableFault RetryableFault Effect)
    (cell : CellId) (record : CellRecord Origin Value StableFault) (owner : EvaluatorId)
    (stack : List (Frame Resume)) :
    ∀ (index : Nat) (alternatives : List (Rule × Local)),
      ∀ x ∈ branchAlternatives machine base cell record owner stack index alternatives,
        isHalted x = false := by
  intro index alternatives
  induction alternatives generalizing index with
  | nil => simp [branchAlternatives]
  | cons head tail ih =>
      obtain ⟨rule, state⟩ := head
      intro x hx
      simp only [branchAlternatives, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact ih (index + 1) x hx

/-- Only the return to the empty stack halts: every successor of any other
control is running. -/
theorem step_not_halted
    (m : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (notReturned : ∀ o, m.control ≠ .returned o []) :
    ∀ x ∈ step spec m, isHalted x = false := by
  rcases m with ⟨world, control, work⟩
  cases control with
  | returned outcome stack =>
      cases stack with
      | nil => exact absurd rfl (notReturned outcome)
      | cons frame rest =>
          simp only [step]
          repeat' first
            | split
            | simp [retryMachine, finished, isHalted]
            | simp_all
  | halted outcome => simp [step]
  | force cell stack =>
      simp only [step]
      repeat' first
        | split
        | exact branchAlternatives_not_halted _ _ _ _ _ _ _ _
        | simp [retryMachine, finished, isHalted]
  | run state stack =>
      simp only [step]
      repeat' first
        | split
        | simp [retryMachine, finished, isHalted]

/-- **Halted frontiers come from completed runs.** If the bounded frontier of a
worklist of running machines has halted at some fuel, the worklist has a
completed run. -/
theorem returns_of_frontier_halted :
    ∀ (fuel : Nat)
      (ms : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)),
      (∀ m ∈ ms, isHalted m = false) →
      (∀ x ∈ ms.flatMap (NeedFrontierLaws.frontier spec fuel), isHalted x = true) →
      ∃ n leaves, Returns spec [] n ms leaves := by
  intro fuel
  induction fuel with
  | zero =>
      intro ms hrun hhalt
      cases ms with
      | nil => exact ⟨0, [], .nil⟩
      | cons m rest =>
          have hm := hhalt m (by simp [NeedFrontierLaws.frontier])
          rw [hrun m (by simp)] at hm
          cases hm
  | succ fuel ih =>
      intro ms
      induction ms with
      | nil => intro _ _; exact ⟨0, [], .nil⟩
      | cons m rest ihr =>
          intro hrun hhalt
          have hm : isHalted m = false := hrun m (by simp)
          obtain ⟨n₂, l₂, h₂⟩ := ihr (fun x hx => hrun x (by simp [hx])) (by
            intro x hx
            apply hhalt
            simp only [List.flatMap_cons, List.mem_append]
            exact Or.inr hx)
          by_cases hret : ∃ o, m.control = .returned o []
          · obtain ⟨o, ho⟩ := hret
            exact ⟨n₂, m :: l₂, .leaf o ho h₂⟩
          · have notRet : ∀ o, m.control ≠ .returned o [] := fun o h => hret ⟨o, h⟩
            have hfront : NeedFrontierLaws.frontier spec (fuel + 1) m =
                (step spec m).flatMap (NeedFrontierLaws.frontier spec fuel) := by
              simp [NeedFrontierLaws.frontier, NeedFrontierLaws.advance_running spec m hm]
            obtain ⟨n₁, l₁, h₁⟩ := ih (step spec m) (step_not_halted m notRet) (by
              intro x hx
              apply hhalt
              simp only [List.flatMap_cons, List.mem_append]
              left
              rw [hfront]
              exact hx)
            have moves : step spec m ≠ [] := by
              intro h0
              have := (NeedFrontierLaws.step_empty_iff spec m).mp h0
              rw [hm] at this
              cases this
            exact ⟨n₁ + n₂ + 1, l₁ ++ l₂, .move notRet moves (h₁.append h₂)⟩

/-- A frontier that has halted is the halted leaves of the completed run. -/
theorem frontier_eq_of_halted {n : Nat}
    {ms leaves : List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)}
    (h : Returns spec [] n ms leaves) (fuel : Nat)
    (halted : ∀ x ∈ ms.flatMap (NeedFrontierLaws.frontier spec fuel), isHalted x = true) :
    ms.flatMap (NeedFrontierLaws.frontier spec fuel) = leaves.map haltOf := by
  obtain ⟨N, hN⟩ := frontier_eq_haltOf h
  have stable : ms.flatMap (NeedFrontierLaws.frontier spec (fuel + N)) =
      ms.flatMap (NeedFrontierLaws.frontier spec fuel) := by
    apply List.flatMap_congr
    intro m hm
    apply frontier_stable_of_halted fuel N m
    intro x hx
    exact halted x (List.mem_flatMap.mpr ⟨m, hm, hx⟩)
  rw [← stable]
  exact hN (fuel + N) (by omega)

end Mettapedia.Machines.BranchLocalNeed.NeedReturningRuns

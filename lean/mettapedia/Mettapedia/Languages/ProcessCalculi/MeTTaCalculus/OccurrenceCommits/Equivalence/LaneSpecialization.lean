import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceCompilation

/-!
# What "lane L's operation equals this transform instance" means

Each MeTTa lane keeps its own operations (`match`, `get-atoms`, `add-atom`, `remove-atom`, …),
and each is to be shown an instance of one `transform`. The claim needs a stated observable, because
the lanes see different things: Prime's results are an unordered bag (settled decision §11), while
HE and PeTTa produce a sequence, in storage order, with the effects of templates interleaved.

## The statement form

A **lane** (`Lane`) fixes its outcome type, how it reads the bag of outcomes a transform produces
(`read`, the lane's order policy: for Prime the bag itself, for HE the storage order), and what it
observes of an outcome (`observe`). Two lane programs are **lane-equivalent** when the lane observes
the same in every context (`Lane.Equiv`, an equivalence relation); a native operation **specializes**
a transform instance when it is lane-equivalent to the instance read by the lane
(`Lane.Specializes`).

* A sequence lane that observes the full sequence is finer than the bag lane: a sequence
  specialization gives a bag specialization (`Specializes.toBag`), not conversely: two programs can
  be equal under bag observation and differ under sequence observation, whether the difference is
  the order of answers or the interleaving of an effect with an answer
  (`Controls.bag_not_sequence`).

## The first instance: Prime `match` is `every` over a read

Prime's `match` over a store returns the bag of template instances, one for each occurrence and
each matcher answer for its label (`primeMatch`). The transform
`transform space (every (read p)) template` has one row, whose commit keeps every matched
occurrence, takes nothing, queries the region of `p` (the completeness query) and makes exactly
that bag (`match_every_makes`, `match_every_takes`). Its compiled `each` form, one row per match,
makes the same bag in total (`match_each_makes`). So under the bag lane `match` specializes both
(`prime_match_specializes_every`, `prime_match_specializes_each`), for every term layer and
matcher; the matcher obligations of the sources module (sound, complete, minimal) are what make the
compiled rows the meaning of the pattern, so they are what makes this a statement about patterns
rather than about one matcher.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe u v w x

/-! ## Lanes and the statement form -/

/-- A lane: its outcomes, how it reads the bag of events of a transform instance in a context, and
what it observes of an outcome. -/
structure Lane (Ctx : Type u) (Ev : Type v) (Outcome : Type w) (Obs : Type x) where
  read : Ctx → Multiset Ev → Outcome
  observe : Outcome → Obs

namespace Lane

variable {Ctx : Type u} {Ev : Type v} {Outcome : Type w} {Obs : Type x}

/-- Lane-equivalent programs: the lane observes the same in every context. -/
def Equiv (lane : Lane Ctx Ev Outcome Obs) (f g : Ctx → Outcome) : Prop :=
  ∀ ctx, lane.observe (f ctx) = lane.observe (g ctx)

theorem Equiv.refl (lane : Lane Ctx Ev Outcome Obs) (f : Ctx → Outcome) : lane.Equiv f f :=
  fun _ => rfl

theorem Equiv.symm {lane : Lane Ctx Ev Outcome Obs} {f g : Ctx → Outcome} (h : lane.Equiv f g) :
    lane.Equiv g f := fun ctx => (h ctx).symm

theorem Equiv.trans {lane : Lane Ctx Ev Outcome Obs} {f g k : Ctx → Outcome} (h : lane.Equiv f g)
    (h' : lane.Equiv g k) : lane.Equiv f k := fun ctx => (h ctx).trans (h' ctx)

/-- **The statement form**: a native operation of the lane specializes a transform instance when it is
lane-equivalent to the instance's events, read by the lane. -/
def Specializes (lane : Lane Ctx Ev Outcome Obs) (native : Ctx → Outcome) (inst : Ctx → Multiset Ev) :
    Prop :=
  lane.Equiv native fun ctx => lane.read ctx (inst ctx)

end Lane

section Instances

variable {Ctx : Type u} {Ev : Type v}

/-- **The bag lane** (Prime): outcomes are bags, the read is the bag itself, the observation is the
bag. -/
def bagLane (Ctx : Type u) (Ev : Type v) : Lane Ctx Ev (Multiset Ev) (Multiset Ev) := ⟨fun _ b => b, id⟩

/-- An order policy enumerates each bag: it lists exactly its events. -/
def IsOrderPolicy (order : Ctx → Multiset Ev → List Ev) : Prop :=
  ∀ ctx b, (order ctx b : Multiset Ev) = b

/-- **A sequence lane** (HE storage order, PeTTa): outcomes are lists of events, answers and
effects interleaved; the read is the lane's order policy, and the lane observes the whole list. -/
def seqLane (order : Ctx → Multiset Ev → List Ev) : Lane Ctx Ev (List Ev) (List Ev) := ⟨order, id⟩

/-- The bag a sequence lane's native operation produces. -/
def asBag (native : Ctx → List Ev) : Ctx → Multiset Ev := fun ctx => (native ctx : Multiset Ev)

/-- **A sequence specialization is a bag specialization.** -/
theorem Specializes.toBag {order : Ctx → Multiset Ev → List Ev} (policy : IsOrderPolicy order)
    {native : Ctx → List Ev} {inst : Ctx → Multiset Ev}
    (h : (seqLane order).Specializes native inst) : (bagLane Ctx Ev).Specializes (asBag native) inst := by
  intro ctx
  have := congrArg (fun l : List Ev => (l : Multiset Ev)) (h ctx)
  simp only [seqLane, id] at this
  rw [policy] at this
  exact this

end Instances

/-! ## Prime `match` as `every` over a read -/

section PrimeMatch

variable {O : Type u} {V : Type v} {T : Type w} {P : Type x} [DecidableEq O]
  (L : TermLayer V T P) (m : Matcher V T P) (label : O → T)

/-- The labels a template instance makes, or nothing when the template does not instantiate. -/
def instBag (template : List P) (τ : Subst V T) : Multiset T :=
  match instTemplate L τ template with
  | some ls => (ls : Multiset T)
  | none => 0

/-- **Prime's `match`**: one template instance for each occurrence of the store and each matcher
answer for its label. -/
def primeMatch (S : Finset O) (p : P) (template : List P) : Multiset T :=
  S.val.bind fun o => (↑(m p (fun _ => none) (label o)) : Multiset (Subst V T)).bind (instBag L template)

/-- `match` as a transform: read every match of `p`, make the template. -/
def matchEvery (p : P) (template : List P) : Transform V T P := ⟨.every (.cons (.read p) .done), template⟩

/-- `match` as a transform with one row per match. -/
def matchEach (p : P) (template : List P) : Transform V T P := ⟨.cons (.read p) .done, template⟩

/-- The rows of a read followed by the template. -/
def readRows (template : List P) (o : O) (τ : Subst V T) :
    Multiset (Subst V T × List (Pick O T)) :=
  match instTemplate L τ template with
  | some ls => {(τ, [Pick.keep o, Pick.make (ls : Multiset T)])}
  | none => 0

variable {L m label}

theorem rows_read (S : Finset O) (p : P) (template : List P) (σ : Subst V T) :
    rows L m label S template (.cons (.read p) .done) σ =
      S.val.bind fun o => (↑(m p σ (label o)) : Multiset (Subst V T)).bind
        (readRows (O := O) L template o) := by
  simp only [rows, stepRows]
  rw [Multiset.bind_assoc]
  refine Multiset.bind_congr fun o _ => ?_
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun τ _ => ?_
  unfold readRows
  cases instTemplate L τ template <;> simp

omit [DecidableEq O] in
theorem readRows_linear {template : List P} {o : O} {τ : Subst V T}
    {y : Subst V T × List (Pick O T)} (member : y ∈ readRows L template o τ) :
    (footprintOf y.2).Linear ∧ (footprintOf y.2).takes = 0 := by
  unfold readRows at member
  cases h : instTemplate L τ template with
  | none => simp [h] at member
  | some ls =>
      simp only [h, Multiset.mem_singleton] at member
      subst member
      exact ⟨⟨by simp [footprintOf_cons, Pick.footprint], by simp [footprintOf_cons, Pick.footprint]⟩,
        by simp [footprintOf_cons, Pick.footprint]⟩

omit [DecidableEq O] in
theorem readRows_makes (template : List P) (o : O) (τ : Subst V T) :
    ((readRows L template o τ).map fun y => (footprintOf y.2).makes).sum = instBag L template τ := by
  unfold readRows instBag
  cases instTemplate L τ template <;> simp [footprintOf_cons, Pick.footprint]

/-- **The `every` row of `match` makes the bag of `match`.** -/
theorem match_every_makes (S : Finset O) (p : P) (template : List P) :
    (everyFootprint L m label S template (.cons (.read p) .done) (fun _ => none)).makes =
      primeMatch L m label S p template := by
  unfold everyFootprint
  rw [rows_read]
  have allLinear : ∀ y ∈ S.val.bind (fun o => (↑(m p (fun _ => none) (label o)) :
      Multiset (Subst V T)).bind (readRows L template o)), (footprintOf y.2).Linear := by
    intro y member
    obtain ⟨o, -, inner⟩ := Multiset.mem_bind.mp member
    obtain ⟨τ, -, inRows⟩ := Multiset.mem_bind.mp inner
    exact (readRows_linear inRows).1
  rw [Multiset.filter_eq_self.mpr allLinear]
  simp only [Footprint.makes_add, Footprint.makes_sum, complQueries, add_zero, Multiset.map_map,
    Function.comp_def]
  rw [Multiset.map_bind, Multiset.sum_bind]
  unfold primeMatch
  rw [Multiset.bind]
  congr 1
  refine Multiset.map_congr rfl fun o _ => ?_
  rw [Multiset.map_bind, Multiset.sum_bind, Multiset.bind]
  congr 1
  exact Multiset.map_congr rfl fun τ _ => readRows_makes template o τ

/-- **The `every` row of `match` takes nothing.** -/
theorem match_every_takes (S : Finset O) (p : P) (template : List P) :
    (everyFootprint L m label S template (.cons (.read p) .done) (fun _ => none)).takes = 0 := by
  unfold everyFootprint
  rw [rows_read]
  simp only [Footprint.takes_add, Footprint.takes_sum, complQueries, add_zero, Multiset.map_map,
    Function.comp_def]
  refine Multiset.sum_eq_zero fun x member => ?_
  obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨o, -, inner⟩ := Multiset.mem_bind.mp (Multiset.mem_of_mem_filter inFilter)
  obtain ⟨τ, -, inRows⟩ := Multiset.mem_bind.mp inner
  exact (readRows_linear inRows).2

/-- **The rows of `match` taken one at a time make, in total, the bag of `match`.** -/
theorem match_each_makes (S : Finset O) (p : P) (template : List P) :
    (((matchEach p template).rows L m label S).map fun y => (footprintOf y.2).makes).sum =
      primeMatch L m label S p template := by
  unfold Transform.rows matchEach primeMatch
  simp only
  rw [rows_read, Multiset.map_bind, Multiset.sum_bind, Multiset.bind]
  congr 1
  refine Multiset.map_congr rfl fun o _ => ?_
  rw [Multiset.map_bind, Multiset.sum_bind, Multiset.bind]
  congr 1
  exact Multiset.map_congr rfl fun τ _ => readRows_makes template o τ

variable (L m label) in
/-- The answers of a transform at a store: what its rows make, over all rows. -/
def answers (t : Transform V T P) (S : Finset O) : Multiset T :=
  ((t.rows L m label S).map fun y => (footprintOf y.2).makes).sum

theorem answers_matchEvery (S : Finset O) (p : P) (template : List P) :
    answers L m label (matchEvery p template) S = primeMatch L m label S p template := by
  unfold answers Transform.rows matchEvery
  simp only [rows_every, Multiset.map_singleton, Multiset.sum_singleton, footprintOf_cons,
    footprintOf_nil, add_zero, Pick.footprint]
  exact match_every_makes S p template

variable (L m label)

/-- **Prime `match` specializes `every` over a read** under the bag lane, at every store. -/
theorem prime_match_specializes_every (p : P) (template : List P) :
    (bagLane (Finset O) T).Specializes (fun S => primeMatch L m label S p template)
      (fun S => answers L m label (matchEvery p template) S) :=
  fun S => (answers_matchEvery S p template).symm

/-- **Prime `match` specializes the one-row-per-match transform** under the bag lane. -/
theorem prime_match_specializes_each (p : P) (template : List P) :
    (bagLane (Finset O) T).Specializes (fun S => primeMatch L m label S p template)
      (fun S => answers L m label (matchEach p template) S) :=
  fun S => (match_each_makes S p template).symm

/-- **A commit of the `match` row leaves the store as it was, apart from the answers it makes.** -/
theorem match_commit_fire {S : Finset O} {p : P} {template : List P} {c : Commit O T}
    (commit : IsCommitOf label S
      (everyFootprint L m label S template (.cons (.read p) .done) (fun _ => none)) c) :
    fire S c = S ∪ c.made ∧ labels label c.made = primeMatch L m label S p template := by
  refine ⟨?_, by rw [commit.made, match_every_makes]⟩
  rw [fire, commit.taken, match_every_takes]
  simp

end PrimeMatch

/-! ## Controls -/

namespace Controls

/-- Answers and effects. -/
inductive Ev where
  | answer (n : ℕ)
  | effect (n : ℕ)
  deriving DecidableEq, Repr

open Ev

/-- **Equal bags, different sequences.** Two answers in either order, and an effect before or after
an answer, are equal under the bag lane and different under a sequence lane. -/
theorem bag_not_sequence :
    ((([answer 1, answer 2] : List Ev) : Multiset Ev) = (([answer 2, answer 1] : List Ev) : Multiset Ev) ∧
      ([answer 1, answer 2] : List Ev) ≠ [answer 2, answer 1]) ∧
    ((([answer 1, effect 1] : List Ev) : Multiset Ev) = (([effect 1, answer 1] : List Ev) : Multiset Ev) ∧
      ([answer 1, effect 1] : List Ev) ≠ [effect 1, answer 1]) := by
  refine ⟨⟨?_, by decide⟩, ⟨?_, by decide⟩⟩
  · exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
  · exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)

/-- **A bag specialization that is not a sequence specialization**: a native operation listing two
answers in one order, against an instance read by the opposite order policy. -/
theorem bag_specialization_not_sequence :
    let native : Unit → List Ev := fun _ => [answer 1, answer 2]
    let inst : Unit → Multiset Ev := fun _ => (([answer 1, answer 2] : List Ev) : Multiset Ev)
    let order : Unit → Multiset Ev → List Ev := fun _ b =>
      if b = (([answer 1, answer 2] : List Ev) : Multiset Ev) then [answer 2, answer 1] else b.toList
    IsOrderPolicy order ∧ (bagLane Unit Ev).Specializes (asBag native) inst ∧
      ¬ (seqLane order).Specializes native inst := by
  intro native inst order
  refine ⟨fun _ b => ?_, fun _ => rfl, fun h => ?_⟩
  · simp only [order]
    split_ifs with hb
    · rw [hb]; exact Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)
    · exact Multiset.coe_toList b
  · have := h ()
    simp [seqLane, order, native, inst] at this

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

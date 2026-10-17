import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.List.Forall2
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-!
# What a client without the unsealer can observe

A module hands sealed values to clients. A client sees an atom whose sealed
leaves show a public nickname and an opaque handle (`Shown`); it sends requests
built from data it writes and from values it received, and finally states a
verdict. This model chooses an unordered observer profile: results of a call
are a multiset, and `outcomes` collects every verdict over every delivery order.
This is not a result-order law for every MeTTa dialect. Ordered HE and PeTTa
execution observations require their ordered machine adapters instead.

**The observer model is a class of relations between handles.** A client is
*parametric* for a class when, on two histories whose values agree except for
handles related by a relation of the class, it asks related questions and gives
the same verdict (Sumii and Pierce's generalized contextual equivalence, with the
context's knowledge as the relation; Pitts and Stark's partial bijections on
names).

* `AnyRelation`: the client cannot compare handles. Every function of the
  printed history is such a client (`PrintingClient`): it may match structure,
  compare data with `==`, count and collect results, print sealed values as
  `(Sealed NICK)`, and send back what it received.
* `PartialBijection`: the client may also compare handles by identity: `==` on
  sealed values, spaces that store and remove them by identity, and aliasing
  (`IdentityClient`).

**Theorem** (`Bisim.indistinguishable`). Two implementations related by a
bisimulation whose handle relations lie in a class closed under converse are
indistinguishable by every client parametric for that class.

**What each excluded observer breaks.**

* Identity and aliasing (`Controls.identity_distinguishes`): a caching module
  and a fresh-sealing module are indistinguishable without identity
  (`Controls.cache_fresh_indistinguishable`) and distinguished with it.
* Handle numbers in printed output (`Controls.handleNumber_distinguishes`): two
  modules that differ only in where their handle counter starts are
  indistinguishable by identity clients (`Controls.countFrom_indistinguishable`)
  and distinguished by printing the number.
* Result order (`Controls.ordered_runtime_distinguishes`): two modules that
  return the same multiset in different orders are the same `Impl`; a runtime
  that delivered results in the module's own order would distinguish them.

Contents, costs, reflection and foreign functions are not channels of an `Impl`
at all; `Seal.Abstraction` shows, on sealed modules, what each of them breaks.

**Sound, not complete** (`DelayedChoice`). Unlike Sumii and Pierce's
bisimulation for deterministic dynamic sealing, this one is not complete: two
modules that return two alike sealed values and answer one question are
indistinguishable by every identity client (`DelayedChoice.indistinguishable`),
yet no bisimulation relates them (`DelayedChoice.no_bisim`). Which value matches
which depends on the client's later question, and unordered delivery lets the
runtime choose late.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal

/-- A value as a client receives it. A sealed leaf shows a public nickname and
an opaque handle; its content is not part of the value. -/
inductive Shown where
  | sym (name : String)
  | num (value : Int)
  | nil
  | cons (head tail : Shown)
  | boxed (nick : String) (handle : Nat)
  deriving DecidableEq, Repr

namespace Shown

/-- The handles in a value, left to right. -/
def handles : Shown → List Nat
  | .sym _ => []
  | .num _ => []
  | .nil => []
  | .cons a b => a.handles ++ b.handles
  | .boxed _ h => [h]

/-- The printed form: a sealed value prints as `(Sealed NICK)`, with no handle
and no content. -/
def erase : Shown → Shown
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons a b => .cons a.erase b.erase
  | .boxed nick _ => .boxed nick 0

/-- The subterm at a path (`false` = head, `true` = tail). -/
def at? : Shown → List Bool → Option Shown
  | v, [] => some v
  | .cons a _, false :: p => a.at? p
  | .cons _ b, true :: p => b.at? p
  | _, _ :: _ => none

theorem at?_nil (v : Shown) : v.at? [] = some v := by
  cases v <;> rfl

/-- Two values with the same structure and data, whose handles are related by
`R`. -/
inductive Rel (R : Nat → Nat → Prop) : Shown → Shown → Prop
  | sym (name : String) : Rel R (.sym name) (.sym name)
  | num (value : Int) : Rel R (.num value) (.num value)
  | nil : Rel R .nil .nil
  | cons {a₁ b₁ a₂ b₂ : Shown} : Rel R a₁ a₂ → Rel R b₁ b₂ → Rel R (.cons a₁ b₁) (.cons a₂ b₂)
  | boxed (nick : String) {h₁ h₂ : Nat} : R h₁ h₂ → Rel R (.boxed nick h₁) (.boxed nick h₂)

theorem Rel.mono {R R' : Nat → Nat → Prop} (grow : ∀ a b, R a b → R' a b) {x y : Shown}
    (rel : Rel R x y) : Rel R' x y := by
  induction rel with
  | sym name => exact .sym name
  | num value => exact .num value
  | nil => exact .nil
  | cons _ _ ihA ihB => exact .cons ihA ihB
  | boxed nick related => exact .boxed nick (grow _ _ related)

theorem Rel.sym_eq {R : Nat → Nat → Prop} {a b : String} (rel : Rel R (.sym a) (.sym b)) : a = b := by
  cases rel
  rfl

theorem Rel.symm {R : Nat → Nat → Prop} {x y : Shown} (rel : Rel R x y) :
    Rel (fun a b => R b a) y x := by
  induction rel with
  | sym name => exact .sym name
  | num value => exact .num value
  | nil => exact .nil
  | cons _ _ ihA ihB => exact .cons ihA ihB
  | boxed nick related => exact .boxed nick related

theorem Rel.erase_eq {R : Nat → Nat → Prop} {x y : Shown} (rel : Rel R x y) :
    x.erase = y.erase := by
  induction rel with
  | sym name => rfl
  | num value => rfl
  | nil => rfl
  | cons _ _ ihA ihB => simp [erase, ihA, ihB]
  | boxed nick related => rfl

theorem Rel.handles {R : Nat → Nat → Prop} {x y : Shown} (rel : Rel R x y) :
    List.Forall₂ R x.handles y.handles := by
  induction rel with
  | sym name => exact .nil
  | num value => exact .nil
  | nil => exact .nil
  | cons _ _ ihA ihB => exact List.rel_append ihA ihB
  | boxed nick related => exact .cons related .nil

/-- A value without handles is related only to itself, by every relation. -/
theorem Rel.eq_of_plain {R : Nat → Nat → Prop} {x y : Shown} (rel : Rel R x y)
    (plain : x.handles = []) : y = x := by
  induction rel with
  | sym name => rfl
  | num value => rfl
  | nil => rfl
  | cons _ _ ihA ihB =>
      simp only [Shown.handles, List.append_eq_nil_iff] at plain
      rw [ihA plain.1, ihB plain.2]
  | boxed nick related => simp [Shown.handles] at plain

theorem Rel.refl_of_plain (R : Nat → Nat → Prop) {x : Shown} (plain : x.handles = []) :
    Rel R x x := by
  induction x with
  | sym name => exact .sym name
  | num value => exact .num value
  | nil => exact .nil
  | cons a b ihA ihB =>
      simp only [Shown.handles, List.append_eq_nil_iff] at plain
      exact .cons (ihA plain.1) (ihB plain.2)
  | boxed nick h => simp [Shown.handles] at plain

theorem Rel.at? {R : Nat → Nat → Prop} : ∀ (path : List Bool) {x y : Shown}, Rel R x y →
    Option.Rel (Rel R) (x.at? path) (y.at? path)
  | [], x, y, rel => by rw [at?_nil, at?_nil]; exact .some rel
  | false :: path, _, _, rel => by
      cases rel with
      | cons relA _ => exact Rel.at? path relA
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | boxed => exact .none
  | true :: path, _, _, rel => by
      cases rel with
      | cons _ relB => exact Rel.at? path relB
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | boxed => exact .none

end Shown

/-- What a client has received: one list per call, in the order delivered. -/
abbrev History := List (List Shown)

/-- Two histories that agree except for handles related by `R`. -/
def HistRel (R : Nat → Nat → Prop) (h₁ h₂ : History) : Prop :=
  List.Forall₂ (List.Forall₂ (Shown.Rel R)) h₁ h₂

theorem HistRel.mono {R R' : Nat → Nat → Prop} (grow : ∀ a b, R a b → R' a b) {h₁ h₂ : History}
    (rel : HistRel R h₁ h₂) : HistRel R' h₁ h₂ :=
  List.Forall₂.imp (fun _ _ round => List.Forall₂.imp (fun _ _ value => value.mono grow) round) rel

theorem HistRel.snoc {R : Nat → Nat → Prop} {h₁ h₂ : History} {d₁ d₂ : List Shown}
    (rel : HistRel R h₁ h₂) (round : List.Forall₂ (Shown.Rel R) d₁ d₂) :
    HistRel R (h₁ ++ [d₁]) (h₂ ++ [d₂]) :=
  List.rel_append rel (.cons round .nil)

/-- A module: its private state, and the multiset of values each request
returns. -/
structure Impl where
  State : Type
  init : State
  call : State → Shown → Multiset Shown × State

/-- A client: the next request, or none to stop, and the final verdict. -/
structure Observer where
  next : History → Option Shown
  verdict : History → Bool

/-- A client for which handles are opaque up to the relations of a class. -/
def Observer.Parametric (Adm : (Nat → Nat → Prop) → Prop) (o : Observer) : Prop :=
  ∀ R, Adm R → ∀ h₁ h₂, HistRel R h₁ h₂ →
    Option.Rel (Shown.Rel R) (o.next h₁) (o.next h₂) ∧ o.verdict h₁ = o.verdict h₂

/-- Every verdict a client can reach within `fuel` calls, over every order in
which the runtime may deliver each multiset of results. -/
def outcomes (o : Observer) (I : Impl) : Nat → I.State → History → Set Bool
  | 0, _, h => {o.verdict h}
  | fuel + 1, s, h =>
      match o.next h with
      | none => {o.verdict h}
      | some q => {b | ∃ delivered : List Shown, (delivered : Multiset Shown) = (I.call s q).1 ∧
          b ∈ outcomes o I fuel (I.call s q).2 (h ++ [delivered])}

/-- No client of the class tells the two modules apart, with any fuel. -/
def Indistinguishable (Adm : (Nat → Nat → Prop) → Prop) (I₁ I₂ : Impl) : Prop :=
  ∀ o : Observer, o.Parametric Adm → ∀ fuel, outcomes o I₁ fuel I₁.init [] = outcomes o I₂ fuel I₂.init []

theorem outcomes_stop {o : Observer} {I : Impl} {fuel : Nat} {s : I.State} {h : History}
    (stop : o.next h = none) : outcomes o I (fuel + 1) s h = {o.verdict h} := by
  simp only [outcomes, stop]

theorem mem_outcomes_ask {o : Observer} {I : Impl} {fuel : Nat} {s : I.State} {h : History}
    {q : Shown} (ask : o.next h = some q) {b : Bool} :
    b ∈ outcomes o I (fuel + 1) s h ↔ ∃ delivered : List Shown,
      (delivered : Multiset Shown) = (I.call s q).1 ∧
        b ∈ outcomes o I fuel (I.call s q).2 (h ++ [delivered]) := by
  simp only [outcomes, ask]
  rfl

/-- A call that returns one value is delivered in one way. -/
theorem outcomes_single {o : Observer} {I : Impl} {fuel : Nat} {s : I.State} {h : History}
    {q x : Shown} (ask : o.next h = some q) (single : (I.call s q).1 = {x}) :
    outcomes o I (fuel + 1) s h = outcomes o I fuel (I.call s q).2 (h ++ [[x]]) := by
  ext b
  rw [mem_outcomes_ask ask, single]
  constructor
  · rintro ⟨d, hd, mem⟩
    rw [Multiset.coe_eq_singleton] at hd
    subst hd
    exact mem
  · intro mem
    exact ⟨[x], rfl, mem⟩

theorem outcomes_single_eq {o : Observer} {I : Impl} {fuel : Nat} {s : I.State} {h : History}
    {q x : Shown} {c : Set Bool} (ask : o.next h = some q) (single : (I.call s q).1 = {x})
    (rest : outcomes o I fuel (I.call s q).2 (h ++ [[x]]) = c) :
    outcomes o I (fuel + 1) s h = c :=
  (outcomes_single ask single).trans rest

theorem outcomes_stop_eq {o : Observer} {I : Impl} {fuel : Nat} {s : I.State} {h : History}
    {c : Set Bool} (stop : o.next h = none) (rest : {o.verdict h} = c) :
    outcomes o I (fuel + 1) s h = c :=
  (outcomes_stop stop).trans rest

/-- Clients that cannot compare handles. -/
def AnyRelation (_ : Nat → Nat → Prop) : Prop := True

/-- Clients that compare handles by identity: the relation relates each handle
to at most one handle on each side. -/
structure PartialBijection (R : Nat → Nat → Prop) : Prop where
  functional : ∀ a b b', R a b → R a b' → b = b'
  injective : ∀ a a' b, R a b → R a' b → a = a'

theorem PartialBijection.symm {R : Nat → Nat → Prop} (bij : PartialBijection R) :
    PartialBijection (fun a b => R b a) :=
  ⟨fun a b b' r r' => bij.injective b b' a r r', fun a a' b r r' => bij.functional b a a' r r'⟩

/-- A bisimulation: related states with a handle relation of the class answer
related requests with related multisets, under a relation that extends the old
one. -/
structure Bisim (Adm : (Nat → Nat → Prop) → Prop) (I₁ I₂ : Impl) where
  rel : I₁.State → I₂.State → (Nat → Nat → Prop) → Prop
  adm : ∀ s₁ s₂ R, rel s₁ s₂ R → Adm R
  start : ∃ R, rel I₁.init I₂.init R
  step : ∀ s₁ s₂ R q₁ q₂, rel s₁ s₂ R → Shown.Rel R q₁ q₂ →
    ∃ R', (∀ a b, R a b → R' a b) ∧ rel (I₁.call s₁ q₁).2 (I₂.call s₂ q₂).2 R' ∧
      Multiset.Rel (Shown.Rel R') (I₁.call s₁ q₁).1 (I₂.call s₂ q₂).1

/-- A delivery order of one side gives a related delivery order of the other. -/
theorem exists_related_delivery {r : Shown → Shown → Prop} :
    ∀ {l₁ : List Shown} {m₂ : Multiset Shown}, Multiset.Rel r (l₁ : Multiset Shown) m₂ →
      ∃ l₂ : List Shown, (l₂ : Multiset Shown) = m₂ ∧ List.Forall₂ r l₁ l₂
  | [], m₂, rel => ⟨[], (Multiset.rel_zero_left.mp rel).symm, .nil⟩
  | a :: l, m₂, rel => by
      rw [← Multiset.cons_coe] at rel
      obtain ⟨b, bs, hab, hrest, rfl⟩ := Multiset.rel_cons_left.mp rel
      obtain ⟨l₂, hl₂, hf⟩ := exists_related_delivery hrest
      exact ⟨b :: l₂, by rw [← Multiset.cons_coe, hl₂], .cons hab hf⟩

theorem Bisim.transfer {Adm : (Nat → Nat → Prop) → Prop} {I₁ I₂ : Impl} (B : Bisim Adm I₁ I₂)
    {o : Observer} (param : o.Parametric Adm) :
    ∀ (fuel : Nat) {s₁ : I₁.State} {s₂ : I₂.State} {h₁ h₂ : History} {R : Nat → Nat → Prop},
      B.rel s₁ s₂ R → HistRel R h₁ h₂ → outcomes o I₁ fuel s₁ h₁ ⊆ outcomes o I₂ fuel s₂ h₂
  | 0, s₁, s₂, h₁, h₂, R, rel, hist => by
      have same := (param R (B.adm _ _ _ rel) h₁ h₂ hist).2
      simp [outcomes, same]
  | fuel + 1, s₁, s₂, h₁, h₂, R, rel, hist => by
      obtain ⟨nextRel, same⟩ := param R (B.adm _ _ _ rel) h₁ h₂ hist
      simp only [outcomes]
      generalize o.next h₁ = n₁ at nextRel ⊢
      generalize o.next h₂ = n₂ at nextRel ⊢
      cases nextRel with
      | none => simp [same]
      | some qrel =>
          rename_i q₁ q₂
          obtain ⟨R', grow, rel', resp⟩ := B.step _ _ _ _ _ rel qrel
          rintro b ⟨d₁, hd₁, mem⟩
          rw [← hd₁] at resp
          obtain ⟨d₂, hd₂, fd⟩ := exists_related_delivery resp
          exact ⟨d₂, hd₂, Bisim.transfer B param fuel rel' ((hist.mono grow).snoc fd) mem⟩

/-- The converse bisimulation. -/
def Bisim.symm {Adm : (Nat → Nat → Prop) → Prop}
    (closed : ∀ R, Adm R → Adm (fun a b => R b a)) {I₁ I₂ : Impl} (B : Bisim Adm I₁ I₂) :
    Bisim Adm I₂ I₁ where
  rel s₂ s₁ R := B.rel s₁ s₂ (fun a b => R b a)
  adm s₂ s₁ R rel := closed _ (B.adm _ _ _ rel)
  start := by
    obtain ⟨R, rel⟩ := B.start
    exact ⟨fun a b => R b a, rel⟩
  step s₂ s₁ R q₂ q₁ rel qrel := by
    obtain ⟨R', grow, rel', resp⟩ := B.step s₁ s₂ (fun a b => R b a) q₁ q₂ rel qrel.symm
    refine ⟨fun a b => R' b a, fun a b r => grow b a r, rel', ?_⟩
    exact (Multiset.rel_flip.mpr resp).mono fun _ _ _ _ value => value.symm

/-- **Bisimilar modules are indistinguishable** by every client parametric for
the class of their handle relations. -/
theorem Bisim.indistinguishable {Adm : (Nat → Nat → Prop) → Prop}
    (closed : ∀ R, Adm R → Adm (fun a b => R b a)) {I₁ I₂ : Impl} (B : Bisim Adm I₁ I₂) :
    Indistinguishable Adm I₁ I₂ := by
  intro o param fuel
  obtain ⟨R, rel⟩ := B.start
  apply Set.Subset.antisymm
  · exact B.transfer param fuel rel .nil
  · exact (B.symm closed).transfer param fuel (R := fun a b => R b a) rel .nil

theorem anyRelation_closed : ∀ R, AnyRelation R → AnyRelation (fun a b => R b a) :=
  fun _ _ => trivial

theorem partialBijection_closed :
    ∀ R, PartialBijection R → PartialBijection (fun a b => R b a) :=
  fun _ bij => bij.symm

/-! ## The allowed observers, concretely -/

/-- A request a client builds: data it writes (without handles), and parts of
values it received, taken by round, position and path. -/
inductive Template where
  | lit (v : Shown)
  | pick (round index : Nat) (path : List Bool)
  | cons (head tail : Template)

/-- The request a template denotes in a history, if every part exists. -/
def Template.fill (h : History) : Template → Option Shown
  | .lit v => if v.handles = [] then some v else none
  | .pick r i p => ((h[r]?).bind fun round => round[i]?).bind fun v => v.at? p
  | .cons a b =>
      match a.fill h, b.fill h with
      | some x, some y => some (.cons x y)
      | _, _ => none

theorem optionRel_bind {α β γ δ : Type} {r : α → β → Prop} {s : γ → δ → Prop}
    {o₁ : Option α} {o₂ : Option β} (rel : Option.Rel r o₁ o₂) {f : α → Option γ}
    {g : β → Option δ} (fg : ∀ a b, r a b → Option.Rel s (f a) (g b)) :
    Option.Rel s (o₁.bind f) (o₂.bind g) := by
  cases rel with
  | none => exact .none
  | some related => exact fg _ _ related

theorem forall₂_getElem? {α β : Type} {r : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ r l₁ l₂ → ∀ i : Nat, Option.Rel r l₁[i]? l₂[i]?
  | [], [], .nil, _ => .none
  | _ :: _, _ :: _, .cons head _, 0 => .some head
  | _ :: _, _ :: _, .cons _ tail, i + 1 => by simpa using forall₂_getElem? tail i

/-- Filling a template in related histories gives related requests. -/
theorem Template.fill_rel {R : Nat → Nat → Prop} {h₁ h₂ : History} (hist : HistRel R h₁ h₂) :
    ∀ t : Template, Option.Rel (Shown.Rel R) (t.fill h₁) (t.fill h₂)
  | .lit v => by
      unfold Template.fill
      split_ifs with plain
      · exact .some (Shown.Rel.refl_of_plain R plain)
      · exact .none
  | .pick r i p => by
      unfold Template.fill
      refine optionRel_bind (s := Shown.Rel R)
        (optionRel_bind (s := Shown.Rel R) (forall₂_getElem? hist r) ?_) ?_
      · intro round₁ round₂ rounds
        exact forall₂_getElem? rounds i
      · intro v₁ v₂ values
        exact Shown.Rel.at? p values
  | .cons a b => by
      have ra := Template.fill_rel hist a
      have rb := Template.fill_rel hist b
      unfold Template.fill
      generalize a.fill h₁ = x₁ at ra ⊢
      generalize a.fill h₂ = x₂ at ra ⊢
      generalize b.fill h₁ = y₁ at rb ⊢
      generalize b.fill h₂ = y₂ at rb ⊢
      cases ra with
      | none => exact .none
      | some relA =>
          cases rb with
          | none => exact .none
          | some relB => exact .some (.cons relA relB)

/-- The printed history: every sealed value as `(Sealed NICK)`. -/
def History.printed (h : History) : List (List Shown) := h.map (List.map Shown.erase)

theorem HistRel.printed_eq {R : Nat → Nat → Prop} {h₁ h₂ : History} (rel : HistRel R h₁ h₂) :
    h₁.printed = h₂.printed := by
  unfold HistRel at rel
  induction rel with
  | nil => rfl
  | cons round _ ih =>
      simp only [History.printed, List.map_cons] at ih ⊢
      rw [ih]
      congr 1
      induction round with
      | nil => rfl
      | cons value _ ihRound => simp [value.erase_eq, ihRound]

/-- A client that sees only the printed history. Every MeTTa operation that does
not look at a sealed value's identity or content is of this kind: `match` on
structure, `==` on data, `collapse`, `superpose`, counting, printing, and passing
values back. -/
structure PrintingClient where
  strategy : List (List Shown) → Option Template
  verdict : List (List Shown) → Bool

def PrintingClient.observer (c : PrintingClient) : Observer where
  next h := (c.strategy h.printed).bind fun t => t.fill h
  verdict h := c.verdict h.printed

theorem PrintingClient.parametric (c : PrintingClient) : c.observer.Parametric AnyRelation := by
  intro R _ h₁ h₂ hist
  have same := hist.printed_eq
  refine ⟨?_, by simp [PrintingClient.observer, same]⟩
  simp only [PrintingClient.observer, same]
  cases c.strategy h₂.printed with
  | none => exact .none
  | some t => exact t.fill_rel hist

/-- The first position of a handle in a list. -/
def firstIndex (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else firstIndex x ys + 1

/-- Which handle occurrences are the same handle: each occurrence replaced by
the first position of its handle. -/
def aliasPattern (l : List Nat) : List Nat := l.map fun x => firstIndex x l

theorem firstIndex_rel {R : Nat → Nat → Prop} (bij : PartialBijection R) {x y : Nat} (xy : R x y) :
    ∀ {l₁ l₂ : List Nat}, List.Forall₂ R l₁ l₂ → firstIndex x l₁ = firstIndex y l₂
  | [], [], .nil => rfl
  | a :: _, b :: _, .cons ab tail => by
      simp only [firstIndex]
      by_cases ax : a = x
      · subst ax
        rw [if_pos rfl, if_pos (bij.functional _ _ _ ab xy)]
      · have by' : b ≠ y := by
          intro same
          have xb : R x b := same ▸ xy
          exact ax (bij.injective _ _ _ ab xb)
        rw [if_neg ax, if_neg by', firstIndex_rel bij xy tail]

theorem map_eq_of_forall₂ {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (pointwise : ∀ x y, R x y → f x = g y) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → xs.map f = ys.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons xy tail => by
      simp only [List.map_cons, pointwise _ _ xy, map_eq_of_forall₂ pointwise tail]

theorem aliasPattern_rel {R : Nat → Nat → Prop} (bij : PartialBijection R) {l₁ l₂ : List Nat}
    (rel : List.Forall₂ R l₁ l₂) : aliasPattern l₁ = aliasPattern l₂ := by
  unfold aliasPattern
  exact map_eq_of_forall₂ (f := fun x => firstIndex x l₁) (g := fun x => firstIndex x l₂)
    (fun _ _ xy => firstIndex_rel bij xy rel) rel

/-- All handles a client has received, in order. -/
def History.handles (h : History) : List Nat := h.flatten.flatMap Shown.handles

theorem forall₂_flatten {α β : Type} {r : α → β → Prop} :
    ∀ {L₁ : List (List α)} {L₂ : List (List β)}, List.Forall₂ (List.Forall₂ r) L₁ L₂ →
      List.Forall₂ r L₁.flatten L₂.flatten
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => by
      simpa [List.flatten_cons] using List.rel_append head (forall₂_flatten tail)

theorem forall₂_flatMap_handles {R : Nat → Nat → Prop} :
    ∀ {l₁ l₂ : List Shown}, List.Forall₂ (Shown.Rel R) l₁ l₂ →
      List.Forall₂ R (l₁.flatMap Shown.handles) (l₂.flatMap Shown.handles)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => by
      simpa [List.flatMap_cons] using List.rel_append head.handles (forall₂_flatMap_handles tail)

theorem HistRel.handles {R : Nat → Nat → Prop} {h₁ h₂ : History} (rel : HistRel R h₁ h₂) :
    List.Forall₂ R h₁.handles h₂.handles :=
  forall₂_flatMap_handles (forall₂_flatten rel)

/-- A client that also sees which received sealed values are the same value:
`==` on sealed values, and spaces that store and remove them by identity. -/
structure IdentityClient where
  strategy : List (List Shown) × List Nat → Option Template
  verdict : List (List Shown) × List Nat → Bool

def IdentityClient.observer (c : IdentityClient) : Observer where
  next h := (c.strategy (h.printed, aliasPattern h.handles)).bind fun t => t.fill h
  verdict h := c.verdict (h.printed, aliasPattern h.handles)

theorem IdentityClient.parametric (c : IdentityClient) :
    c.observer.Parametric PartialBijection := by
  intro R bij h₁ h₂ hist
  have same : (h₁.printed, aliasPattern h₁.handles) = (h₂.printed, aliasPattern h₂.handles) := by
    rw [hist.printed_eq, aliasPattern_rel bij hist.handles]
  refine ⟨?_, by simp only [IdentityClient.observer, same]⟩
  simp only [IdentityClient.observer, same]
  cases c.strategy (h₂.printed, aliasPattern h₂.handles) with
  | none => exact .none
  | some t => exact t.fill_rel hist

/-! ## Controls: what each excluded observer breaks -/

namespace Controls

/-- Hands out the same sealed value on every call. -/
abbrev cacheImpl : Impl where
  State := Unit
  init := ()
  call s _ := ({.boxed "box" 0}, s)

/-- Hands out a new sealed value on every call. -/
abbrev countFrom (start : Nat) : Impl where
  State := Nat
  init := start
  call n _ := ({.boxed "box" n}, n + 1)

/-- Without identity, a cache and fresh sealing are the same: the one cached
handle is related to every fresh one. -/
def cacheFresh : Bisim AnyRelation cacheImpl (countFrom 0) where
  rel _ n R := ∀ a b, R a b ↔ a = 0 ∧ b < n
  adm _ _ _ _ := trivial
  start := ⟨fun _ _ => False, by intro a b; simp⟩
  step _ n R _ _ rel _ := by
    refine ⟨fun a b => a = 0 ∧ b < n + 1, ?_, ?_, ?_⟩
    · intro a b r
      obtain ⟨ha, hb⟩ := (rel a b).mp r
      exact ⟨ha, Nat.lt_succ_of_lt hb⟩
    · intro a b
      exact Iff.rfl
    · exact Multiset.Rel.cons (Shown.Rel.boxed "box" ⟨rfl, Nat.lt_succ_self n⟩) Multiset.Rel.zero

theorem cache_fresh_indistinguishable : Indistinguishable AnyRelation cacheImpl (countFrom 0) :=
  cacheFresh.indistinguishable anyRelation_closed

/-- Asks twice, then says whether the two answers are the same sealed value. -/
def sameTwice : IdentityClient where
  strategy view := if view.1.length < 2 then some (.lit (.sym "get")) else none
  verdict view := decide (view.2 = [0, 0])

theorem sameTwice_cache : outcomes sameTwice.observer cacheImpl 3 () [] = {true} := by
  rw [outcomes_single (o := sameTwice.observer) (I := cacheImpl) (h := []) (q := .sym "get")
      (x := .boxed "box" 0) rfl rfl,
    outcomes_single (o := sameTwice.observer) (I := cacheImpl) (h := [] ++ [[Shown.boxed "box" 0]])
      (q := .sym "get") (x := .boxed "box" 0) rfl rfl,
    outcomes_stop rfl]
  rfl

theorem sameTwice_fresh : outcomes sameTwice.observer (countFrom 0) 3 0 [] = {false} := by
  rw [outcomes_single (o := sameTwice.observer) (I := countFrom 0) (h := []) (q := .sym "get")
      (x := .boxed "box" 0) rfl rfl,
    outcomes_single (o := sameTwice.observer) (I := countFrom 0) (h := [] ++ [[Shown.boxed "box" 0]])
      (q := .sym "get") (x := .boxed "box" 1) rfl rfl,
    outcomes_stop rfl]
  rfl

/-- **Identity distinguishes** the cache from fresh sealing, so the two are not
indistinguishable once clients may compare sealed values. -/
theorem identity_distinguishes : ¬ Indistinguishable PartialBijection cacheImpl (countFrom 0) := by
  intro same
  have := same sameTwice.observer sameTwice.parametric 3
  change outcomes sameTwice.observer cacheImpl 3 () [] =
    outcomes sameTwice.observer (countFrom 0) 3 0 [] at this
  rw [sameTwice_cache, sameTwice_fresh] at this
  exact Bool.noConfusion (Set.singleton_eq_singleton_iff.mp this)

/-- With identity allowed, where a handle counter starts does not matter: the
handles are related by a shift. -/
def shifted : Bisim PartialBijection (countFrom 0) (countFrom 1) where
  rel n m R := m = n + 1 ∧ ∀ a b, R a b ↔ b = a + 1 ∧ a < n
  adm _ _ R rel := by
    obtain ⟨_, iff⟩ := rel
    refine ⟨fun a b b' r r' => ?_, fun a a' b r r' => ?_⟩
    · rw [((iff a b).mp r).1, ((iff a b').mp r').1]
    · have e := ((iff a b).mp r).1
      have e' := ((iff a' b).mp r').1
      omega
  start := ⟨fun _ _ => False, rfl, by intro a b; simp⟩
  step n m R _ _ rel _ := by
    obtain ⟨rfl, iff⟩ := rel
    refine ⟨fun a b => b = a + 1 ∧ a < n + 1, ?_, ⟨rfl, fun a b => Iff.rfl⟩, ?_⟩
    · intro a b r
      obtain ⟨hb, ha⟩ := (iff a b).mp r
      exact ⟨hb, Nat.lt_succ_of_lt ha⟩
    · exact Multiset.Rel.cons (Shown.Rel.boxed "box" ⟨rfl, Nat.lt_succ_self n⟩) Multiset.Rel.zero

theorem countFrom_indistinguishable :
    Indistinguishable PartialBijection (countFrom 0) (countFrom 1) :=
  shifted.indistinguishable partialBijection_closed

/-- Prints the number of the first handle it receives, as a runtime that prints
handle identifiers lets a client do. -/
def printsHandleNumber : Observer where
  next h := if h.length < 1 then some (.sym "get") else none
  verdict h := decide (h.handles.head? = some 0)

theorem printsHandleNumber_from (start : Nat) :
    outcomes printsHandleNumber (countFrom start) 2 start [] = {decide (start = 0)} := by
  rw [outcomes_single (o := printsHandleNumber) (I := countFrom start) (h := []) (q := .sym "get")
      (x := .boxed "box" start) rfl rfl,
    outcomes_stop rfl]
  simp [printsHandleNumber, History.handles, Shown.handles]

/-- **Handle numbers distinguish** modules that no identity client can, so
printing a handle number is not an identity observation. -/
theorem printsHandleNumber_not_parametric : ¬ printsHandleNumber.Parametric PartialBijection := by
  intro param
  have same := countFrom_indistinguishable printsHandleNumber param 2
  change outcomes printsHandleNumber (countFrom 0) 2 0 [] =
    outcomes printsHandleNumber (countFrom 1) 2 1 [] at same
  rw [printsHandleNumber_from, printsHandleNumber_from] at same
  simp at same

/-- **Result order.** Two modules that return the same two answers in different
orders. As multisets they are equal, so they are the same module. -/
def answersAB : List Shown := [.sym "a", .sym "b"]
def answersBA : List Shown := [.sym "b", .sym "a"]

theorem same_multiset : (answersAB : Multiset Shown) = answersBA :=
  Multiset.coe_eq_coe.mpr (List.Perm.swap (Shown.sym "b") (Shown.sym "a") [])

/-- A runtime that delivered results in the module's own order would let a
client tell them apart by reading the first one. -/
def firstAnswerIsA (delivered : List Shown) : Bool := decide (delivered.head? = some (.sym "a"))

theorem ordered_runtime_distinguishes :
    firstAnswerIsA answersAB = true ∧ firstAnswerIsA answersBA = false := by decide

/-- Reads the first answer of its one call. -/
def readsFirst : Observer where
  next h := if h.length < 1 then some (.sym "ask") else none
  verdict h := decide ((h.head?.bind List.head?) = some (.sym "a"))

abbrev returns (answers : List Shown) : Impl where
  State := Unit
  init := ()
  call s _ := (answers, s)

/-- Under MeTTa's unordered delivery, the client that reads the first answer
reaches every verdict with either module: order is not public behaviour. -/
theorem unordered_outcomes (answers : List Shown) (which : answers = answersAB ∨ answers = answersBA) :
    outcomes readsFirst (returns answers) 2 () [] = Set.univ := by
  have both : (answersAB : Multiset Shown) = answers ∧ (answersBA : Multiset Shown) = answers := by
    rcases which with rfl | rfl
    · exact ⟨rfl, same_multiset.symm⟩
    · exact ⟨same_multiset, rfl⟩
  have ask : readsFirst.next [] = some (.sym "ask") := rfl
  ext b
  simp only [Set.mem_univ, iff_true]
  rw [mem_outcomes_ask ask]
  cases b
  · refine ⟨answersBA, both.2, ?_⟩
    rw [outcomes_stop rfl]
    exact Set.mem_singleton_iff.mpr rfl
  · refine ⟨answersAB, both.1, ?_⟩
    rw [outcomes_stop rfl]
    exact Set.mem_singleton_iff.mpr rfl

end Controls

/-! ## The bisimulation is not complete under unordered delivery

Sumii and Pierce's bisimulation for dynamic sealing is complete for contextual
equivalence. Under MeTTa's unordered results it is not: when a call returns two
sealed values that print alike, the runtime may deliver them in either order,
and which value of one module matches which value of the other may depend on the
client's next question. A client asks only one question per run; a bisimulation
must answer every question with one matching. Two modules show it
(`DelayedChoice.indistinguishable`, `DelayedChoice.no_bisim`), as `a.(b + c)` and
`a.b + a.c` show it for may-testing in process calculi. -/

namespace DelayedChoice

/-- Where a two-box module is: before `(get)`, after it, after one question. -/
inductive Phase where
  | start
  | waiting
  | done
  deriving DecidableEq

def getRequest : Shown := .cons (.sym "get") .nil

/-- A question `(k (Sealed n h))` with `k` one of `q1` and `q2`, about one of
the two issued handles. -/
def valid : Shown → Option (String × Nat)
  | .cons (.sym k) (.cons (.boxed nick h) .nil) =>
      if nick = "n" ∧ (k = "q1" ∨ k = "q2") ∧ h < 2 then some (k, h) else none
  | _ => none

/-- `(get)` returns two sealed values `(Sealed n)`; one question about one of
them is answered from the table; then nothing more is answered. -/
abbrev twoBoxes (answer : String → Nat → String) : Impl where
  State := Phase
  init := .start
  call s q :=
    match s with
    | .start => if q = getRequest then ({.boxed "n" 0, .boxed "n" 1}, .waiting) else (0, .start)
    | .waiting =>
        match valid q with
        | some (k, h) => ({.sym (answer k h)}, .done)
        | none => (0, .waiting)
    | .done => (0, .done)

/-- Exchange the two handles, or not. -/
def flip (swap : Bool) (h : Nat) : Nat := if swap then 1 - h else h

theorem flip_lt {swap : Bool} {h : Nat} (lt : h < 2) : flip swap h < 2 := by
  unfold flip; split <;> omega

theorem flip_flip {swap : Bool} {h : Nat} (lt : h < 2) : flip swap (flip swap h) = h := by
  unfold flip; split <;> omega

/-- The handle relation of a delivery order. -/
def graph (swap : Bool) (a b : Nat) : Prop := a < 2 ∧ b = flip swap a

theorem graph_bijection (swap : Bool) : PartialBijection (graph swap) := by
  refine ⟨fun a b b' r r' => r.2.trans r'.2.symm, fun a a' b r r' => ?_⟩
  have e := r.2.symm.trans r'.2
  have := congrArg (flip swap) e
  rwa [flip_flip r.1, flip_flip r'.1] at this

theorem valid_rel {swap : Bool} {q₁ q₂ : Shown} (rel : Shown.Rel (graph swap) q₁ q₂) :
    valid q₂ = (valid q₁).map fun p => (p.1, flip swap p.2) := by
  rcases rel with _ | _ | _ | ⟨ra, rb⟩ | _
  · rfl
  · rfl
  · rfl
  · rcases ra with k | _ | _ | ⟨_, _⟩ | ⟨_, _⟩
    · rcases rb with _ | _ | _ | ⟨rc, re⟩ | _
      · rfl
      · rfl
      · rfl
      · rcases rc with _ | _ | _ | ⟨_, _⟩ | ⟨nick, related⟩
        · rfl
        · rfl
        · rfl
        · rfl
        · rcases re with _ | _ | _ | ⟨_, _⟩ | ⟨_, _⟩
          · rfl
          · rfl
          · obtain ⟨lt, rfl⟩ := related
            simp only [valid, flip_lt lt, lt, and_true]
            split_ifs <;> rfl
          · rfl
          · rfl
      · rfl
    all_goals rfl
  · rfl

/-- The first question a client asks from a history, within `fuel` calls,
when every other request is answered with nothing. -/
def firstQuestion (o : Observer) : Nat → History → Option (String × Nat)
  | 0, _ => none
  | fuel + 1, h =>
      match o.next h with
      | none => none
      | some q =>
          match valid q with
          | some p => some p
          | none => firstQuestion o fuel (h ++ [[]])

theorem valid_lt {q : Shown} {k : String} {h : Nat} (found : valid q = some (k, h)) : h < 2 := by
  unfold valid at found
  split at found
  · split_ifs at found with ok
    cases found
    exact ok.2.2
  · cases found

theorem firstQuestion_lt {o : Observer} :
    ∀ {fuel : Nat} {h : History} {k : String} {hh : Nat},
      firstQuestion o fuel h = some (k, hh) → hh < 2
  | 0, _, _, _, found => by simp [firstQuestion] at found
  | fuel + 1, h, k, hh, found => by
      simp only [firstQuestion] at found
      cases hn : o.next h with
      | none => simp only [hn] at found; cases found
      | some q =>
          simp only [hn] at found
          cases hv : valid q with
          | none =>
              simp only [hv] at found
              exact firstQuestion_lt found
          | some p =>
              simp only [hv] at found
              cases found
              exact valid_lt hv

section Runs

variable {A A' : String → Nat → String} {o : Observer}

theorem delivered_nil {d : List Shown} (hd : (d : Multiset Shown) = 0) : d = [] := by
  simpa using hd

theorem delivered_single {d : List Shown} {x : Shown} (hd : (d : Multiset Shown) = {x}) : d = [x] :=
  Multiset.coe_eq_singleton.mp hd

/-- After the question, nothing more is answered: the outcomes are the same for
histories related by an identity relation. -/
theorem done_phase (param : o.Parametric PartialBijection) :
    ∀ (fuel : Nat) {h₁ h₂ : History} {R : Nat → Nat → Prop}, PartialBijection R →
      HistRel R h₁ h₂ → outcomes o (twoBoxes A) fuel Phase.done h₁ ⊆
        outcomes o (twoBoxes A') fuel Phase.done h₂
  | 0, h₁, h₂, R, bij, hist => by
      simp [outcomes, (param R bij h₁ h₂ hist).2]
  | fuel + 1, h₁, h₂, R, bij, hist => by
      obtain ⟨nextRel, same⟩ := param R bij h₁ h₂ hist
      simp only [outcomes]
      generalize o.next h₁ = n₁ at nextRel ⊢
      generalize o.next h₂ = n₂ at nextRel ⊢
      cases nextRel with
      | none => simp [same]
      | some _ =>
          rintro b ⟨d, hd, mem⟩
          have := delivered_nil hd
          subst this
          exact ⟨[], rfl, done_phase param fuel bij (hist.snoc .nil) mem⟩

/-- While waiting, a run of the first module is matched by a run of the second
whose handles are exchanged as the first question requires. -/
theorem waiting_phase (param : o.Parametric PartialBijection) :
    ∀ (fuel : Nat) {h₁ h₂ : History} (swap : Bool), HistRel (graph swap) h₁ h₂ →
      (∀ k h, firstQuestion o fuel h₁ = some (k, h) → A' k (flip swap h) = A k h) →
      outcomes o (twoBoxes A) fuel Phase.waiting h₁ ⊆ outcomes o (twoBoxes A') fuel Phase.waiting h₂
  | 0, h₁, h₂, swap, hist, _ => by
      simp [outcomes, (param _ (graph_bijection swap) h₁ h₂ hist).2]
  | fuel + 1, h₁, h₂, swap, hist, agree => by
      obtain ⟨nextRel, same⟩ := param _ (graph_bijection swap) h₁ h₂ hist
      have first : ∀ q, o.next h₁ = some q → firstQuestion o (fuel + 1) h₁ =
          match valid q with
          | some p => some p
          | none => firstQuestion o fuel (h₁ ++ [[]]) := by
        intro q ask
        simp only [firstQuestion, ask]
      cases ask₁ : o.next h₁ with
      | none =>
          rw [ask₁] at nextRel
          cases ask₂ : o.next h₂ with
          | none => rw [outcomes_stop ask₁, outcomes_stop ask₂, same]
          | some _ => rw [ask₂] at nextRel; cases nextRel
      | some q₁ =>
          rw [ask₁] at nextRel
          cases ask₂ : o.next h₂ with
          | none => rw [ask₂] at nextRel; cases nextRel
          | some q₂ =>
              rw [ask₂] at nextRel
              cases nextRel with
              | some qrel =>
                  have checked := valid_rel qrel
                  intro b mem
                  rw [mem_outcomes_ask ask₁] at mem
                  rw [mem_outcomes_ask ask₂]
                  obtain ⟨d₁, hd₁, rest⟩ := mem
                  have firstAt := first q₁ ask₁
                  cases question : valid q₁ with
                  | some p =>
                      obtain ⟨k, h⟩ := p
                      simp only [question, Option.map_some] at checked firstAt
                      have answered : A' k (flip swap h) = A k h := agree k h firstAt
                      have call₁ : (twoBoxes A).call Phase.waiting q₁ = ({.sym (A k h)}, Phase.done) := by
                        simp [twoBoxes, question]
                      have call₂ : (twoBoxes A').call Phase.waiting q₂ =
                          ({.sym (A k h)}, Phase.done) := by
                        simp [twoBoxes, checked, answered]
                      rw [call₁] at hd₁ rest
                      rw [call₂]
                      dsimp only at hd₁ rest ⊢
                      have := delivered_single hd₁
                      subst this
                      exact ⟨[.sym (A k h)], rfl, done_phase param fuel (graph_bijection swap)
                        (hist.snoc (.cons (.sym _) .nil)) rest⟩
                  | none =>
                      simp only [question, Option.map_none] at checked firstAt
                      have call₁ : (twoBoxes A).call Phase.waiting q₁ = (0, Phase.waiting) := by
                        simp [twoBoxes, question]
                      have call₂ : (twoBoxes A').call Phase.waiting q₂ = (0, Phase.waiting) := by
                        simp [twoBoxes, checked]
                      rw [call₁] at hd₁ rest
                      rw [call₂]
                      dsimp only at hd₁ rest ⊢
                      have := delivered_nil hd₁
                      subst this
                      refine ⟨[], rfl, waiting_phase param fuel swap (hist.snoc .nil) ?_ rest⟩
                      intro k h later
                      exact agree k h (firstAt.trans later)

/-- Exchange the handles of a sealed value `(Sealed n h)`. -/
def relabel (swap : Bool) : Shown → Shown
  | .boxed nick h => .boxed nick (flip swap h)
  | v => v

theorem relabel_pair (swap : Bool) :
    Multiset.map (relabel swap) {Shown.boxed "n" 0, Shown.boxed "n" 1} =
      {Shown.boxed "n" 0, Shown.boxed "n" 1} := by
  cases swap
  · rfl
  · conv_rhs => rw [Multiset.pair_comm]
    rfl

theorem relabel_rel (swap : Bool) : ∀ d : List Shown,
    (∀ x ∈ d, x = .boxed "n" 0 ∨ x = .boxed "n" 1) →
      List.Forall₂ (Shown.Rel (graph swap)) d (d.map (relabel swap))
  | [], _ => .nil
  | x :: rest, both => by
      refine .cons ?_ (relabel_rel swap rest fun y m => both y (List.mem_cons_of_mem x m))
      rcases both x (List.mem_cons.mpr (Or.inl rfl)) with rfl | rfl
      · exact .boxed "n" ⟨by decide, rfl⟩
      · exact .boxed "n" ⟨by decide, rfl⟩

/-- Before `(get)`, a client's history holds only empty rounds. -/
def Empty (h : History) : Prop := ∀ round ∈ h, round = []

theorem Empty.rel {h : History} (empty : Empty h) (R : Nat → Nat → Prop) : HistRel R h h := by
  induction h with
  | nil => exact .nil
  | cons round rest ih =>
      have here : round = [] := empty round (List.mem_cons.mpr (Or.inl rfl))
      subst here
      exact .cons .nil (ih fun r m => empty r (List.mem_cons_of_mem _ m))

theorem start_phase (param : o.Parametric PartialBijection)
    (columns : ∀ k, ∃ swap : Bool, ∀ h, h < 2 → A' k (flip swap h) = A k h) :
    ∀ (fuel : Nat) {h : History}, Empty h →
      outcomes o (twoBoxes A) fuel Phase.start h ⊆ outcomes o (twoBoxes A') fuel Phase.start h
  | 0, h, _ => fun _ mem => mem
  | fuel + 1, h, empty => by
      intro b mem
      cases ask : o.next h with
      | none =>
          rw [outcomes_stop ask] at mem
          rw [outcomes_stop ask]
          exact mem
      | some q =>
          rw [mem_outcomes_ask ask] at mem
          rw [mem_outcomes_ask ask]
          obtain ⟨d₁, hd₁, rest⟩ := mem
          by_cases isGet : q = getRequest
          · have call₁ : (twoBoxes A).call Phase.start q =
                ({.boxed "n" 0, .boxed "n" 1}, Phase.waiting) := by simp [twoBoxes, isGet]
            have call₂ : (twoBoxes A').call Phase.start q =
                ({.boxed "n" 0, .boxed "n" 1}, Phase.waiting) := by simp [twoBoxes, isGet]
            rw [call₁] at hd₁ rest
            rw [call₂]
            dsimp only at hd₁ rest ⊢
            -- Choose the exchange that the first question needs.
            let swap : Bool :=
              match firstQuestion o fuel (h ++ [d₁]) with
              | some (k, _) => Classical.choose (columns k)
              | none => false
            have both : ∀ x ∈ d₁, x = .boxed "n" 0 ∨ x = .boxed "n" 1 := by
              intro x m
              have : x ∈ ((d₁ : Multiset Shown)) := Multiset.mem_coe.mpr m
              rw [hd₁] at this
              simpa using this
            refine ⟨d₁.map (relabel swap), ?_, ?_⟩
            · rw [← Multiset.map_coe, hd₁, relabel_pair]
            · refine waiting_phase param fuel swap
                ((empty.rel _).snoc (relabel_rel swap d₁ both)) ?_ rest
              intro k hh found
              have chosen : swap = Classical.choose (columns k) := by
                simp only [swap, found]
              have bounded : hh < 2 := firstQuestion_lt found
              rw [chosen]
              exact Classical.choose_spec (columns k) hh bounded
          · have call₁ : (twoBoxes A).call Phase.start q = (0, Phase.start) := by
              simp [twoBoxes, isGet]
            have call₂ : (twoBoxes A').call Phase.start q = (0, Phase.start) := by
              simp [twoBoxes, isGet]
            rw [call₁] at hd₁ rest
            rw [call₂]
            dsimp only at hd₁ rest ⊢
            have := delivered_nil hd₁
            subst this
            refine ⟨[], rfl, start_phase param columns fuel ?_ rest⟩
            intro round m
            rcases List.mem_append.mp m with old | new
            · exact empty round old
            · simpa using new

end Runs

/-- `q1` answers `x` about handle 0 and `w` about handle 1; `q2` answers `y` and
`z`. -/
def answers₁ (k : String) (h : Nat) : String :=
  if k = "q1" then (if h = 0 then "x" else "w") else (if h = 0 then "y" else "z")

/-- The same answers with the column of `q2` exchanged: the value that answers
`x` to `q1` now answers `z` to `q2`. -/
def answers₂ (k : String) (h : Nat) : String :=
  if k = "q1" then (if h = 0 then "x" else "w") else (if h = 0 then "z" else "y")

theorem columns₁₂ : ∀ k, ∃ swap : Bool, ∀ h, h < 2 → answers₂ k (flip swap h) = answers₁ k h := by
  intro k
  by_cases q1 : k = "q1"
  · exact ⟨false, fun h _ => by simp [answers₁, answers₂, flip, q1]⟩
  · refine ⟨true, fun h lt => ?_⟩
    simp only [answers₁, answers₂, flip, q1, if_false, if_true]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp

theorem columns₂₁ : ∀ k, ∃ swap : Bool, ∀ h, h < 2 → answers₁ k (flip swap h) = answers₂ k h := by
  intro k
  by_cases q1 : k = "q1"
  · exact ⟨false, fun h _ => by simp [answers₁, answers₂, flip, q1]⟩
  · refine ⟨true, fun h lt => ?_⟩
    simp only [answers₁, answers₂, flip, q1, if_false, if_true]
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp

/-- **No client that may compare sealed values by identity tells the two
modules apart**, with any fuel. -/
theorem indistinguishable :
    Indistinguishable PartialBijection (twoBoxes answers₁) (twoBoxes answers₂) := by
  intro o param fuel
  apply Set.Subset.antisymm
  · exact start_phase param columns₁₂ fuel (h := []) (fun _ m => by cases m)
  · exact start_phase param columns₂₁ fuel (h := []) (fun _ m => by cases m)

/-- **Yet no bisimulation relates them**, for any class of handle relations. -/
theorem no_bisim {Adm : (Nat → Nat → Prop) → Prop}
    (B : Bisim Adm (twoBoxes answers₁) (twoBoxes answers₂)) : False := by
  obtain ⟨R₀, rel₀⟩ := B.start
  obtain ⟨R₁, -, rel₁, resp⟩ :=
    B.step _ _ R₀ getRequest getRequest rel₀ (Shown.Rel.refl_of_plain R₀ rfl)
  have pair : Multiset.Rel (Shown.Rel R₁) {Shown.boxed "n" 0, Shown.boxed "n" 1}
      {Shown.boxed "n" 0, Shown.boxed "n" 1} := by
    simpa [twoBoxes] using resp
  obtain ⟨y, ymem, yrel⟩ := Multiset.exists_mem_of_rel_of_mem pair (a := Shown.boxed "n" 0) (by simp)
  rcases yrel with _ | _ | _ | _ | @⟨_, _, a, related⟩
  have which : a = 0 ∨ a = 1 := by simpa using ymem
  -- The same state must answer both questions with one matching.
  have answer : ∀ k, (k = "q1" ∨ k = "q2") → answers₂ k a = answers₁ k 0 := by
    intro k isQuestion
    have lt : a < 2 := by rcases which with rfl | rfl <;> decide
    obtain ⟨R₂, -, -, resp₂⟩ := B.step _ _ R₁ (.cons (.sym k) (.cons (.boxed "n" 0) .nil))
      (.cons (.sym k) (.cons (.boxed "n" a) .nil)) rel₁
      (.cons (.sym k) (.cons (.boxed "n" related) .nil))
    have single : Multiset.Rel (Shown.Rel R₂) {Shown.sym (answers₁ k 0)}
        {Shown.sym (answers₂ k a)} := by
      simpa [twoBoxes, valid, isQuestion, lt] using resp₂
    obtain ⟨z, zmem, zrel⟩ :=
      Multiset.exists_mem_of_rel_of_mem single (a := Shown.sym (answers₁ k 0)) (by simp)
    rw [Multiset.mem_singleton] at zmem
    subst zmem
    exact (Shown.Rel.sym_eq zrel).symm
  have first := answer "q1" (Or.inl rfl)
  have second := answer "q2" (Or.inr rfl)
  rcases which with rfl | rfl
  · simp [answers₁, answers₂] at second
  · simp [answers₁, answers₂] at first

end DelayedChoice

end Mettapedia.Languages.MeTTa.Seal

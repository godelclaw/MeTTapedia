import Mathlib.Data.List.Sort

/-!
# Reading a capped relay to its end

A relay answers a filter with at most a cap of events: the newest, ordered by
time and then identifier, as `Filter.select` models. `select_truncates` shows a
reader that asks once misses older mail past the cap. A reader can page back
with `until`, which bounds the time inclusively.

The walk modelled here is the mailbox's. It asks for the newest page, then pages
back with `until` set to the oldest time of the last page. A page that brings
nothing it has not already seen is stuck on that one second, and the walk steps
`until` back past it.

The walk reads to the end of the relay: a walk that stops at a page of mail the
reader already holds assumes mail reaches a relay in the order of its times, and
`created_at` is the sender's clock.

The theorems:
- `walk_complete`: if no second holds more events than a page, the walk sees
  every event of the relay.
- `walk_stopping_misses`: a walk that stops at the first page bringing nothing
  new misses older events when a full page falls within one second.
- `walk_held_misses_late`: a walk that stops at a page of held mail misses an
  event that reached the relay after a page of newer mail.

An event is a time and an identifier; the filter's other conditions are fixed.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Paging

/-- An event: its creation time and its identifier. -/
abbrev Ev := Nat × Nat

/-- `a` comes first: newer, or as new with a smaller identifier. -/
def NewerFirst (a b : Ev) : Prop := b.1 < a.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel NewerFirst := fun a b => by unfold NewerFirst; infer_instance

instance : Std.Total NewerFirst := ⟨fun a b => by
  unfold NewerFirst
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases le_total a.2 b.2 with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inl (Or.inl h)⟩

instance : IsTrans Ev NewerFirst := ⟨fun a b c hab hbc => by
  unfold NewerFirst at *
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · exact Or.inl (lt_trans h2 h1)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, le_trans h1' h2'⟩⟩

/-- The events at or before `until` (all of them, without a bound). -/
def window (store : List Ev) (u : Option Nat) : List Ev :=
  store.filter fun e => u.all (e.1 ≤ ·)

/-- One page: the newest `cap` events of the window, newest first. -/
def page (cap : Nat) (store : List Ev) (u : Option Nat) : List Ev :=
  ((window store u).insertionSort NewerFirst).take cap

/-- The walk, with fuel: the events seen so far. -/
def walk (cap : Nat) (store : List Ev) : Nat → Option Nat → List Ev → List Ev
  | 0, _, seen => seen
  | fuel + 1, u, seen =>
    match (page cap store u).getLast? with
    | none => seen
    | some last =>
      let seen' := seen ++ (page cap store u).filter (· ∉ seen)
      if (page cap store u).all (· ∈ seen) then
        match u with
        | some (v + 1) => walk cap store fuel (some v) seen'
        | _ => seen'
      else
        match u with
        | some v =>
          if last.1 < v then walk cap store fuel (some last.1) seen'
          else match v with
            | 0 => seen'
            | w + 1 => walk cap store fuel (some w) seen'
        | none => walk cap store fuel (some last.1) seen'

/-! ## The stopping walk misses mail -/

/-- The walk that stops at the first page bringing nothing new. -/
def walkStopping (cap : Nat) (store : List Ev) : Nat → Option Nat → List Ev → List Ev
  | 0, _, seen => seen
  | fuel + 1, u, seen =>
    match (page cap store u).getLast? with
    | none => seen
    | some last =>
      if (page cap store u).all (· ∈ seen) then seen
      else walkStopping cap store fuel (some last.1) (seen ++ (page cap store u).filter (· ∉ seen))

/-- Three events in second 10, two in second 9, a cap of three: stopping at the
first page with nothing new never reaches second 9. -/
theorem walk_stopping_misses :
    (9, 4) ∉ walkStopping 3 [(9, 4), (9, 5), (10, 1), (10, 2), (10, 3)] 10 none [] := by
  decide

/-- The walk reaches it. -/
theorem walk_reaches :
    ∀ e ∈ [(9, 4), (9, 5), (10, 1), (10, 2), (10, 3)],
      e ∈ walk 3 [(9, 4), (9, 5), (10, 1), (10, 2), (10, 3)] 10 none [] := by
  decide

/-- The walk that stops at a page bringing nothing new but mail the reader holds. -/
def walkHeld (cap : Nat) (store held : List Ev) : Nat → Option Nat → List Ev → List Ev
  | 0, _, seen => seen
  | fuel + 1, u, seen =>
    match (page cap store u).getLast? with
    | none => seen
    | some last =>
      let seen' := seen ++ (page cap store u).filter (· ∉ seen)
      if (page cap store u).all (· ∈ seen) then
        match u with
        | some (v + 1) => walkHeld cap store held fuel (some v) seen'
        | _ => seen'
      else if (page cap store u).all (fun e => e ∈ seen ∨ e ∈ held) then seen'
      else
        match u with
        | some v =>
          if last.1 < v then walkHeld cap store held fuel (some last.1) seen'
          else match v with
            | 0 => seen'
            | w + 1 => walkHeld cap store held fuel (some w) seen'
        | none => walkHeld cap store held fuel (some last.1) seen'

/-- The reader holds three events; a fourth, older than all of them, reached the
relay after them. A walk that stops at held mail never reaches it. -/
theorem walk_held_misses_late :
    (5, 9) ∉ walkHeld 3 [(10, 1), (11, 2), (12, 3), (5, 9)] [(10, 1), (11, 2), (12, 3)] 10 none [] := by
  decide

/-- The walk reaches it. -/
theorem walk_reaches_late : (5, 9) ∈ walk 3 [(10, 1), (11, 2), (12, 3), (5, 9)] 10 none [] := by
  decide

/-! ## The walk sees everything -/

section Complete

variable {cap : Nat} {store : List Ev}

theorem sorted_page_window (u : Option Nat) :
    List.Pairwise NewerFirst ((window store u).insertionSort NewerFirst) :=
  List.pairwise_insertionSort NewerFirst _

theorem mem_window {u : Option Nat} {e : Ev} :
    e ∈ window store u ↔ e ∈ store ∧ u.all (e.1 ≤ ·) = true := by
  simp [window]

theorem mem_page {u : Option Nat} {e : Ev} (h : e ∈ page cap store u) : e ∈ window store u :=
  (List.perm_insertionSort NewerFirst _).mem_iff.mp (List.mem_of_mem_take h)

theorem le_of_mem_window {v : Nat} {x : Ev} (h : x ∈ window store (some v)) : x.1 ≤ v := by
  simpa [window] using (List.mem_filter.mp h).2

/-- The last event of a page is its oldest. -/
theorem last_oldest {u : Option Nat} {last : Ev} (hl : (page cap store u).getLast? = some last)
    {x : Ev} (hx : x ∈ page cap store u) : last.1 ≤ x.1 := by
  have hs : List.Pairwise NewerFirst (page cap store u) :=
    (sorted_page_window u).sublist (List.take_sublist _ _)
  obtain ⟨pre, hpre⟩ : ∃ pre, page cap store u = pre ++ [last] := List.getLast?_eq_some_iff.mp hl
  rw [hpre] at hs hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases (List.pairwise_append.mp hs).2.2 x hx last (by simp) with h | ⟨h, -⟩
    · exact h.le
    · exact h.ge
  · simp at hx; rw [hx]

/-- An event of the window that the page left out is no newer than its oldest. -/
theorem left_out_older {u : Option Nat} {last : Ev} (hl : (page cap store u).getLast? = some last)
    {e : Ev} (he : e ∈ window store u) (hn : e ∉ page cap store u) : e.1 ≤ last.1 := by
  have hsL := sorted_page_window (store := store) u
  have heL : e ∈ (window store u).insertionSort NewerFirst :=
    (List.perm_insertionSort NewerFirst _).mem_iff.mpr he
  rw [← List.take_append_drop cap ((window store u).insertionSort NewerFirst)] at hsL heL
  have hdrop : e ∈ ((window store u).insertionSort NewerFirst).drop cap := by
    rcases List.mem_append.mp heL with h | h
    · exact absurd h hn
    · exact h
  have hlast : last ∈ page cap store u := List.mem_of_getLast? hl
  rcases (List.pairwise_append.mp hsL).2.2 last hlast e hdrop with h | ⟨h, -⟩
  · exact h.le
  · exact h.ge

/-- A page that leaves something out is full. -/
theorem page_full {u : Option Nat} {e : Ev} (he : e ∈ window store u) (hn : e ∉ page cap store u) :
    (page cap store u).length = cap := by
  unfold page
  rw [List.length_take, List.length_insertionSort]
  apply min_eq_left
  by_contra hlt
  apply hn
  unfold page
  rw [List.take_of_length_le (by rw [List.length_insertionSort]; exact (not_le.mp hlt).le)]
  exact (List.perm_insertionSort NewerFirst _).mem_iff.mpr he

/-- The events of one second. -/
def atSecond (store : List Ev) (t : Nat) : List Ev := store.filter (·.1 = t)

/-- If no second holds more events than a page, a page asked for with `until` at
its own oldest second holds every event of that second. -/
theorem page_holds_second (hnd : store.Nodup) (hsec : ∀ t, (atSecond store t).length ≤ cap)
    {v : Nat} {last : Ev} (hl : (page cap store (some v)).getLast? = some last) (hv : last.1 = v)
    {e : Ev} (he : e ∈ window store (some v)) (ht : e.1 = v) : e ∈ page cap store (some v) := by
  by_contra hn
  have hfull := page_full he hn
  have hnodup : (page cap store (some v)).Nodup :=
    ((List.perm_insertionSort NewerFirst _).nodup_iff.mpr (hnd.filter _)).sublist (List.take_sublist _ _)
  have hat : ∀ x ∈ page cap store (some v), x ∈ atSecond store v := by
    intro x hx
    have h1 := le_of_mem_window (mem_page hx)
    have h2 := last_oldest hl hx
    exact List.mem_filter.mpr ⟨(mem_window.mp (mem_page hx)).1, by simp; omega⟩
  have hsubl : (e :: page cap store (some v)).Subperm (atSecond store v) := by
    apply List.subperm_of_subset (List.nodup_cons.mpr ⟨hn, hnodup⟩)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_filter.mpr ⟨(mem_window.mp he).1, by simp [ht]⟩
    · exact hat x hx
  have hlen := hsubl.length_le
  simp only [List.length_cons, hfull] at hlen
  have := hsec v
  omega

/-- What the walk may assume: at the start nothing is seen, and later everything
newer than `until` is. -/
def Inv (store : List Ev) : Option Nat → List Ev → Prop
  | none, seen => seen = []
  | some v, seen => ∀ e ∈ store, v < e.1 → e ∈ seen

/-- The latest time in the relay. -/
def maxTime (store : List Ev) : Nat := store.foldr (fun e m => max e.1 m) 0

theorem le_maxTime {e : Ev} (h : e ∈ store) : e.1 ≤ maxTime store := by
  induction store with
  | nil => simp at h
  | cons x xs ih =>
    simp only [maxTime, List.foldr_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- How many steps the walk may still need. -/
def budget (store : List Ev) : Option Nat → Nat
  | none => maxTime store + 2
  | some v => v + 1

theorem mem_seen' {seen p : List Ev} {x : Ev} (h : x ∈ seen ∨ x ∈ p) :
    x ∈ seen ++ p.filter (· ∉ seen) := by
  by_cases hx : x ∈ seen
  · exact List.mem_append_left _ hx
  · rcases h with h | h
    · exact absurd h hx
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨h, by simpa using hx⟩)

theorem page_nil_window {u : Option Nat} (hcap : 0 < cap) (h : (page cap store u).getLast? = none) :
    window store u = [] := by
  have hp : page cap store u = [] := List.getLast?_eq_none_iff.mp h
  unfold page at hp
  rcases List.take_eq_nil_iff.mp hp with h0 | h0
  · omega
  · exact List.eq_nil_of_length_eq_zero (by
      have := congrArg List.length h0
      rwa [List.length_insertionSort, List.length_nil] at this)

/-- **The walk sees everything**, from any state that satisfies its assumption,
given enough steps, if no second holds more events than a page. -/
theorem walk_complete_from (hcap : 0 < cap) (hnd : store.Nodup)
    (hsec : ∀ t, (atSecond store t).length ≤ cap) :
    ∀ (fuel : Nat) (u : Option Nat) (seen : List Ev), Inv store u seen → budget store u ≤ fuel →
      ∀ e ∈ store, e ∈ walk cap store fuel u seen := by
  intro fuel
  induction fuel with
  | zero => intro u seen _ hb; cases u <;> simp [budget] at hb
  | succ fuel ih =>
    intro u seen hinv hb e he
    -- the page's events, and an event left out of a page asked for at its own oldest second
    have hpage : ∀ x ∈ page cap store u, x ∈ seen ++ (page cap store u).filter (· ∉ seen) :=
      fun x hx => mem_seen' (Or.inr hx)
    have hold : ∀ x ∈ seen, x ∈ seen ++ (page cap store u).filter (· ∉ seen) :=
      fun x hx => mem_seen' (Or.inl hx)
    cases hlast : (page cap store u).getLast? with
    | none =>
      simp only [walk, hlast]
      have hw := page_nil_window hcap hlast
      cases u with
      | none => simp [window] at hw; subst hw; simp at he
      | some v =>
        have : ¬ e.1 ≤ v := fun hle => by
          have : e ∈ window store (some v) := mem_window.mpr ⟨he, by simpa using hle⟩
          rw [hw] at this; simp at this
        exact hinv e he (by omega)
    | some last =>
      have hlast_mem : last ∈ page cap store u := List.mem_of_getLast? hlast
      -- with `until` at the page's oldest second, the whole second is in the page
      have hsecond : ∀ v, u = some v → last.1 = v → ∀ x ∈ store, x.1 = v →
          x ∈ seen ++ (page cap store u).filter (· ∉ seen) := by
        intro v huv hlv x hx hxv
        subst huv
        exact hpage x (page_holds_second hnd hsec hlast hlv (mem_window.mpr ⟨hx, by simp [hxv]⟩) hxv)
      -- an event at `until` the page left out puts the page's oldest second at `until`
      have hforce : ∀ v, u = some v → ∀ x ∈ store, x.1 = v →
          x ∈ seen ++ (page cap store u).filter (· ∉ seen) := by
        intro v huv x hx hxv
        have hxw : x ∈ window store u := huv ▸ mem_window.mpr ⟨hx, by simp [hxv]⟩
        by_cases hxp : x ∈ page cap store u
        · exact hpage x hxp
        · have hlo := left_out_older hlast hxw hxp
          have hlv : last.1 ≤ v := le_of_mem_window (huv ▸ mem_page hlast_mem)
          exact hsecond v huv (by omega) x hx hxv
      -- below the page's oldest second, the page holds the window
      have hbelow : ∀ x ∈ window store u, last.1 < x.1 →
          x ∈ seen ++ (page cap store u).filter (· ∉ seen) := by
        intro x hxw hgt
        by_cases hxp : x ∈ page cap store u
        · exact hpage x hxp
        · have := left_out_older hlast hxw hxp; omega
      cases hall : (page cap store u).all (· ∈ seen) with
      | true =>
        cases u with
        | none =>
          simp only [Inv] at hinv; subst hinv
          have := List.all_eq_true.mp hall _ hlast_mem
          simp at this
        | some v =>
          cases v with
          | zero =>
            simp only [walk, hlast, hall, if_true]
            by_cases hgt : 0 < e.1
            · exact hold e (hinv e he hgt)
            · exact hforce 0 rfl e he (by omega)
          | succ w =>
            simp only [walk, hlast, hall, if_true]
            apply ih (some w) _ _ (by simp [budget] at hb ⊢; omega) e he
            intro x hx hwx
            by_cases hgt : w + 1 < x.1
            · exact hold x (hinv x hx hgt)
            · exact hforce (w + 1) rfl x hx (by omega)
      | false =>
        cases u with
        | none =>
          simp only [walk, hlast, hall, Bool.false_eq_true, if_false]
          apply ih (some last.1) _ _ ?_ e he
          · intro x hx hgt
            exact hbelow x (mem_window.mpr ⟨hx, rfl⟩) hgt
          · have := le_maxTime (store := store) ((mem_window.mp (mem_page hlast_mem)).1)
            simp [budget] at hb ⊢
            omega
        | some v =>
          have hlv : last.1 ≤ v := le_of_mem_window (mem_page hlast_mem)
          by_cases hlt : last.1 < v
          · simp only [walk, hlast, hall, Bool.false_eq_true, if_false, hlt, if_true]
            apply ih (some last.1) _ _ (by simp [budget] at hb ⊢; omega) e he
            intro x hx hgt
            by_cases hxv : v < x.1
            · exact hold x (hinv x hx hxv)
            · exact hbelow x (mem_window.mpr ⟨hx, by simpa using (by omega : x.1 ≤ v)⟩) hgt
          · have heq : last.1 = v := by omega
            cases v with
            | zero =>
              simp only [walk, hlast, hall, Bool.false_eq_true, if_false, hlt]
              by_cases hgt : 0 < e.1
              · exact hold e (hinv e he hgt)
              · exact hsecond 0 rfl heq e he (by omega)
            | succ w =>
              simp only [walk, hlast, hall, Bool.false_eq_true, if_false, hlt]
              apply ih (some w) _ _ (by simp [budget] at hb ⊢; omega) e he
              intro x hx hgt
              by_cases hxv : w + 1 < x.1
              · exact hold x (hinv x hx hxv)
              · exact hsecond (w + 1) rfl heq x hx (by omega)

/-- **The walk sees every event of the relay**, if no second holds more events
than a page. -/
theorem walk_complete (hcap : 0 < cap) (hnd : store.Nodup)
    (hsec : ∀ t, (atSecond store t).length ≤ cap) :
    ∀ e ∈ store, e ∈ walk cap store (maxTime store + 2) none [] :=
  walk_complete_from hcap hnd hsec _ none [] rfl (by simp [budget])

end Complete

end Mettapedia.Protocols.Nostr.Paging

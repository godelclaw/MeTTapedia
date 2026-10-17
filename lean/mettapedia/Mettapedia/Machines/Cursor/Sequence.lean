import Mettapedia.Machines.Cursor.Amortized
import Mettapedia.Machines.Cursor.Transfer
import Mathlib.Data.List.TakeDrop

/-!
# Sequence cursors: tails, array slices, and bounded prefetch

These independently implemented providers realize the same pull protocol.
The array provider retains its original storage and advances an offset. The
prefetch provider moves a bounded prefix into a private buffer. Both preserve
duplicates and exact exhaustion. The latter has a nonconstant local charge
but an amortized bound for every adaptive client, including early stopping.

Charges in the prefetch theorem count elements loaded from backing storage;
they are not measured instructions, allocations, or seconds.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.Sequence

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

variable (Item : Type)

def protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Option Item
  next _ _ := ()

def tails : Provider (protocol Item) where
  State _ _ := List Item
  step items _ := match items with
    | [] => ⟨none, []⟩
    | first :: rest => ⟨some first, rest⟩

structure Slice where
  storage : Array Item
  offset : Nat
  remaining : Nat

def slices : Provider (protocol Item) where
  State _ _ := Slice Item
  step view _ := match view.remaining with
    | 0 => ⟨none, view⟩
    | remaining + 1 => match view.storage[view.offset]? with
      | none => ⟨none, view⟩
      | some value =>
          ⟨some value, { view with offset := view.offset + 1, remaining := remaining }⟩

def sliceHom : Hom (slices Item) (tails Item) where
  map view := (view.storage.toList.drop view.offset).take view.remaining
  step view request := by
    rcases view with ⟨storage, offset, remaining⟩
    cases remaining with
    | zero => simp [slices, tails]
    | succ remaining =>
        cases found : storage[offset]? with
        | none =>
            have empty : storage.toList.drop offset = [] := by
              apply List.drop_eq_nil_iff.mpr
              simpa using (Array.getElem?_eq_none_iff.mp found)
            simp [slices, tails, found, empty]
        | some value =>
            have listFound : storage.toList[offset]? = some value := by simpa using found
            obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp listFound
            have head := List.drop_eq_getElem_cons bound
            rw [equal] at head
            simp [slices, tails, found, head]

/-- The buffer invariant bounds speculative demand independently of the size
of the remaining sequence. -/
structure Buffered (width : Nat) where
  buffer : List Item
  backing : List Item
  bounded : buffer.length ≤ width

def prefetched (width : Nat) : Provider (protocol Item) where
  State _ _ := Buffered Item width
  step state _ := match buffered : state.buffer with
    | first :: rest => ⟨some first, ⟨rest, state.backing, by
        have bound := state.bounded
        rw [buffered, List.length_cons] at bound
        omega⟩⟩
    | [] => match state.backing with
      | [] => ⟨none, state⟩
      | first :: rest =>
          ⟨some first, ⟨rest.take width, rest.drop width, List.length_take_le _ _⟩⟩

def prefetchHom (width : Nat) : Hom (prefetched Item width) (tails Item) where
  map state := state.buffer ++ state.backing
  step state request := by
    rcases state with ⟨buffer, backing, bounded⟩
    cases buffer with
    | cons first rest => simp [prefetched, tails]
    | nil =>
        cases backing with
        | nil => simp [prefetched, tails]
        | cons first rest =>
            simp [prefetched, tails, List.take_append_drop]

def loaded (width : Nat) : Charge (prefetched Item width) :=
  fun state _ => match state.buffer with
    | _ :: _ => 0
    | [] => match state.backing with
      | [] => 0
      | _ :: rest => 1 + (rest.take width).length

def requested : Charge (tails Item) :=
  fun items _ => match items with
    | [] => 0
    | _ :: _ => 1

def credit (width : Nat) : Potential (prefetched Item width) :=
  fun state => width - state.buffer.length

/-- Prefetch can spend many element-loads at one request, but the local
potential accounts exactly for the stored lookahead. -/
theorem prefetch_amortized (width : Nat) :
    Amortized (prefetchHom Item width) (loaded Item width) (requested Item)
      (credit Item width) := by
  intro base index state request
  rcases state with ⟨buffer, backing, bound⟩
  cases buffer with
  | cons first rest =>
      simp only [loaded, credit, prefetched, prefetchHom, requested,
        List.cons_append, List.length_cons, Nat.zero_add]
      rw [List.length_cons] at bound
      omega
  | nil =>
      cases backing with
      | nil => simp [loaded, credit, prefetched, prefetchHom, requested]
      | cons first rest =>
          simp [loaded, credit, prefetched, prefetchHom, requested]

/-- At most `width` unrequested elements can be paid for in any prefix of
any client. This includes clients that inspect replies before deciding to stop. -/
theorem prefetch_prefix_bound
    {Return : Unit → Unit → Type}
    (C : Client (P := protocol Item) (Return := Return))
    (width fuel : Nat) (index : Unit) (control : C.V () index)
    (state : Buffered Item width) :
    (advance (prefetched Item width) C (loaded Item width) fuel
        ⟨index, control, state⟩).1 ≤
      (advance (tails Item) C (requested Item) fuel
        ⟨index, control, state.buffer ++ state.backing⟩).1 + width := by
  have bound := advance_amortized C (prefetchHom Item width)
    (loaded Item width) (requested Item) (credit Item width)
    (prefetch_amortized Item width) fuel ⟨index, control, state⟩
  dsimp only [Hom.packet, prefetchHom, credit] at bound
  omega

/-! ## Producer-supplied final-return evidence

The extra reply bit comes from the retained representation. Erasing it keeps
the existing pull protocol and every adaptive client law. It is not established
by asking the producer for another item, and a prefix length cannot replace it.
-/

def finalProtocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Option (Item × Bool)
  next _ _ := ()

def finalTails : Provider (finalProtocol Item) where
  State _ _ := List Item
  step items _ := match items with
    | [] => ⟨none, []⟩
    | first :: rest => ⟨some (first, rest.isEmpty), rest⟩

def finalSlices : Provider (finalProtocol Item) where
  State _ _ := Slice Item
  step view _ := match view.remaining with
    | 0 => ⟨none, view⟩
    | remaining + 1 => match view.storage[view.offset]? with
      | none => ⟨none, view⟩
      | some value =>
          ⟨some (value, remaining == 0),
            {view with offset := view.offset + 1, remaining := remaining}⟩

/-- Reply erasure retains the provider state; it does not run a second pull. -/
def eraseFinal (source : Provider (finalProtocol Item)) : Provider (protocol Item) where
  State := source.State
  step state _ :=
    let observed := source.step state ()
    ⟨observed.1.map Prod.fst, observed.2⟩

/-- The annotated list implementation and the ordinary list implementation
are independent steps with equal replies after metadata erasure. -/
def finalTailHom : Hom (eraseFinal Item (finalTails Item)) (tails Item) where
  map items := items
  step items request := by cases items <;> simp [eraseFinal, finalTails, tails]

def finalSliceHom : Hom (eraseFinal Item (finalSlices Item)) (slices Item) where
  map view := view
  step view request := by
    cases remaining : view.remaining with
    | zero => simp [eraseFinal, finalSlices, slices, remaining]
    | succ rest => cases found : view.storage[view.offset]? <;>
        simp [eraseFinal, finalSlices, slices, remaining, found]

/-- The bit implies that the independently specified source tail has no item.
No assumption about answer values, equality or distinctness is used. -/
theorem final_tail_has_no_future (items : List Item) (value : Item)
    (last : ((finalTails Item).step (base := ()) (index := ()) items ()).1 = some (value, true)) :
    ((tails Item).step (base := ()) (index := ()) ((finalTails Item).step (base := ()) (index := ()) items ()).2 ()).1 = none := by
  cases items with
  | nil => simp [finalTails] at last
  | cons first rest => cases rest with
    | nil => rfl
    | cons second later =>
        have flags : (false : Bool) = true := congrArg Prod.snd (Option.some.inj last)
        cases flags

/-- Array metadata gives the same empty source tail through the existing
slice representation map. Storage remains owned; the reply is not a release. -/
theorem final_slice_has_empty_source (view : Slice Item) (value : Item)
    (last : ((finalSlices Item).step (base := ()) (index := ()) view ()).1 = some (value, true)) :
    (sliceHom Item).map (base := ()) (index := ()) ((finalSlices Item).step (base := ()) (index := ()) view ()).2 = [] := by
  cases remaining : view.remaining with
  | zero => simp [finalSlices, remaining] at last
  | succ rest =>
      cases found : view.storage[view.offset]? with
      | none => simp [finalSlices, remaining, found] at last
      | some item => cases rest with
        | zero =>
            simp only [finalSlices, remaining, found, sliceHom, List.take_zero]
            rfl
        | succ rest =>
            simp only [finalSlices, remaining, found] at last
            have flags : (false : Bool) = true := congrArg Prod.snd (Option.some.inj last)
            cases flags

theorem equal_payloads_do_not_make_the_first_final (value : Item) :
    ((finalTails Item).step (base := ()) (index := ()) [value, value] ()).1 = some (value, false) ∧
      ((finalTails Item).step (base := ()) (index := ()) [value] ()).1 = some (value, true) := ⟨rfl, rfl⟩

end Mettapedia.Machines.Cursor.Sequence

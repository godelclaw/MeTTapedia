import Mettapedia.OSLF.NativeTypes.Decision.Stream

/-!
# Suspended matching alternatives

Binding a finite work stream delays its per-item continuation. Filtering can
therefore reject an alternative without enumerating later alternatives.
Enumerating assigns ordinals only to yielded items, independently of pauses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Scheduling.Stream

universe u v

def bind {Item : Type u} {Result : Type v}
    (stream : Stream Item) (continuation : Item → Stream Result) : Stream Result :=
  match stream with
  | .done => .done
  | .pause next => .pause fun _ => bind (next ()) continuation
  | .yield item next => .pause fun _ =>
      append (continuation item) fun _ => bind (next ()) continuation

theorem flatten_bind {Item : Type u} {Result : Type v}
    (stream : Stream Item) (continuation : Item → Stream Result) :
    (bind stream continuation).flatten = stream.flatten.flatMap fun item =>
      (continuation item).flatten := by
  induction stream with
  | done => rfl
  | pause next ih => exact ih ()
  | yield item next ih =>
      exact (flatten_append _ _).trans (congrArg (List.append _) (ih ()))

def filterMap {Item : Type u} {Result : Type v} (transform : Item → Option Result)
    (stream : Stream Item) : Stream Result :=
  bind stream fun item =>
    match transform item with
    | none => .done
    | some result => .yield result fun _ => .done

theorem flatten_filterMap {Item : Type u} {Result : Type v}
    (transform : Item → Option Result) (stream : Stream Item) :
    (filterMap transform stream).flatten = stream.flatten.filterMap transform := by
  rw [filterMap, flatten_bind]
  induction stream.flatten with
  | nil => rfl
  | cons item rest ih =>
      cases found : transform item <;> simp only [List.flatMap_cons, found, flatten,
        List.filterMap_cons, List.nil_append,
        List.singleton_append, ih]

def enumerate {Item : Type u} (stream : Stream Item) : Stream (Item × Nat) :=
  mapIdx (fun item ordinal => (item, ordinal)) stream

theorem flatten_enumerate {Item : Type u} (stream : Stream Item) :
    (enumerate stream).flatten = stream.flatten.zipIdx := by
  rw [enumerate, flatten_mapIdx_zero]
  exact List.map_id _

end Mettapedia.OSLF.NativeTypes.Decision.Scheduling.Stream

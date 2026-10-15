import Mettapedia.OSLF.NativeTypes.Decision.Stream

/-!
# Dependent receipt maps on suspended work

The membership proof follows the suspended stream. Mapping does not enumerate
its answers or advance any pending job. The exhaustive list and work bound
are used only to state the comparison laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Scheduling.Stream

universe u v

def mapAttached {Item : Type u} {Result : Type v} (stream : Stream Item)
    (transform : {item // item ∈ stream.flatten} → Result) : Stream Result :=
  match stream with
  | .done => .done
  | .pause next => .pause fun _ => mapAttached (next ()) fun item => transform item
  | .yield item next => .yield (transform ⟨item, by simp only [flatten, List.mem_cons, true_or]⟩)
      fun _ => mapAttached (next ()) fun rest =>
        transform ⟨rest.val, List.mem_cons_of_mem item rest.property⟩

theorem flatten_mapAttached {Item : Type u} {Result : Type v} (stream : Stream Item)
    (transform : {item // item ∈ stream.flatten} → Result) :
    (mapAttached stream transform).flatten = stream.flatten.attach.map transform := by
  induction stream with
  | done => rfl
  | pause next ih => exact ih () _
  | yield item next ih =>
    change {entry // entry ∈ item :: (next ()).flatten} → Result at transform
    simp only [mapAttached, flatten]
    rw [ih ()]
    rw [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem workBound_mapAttached {Item : Type u} {Result : Type v} (stream : Stream Item)
    (transform : {item // item ∈ stream.flatten} → Result) :
    (mapAttached stream transform).workBound = stream.workBound := by
  induction stream with
  | done => rfl
  | pause next ih => exact congrArg (1 + ·) (ih () _)
  | yield item next ih => exact congrArg (1 + ·) (ih () _)

def attach {Item : Type u} (stream : Stream Item) :
    Stream {item // item ∈ stream.flatten} := mapAttached stream id

theorem flatten_attach {Item : Type u} (stream : Stream Item) :
    stream.attach.flatten = stream.flatten.attach := by
  rw [attach, flatten_mapAttached, List.map_id]

theorem workBound_attach {Item : Type u} (stream : Stream Item) :
    stream.attach.workBound = stream.workBound := workBound_mapAttached stream id

theorem mem_flatten_mapAttached {Item : Type u} {Result : Type v} (stream : Stream Item)
    (transform : {item // item ∈ stream.flatten} → Result) (result : Result) :
    result ∈ (mapAttached stream transform).flatten ↔ ∃ item, transform item = result := by
  rw [flatten_mapAttached]
  simp

end Mettapedia.OSLF.NativeTypes.Decision.Scheduling.Stream

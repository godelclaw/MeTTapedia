import Mettapedia.Machines.Cursor.GenerationalSharing

/-!
# Borrowed native returns and retained residual roots

Synchronous completed values may use their caller's live graph. A residual
must transport all its roots before that caller's storage can be released.
The reference transports both; the deferred algorithm transports only the
escaping residual. They preserve ordered graph observations and control events,
including every duplicate occurrence and every finite prefix.

The graph transfer and release discipline are those of GenerationalSharing.
Its nodes record homes and edges: the observer below forgets only homes.
Payload contents, C root discovery, sharing within a copy session, pointer
validity, allocation failure and source-level fuel need separate checks.
The traversal account is a tree-occurrence upper bound, not an exact count
of allocations in a sharing-preserving implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.NativeBorrowedReturn

open GenerationalSharing
open Mettapedia.Machines.Cursor.TailSummary (Home)

inductive Image where
  | node (children : List Image)

mutual
def image : Node → Image
  | .mk _ children => .node (images children)
def images : List Node → List Image
  | [] => []
  | node :: rest => image node :: images rest
end

theorem images_eq_map (nodes : List Node) : images nodes = nodes.map image := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp only [images, List.map_cons, ih]

/-- Moving a graph changes its storage homes, preserving its complete shape. -/
theorem transfer_image (G : Generations) (destination : Nat)
    (share : Node → Bool) (node : Node) :
    image (transfer G destination share node) = image node := by
  refine Node.rec
    (motive_1 := fun node => image (transfer G destination share node) = image node)
    (motive_2 := fun nodes => ∀ node ∈ nodes,
      image (transfer G destination share node) = image node)
    ?_ ?_ ?_ node
  · intro home children ih
    rw [transfer_mk]
    split
    · rfl
    · simp only [image, images_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left ih
  · intro node member
    cases member
  · intro node rest first later child member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact later child member

inductive Event (Value Effect Fault : Type) where
  | completed (value : Value)
  | residual (roots : List Value)
  | effect (value : Effect)
  | failure
  | raised (fault : Fault)
  | interrupted

variable {Effect Fault : Type}

def observe : Event Node Effect Fault → Event Image Effect Fault
  | .completed value => .completed (image value)
  | .residual roots => .residual (roots.map image)
  | .effect effect => .effect effect
  | .failure => .failure
  | .raised fault => .raised fault
  | .interrupted => .interrupted

/-- Reference: transport a completed value as well as every escaping root. -/
def eager (G : Generations) (destination : Nat) (share : Node → Bool) :
    Event Node Effect Fault → Event Node Effect Fault
  | .completed value => .completed (transfer G destination share value)
  | .residual roots => .residual (roots.map (transfer G destination share))
  | .effect effect => .effect effect
  | .failure => .failure
  | .raised fault => .raised fault
  | .interrupted => .interrupted

/-- Implementation: synchronous values are loaned; escaping roots are owned. -/
def deferred (G : Generations) (destination : Nat) (share : Node → Bool) :
    Event Node Effect Fault → Event Node Effect Fault
  | .completed value => .completed value
  | .residual roots => .residual (roots.map (transfer G destination share))
  | .effect effect => .effect effect
  | .failure => .failure
  | .raised fault => .raised fault
  | .interrupted => .interrupted

theorem deferred_event_refines (G : Generations) (destination : Nat)
    (share : Node → Bool) (event : Event Node Effect Fault) :
    observe (deferred G destination share event) = observe event ∧
      observe (eager G destination share event) = observe event := by
  cases event with
  | completed value => simp only [deferred, eager, observe, transfer_image, and_self]
  | residual roots =>
      simp only [deferred, eager, observe, List.map_map]
      have same : roots.map (image ∘ transfer G destination share) =
          roots.map image := List.map_congr_left (fun node _ => transfer_image G destination share node)
      simp only [same, and_self]
  | effect effect => exact ⟨rfl, rfl⟩
  | failure => exact ⟨rfl, rfl⟩
  | raised fault => exact ⟨rfl, rfl⟩
  | interrupted => exact ⟨rfl, rfl⟩

/-- Ordered observations agree for every finite trace, without deduplication
or reordering effects, failures, raised faults or interruptions. -/
theorem deferred_trace_refines (G : Generations) (destination : Nat)
    (share : Node → Bool) (trace : List (Event Node Effect Fault)) :
    (trace.map (deferred G destination share)).map observe = trace.map observe ∧
      (trace.map (eager G destination share)).map observe = trace.map observe := by
  constructor
  · simp only [List.map_map]
    exact List.map_congr_left fun event _ => (deferred_event_refines G destination share event).1
  · simp only [List.map_map]
    exact List.map_congr_left fun event _ => (deferred_event_refines G destination share event).2

/-- This prefix is measured in retained trace events, not authored fuel. -/
theorem deferred_prefix_refines (G : Generations) (destination : Nat)
    (share : Node → Bool) (trace : List (Event Node Effect Fault)) (budget : Nat) :
    ((trace.take budget).map (deferred G destination share)).map observe =
      (trace.map observe).take budget := by
  rw [(deferred_trace_refines G destination share (trace.take budget)).1]
  exact List.map_take ..

mutual
def traversal : Node → Nat
  | .mk _ children => 1 + traversals children
def traversals : List Node → Nat
  | [] => 0
  | node :: rest => traversal node + traversals rest
end

def eagerWork : Event Node Effect Fault → Nat
  | .completed value => traversal value
  | .residual roots => traversals roots
  | _ => 0

def deferredWork : Event Node Effect Fault → Nat
  | .residual roots => traversals roots
  | _ => 0

theorem deferred_work_le_eager (trace : List (Event Node Effect Fault)) :
    (trace.map deferredWork).sum ≤ (trace.map eagerWork).sum := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons event rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have here : deferredWork event ≤ eagerWork event := by
        cases event <;> simp [deferredWork, eagerWork]
      exact Nat.add_le_add here ih

/-- A residual's entire transported graph survives a legal release that keeps
its destination. Merely preserving the top-level root would be insufficient. -/
theorem escaped_descendant_survives (G : Generations) (released : Nat → Prop)
    (legal : FollowsGenerations G released) (destination : Nat)
    (share : Node → Bool) (kept : ¬ released destination)
    (roots : List Node) (root : Node) (member : root ∈ roots) (descendant : Node)
    (below : Below (transfer G destination share root) descendant) :
    ∃ retained ∈ roots.map (transfer G destination share),
      Below retained descendant ∧ ¬ Frees released descendant.home := by
  exact ⟨transfer G destination share root, List.mem_map.mpr ⟨root, member, rfl⟩,
    below, transfer_survives_source_release G released legal destination share kept root descendant below⟩

/-- The retained trace keeps both appearances of a shared result. -/
theorem duplicate_returns_preserved (G : Generations) (destination : Nat)
    (share : Node → Bool) (value : Node) :
    ([Event.completed value, Event.completed value] : List (Event Node Effect Fault)).map
      (deferred G destination share) = [.completed value, .completed value] := rfl

/-- Borrowing across the source's release without first retaining the residual
is invalid, even for an immutable leaf. -/
theorem unretained_borrow_is_freed :
    Frees (fun arena => arena = 1) (Node.mk (.arena 1) []).home := by
  simp [Frees, Node.home]

/-- For one synchronous leaf the eliminated traversal is strictly positive. -/
theorem synchronous_transfer_is_avoided :
    deferredWork (Event.completed (.mk (.arena 1) []) : Event Node Effect Fault) = 0 ∧
      eagerWork (Event.completed (.mk (.arena 1) []) : Event Node Effect Fault) = 1 := by
  simp [deferredWork, eagerWork, traversal, traversals]

#print axioms transfer_image
#print axioms deferred_event_refines
#print axioms deferred_trace_refines
#print axioms deferred_prefix_refines
#print axioms deferred_work_le_eager
#print axioms escaped_descendant_survives
#print axioms duplicate_returns_preserved
#print axioms unretained_borrow_is_freed
#print axioms synchronous_transfer_is_avoided

end Mettapedia.Machines.Cursor.NativeBorrowedReturn

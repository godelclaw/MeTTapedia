import Mettapedia.GSLT.Poly.SortedSignature
import Mettapedia.Machines.Cursor.Protocol

/-!
# Sorted dissections as resumable cursor clients

A constructor's argument frontier is a client of the existing request/reply
machine. Each request names its source occurrence and carries only that pending
payload; its reply fills the occurrence's own sorted slot. The provider's state
and the completed prefix remain in the same retained packet.

The general client does not choose how a child is interpreted. A concrete pure
provider yields an exact correspondence with the independently specified
pointwise argument map, including completion and a linear request count. These
counts are protocol operations, not CPU work or a language's evaluation fuel.
The functional slot carrier has no native allocation or byte-cost claim.

This is an ordered constructor traversal, not a complete HE or Prime evaluator.
Demand, effects, waiting and ownership must be supplied by a suitable child
service and its language-specific admission law. This client suspends between
child replies; suspension inside an unfinished child needs an expanded protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Poly.SortedTraversal

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.GSLT.Poly.SortedSignature
open Mettapedia.TypeTheory
open Mettapedia.Machines.Cursor

variable {signature : Signature.{0, 0}}
variable (Done Pending : signature.Srt → Type) (constructor : signature.Constructor)

abbrev Arguments :=
  (position : Fin (signature.arity constructor)) → Done (signature.input constructor position)

/-- A request retains the occurrence even when two source payloads are equal.
The reply sort is fixed by that exact argument position. -/
abbrev protocol : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Σ position : Fin (signature.arity constructor),
    Pending (signature.input constructor position)
  Position request := Done (signature.input constructor request.1)
  next _ _ := ()

/-- Expose the next sorted request, or the completed tuple. -/
def nextLayer (base index : Unit)
    (cursor : ArgumentCursor signature Done Pending constructor) :
    ((protocol Done Pending constructor).withHoles
      (fun _ _ => Arguments Done constructor)).endofunctor.obj
      (fun _ _ => ArgumentCursor signature Done Pending constructor) base index := by
  if more : cursor.position.val < signature.arity constructor then
    exact ⟨.inr ⟨⟨cursor.position.val, more⟩, cursor.current more⟩,
      fun value => cursor.accept more value⟩
  else
    have complete : cursor.position.val = signature.arity constructor := by
      have bound := cursor.position.isLt
      omega
    exact ⟨.inl (cursor.finish complete), fun impossible => nomatch impossible⟩

/-- The continuation is the dissection frontier itself. No reconstructed term
or second traversal stack is needed to choose the following request. -/
abbrev client : Client (P := protocol Done Pending constructor)
    (Return := fun _ _ => Arguments Done constructor) where
  V _ _ := ArgumentCursor signature Done Pending constructor
  str := fun base index => ↾(nextLayer Done Pending constructor base index)

variable {Done Pending constructor}

def packet (provider : Provider (protocol Done Pending constructor))
    (cursor : ArgumentCursor signature Done Pending constructor)
    (state : provider.State () ()) : Packet provider (client Done Pending constructor) () :=
  ⟨(), cursor, state⟩

theorem advance_more (provider : Provider (protocol Done Pending constructor))
    (charge : Charge provider) (fuel : Nat)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (state : provider.State () ())
    (more : cursor.position.val < signature.arity constructor) :
    advance provider (client Done Pending constructor) charge (fuel + 1)
        (packet provider cursor state) =
      let request : (protocol Done Pending constructor).Shape () () :=
        ⟨⟨cursor.position.val, more⟩, cursor.current more⟩
      let reply := provider.step state request
      let rest := advance provider (client Done Pending constructor) charge fuel
        (packet provider (cursor.accept more reply.1) reply.2)
      (charge state request + rest.1, rest.2) := by
  have layer : (client Done Pending constructor).str () () cursor =
      ⟨.inr ⟨⟨cursor.position.val, more⟩, cursor.current more⟩,
        fun value => cursor.accept more value⟩ := by
    change nextLayer Done Pending constructor () () cursor = _
    exact dif_pos more
  simp only [advance, packet, layer]

theorem advance_complete (provider : Provider (protocol Done Pending constructor))
    (charge : Charge provider) (fuel : Nat)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (state : provider.State () ())
    (complete : cursor.position.val = signature.arity constructor) :
    advance provider (client Done Pending constructor) charge (fuel + 1)
        (packet provider cursor state) =
      (0, .done ⟨(), cursor.finish complete, state⟩) := by
  have noMore : ¬ cursor.position.val < signature.arity constructor := by omega
  have layer : (client Done Pending constructor).str () () cursor =
      ⟨.inl (cursor.finish complete), fun impossible => nomatch impossible⟩ := by
    change nextLayer Done Pending constructor () () cursor = _
    apply (dif_neg noMore).trans
    dsimp only
    exact Sigma.ext rfl (heq_of_eq (funext fun impossible => impossible.elim))
  simp only [advance, packet, layer]

/-- This constructed traversal inherits exact chunking for every provider,
including a provider with mutable state and nonconstant operation charges. -/
theorem resume_exact (provider : Provider (protocol Done Pending constructor))
    (charge : Charge provider) (first second : Nat)
    (cursor : ArgumentCursor signature Done Pending constructor)
    (state : provider.State () ()) :
    resume provider (client Done Pending constructor) charge second
        (advance provider (client Done Pending constructor) charge first
          (packet provider cursor state)) =
      advance provider (client Done Pending constructor) charge (first + second)
        (packet provider cursor state) :=
  (advance_add provider (client Done Pending constructor) charge first second _).symm

/-- With any total child service, a bounded prefix makes one request per
advanced occurrence. Both the actual replies and service state are retained.
No commutativity, purity or history erasure is assumed of the service. -/
theorem service_prefix (provider : Provider (protocol Done Pending constructor))
    (quantum : Nat) (cursor : ArgumentCursor signature Done Pending constructor)
    (state : provider.State () ())
    (within : cursor.position.val + quantum ≤ signature.arity constructor) :
    ∃ (retained : ArgumentCursor signature Done Pending constructor)
        (saved : provider.State () ()),
      advance provider (client Done Pending constructor) (fun _ _ => 1) quantum
          (packet provider cursor state) =
        (quantum, .paused (packet provider retained saved)) ∧
      retained.position.val = cursor.position.val + quantum := by
  induction quantum generalizing cursor state with
  | zero => exact ⟨cursor, state, rfl, by omega⟩
  | succ quantum ih =>
      have more : cursor.position.val < signature.arity constructor := by omega
      let request : (protocol Done Pending constructor).Shape () () :=
        ⟨⟨cursor.position.val, more⟩, cursor.current more⟩
      let response := provider.step state request
      have nextWithin : (cursor.accept more response.1).position.val + quantum ≤
          signature.arity constructor := by
        simp only [ArgumentCursor.accept]
        omega
      obtain ⟨retained, saved, ran, position⟩ := ih _ response.2 nextWithin
      refine ⟨retained, saved, ?_, ?_⟩
      · rw [advance_more _ _ quantum _ _ more]
        change (1 + (advance provider (client Done Pending constructor)
            (fun _ _ => 1) quantum
            (packet provider (cursor.accept more response.1) response.2)).1,
          (advance provider (client Done Pending constructor)
            (fun _ _ => 1) quantum
            (packet provider (cursor.accept more response.1) response.2)).2) = _
        rw [ran]
        simp [Nat.add_comm]
      · simp only [ArgumentCursor.accept] at position
        omega

/-- A concrete child service processes just the supplied argument. -/
abbrev pureProvider (process : (sort : signature.Srt) → Pending sort → Done sort) :
    Provider (protocol Done Pending constructor) where
  State _ _ := Unit
  step _ request := ⟨process _ request.2, ()⟩

/-- Every remaining child is requested once. One additional inspection returns
the completed tuple and charges no provider operation. The result is the
independent pointwise decoder, not a second run of the cursor. -/
theorem complete_exact (process : (sort : signature.Srt) → Pending sort → Done sort)
    (remaining : Nat) (cursor : ArgumentCursor signature Done Pending constructor)
    (ends : cursor.position.val + remaining = signature.arity constructor) :
    advance (pureProvider process) (client Done Pending constructor) (fun _ _ => 1)
        (remaining + 1) (packet _ cursor ()) =
      (remaining, .done ⟨(), cursor.denote process, ()⟩) := by
  induction remaining generalizing cursor with
  | zero =>
      have complete : cursor.position.val = signature.arity constructor := by omega
      rw [advance_complete _ _ 0 _ _ complete, ArgumentCursor.denote_finish process]
  | succ remaining ih =>
      have more : cursor.position.val < signature.arity constructor := by omega
      have nextEnds :
          (cursor.accept more (process _ (cursor.current more))).position.val + remaining =
            signature.arity constructor := by
        simp only [ArgumentCursor.accept]
        omega
      rw [advance_more _ _ (remaining + 1) _ _ more]
      change (1 + (advance (pureProvider process) (client Done Pending constructor)
          (fun _ _ => 1) (remaining + 1)
          (packet _ (cursor.accept more (process _ (cursor.current more))) ())).1,
        (advance (pureProvider process) (client Done Pending constructor)
          (fun _ _ => 1) (remaining + 1)
          (packet _ (cursor.accept more (process _ (cursor.current more))) ())).2) = _
      rw [ih _ nextEnds, ArgumentCursor.denote_accept]
      simp [Nat.add_comm]

theorem map_exact (process : (sort : signature.Srt) → Pending sort → Done sort)
    (arguments : Arguments Pending constructor) :
    advance (pureProvider process) (client Done Pending constructor) (fun _ _ => 1)
        (signature.arity constructor + 1) (packet _ (ArgumentCursor.start arguments) ()) =
      (signature.arity constructor,
        .done ⟨(), (fun other => process _ (arguments other)), ()⟩) := by
  rw [complete_exact process _ _ (by simp [ArgumentCursor.start]), ArgumentCursor.denote_start]

/-- A prefix retains its actual frontier and its processed results. It has
made exactly `quantum` requests, including equal-valued occurrences. -/
theorem prefix_exact (process : (sort : signature.Srt) → Pending sort → Done sort)
    (quantum : Nat) (cursor : ArgumentCursor signature Done Pending constructor)
    (within : cursor.position.val + quantum ≤ signature.arity constructor) :
    ∃ retained : ArgumentCursor signature Done Pending constructor,
      advance (pureProvider process) (client Done Pending constructor) (fun _ _ => 1)
          quantum (packet _ cursor ()) = (quantum, .paused (packet _ retained ())) ∧
        retained.position.val = cursor.position.val + quantum ∧
        retained.denote process = cursor.denote process := by
  induction quantum generalizing cursor with
  | zero => exact ⟨cursor, rfl, by omega, rfl⟩
  | succ quantum ih =>
      have more : cursor.position.val < signature.arity constructor := by omega
      have nextWithin :
          (cursor.accept more (process _ (cursor.current more))).position.val + quantum ≤
            signature.arity constructor := by
        simp only [ArgumentCursor.accept]
        omega
      obtain ⟨retained, ran, position, result⟩ := ih _ nextWithin
      refine ⟨retained, ?_, ?_, ?_⟩
      · rw [advance_more _ _ quantum _ _ more]
        change (1 + (advance (pureProvider process) (client Done Pending constructor)
            (fun _ _ => 1) quantum
            (packet _ (cursor.accept more (process _ (cursor.current more))) ())).1,
          (advance (pureProvider process) (client Done Pending constructor)
            (fun _ _ => 1) quantum
            (packet _ (cursor.accept more (process _ (cursor.current more))) ())).2) = _
        rw [ran]
        simp [Nat.add_comm]
      · simp only [ArgumentCursor.accept] at position
        omega
      · exact result.trans (ArgumentCursor.denote_accept process cursor more)

end Mettapedia.GSLT.Poly.SortedTraversal

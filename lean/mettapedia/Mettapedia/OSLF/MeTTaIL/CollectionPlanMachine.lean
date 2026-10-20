import Mettapedia.OSLF.MeTTaIL.ScopedCollectionCanonical

/-!
# Resumable batches for every root-collection rule in a plan

Each job retains its source-derived request and independent matcher state.
Rules are resumed uniformly; publication keeps the rule request beside every
checked source receipt and authored target.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine

open ScopedCollectionMachine

structure Job where
  ordinal : Nat
  request : Request
  state : ScopedCollectionMachine.State
  deriving Repr

abbrev State := List Job

structure Firing where
  ordinal : Nat
  request : Request
  receipt : FiringReceipt
  deriving Repr

def start (requests : List (Nat × Request)) : State :=
  requests.map fun (ordinal, request) =>
    ⟨ordinal, request, ScopedCollectionMachine.start request⟩

def resume (fuel : Nat) (state : State) : State :=
  state.map fun job => { job with
    state := ScopedCollectionMachine.resume job.request fuel job.state }

def complete (state : State) : Bool :=
  state.all fun job => ScopedCollectionMachine.complete job.state

def publication (state : State) : List Firing :=
  state.flatMap fun job =>
    (ScopedCollectionMachine.firings job.request job.state).map fun receipt =>
      ⟨job.ordinal, job.request, receipt⟩

theorem resume_add (first extra : Nat) (state : State) :
    resume (first + extra) state = resume extra (resume first state) := by
  simp [resume, List.map_map, Function.comp_def, ScopedCollectionMachine.resume_add]

theorem resume_zero (state : State) : resume 0 state = state := by
  simp [resume, ScopedCollectionMachine.resume_zero]

def Firing.Valid (firing : Firing) : Prop :=
  ScopedCollectionMachine.FiringValid firing.request firing.receipt

theorem publication_sound (fuel : Nat) (requests : List (Nat × Request)) {firing : Firing}
    (member : firing ∈ publication (resume fuel (start requests))) : firing.Valid := by
  simp only [publication, resume, start, List.map_map, List.mem_flatMap, List.mem_map] at member
  obtain ⟨job, ⟨entry, requestMember, rfl⟩, receipt, receiptMember, same⟩ := member
  obtain ⟨ordinal, request⟩ := entry
  cases same
  exact ScopedCollectionMachine.firings_sound request fuel receiptMember

theorem publication_origin (fuel : Nat) (requests : List (Nat × Request))
    {firing : Firing}
    (member : firing ∈ publication (resume fuel (start requests))) :
    (firing.ordinal, firing.request) ∈ requests := by
  simp only [publication, resume, start, List.map_map, List.mem_flatMap,
    List.mem_map] at member
  obtain ⟨job, ⟨entry, requestMember, rfl⟩, receipt, receiptMember, same⟩ := member
  obtain ⟨ordinal, request⟩ := entry
  cases same
  exact requestMember

end Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine

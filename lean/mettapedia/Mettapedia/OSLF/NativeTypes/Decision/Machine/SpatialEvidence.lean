import Mettapedia.OSLF.NativeTypes.Decision.Machine.ModalTrace

/-!
# Retained structural witnesses

A successful separation retains the decomposition that earned it. A negative
answer has checked every enumerated decomposition; the structural backend's
coverage theorem transports that absence to all semantic decompositions.
Neither claim treats structural work as an operational transition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Machine

open Mettapedia.GSLT
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

universe u v w

theorem separation_trace_evidence {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (index : Nat) (left right : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source)
    {seen : List (Evidence backend)}
    {result : Outcome (denotation leaves (.separating index left right) backend.spatial.theory source)}
    (trace : Trace (tasks backend leaves (.separating index left right) source sourceAdmitted []) seen result) :
    (result.answer = some true → ∃ parts listed,
      Evidence.separation (SpatialObservation.mk index source parts listed []) ∈ seen ∧
      denotation leaves left backend.spatial.theory parts.1 ∧
      denotation leaves right backend.spatial.theory parts.2) ∧
    (result.answer = some false → ∀ parts listed,
      Evidence.separation (SpatialObservation.mk index source parts listed []) ∈ seen ∧
      ¬ (denotation leaves left backend.spatial.theory parts.1 ∧
         denotation leaves right backend.spatial.theory parts.2)) := by
  rw [tasks] at trace
  cases trace with
  | paused tail =>
    obtain ⟨reply, splitTrace, result_eq⟩ := mapReply_trace _
      (fun reply => by cases reply <;> rfl) _ tail
    have childrenComplete : ∀ parts listed, Decides
        (let admittedParts := backend.spatial.components_admitted index source sourceAdmitted
          parts (by rw [← backend.splitTasks_exact]; exact listed)
         bindReply
           (tasks backend leaves left parts.1 admittedParts.1 [0]) fun first =>
           match first with
           | .refuted refutation => finish (.refuted (fun holds => refutation holds.1))
           | _ => mapReply (Outcome.conjunction first)
               (tasks backend leaves right parts.2 admittedParts.2 [1])) := by
      intro parts listed
      dsimp only
      apply bindReply_decides
      · exact tasks_complete _ _ _ _ _ _
      · intro first decided
        cases first with
        | proved proof =>
          apply mapReply_decides
          · exact fun other settled =>
              Outcome.conjunction_decided (.proved proof) other ⟨true, rfl⟩ settled
          · exact tasks_complete _ _ _ _ _ _
        | refuted refutation => exact finish_decides _ ⟨false, rfl⟩
        | unknown => obtain ⟨_, impossible⟩ := decided; cases impossible
    obtain ⟨positive, negative⟩ := existsTasks_trace _ _ _ _ childrenComplete splitTrace
    constructor
    · intro read
      rw [result_eq] at read
      apply positive
      cases reply <;> exact read
    · intro read
      rw [result_eq] at read
      apply negative
      cases reply <;> exact read

theorem positive_saved_split {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (index : Nat) (left right : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.separating index left right) source sourceAdmitted budget).outcome.answer = some true) :
    ∃ parts listed,
      Evidence.separation (SpatialObservation.mk index source parts listed []) ∈
        (run backend leaves (.separating index left right) source sourceAdmitted budget).observations ∧
      denotation leaves left backend.spatial.theory parts.1 ∧
      denotation leaves right backend.spatial.theory parts.2 :=
  (separation_trace_evidence backend leaves index left right source sourceAdmitted
    (run_trace backend leaves _ source sourceAdmitted budget ⟨true, read⟩)).1 read

theorem negative_saved_split_coverage {system : GSLT.{u}} {admitted : system.Term → Prop}
    {Leaf : Type w} (backend : CursorBackend.{u,v} system admitted)
    (leaves : Leaf → LeafBackend system admitted) (index : Nat) (left right : Formula Leaf)
    (source : system.Term) (sourceAdmitted : admitted source) (budget : Nat)
    (read : (run backend leaves (.separating index left right) source sourceAdmitted budget).outcome.answer = some false) :
    ∀ parts listed,
      Evidence.separation (SpatialObservation.mk index source parts listed []) ∈
        (run backend leaves (.separating index left right) source sourceAdmitted budget).observations ∧
      ¬ (denotation leaves left backend.spatial.theory parts.1 ∧
         denotation leaves right backend.spatial.theory parts.2) :=
  (separation_trace_evidence backend leaves index left right source sourceAdmitted
    (run_trace backend leaves _ source sourceAdmitted budget ⟨false, read⟩)).2 read

end Mettapedia.OSLF.NativeTypes.Decision.Machine

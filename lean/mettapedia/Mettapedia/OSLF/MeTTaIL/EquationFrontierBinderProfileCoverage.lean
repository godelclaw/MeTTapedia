import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
import Mettapedia.OSLF.Framework.FiniteEquationCoverage

/-!
# Complete equation and occurrence coverage for the binder family

The finite certificate is constructed for every ambient-indexed state and
every finite provider snapshot. Its closure is checked by the shared checker.
The independent event relation retains authored declarations and provider-row
origins; endpoint and modal readouts are obtained only after both independent
coverage proofs have been earned.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open Mettapedia.OSLF.Framework.FiniteEquationCoverage

def certificate {ambient : Nat} (allowed : List Token) (state : State ambient) :
    Certificate (State ambient) where
  walks := (neighbors allowed state).map fun neighbor => [neighbor]

theorem certificate_checked {ambient : Nat} (allowed : List Token)
    (state : State ambient) :
    (certificate allowed state).check (neighbors allowed) state = true := by
  cases state with
  | mk phase name key =>
    cases phase <;> by_cases admitted : key ∈ allowed <;>
      simp [certificate, Certificate.check, Certificate.representatives,
        checkWalk, walkEnd, checkClosure, neighbors, admitted, opposite]

/-- The two represented presentations are the entire independently generated
equation class. Arbitrarily long conversion proofs add no missing state. -/
theorem representatives_complete {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    target ∈ (certificate allowed source).representatives source ↔
      Relation.EqvGen (EquationEdge allowed) source target :=
  representatives_spec (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (certificate allowed source) source
    (certificate_checked allowed source) target

structure Event (ambient : Nat) where
  origin : Origin
  target : State ambient
  deriving DecidableEq, Repr

def occurrences {ambient : Nat} (allowed : List Token)
    (source : State ambient) : List (Event ambient) :=
  match source.phase with
  | .exposed =>
      (List.finRange 2).flatMap fun declaration =>
        (allowed.zipIdx.filter fun row => row.1 == source.key).map fun row =>
          { origin := ⟨declaration, row.2⟩
            target := { source with phase := .finished } }
  | _ => []

def Enabled {ambient : Nat} (allowed : List Token)
    (source : State ambient) (event : Event ambient) : Prop :=
  Firing allowed source event.origin event.target

theorem occurrences_spec {ambient : Nat} (allowed : List Token)
    (source : State ambient) (event : Event ambient) :
    event ∈ occurrences allowed source ↔ Enabled allowed source event := by
  constructor
  · intro present
    cases source with
    | mk phase name key =>
      cases phase with
      | tucked => simp [occurrences] at present
      | finished => simp [occurrences] at present
      | exposed =>
        simp only [occurrences, List.mem_flatMap, List.mem_map] at present
        obtain ⟨declaration, _, ⟨rowKey, rowIndex⟩, member, represented⟩ := present
        obtain ⟨row, keyEq⟩ := List.mem_filter.mp member
        have keyEq : rowKey = key := by simpa using keyEq
        subst rowKey
        cases represented
        exact .consume name key declaration rowIndex
          (List.mk_mem_zipIdx_iff_getElem?.mp row)
  · intro enabled
    rcases event with ⟨origin, target⟩
    change Firing allowed source origin target at enabled
    cases enabled with
    | consume name key declaration rowIndex provided =>
      simp only [occurrences, List.mem_flatMap, List.mem_map]
      refine ⟨declaration, by simp, (key, rowIndex), ?_, rfl⟩
      exact List.mem_filter.mpr
        ⟨List.mk_mem_zipIdx_iff_getElem?.mpr provided, by simp⟩

def frontier {ambient : Nat} (allowed : List Token) (source : State ambient) :
    List (State ambient × Event ambient) :=
  occurrenceFrontier (certificate allowed source) source (occurrences allowed)

theorem frontier_occurrence_spec {ambient : Nat} (allowed : List Token)
    (source representative : State ambient) (event : Event ambient) :
    (representative, event) ∈ frontier allowed source ↔
      Relation.EqvGen (EquationEdge allowed) source representative ∧
        Enabled allowed representative event :=
  occurrenceFrontier_spec (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (Enabled allowed) (occurrences allowed)
    (occurrences_spec allowed) (certificate allowed source) source
    (certificate_checked allowed source) representative event

def Step {ambient : Nat} (allowed : List Token) : State ambient → State ambient → Prop :=
  ModuloStep (EquationEdge allowed) (Enabled allowed) Event.target

theorem frontier_target_classes {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Quotient.mk (Relation.EqvGen.setoid (EquationEdge allowed)) target ∈
      classFrontier (EquationEdge allowed) (occurrences allowed) Event.target
        (certificate allowed source) source ↔ Step allowed source target :=
  classFrontier_spec (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (Enabled allowed) (occurrences allowed)
    (occurrences_spec allowed) Event.target (certificate allowed source) source
    (certificate_checked allowed source) target

theorem frontier_diamond {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (endpoints Event.target (frontier allowed source)).any test = true ↔
      ∃ target, Step allowed source target ∧ test target = true :=
  any_iff_outgoingDiamond (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (Enabled allowed) (occurrences allowed)
    (occurrences_spec allowed) Event.target (certificate allowed source) source
    (certificate_checked allowed source) test invariant

theorem frontier_outgoing_universal {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : State ambient → Bool)
    (invariant : ∀ before after, Relation.EqvGen (EquationEdge allowed) before after →
      test before = test after) :
    (endpoints Event.target (frontier allowed source)).all test = true ↔
      ∀ target, Step allowed source target → test target = true :=
  all_iff_outgoingUniversal (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (Enabled allowed) (occurrences allowed)
    (occurrences_spec allowed) Event.target (certificate allowed source) source
    (certificate_checked allowed source) test invariant

theorem frontier_empty_iff {ambient : Nat} (allowed : List Token)
    (source : State ambient) :
    frontier allowed source = [] ↔ ¬ ∃ target, Step allowed source target :=
  empty_iff_no_step (EquationEdge allowed) (neighbors allowed)
    (neighbors_spec allowed) (Enabled allowed) (occurrences allowed)
    (occurrences_spec allowed) Event.target (certificate allowed source) source
    (certificate_checked allowed source)

/-- A binding equation can expose a directed redex without itself contributing
an event. The two authored occurrences have the same target and distinct origins. -/
theorem tucked_frontier {ambient : Nat} (name : Fin (ambient + 1)) :
    frontier [.permit] ⟨.tucked, name, .permit⟩ =
      [(⟨.exposed, name, .permit⟩,
         ⟨⟨⟨0, by omega⟩, 0⟩, ⟨.finished, name, .permit⟩⟩),
       (⟨.exposed, name, .permit⟩,
         ⟨⟨⟨1, by omega⟩, 0⟩, ⟨.finished, name, .permit⟩⟩)] := by
  simp [frontier, occurrenceFrontier, certificate, Certificate.representatives,
    neighbors, opposite, walkEnd, occurrences, List.finRange_succ,
    List.eraseDups_cons]

theorem failed_query_has_no_step {ambient : Nat} (name : Fin (ambient + 1)) :
    ¬ ∃ target, Step [.permit] ⟨.tucked, name, .revoked⟩ target := by
  apply (frontier_empty_iff [.permit] ⟨.tucked, name, .revoked⟩).mp
  simp [frontier, occurrenceFrontier, certificate, Certificate.representatives,
    neighbors, occurrences]

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

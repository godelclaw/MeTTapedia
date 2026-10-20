import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

open Mettapedia.OSLF.Framework

/-!
# Ordered guard admission and actual premise execution

The finite guard witnesses have the same existence criterion as the
independent premise execution. Every successful nullary query retains its
original row index and the ordered premise event. The complete assignment
is unchanged, while the actual context advances its authored premise index.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)

theorem nullary_query_traced {environment : Environment} {context : Context}
    {relation : String} {initial : Assignment} {index : Nat}
    (query : QueryHolds environment context relation [] initial index initial) :
    TracedQuery environment context relation [] initial index initial [] := by
  cases query with
  | row selected declared rowTyped arguments finalTyped =>
    have valuesEmpty := (arguments_nil_readout arguments).1
    have modesEmpty := (arguments_nil_readout arguments).2.1
    refine .row selected declared rowTyped ?_ finalTyped
    rw [valuesEmpty, modesEmpty]
    exact .nil
  | dynamicRow registered declared inputs source found rowTyped arguments finalTyped =>
    have valuesEmpty := (arguments_nil_readout arguments).1
    have modesEmpty := (arguments_nil_readout arguments).2.1
    refine .dynamicRow registered declared inputs source found rowTyped ?_ finalTyped
    rw [valuesEmpty, modesEmpty]
    exact .nil

theorem nullary_query_final {environment : Environment} {context : Context}
    {relation : String} {initial final : Assignment} {index : Nat}
    (query : QueryHolds environment context relation [] initial index final) : final = initial := by
  cases query with
  | row _ _ _ arguments _ => exact (arguments_nil_readout arguments).2.2
  | dynamicRow _ _ _ _ _ _ arguments _ => exact (arguments_nil_readout arguments).2.2

/-- Guard admission reads only the static rows, so it agrees with premise
execution when no guarded relation is served by a registered dynamic provider. -/
theorem enabled_iff_premises_execute {environment : Environment} {index : Nat}
    {premises : List Premise} {witnesses : List Witness}
    (original : GuardedBy environment.provider index premises witnesses)
    (unregistered : ∀ witness ∈ witnesses, witness.relation ∉ environment.provider.dynamicRelations)
    (context : Context) (initial : Assignment) (typed : TypedAssignment environment context initial) :
    enabled witnesses = true ↔
      ∃ events, PremisesHold environment context premises initial initial events := by
  induction original generalizing context with
  | nil _ =>
    constructor
    · intro _; exact ⟨[], .nil⟩
    · intro _; rfl
  | @cons index relation premises originals witnesses declared rowsRead more ih =>
    have read : enabled ({premise := index, relation := relation, rows := originals} :: witnesses) = true ↔
        originals.isEmpty = false ∧ enabled witnesses = true := by
      cases empty : originals.isEmpty <;> simp [enabled, empty]
    rw [read]
    have headUnregistered : relation ∉ environment.provider.dynamicRelations :=
      unregistered _ List.mem_cons_self
    have tailUnregistered : ∀ witness ∈ witnesses,
        witness.relation ∉ environment.provider.dynamicRelations :=
      fun witness member => unregistered witness (List.mem_cons_of_mem _ member)
    constructor
    · rintro ⟨nonempty, restEnabled⟩
      obtain ⟨rowIndex, member⟩ := List.exists_mem_of_ne_nil originals (List.isEmpty_eq_false_iff.mp nonempty)
      have held : QueryHolds environment context relation [] initial rowIndex initial :=
        (nullary_query_exact environment context relation initial typed rowIndex headUnregistered).mpr
          ⟨declared, rowsRead ▸ member⟩
      obtain ⟨events, tail⟩ := (ih tailUnregistered context.next typed).mp restEnabled
      exact ⟨.query context.premiseIndex context.quantifierDepth rowIndex [] :: events,
        .cons (.query (nullary_query_traced held)) tail⟩
    · rintro ⟨events, execution⟩
      cases execution with
      | cons head tail =>
        cases head with
        | query query =>
          have same := nullary_query_final query.readout
          subst_vars
          have existsRow :=
            (nullary_query_exact environment context relation _ typed _ headUnregistered).mp query.readout
          refine ⟨?_, (ih tailUnregistered context.next typed).mpr ⟨_, tail⟩⟩
          exact List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem existsRow.2)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

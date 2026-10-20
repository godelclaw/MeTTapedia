import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerRenaming

open Mettapedia.OSLF.Framework

/-!
# Finite guards from an actual provider snapshot

A nullary relation query has no term arguments or output assignments. Its
ordered witnesses are the original provider row indices. Missing or ambiguous
signatures remain unresolved; an admitted empty relation is a decided failure.
The comparison is with the actual independently specified premise semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)

def rows (provider : ProviderSnapshot) (relation : String) : List Nat :=
  provider.rows.zipIdx.filterMap fun entry =>
    if entry.1.relation == relation && entry.1.values.isEmpty then some entry.2 else none

def query? (provider : ProviderSnapshot) (relation : String) : Option (List Nat) :=
  match signature? provider relation 0 with
  | none => none
  | some _ => some (rows provider relation)

theorem row_mem_iff (provider : ProviderSnapshot) (relation : String) (index : Nat) :
    index ∈ rows provider relation ↔
      ∃ row, provider.rows[index]? = some row ∧ row.relation = relation ∧ row.values = [] := by
  simp only [rows, List.mem_filterMap]
  constructor
  · rintro ⟨⟨row, position⟩, original, selected⟩
    split at selected
    · rename_i admitted
      cases Option.some.inj selected
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at admitted
      exact ⟨row, List.mk_mem_zipIdx_iff_getElem?.mp original, admitted⟩
    · cases selected
  · rintro ⟨row, found, same, empty⟩
    exact ⟨(row, index), List.mk_mem_zipIdx_iff_getElem?.mpr found,
      by simp [same, empty]⟩

theorem query?_some_iff (provider : ProviderSnapshot) (relation : String) (indices : List Nat) :
    query? provider relation = some indices ↔
      (∃ signature, signature? provider relation 0 = some signature) ∧
        indices = rows provider relation := by
  unfold query?
  cases found : signature? provider relation 0 with
  | none => simp
  | some signature => simp [eq_comm]

theorem arguments_nil_readout {context : Context} {index : Nat} {initial final : Assignment}
    {values : List Pattern} {modes : List RelationArgMode}
    (arguments : ArgumentsHold context index initial [] values modes final) :
    values = [] ∧ modes = [] ∧ final = initial := by
  cases arguments
  exact ⟨rfl, rfl, rfl⟩

/-- The static row table decides a nullary query only for a relation that is
not served by a registered dynamic provider; a dynamic relation can hold at a
native row index past the static rows. -/
theorem nullary_query_exact (environment : Environment) (context : Context)
    (relation : String) (initial : Assignment) (typed : TypedAssignment environment context initial)
    (index : Nat) (unregistered : relation ∉ environment.provider.dynamicRelations) :
    QueryHolds environment context relation [] initial index initial ↔
      (∃ signature, signature? environment.provider relation 0 = some signature) ∧
        index ∈ rows environment.provider relation := by
  constructor
  · intro held
    cases held with
    | row found signature typedRow arguments _ =>
      have valuesEmpty := (arguments_nil_readout arguments).1
      refine ⟨⟨_, signature⟩, (row_mem_iff _ _ _).mpr ⟨_, found, ?_, valuesEmpty⟩⟩
      exact typedRow.1.trans (signature?_readout _ _ _ _ signature).2.1
    | dynamicRow registered _ _ _ _ _ _ _ => exact absurd registered unregistered
  · rintro ⟨⟨signature, selected⟩, member⟩
    obtain ⟨row, found, same, empty⟩ := (row_mem_iff _ _ _).mp member
    obtain ⟨_, relationRead, typesLength, modesLength⟩ := signature?_readout _ _ _ _ selected
    have typesEmpty : signature.argumentTypes = [] := List.length_eq_zero_iff.mp typesLength
    have modesEmpty : signature.modes = [] := List.length_eq_zero_iff.mp modesLength
    refine QueryHolds.row found selected ?_ ?_ typed
    · exact ⟨same.trans relationRead.symm, by rw [empty, typesEmpty]; exact .nil⟩
    · rw [empty, modesEmpty]
      exact .nil

structure Witness where
  premise : Nat
  relation : String
  rows : List Nat
  deriving DecidableEq, Repr

def guardsFrom? (provider : ProviderSnapshot) : Nat → List Premise → Option (List Witness)
  | _, [] => some []
  | index, .relationQuery relation [] :: tail => do
      let originals ← query? provider relation
      let rest ← guardsFrom? provider (index + 1) tail
      pure ({premise := index, relation := relation, rows := originals} :: rest)
  | _, _ => none

def guards? (provider : ProviderSnapshot) (premises : List Premise) : Option (List Witness) :=
  guardsFrom? provider 0 premises

def enabled (witnesses : List Witness) : Bool :=
  witnesses.all fun witness => !witness.rows.isEmpty

inductive GuardedBy (provider : ProviderSnapshot) : Nat → List Premise → List Witness → Prop where
  | nil (index : Nat) : GuardedBy provider index [] []
  | cons {index : Nat} {relation : String} {premises : List Premise}
      {originals : List Nat} {tail : List Witness} :
      (∃ signature, signature? provider relation 0 = some signature) →
      originals = rows provider relation →
      GuardedBy provider (index + 1) premises tail →
      GuardedBy provider index (.relationQuery relation [] :: premises)
        ({premise := index, relation := relation, rows := originals} :: tail)

theorem guardsFrom?_exact (provider : ProviderSnapshot) (index : Nat) (premises : List Premise)
    (witnesses : List Witness) :
    guardsFrom? provider index premises = some witnesses ↔ GuardedBy provider index premises witnesses := by
  induction premises generalizing index witnesses with
  | nil =>
    constructor
    · intro computed
      cases Option.some.inj computed
      exact .nil _
    · intro admitted
      cases admitted
      rfl
  | cons premise premises ih =>
    constructor
    · intro computed
      cases premise with
      | freshness _ => cases computed
      | congruence _ _ => cases computed
      | scopedStep _ => cases computed
      | forAll _ _ _ => cases computed
      | relationQuery relation arguments =>
        cases arguments with
        | cons _ _ => cases computed
        | nil =>
          simp only [guardsFrom?, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def] at computed
          obtain ⟨originals, chosen, tail, more, same⟩ := computed
          cases Option.some.inj same
          obtain ⟨signature, original⟩ := (query?_some_iff _ _ _).mp chosen
          exact .cons signature original ((ih _ _).mp more)
    · intro admitted
      cases admitted with
      | cons signature original tail =>
        rw [guardsFrom?, (query?_some_iff _ _ _).mpr ⟨signature, original⟩,
          show (some _) >>= _ = _ from rfl]
        rw [(ih _ _).mpr tail]
        rfl

theorem guards?_exact (provider : ProviderSnapshot) (premises : List Premise)
    (witnesses : List Witness) :
    guards? provider premises = some witnesses ↔ GuardedBy provider 0 premises witnesses :=
  guardsFrom?_exact provider 0 premises witnesses

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards

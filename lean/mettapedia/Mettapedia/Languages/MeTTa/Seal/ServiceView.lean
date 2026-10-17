import Mettapedia.Languages.MeTTa.Seal.NativeContract

/-!
# A space reader is a distinct service facet

This is the result boundary after `NativeContract.invokeKeyed` authenticates
the offered key and checks current policy. Giving a caller the general opener
also permits raw payload access; merely offering a snapshot operation does
not attenuate that caller. A separate reader facet rejects raw opening.

Snapshots use the existing portable codec. Copying a row can retain a nested
space, state cell or seal, so copying alone is not a read-only boundary. The
datum predicate remains responsible for rejecting native reference kinds.
The source space stays live and other aliases remain usable. No atomicity
under concurrent space mutation, revocation of existing aliases, or native
memory-management theorem is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal.ServiceView

open NativeContract

inductive Facet where
  | opener | reader
  deriving DecidableEq, Repr

inductive Request where
  | open | readSpace
  deriving DecidableEq, Repr

inductive Output (D : Type) where
  | raw (value : Value D)
  | snapshot (rows : List (Wire D))

inductive Result (D : Type) where
  | value (output : Output D)
  | empty
  | denied
  | notPortable

/-- An all-or-nothing snapshot: no partial result is returned when any row
contains an authority object or a datum rejected by the native codec. -/
def encodeRows {D : Type} (admitDatum : D → Bool) : List (Value D) → Option (List (Wire D))
  | [] => some []
  | value :: rest =>
      match serialize admitDatum value, encodeRows admitDatum rest with
      | some encoded, some following => some (encoded :: following)
      | _, _ => none

/-- Trusted dispatch after key/policy recognition. `rowsOf` is the host's
space observation, not a caller-supplied authority-minting function. -/
def present {D : Type} (admitDatum : D → Bool)
    (rowsOf : Value D → Option (List (Value D)))
    (facet : Facet) (request : Request) (payload : Value D) : Result D :=
  match facet, request with
  | .reader, .open => .denied
  | .opener, .open => .value (.raw payload)
  | _, .readSpace =>
      match rowsOf payload with
      | none => .empty
      | some rows => match encodeRows admitDatum rows with
        | none => .notPortable
        | some encoded => .value (.snapshot encoded)

theorem encodeRows_members {D : Type} {admitDatum : D → Bool}
    {rows : List (Value D)} {encoded : List (Wire D)}
    (accepted : encodeRows admitDatum rows = some encoded) :
    ∀ wire ∈ encoded, ∃ value ∈ rows, serialize admitDatum value = some wire := by
  induction rows generalizing encoded with
  | nil => cases accepted; simp
  | cons value rest ih =>
      cases first : serialize admitDatum value with
      | none => simp [encodeRows, first] at accepted
      | some wire =>
          cases following : encodeRows admitDatum rest with
          | none => simp [encodeRows, first, following] at accepted
          | some tail =>
              simp only [encodeRows, first, following,
                Option.some.injEq] at accepted
              subst encoded
              intro next member
              rcases List.mem_cons.mp member with same | later
              · subst next
                exact ⟨value, by simp, first⟩
              · obtain ⟨retained, found, encoded⟩ := ih following next later
                exact ⟨retained, List.mem_cons_of_mem _ found, encoded⟩

/-- Every returned row decodes to a portable value, so it carries neither
explicit seal authority nor any datum kind excluded by the codec. -/
theorem encodeRows_portable {D : Type} {admitDatum : D → Bool}
    {rows : List (Value D)} {encoded : List (Wire D)}
    (accepted : encodeRows admitDatum rows = some encoded) :
    ∀ wire ∈ encoded, ∃ value, decode admitDatum wire = some value ∧
      Portable admitDatum value ∧
      ∀ brand right, ¬ value.erase.hasCap brand right := by
  intro wire member
  obtain ⟨value, _, serialized⟩ := encodeRows_members accepted wire member
  have decoded := decode_serialized admitDatum value wire serialized
  have portable := decoded_portable admitDatum wire value decoded
  exact ⟨value, decoded, portable, fun brand right => portable.no_authority brand right⟩

theorem reader_never_opens {D : Type} (admitDatum : D → Bool)
    (rowsOf : Value D → Option (List (Value D))) (payload : Value D) :
    present admitDatum rowsOf .reader .open payload = .denied := rfl

theorem snapshot_contains_only_portable_rows {D : Type} {admitDatum : D → Bool}
    {rowsOf : Value D → Option (List (Value D))} {facet : Facet} {payload : Value D}
    {encoded : List (Wire D)}
    (accepted : present admitDatum rowsOf facet .readSpace payload = .value (.snapshot encoded)) :
    ∀ wire ∈ encoded, ∃ value, decode admitDatum wire = some value ∧ Portable admitDatum value := by
  cases facet <;> simp only [present] at accepted
  all_goals
    cases observed : rowsOf payload with
    | none => simp [observed] at accepted
    | some rows =>
        cases result : encodeRows admitDatum rows with
        | none => simp [observed, result] at accepted
        | some actual =>
            simp only [observed, result, Result.value.injEq, Output.snapshot.injEq] at accepted
            subst encoded
            intro wire member
            obtain ⟨value, decoded, portable, _⟩ := encodeRows_portable result wire member
            exact ⟨value, decoded, portable⟩

namespace Controls

inductive Datum where
  | text (content : String)
  | space (identity : Nat)
  deriving DecidableEq, Repr

def admits : Datum → Bool
  | .text _ => true
  | .space _ => false

def source : Value Datum := .data (.space 7)
def ordinary : Value Datum := .data (.text "fact")
def observes : Value Datum → Option (List (Value Datum))
  | .data (.space 7) => some [ordinary]
  | _ => none

/-- The delivered service used the opener for both calls. The same facet
which successfully reads the rows can therefore recover the raw live space. -/
theorem general_user_is_not_a_restricted_reader :
    present admits observes .opener .readSpace source =
        .value (.snapshot [.data (.text "fact")]) ∧
      present admits observes .opener .open source = .value (.raw source) := by
  constructor <;> rfl

theorem reader_keeps_snapshot_access_without_raw_access :
    present admits observes .reader .readSpace source =
        .value (.snapshot [.data (.text "fact")]) ∧
      present admits observes .reader .open source = .denied := by
  constructor <;> rfl

/-- A copied ordinary pair can still carry a live space descriptor. The
existing recursive codec detects it, even when the outer row looks like data. -/
theorem nested_reference_refused :
    encodeRows admits [.pair ordinary source] = none := rfl

theorem nested_seal_refused (brand : Brand) (rights : Rights) :
    encodeRows admits [.pair ordinary (.cap brand rights)] = none := rfl

end Controls

#print axioms encodeRows_members
#print axioms encodeRows_portable
#print axioms snapshot_contains_only_portable_rows
#print axioms Controls.general_user_is_not_a_restricted_reader
#print axioms Controls.nested_reference_refused

end Mettapedia.Languages.MeTTa.Seal.ServiceView

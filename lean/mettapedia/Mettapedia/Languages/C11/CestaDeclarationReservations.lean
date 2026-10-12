import Mettapedia.Languages.C11.CestaIntegerDeclarations
import Mettapedia.Languages.C11.IntegerObjectSequences

/-!
# Checked Cesta declarations reserving integer object lifetimes

The selected declaration is elaborated, each explicit allocation choice is
paired with its source declaration, and every object is constructed through
the checked byte-memory allocator. All reserved objects begin indeterminate,
even when the source declaration retains a zero initializer descriptor.
Identifier visibility and initializer execution remain later source events.
This separation matches the lifetime/initializer distinction needed for
non-VLA block entry without identifying reservation with a reached C
declaration statement.

General correspondence composes independent sorted syntax, declaration
reading, allocation-choice pairing and heap creation judgments. Layout
selection is explicit and each chosen size is checked against the integer
memory model. The adapter does not assume native stack, allocator or ABI
correspondence. Joining reservation to the complete statement/control machine
and scheduling every non-VLA declaration at block entry are further source
composition obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaDeclarationReservations

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
  (Schema Notation Sorted encode? decode? decode_sorted encode_decoded decode_encoded)
open CestaIntegerDeclarations IntegerObjectConstruction IntegerObjectSequences
open Mettapedia.Machines.CMemory (BlockId)

abbrev LayoutSelection := IntegerType IntegerExtension → ObjectLayout.Layout

def requests? (layouts : LayoutSelection) : List Entry → List BlockId → Option (List Request)
  | [], [] => some []
  | entry :: rest, identity :: identities => do
      let following ← requests? layouts rest identities
      some (⟨entry.declaration, layouts entry.declaration.integer, identity, .indeterminate⟩ :: following)
  | _, _ => none

inductive Requests (layouts : LayoutSelection) : List Entry → List BlockId → List Request → Prop where
  | empty : Requests layouts [] [] []
  | cons (entry : Entry) (entries : List Entry) (identity : BlockId) (identities : List BlockId)
      (requests : List Request) (following : Requests layouts entries identities requests) :
      Requests layouts (entry :: entries) (identity :: identities)
        (⟨entry.declaration, layouts entry.declaration.integer, identity, .indeterminate⟩ :: requests)

theorem requests_complete (layouts : LayoutSelection) (entries : List Entry) (identities : List BlockId)
    (requests : List Request) (paired : Requests layouts entries identities requests) :
    requests? layouts entries identities = some requests := by
  induction paired with
  | empty => rfl
  | cons entry entries identity identities requests following ih =>
      simp only [requests?, ih, bind, Option.bind_some]

theorem requests_sound (layouts : LayoutSelection) (entries : List Entry) (identities : List BlockId)
    (requests : List Request) (paired : requests? layouts entries identities = some requests) :
    Requests layouts entries identities requests := by
  induction entries generalizing identities requests with
  | nil =>
      cases identities with
      | nil => cases paired; exact .empty
      | cons => cases paired
  | cons entry entries ih =>
      cases identities with
      | nil => cases paired
      | cons identity identities =>
          simp only [requests?, bind, Option.bind_eq_some_iff, Option.some.injEq] at paired
          obtain ⟨following, paired, rfl⟩ := paired
          exact .cons _ _ _ _ _ (ih _ _ paired)

theorem Requests.identities (layouts : LayoutSelection) (entries : List Entry) (identities : List BlockId)
    (requests : List Request) (paired : Requests layouts entries identities requests) :
    requests.map Request.identity = identities := by
  induction paired with
  | empty => rfl
  | cons entry entries identity identities requests following ih => simp only [List.map_cons, ih]

theorem Requests.indeterminate (layouts : LayoutSelection) (entries : List Entry) (identities : List BlockId)
    (requests : List Request) (paired : Requests layouts entries identities requests)
    (request : Request) (member : request ∈ requests) : request.contents = .indeterminate := by
  induction paired with
  | empty => cases member
  | cons entry entries identity identities requests following ih =>
      rcases List.mem_cons.mp member with same | followingMember
      · subst request; rfl
      · exact ih followingMember

structure Reserved (model : IntegerMemoryModel.Model) where
  entries : List Entry
  objects : Prepared model
  deriving DecidableEq, Repr

def reserveTerm (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (layouts : LayoutSelection) (identities : List BlockId) (term : CanonicalTerm) :
    Option (Reserved model) := do
  let entries ← CestaIntegerDeclarations.readTerm model term
  let requests ← requests? layouts entries identities
  let objects ← IntegerObjectSequences.construct model memory arrays requests
  some ⟨entries, objects⟩

def Reservation (model : IntegerMemoryModel.Model) (before : ObjectAccessMemory.SemanticState model.characters)
    (arrays : ArrayPointers.Catalog) (layouts : LayoutSelection) (identities : List BlockId) (term : CanonicalTerm)
    (entries : List Entry) (after : ObjectAccessMemory.SemanticState model.characters)
    (nextArrays : ArrayPointers.Catalog) (locations : List ObjectAccessMemory.Lvalue) : Prop :=
  ∃ requests, CestaIntegerDeclarations.Reading model term entries ∧ Requests layouts entries identities requests ∧
    CreationSequence model before arrays requests after nextArrays locations

theorem reserveTerm_sound (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (layouts : LayoutSelection) (identities : List BlockId) (term : CanonicalTerm)
    (result : Reserved model) (computed : reserveTerm model memory arrays layouts identities term = some result) :
    Reservation model (ObjectAccessMemory.represent memory) arrays layouts identities term result.entries
      (ObjectAccessMemory.represent result.objects.memory) result.objects.arrays result.objects.locations := by
  simp only [reserveTerm, bind, Option.bind_eq_some_iff, Option.some.injEq] at computed
  obtain ⟨entries, read, requests, paired, objects, created, rfl⟩ := computed
  exact ⟨requests, readTerm_sound _ _ _ read, requests_sound _ _ _ _ paired,
    IntegerObjectSequences.construct_sound _ _ _ _ _ created⟩

theorem reserveTerm_complete (model : IntegerMemoryModel.Model) (memory : ObjectAccessMemory.State model.characters)
    (arrays : ArrayPointers.Catalog) (layouts : LayoutSelection) (identities : List BlockId) (term : CanonicalTerm)
    (entries : List Entry) (after : ObjectAccessMemory.SemanticState model.characters)
    (nextArrays : ArrayPointers.Catalog) (locations : List ObjectAccessMemory.Lvalue)
    (reserved : Reservation model (ObjectAccessMemory.represent memory) arrays layouts identities term entries
      after nextArrays locations) : ∃ result,
    reserveTerm model memory arrays layouts identities term = some result ∧ result.entries = entries ∧
      ObjectAccessMemory.represent result.objects.memory = after ∧ result.objects.arrays = nextArrays ∧
      result.objects.locations = locations := by
  obtain ⟨requests, reading, paired, creation⟩ := reserved
  obtain ⟨objects, created, memory, arrays, locations⟩ := IntegerObjectSequences.construct_complete _ _ _ _ _ _ _ creation
  refine ⟨⟨entries, objects⟩, ?_, rfl, memory, arrays, locations⟩
  simp only [reserveTerm, readTerm_complete _ _ _ reading, requests_complete _ _ _ _ paired,
    created, bind, Option.bind_some]

def reserve (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (layouts : LayoutSelection) (identities : List BlockId) (wire : CestaObjectAccess.Wire) : Option (Reserved model) := do
  reserveTerm model memory arrays layouts identities (← decode? schema codecProfile sort wire)

def WireReservation (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (before : ObjectAccessMemory.SemanticState model.characters) (arrays : ArrayPointers.Catalog)
    (layouts : LayoutSelection) (identities : List BlockId) (wire : CestaObjectAccess.Wire) (entries : List Entry)
    (after : ObjectAccessMemory.SemanticState model.characters) (nextArrays : ArrayPointers.Catalog)
    (locations : List ObjectAccessMemory.Lvalue) : Prop :=
  ∃ term, Sorted schema codecProfile sort term ∧ encode? schema codecProfile sort term = some wire ∧
    Reservation model before arrays layouts identities term entries after nextArrays locations

theorem reserve_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (layouts : LayoutSelection) (identities : List BlockId) (wire : CestaObjectAccess.Wire) (result : Reserved model)
    (computed : reserve schema codecProfile sort model memory arrays layouts identities wire = some result) :
    WireReservation schema codecProfile sort model (ObjectAccessMemory.represent memory) arrays layouts identities wire
      result.entries (ObjectAccessMemory.represent result.objects.memory) result.objects.arrays result.objects.locations := by
  simp only [reserve, bind, Option.bind_eq_some_iff] at computed
  obtain ⟨term, decoded, reserved⟩ := computed
  exact ⟨term, decode_sorted _ _ _ _ _ decoded, encode_decoded _ _ _ _ _ decoded,
    reserveTerm_sound _ _ _ _ _ _ _ reserved⟩

theorem reserve_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (memory : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (layouts : LayoutSelection) (identities : List BlockId) (wire : CestaObjectAccess.Wire) (entries : List Entry)
    (after : ObjectAccessMemory.SemanticState model.characters) (nextArrays : ArrayPointers.Catalog)
    (locations : List ObjectAccessMemory.Lvalue)
    (reserved : WireReservation schema codecProfile sort model (ObjectAccessMemory.represent memory) arrays layouts identities wire
      entries after nextArrays locations) : ∃ result,
    reserve schema codecProfile sort model memory arrays layouts identities wire = some result ∧ result.entries = entries ∧
      ObjectAccessMemory.represent result.objects.memory = after ∧ result.objects.arrays = nextArrays ∧
      result.objects.locations = locations := by
  obtain ⟨term, _, encoded, reservation⟩ := reserved
  obtain ⟨result, computed, entries, memory, arrays, locations⟩ := reserveTerm_complete _ _ _ _ _ _ _ _ _ _ reservation
  exact ⟨result, by simp only [reserve, decode_encoded _ _ _ _ _ encoded, bind, Option.bind_some, computed],
    entries, memory, arrays, locations⟩

end Mettapedia.Languages.C11.CestaDeclarationReservations

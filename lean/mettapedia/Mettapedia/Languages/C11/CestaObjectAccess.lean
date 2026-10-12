import Mettapedia.Languages.C11.ScopedLvalues
import Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec

/-!
# Sorted C identifier data connected to object accesses

Cesta's `Var` constructor retains one ordinary-name token. This adapter uses
the existing schema-indexed codec, preserving the full schema and codecProfile
policy instead of introducing a replacement identifier-only grammar.
Successful admission constructs the sorted source term, its exact encoded
form, scoped binding evidence and independent typed memory judgment.

The source term here is one identifier lvalue in the pure whole-object
integer profile. The native byte reader, scope/type elaborator, full expression
machine and implementation fidelity of the exported schema are separate
obligations. Stores receive an already evaluated, admitted integer value;
they do not erase evaluation of a C assignment's other operands.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaObjectAccess

open ObjectAccessMemory
open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec

abbrev Wire := Mettapedia.Languages.MeTTa.OSLFCore.Atom

inductive Identifier : CanonicalTerm → String → Prop where
  | var (name : String) : Identifier (.node "Var" [.text name]) name

def identifierName : CanonicalTerm → Option String
  | .node head [.text name] => if head = "Var" then some name else none
  | _ => none

theorem identifier_sound (term : CanonicalTerm) (name : String)
    (accepted : identifierName term = some name) : Identifier term name := by
  cases term with
  | text => simp [identifierName] at accepted
  | seq => simp [identifierName] at accepted
  | node head children =>
      cases children with
      | nil => simp [identifierName] at accepted
      | cons first rest =>
          cases rest with
          | cons => simp [identifierName] at accepted
          | nil =>
              cases first with
              | node => simp [identifierName] at accepted
              | seq => simp [identifierName] at accepted
              | text spelling =>
                  by_cases var : head = "Var"
                  · subst head
                    simp only [identifierName, ↓reduceIte, Option.some.injEq] at accepted
                    subst name
                    exact .var spelling
                  · simp [identifierName, var] at accepted

theorem identifier_complete (term : CanonicalTerm) (name : String) (identifier : Identifier term name) :
    identifierName term = some name := by
  cases identifier
  simp [identifierName]

def read (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (environment : ScopedLvalues.Environment) (wire : Wire) :
    Option IntegerObject.Outcome := do
  let term ← decode? schema codecProfile sort wire
  let name ← identifierName term
  ScopedLvalues.read layout state environment name

def Reading (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (outcome : IntegerObject.Outcome) : Prop :=
  ∃ term name, Sorted schema codecProfile sort term ∧ encode? schema codecProfile sort term = some wire ∧
    Identifier term name ∧ ScopedLvalues.Reading layout state environment name outcome

theorem read_sound (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (outcome : IntegerObject.Outcome) (executed : read schema codecProfile sort layout state environment wire = some outcome) :
    Reading schema codecProfile sort layout (represent state) environment wire outcome := by
  cases decoded : decode? schema codecProfile sort wire with
  | none => simp [read, decoded] at executed
  | some term =>
      cases identifier : identifierName term with
      | none => simp [read, decoded, identifier] at executed
      | some name =>
          refine ⟨term, name, decode_sorted _ _ _ _ _ decoded,
            encode_decoded _ _ _ _ _ decoded, identifier_sound _ _ identifier, ?_⟩
          exact (ScopedLvalues.read_iff _ _ _ _ _).mp (by simpa [read, decoded, identifier] using executed)

theorem read_complete (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (outcome : IntegerObject.Outcome)
    (reading : Reading schema codecProfile sort layout (represent state) environment wire outcome) :
    read schema codecProfile sort layout state environment wire = some outcome := by
  obtain ⟨term, name, _, encoded, identifier, reading⟩ := reading
  have decoded := decode_encoded _ _ _ _ _ encoded
  have named := identifier_complete _ _ identifier
  have observed := (ScopedLvalues.read_iff _ _ _ _ _).mpr reading
  simp [read, decoded, named, observed]

theorem read_iff (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (outcome : IntegerObject.Outcome) :
    read schema codecProfile sort layout state environment wire = some outcome ↔
      Reading schema codecProfile sort layout (represent state) environment wire outcome :=
  ⟨read_sound schema codecProfile sort layout state environment wire outcome,
    read_complete schema codecProfile sort layout state environment wire outcome⟩

def store (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (value : IntegerValue layout.representation.integer) : Option (State layout.representation.characters) := do
  let term ← decode? schema codecProfile sort wire
  let name ← identifierName term
  ScopedLvalues.store layout state environment name value

def Writing (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before after : SemanticState layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (value : IntegerValue layout.representation.integer) : Prop :=
  ∃ term name, Sorted schema codecProfile sort term ∧ encode? schema codecProfile sort term = some wire ∧
    Identifier term name ∧ ScopedLvalues.Writing layout before after environment name value

theorem store_sound (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state saved : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (wire : Wire) (value : IntegerValue layout.representation.integer)
    (executed : store schema codecProfile sort layout state environment wire value = some saved) :
    Writing schema codecProfile sort layout (represent state) (represent saved) environment wire value := by
  cases decoded : decode? schema codecProfile sort wire with
  | none => simp [store, decoded] at executed
  | some term =>
      cases identifier : identifierName term with
      | none => simp [store, decoded, identifier] at executed
      | some name =>
          refine ⟨term, name, decode_sorted _ _ _ _ _ decoded,
            encode_decoded _ _ _ _ _ decoded, identifier_sound _ _ identifier, ?_⟩
          exact ScopedLvalues.store_sound _ _ _ _ _ _ (by simpa [store, decoded, identifier] using executed)

theorem store_complete (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (state : State layout.representation.characters) (after : SemanticState layout.representation.characters)
    (environment : ScopedLvalues.Environment) (wire : Wire) (value : IntegerValue layout.representation.integer)
    (writing : Writing schema codecProfile sort layout (represent state) after environment wire value) :
    ∃ saved, store schema codecProfile sort layout state environment wire value = some saved ∧ represent saved = after := by
  obtain ⟨term, name, _, encoded, identifier, writing⟩ := writing
  have decoded := decode_encoded _ _ _ _ _ encoded
  have named := identifier_complete _ _ identifier
  obtain ⟨saved, executed, same⟩ := ScopedLvalues.store_complete _ _ _ _ _ _ writing
  exact ⟨saved, by simp [store, decoded, named, executed], same⟩

theorem read_encoded_identifier (schema : Schema) (codecProfile : Notation) (sort : String)
    (layout : Layout) (state : State layout.representation.characters)
    (environment : ScopedLvalues.Environment) (name : String) (wire : Wire)
    (encoded : encode? schema codecProfile sort (.node "Var" [.text name]) = some wire) :
    read schema codecProfile sort layout state environment wire =
      ScopedLvalues.read layout state environment name := by
  have decoded := decode_encoded _ _ _ _ _ encoded
  simp [read, decoded, identifierName]

theorem store_encoded_identifier (schema : Schema) (codecProfile : Notation) (sort : String)
    (layout : Layout) (state : State layout.representation.characters)
    (environment : ScopedLvalues.Environment) (name : String) (wire : Wire)
    (value : IntegerValue layout.representation.integer)
    (encoded : encode? schema codecProfile sort (.node "Var" [.text name]) = some wire) :
    store schema codecProfile sort layout state environment wire value =
      ScopedLvalues.store layout state environment name value := by
  have decoded := decode_encoded _ _ _ _ _ encoded
  simp [store, decoded, identifierName]

theorem represent_sorted_identifier (schema : Schema) (codecProfile : Notation) (sort : String)
    (name : String) (sorted : Sorted schema codecProfile sort (.node "Var" [.text name])) :
    ∃ wire, encode? schema codecProfile sort (.node "Var" [.text name]) = some wire ∧
      decode? schema codecProfile sort wire = some (.node "Var" [.text name]) := by
  obtain ⟨wire, encoded⟩ := encode_sorted sorted
  exact ⟨wire, encoded, decode_encoded _ _ _ _ _ encoded⟩

end Mettapedia.Languages.C11.CestaObjectAccess

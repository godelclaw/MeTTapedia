import Mettapedia.GSLT.Parsing.CanonicalGrammarLowering
import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.GSLT.LanguageDef.ExtensionComposition

/-!
# Sort-directed canonical trees in MeTTa data

The existing canonical grammar carrier is represented in the existing MeTTa
`Atom` carrier. A schema declares the lexical, ordered-list, and constructor
sorts. Admission checks the expected sort, constructor identity, exact arity,
and every child. Token spellings remain strings; numeric values are never
interpreted. Identifier positions admit bare symbols only under an explicit
host lexical policy, with a reserved string wrapper for other spellings.

This is a structural boundary after grammar extraction and ambiguity selection.
It is neither a byte `.module` reader nor C name/type elaboration. The historical
`metta_venus.cf` source and the frozen mettail-rust authoring quotation remain
distinct source boundaries. The schema is the index of the admission fibre;
the codec does not establish origin-sensitive module joins or native execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec

open CanonicalGrammar (CanonicalTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

inductive TokenRepresentation where
  | literal
  | identifier
  deriving DecidableEq, Repr

structure Constructor where
  name : String
  arguments : List String
  deriving DecidableEq, Repr

inductive Shape where
  | token (representation : TokenRepresentation)
  | list (elementSort : String)
  | constructors (declarations : List Constructor)
  deriving DecidableEq, Repr

/-- An extracted schema, indexed by its exact declaration and lexical policy.
It is not a nominal language name used as a substitute for that data. -/
structure Schema where
  shape? : String → Option Shape
  acceptsToken : String → String → Bool

structure Notation where
  headPrefix : String := "c:"
  listName : String := "List"
  symbolName : String := "Symbol"
  safeSymbol : String → Bool

def Notation.listHead (profile : Notation) : String := profile.headPrefix ++ profile.listName
def Notation.symbolHead (profile : Notation) : String := profile.headPrefix ++ profile.symbolName

def stripPrefix? : List Char → List Char → Option (List Char)
  | [], text => some text
  | first :: headPrefix, next :: text =>
      if first = next then stripPrefix? headPrefix text else none
  | _ :: _, [] => none

@[simp] theorem stripPrefix_append (headPrefix text : List Char) :
    stripPrefix? headPrefix (headPrefix ++ text) = some text := by
  induction headPrefix with
  | nil => rfl
  | cons first headPrefix ih => simp [stripPrefix?, ih]

def constructorName? (profile : Notation) (head : String) : Option String :=
  (stripPrefix? profile.headPrefix.toList head.toList).map String.ofList

@[simp] theorem constructorName_head (profile : Notation) (name : String) :
    constructorName? profile (profile.headPrefix ++ name) = some name := by
  simp [constructorName?, String.toList_append]

theorem stripPrefix_reflects (headPrefix text suffix : List Char)
    (decoded : stripPrefix? headPrefix text = some suffix) :
    text = headPrefix ++ suffix := by
  induction headPrefix generalizing text with
  | nil =>
      simpa [stripPrefix?] using decoded
  | cons first headPrefix ih =>
      cases text with
      | nil => simp [stripPrefix?] at decoded
      | cons next text =>
          by_cases same : first = next
          · subst next
            simp only [stripPrefix?, ↓reduceIte] at decoded
            exact congrArg (List.cons first) (ih text decoded)
          · simp [stripPrefix?, same] at decoded

theorem constructorName_reflects (profile : Notation) (head name : String)
    (decoded : constructorName? profile head = some name) :
    head = profile.headPrefix ++ name := by
  cases suffix : stripPrefix? profile.headPrefix.toList head.toList with
  | none => simp [constructorName?, suffix] at decoded
  | some characters =>
      simp [constructorName?, suffix] at decoded
      rw [← decoded]
      have shape := congrArg String.ofList
        (stripPrefix_reflects profile.headPrefix.toList head.toList characters suffix)
      simpa only [String.ofList_toList, String.ofList_append] using shape

/-- Duplicate declarations and reserved codec names have no list-order fallback. -/
def constructor? (profile : Notation) (declarations : List Constructor)
    (name : String) : Option Constructor :=
  if name = profile.listName ∨ name = profile.symbolName then none
  else match declarations.filter (fun declaration => declaration.name == name) with
    | [declaration] => some declaration
    | _ => none

theorem constructor_name (profile : Notation) (declarations : List Constructor)
    (name : String) (declaration : Constructor)
    (found : constructor? profile declarations name = some declaration) :
    declaration.name = name := by
  unfold constructor? at found
  split at found
  · contradiction
  · split at found
    · rename_i candidate filtered
      cases found
      have member : declaration ∈ declarations.filter (fun row => row.name == name) := by
        rw [filtered]
        simp
      exact beq_iff_eq.mp (List.mem_filter.mp member).2
    · contradiction

def encodeToken (profile : Notation) : TokenRepresentation → String → Atom
  | .literal, spelling => .grounded (.string spelling)
  | .identifier, spelling =>
      if profile.safeSymbol spelling then .symbol spelling
      else .expression [.symbol profile.symbolHead, .grounded (.string spelling)]

def decodeToken? (profile : Notation) : TokenRepresentation → Atom → Option String
  | .literal, .grounded (.string spelling) => some spelling
  | .identifier, .symbol spelling =>
      if profile.safeSymbol spelling then some spelling else none
  | .identifier, .expression [.symbol head, .grounded (.string spelling)] =>
      if head = profile.symbolHead ∧ profile.safeSymbol spelling = false
      then some spelling else none
  | _, _ => none

@[simp] theorem decodeToken_encodeToken (profile : Notation)
    (representation : TokenRepresentation) (spelling : String) :
    decodeToken? profile representation (encodeToken profile representation spelling) =
      some spelling := by
  cases representation with
  | literal => rfl
  | identifier =>
      cases valid : profile.safeSymbol spelling <;>
        simp [encodeToken, decodeToken?, valid]

/-- The wrapper has one canonical reading; redundant escapes are rejected. -/
theorem encodeToken_of_decode (profile : Notation)
    (representation : TokenRepresentation) (wire : Atom) (spelling : String)
    (decoded : decodeToken? profile representation wire = some spelling) :
    encodeToken profile representation spelling = wire := by
  unfold decodeToken? at decoded
  split at decoded
  · cases decoded
    rfl
  · split at decoded
    · cases decoded
      simp_all [encodeToken]
    · contradiction
  · split at decoded
    · rename_i guard
      cases decoded
      simp_all [encodeToken]
    · contradiction
  · contradiction

mutual
  def encode? (schema : Schema) (profile : Notation) (sort : String) :
      CanonicalTerm → Option Atom
    | .text spelling =>
        match schema.shape? sort with
        | some (.token representation) =>
            if schema.acceptsToken sort spelling then
              some (encodeToken profile representation spelling) else none
        | _ => none
    | .node name children => do
        let .constructors declarations ← schema.shape? sort | none
        let declaration ← constructor? profile declarations name
        let arguments ← encodeArguments? schema profile declaration.arguments children
        pure (.expression (.symbol (profile.headPrefix ++ name) :: arguments))
    | .seq elements => do
        let .list elementSort ← schema.shape? sort | none
        let arguments ← encodeElements? schema profile elementSort elements
        pure (.expression (.symbol profile.listHead :: arguments))

  def encodeArguments? (schema : Schema) (profile : Notation) :
      List String → List CanonicalTerm → Option (List Atom)
    | [], [] => some []
    | sort :: sorts, child :: children => do
        return (← encode? schema profile sort child) ::
          (← encodeArguments? schema profile sorts children)
    | _, _ => none

  def encodeElements? (schema : Schema) (profile : Notation) (sort : String) :
      List CanonicalTerm → Option (List Atom)
    | [] => some []
    | child :: children => do
        return (← encode? schema profile sort child) ::
          (← encodeElements? schema profile sort children)
end

mutual
  def decode? (schema : Schema) (profile : Notation) (sort : String)
      (wire : Atom) : Option CanonicalTerm :=
    match schema.shape? sort with
    | some (.token representation) => do
        let spelling ← decodeToken? profile representation wire
        if schema.acceptsToken sort spelling then some (.text spelling) else none
    | some (.constructors declarations) =>
        match wire with
        | .expression (.symbol head :: children) => do
            let name ← constructorName? profile head
            let declaration ← constructor? profile declarations name
            let arguments ← decodeArguments? schema profile declaration.arguments children
            pure (.node name arguments)
        | _ => none
    | some (.list elementSort) =>
        match wire with
        | .expression (.symbol head :: children) =>
            if head = profile.listHead then
              (decodeElements? schema profile elementSort children).map CanonicalTerm.seq
            else none
        | _ => none
    | none => none

  def decodeArguments? (schema : Schema) (profile : Notation) :
      List String → List Atom → Option (List CanonicalTerm)
    | [], [] => some []
    | sort :: sorts, child :: children => do
        return (← decode? schema profile sort child) ::
          (← decodeArguments? schema profile sorts children)
    | _, _ => none

  def decodeElements? (schema : Schema) (profile : Notation) (sort : String) :
      List Atom → Option (List CanonicalTerm)
    | [] => some []
    | child :: children => do
        return (← decode? schema profile sort child) ::
          (← decodeElements? schema profile sort children)
end

mutual
  /-- Independent sorted-tree formation, prior to any wire representation. -/
  inductive Sorted (schema : Schema) (profile : Notation) : String → CanonicalTerm → Prop
    | token (sort spelling : String) (representation : TokenRepresentation)
        (shape : schema.shape? sort = some (.token representation))
        (accepted : schema.acceptsToken sort spelling = true) :
        Sorted schema profile sort (.text spelling)
    | node (sort name : String) (declarations : List Constructor) (declaration : Constructor)
        (children : List CanonicalTerm)
        (shape : schema.shape? sort = some (.constructors declarations))
        (found : constructor? profile declarations name = some declaration)
        (arguments : SortedArguments schema profile declaration.arguments children) :
        Sorted schema profile sort (.node name children)
    | list (sort elementSort : String) (elements : List CanonicalTerm)
        (shape : schema.shape? sort = some (.list elementSort))
        (children : SortedElements schema profile elementSort elements) :
        Sorted schema profile sort (.seq elements)

  inductive SortedArguments (schema : Schema) (profile : Notation) :
      List String → List CanonicalTerm → Prop
    | nil : SortedArguments schema profile [] []
    | cons {sort : String} {sorts : List String} {child : CanonicalTerm}
        {children : List CanonicalTerm}
        (head : Sorted schema profile sort child)
        (tail : SortedArguments schema profile sorts children) :
        SortedArguments schema profile (sort :: sorts) (child :: children)

  inductive SortedElements (schema : Schema) (profile : Notation) :
      String → List CanonicalTerm → Prop
    | nil (sort : String) : SortedElements schema profile sort []
    | cons {sort : String} {child : CanonicalTerm} {children : List CanonicalTerm}
        (head : Sorted schema profile sort child)
        (tail : SortedElements schema profile sort children) :
        SortedElements schema profile sort (child :: children)
end

mutual
  /-- The decoder is a left inverse of successful structural encoding. -/
  theorem decode_encoded (schema : Schema) (profile : Notation) (sort : String)
      (term : CanonicalTerm) (wire : Atom)
      (encoded : encode? schema profile sort term = some wire) :
      decode? schema profile sort wire = some term := by
    cases term with
    | text spelling =>
        cases shape : schema.shape? sort with
        | none => simp [encode?, shape] at encoded
        | some shapeValue =>
            cases shapeValue with
            | token representation =>
                cases admitted : schema.acceptsToken sort spelling with
                | false => simp [encode?, shape, admitted] at encoded
                | true =>
                    simp only [encode?, shape, admitted, ↓reduceIte,
                      Option.some.injEq] at encoded
                    rw [← encoded]
                    simp [decode?, shape, admitted]
            | list elementSort => simp [encode?, shape] at encoded
            | constructors declarations => simp [encode?, shape] at encoded
    | node name children =>
        cases shape : schema.shape? sort with
        | none => simp [encode?, shape] at encoded
        | some shapeValue =>
            cases shapeValue with
            | token representation => simp [encode?, shape] at encoded
            | list elementSort => simp [encode?, shape] at encoded
            | constructors declarations =>
                cases found : constructor? profile declarations name with
                | none => simp [encode?, shape, found] at encoded
                | some declaration =>
                    cases arguments : encodeArguments? schema profile declaration.arguments children with
                    | none => simp [encode?, shape, found, arguments] at encoded
                    | some values =>
                        simp [encode?, shape, found, arguments] at encoded
                        rw [← encoded]
                        simp [decode?, shape, found,
                          decodeArguments_encoded schema profile declaration.arguments children values arguments]
    | seq elements =>
        cases shape : schema.shape? sort with
        | none => simp [encode?, shape] at encoded
        | some shapeValue =>
            cases shapeValue with
            | token representation => simp [encode?, shape] at encoded
            | constructors declarations => simp [encode?, shape] at encoded
            | list elementSort =>
                cases arguments : encodeElements? schema profile elementSort elements with
                | none => simp [encode?, shape, arguments] at encoded
                | some values =>
                    simp [encode?, shape, arguments] at encoded
                    rw [← encoded]
                    simp [decode?, shape,
                      decodeElements_encoded schema profile elementSort elements values arguments]
  termination_by sizeOf term

  theorem decodeArguments_encoded (schema : Schema) (profile : Notation)
      (sorts : List String) (terms : List CanonicalTerm) (wires : List Atom)
      (encoded : encodeArguments? schema profile sorts terms = some wires) :
      decodeArguments? schema profile sorts wires = some terms := by
    cases terms with
    | nil =>
        cases sorts <;> simp [encodeArguments?] at encoded
        subst wires
        rfl
    | cons child children =>
        cases sorts with
        | nil => simp [encodeArguments?] at encoded
        | cons sort sorts =>
            cases head : encode? schema profile sort child with
            | none => simp [encodeArguments?, head] at encoded
            | some value =>
                cases tail : encodeArguments? schema profile sorts children with
                | none => simp [encodeArguments?, head, tail] at encoded
                | some rest =>
                    simp [encodeArguments?, head, tail] at encoded
                    rw [← encoded]
                    simp [decodeArguments?, decode_encoded schema profile sort child value head,
                      decodeArguments_encoded schema profile sorts children rest tail]
  termination_by sizeOf terms

  theorem decodeElements_encoded (schema : Schema) (profile : Notation)
      (sort : String) (terms : List CanonicalTerm) (wires : List Atom)
      (encoded : encodeElements? schema profile sort terms = some wires) :
      decodeElements? schema profile sort wires = some terms := by
    cases terms with
    | nil =>
        simp [encodeElements?] at encoded
        subst wires
        rfl
    | cons child children =>
        cases head : encode? schema profile sort child with
        | none => simp [encodeElements?, head] at encoded
        | some value =>
            cases tail : encodeElements? schema profile sort children with
            | none => simp [encodeElements?, head, tail] at encoded
            | some rest =>
                simp [encodeElements?, head, tail] at encoded
                rw [← encoded]
                simp [decodeElements?, decode_encoded schema profile sort child value head,
                  decodeElements_encoded schema profile sort children rest tail]
  termination_by sizeOf terms
end

mutual
  theorem encode_sorted {schema : Schema} {profile : Notation} {sort : String}
      {term : CanonicalTerm} (valid : Sorted schema profile sort term) :
      ∃ wire, encode? schema profile sort term = some wire := by
    cases valid with
    | token sort spelling representation shape accepted =>
        exact ⟨encodeToken profile representation spelling, by simp [encode?, shape, accepted]⟩
    | node sort name declarations declaration children shape found arguments =>
        obtain ⟨values, encoded⟩ := encodeArguments_sorted arguments
        exact ⟨.expression (.symbol (profile.headPrefix ++ name) :: values),
          by simp [encode?, shape, found, encoded]⟩
    | list sort elementSort elements shape children =>
        obtain ⟨values, encoded⟩ := encodeElements_sorted children
        exact ⟨.expression (.symbol profile.listHead :: values),
          by simp [encode?, shape, encoded]⟩
  termination_by sizeOf term

  theorem encodeArguments_sorted {schema : Schema} {profile : Notation}
      {sorts : List String} {terms : List CanonicalTerm}
      (valid : SortedArguments schema profile sorts terms) :
      ∃ wires, encodeArguments? schema profile sorts terms = some wires := by
    cases valid with
    | nil => exact ⟨[], rfl⟩
    | cons head tail =>
        obtain ⟨value, encodedHead⟩ := encode_sorted head
        obtain ⟨values, encodedTail⟩ := encodeArguments_sorted tail
        exact ⟨value :: values, by simp [encodeArguments?, encodedHead, encodedTail]⟩
  termination_by sizeOf terms

  theorem encodeElements_sorted {schema : Schema} {profile : Notation} {sort : String}
      {terms : List CanonicalTerm} (valid : SortedElements schema profile sort terms) :
      ∃ wires, encodeElements? schema profile sort terms = some wires := by
    cases valid with
    | nil => exact ⟨[], rfl⟩
    | cons head tail =>
        obtain ⟨value, encodedHead⟩ := encode_sorted head
        obtain ⟨values, encodedTail⟩ := encodeElements_sorted tail
        exact ⟨value :: values, by simp [encodeElements?, encodedHead, encodedTail]⟩
  termination_by sizeOf terms
end

abbrev SortedTerm (schema : Schema) (profile : Notation) (sort : String) :=
  { term : CanonicalTerm // Sorted schema profile sort term }

/-- Total quotation of an independently well-sorted tree. -/
def quote {schema : Schema} {profile : Notation} {sort : String}
    (term : SortedTerm schema profile sort) : Atom :=
  (encode? schema profile sort term.val).get
    (by obtain ⟨wire, encoded⟩ := encode_sorted term.property; simp [encoded])

theorem encode_quote {schema : Schema} {profile : Notation} {sort : String}
    (term : SortedTerm schema profile sort) :
    encode? schema profile sort term.val = some (quote term) := by
  unfold quote
  exact (Option.some_get _).symm

/-- Every tree of arbitrary finite depth and arity survives the structural codec. -/
theorem decode_quote {schema : Schema} {profile : Notation} {sort : String}
    (term : SortedTerm schema profile sort) :
    decode? schema profile sort (quote term) = some term.val :=
  decode_encoded schema profile sort term.val (quote term) (encode_quote term)

theorem quote_injective {schema : Schema} {profile : Notation} {sort : String} :
    Function.Injective (@quote schema profile sort) := by
  intro first second same
  apply Subtype.ext
  have decoded := congrArg (decode? schema profile sort) same
  simpa only [decode_quote, Option.some.injEq] using decoded

mutual
  /-- A successful decoder produces a tree formed by the independent sort rules. -/
  theorem decode_sorted (schema : Schema) (profile : Notation) (sort : String)
      (wire : Atom) (term : CanonicalTerm)
      (decoded : decode? schema profile sort wire = some term) :
      Sorted schema profile sort term := by
    cases shape : schema.shape? sort with
    | none => simp [decode?, shape] at decoded
    | some shapeValue =>
        cases shapeValue with
        | token representation =>
            cases token : decodeToken? profile representation wire with
            | none => simp [decode?, shape, token] at decoded
            | some spelling =>
                cases accepted : schema.acceptsToken sort spelling with
                | false => simp [decode?, shape, token, accepted] at decoded
                | true =>
                    simp [decode?, shape, token, accepted] at decoded
                    subst term
                    exact .token sort spelling representation shape accepted
        | constructors declarations =>
            cases wire with
            | symbol _ => simp [decode?, shape] at decoded
            | var _ => simp [decode?, shape] at decoded
            | grounded _ => simp [decode?, shape] at decoded
            | expression atoms =>
                cases atoms with
                | nil => simp [decode?, shape] at decoded
                | cons head children =>
                    cases head with
                    | var _ => simp [decode?, shape] at decoded
                    | grounded _ => simp [decode?, shape] at decoded
                    | expression _ => simp [decode?, shape] at decoded
                    | symbol head =>
                        cases name : constructorName? profile head with
                        | none => simp [decode?, shape, name] at decoded
                        | some constructorName =>
                            cases found : constructor? profile declarations constructorName with
                            | none => simp [decode?, shape, name, found] at decoded
                            | some declaration =>
                                cases arguments : decodeArguments? schema profile declaration.arguments children with
                                | none => simp [decode?, shape, name, found, arguments] at decoded
                                | some terms =>
                                    simp [decode?, shape, name, found, arguments] at decoded
                                    subst term
                                    exact .node sort constructorName declarations declaration terms shape found
                                      (decodeArguments_sorted schema profile declaration.arguments children terms arguments)
        | list elementSort =>
            cases wire with
            | symbol _ => simp [decode?, shape] at decoded
            | var _ => simp [decode?, shape] at decoded
            | grounded _ => simp [decode?, shape] at decoded
            | expression atoms =>
                cases atoms with
                | nil => simp [decode?, shape] at decoded
                | cons head children =>
                    cases head with
                    | var _ => simp [decode?, shape] at decoded
                    | grounded _ => simp [decode?, shape] at decoded
                    | expression _ => simp [decode?, shape] at decoded
                    | symbol head =>
                        by_cases same : head = profile.listHead
                        · cases arguments : decodeElements? schema profile elementSort children with
                          | none => simp [decode?, shape, same, arguments] at decoded
                          | some terms =>
                              simp [decode?, shape, same, arguments] at decoded
                              subst term
                              exact .list sort elementSort terms shape
                                (decodeElements_sorted schema profile elementSort children terms arguments)
                        · simp [decode?, shape, same] at decoded
  termination_by sizeOf wire

  theorem decodeArguments_sorted (schema : Schema) (profile : Notation)
      (sorts : List String) (wires : List Atom) (terms : List CanonicalTerm)
      (decoded : decodeArguments? schema profile sorts wires = some terms) :
      SortedArguments schema profile sorts terms := by
    cases wires with
    | nil =>
        cases sorts <;> simp [decodeArguments?] at decoded
        subst terms
        exact .nil
    | cons child children =>
        cases sorts with
        | nil => simp [decodeArguments?] at decoded
        | cons sort sorts =>
            cases head : decode? schema profile sort child with
            | none => simp [decodeArguments?, head] at decoded
            | some value =>
                cases tail : decodeArguments? schema profile sorts children with
                | none => simp [decodeArguments?, head, tail] at decoded
                | some rest =>
                    simp [decodeArguments?, head, tail] at decoded
                    subst terms
                    exact .cons (decode_sorted schema profile sort child value head)
                      (decodeArguments_sorted schema profile sorts children rest tail)
  termination_by sizeOf wires

  theorem decodeElements_sorted (schema : Schema) (profile : Notation) (sort : String)
      (wires : List Atom) (terms : List CanonicalTerm)
      (decoded : decodeElements? schema profile sort wires = some terms) :
      SortedElements schema profile sort terms := by
    cases wires with
    | nil =>
        simp [decodeElements?] at decoded
        subst terms
        exact .nil sort
    | cons child children =>
        cases head : decode? schema profile sort child with
        | none => simp [decodeElements?, head] at decoded
        | some value =>
            cases tail : decodeElements? schema profile sort children with
            | none => simp [decodeElements?, head, tail] at decoded
            | some rest =>
                simp [decodeElements?, head, tail] at decoded
                subst terms
                exact .cons (decode_sorted schema profile sort child value head)
                  (decodeElements_sorted schema profile sort children rest tail)
  termination_by sizeOf wires
end

mutual
  /-- Every accepted wire is the exact encoding of its result. No aliases or
  extra wire forms enter the admitted image. -/
  theorem encode_decoded (schema : Schema) (profile : Notation) (sort : String)
      (wire : Atom) (term : CanonicalTerm)
      (decoded : decode? schema profile sort wire = some term) :
      encode? schema profile sort term = some wire := by
    cases shape : schema.shape? sort with
    | none => simp [decode?, shape] at decoded
    | some shapeValue =>
        cases shapeValue with
        | token representation =>
            cases token : decodeToken? profile representation wire with
            | none => simp [decode?, shape, token] at decoded
            | some spelling =>
                cases accepted : schema.acceptsToken sort spelling with
                | false => simp [decode?, shape, token, accepted] at decoded
                | true =>
                    simp [decode?, shape, token, accepted] at decoded
                    subst term
                    simp [encode?, shape, accepted,
                      encodeToken_of_decode profile representation wire spelling token]
        | constructors declarations =>
            cases wire with
            | symbol _ => simp [decode?, shape] at decoded
            | var _ => simp [decode?, shape] at decoded
            | grounded _ => simp [decode?, shape] at decoded
            | expression atoms =>
                cases atoms with
                | nil => simp [decode?, shape] at decoded
                | cons head children =>
                    cases head with
                    | var _ => simp [decode?, shape] at decoded
                    | grounded _ => simp [decode?, shape] at decoded
                    | expression _ => simp [decode?, shape] at decoded
                    | symbol head =>
                        cases name : constructorName? profile head with
                        | none => simp [decode?, shape, name] at decoded
                        | some constructorName =>
                            cases found : constructor? profile declarations constructorName with
                            | none => simp [decode?, shape, name, found] at decoded
                            | some declaration =>
                                cases arguments : decodeArguments? schema profile declaration.arguments children with
                                | none => simp [decode?, shape, name, found, arguments] at decoded
                                | some terms =>
                                    simp [decode?, shape, name, found, arguments] at decoded
                                    subst term
                                    have spelling := constructorName_reflects profile head constructorName name
                                    simp [encode?, shape, found,
                                      encodeArguments_decoded schema profile declaration.arguments children terms arguments,
                                      ← spelling]
        | list elementSort =>
            cases wire with
            | symbol _ => simp [decode?, shape] at decoded
            | var _ => simp [decode?, shape] at decoded
            | grounded _ => simp [decode?, shape] at decoded
            | expression atoms =>
                cases atoms with
                | nil => simp [decode?, shape] at decoded
                | cons head children =>
                    cases head with
                    | var _ => simp [decode?, shape] at decoded
                    | grounded _ => simp [decode?, shape] at decoded
                    | expression _ => simp [decode?, shape] at decoded
                    | symbol head =>
                        by_cases same : head = profile.listHead
                        · cases arguments : decodeElements? schema profile elementSort children with
                          | none => simp [decode?, shape, same, arguments] at decoded
                          | some terms =>
                              simp [decode?, shape, same, arguments] at decoded
                              subst term
                              simp [encode?, shape, same,
                                encodeElements_decoded schema profile elementSort children terms arguments]
                        · simp [decode?, shape, same] at decoded
  termination_by sizeOf wire

  theorem encodeArguments_decoded (schema : Schema) (profile : Notation)
      (sorts : List String) (wires : List Atom) (terms : List CanonicalTerm)
      (decoded : decodeArguments? schema profile sorts wires = some terms) :
      encodeArguments? schema profile sorts terms = some wires := by
    cases wires with
    | nil =>
        cases sorts <;> simp [decodeArguments?] at decoded
        subst terms
        rfl
    | cons child children =>
        cases sorts with
        | nil => simp [decodeArguments?] at decoded
        | cons sort sorts =>
            cases head : decode? schema profile sort child with
            | none => simp [decodeArguments?, head] at decoded
            | some value =>
                cases tail : decodeArguments? schema profile sorts children with
                | none => simp [decodeArguments?, head, tail] at decoded
                | some rest =>
                    simp [decodeArguments?, head, tail] at decoded
                    subst terms
                    simp [encodeArguments?, encode_decoded schema profile sort child value head,
                      encodeArguments_decoded schema profile sorts children rest tail]
  termination_by sizeOf wires

  theorem encodeElements_decoded (schema : Schema) (profile : Notation) (sort : String)
      (wires : List Atom) (terms : List CanonicalTerm)
      (decoded : decodeElements? schema profile sort wires = some terms) :
      encodeElements? schema profile sort terms = some wires := by
    cases wires with
    | nil =>
        simp [decodeElements?] at decoded
        subst terms
        rfl
    | cons child children =>
        cases head : decode? schema profile sort child with
        | none => simp [decodeElements?, head] at decoded
        | some value =>
            cases tail : decodeElements? schema profile sort children with
            | none => simp [decodeElements?, head, tail] at decoded
            | some rest =>
                simp [decodeElements?, head, tail] at decoded
                subst terms
                simp [encodeElements?, encode_decoded schema profile sort child value head,
                  encodeElements_decoded schema profile sort children rest tail]
  termination_by sizeOf wires
end

theorem decode_some_iff (schema : Schema) (profile : Notation) (sort : String)
    (wire : Atom) (term : CanonicalTerm) :
    decode? schema profile sort wire = some term ↔
      encode? schema profile sort term = some wire :=
  ⟨encode_decoded schema profile sort wire term, decode_encoded schema profile sort term wire⟩

def admit? (schema : Schema) (profile : Notation) (sort : String)
    (wire : Atom) : Option (SortedTerm schema profile sort) :=
  match decoded : decode? schema profile sort wire with
  | none => none
  | some term => some ⟨term, decode_sorted schema profile sort wire term decoded⟩

@[simp] theorem admit_quote {schema : Schema} {profile : Notation} {sort : String}
    (term : SortedTerm schema profile sort) :
    admit? schema profile sort (quote term) = some term := by
  unfold admit?
  split
  · rename_i decoded
    have impossible := decode_quote term
    rw [decoded] at impossible
    contradiction
  · rename_i parsed decoded
    exact congrArg some (Subtype.ext (Option.some.inj (decoded.symm.trans (decode_quote term))))

theorem admit_some_iff (schema : Schema) (profile : Notation) (sort : String)
    (wire : Atom) (term : SortedTerm schema profile sort) :
    admit? schema profile sort wire = some term ↔
      decode? schema profile sort wire = some term.val := by
  unfold admit?
  split
  · rename_i decoded
    simp [decoded]
  · rename_i parsed decoded
    constructor
    · intro same
      exact decoded.trans (congrArg some (congrArg Subtype.val (Option.some.inj same)))
    · intro same
      exact congrArg some (Subtype.ext (Option.some.inj (decoded.symm.trans same)))

theorem quote_of_admit (schema : Schema) (profile : Notation) (sort : String)
    (wire : Atom) (term : SortedTerm schema profile sort)
    (admitted : admit? schema profile sort wire = some term) :
    quote term = wire := by
  have decoded := (admit_some_iff schema profile sort wire term).mp admitted
  exact Option.some.inj ((encode_quote term).symm.trans
    (encode_decoded schema profile sort wire term.val decoded))

/-- The admitted wire image is exact in both directions at its declared context. -/
theorem admit_some_iff_quote (schema : Schema) (profile : Notation) (sort : String)
    (wire : Atom) (term : SortedTerm schema profile sort) :
    admit? schema profile sort wire = some term ↔ quote term = wire := by
  constructor
  · exact quote_of_admit schema profile sort wire term
  · intro same
    rw [← same]
    exact admit_quote term

/-- An exact schema, lexical policy, namespace, and expected root sort form
one admission context. No declaration is admitted under an unrelated schema. -/
structure Context where
  schema : Schema
  profile : Notation
  rootSort : String

abbrev Document := DeclarationDocument Atom
abbrev Payload (context : Context) :=
  List (SortedTerm context.schema context.profile context.rootSort)

def elaborateDocument? (context : Context) (document : Document) : Option (Payload context) :=
  document.values.mapM (admit? context.schema context.profile context.rootSort)

def quoteDocument (context : Context) (terms : Payload context) : Document :=
  .bundle ((terms.map quote).map .declaration)

@[simp] theorem elaborate_quoteDocument (context : Context) (terms : Payload context) :
    elaborateDocument? context (quoteDocument context terms) = some terms := by
  unfold elaborateDocument? quoteDocument
  rw [DeclarationDocument.values_bundle_map]
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [List.mapM_cons, ih]

/-- The existing document algebra gives ordered composition. The additional
content is the independently checked sorted-tree fibre and its exact codec. -/
def documentSystem (context : Context) : GSLT.CompositionalElaboration (Payload context) where
  authoring := ExactDeclarationCodec.documentCompositional Atom
  elaboration := {
    elaborate := elaborateDocument? context
    quote := quoteDocument context
    elaborate_quote := elaborate_quoteDocument context
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      unfold elaborateDocument?
      rw [equivalent]
    rewrite := by
      intro first second impossible
      exact False.elim impossible }
  emptyPayload := []
  merge := fun first second => some (first ++ second)
  elaborate_empty := by
    change elaborateDocument? context (.bundle []) = some []
    simp [elaborateDocument?, DeclarationDocument.values, DeclarationDocument.valuesList]
  elaborate_append := by
    intro first second
    change Document at first second
    change elaborateDocument? context (.bundle [first, second]) = _
    simp [elaborateDocument?, DeclarationDocument.values, DeclarationDocument.valuesList]

/-- Admission genuinely depends on the grammar schema and lexical context;
this reuses the established coGSLT interface rather than adding another one. -/
def sortedTreeLayer : CompositionalLayer Context where
  Fiber := Payload
  system := documentSystem

def sortedTreeCoGSLT : CoGSLTLayer Context := sortedTreeLayer.toCoGSLTLayer

theorem elaborateDocument_append (context : Context) (first second : Document) :
    elaborateDocument? context (.bundle [first, second]) =
      (elaborateDocument? context first).bind fun left =>
        (elaborateDocument? context second).bind fun right => some (left ++ right) :=
  (documentSystem context).elaborate_append first second

/-- A malformed tree anywhere rejects the complete composed document. -/
theorem append_rejected_left (context : Context) (first second : Document)
    (rejected : elaborateDocument? context first = none) :
    elaborateDocument? context (.bundle [first, second]) = none := by
  rw [elaborateDocument_append, rejected]
  rfl

theorem append_rejected_right (context : Context) (first second : Document)
    (rejected : elaborateDocument? context second = none) :
    elaborateDocument? context (.bundle [first, second]) = none := by
  rw [elaborateDocument_append, rejected]
  cases elaborateDocument? context first <;> rfl

open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef GrammarRule TermParam)

/-- The first-order structural fragment is explicit. A binder or higher type
has no approximate constructor signature. -/
def parameterSort? : TermParam → Option String
  | .simple _ (.base sort) => some sort
  | _ => none

/-- Derivation children follow nonterminal occurrences in the authored syntax,
including repeated occurrences, rather than the order of parameter declarations.
Reuse the established structural lowering after the explicit first-order gate. -/
def rowArgumentSorts? (row : GrammarRule) : Option (List String) := do
  let _ ← row.params.mapM parameterSort?
  let symbols ← CanonicalGrammar.Lowering.lowerItems row row.syntaxPattern
  pure (symbols.filterMap fun
    | .rule sort | .token sort => some sort
    | .fixed _ => none)

def constructorOfRow? (row : GrammarRule) : Option Constructor :=
  (rowArgumentSorts? row).map (fun arguments => ⟨row.label, arguments⟩)

/-- Successful extraction retains the source label and exactly the ordered
nonterminal-occurrence traversal; it does not compare an object defined as itself. -/
theorem constructorOfRow_exact (row : GrammarRule) (declaration : Constructor) :
    constructorOfRow? row = some declaration ↔
      declaration.name = row.label ∧ rowArgumentSorts? row = some declaration.arguments := by
  cases declaration with
  | mk label arguments =>
      cases sorts : rowArgumentSorts? row with
      | none => simp [constructorOfRow?, sorts]
      | some declared =>
          simp [constructorOfRow?, sorts, eq_comm]

/-- Extract every source row, preserving its label and child occurrence order.
Lexical and canonical-list classifications are supplied independently. These
are representation classifications, not a C lexical grammar or parse policy.
A token/list overlap or undeclared sort is not admitted by the resulting schema.
Any unsupported parameter fails extraction of the complete row collection. -/
def schemaOfLanguage? (language : LanguageDef)
    (tokenShape? : String → Option TokenRepresentation)
    (listShape? : String → Option String)
    (acceptsToken : String → String → Bool) : Option Schema := do
  let declarations ← language.terms.mapM (fun row => do
    let declaration ← constructorOfRow? row
    pure (row.category, declaration))
  pure {
    acceptsToken
    shape? := fun sort =>
      if language.typeNames.contains sort then
        match tokenShape? sort, listShape? sort with
        | some representation, none => some (.token representation)
        | none, some elementSort =>
            if language.typeNames.contains elementSort then some (.list elementSort) else none
        | none, none => some (.constructors
            ((declarations.filter (fun row => row.1 == sort)).map Prod.snd))
        | some _, some _ => none
      else none }

/-- First-order extraction cannot silently erase a binding parameter. -/
theorem binder_parameter_rejected (binder : Option String) (body : String)
    (type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) :
    parameterSort? (.abstractionNamed binder body type) = none := rfl

theorem multiBinder_parameter_rejected (binders : List String) (body : String)
    (type : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) :
    parameterSort? (.multiAbstractionNamed binders body type) = none := rfl

#print axioms decode_encoded
#print axioms decode_quote
#print axioms decode_sorted
#print axioms encode_decoded
#print axioms decode_some_iff
#print axioms admit_some_iff_quote
#print axioms quote_injective
#print axioms elaborate_quoteDocument

end Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec

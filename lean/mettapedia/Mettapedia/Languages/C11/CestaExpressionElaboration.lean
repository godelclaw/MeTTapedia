import Mettapedia.Languages.C11.CestaObjectAccess
import Mettapedia.Languages.C11.LocatedExpressions

/-!
# Integer formation in selected Cesta canonical syntax

The adapter reads the existing canonical constructor, token and ordered-list
carrier. Primitive type specifiers use the CDecl constructor names and retain
their multiplicity; every legal ordering of the admitted standard integer
specifier combinations is accepted. Plain `char`, qualifiers, typedefs,
abstract declarators and extensions require additional source-type profiles.

The literal profile is zero and unsuffixed decimal constants whose value fits `int`.
The single zero spelling has the same `int` interpretation as C11's zero
octal constant; other octal spellings need their separate base interpretation.
Its digit and range judgments are independent of the executable reader.
Octal, hexadecimal, suffixes and the larger candidate-type selection required
by C11 remain outside this literal profile. Admission of an ordinary C token,
the native parser and selection of a parse are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaExpressionElaboration

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open ObjectAccessMemory IntegerMemoryModel LocatedExpressions

def decimalDigit? (character : Char) : Option Nat :=
  if 48 ≤ character.toNat ∧ character.toNat ≤ 57 then some (character.toNat - 48) else none

inductive DecimalDigit : Char → Nat → Prop where
  | digit (character : Char) (value : Nat) (bound : value < 10)
      (spelling : character.toNat = 48 + value) : DecimalDigit character value

theorem decimalDigit_iff (character : Char) (value : Nat) :
    decimalDigit? character = some value ↔ DecimalDigit character value := by
  constructor
  · intro parsed
    unfold decimalDigit? at parsed
    split at parsed
    · rename_i bounds
      cases parsed
      exact .digit _ _ (by omega) (by omega)
    · contradiction
  · intro digit
    cases digit with
    | digit bound spelling =>
        have bounds : 48 ≤ character.toNat ∧ character.toNat ≤ 57 := by omega
        simp only [decimalDigit?, if_pos bounds, Option.some.injEq]
        omega

def decimalDigits? : List Char → Option Nat
  | [] => some 0
  | first :: rest => do
      let digit ← decimalDigit? first
      let suffix ← decimalDigits? rest
      some (digit * 10 ^ rest.length + suffix)

inductive DecimalDigits : List Char → Nat → Prop where
  | nil : DecimalDigits [] 0
  | cons (first : Char) (rest : List Char) (digit suffix : Nat)
      (head : DecimalDigit first digit) (tail : DecimalDigits rest suffix) :
      DecimalDigits (first :: rest) (digit * 10 ^ rest.length + suffix)

theorem decimalDigits_iff (characters : List Char) (value : Nat) :
    decimalDigits? characters = some value ↔ DecimalDigits characters value := by
  induction characters generalizing value with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro digits; cases digits; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [decimalDigits?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨digit, head, suffix, tail, rfl⟩ := parsed
        exact .cons _ _ _ _ ((decimalDigit_iff _ _).mp head) ((ih _).mp tail)
      · intro digits
        cases digits with
        | cons _ _ digit suffix head tail =>
            simp only [decimalDigits?, (decimalDigit_iff _ _).mpr head,
              (ih _).mpr tail, bind, Option.bind_some]

def DecimalShape (characters : List Char) : Prop :=
  0 < characters.length ∧ (characters.length = 1 ∨ characters.head? ≠ some '0')

instance (characters : List Char) : Decidable (DecimalShape characters) :=
  inferInstanceAs (Decidable (0 < characters.length ∧
    (characters.length = 1 ∨ characters.head? ≠ some '0')))

def decimal? (spelling : String) : Option Nat :=
  if DecimalShape spelling.toList then decimalDigits? spelling.toList else none

def DecimalToken (spelling : String) (value : Nat) : Prop :=
  DecimalShape spelling.toList ∧ DecimalDigits spelling.toList value

theorem decimal_iff (spelling : String) (value : Nat) :
    decimal? spelling = some value ↔ DecimalToken spelling value := by
  by_cases formed : DecimalShape spelling.toList
  · rw [decimal?, if_pos formed]
    simp only [DecimalToken, formed, true_and, decimalDigits_iff]
  · rw [decimal?, if_neg formed]
    simp only [reduceCtorEq, DecimalToken, formed, false_and]

def literal? (model : Model) (spelling : String) : Option (IntegerScalar.Value model.parameters) := do
  let value ← decimal? spelling
  let integer ← IntegerStep.decodeValue (IntegerType.int.format model.parameters) (Int.ofNat value)
  some ⟨.int, integer⟩

inductive Literal (model : Model) : String → IntegerScalar.Value model.parameters → Prop where
  | decimal (spelling : String) (value : Nat) (token : DecimalToken spelling value)
      (range : (IntegerType.int.format model.parameters).Represents (Int.ofNat value)) :
      Literal model spelling ⟨.int, ⟨Int.ofNat value, range⟩⟩

theorem literal_sound (model : Model) (spelling : String) (scalar : IntegerScalar.Value model.parameters)
    (parsed : literal? model spelling = some scalar) : Literal model spelling scalar := by
  simp only [literal?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
  obtain ⟨value, token, integer, decoded, rfl⟩ := parsed
  have equal := IntegerStep.value_decode _ _ _ decoded
  cases integer with
  | mk actual range =>
      dsimp only at equal
      cases equal
      exact .decimal _ _ ((decimal_iff _ _).mp token) range

theorem literal_complete (model : Model) (spelling : String) (scalar : IntegerScalar.Value model.parameters)
    (literal : Literal model spelling scalar) : literal? model spelling = some scalar := by
  cases literal with
  | decimal value token range =>
      have decoded := IntegerStep.decodeValue_encode (IntegerType.int.format model.parameters) ⟨Int.ofNat value, range⟩
      simp only [literal?, (decimal_iff _ _).mpr token, bind, Option.bind_some,
        decoded]

theorem literal_iff (model : Model) (spelling : String) (scalar : IntegerScalar.Value model.parameters) :
    literal? model spelling = some scalar ↔ Literal model spelling scalar :=
  ⟨literal_sound model spelling scalar, literal_complete model spelling scalar⟩

inductive PrimitiveSpecifier where
  | char | short | int | long | signed | unsigned
  deriving DecidableEq, Repr

def PrimitiveSpecifier.head : PrimitiveSpecifier → String
  | .char => "Char"
  | .short => "Short"
  | .int => "Int"
  | .long => "Long"
  | .signed => "Signed"
  | .unsigned => "Unsigned"

def primitive? : CanonicalTerm → Option PrimitiveSpecifier
  | .node "Char" [] => some .char
  | .node "Short" [] => some .short
  | .node "Int" [] => some .int
  | .node "Long" [] => some .long
  | .node "Signed" [] => some .signed
  | .node "Unsigned" [] => some .unsigned
  | _ => none

inductive PrimitiveReading : CanonicalTerm → PrimitiveSpecifier → Prop where
  | primitive (specifier : PrimitiveSpecifier) :
      PrimitiveReading (.node specifier.head []) specifier

theorem primitive_complete (term : CanonicalTerm) (specifier : PrimitiveSpecifier)
    (reading : PrimitiveReading term specifier) : primitive? term = some specifier := by
  cases reading with
  | primitive specifier => cases specifier <;> rfl

theorem primitive_sound (term : CanonicalTerm) (specifier : PrimitiveSpecifier)
    (parsed : primitive? term = some specifier) : PrimitiveReading term specifier := by
  unfold primitive? at parsed
  split at parsed <;> first
    | contradiction
    | (cases parsed; first
        | exact .primitive .char
        | exact .primitive .short
        | exact .primitive .int
        | exact .primitive .long
        | exact .primitive .signed
        | exact .primitive .unsigned)

def primitiveTail? : CanonicalTerm → Option PrimitiveSpecifier
  | .node "PrimitiveQualifierTail" [term] => primitive? term
  | _ => none

inductive PrimitiveTailReading : CanonicalTerm → PrimitiveSpecifier → Prop where
  | tail (term : CanonicalTerm) (specifier : PrimitiveSpecifier)
      (reading : PrimitiveReading term specifier) :
      PrimitiveTailReading (.node "PrimitiveQualifierTail" [term]) specifier

theorem primitiveTail_iff (term : CanonicalTerm) (specifier : PrimitiveSpecifier) :
    primitiveTail? term = some specifier ↔ PrimitiveTailReading term specifier := by
  constructor
  · intro parsed
    unfold primitiveTail? at parsed
    split at parsed
    · exact .tail _ _ (primitive_sound _ _ parsed)
    · contradiction
  · intro reading
    cases reading with
    | tail term specifier reading => exact primitive_complete _ _ reading

def primitiveTails? : List CanonicalTerm → Option (List PrimitiveSpecifier)
  | [] => some []
  | first :: rest => do some ((← primitiveTail? first) :: (← primitiveTails? rest))

inductive PrimitiveTailsReading : List CanonicalTerm → List PrimitiveSpecifier → Prop where
  | nil : PrimitiveTailsReading [] []
  | cons (first : CanonicalTerm) (rest : List CanonicalTerm) (specifier : PrimitiveSpecifier)
      (specifiers : List PrimitiveSpecifier) (head : PrimitiveTailReading first specifier)
      (tail : PrimitiveTailsReading rest specifiers) :
      PrimitiveTailsReading (first :: rest) (specifier :: specifiers)

theorem primitiveTails_iff (terms : List CanonicalTerm) (specifiers : List PrimitiveSpecifier) :
    primitiveTails? terms = some specifiers ↔ PrimitiveTailsReading terms specifiers := by
  induction terms generalizing specifiers with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [primitiveTails?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, headParsed, tail, tailParsed, rfl⟩ := parsed
        exact .cons _ _ _ _ ((primitiveTail_iff _ _).mp headParsed) ((ih _).mp tailParsed)
      · intro reading
        cases reading with
        | cons _ _ head tail headReading tailReading =>
            simp only [primitiveTails?, (primitiveTail_iff _ _).mpr headReading,
              (ih _).mpr tailReading, bind, Option.bind_some]

/-- Unqualified standard integer type combinations from C11 6.7.2p2.
The selection accepts all permutations, with exact retained multiplicities. -/
def integerForms : List (List PrimitiveSpecifier × IntegerType IntegerExtension) :=
  let families : List (List PrimitiveSpecifier × StandardIntegerFamily) :=
    [([.short], .short), ([.short, .int], .short),
      ([.long], .long), ([.long, .int], .long),
      ([.long, .long], .longLong), ([.long, .long, .int], .longLong)]
  [([.int], .int), ([.signed], .int), ([.signed, .int], .int),
    ([.unsigned], .unsignedInt), ([.unsigned, .int], .unsignedInt),
    ([.signed, .char], .signed (.standard .char)),
    ([.unsigned, .char], .unsigned (.standard .char))] ++
    families.flatMap (fun row =>
      [(row.1, .signed (.standard row.2)),
        (.signed :: row.1, .signed (.standard row.2)),
        (.unsigned :: row.1, .unsigned (.standard row.2))])

theorem integerForms_consistent :
    ∀ first ∈ integerForms, ∀ second ∈ integerForms,
      first.1.Perm second.1 → first.2 = second.2 := by decide +kernel

def selectInteger? (specifiers : List PrimitiveSpecifier) :
    List (List PrimitiveSpecifier × IntegerType IntegerExtension) → Option (IntegerType IntegerExtension)
  | [] => none
  | row :: rows =>
      if specifiers.Perm row.1 then some row.2 else selectInteger? specifiers rows

def IntegerSpecifiers (specifiers : List PrimitiveSpecifier) (type : IntegerType IntegerExtension) : Prop :=
  ∃ canonical, (canonical, type) ∈ integerForms ∧ specifiers.Perm canonical

private theorem selectInteger_sound (specifiers : List PrimitiveSpecifier)
    (rows : List (List PrimitiveSpecifier × IntegerType IntegerExtension))
    (type : IntegerType IntegerExtension) (parsed : selectInteger? specifiers rows = some type) :
    ∃ canonical, (canonical, type) ∈ rows ∧ specifiers.Perm canonical := by
  induction rows with
  | nil => cases parsed
  | cons row rows ih =>
      by_cases matching : specifiers.Perm row.1
      · simp only [selectInteger?, if_pos matching, Option.some.injEq] at parsed
        subst type
        exact ⟨row.1, List.mem_cons_self, matching⟩
      · obtain ⟨canonical, member, perm⟩ := ih (by simpa only [selectInteger?, if_neg matching] using parsed)
        exact ⟨canonical, List.mem_cons_of_mem _ member, perm⟩

private theorem selectInteger_complete (specifiers : List PrimitiveSpecifier)
    (rows : List (List PrimitiveSpecifier × IntegerType IntegerExtension))
    (included : ∀ row ∈ rows, row ∈ integerForms) (canonical : List PrimitiveSpecifier)
    (type : IntegerType IntegerExtension) (member : (canonical, type) ∈ rows)
    (matching : specifiers.Perm canonical) : selectInteger? specifiers rows = some type := by
  induction rows with
  | nil => cases member
  | cons row rows ih =>
      by_cases selected : specifiers.Perm row.1
      · have same : row.2 = type := integerForms_consistent row (included row List.mem_cons_self)
          (canonical, type) (included _ member) (selected.symm.trans matching)
        simp only [selectInteger?, if_pos selected, same]
      · have following : (canonical, type) ∈ rows := by
          rcases List.mem_cons.mp member with same | following
          · cases same
            exact False.elim (selected matching)
          · exact following
        simpa only [selectInteger?, if_neg selected] using
          (ih (fun candidate found => included candidate (List.mem_cons_of_mem _ found)) following)

theorem selectInteger_iff (specifiers : List PrimitiveSpecifier) (type : IntegerType IntegerExtension) :
    selectInteger? specifiers integerForms = some type ↔ IntegerSpecifiers specifiers type := by
  constructor
  · exact selectInteger_sound specifiers integerForms type
  · rintro ⟨canonical, member, matching⟩
    exact selectInteger_complete specifiers integerForms (fun _ found => found) canonical type member matching

def typeName? : CanonicalTerm → Option (IntegerType IntegerExtension)
  | .node "TypeName" [.node "UniqueSpecifierQualifiers"
      [.node "Bool" [], .node "NoTypeQualifiers" []], .node "NoAbstractDeclarator" []] => some .boolean
  | .node "TypeName" [.node "PrimitiveSpecifierQualifiers" [first, .seq rest],
      .node "NoAbstractDeclarator" []] => do
      let head ← primitive? first
      let tail ← primitiveTails? rest
      selectInteger? (head :: tail) integerForms
  | _ => none

inductive TypeNameReading : CanonicalTerm → IntegerType IntegerExtension → Prop where
  | boolean : TypeNameReading (.node "TypeName" [.node "UniqueSpecifierQualifiers"
      [.node "Bool" [], .node "NoTypeQualifiers" []], .node "NoAbstractDeclarator" []]) .boolean
  | integer (first : CanonicalTerm) (rest : List CanonicalTerm) (head : PrimitiveSpecifier)
      (tail : List PrimitiveSpecifier) (type : IntegerType IntegerExtension)
      (firstReading : PrimitiveReading first head) (tailReading : PrimitiveTailsReading rest tail)
      (specifiers : IntegerSpecifiers (head :: tail) type) :
      TypeNameReading (.node "TypeName" [.node "PrimitiveSpecifierQualifiers" [first, .seq rest],
        .node "NoAbstractDeclarator" []]) type

theorem typeName_sound (term : CanonicalTerm) (type : IntegerType IntegerExtension)
    (parsed : typeName? term = some type) : TypeNameReading term type := by
  unfold typeName? at parsed
  split at parsed
  · cases parsed; exact .boolean
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨head, firstParsed, tail, tailParsed, selected⟩ := parsed
    exact .integer _ _ _ _ _ (primitive_sound _ _ firstParsed)
      ((primitiveTails_iff _ _).mp tailParsed) ((selectInteger_iff _ _).mp selected)
  · contradiction

theorem typeName_complete (term : CanonicalTerm) (type : IntegerType IntegerExtension)
    (reading : TypeNameReading term type) : typeName? term = some type := by
  cases reading with
  | boolean => rfl
  | integer first rest head tail type firstReading tailReading specifiers =>
      simp only [typeName?, primitive_complete _ _ firstReading,
        (primitiveTails_iff _ _).mpr tailReading, (selectInteger_iff _ _).mpr specifiers,
        bind, Option.bind_some]

theorem typeName_iff (term : CanonicalTerm) (type : IntegerType IntegerExtension) :
    typeName? term = some type ↔ TypeNameReading term type :=
  ⟨typeName_sound term type, typeName_complete term type⟩

def namedDestination? (environment : ScopedLvalues.Environment) (name : String) : Option Destination := do
  let location ← ScopedLvalues.lookup environment name
  destination location

inductive NamedDestination (environment : ScopedLvalues.Environment) (name : String) : Destination → Prop where
  | bound (selected : Destination) (binding : ScopedLvalues.Binding name environment selected.location) :
      NamedDestination environment name selected

theorem namedDestination_sound (environment : ScopedLvalues.Environment) (name : String) (selected : Destination)
    (parsed : namedDestination? environment name = some selected) : NamedDestination environment name selected := by
  obtain ⟨location, found, typed⟩ := Option.bind_eq_some_iff.mp parsed
  have same : selected.location = location := by
    unfold destination at typed
    split at typed
    · contradiction
    · cases typed; rfl
  exact .bound selected (same.symm ▸ ScopedLvalues.lookup_sound _ _ _ found)

theorem namedDestination_complete (environment : ScopedLvalues.Environment) (name : String) (selected : Destination)
    (reading : NamedDestination environment name selected) : namedDestination? environment name = some selected := by
  cases reading with
  | bound binding =>
      simp only [namedDestination?, ScopedLvalues.lookup_complete _ _ _ binding,
        bind, Option.bind_some, destination_complete]

theorem namedDestination_iff (environment : ScopedLvalues.Environment) (name : String) (selected : Destination) :
    namedDestination? environment name = some selected ↔ NamedDestination environment name selected :=
  ⟨namedDestination_sound environment name selected, namedDestination_complete environment name selected⟩

end Mettapedia.Languages.C11.CestaExpressionElaboration

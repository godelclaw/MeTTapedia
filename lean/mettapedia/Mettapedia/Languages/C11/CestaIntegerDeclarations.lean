import Mettapedia.Languages.C11.CestaExpressionElaboration
import Mettapedia.Languages.C11.IntegerObjectConstruction

/-!
# Cesta integer declarations into constructed object requests

The selected canonical CDecl representation is read into the existing
integer declaration carrier. Primitive specifier permutations share the
expression adapter's checked C11 type formation. Declarators retain names,
scalar versus array type, positive constant bounds and arbitrary enclosing
parentheses. Initializer syntax distinguishes indeterminate entry from an
explicit ordinary zero initializer, including the array form `{0}`.

Sorted wire admission uses Cesta's schema and lexical policy, not a
replacement declaration grammar. General syntax correspondence is proved
against independent reading rules. A separately checked object constructor
then derives locations from the admitted declaration and layout.

This adapter covers unqualified standard integers and one-dimensional arrays
with positive unsuffixed decimal `int` bounds. Qualifiers, storage classes,
typedefs, pointers, functions, multidimensional and variable-length arrays,
other constant-expression bounds and nonzero/designated initializers remain
additional source profiles. An initializer descriptor is not an executed
initializer. Non-VLA lifetimes begin at block entry; explicit initializers
execute when their declaration is reached. The native byte parser and
complete ordinary-C declaration elaboration are separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaIntegerDeclarations

open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
  (Schema Notation Sorted encode? decode? decode_sorted encode_decoded decode_encoded)
open CestaExpressionElaboration IntegerObjectConstruction

def tail? : CanonicalTerm → Option PrimitiveSpecifier
  | .node "PrimitiveSpecifierTail" [term] => primitive? term
  | _ => none

inductive TailReading : CanonicalTerm → PrimitiveSpecifier → Prop where
  | tail (term : CanonicalTerm) (specifier : PrimitiveSpecifier) (reading : PrimitiveReading term specifier) :
      TailReading (.node "PrimitiveSpecifierTail" [term]) specifier

theorem tail_iff (term : CanonicalTerm) (specifier : PrimitiveSpecifier) :
    tail? term = some specifier ↔ TailReading term specifier := by
  constructor
  · intro parsed
    unfold tail? at parsed
    split at parsed
    · exact .tail _ _ (primitive_sound _ _ parsed)
    · contradiction
  · intro reading
    cases reading with
    | tail term specifier reading => exact primitive_complete _ _ reading

def tails? : List CanonicalTerm → Option (List PrimitiveSpecifier)
  | [] => some []
  | first :: rest => do some ((← tail? first) :: (← tails? rest))

inductive TailsReading : List CanonicalTerm → List PrimitiveSpecifier → Prop where
  | nil : TailsReading [] []
  | cons (first : CanonicalTerm) (rest : List CanonicalTerm) (specifier : PrimitiveSpecifier)
      (specifiers : List PrimitiveSpecifier) (head : TailReading first specifier) (tail : TailsReading rest specifiers) :
      TailsReading (first :: rest) (specifier :: specifiers)

theorem tails_iff (terms : List CanonicalTerm) (specifiers : List PrimitiveSpecifier) :
    tails? terms = some specifiers ↔ TailsReading terms specifiers := by
  induction terms generalizing specifiers with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [tails?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, headParsed, tail, tailParsed, rfl⟩ := parsed
        exact .cons _ _ _ _ ((tail_iff _ _).mp headParsed) ((ih _).mp tailParsed)
      · intro reading
        cases reading with
        | cons _ _ head tail headReading tailReading =>
            simp only [tails?, (tail_iff _ _).mpr headReading, (ih _).mpr tailReading, bind, Option.bind_some]

def specifiers? : CanonicalTerm → Option (IntegerType IntegerExtension)
  | .node "UniqueDeclarationSpecifiers" [.node "Bool" [], .seq []] => some .boolean
  | .node "PrimitiveDeclarationSpecifiers" [first, .seq rest] => do
      let head ← primitive? first
      let tail ← tails? rest
      selectInteger? (head :: tail) integerForms
  | _ => none

inductive SpecifiersReading : CanonicalTerm → IntegerType IntegerExtension → Prop where
  | boolean : SpecifiersReading (.node "UniqueDeclarationSpecifiers" [.node "Bool" [], .seq []]) .boolean
  | integer (first : CanonicalTerm) (rest : List CanonicalTerm) (head : PrimitiveSpecifier)
      (tail : List PrimitiveSpecifier) (type : IntegerType IntegerExtension)
      (firstReading : PrimitiveReading first head) (tailReading : TailsReading rest tail)
      (specifiers : IntegerSpecifiers (head :: tail) type) :
      SpecifiersReading (.node "PrimitiveDeclarationSpecifiers" [first, .seq rest]) type

theorem specifiers_sound (term : CanonicalTerm) (type : IntegerType IntegerExtension)
    (parsed : specifiers? term = some type) : SpecifiersReading term type := by
  unfold specifiers? at parsed
  split at parsed
  · cases parsed; exact .boolean
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨head, firstParsed, tail, tailParsed, selected⟩ := parsed
    exact .integer _ _ _ _ _ (primitive_sound _ _ firstParsed)
      ((tails_iff _ _).mp tailParsed) ((selectInteger_iff _ _).mp selected)
  · contradiction

theorem specifiers_complete (term : CanonicalTerm) (type : IntegerType IntegerExtension)
    (reading : SpecifiersReading term type) : specifiers? term = some type := by
  cases reading with
  | boolean => rfl
  | integer first rest head tail type firstReading tailReading specifiers =>
      simp only [specifiers?, primitive_complete _ _ firstReading, (tails_iff _ _).mpr tailReading,
        (selectInteger_iff _ _).mpr specifiers, bind, Option.bind_some]

def bound? (model : IntegerMemoryModel.Model) (spelling : String) : Option { count : Nat // 0 < count } := do
  let count ← decimal? spelling
  if admitted : 0 < count ∧ (IntegerType.int.format model.parameters).Represents (Int.ofNat count) then
    some ⟨count, admitted.1⟩
  else none

def BoundReading (model : IntegerMemoryModel.Model) (spelling : String) (count : Nat) : Prop :=
  DecimalToken spelling count ∧ 0 < count ∧ (IntegerType.int.format model.parameters).Represents (Int.ofNat count)

theorem bound_sound (model : IntegerMemoryModel.Model) (spelling : String) (count : { count : Nat // 0 < count })
    (parsed : bound? model spelling = some count) : BoundReading model spelling count.val := by
  simp only [bound?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨actual, token, accepted⟩ := parsed
  split at accepted
  · rename_i admitted
    cases accepted
    exact ⟨(decimal_iff _ _).mp token, admitted⟩
  · contradiction

theorem bound_complete (model : IntegerMemoryModel.Model) (spelling : String) (count : { count : Nat // 0 < count })
    (reading : BoundReading model spelling count.val) : bound? model spelling = some count := by
  obtain ⟨token, positive, fits⟩ := reading
  simp only [bound?, (decimal_iff _ _).mpr token, bind, Option.bind_some,
    dif_pos (show 0 < count.val ∧ (IntegerType.int.format model.parameters).Represents (Int.ofNat count.val) from ⟨positive, fits⟩)]

def direct? (model : IntegerMemoryModel.Model) : CanonicalTerm → Option (String × Shape)
  | .node "NameDeclarator" [.text name] => some (name, .scalar)
  | .node "ParenthesizedDeclarator" [.node "Declarator" [child]] => direct? model child
  | .node "ArrayDeclarator" [base, .node "NoTypeQualifiers" [],
      .node "SomeExpression" [.node "IntConst" [.text spelling]]] => do
      let selected ← direct? model base
      match selected.2 with
      | .scalar =>
          let count ← bound? model spelling
          some (selected.1, .array count.val count.property)
      | .array _ _ => none
  | _ => none
termination_by term => sizeOf term

inductive DirectReading (model : IntegerMemoryModel.Model) : CanonicalTerm → String → Shape → Prop where
  | name (name : String) : DirectReading model (.node "NameDeclarator" [.text name]) name .scalar
  | parenthesized (child : CanonicalTerm) (name : String) (shape : Shape) (reading : DirectReading model child name shape) :
      DirectReading model (.node "ParenthesizedDeclarator" [.node "Declarator" [child]]) name shape
  | array (base : CanonicalTerm) (name spelling : String) (count : Nat) (positive : 0 < count)
      (baseReading : DirectReading model base name .scalar) (bound : BoundReading model spelling count) :
      DirectReading model (.node "ArrayDeclarator" [base, .node "NoTypeQualifiers" [],
        .node "SomeExpression" [.node "IntConst" [.text spelling]]]) name (.array count positive)

theorem direct_complete (model : IntegerMemoryModel.Model) (term : CanonicalTerm) (name : String) (shape : Shape)
    (reading : DirectReading model term name shape) : direct? model term = some (name, shape) := by
  induction reading with
  | name => simp only [direct?]
  | parenthesized child name shape reading ih => simpa only [direct?] using ih
  | array base name spelling count positive baseReading bound ih =>
      simp only [direct?, ih, bind, Option.bind_some, bound_complete model spelling ⟨count, positive⟩ bound]

theorem direct_sound (model : IntegerMemoryModel.Model) (term : CanonicalTerm) (name : String) (shape : Shape)
    (parsed : direct? model term = some (name, shape)) : DirectReading model term name shape := by
  unfold direct? at parsed
  split at parsed
  · cases parsed; exact .name _
  · exact .parenthesized _ _ _ (direct_sound model _ _ _ parsed)
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨⟨selected, selectedShape⟩, selectedReading, following⟩ := parsed
    cases selectedShape with
    | scalar =>
        obtain ⟨count, bound, same⟩ := Option.bind_eq_some_iff.mp following
        cases same
        exact .array _ _ _ _ _ (direct_sound _ _ _ _ selectedReading) (bound_sound _ _ _ bound)
    | array => cases following
  · contradiction
termination_by sizeOf term

def declarator? (model : IntegerMemoryModel.Model) : CanonicalTerm → Option (String × Shape)
  | .node "Declarator" [direct] => direct? model direct
  | _ => none

inductive DeclaratorReading (model : IntegerMemoryModel.Model) : CanonicalTerm → String → Shape → Prop where
  | declarator (direct : CanonicalTerm) (name : String) (shape : Shape) (reading : DirectReading model direct name shape) :
      DeclaratorReading model (.node "Declarator" [direct]) name shape

theorem declarator_iff (model : IntegerMemoryModel.Model) (term : CanonicalTerm) (name : String) (shape : Shape) :
    declarator? model term = some (name, shape) ↔ DeclaratorReading model term name shape := by
  constructor
  · intro parsed
    unfold declarator? at parsed
    split at parsed
    · exact .declarator _ _ _ (direct_sound _ _ _ _ parsed)
    · contradiction
  · intro reading
    cases reading with
    | declarator direct name shape reading => exact direct_complete _ _ _ _ reading

def zeroInitializer? (shape : Shape) : CanonicalTerm → Bool
  | .node "InitializerExpression" [.node "IntConst" [.text "0"]] => shape == .scalar
  | .node "InitializerList" [.seq [.node "InitializerElement"
      [.node "InitializerExpression" [.node "IntConst" [.text "0"]]]]] => true
  | .node "InitializerListComma" [.seq [.node "InitializerElement"
      [.node "InitializerExpression" [.node "IntConst" [.text "0"]]]]] => true
  | _ => false

inductive ZeroInitializer : Shape → CanonicalTerm → Prop where
  | expression : ZeroInitializer .scalar (.node "InitializerExpression" [.node "IntConst" [.text "0"]])
  | list (shape : Shape) : ZeroInitializer shape (.node "InitializerList" [.seq [.node "InitializerElement"
      [.node "InitializerExpression" [.node "IntConst" [.text "0"]]]]])
  | listComma (shape : Shape) : ZeroInitializer shape (.node "InitializerListComma" [.seq [.node "InitializerElement"
      [.node "InitializerExpression" [.node "IntConst" [.text "0"]]]]])

theorem zeroInitializer_iff (shape : Shape) (term : CanonicalTerm) :
    zeroInitializer? shape term = true ↔ ZeroInitializer shape term := by
  constructor
  · intro accepted
    unfold zeroInitializer? at accepted
    split at accepted
    · have scalar : shape = .scalar := by simpa only [beq_iff_eq] using accepted
      subst shape; exact .expression
    · exact .list _
    · exact .listComma _
    · contradiction
  · intro reading
    cases reading <;> rfl

structure Entry where
  declaration : Declaration
  initialContents : InitialContents
  deriving DecidableEq, Repr

def entry? (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) : CanonicalTerm → Option Entry
  | .node "InitDeclarator" [term] => do
      let selected ← declarator? model term
      some ⟨⟨selected.1, type, selected.2⟩, .indeterminate⟩
  | .node "InitDeclaratorValue" [term, initializer] => do
      let selected ← declarator? model term
      if zeroInitializer? selected.2 initializer then some ⟨⟨selected.1, type, selected.2⟩, .zero⟩ else none
  | _ => none

inductive EntryReading (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) : CanonicalTerm → Entry → Prop where
  | indeterminate (term : CanonicalTerm) (name : String) (shape : Shape) (reading : DeclaratorReading model term name shape) :
      EntryReading model type (.node "InitDeclarator" [term]) ⟨⟨name, type, shape⟩, .indeterminate⟩
  | zero (term initializer : CanonicalTerm) (name : String) (shape : Shape)
      (reading : DeclaratorReading model term name shape) (zero : ZeroInitializer shape initializer) :
      EntryReading model type (.node "InitDeclaratorValue" [term, initializer]) ⟨⟨name, type, shape⟩, .zero⟩

theorem entry_sound (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) (term : CanonicalTerm)
    (entry : Entry) (parsed : entry? model type term = some entry) : EntryReading model type term entry := by
  unfold entry? at parsed
  split at parsed
  · simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨⟨name, shape⟩, selected, rfl⟩ := parsed
    exact .indeterminate _ _ _ ((declarator_iff _ _ _ _).mp selected)
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨⟨name, shape⟩, selected, result⟩ := parsed
    split at result
    · rename_i zero
      cases result
      exact .zero _ _ _ _ ((declarator_iff _ _ _ _).mp selected) ((zeroInitializer_iff _ _).mp zero)
    · contradiction
  · contradiction

theorem entry_complete (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) (term : CanonicalTerm)
    (entry : Entry) (reading : EntryReading model type term entry) : entry? model type term = some entry := by
  cases reading with
  | indeterminate term name shape reading =>
      simp only [entry?, (declarator_iff _ _ _ _).mpr reading, bind, Option.bind_some]
  | zero term initializer name shape reading zero =>
      simp only [entry?, (declarator_iff _ _ _ _).mpr reading, bind, Option.bind_some,
        (zeroInitializer_iff _ _).mpr zero, ↓reduceIte]

def entries? (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) :
    List CanonicalTerm → Option (List Entry)
  | [] => some []
  | first :: rest => do some ((← entry? model type first) :: (← entries? model type rest))

inductive EntriesReading (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension) :
    List CanonicalTerm → List Entry → Prop where
  | nil : EntriesReading model type [] []
  | cons (first : CanonicalTerm) (rest : List CanonicalTerm) (entry : Entry) (entries : List Entry)
      (head : EntryReading model type first entry) (tail : EntriesReading model type rest entries) :
      EntriesReading model type (first :: rest) (entry :: entries)

theorem entries_iff (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension)
    (terms : List CanonicalTerm) (entries : List Entry) :
    entries? model type terms = some entries ↔ EntriesReading model type terms entries := by
  induction terms generalizing entries with
  | nil =>
      constructor
      · intro same; cases same; exact .nil
      · intro reading; cases reading; rfl
  | cons first rest ih =>
      constructor
      · intro parsed
        simp only [entries?, bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨head, parsedHead, tail, parsedTail, rfl⟩ := parsed
        exact .cons _ _ _ _ (entry_sound _ _ _ _ parsedHead) ((ih _).mp parsedTail)
      · intro reading
        cases reading with
        | cons first rest head tail headReading tailReading =>
            simp only [entries?, entry_complete _ _ _ _ headReading, (ih _).mpr tailReading, bind, Option.bind_some]

def readTerm (model : IntegerMemoryModel.Model) : CanonicalTerm → Option (List Entry)
  | .node "Declaration" [specifiers, .node "InitDeclarators" [.seq (first :: rest)]] => do
      let type ← specifiers? specifiers
      entries? model type (first :: rest)
  | _ => none

inductive Reading (model : IntegerMemoryModel.Model) : CanonicalTerm → List Entry → Prop where
  | declaration (specifiers first : CanonicalTerm) (rest : List CanonicalTerm) (type : IntegerType IntegerExtension)
      (entries : List Entry) (typed : SpecifiersReading specifiers type)
      (declarators : EntriesReading model type (first :: rest) entries) :
      Reading model (.node "Declaration" [specifiers, .node "InitDeclarators" [.seq (first :: rest)]]) entries

theorem readTerm_sound (model : IntegerMemoryModel.Model) (term : CanonicalTerm) (entries : List Entry)
    (parsed : readTerm model term = some entries) : Reading model term entries := by
  unfold readTerm at parsed
  split at parsed
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨type, typed, declarators⟩ := parsed
    exact .declaration _ _ _ _ _ (specifiers_sound _ _ typed) ((entries_iff _ _ _ _).mp declarators)
  · contradiction

theorem readTerm_complete (model : IntegerMemoryModel.Model) (term : CanonicalTerm) (entries : List Entry)
    (reading : Reading model term entries) : readTerm model term = some entries := by
  cases reading with
  | declaration specifiers first rest type entries typed declarators =>
      simp only [readTerm, specifiers_complete _ _ typed, (entries_iff _ _ _ _).mpr declarators, bind, Option.bind_some]

def read (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (wire : CestaObjectAccess.Wire) : Option (List Entry) := do
  readTerm model (← decode? schema codecProfile sort wire)

def WireReading (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (wire : CestaObjectAccess.Wire) (entries : List Entry) : Prop :=
  ∃ term, Sorted schema codecProfile sort term ∧ encode? schema codecProfile sort term = some wire ∧ Reading model term entries

theorem read_sound (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (wire : CestaObjectAccess.Wire) (entries : List Entry) (parsed : read schema codecProfile sort model wire = some entries) :
    WireReading schema codecProfile sort model wire entries := by
  simp only [read, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨term, decoded, reading⟩ := parsed
  exact ⟨term, decode_sorted _ _ _ _ _ decoded, encode_decoded _ _ _ _ _ decoded, readTerm_sound _ _ _ reading⟩

theorem read_complete (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (wire : CestaObjectAccess.Wire) (entries : List Entry) (reading : WireReading schema codecProfile sort model wire entries) :
    read schema codecProfile sort model wire = some entries := by
  obtain ⟨term, _, encoded, reading⟩ := reading
  simp only [read, decode_encoded _ _ _ _ _ encoded, readTerm_complete _ _ _ reading, bind, Option.bind_some]

theorem read_iff (schema : Schema) (codecProfile : Notation) (sort : String) (model : IntegerMemoryModel.Model)
    (wire : CestaObjectAccess.Wire) (entries : List Entry) :
    read schema codecProfile sort model wire = some entries ↔ WireReading schema codecProfile sort model wire entries :=
  ⟨read_sound _ _ _ _ _ _, read_complete _ _ _ _ _ _⟩

theorem read_entry_constructed (model : IntegerMemoryModel.Model) (type : IntegerType IntegerExtension)
    (term : CanonicalTerm) (entry : Entry) (parsed : entry? model type term = some entry)
    (before : ObjectAccessMemory.State model.characters) (arrays : ArrayPointers.Catalog)
    (element : ObjectLayout.Layout) (identity : Mettapedia.Machines.CMemory.BlockId)
    (mode : InitialContents) (result : Constructed model)
    (created : construct model before arrays entry.declaration element identity mode = some result) :
    EntryReading model type term entry ∧
    Creation model (ObjectAccessMemory.represent before) arrays entry.declaration element identity mode
      (ObjectAccessMemory.represent result.memory) result.arrays result.location :=
  ⟨entry_sound _ _ _ _ parsed, construct_sound _ _ _ _ _ _ _ _ created⟩

end Mettapedia.Languages.C11.CestaIntegerDeclarations

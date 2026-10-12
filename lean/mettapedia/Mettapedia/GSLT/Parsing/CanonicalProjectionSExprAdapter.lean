import Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
import Mettapedia.GSLT.Parsing.NonemptySeparatorRefactoring

/-!
# Canonical grammar projections and sort-directed codec values

CanonicalGrammar names a token leaf by its class and names a list projection
by its classification key. The sorted codec instead carries bare token text
and bare ordered sequences at the corresponding sorts. This recursive adapter
checks the actual schema, constructor arities, lexical admission, and exact
source wrapper names. It neither guesses wrapper names nor globally erases
nodes with one child.

The independent relation `Adapts` records both representations. Successful
conversions are exact in both directions. Source grammar derivability remains
a separate contract; byte readers and native parser implementation are outside
this structural boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter

open CanonicalGrammar (CanonicalTerm Grammar Classification ListForm Tree Tok Derives canon)
open SortedCanonicalSExprCodec
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Exact source metadata at each expected sort, supplied by the projection
classification. Constructor declarations remain those of the actual schema. -/
structure Layout where
  tokenHead : String → String
  listKey : String → String

mutual
  def toCodec? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :
      CanonicalTerm → Option CanonicalTerm
    | .text _ => none
    | .seq _ => none
    | .node name children => do
        let shape ← schema.shape? sort
        match shape with
        | .token _ =>
            let [.text spelling] := children | none
            if name = layout.tokenHead sort ∧ schema.acceptsToken sort spelling = true
            then some (.text spelling) else none
        | .constructors declarations => do
            let declaration ← constructor? profile declarations name
            let arguments ← toArguments? schema profile layout declaration.arguments children
            pure (.node name arguments)
        | .list elementSort =>
            let [.seq elements] := children | none
            if name = layout.listKey sort then
              (toElements? schema profile layout elementSort elements).map CanonicalTerm.seq
            else none

  def toArguments? (schema : Schema) (profile : Notation) (layout : Layout) :
      List String → List CanonicalTerm → Option (List CanonicalTerm)
    | [], [] => some []
    | sort :: sorts, child :: children => do
        return (← toCodec? schema profile layout sort child) ::
          (← toArguments? schema profile layout sorts children)
    | _, _ => none

  def toElements? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :
      List CanonicalTerm → Option (List CanonicalTerm)
    | [] => some []
    | child :: children => do
        return (← toCodec? schema profile layout sort child) ::
          (← toElements? schema profile layout sort children)
end

mutual
  def fromCodec? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :
      CanonicalTerm → Option CanonicalTerm
    | .text spelling =>
        match schema.shape? sort with
        | some (.token _) =>
            if schema.acceptsToken sort spelling then
              some (.node (layout.tokenHead sort) [.text spelling]) else none
        | _ => none
    | .node name children => do
        let .constructors declarations ← schema.shape? sort | none
        let declaration ← constructor? profile declarations name
        let arguments ← fromArguments? schema profile layout declaration.arguments children
        pure (.node name arguments)
    | .seq elements => do
        let .list elementSort ← schema.shape? sort | none
        let arguments ← fromElements? schema profile layout elementSort elements
        pure (.node (layout.listKey sort) [.seq arguments])

  def fromArguments? (schema : Schema) (profile : Notation) (layout : Layout) :
      List String → List CanonicalTerm → Option (List CanonicalTerm)
    | [], [] => some []
    | sort :: sorts, child :: children => do
        return (← fromCodec? schema profile layout sort child) ::
          (← fromArguments? schema profile layout sorts children)
    | _, _ => none

  def fromElements? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :
      List CanonicalTerm → Option (List CanonicalTerm)
    | [] => some []
    | child :: children => do
        return (← fromCodec? schema profile layout sort child) ::
          (← fromElements? schema profile layout sort children)
end

mutual
  /-- Formation of both representations, independently of either conversion. -/
  inductive Adapts (schema : Schema) (profile : Notation) (layout : Layout) :
      String → CanonicalTerm → CanonicalTerm → Prop
    | token (sort spelling : String) (representation : TokenRepresentation)
        (shape : schema.shape? sort = some (.token representation))
        (accepted : schema.acceptsToken sort spelling = true) :
        Adapts schema profile layout sort
          (.node (layout.tokenHead sort) [.text spelling]) (.text spelling)
    | node (sort name : String) (declarations : List Constructor) (declaration : Constructor)
        (source children : List CanonicalTerm)
        (shape : schema.shape? sort = some (.constructors declarations))
        (found : constructor? profile declarations name = some declaration)
        (arguments : AdaptArguments schema profile layout declaration.arguments source children) :
        Adapts schema profile layout sort (.node name source) (.node name children)
    | list (sort elementSort : String) (source children : List CanonicalTerm)
        (shape : schema.shape? sort = some (.list elementSort))
        (elements : AdaptElements schema profile layout elementSort source children) :
        Adapts schema profile layout sort (.node (layout.listKey sort) [.seq source]) (.seq children)

  inductive AdaptArguments (schema : Schema) (profile : Notation) (layout : Layout) :
      List String → List CanonicalTerm → List CanonicalTerm → Prop
    | nil : AdaptArguments schema profile layout [] [] []
    | cons {sort : String} {sorts : List String} {source child : CanonicalTerm}
        {sources children : List CanonicalTerm}
        (head : Adapts schema profile layout sort source child)
        (tail : AdaptArguments schema profile layout sorts sources children) :
        AdaptArguments schema profile layout (sort :: sorts) (source :: sources) (child :: children)

  inductive AdaptElements (schema : Schema) (profile : Notation) (layout : Layout) :
      String → List CanonicalTerm → List CanonicalTerm → Prop
    | nil (sort : String) : AdaptElements schema profile layout sort [] []
    | cons {sort : String} {source child : CanonicalTerm} {sources children : List CanonicalTerm}
        (head : Adapts schema profile layout sort source child)
        (tail : AdaptElements schema profile layout sort sources children) :
        AdaptElements schema profile layout sort (source :: sources) (child :: children)
end

variable {schema : Schema} {profile : Notation} {layout : Layout}

mutual
  theorem Adapts.codec_sorted {sort : String} {source term : CanonicalTerm}
      (adapted : Adapts schema profile layout sort source term) : Sorted schema profile sort term := by
    cases adapted with
    | token sort spelling representation shape accepted => exact .token _ _ _ shape accepted
    | node sort name declarations declaration source children shape found arguments =>
        exact .node _ _ _ _ _ shape found arguments.codec_sorted
    | list sort elementSort source children shape elements =>
        exact .list _ _ _ shape elements.codec_sorted
  termination_by sizeOf term

  theorem AdaptArguments.codec_sorted {sorts : List String} {source terms : List CanonicalTerm}
      (adapted : AdaptArguments schema profile layout sorts source terms) :
      SortedArguments schema profile sorts terms := by
    cases adapted with
    | nil => exact .nil
    | cons head tail => exact .cons head.codec_sorted tail.codec_sorted
  termination_by sizeOf terms

  theorem AdaptElements.codec_sorted {sort : String} {source terms : List CanonicalTerm}
      (adapted : AdaptElements schema profile layout sort source terms) :
      SortedElements schema profile sort terms := by
    cases adapted with
    | nil sort => exact .nil sort
    | cons head tail => exact .cons head.codec_sorted tail.codec_sorted
  termination_by sizeOf terms
end

mutual
  theorem Adapts.toCodec {sort : String} {source term : CanonicalTerm}
      (adapted : Adapts schema profile layout sort source term) :
      toCodec? schema profile layout sort source = some term := by
    cases adapted with
    | token sort spelling representation shape accepted => simp [toCodec?.eq_def, shape, accepted]
    | node sort name declarations declaration source children shape found arguments =>
        simp [toCodec?.eq_def, shape, found, arguments.toCodec]
    | list sort elementSort source children shape elements =>
        simp [toCodec?.eq_def, shape, elements.toCodec]
  termination_by sizeOf source

  theorem AdaptArguments.toCodec {sorts : List String} {source terms : List CanonicalTerm}
      (adapted : AdaptArguments schema profile layout sorts source terms) :
      toArguments? schema profile layout sorts source = some terms := by
    cases adapted with
    | nil => rfl
    | cons head tail => simp [toArguments?, head.toCodec, tail.toCodec]
  termination_by sizeOf source

  theorem AdaptElements.toCodec {sort : String} {source terms : List CanonicalTerm}
      (adapted : AdaptElements schema profile layout sort source terms) :
      toElements? schema profile layout sort source = some terms := by
    cases adapted with
    | nil => rfl
    | cons head tail => simp [toElements?, head.toCodec, tail.toCodec]
  termination_by sizeOf source
end

mutual
  theorem Adapts.fromCodec {sort : String} {source term : CanonicalTerm}
      (adapted : Adapts schema profile layout sort source term) :
      fromCodec? schema profile layout sort term = some source := by
    cases adapted with
    | token sort spelling representation shape accepted => simp [fromCodec?, shape, accepted]
    | node sort name declarations declaration source children shape found arguments =>
        simp [fromCodec?, shape, found, arguments.fromCodec]
    | list sort elementSort source children shape elements =>
        simp [fromCodec?, shape, elements.fromCodec]
  termination_by sizeOf term

  theorem AdaptArguments.fromCodec {sorts : List String} {source terms : List CanonicalTerm}
      (adapted : AdaptArguments schema profile layout sorts source terms) :
      fromArguments? schema profile layout sorts terms = some source := by
    cases adapted with
    | nil => rfl
    | cons head tail => simp [fromArguments?, head.fromCodec, tail.fromCodec]
  termination_by sizeOf terms

  theorem AdaptElements.fromCodec {sort : String} {source terms : List CanonicalTerm}
      (adapted : AdaptElements schema profile layout sort source terms) :
      fromElements? schema profile layout sort terms = some source := by
    cases adapted with
    | nil => rfl
    | cons head tail => simp [fromElements?, head.fromCodec, tail.fromCodec]
  termination_by sizeOf terms
end

mutual
  theorem fromCodec_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sort : String) (term source : CanonicalTerm)
      (converted : fromCodec? schema profile layout sort term = some source) :
      Adapts schema profile layout sort source term := by
    cases term with
    | text spelling =>
        cases shape : schema.shape? sort with
        | none => simp [fromCodec?, shape] at converted
        | some shapeValue =>
            cases shapeValue with
            | constructors declarations => simp [fromCodec?, shape] at converted
            | list elementSort => simp [fromCodec?, shape] at converted
            | token representation =>
                cases accepted : schema.acceptsToken sort spelling with
                | false => simp [fromCodec?, shape, accepted] at converted
                | true =>
                    simp [fromCodec?, shape, accepted] at converted
                    subst source
                    exact .token sort spelling representation shape accepted
    | node name children =>
        cases shape : schema.shape? sort with
        | none => simp [fromCodec?, shape] at converted
        | some shapeValue =>
            cases shapeValue with
            | token representation => simp [fromCodec?, shape] at converted
            | list elementSort => simp [fromCodec?, shape] at converted
            | constructors declarations =>
                cases found : constructor? profile declarations name with
                | none => simp [fromCodec?, shape, found] at converted
                | some declaration =>
                    cases arguments : fromArguments? schema profile layout declaration.arguments children with
                    | none => simp [fromCodec?, shape, found, arguments] at converted
                    | some values =>
                        simp [fromCodec?, shape, found, arguments] at converted
                        subst source
                        exact .node sort name declarations declaration values children shape found
                          (fromArguments_adapts schema profile layout declaration.arguments children values arguments)
    | seq elements =>
        cases shape : schema.shape? sort with
        | none => simp [fromCodec?, shape] at converted
        | some shapeValue =>
            cases shapeValue with
            | token representation => simp [fromCodec?, shape] at converted
            | constructors declarations => simp [fromCodec?, shape] at converted
            | list elementSort =>
                cases arguments : fromElements? schema profile layout elementSort elements with
                | none => simp [fromCodec?, shape, arguments] at converted
                | some values =>
                    simp [fromCodec?, shape, arguments] at converted
                    subst source
                    exact .list sort elementSort values elements shape
                      (fromElements_adapts schema profile layout elementSort elements values arguments)
  termination_by sizeOf term

  theorem fromArguments_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sorts : List String) (terms source : List CanonicalTerm)
      (converted : fromArguments? schema profile layout sorts terms = some source) :
      AdaptArguments schema profile layout sorts source terms := by
    cases terms with
    | nil =>
        cases sorts <;> simp [fromArguments?] at converted
        subst source
        exact .nil
    | cons child children =>
        cases sorts with
        | nil => simp [fromArguments?] at converted
        | cons sort sorts =>
            cases head : fromCodec? schema profile layout sort child with
            | none => simp [fromArguments?, head] at converted
            | some value =>
                cases tail : fromArguments? schema profile layout sorts children with
                | none => simp [fromArguments?, head, tail] at converted
                | some rest =>
                    simp [fromArguments?, head, tail] at converted
                    subst source
                    exact .cons (fromCodec_adapts schema profile layout sort child value head)
                      (fromArguments_adapts schema profile layout sorts children rest tail)
  termination_by sizeOf terms

  theorem fromElements_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sort : String) (terms source : List CanonicalTerm)
      (converted : fromElements? schema profile layout sort terms = some source) :
      AdaptElements schema profile layout sort source terms := by
    cases terms with
    | nil =>
        simp [fromElements?] at converted
        subst source
        exact .nil sort
    | cons child children =>
        cases head : fromCodec? schema profile layout sort child with
        | none => simp [fromElements?, head] at converted
        | some value =>
            cases tail : fromElements? schema profile layout sort children with
            | none => simp [fromElements?, head, tail] at converted
            | some rest =>
                simp [fromElements?, head, tail] at converted
                subst source
                exact .cons (fromCodec_adapts schema profile layout sort child value head)
                  (fromElements_adapts schema profile layout sort children rest tail)
  termination_by sizeOf terms
end

mutual
  theorem toCodec_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sort : String) (source term : CanonicalTerm)
      (converted : toCodec? schema profile layout sort source = some term) :
      Adapts schema profile layout sort source term := by
    cases source with
    | text spelling => simp [toCodec?.eq_def] at converted
    | seq elements => simp [toCodec?.eq_def] at converted
    | node name children =>
        cases shape : schema.shape? sort with
        | none => simp [toCodec?.eq_def, shape] at converted
        | some shapeValue =>
            cases shapeValue with
            | token representation =>
                cases children with
                | nil => simp [toCodec?.eq_def, shape] at converted
                | cons child children =>
                    cases children with
                    | cons next rest => simp [toCodec?.eq_def, shape] at converted
                    | nil =>
                        cases child with
                        | node childName kids => simp [toCodec?.eq_def, shape] at converted
                        | seq elems => simp [toCodec?.eq_def, shape] at converted
                        | text spelling =>
                            by_cases guard : name = layout.tokenHead sort ∧
                                schema.acceptsToken sort spelling = true
                            · simp [toCodec?.eq_def, shape, guard] at converted
                              subst term
                              rw [guard.1]
                              exact .token sort spelling representation shape guard.2
                            · simp [toCodec?.eq_def, shape, guard] at converted
            | constructors declarations =>
                cases found : constructor? profile declarations name with
                | none => simp [toCodec?.eq_def, shape, found] at converted
                | some declaration =>
                    cases arguments : toArguments? schema profile layout declaration.arguments children with
                    | none => simp [toCodec?.eq_def, shape, found, arguments] at converted
                    | some values =>
                        simp [toCodec?.eq_def, shape, found, arguments] at converted
                        subst term
                        exact .node sort name declarations declaration children values shape found
                          (toArguments_adapts schema profile layout declaration.arguments children values arguments)
            | list elementSort =>
                cases children with
                | nil => simp [toCodec?.eq_def, shape] at converted
                | cons child children =>
                    cases children with
                    | cons next rest => simp [toCodec?.eq_def, shape] at converted
                    | nil =>
                        cases child with
                        | node childName kids => simp [toCodec?.eq_def, shape] at converted
                        | text spelling => simp [toCodec?.eq_def, shape] at converted
                        | seq elements =>
                            by_cases same : name = layout.listKey sort
                            · cases values : toElements? schema profile layout elementSort elements with
                              | none => simp [toCodec?.eq_def, shape, same, values] at converted
                              | some terms =>
                                  simp [toCodec?.eq_def, shape, same, values] at converted
                                  subst term
                                  rw [same]
                                  exact .list sort elementSort elements terms shape
                                    (toElements_adapts schema profile layout elementSort elements terms values)
                            · simp [toCodec?.eq_def, shape, same] at converted
  termination_by sizeOf source

  theorem toArguments_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sorts : List String) (source terms : List CanonicalTerm)
      (converted : toArguments? schema profile layout sorts source = some terms) :
      AdaptArguments schema profile layout sorts source terms := by
    cases source with
    | nil =>
        cases sorts <;> simp [toArguments?] at converted
        subst terms
        exact .nil
    | cons child children =>
        cases sorts with
        | nil => simp [toArguments?] at converted
        | cons sort sorts =>
            cases head : toCodec? schema profile layout sort child with
            | none => simp [toArguments?, head] at converted
            | some value =>
                cases tail : toArguments? schema profile layout sorts children with
                | none => simp [toArguments?, head, tail] at converted
                | some rest =>
                    simp [toArguments?, head, tail] at converted
                    subst terms
                    exact .cons (toCodec_adapts schema profile layout sort child value head)
                      (toArguments_adapts schema profile layout sorts children rest tail)
  termination_by sizeOf source

  theorem toElements_adapts (schema : Schema) (profile : Notation) (layout : Layout)
      (sort : String) (source terms : List CanonicalTerm)
      (converted : toElements? schema profile layout sort source = some terms) :
      AdaptElements schema profile layout sort source terms := by
    cases source with
    | nil =>
        simp [toElements?] at converted
        subst terms
        exact .nil sort
    | cons child children =>
        cases head : toCodec? schema profile layout sort child with
        | none => simp [toElements?, head] at converted
        | some value =>
            cases tail : toElements? schema profile layout sort children with
            | none => simp [toElements?, head, tail] at converted
            | some rest =>
                simp [toElements?, head, tail] at converted
                subst terms
                exact .cons (toCodec_adapts schema profile layout sort child value head)
                  (toElements_adapts schema profile layout sort children rest tail)
  termination_by sizeOf source
end

theorem adapts_iff_toCodec (sort : String) (source term : CanonicalTerm) :
    Adapts schema profile layout sort source term ↔
      toCodec? schema profile layout sort source = some term :=
  ⟨Adapts.toCodec, toCodec_adapts schema profile layout sort source term⟩

theorem adapts_iff_fromCodec (sort : String) (source term : CanonicalTerm) :
    Adapts schema profile layout sort source term ↔
      fromCodec? schema profile layout sort term = some source :=
  ⟨Adapts.fromCodec, fromCodec_adapts schema profile layout sort term source⟩

theorem fromCodec_of_toCodec (sort : String) (source term : CanonicalTerm)
    (converted : toCodec? schema profile layout sort source = some term) :
    fromCodec? schema profile layout sort term = some source :=
  (toCodec_adapts schema profile layout sort source term converted).fromCodec

theorem toCodec_of_fromCodec (sort : String) (term source : CanonicalTerm)
    (converted : fromCodec? schema profile layout sort term = some source) :
    toCodec? schema profile layout sort source = some term :=
  (fromCodec_adapts schema profile layout sort term source converted).toCodec

theorem toCodec_some_iff_fromCodec (sort : String) (source term : CanonicalTerm) :
    toCodec? schema profile layout sort source = some term ↔
      fromCodec? schema profile layout sort term = some source :=
  ⟨fromCodec_of_toCodec sort source term, toCodec_of_fromCodec sort term source⟩

mutual
  theorem sorted_adapts (layout : Layout) {sort : String} {term : CanonicalTerm}
      (valid : Sorted schema profile sort term) :
      ∃ source, Adapts schema profile layout sort source term := by
    cases valid with
    | token sort spelling representation shape accepted =>
        exact ⟨_, .token sort spelling representation shape accepted⟩
    | node sort name declarations declaration children shape found arguments =>
        obtain ⟨source, adapted⟩ := sortedArguments_adapts layout arguments
        exact ⟨_, .node sort name declarations declaration source children shape found adapted⟩
    | list sort elementSort children shape elements =>
        obtain ⟨source, adapted⟩ := sortedElements_adapts layout elements
        exact ⟨_, .list sort elementSort source children shape adapted⟩
  termination_by sizeOf term

  theorem sortedArguments_adapts (layout : Layout) {sorts : List String} {terms : List CanonicalTerm}
      (valid : SortedArguments schema profile sorts terms) :
      ∃ source, AdaptArguments schema profile layout sorts source terms := by
    cases valid with
    | nil => exact ⟨[], .nil⟩
    | cons head tail =>
        obtain ⟨source, first⟩ := sorted_adapts layout head
        obtain ⟨sources, rest⟩ := sortedArguments_adapts layout tail
        exact ⟨source :: sources, .cons first rest⟩
  termination_by sizeOf terms

  theorem sortedElements_adapts (layout : Layout) {sort : String} {terms : List CanonicalTerm}
      (valid : SortedElements schema profile sort terms) :
      ∃ source, AdaptElements schema profile layout sort source terms := by
    cases valid with
    | nil sort => exact ⟨[], .nil sort⟩
    | cons head tail =>
        obtain ⟨source, first⟩ := sorted_adapts layout head
        obtain ⟨sources, rest⟩ := sortedElements_adapts layout tail
        exact ⟨source :: sources, .cons first rest⟩
  termination_by sizeOf terms
end

/-- Source values satisfying the independent two-carrier formation relation.
This is structural admission, not a substitute for source grammar derivability. -/
abbrev ProjectionTerm (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :=
  { source : CanonicalTerm // ∃ term, Adapts schema profile layout sort source term }

def toSorted {sort : String} (source : ProjectionTerm schema profile layout sort) :
    SortedTerm schema profile sort :=
  let term := (toCodec? schema profile layout sort source.val).get
    (by obtain ⟨term, adapted⟩ := source.property; simp [adapted.toCodec])
  ⟨term, (toCodec_adapts schema profile layout sort source.val term (Option.some_get _).symm).codec_sorted⟩

def fromSorted (layout : Layout) {sort : String} (term : SortedTerm schema profile sort) :
    ProjectionTerm schema profile layout sort :=
  let source := (fromCodec? schema profile layout sort term.val).get
    (by obtain ⟨source, adapted⟩ := sorted_adapts layout term.property; simp [adapted.fromCodec])
  ⟨source, term.val, fromCodec_adapts schema profile layout sort term.val source (Option.some_get _).symm⟩

theorem toCodec_toSorted {sort : String} (source : ProjectionTerm schema profile layout sort) :
    toCodec? schema profile layout sort source.val = some (toSorted source).val :=
  (Option.some_get _).symm

theorem fromCodec_fromSorted {sort : String} (term : SortedTerm schema profile sort) :
    fromCodec? schema profile layout sort term.val = some (fromSorted layout term).val :=
  (Option.some_get _).symm

@[simp] theorem toSorted_fromSorted {sort : String} (term : SortedTerm schema profile sort) :
    toSorted (fromSorted layout term) = term := by
  apply Subtype.ext
  exact Option.some.inj ((toCodec_toSorted (fromSorted layout term)).symm.trans
    (toCodec_of_fromCodec sort term.val _ (fromCodec_fromSorted term)))

@[simp] theorem fromSorted_toSorted {sort : String} (source : ProjectionTerm schema profile layout sort) :
    fromSorted layout (toSorted source) = source := by
  apply Subtype.ext
  exact Option.some.inj ((fromCodec_fromSorted (toSorted source)).symm.trans
    (fromCodec_of_toCodec sort source.val _ (toCodec_toSorted source)))

/-- Total quotation after the explicit checked representation conversion. -/
def quoteProjection {sort : String} (source : ProjectionTerm schema profile layout sort) : Atom :=
  quote (toSorted source)

def admitProjection? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String)
    (wire : Atom) : Option (ProjectionTerm schema profile layout sort) :=
  (admit? schema profile sort wire).map (fromSorted layout)

@[simp] theorem admitProjection_quoteProjection {sort : String}
    (source : ProjectionTerm schema profile layout sort) :
    admitProjection? schema profile layout sort (quoteProjection source) = some source := by
  simp [admitProjection?, quoteProjection]

theorem quoteProjection_of_admitProjection (sort : String) (wire : Atom)
    (source : ProjectionTerm schema profile layout sort)
    (admitted : admitProjection? schema profile layout sort wire = some source) :
    quoteProjection source = wire := by
  cases parsed : admit? schema profile sort wire with
  | none => simp [admitProjection?, parsed] at admitted
  | some term =>
      simp [admitProjection?, parsed] at admitted
      rw [← admitted]
      simp only [quoteProjection, toSorted_fromSorted]
      exact quote_of_admit schema profile sort wire term parsed

theorem admitProjection_some_iff_quoteProjection (sort : String) (wire : Atom)
    (source : ProjectionTerm schema profile layout sort) :
    admitProjection? schema profile layout sort wire = some source ↔ quoteProjection source = wire := by
  constructor
  · exact quoteProjection_of_admitProjection sort wire source
  · intro same
    rw [← same]
    exact admitProjection_quoteProjection source

theorem quoteProjection_injective {sort : String} :
    Function.Injective (@quoteProjection schema profile layout sort) := by
  intro first second same
  have decoded := congrArg (admitProjection? schema profile layout sort) same
  simpa only [admitProjection_quoteProjection, Option.some.injEq] using decoded

/-! ## Partial wire conversion and separated-list grammar composition -/

def encodeProjection? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String)
    (source : CanonicalTerm) : Option Atom :=
  toCodec? schema profile layout sort source >>= encode? schema profile sort

def decodeProjection? (schema : Schema) (profile : Notation) (layout : Layout) (sort : String)
    (wire : Atom) : Option CanonicalTerm :=
  decode? schema profile sort wire >>= fromCodec? schema profile layout sort

theorem decodeProjection_encoded (sort : String) (source : CanonicalTerm) (wire : Atom)
    (encoded : encodeProjection? schema profile layout sort source = some wire) :
    decodeProjection? schema profile layout sort wire = some source := by
  cases converted : toCodec? schema profile layout sort source with
  | none => simp [encodeProjection?, converted] at encoded
  | some term =>
      simp [encodeProjection?, converted] at encoded
      simp [decodeProjection?, decode_encoded schema profile sort term wire encoded,
        fromCodec_of_toCodec sort source term converted]

theorem encodeProjection_decoded (sort : String) (wire : Atom) (source : CanonicalTerm)
    (decoded : decodeProjection? schema profile layout sort wire = some source) :
    encodeProjection? schema profile layout sort source = some wire := by
  cases parsed : decode? schema profile sort wire with
  | none => simp [decodeProjection?, parsed] at decoded
  | some term =>
      simp [decodeProjection?, parsed] at decoded
      simp [encodeProjection?, toCodec_of_fromCodec sort term source decoded,
        encode_decoded schema profile sort wire term parsed]

theorem decodeProjection_some_iff (sort : String) (wire : Atom) (source : CanonicalTerm) :
    decodeProjection? schema profile layout sort wire = some source ↔
      encodeProjection? schema profile layout sort source = some wire :=
  ⟨encodeProjection_decoded sort wire source, decodeProjection_encoded sort source wire⟩

theorem encodeProjection_quoteProjection {sort : String}
    (source : ProjectionTerm schema profile layout sort) :
    encodeProjection? schema profile layout sort source.val = some (quoteProjection source) := by
  simp [encodeProjection?, toCodec_toSorted source, quoteProjection, encode_quote]

theorem decodeProjection_quoteProjection {sort : String}
    (source : ProjectionTerm schema profile layout sort) :
    decodeProjection? schema profile layout sort (quoteProjection source) = some source.val :=
  decodeProjection_encoded sort source.val _ (encodeProjection_quoteProjection source)

theorem adapted_list {sort elementSort key : String} {source terms : List CanonicalTerm}
    (shape : schema.shape? sort = some (.list elementSort)) (keyMatches : layout.listKey sort = key)
    (elements : AdaptElements schema profile layout elementSort source terms) :
    Adapts schema profile layout sort (.node key [.seq source]) (.seq terms) := by
  rw [← keyMatches]
  exact .list sort elementSort source terms shape elements

theorem encodeProjection_list {sort elementSort key : String} {source terms : List CanonicalTerm}
    (shape : schema.shape? sort = some (.list elementSort)) (keyMatches : layout.listKey sort = key)
    (elements : AdaptElements schema profile layout elementSort source terms) :
    encodeProjection? schema profile layout sort (.node key [.seq source]) =
      encode? schema profile sort (.seq terms) := by
  simp [encodeProjection?, (adapted_list shape keyMatches elements).toCodec]

theorem adapted_list_has_exact_wire {sort elementSort key : String} {source terms : List CanonicalTerm}
    (shape : schema.shape? sort = some (.list elementSort)) (keyMatches : layout.listKey sort = key)
    (elements : AdaptElements schema profile layout elementSort source terms) :
    ∃ wire, encodeProjection? schema profile layout sort (.node key [.seq source]) = some wire ∧
      decodeProjection? schema profile layout sort wire = some (.node key [.seq source]) := by
  obtain ⟨wire, encoded⟩ := encode_sorted (adapted_list shape keyMatches elements).codec_sorted
  have encodedSource : encodeProjection? schema profile layout sort (.node key [.seq source]) = some wire := by
    rw [encodeProjection_list shape keyMatches elements]
    exact encoded
  exact ⟨wire, encodedSource, decodeProjection_encoded sort _ wire encodedSource⟩

/-- The same declared wire result survives the real grammar refactoring.
Both derivations retain their own CST, and the source projection is explicit. -/
theorem encoded_derivation_refactoring
    {G G' : Grammar} {C C' : Classification} {L L' : String → Option (ListForm × String)}
    (wellFormed : CanonicalGrammar.WellFormed G C L)
    (wellFormed' : CanonicalGrammar.WellFormed G' C' L')
    {root root' key : String} (item : CanonicalGrammar.Sym) (sep : List String)
    (form : L root = some (.separated item sep true, key))
    (form' : L' root' = some (.separated item sep false, key))
    (sameElements : ∀ e tokens, CanonicalGrammar.Prints G C L item e tokens ↔
      CanonicalGrammar.Prints G' C' L' item e tokens)
    (sort : String) (tokens : List Tok) (wire : Atom) :
    (∃ tree source, Derives G root tokens tree ∧ canon G C tree = some source ∧
      encodeProjection? schema profile layout sort source = some wire) ↔
    (∃ tree source, Derives G' root' tokens tree ∧ canon G' C' tree = some source ∧
      encodeProjection? schema profile layout sort source = some wire) := by
  have listValue : ∀ {H : Grammar} {D : Classification} {K : String → Option (ListForm × String)}
      {name : String} {direction : Bool}, CanonicalGrammar.WellFormed H D K →
      K name = some (.separated item sep direction, key) →
      ∀ {tree}, Derives H name tokens tree →
        ∃ es, canon H D tree = some (.node key [.seq es]) := by
    intro H D K name direction wf listForm tree derived
    obtain ⟨value, k, finished, formation⟩ := CanonicalGrammar.finishes wf derived
    simp only [CanonicalGrammar.Finished, listForm] at formation
    obtain ⟨rfl, es, rfl⟩ := formation
    exact ⟨es, by simp only [canon, finished, Option.map_some, CanonicalGrammar.named]⟩
  constructor
  · rintro ⟨tree, source, derived, projected, encoded⟩
    obtain ⟨es, canonical⟩ := listValue wellFormed form derived
    have sourceValue : source = .node key [.seq es] := Option.some.inj (projected.symm.trans canonical)
    obtain ⟨tree', derived', canonical'⟩ :=
      (NonemptySeparatorRefactoring.projected_derivation_refactoring wellFormed wellFormed'
        item sep form form' sameElements es tokens).mp ⟨tree, derived, canonical⟩
    exact ⟨tree', source, derived', by rw [sourceValue]; exact canonical', encoded⟩
  · rintro ⟨tree, source, derived, projected, encoded⟩
    obtain ⟨es, canonical⟩ := listValue wellFormed' form' derived
    have sourceValue : source = .node key [.seq es] := Option.some.inj (projected.symm.trans canonical)
    obtain ⟨tree', derived', canonical'⟩ :=
      (NonemptySeparatorRefactoring.projected_derivation_refactoring wellFormed wellFormed'
        item sep form form' sameElements es tokens).mpr ⟨tree, derived, canonical⟩
    exact ⟨tree', source, derived', by rw [sourceValue]; exact canonical', encoded⟩

/-! ## Restriction to actual source grammar projection fibres -/

/-- A value produced by a real derivation and the declared canonical builder. -/
def DerivableProjection (grammar : Grammar) (classification : Classification) (root : String)
    (source : CanonicalTerm) : Prop :=
  ∃ tokens tree, Derives grammar root tokens tree ∧ canon grammar classification tree = some source

abbrev GrammarProjectionTerm (grammar : Grammar) (classification : Classification) (root : String)
    (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :=
  { source : ProjectionTerm schema profile layout sort //
    DerivableProjection grammar classification root source.val }

/-- The sorted codec fibre whose reconstructed projections are grammar-produced.
This restriction is necessary: an unrestricted schema list admits the empty
sequence even when the source list rule has only nonempty productions. -/
abbrev GrammarSortedTerm (grammar : Grammar) (classification : Classification) (root : String)
    (schema : Schema) (profile : Notation) (layout : Layout) (sort : String) :=
  { term : SortedTerm schema profile sort //
    ∃ source, DerivableProjection grammar classification root source ∧
      fromCodec? schema profile layout sort term.val = some source }

def toGrammarSorted {grammar : Grammar} {classification : Classification} {root sort : String}
    (source : GrammarProjectionTerm grammar classification root schema profile layout sort) :
    GrammarSortedTerm grammar classification root schema profile layout sort :=
  ⟨toSorted source.val, source.val.val, source.property,
    fromCodec_of_toCodec sort source.val.val _ (toCodec_toSorted source.val)⟩

def fromGrammarSorted (layout : Layout) {grammar : Grammar} {classification : Classification}
    {root sort : String}
    (term : GrammarSortedTerm grammar classification root schema profile layout sort) :
    GrammarProjectionTerm grammar classification root schema profile layout sort :=
  ⟨fromSorted layout term.val, by
    obtain ⟨source, derived, converted⟩ := term.property
    have same : (fromSorted layout term.val).val = source :=
      Option.some.inj ((fromCodec_fromSorted term.val).symm.trans converted)
    rw [same]
    exact derived⟩

@[simp] theorem toGrammarSorted_fromGrammarSorted
    {grammar : Grammar} {classification : Classification} {root sort : String}
    (term : GrammarSortedTerm grammar classification root schema profile layout sort) :
    toGrammarSorted (fromGrammarSorted layout term) = term := by
  apply Subtype.ext
  exact toSorted_fromSorted term.val

@[simp] theorem fromGrammarSorted_toGrammarSorted
    {grammar : Grammar} {classification : Classification} {root sort : String}
    (source : GrammarProjectionTerm grammar classification root schema profile layout sort) :
    fromGrammarSorted layout (toGrammarSorted source) = source := by
  apply Subtype.ext
  exact fromSorted_toSorted source.val

end Mettapedia.GSLT.Parsing.CanonicalProjectionSExprAdapter

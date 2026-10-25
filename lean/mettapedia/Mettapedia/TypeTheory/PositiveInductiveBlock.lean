import Mettapedia.TypeTheory.IndexedContainer
import Mettapedia.TypeTheory.IndexedPolynomialDescription
import Mettapedia.TypeTheory.IndexedPolynomialInduction
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-!
# Staged admission of mutual and registered-nested positive blocks

This module separates four components of inductive admission:

1. an executable block recognizer;
2. positivity and uniform-parameter evidence retained by its result;
3. recursors and dependent eliminators generated from the recognized block;
4. the initial-algebra law of the resulting indexed polynomial family.

Direct recursive fields and recursive families stored under a registered
positive container are accepted.  Every recursive occurrence must repeat the
block's canonical parameter vector.  Function fields, unknown containers and
changed parameter vectors are refused by the recognizer.

The registered-nested fragment here gives all children of one container field
the same family index.  It covers forms such as `List (Tree A)` and mutual
families selected by the index.  It is not yet Lean's complete nested-inductive
admission algorithm, a textual `.module` decoder, or guest judgmental
computation authority.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PositiveInductiveBlock

open IndexedContainer
open IndexedPolynomial
open IndexedPolynomial.Description

universe u v

/-- Positive containers usable by the bounded source grammar.  Shape and
position data live in `Type`; richer universe-polymorphic registries are a
separate extension. -/
abbrev Container := IndexedContainer.{0, 0, 0} Unit

/-- Source names are resolved through an explicit positive-container
registry.  Merely naming an unknown constructor does not grant positivity. -/
structure Registry where
  lookup : String → Option Container

/-- Executable enumeration is a separate capability: every registered
container has finitely many positions at each shape. -/
structure Registry.Finitary (registry : Registry) where
  containerFinitary : ∀ name container,
    registry.lookup name = some container → IndexedContainer.Finitary container

/-- The parameter vector every recursive occurrence in a block must repeat. -/
def canonicalParameters (parameterCount : Nat) : List Nat :=
  List.range parameterCount

/-- Function fields remain in raw syntax so negative occurrences and other
unsupported higher-order forms are refused explicitly. -/
inductive FieldType (I : Interface.{u}) (context : List I.SortCode) where
  | ground (sort : I.SortCode)
  | family (index : I.IndexExpr context)
  | arrow (domain codomain : FieldType I context)

/-- Raw field syntax keeps unsupported function fields visible.  Recursive
fields carry their written parameter vector so uniformity is checked rather
than assumed by erasure. -/
inductive RawCode (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) : List I.SortCode → Type (u + 1) where
  | result {context} (index : I.IndexExpr context) :
      RawCode registry I parameterCount context
  | data {context} (sort : I.SortCode)
      (body : RawCode registry I parameterCount (sort :: context)) :
      RawCode registry I parameterCount context
  | recursive {context} (parameters : List Nat)
      (index : I.IndexExpr context)
      (rest : RawCode registry I parameterCount context) :
      RawCode registry I parameterCount context
  | nested {context} (containerName : String) (parameters : List Nat)
      (index : I.IndexExpr context)
      (rest : RawCode registry I parameterCount context) :
      RawCode registry I parameterCount context
  | functionField {context}
      (domain codomain : FieldType I context)
      (rest : RawCode registry I parameterCount context) :
      RawCode registry I parameterCount context

/-- Recognized positive syntax.  There is no negative constructor.  A nested
field retains the successful positive-container lookup. -/
inductive Code (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) : List I.SortCode → Type (u + 1) where
  | result {context} (index : I.IndexExpr context) :
      Code registry I parameterCount context
  | data {context} (sort : I.SortCode)
      (body : Code registry I parameterCount (sort :: context)) :
      Code registry I parameterCount context
  | recursive {context} (index : I.IndexExpr context)
      (rest : Code registry I parameterCount context) :
      Code registry I parameterCount context
  | nested {context} (containerName : String) (container : Container)
      (index : I.IndexExpr context)
      (rest : Code registry I parameterCount context) :
      Code registry I parameterCount context

namespace RawCode

/-- Recognize the strictly scoped direct/registered-nested fragment. -/
def decode {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} :
    RawCode registry I parameterCount context →
      Option (Code registry I parameterCount context)
  | .result index => some (.result index)
  | .data sort body => (decode body).map (.data sort)
  | .recursive parameters index rest =>
      if parameters = canonicalParameters parameterCount then
        (decode rest).map (.recursive index)
      else none
  | .nested name parameters index rest =>
      if parameters = canonicalParameters parameterCount then
        match registry.lookup name with
        | none => none
        | some container =>
            (decode rest).map (.nested name container index)
      else none
  | .functionField _ _ _ => none

/-- Quote recognized syntax with the canonical parameter vector and retained
container name. -/
def quote {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} :
    Code registry I parameterCount context →
      RawCode registry I parameterCount context
  | .result index => .result index
  | .data sort body => .data sort (quote body)
  | .recursive index rest =>
      .recursive (canonicalParameters parameterCount) index (quote rest)
  | .nested name _ index rest =>
      .nested name (canonicalParameters parameterCount) index
        (quote rest)

/-- Registry coherence of every nested constructor retained by recognized
syntax. -/
def WellRegistered
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat} :
    {context : List I.SortCode} → Code registry I parameterCount context → Prop
  | _, .result _ => True
  | _, .data _ body => WellRegistered body
  | _, .recursive _ rest => WellRegistered rest
  | _, .nested name container _ rest =>
      registry.lookup name = some container ∧ WellRegistered rest

theorem wellRegistered_of_decode
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (raw : RawCode registry I parameterCount context)
    {code : Code registry I parameterCount context}
    (accepted : decode raw = some code) : WellRegistered code := by
  induction raw with
  | result index =>
      have same : Code.result index = code := by
        simpa [decode] using accepted
      rw [← same]
      trivial
  | data sort body ih =>
      cases decoded : decode body with
      | none => simp [decode, decoded] at accepted
      | some result =>
          have same : Code.data sort result = code := by
            simpa [decode, decoded] using accepted
          rw [← same]
          exact ih decoded
  | recursive parameters index rest ih =>
      by_cases uniform : parameters = canonicalParameters parameterCount
      · cases decoded : decode rest with
        | none => simp [decode, uniform, decoded] at accepted
        | some result =>
            have same : Code.recursive index result = code := by
              simpa [decode, uniform, decoded] using accepted
            rw [← same]
            exact ih (code := result) decoded
      · simp [decode, uniform] at accepted
  | nested name parameters index rest ih =>
      by_cases uniform : parameters = canonicalParameters parameterCount
      · cases found : registry.lookup name with
        | none => simp [decode, uniform, found] at accepted
        | some container =>
            cases decoded : decode rest with
            | none => simp [decode, uniform, found, decoded] at accepted
            | some result =>
                have same : Code.nested name container index result = code := by
                  simpa [decode, uniform, found, decoded] using accepted
                rw [← same]
                exact ⟨found, ih (code := result) decoded⟩
      · simp [decode, uniform] at accepted
  | functionField => simp [decode] at accepted

@[simp] theorem decode_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (code : Code registry I parameterCount context)
    (registered : WellRegistered code) :
    decode (quote code) = some code := by
  induction code with
  | result => rfl
  | data sort body ih => simpa [quote, decode] using ih registered
  | recursive index rest ih =>
      simpa [quote, decode] using ih registered
  | nested name container index rest ih =>
      simpa [quote, decode, registered.1] using ih registered.2

/-- A raw term is positive and parameter-uniform exactly by the evidence
needed at its recursive fields. Registered nested fields retain the existence
of their lookup witness. -/
def Positive
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat} :
    {context : List I.SortCode} →
      RawCode registry I parameterCount context → Prop
  | _, .result _ => True
  | _, .data _ body => Positive body
  | _, .recursive parameters _ rest =>
      parameters = canonicalParameters parameterCount ∧ Positive rest
  | _, .nested name parameters _ rest =>
      parameters = canonicalParameters parameterCount ∧
        (∃ container, registry.lookup name = some container) ∧ Positive rest
  | _, .functionField _ _ _ => False

/-- Successful recognition produces positivity and uniform-parameter
evidence for the complete raw constructor telescope. -/
theorem positive_of_decode
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (raw : RawCode registry I parameterCount context)
    {code : Code registry I parameterCount context}
    (accepted : decode raw = some code) : Positive raw := by
  induction raw with
  | result index => trivial
  | data sort body ih =>
      cases decoded : decode body with
      | none => simp [decode, decoded] at accepted
      | some result =>
          exact ih decoded
  | recursive parameters index rest ih =>
      by_cases uniform : parameters = canonicalParameters parameterCount
      · cases decoded : decode rest with
        | none => simp [decode, uniform, decoded] at accepted
        | some result => exact ⟨uniform, ih decoded⟩
      · simp [decode, uniform] at accepted
  | nested name parameters index rest ih =>
      by_cases uniform : parameters = canonicalParameters parameterCount
      · cases found : registry.lookup name with
        | none => simp [decode, uniform, found] at accepted
        | some container =>
            cases decoded : decode rest with
            | none => simp [decode, uniform, found, decoded] at accepted
            | some result => exact ⟨uniform, ⟨container, found⟩, ih decoded⟩
      · simp [decode, uniform] at accepted
  | functionField => simp [decode] at accepted

theorem functionField_refused
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (domain codomain : FieldType I context)
    (rest : RawCode registry I parameterCount context) :
    decode (.functionField domain codomain rest) = none := rfl

theorem changedParameters_refused
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (parameters : List Nat)
    (changed : parameters ≠ canonicalParameters parameterCount)
    (index : I.IndexExpr context)
    (rest : RawCode registry I parameterCount context) :
    decode (.recursive parameters index rest) = none := by
  simp [decode, changed]

theorem unknownContainer_refused
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (name : String) (unknown : registry.lookup name = none)
    (index : I.IndexExpr context)
    (rest : RawCode registry I parameterCount context) :
    decode (.nested name (canonicalParameters parameterCount) index rest) = none := by
  simp only [decode, ↓reduceIte]
  rw [unknown]

end RawCode

/-! ## Polynomial semantics of recognized syntax -/

namespace Code

variable {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}

/-- Constructor data, nested-container shapes and the output-index equation. -/
def Shape : {context : List I.SortCode} →
    Code registry I parameterCount context →
      Env I.Value context → I.Index → Type u
  | _, .result expression, environment, index =>
      ULift.{u} (PLift (I.evalIndex expression environment = index))
  | _, .data sort body, environment, index =>
      Σ value : I.Value sort, Shape body (value, environment) index
  | _, .recursive _ rest, environment, index => Shape rest environment index
  | _, .nested _ container _ rest, environment, index =>
      Σ _shape : container.Shape (), Shape rest environment index

/-- Recursive positions include direct children and every position exposed by
a registered positive container. -/
def Position : {context : List I.SortCode} →
    (code : Code registry I parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
      Shape code environment index → Type u
  | _, .result _, _, _, _ => PEmpty
  | _, .data _ body, _, _, shape => Position body shape.2
  | _, .recursive _ rest, _, _, shape => Option (Position rest shape)
  | _, .nested _ container _ rest, _, _, shape =>
      Sum (container.Position shape.1) (Position rest shape.2)

/-- Every direct or nested recursive position records its child index. -/
def next : {context : List I.SortCode} →
    (code : Code registry I parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → Position code shape → I.Index
  | _, .result _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, _, _, shape, position => next body shape.2 position
  | _, .recursive expression rest, environment, _, shape, position =>
      match position with
      | none => I.evalIndex expression environment
      | some prior => next rest shape prior
  | _, .nested _ _ expression rest, environment, _, shape, position =>
      match position with
      | .inl _ => I.evalIndex expression environment
      | .inr prior => next rest shape.2 prior

/-- Recognized syntax compiles directly to an indexed polynomial. -/
def polynomial {context : List I.SortCode}
    (code : Code registry I parameterCount context) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := Shape code
  Position := Position code
  next := next code

/-- A finitary registry induces finite recursive-position fibres for every
registry-coherent recognized constructor. Strict positivity alone does not. -/
@[instance_reducible] noncomputable def positionFintype
    (finitary : registry.Finitary) :
    ∀ {context : List I.SortCode}
      (code : Code registry I parameterCount context),
      RawCode.WellRegistered code →
      ∀ {environment : Env I.Value context} {index : I.Index}
        (shape : Shape code environment index),
        Fintype (Position code shape)
  | _, .result _, _, _, _, _ => by
      change Fintype PEmpty
      infer_instance
  | _, .data _ body, registered, _, _, shape =>
      positionFintype finitary body registered shape.2
  | _, .recursive _ rest, registered, _, _, shape => by
      letI restFintype : Fintype (Position rest shape) :=
        positionFintype finitary rest registered shape
      change Fintype (Option (Position rest shape))
      infer_instance
  | _, .nested name container _ rest, registered, _, _, shape => by
      letI containerFintype : Fintype (container.Position shape.1) :=
        (finitary.containerFinitary name container registered.1).positionFintype shape.1
      letI restFintype : Fintype (Position rest shape.2) :=
        positionFintype finitary rest registered.2 shape.2
      change Fintype (Sum (container.Position shape.1) (Position rest shape.2))
      infer_instance

end Code

/-! ## Executable block recognition -/

structure RawConstructor (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) (context : List I.SortCode) where
  name : String
  body : RawCode registry I parameterCount context

structure Constructor (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) (context : List I.SortCode) where
  name : String
  body : Code registry I parameterCount context

def RawConstructor.decode
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (raw : RawConstructor registry I parameterCount context) :
    Option (Constructor registry I parameterCount context) :=
  (RawCode.decode raw.body).map fun body => ⟨raw.name, body⟩

private theorem mapM_member_some
    {α : Type u} {β : Type v} (f : α → Option β) :
    ∀ {source : List α} {results : List β},
      source.mapM f = some results →
      ∀ item ∈ source, ∃ result, f item = some result := by
  intro source
  induction source with
  | nil =>
      intro results accepted item member
      simp at member
  | cons head tail ih =>
      intro results accepted item member
      cases headResult : f head with
      | none => simp [List.mapM_cons, headResult] at accepted
      | some decodedHead =>
          cases tailResult : tail.mapM f with
          | none => simp [List.mapM_cons, headResult, tailResult] at accepted
          | some decodedTail =>
              have resultsEqual : decodedHead :: decodedTail = results := by
                simpa [List.mapM_cons, headResult, tailResult] using accepted
              subst results
              simp only [List.mem_cons] at member
              rcases member with same | member
              · subst item
                exact ⟨decodedHead, headResult⟩
              · exact ih tailResult item member

structure Admitted (registry : Registry) (I : Interface.{u})
    (parameterCount : Nat) (context : List I.SortCode) where
  constructors : List (Constructor registry I parameterCount context)
  uniqueNames : (constructors.map (·.name)).Nodup

/-- Every nested container retained by an admitted block still resolves to
the same registered semantics. -/
def Admitted.WellRegistered
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (admitted : Admitted registry I parameterCount context) : Prop :=
  ∀ constructor ∈ admitted.constructors,
    RawCode.WellRegistered constructor.body

/-- Canonical raw spelling of one recognized constructor. -/
def quoteConstructor
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (constructor : Constructor registry I parameterCount context) :
    RawConstructor registry I parameterCount context :=
  ⟨constructor.name, RawCode.quote constructor.body⟩

@[simp] theorem decode_quoteConstructor
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (constructor : Constructor registry I parameterCount context)
    (registered : RawCode.WellRegistered constructor.body) :
    (quoteConstructor constructor).decode = some constructor := by
  cases constructor with
  | mk name body => simp [quoteConstructor, RawConstructor.decode,
      RawCode.decode_quote body registered]

private theorem decodeList_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (constructors : List (Constructor registry I parameterCount context))
    (registered : ∀ constructor ∈ constructors,
      RawCode.WellRegistered constructor.body) :
    (constructors.map quoteConstructor).mapM RawConstructor.decode =
      some constructors := by
  induction constructors with
  | nil => rfl
  | cons constructor rest ih =>
      simp only [List.mem_cons] at registered
      simp [decode_quoteConstructor constructor (registered constructor (Or.inl rfl)),
        ih (fun item member => registered item (Or.inr member))]

/-- Phase 1 and phase 2 together: recognize every constructor, retaining
source order, and reject duplicate public names. -/
def recognize?
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : List (RawConstructor registry I parameterCount context)) :
    Option (Admitted registry I parameterCount context) := do
  let constructors ← source.mapM RawConstructor.decode
  if unique : (constructors.map (·.name)).Nodup then
    some ⟨constructors, unique⟩
  else none

/-- Quoting any registry-coherent admitted block and recognizing it recovers
the exact ordered block. -/
@[simp] theorem recognize_quote
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (admitted : Admitted registry I parameterCount context)
    (registered : admitted.WellRegistered) :
    recognize? (admitted.constructors.map quoteConstructor) = some admitted := by
  cases admitted with
  | mk constructors uniqueNames =>
      unfold recognize?
      rw [decodeList_quote constructors registered]
      simp [uniqueNames]

/-- A successful block retains positivity and parameter-uniformity for every
source constructor. -/
theorem recognize_positive
    {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : List (RawConstructor registry I parameterCount context))
    (admitted : Admitted registry I parameterCount context)
    (accepted : recognize? source = some admitted) :
    ∀ raw ∈ source, RawCode.Positive raw.body := by
  intro raw member
  unfold recognize? at accepted
  cases decoded : source.mapM RawConstructor.decode with
  | none => simp [decoded] at accepted
  | some constructors =>
      by_cases unique : (constructors.map (·.name)).Nodup
      · have same : (⟨constructors, unique⟩ : Admitted registry I parameterCount context) = admitted := by
          simpa [decoded, unique] using accepted
        subst admitted
        have rawDecoded : ∃ constructor, raw.decode = some constructor :=
          mapM_member_some RawConstructor.decode decoded raw member
        obtain ⟨constructor, decodedRaw⟩ := rawDecoded
        unfold RawConstructor.decode at decodedRaw
        cases bodyDecoded : RawCode.decode raw.body with
        | none => simp [bodyDecoded] at decodedRaw
        | some code => exact RawCode.positive_of_decode raw.body bodyDecoded
      · simp [decoded, unique] at accepted

/-! ## Inventory polynomial and generated eliminators -/

namespace Admitted

variable {registry : Registry} {I : Interface.{u}} {parameterCount : Nat}
  {context : List I.SortCode}

/-- All recognized constructors form one polynomial.  The occurrence ordinal
keeps equal-shaped declarations distinct. -/
def polynomial (admitted : Admitted registry I parameterCount context) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := fun environment index =>
    Σ occurrence : Fin admitted.constructors.length,
      Code.Shape (admitted.constructors.get occurrence).body environment index
  Position := fun shape =>
    Code.Position (admitted.constructors.get shape.1).body shape.2
  next := fun shape position =>
    Code.next (admitted.constructors.get shape.1).body shape.2 position

abbrev Family (admitted : Admitted registry I parameterCount context) :=
  Fix admitted.polynomial

/-- Phase 3: construct a value from one recognized polynomial layer. -/
def construct (admitted : Admitted registry I parameterCount context)
    {environment : Env I.Value context} {index : I.Index}
    (layer : admitted.polynomial.Extension admitted.Family environment index) :
    admitted.Family environment index :=
  Fix.rollExtension admitted.polynomial layer

/-- Phase 3: the nondependent recursor is generated from the recognized
polynomial, not accepted from the source block. -/
noncomputable def recursor
    (admitted : Admitted registry I parameterCount context)
    {carrier : Env I.Value context → I.Index → Type v}
    (algebra : Algebra admitted.polynomial carrier) :
    ∀ environment index, admitted.Family environment index → carrier environment index :=
  Fix.fold admitted.polynomial algebra.act

@[simp] theorem recursor_construct
    (admitted : Admitted registry I parameterCount context)
    {carrier : Env I.Value context → I.Index → Type v}
    (algebra : Algebra admitted.polynomial carrier)
    {environment : Env I.Value context} {index : I.Index}
    (layer : admitted.polynomial.Extension admitted.Family environment index) :
    admitted.recursor algebra environment index (admitted.construct layer) =
      algebra.act environment index
        (Extension.map admitted.polynomial (admitted.recursor algebra) layer) := by
  cases layer
  rfl

/-- Phase 4: every constructor-preserving map out of the generated family is
the generated recursor. -/
theorem recursor_unique
    (admitted : Admitted registry I parameterCount context)
    {carrier : Env I.Value context → I.Index → Type v}
    (algebra : Algebra admitted.polynomial carrier)
    (candidate : Algebra.Hom (Algebra.initial admitted.polynomial) algebra)
    (environment : Env I.Value context) (index : I.Index)
    (value : admitted.Family environment index) :
    candidate.toFun environment index value =
      admitted.recursor algebra environment index value :=
  Algebra.hom_eq_fold algebra candidate environment index value

/-- Phase 3, dependent form: generate the eliminator from displayed
constructor methods. -/
noncomputable def eliminator
    (admitted : Admitted registry I parameterCount context)
    {motive : ∀ environment index,
      admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive) :
    methods.Section :=
  methods.initialSection

@[simp] theorem eliminator_construct
    (admitted : Admitted registry I parameterCount context)
    {motive : ∀ environment index,
      admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive)
    {environment : Env I.Value context} {index : I.Index}
    (shape : admitted.polynomial.Shape environment index)
    (children : ∀ position, admitted.Family environment
      (admitted.polynomial.next shape position)) :
    (admitted.eliminator methods).toFun environment index (.roll shape children) =
      methods.act environment index shape children
        (fun position => (admitted.eliminator methods).toFun environment _
          (children position)) := rfl

/-- Phase 4, dependent form: the generated constructor equations determine
the complete dependent eliminator. -/
theorem eliminator_unique
    (admitted : Admitted registry I parameterCount context)
    {motive : ∀ environment index,
      admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive)
    (candidate : methods.Section)
    (environment : Env I.Value context) (index : I.Index)
    (value : admitted.Family environment index) :
    candidate.toFun environment index value =
      (admitted.eliminator methods).toFun environment index value :=
  methods.initialSection_unique candidate environment index value

end Admitted

section AxiomAudit

#print axioms RawCode.decode_quote
#print axioms RawCode.positive_of_decode
#print axioms Code.positionFintype
#print axioms recognize_positive
#print axioms Admitted.recursor_construct
#print axioms Admitted.recursor_unique
#print axioms Admitted.eliminator_construct
#print axioms Admitted.eliminator_unique
#print axioms recognize_quote

end AxiomAudit

end Mettapedia.TypeTheory.PositiveInductiveBlock

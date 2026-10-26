import Mettapedia.TypeTheory.IndexedPolynomial
import Mathlib.Logic.Equiv.Fin.Basic
import Mettapedia.TypeTheory.IndexedPolynomialEquivalence

/-!
# Finite descriptions of indexed constructor telescopes

A description distinguishes interpreted data arguments from recursive children.
Data arguments may determine later indices through the supplied expression
interface. Their carrier sorts are fixed by the declaration. Recursive arguments do not extend that expression
environment: the supported fragment does not permit later indices to inspect
the recursive value itself.

The interpretation into indexed polynomials is compared with an independent
ordered argument interpretation. Constructor inventory positions remain part
of the polynomial shape, preserving distinct authored occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description

universe u v w s

/-- Values of a finite, most-recent-first data context. -/
def Env {SortCode : Type s} (Value : SortCode → Type u) : List SortCode → Type u
  | [] => PUnit
  | sort :: rest => Value sort × Env Value rest

/-- Interpretation of the nonrecursive expression fragment. -/
structure Interface where
  SortCode : Type
  Value : SortCode → Type u
  Index : Type u
  IndexExpr : List SortCode → Type
  evalIndex : {context : List SortCode} → IndexExpr context → Env Value context → Index

/-- A finite constructor telescope. Every recursive field is covariant. -/
inductive Code (I : Interface.{u}) : List I.SortCode → Type where
  | result {context} (index : I.IndexExpr context) : Code I context
  | data {context} (sort : I.SortCode) (body : Code I (sort :: context)) : Code I context
  | recursive {context} (index : I.IndexExpr context) (rest : Code I context) : Code I context

variable {I : Interface.{u}}

/-- The constructor's nonrecursive data and its output-index constraint. -/
def Shape : {context : List I.SortCode} → Code I context →
    Env I.Value context → I.Index → Type u
  | _, .result expression, environment, index =>
      ULift.{u} (PLift (I.evalIndex expression environment = index))
  | _, .data sort body, environment, index =>
      Σ value : I.Value sort, Shape body (value, environment) index
  | _, .recursive _ rest, environment, index => Shape rest environment index

/-- One position for each recursive field, in source order. -/
def Position : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Shape code environment index → Type u
  | _, .result _, _, _, _ => PEmpty
  | _, .data _ body, _, _, shape => Position body shape.2
  | _, .recursive _ rest, _, _, shape => Option (Position rest shape)

/-- The index required by a recursive field. -/
def next : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → Position code shape → I.Index
  | _, .result _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, _, _, shape, position => next body shape.2 position
  | _, .recursive expression rest, environment, _, shape, position =>
      match position with
      | none => I.evalIndex expression environment
      | some prior => next rest shape prior

/-- Polynomial interpretation of one constructor description. -/
def polynomial {context : List I.SortCode} (code : Code I context) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := Shape code
  Position := Position code
  next := next code

/-- Ordered source arguments, interpreted without polynomial shapes or positions. -/
def Arguments (family : I.Index → Type v) :
    {context : List I.SortCode} → Code I context →
      Env I.Value context → I.Index → Type (max u v)
  | _, .result expression, environment, index =>
      ULift.{max u v} (PLift (I.evalIndex expression environment = index))
  | _, .data sort body, environment, index =>
      Σ value : I.Value sort, Arguments family body (value, environment) index
  | _, .recursive expression rest, environment, index =>
      family (I.evalIndex expression environment) × Arguments family rest environment index

/-- Mapping recursive children retains all data arguments and their order. -/
def Arguments.map {source : I.Index → Type v} {target : I.Index → Type w}
    (mapping : ∀ index, source index → target index) :
    {context : List I.SortCode} → (code : Code I context) →
      {environment : Env I.Value context} → {index : I.Index} →
      Arguments source code environment index → Arguments target code environment index
  | _, .result _, _, _, arguments => ⟨arguments.down⟩
  | _, .data _ body, _, _, arguments =>
      ⟨arguments.1, Arguments.map mapping body arguments.2⟩
  | _, .recursive expression rest, environment, _, arguments =>
      (mapping (I.evalIndex expression environment) arguments.1,
        Arguments.map mapping rest arguments.2)

/-- Separate data shapes from recursive children. -/
def encode {family : I.Index → Type v} :
    {context : List I.SortCode} → (code : Code I context) →
      {environment : Env I.Value context} → {index : I.Index} →
      Arguments family code environment index →
      (polynomial code).Extension (fun _ => family) environment index
  | _, .result _, _, _, arguments => ⟨⟨arguments.down⟩, fun position => nomatch position⟩
  | _, .data _ body, _, _, arguments =>
      let encoded := encode body arguments.2
      ⟨⟨arguments.1, encoded.1⟩, encoded.2⟩
  | _, .recursive _ rest, _, _, arguments =>
      let encoded := encode rest arguments.2
      ⟨encoded.1, fun position => match position with
        | none => arguments.1
        | some prior => encoded.2 prior⟩

/-- Recover the ordered telescope arguments from a polynomial layer. -/
def decode {family : I.Index → Type v} :
    {context : List I.SortCode} → (code : Code I context) →
      {environment : Env I.Value context} → {index : I.Index} →
      (polynomial code).Extension (fun _ => family) environment index →
      Arguments family code environment index
  | _, .result _, _, _, layer => ⟨layer.1.down⟩
  | _, .data _ body, _, _, layer =>
      ⟨layer.1.1, decode body ⟨layer.1.2, layer.2⟩⟩
  | _, .recursive _ rest, _, _, layer =>
      (layer.2 none, decode rest ⟨layer.1, fun position => layer.2 (some position)⟩)

theorem decode_encode {family : I.Index → Type v}
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments family code environment index) :
    decode code (encode code arguments) = arguments := by
  induction code with
  | result _ => rfl
  | data sort body ih =>
      cases arguments with
      | mk value rest =>
          simp only [encode, decode]
          exact congrArg (fun remaining => (⟨value, remaining⟩ : Arguments family (.data sort body) environment index)) (ih rest)
  | recursive expression rest ih =>
      cases arguments with
      | mk value rest =>
          simp only [encode, decode]
          exact congrArg (Prod.mk value) (ih rest)

theorem encode_decode {family : I.Index → Type v}
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (layer : (polynomial code).Extension (fun _ => family) environment index) :
    encode code (decode code layer) = layer := by
  induction code with
  | result expression =>
      rcases layer with ⟨⟨⟨equality⟩⟩, children⟩
      simp only [encode, decode]
      refine Sigma.ext ?_ ?_
      · rfl
      · apply heq_of_eq
        funext position
        exact PEmpty.elim position
  | data sort body ih =>
      rcases layer with ⟨⟨value, shape⟩, children⟩
      simp only [encode, decode]
      erw [ih]
  | recursive expression rest ih =>
      rcases layer with ⟨shape, children⟩
      simp only [encode, decode]
      erw [ih]
      refine Sigma.ext ?_ ?_
      · rfl
      · apply heq_of_eq
        funext position
        cases position <;> rfl

/-- Source constructor arguments and the compiled polynomial layer agree exactly. -/
def argumentsEquiv {context : List I.SortCode} (code : Code I context)
    (environment : Env I.Value context) (family : I.Index → Type v) (index : I.Index) :
    Arguments family code environment index ≃
      (polynomial code).Extension (fun _ => family) environment index where
  toFun := encode code
  invFun := decode code
  left_inv := decode_encode code
  right_inv := encode_decode code

theorem encode_map {source : I.Index → Type v} {target : I.Index → Type w}
    (mapping : ∀ index, source index → target index)
    {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : Arguments source code environment index) :
    encode code (Arguments.map mapping code arguments) =
      Extension.map (polynomial code) (fun _ => mapping) (encode code arguments) := by
  induction code with
  | result expression =>
      simp only [encode, Arguments.map, Extension.map]
      refine Sigma.ext ?_ ?_
      · rfl
      · apply heq_of_eq
        funext position
        exact PEmpty.elim position
  | data sort body ih =>
      cases arguments with
      | mk value remaining =>
          simp only [encode, Arguments.map]
          erw [ih]
          rfl
  | recursive expression rest ih =>
      cases arguments with
      | mk value remaining =>
          simp only [encode, Arguments.map]
          erw [ih]
          refine Sigma.ext ?_ ?_
          · rfl
          · apply heq_of_eq
            funext position
            cases position <;> rfl

/-- One source declaration; list position, rather than name, identifies its occurrence. -/
structure NamedConstructor (I : Interface.{u}) (context : List I.SortCode) where
  name : String
  body : Code I context

/-- A finite constructor inventory compiles to one indexed polynomial. -/
def inventoryPolynomial {context : List I.SortCode}
    (constructors : List (NamedConstructor I context)) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := fun environment index =>
    Σ occurrence : Fin constructors.length,
      Shape (constructors.get occurrence).body environment index
  Position := fun shape => Position (constructors.get shape.1).body shape.2
  next := fun shape => next (constructors.get shape.1).body shape.2

/-- Source inventory semantics retains the selected constructor occurrence. -/
def InventoryArguments {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    (environment : Env I.Value context) (family : I.Index → Type v) (index : I.Index) :=
  Σ occurrence : Fin constructors.length,
    Arguments family (constructors.get occurrence).body environment index

def inventoryEncode {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (arguments : InventoryArguments constructors environment family index) :
    (inventoryPolynomial constructors).Extension (fun _ => family) environment index :=
  let encoded := encode (constructors.get arguments.1).body arguments.2
  ⟨⟨arguments.1, encoded.1⟩, encoded.2⟩

def inventoryDecode {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (layer : (inventoryPolynomial constructors).Extension (fun _ => family) environment index) :
    InventoryArguments constructors environment family index :=
  ⟨layer.1.1, decode (constructors.get layer.1.1).body ⟨layer.1.2, layer.2⟩⟩

/-- The finite source inventory and its polynomial have the same constructor layers. -/
def inventoryArgumentsEquiv {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    (environment : Env I.Value context) (family : I.Index → Type v) (index : I.Index) :
    InventoryArguments constructors environment family index ≃
      (inventoryPolynomial constructors).Extension (fun _ => family) environment index where
  toFun := inventoryEncode constructors
  invFun := inventoryDecode constructors
  left_inv := by
    rintro ⟨occurrence, arguments⟩
    exact congrArg (Sigma.mk occurrence) (decode_encode _ arguments)
  right_inv := by
    rintro ⟨⟨occurrence, shape⟩, children⟩
    exact congrArg (fun inner => (⟨⟨occurrence, inner.1⟩, inner.2⟩ :
      (inventoryPolynomial constructors).Extension (fun _ => family) environment index))
      (encode_decode _ ⟨shape, children⟩)

@[simp] theorem inventoryDecode_encode {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (arguments : InventoryArguments constructors environment family index) :
    inventoryDecode constructors (inventoryEncode constructors arguments) = arguments :=
  (inventoryArgumentsEquiv constructors environment family index).left_inv arguments

@[simp] theorem inventoryEncode_decode {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (layer : (inventoryPolynomial constructors).Extension (fun _ => family) environment index) :
    inventoryEncode constructors (inventoryDecode constructors layer) = layer :=
  (inventoryArgumentsEquiv constructors environment family index).right_inv layer

/-- Act on recursive arguments without changing the selected source occurrence. -/
def InventoryArguments.map {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {source : I.Index → Type v} {target : I.Index → Type w}
    (mapping : ∀ index, source index → target index)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : InventoryArguments constructors environment source index) :
    InventoryArguments constructors environment target index :=
  ⟨arguments.1, Arguments.map mapping (constructors.get arguments.1).body arguments.2⟩

/-- Polynomial interpretation commutes with changing the recursive children. -/
theorem inventoryEncode_map {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {source : I.Index → Type v} {target : I.Index → Type w}
    (mapping : ∀ index, source index → target index)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : InventoryArguments constructors environment source index) :
    inventoryEncode constructors (InventoryArguments.map constructors mapping arguments) =
      Extension.map (inventoryPolynomial constructors) (fun _ => mapping)
        (inventoryEncode constructors arguments) := by
  rcases arguments with ⟨occurrence, arguments⟩
  exact congrArg (fun inner => (⟨⟨occurrence, inner.1⟩, inner.2⟩ :
    (inventoryPolynomial constructors).Extension (fun _ => target) environment index))
    (encode_map mapping (constructors.get occurrence).body arguments)

/-- Interpretation never identifies different constructor occurrences. -/
theorem inventoryEncode_occurrence {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (arguments : InventoryArguments constructors environment family index) :
    (inventoryEncode constructors arguments).1.1 = arguments.1 := rfl

theorem inventoryEncode_ne_of_occurrence_ne {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {environment : Env I.Value context} {family : I.Index → Type v} {index : I.Index}
    (first second : InventoryArguments constructors environment family index)
    (different : first.1 ≠ second.1) :
    inventoryEncode constructors first ≠ inventoryEncode constructors second := by
  intro equal
  exact different (congrArg (fun layer => layer.1.1) equal)

/-- No constructors means no source layer at any result index. -/
theorem emptyInventory_no_arguments {context : List I.SortCode}
    (environment : Env I.Value context) (family : I.Index → Type v) (index : I.Index) :
    IsEmpty (InventoryArguments ([] : List (NamedConstructor I context))
      environment family index) :=
  ⟨fun arguments => Fin.elim0 arguments.1⟩

theorem result_wrong_index {context : List I.SortCode}
    (expression : I.IndexExpr context) (environment : Env I.Value context)
    (family : I.Index → Type v) (index : I.Index)
    (different : I.evalIndex expression environment ≠ index) :
    IsEmpty (Arguments family (.result expression) environment index) :=
  ⟨fun arguments => different arguments.down.down⟩

end Mettapedia.TypeTheory.IndexedPolynomial.Description

/-! Recursive positions have an exact source-order ordinal codec. Index
reading follows the original expression telescope, including data binders;
the coherence theorem joins it to polynomial child indices. -/

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v
variable {I : Interface.{u}}

def recursiveCount : {context : List I.SortCode} → Code I context → Nat
  | _, .result _ => 0
  | _, .data _ body => recursiveCount body
  | _, .recursive _ rest => recursiveCount rest + 1

def positionToFin : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → Position code shape → Fin (recursiveCount code)
  | _, .result _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, _, _, shape, position => positionToFin body shape.2 position
  | _, .recursive _ rest, _, _, shape, position =>
      match position with
      | none => ⟨0, Nat.zero_lt_succ (recursiveCount rest)⟩
      | some prior => (positionToFin rest shape prior).succ

def positionOfFin : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → Fin (recursiveCount code) → Position code shape
  | _, .result _, _, _, _, ordinal => Fin.elim0 ordinal
  | _, .data _ body, _, _, shape, ordinal => positionOfFin body shape.2 ordinal
  | _, .recursive _ rest, _, _, shape, ordinal =>
      Fin.cases none (fun prior => some (positionOfFin rest shape prior)) ordinal

theorem positionOfFin_toFin {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (position : Position code shape) :
    positionOfFin code shape (positionToFin code shape position) = position := by
  induction code with
  | result => exact PEmpty.elim position
  | data sort body ih => exact ih shape.2 position
  | recursive expression rest ih =>
    cases position with
    | none => rfl
    | some position =>
      change some (positionOfFin rest shape (positionToFin rest shape position)) = some position
      exact congrArg some (ih shape position)

theorem positionToFin_ofFin {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (ordinal : Fin (recursiveCount code)) :
    positionToFin code shape (positionOfFin code shape ordinal) = ordinal := by
  induction code with
  | result => exact Fin.elim0 ordinal
  | data sort body ih => exact ih shape.2 ordinal
  | recursive expression rest ih =>
    refine Fin.cases ?_ (fun prior => ?_) ordinal
    · rfl
    · change (positionToFin rest shape (positionOfFin rest shape prior)).succ = prior.succ
      exact congrArg Fin.succ (ih shape prior)

def positionEquivFin {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index) :
    Position code shape ≃ Fin (recursiveCount code) where
  toFun := positionToFin code shape
  invFun := positionOfFin code shape
  left_inv := positionOfFin_toFin code shape
  right_inv := positionToFin_ofFin code shape

/-- Evaluation follows the authored telescope, independently of polynomial positions. -/
def recursiveIndexAt : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Shape code environment index → Fin (recursiveCount code) → I.Index
  | _, .result _, _, _, _, ordinal => Fin.elim0 ordinal
  | _, .data _ body, _, _, shape, ordinal => recursiveIndexAt body shape.2 ordinal
  | _, .recursive expression rest, environment, _, shape, ordinal =>
      Fin.cases (I.evalIndex expression environment) (recursiveIndexAt rest shape) ordinal

theorem next_positionOfFin {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (ordinal : Fin (recursiveCount code)) :
    next code shape (positionOfFin code shape ordinal) = recursiveIndexAt code shape ordinal := by
  induction code with
  | result => exact Fin.elim0 ordinal
  | data sort body ih => exact ih shape.2 ordinal
  | recursive expression rest ih =>
    refine Fin.cases ?_ (fun prior => ?_) ordinal
    · rfl
    · exact ih shape prior

theorem recursiveIndexAt_toFin {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) (position : Position code shape) :
    recursiveIndexAt code shape (positionToFin code shape position) = next code shape position := by
  rw [← next_positionOfFin, positionOfFin_toFin]


def childrenVectorEquiv {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index)
    (family : I.Index → Type v) :
    (∀ position : Position code shape, family (next code shape position)) ≃
      (∀ ordinal : Fin (recursiveCount code), family (recursiveIndexAt code shape ordinal)) :=
  (positionEquivFin code shape).piCongr (fun position =>
    Equiv.cast (congrArg family (recursiveIndexAt_toFin code shape position).symm))

theorem positionToFin_injective {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index) :
    Function.Injective (positionToFin code shape) := (positionEquivFin code shape).injective

#print axioms childrenVectorEquiv
#print axioms positionToFin_injective

#print axioms positionEquivFin
#print axioms next_positionOfFin
#print axioms recursiveIndexAt_toFin
end Mettapedia.TypeTheory.IndexedPolynomial.Description

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u v
variable {I : Interface.{u}}

def vectorPolynomial {context : List I.SortCode} (code : Code I context) :
    IndexedPolynomial.{u, u, u, 0} (Env I.Value context) (fun _ => I.Index) where
  Shape := Shape code
  Position := fun _ => Fin (recursiveCount code)
  next := recursiveIndexAt code

def positionSignatureEquiv {context : List I.SortCode} (code : Code I context) :
    SignatureEquiv (polynomial code) (vectorPolynomial code) where
  shape := fun _ _ => Equiv.refl _
  position := positionEquivFin code
  next_preserved := recursiveIndexAt_toFin code

def inventoryVectorPolynomial {context : List I.SortCode}
    (constructors : List (NamedConstructor I context)) :
    IndexedPolynomial.{u, u, u, 0} (Env I.Value context) (fun _ => I.Index) where
  Shape := (inventoryPolynomial constructors).Shape
  Position := fun shape => Fin (recursiveCount (constructors.get shape.1).body)
  next := fun shape => recursiveIndexAt (constructors.get shape.1).body shape.2

def inventoryPositionSignatureEquiv {context : List I.SortCode}
    (constructors : List (NamedConstructor I context)) :
    SignatureEquiv (inventoryPolynomial constructors) (inventoryVectorPolynomial constructors) where
  shape := fun _ _ => Equiv.refl _
  position := fun shape => positionEquivFin (constructors.get shape.1).body shape.2
  next_preserved := fun shape => recursiveIndexAt_toFin (constructors.get shape.1).body shape.2

noncomputable def inventoryVectorFixEquiv {context : List I.SortCode}
    (constructors : List (NamedConstructor I context)) (environment : Env I.Value context) (index : I.Index) :
    Fix (inventoryPolynomial constructors) environment index ≃
      Fix (inventoryVectorPolynomial constructors) environment index :=
  (inventoryPositionSignatureEquiv constructors).fixEquiv environment index

theorem inventoryVector_fold {context : List I.SortCode}
    (constructors : List (NamedConstructor I context))
    {carrier : Env I.Value context → I.Index → Type v}
    (algebra : Algebra (inventoryVectorPolynomial constructors) carrier)
    (environment : Env I.Value context) (index : I.Index)
    (tree : Fix (inventoryPolynomial constructors) environment index) :
    Fix.fold (inventoryVectorPolynomial constructors) algebra.act environment index
      (inventoryVectorFixEquiv constructors environment index tree) =
      Fix.fold (inventoryPolynomial constructors)
        ((inventoryPositionSignatureEquiv constructors).pullAlgebra algebra).act environment index tree :=
  (inventoryPositionSignatureEquiv constructors).fold_toFix algebra environment index tree

#print axioms positionSignatureEquiv
#print axioms inventoryPositionSignatureEquiv
#print axioms inventoryVectorFixEquiv
#print axioms inventoryVector_fold
end Mettapedia.TypeTheory.IndexedPolynomial.Description

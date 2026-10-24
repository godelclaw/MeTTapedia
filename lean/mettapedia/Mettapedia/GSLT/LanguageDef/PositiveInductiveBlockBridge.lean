import Mettapedia.TypeTheory.PositiveInductiveBlock
import Mettapedia.TypeTheory.IndexedPolynomialEquivalence
import Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples

/-!
# Direct indexed-positive blocks enter the staged admission flower

The existing finite direct-recursion grammar embeds in the richer generic
block recognizer without changing constructor order, names, data shapes or
output-index constraints.  This is the source-level bridge; a complete
equality of the two compiled polynomial position families remains a separate
comparison.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.PositiveInductiveBlock
open Mettapedia.GSLT.LanguageDef

universe u

namespace Direct

def registry : Registry where
  lookup _ := none

def code {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode} :
    IndexedPolynomial.Description.Code I context →
      PositiveInductiveBlock.Code registry I parameterCount context
  | .result index => .result index
  | .data sort body => .data sort (code body)
  | .recursive index rest => .recursive index (code rest)

/-- Direct constructor data and output-index constraints retain their exact
shape interpretation in the richer grammar. -/
theorem shape_eq
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context) :
    @PositiveInductiveBlock.Code.Shape registry I parameterCount context
        (code source) =
      @IndexedPolynomial.Description.Shape I context source := by
  induction source with
  | result => rfl
  | data sort body ih => simp [code, PositiveInductiveBlock.Code.Shape,
      IndexedPolynomial.Description.Shape, ih]
  | recursive index rest ih => simp [code,
      PositiveInductiveBlock.Code.Shape,
      IndexedPolynomial.Description.Shape, ih]

/-- The richer direct-code shape fibre is equivalent to the original one
without erasing data or output-index evidence. -/
def shapeEquiv
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context)
    (environment : Env I.Value context) (index : I.Index) :
    @PositiveInductiveBlock.Code.Shape registry I parameterCount context
        (code source) environment index ≃
      @IndexedPolynomial.Description.Shape I context source environment index :=
  match source with
  | .result _ => Equiv.refl _
  | .data _ body => Equiv.sigmaCongrRight fun value =>
      shapeEquiv body (value, environment) index
  | .recursive _ rest => shapeEquiv rest environment index

/-- Recursive positions agree fibrewise over the shape comparison. -/
def positionEquiv
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : @PositiveInductiveBlock.Code.Shape registry I parameterCount context
      (code source) environment index) :
    @PositiveInductiveBlock.Code.Position registry I parameterCount context
        (code source) environment index shape ≃
      @IndexedPolynomial.Description.Position I context source environment index
        (shapeEquiv source environment index shape) :=
  match source with
  | .result _ => Equiv.refl _
  | .data _ body => positionEquiv body shape.2
  | .recursive _ rest => Equiv.optionCongr (positionEquiv rest shape)

/-- The position equivalence preserves the required recursive child index. -/
theorem next_eq
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : @PositiveInductiveBlock.Code.Shape registry I parameterCount context
      (code source) environment index)
    (position : @PositiveInductiveBlock.Code.Position registry I parameterCount context
      (code source) environment index shape) :
    @IndexedPolynomial.Description.next I context source environment index
        (shapeEquiv source environment index shape)
        (positionEquiv source shape position) =
      @PositiveInductiveBlock.Code.next registry I parameterCount context
        (code source) environment index shape position := by
  induction source with
  | result expression => exact PEmpty.elim position
  | data sort body ih => exact ih shape.2 position
  | recursive expression rest ih =>
      cases position with
      | none => rfl
      | some prior => exact ih shape prior

/-- Complete signature comparison for one direct constructor code. -/
def polynomialEquiv
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context) :
    IndexedPolynomial.SignatureEquiv
      (@PositiveInductiveBlock.Code.polynomial registry I parameterCount context
        (code source))
      (IndexedPolynomial.Description.polynomial source) where
  shape := shapeEquiv source
  position := positionEquiv source
  next_preserved := next_eq source

theorem code_registered
    {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.Code I context) :
    PositiveInductiveBlock.RawCode.WellRegistered
      (code (parameterCount := parameterCount) source) := by
  induction source with
  | result => trivial
  | data sort body ih => exact ih
  | recursive index rest ih => exact ih

def constructor {I : Interface.{u}} {parameterCount : Nat}
    {context : List I.SortCode}
    (source : IndexedPolynomial.Description.NamedConstructor I context) :
    PositiveInductiveBlock.Constructor registry I parameterCount context :=
  ⟨source.name, code source.body⟩

/-- Every existing admitted block enters the richer staged pipeline without
changing constructor order or names. -/
def admitted {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    PositiveInductiveBlock.Admitted registry I parameterCount context where
  constructors := source.constructors.map constructor
  uniqueNames := by
    simpa [constructor, Function.comp_def] using source.uniqueNames

/-- Constructor occurrences are unchanged by the pointwise translation. -/
def occurrenceEquiv {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    Fin (admitted parameterCount source).constructors.length ≃
      Fin source.constructors.length where
  toFun occurrence := ⟨occurrence.val, by
    simpa [admitted] using occurrence.isLt⟩
  invFun occurrence := ⟨occurrence.val, by
    simp [admitted]⟩
  left_inv occurrence := by apply Fin.ext; rfl
  right_inv occurrence := by apply Fin.ext; rfl

theorem constructor_body_eq
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context)
    (occurrence : Fin (admitted parameterCount source).constructors.length) :
    ((admitted parameterCount source).constructors.get occurrence).body =
      code ((source.constructors.get
        (occurrenceEquiv parameterCount source occurrence)).body) := by
  rcases source with ⟨constructors, uniqueNames⟩
  have newBound : occurrence.val <
      (List.map (constructor (parameterCount := parameterCount)) constructors).length := by
    simpa [admitted] using occurrence.isLt
  have oldBound : occurrence.val < constructors.length := by
    simpa [admitted] using occurrence.isLt
  change ((List.map (constructor (parameterCount := parameterCount))
      constructors)[occurrence.val]'newBound).body =
    code (constructors[occurrence.val]'oldBound).body
  rw [List.getElem_map]
  rfl

/-- Each translated constructor has the complete old polynomial signature,
including recursive positions and their child indices. -/
def constructorPolynomialEquiv
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context)
    (occurrence : Fin (admitted parameterCount source).constructors.length) :
    IndexedPolynomial.SignatureEquiv
      (PositiveInductiveBlock.Code.polynomial
        ((admitted parameterCount source).constructors.get occurrence).body)
      (IndexedPolynomial.Description.polynomial
        ((source.constructors.get
          (occurrenceEquiv parameterCount source occurrence)).body)) := by
  rw [constructor_body_eq parameterCount source occurrence]
  exact polynomialEquiv _

/-- The complete translated constructor inventory is polynomially equivalent
to the original inventory.  Constructor occurrences, local shapes, recursive
positions and required child indices are all retained. -/
def admittedPolynomialEquiv
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    IndexedPolynomial.SignatureEquiv
      (PositiveInductiveBlock.Admitted.polynomial
        (admitted parameterCount source))
      source.polynomial where
  shape environment index :=
    Equiv.sigmaCongr (occurrenceEquiv parameterCount source) fun occurrence =>
      (constructorPolynomialEquiv parameterCount source occurrence).shape
        environment index
  position := by
    rintro environment index ⟨occurrence, shape⟩
    exact (constructorPolynomialEquiv parameterCount source occurrence).position
      shape
  next_preserved := by
    rintro environment index ⟨occurrence, shape⟩ position
    exact (constructorPolynomialEquiv parameterCount source occurrence).next_preserved
      shape position

theorem admitted_names
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    (admitted parameterCount source).constructors.map (·.name) =
      source.constructors.map (·.name) := by
  simp [admitted, constructor, Function.comp_def]

theorem admitted_registered
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    (admitted parameterCount source).WellRegistered := by
  intro translated member
  obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
  subst translated
  exact code_registered (parameterCount := parameterCount) original.body

theorem admitted_recognized
    {I : Interface.{u}} (parameterCount : Nat)
    {context : List I.SortCode}
    (source : IndexedInductive.Admitted I context) :
    PositiveInductiveBlock.recognize?
      ((admitted parameterCount source).constructors.map
        PositiveInductiveBlock.quoteConstructor) =
        some (admitted parameterCount source) :=
  PositiveInductiveBlock.recognize_quote _
    (admitted_registered parameterCount source)

end Direct

namespace Controls

open IndexedInductiveExamples

def vector := Direct.admitted 0 Vectors.admitted
def mutualBlock := Direct.admitted 0 Mutual.admitted

theorem vector_names :
    vector.constructors.map (·.name) =
      Vectors.admitted.constructors.map (·.name) :=
  Direct.admitted_names 0 Vectors.admitted

theorem mutual_names :
    mutualBlock.constructors.map (·.name) =
      Mutual.admitted.constructors.map (·.name) :=
  Direct.admitted_names 0 Mutual.admitted

theorem vector_recognized :
    PositiveInductiveBlock.recognize?
      (vector.constructors.map PositiveInductiveBlock.quoteConstructor) =
        some vector :=
  Direct.admitted_recognized 0 Vectors.admitted

theorem mutual_recognized :
    PositiveInductiveBlock.recognize?
      (mutualBlock.constructors.map PositiveInductiveBlock.quoteConstructor) =
        some mutualBlock :=
  Direct.admitted_recognized 0 Mutual.admitted

def vectorPolynomialEquiv :
    IndexedPolynomial.SignatureEquiv vector.polynomial
      Vectors.admitted.polynomial :=
  Direct.admittedPolynomialEquiv 0 Vectors.admitted

def mutualPolynomialEquiv :
    IndexedPolynomial.SignatureEquiv mutualBlock.polynomial
      Mutual.admitted.polynomial :=
  Direct.admittedPolynomialEquiv 0 Mutual.admitted

/-- Changing the sole recursive child's family index destroys polynomial
signature equivalence, even though the outer constructor result is unchanged. -/
def wrongOddCode : IndexedPolynomial.Description.Code Mutual.interface [] :=
  .recursive true (.result true)

theorem translated_odd_not_equiv_wrongChild :
    ¬ Nonempty (IndexedPolynomial.SignatureEquiv
      (PositiveInductiveBlock.Code.polynomial
        (Direct.code (parameterCount := 0) Mutual.oddCode))
      (IndexedPolynomial.Description.polynomial wrongOddCode)) := by
  rintro ⟨equivalent⟩
  let shape : @PositiveInductiveBlock.Code.Shape Direct.registry
      Mutual.interface 0 [] (Direct.code Mutual.oddCode) PUnit.unit true :=
    ⟨⟨rfl⟩⟩
  let position : @PositiveInductiveBlock.Code.Position Direct.registry
      Mutual.interface 0 [] (Direct.code Mutual.oddCode) PUnit.unit true shape := none
  have preserved := equivalent.next_preserved shape position
  generalize mapped : equivalent.position shape position = targetPosition at preserved
  cases targetPosition with
  | none =>
      change true = false at preserved
      exact Bool.noConfusion preserved
  | some impossible => exact PEmpty.elim impossible

def verdicts : List (String × Bool) :=
  [("existing vector block enters staged admission",
      (PositiveInductiveBlock.recognize?
        (vector.constructors.map PositiveInductiveBlock.quoteConstructor)).isSome),
   ("existing mutual block enters staged admission",
      (PositiveInductiveBlock.recognize?
        (mutualBlock.constructors.map PositiveInductiveBlock.quoteConstructor)).isSome)]

end Controls

section AxiomAudit

#print axioms Direct.shape_eq
#print axioms Direct.admitted_names
#print axioms Direct.admitted_recognized
#print axioms Controls.vector_names
#print axioms Controls.mutual_names
#print axioms Controls.vector_recognized
#print axioms Controls.mutual_recognized
#print axioms Direct.polynomialEquiv
#print axioms Direct.admittedPolynomialEquiv
#print axioms Controls.vectorPolynomialEquiv
#print axioms Controls.mutualPolynomialEquiv
#print axioms Controls.translated_odd_not_equiv_wrongChild

end AxiomAudit

end Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge

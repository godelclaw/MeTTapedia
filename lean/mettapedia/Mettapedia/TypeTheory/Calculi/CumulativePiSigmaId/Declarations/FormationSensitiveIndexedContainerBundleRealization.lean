import Mettapedia.TypeTheory.IndexedPositiveContainerInduction
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveRegisteredListGuestLift
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation

/-!
# Formation-sensitive object realizations of registered induction bundles

A semantic induction bundle and a typed object term are not yet related merely
because both exist.  `SelectedObjectBundle` records the missing triangle for
one selected container value:

* an inhabitant of the registered semantic bundle;
* a formation-sensitive object term;
* a quotation of semantic bundles into object syntax;
* an actual computation from the object term to the quotation of the selected
  semantic bundle.

The container's existing exactness law then recovers one motive witness at
every recursive position.  The registry abbreviation fixes the semantic
bundle from the exact entry returned by lookup, so a realization for another
container cannot be substituted by name alone.

The canonical native List and Vector constructions are nontrivial instances.
The List instance uses its typed relation spine.  The Vector instance uses the
closed two-element reflexivity control and its proved native reduction to the
source-ordered semantic bundle.  This interface grants no judgmental
conversion authority and does not imply executable traversal for an
infinitary container.

For complete constructor codes, `PartialLeafProviders` names the admissible
direct and registered-nested object producers. `realizeWithProviders?` walks
the code in source order, selects the actual provider at each leaf, combines
successful results with the pair algebra, and refuses if any provider is
missing. A successful result contains the exact complete semantic bundle and
therefore yields every position witness. This remains evidence-directed:
constructor syntax alone never manufactures a motive witness.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
namespace FormationSensitiveIndexedContainerBundleRealization

open Mettapedia.TypeTheory.IndexedContainer
open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

/-- A formed object term computing to the quotation of one exact semantic
induction bundle.  The semantic bundle is fixed by the selected container
value, and its `exact` field supplies the positionwise meaning. -/
structure SelectedObjectBundle
    {Output : Type}
    {container : IndexedContainer Output}
    {Element : Type} {motive : Element → Type}
    (semantic : InductionBundle container Element motive)
    {output : Output} (value : container.Extension Element output)
    {Head : Type} (rules : Rules Head)
    {n : Nat} (context : Ctx Head n) where
  bundle : semantic.Bundle value
  objectType : Tm Head n
  objectTerm : Tm Head n
  quote : semantic.Bundle value → Tm Head n
  formed : FormationSensitive.Judgment rules context objectTerm objectType
  computes : Relation.ReflTransGen
    (StepCore rules.computation rules.headEq) objectTerm (quote bundle)

namespace SelectedObjectBundle

/-- Read the selected semantic bundle at one actual recursive position. -/
def positionWitness
    {Output : Type}
    {container : IndexedContainer Output}
    {Element : Type} {motive : Element → Type}
    {semantic : InductionBundle container Element motive}
    {output : Output} {value : container.Extension Element output}
    {Head : Type} {rules : Rules Head} {n : Nat} {context : Ctx Head n}
    (realization : SelectedObjectBundle semantic value rules context)
    (position : container.Position value.1) : motive (value.2 position) :=
  (semantic.exact value).toFun realization.bundle position

/-- Complete position coverage is extracted from the same semantic bundle
whose quotation is the target of the retained object computation. -/
noncomputable def positionWitnesses
    {Output : Type}
    {container : IndexedContainer Output}
    {Element : Type} {motive : Element → Type}
    {semantic : InductionBundle container Element motive}
    {output : Output} {value : container.Extension Element output}
    {Head : Type} {rules : Rules Head} {n : Nat} {context : Ctx Head n}
    (realization : SelectedObjectBundle semantic value rules context) :
    ∀ position : container.Position value.1,
      motive (value.2 position) :=
  realization.positionWitness

end SelectedObjectBundle

/-- Registry-scoped spelling of the same contract.  The lookup proof selects
the exact entry whose semantic induction qualification is consumed. -/
abbrev RegisteredSelectedObjectBundle
    {I : IndexedPolynomial.Description.Interface}
    {registry : IndexedPositiveContainer.Registry I}
    (qualified : registry.InductionQualified)
    {name : String} {entry : IndexedPositiveContainer.Entry I}
    (found : registry.lookup name = some entry)
    {Element : Type} (motive : Element → Type)
    {output : entry.Output}
    (value : entry.container.Extension Element output)
    {Head : Type} (rules : Rules Head)
    {n : Nat} (context : Ctx Head n) :=
  SelectedObjectBundle
    ((qualified.entryQualified name entry found).bundle motive)
    value rules context

/-! ## Code-wide quotation and selected realizations -/

namespace Code

variable {I : IndexedPolynomial.Description.Interface}
variable {registry : IndexedPositiveContainer.Registry I}
variable {parameterCount : Nat}

/-- Fold direct witnesses and registered nested bundles into one object
quotation, following the exact constructor-code order.  The nested callback
is indexed by the actual registry entry, output, shape and children. -/
def quoteBundle
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    {Term : Type} (unit : Term) (pair : Term → Term → Term)
    (direct : ∀ index (element : Element index), motive index element → Term)
    (nested : ∀ (name : String) (entry : IndexedPositiveContainer.Entry I)
      (registered : registry.lookup name = some entry)
      {context : List I.SortCode} (output : entry.OutputExpr context)
      (childIndex : I.IndexExpr context)
      (environment : IndexedPolynomial.Description.Env I.Value context)
      (shape : entry.container.Shape (entry.evalOutput output environment))
      (children : entry.container.Position shape →
        Element (I.evalIndex childIndex environment)),
      ((qualified.entryQualified name entry registered).bundle
        (motive (I.evalIndex childIndex environment))).Bundle
          ⟨shape, children⟩ → Term) :
    {context : List I.SortCode} →
    (code : IndexedPositiveContainer.Code I registry parameterCount context) →
    {environment : IndexedPolynomial.Description.Env I.Value context} →
    {index : I.Index} →
    (shape : IndexedPositiveContainer.Code.Shape code environment index) →
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)) →
    IndexedPositiveContainer.Code.Bundle qualified motive code shape children → Term
  | _, .result _, _, _, _, _, _ => unit
  | _, .data _ body, _, _, shape, children, bundle =>
      quoteBundle qualified motive unit pair direct nested body shape.2 children bundle
  | _, .recursive expression rest, environment, _, shape, children, bundle =>
      pair
        (direct (I.evalIndex expression environment) (children none) bundle.1)
        (quoteBundle qualified motive unit pair direct nested rest shape
          (fun position => children (some position)) bundle.2)
  | _, .nested name entry registered output childIndex rest,
      environment, _, shape, children, bundle =>
      pair
        (nested name entry registered output childIndex environment shape.1
          (fun position => children (.inl position)) bundle.1)
        (quoteBundle qualified motive unit pair direct nested rest shape.2
          (fun position => children (.inr position)) bundle.2)

/-- A formed object term computing to the code-wide quotation of one exact
`Code.Bundle`. -/
structure SelectedObjectBundle
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context)
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    (shape : IndexedPositiveContainer.Code.Shape code environment index)
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position))
    {Head : Type} (rules : Rules Head) {n : Nat} (objectContext : Ctx Head n)
    (quote : IndexedPositiveContainer.Code.Bundle qualified motive code shape children →
      Tm Head n) where
  bundle : IndexedPositiveContainer.Code.Bundle qualified motive code shape children
  objectType : Tm Head n
  objectTerm : Tm Head n
  formed : FormationSensitive.Judgment rules objectContext objectTerm objectType
  computes : Relation.ReflTransGen (StepCore rules.computation rules.headEq)
    objectTerm (quote bundle)

namespace SelectedObjectBundle

/-- A connected code-wide realization supplies the exact motive witness at
every direct or registered nested recursive position. -/
noncomputable def positionWitnesses
    {qualified : registry.InductionQualified}
    {Element : I.Index → Type}
    {motive : ∀ index, Element index → Type}
    {context : List I.SortCode}
    {code : IndexedPositiveContainer.Code I registry parameterCount context}
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    {shape : IndexedPositiveContainer.Code.Shape code environment index}
    {children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)}
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    {quote : IndexedPositiveContainer.Code.Bundle qualified motive code shape children →
      Tm Head n}
    (realization : SelectedObjectBundle qualified motive code shape children
      rules objectContext quote) :
    ∀ position : IndexedPositiveContainer.Code.Position code shape,
      motive (IndexedPositiveContainer.Code.next code shape position)
        (children position) :=
  (IndexedPositiveContainer.Code.bundleExact qualified motive code shape children).toFun
    realization.bundle

end SelectedObjectBundle

/-- A selected semantic value with a formed object representation and a
computation to its quotation. -/
structure ObjectValue {Head : Type} (rules : Rules Head)
    {n : Nat} (context : Ctx Head n) (Value : Type) where
  value : Value
  objectType : Tm Head n
  objectTerm : Tm Head n
  quote : Value → Tm Head n
  formed : FormationSensitive.Judgment rules context objectTerm objectType
  computes : Relation.ReflTransGen (StepCore rules.computation rules.headEq)
    objectTerm (quote value)

/-- The formation layer needed to combine independently realized bundle
components. -/
structure PairAlgebra {Head : Type} (rules : Rules Head)
    {n : Nat} (context : Ctx Head n) where
  pair : {First Second : Type} →
    ObjectValue rules context First → ObjectValue rules context Second →
      ObjectValue rules context (First × Second)

/-- Given formed leaves, recursively construct a formed realization of the
complete semantic `Code.Bundle`.  Leaf production remains an explicit caller
obligation. -/
noncomputable def realizeBundle
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (unit : ObjectValue rules objectContext PUnit)
    (direct : ∀ index (element : Element index),
      ObjectValue rules objectContext (motive index element))
    (nested : ∀ (name : String) (entry : IndexedPositiveContainer.Entry I)
      (registered : registry.lookup name = some entry)
      {context : List I.SortCode} (output : entry.OutputExpr context)
      (childIndex : I.IndexExpr context)
      (environment : IndexedPolynomial.Description.Env I.Value context)
      (shape : entry.container.Shape (entry.evalOutput output environment))
      (children : entry.container.Position shape →
        Element (I.evalIndex childIndex environment)),
      ObjectValue rules objectContext
        (((qualified.entryQualified name entry registered).bundle
          (motive (I.evalIndex childIndex environment))).Bundle
            ⟨shape, children⟩)) :
    {context : List I.SortCode} →
    (code : IndexedPositiveContainer.Code I registry parameterCount context) →
    {environment : IndexedPolynomial.Description.Env I.Value context} →
    {index : I.Index} →
    (shape : IndexedPositiveContainer.Code.Shape code environment index) →
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)) →
    ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code shape children)
  | _, .result _, _, _, _, _ => unit
  | _, .data _ body, _, _, shape, children =>
      realizeBundle algebra qualified motive unit direct nested body shape.2 children
  | _, .recursive expression rest, environment, _, shape, children =>
      algebra.pair
        (direct (I.evalIndex expression environment) (children none))
        (realizeBundle algebra qualified motive unit direct nested rest shape
          (fun position => children (some position)))
  | _, .nested name entry registered output childIndex rest,
      environment, _, shape, children =>
      algebra.pair
        (nested name entry registered output childIndex environment shape.1
          (fun position => children (.inl position)))
        (realizeBundle algebra qualified motive unit direct nested rest shape.2
          (fun position => children (.inr position)))

/-- Formation-qualified leaves for one fixed constructor shape.  Unlike a
total callback, this asks only for the direct and nested values that actually
occur in the selected code instance. -/
def LeafRealizations
    {Head : Type} (rules : Rules Head) {n : Nat} (objectContext : Ctx Head n)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type) :
    {context : List I.SortCode} →
    (code : IndexedPositiveContainer.Code I registry parameterCount context) →
    {environment : IndexedPolynomial.Description.Env I.Value context} →
    {index : I.Index} →
    (shape : IndexedPositiveContainer.Code.Shape code environment index) →
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)) → Type
  | _, .result _, _, _, _, _ => PUnit
  | _, .data _ body, _, _, shape, children =>
      LeafRealizations rules objectContext qualified motive body shape.2 children
  | _, .recursive expression rest, environment, _, shape, children =>
      ObjectValue rules objectContext
          (motive (I.evalIndex expression environment) (children none)) ×
        LeafRealizations rules objectContext qualified motive rest shape
          (fun position => children (some position))
  | _, .nested name entry registered _output childIndex rest,
      environment, _, shape, children =>
      ObjectValue rules objectContext
          (((qualified.entryQualified name entry registered).bundle
            (motive (I.evalIndex childIndex environment))).Bundle
              ⟨shape.1, fun position => children (.inl position)⟩) ×
        LeafRealizations rules objectContext qualified motive rest shape.2
          (fun position => children (.inr position))

/-- Assemble exactly the supplied direct and nested leaves into a formed
realization of the complete code bundle. -/
noncomputable def realizeFromLeaves
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (unit : ObjectValue rules objectContext PUnit) :
    {context : List I.SortCode} →
    (code : IndexedPositiveContainer.Code I registry parameterCount context) →
    {environment : IndexedPolynomial.Description.Env I.Value context} →
    {index : I.Index} →
    (shape : IndexedPositiveContainer.Code.Shape code environment index) →
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)) →
    LeafRealizations rules objectContext qualified motive code shape children →
    ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code shape children)
  | _, .result _, _, _, _, _, _ => unit
  | _, .data _ body, _, _, shape, children, leaves =>
      realizeFromLeaves algebra qualified motive unit body shape.2 children leaves
  | _, .recursive _ rest, _, _, shape, children, leaves =>
      algebra.pair leaves.1
        (realizeFromLeaves algebra qualified motive unit rest shape
          (fun position => children (some position)) leaves.2)
  | _, .nested _ _ _ _ _ rest, _, _, shape, children, leaves =>
      algebra.pair leaves.1
        (realizeFromLeaves algebra qualified motive unit rest shape.2
          (fun position => children (.inr position)) leaves.2)

/-- Partial formation-qualified providers for direct recursive positions and
registered nested containers.  A provider may refuse a leaf it does not know
how to realize; successful compilation therefore retains every object-level
formation and computation obligation instead of manufacturing evidence from
the constructor code alone. -/
structure PartialLeafProviders
    {Head : Type} (rules : Rules Head) {n : Nat} (objectContext : Ctx Head n)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type) where
  unit : ObjectValue rules objectContext PUnit
  direct? : ∀ index (element : Element index),
    Option (ObjectValue rules objectContext (motive index element))
  nested? : ∀ (name : String) (entry : IndexedPositiveContainer.Entry I)
    (registered : registry.lookup name = some entry)
    {context : List I.SortCode} (output : entry.OutputExpr context)
    (childIndex : I.IndexExpr context)
    (environment : IndexedPolynomial.Description.Env I.Value context)
    (shape : entry.container.Shape (entry.evalOutput output environment))
    (children : entry.container.Position shape →
      Element (I.evalIndex childIndex environment)),
    Option (ObjectValue rules objectContext
      (((qualified.entryQualified name entry registered).bundle
        (motive (I.evalIndex childIndex environment))).Bundle
          ⟨shape, children⟩))

namespace PartialLeafProviders

/-- Regard total leaf producers as a partial provider table that always
accepts. -/
noncomputable def ofTotal
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (unit : ObjectValue rules objectContext PUnit)
    (direct : ∀ index (element : Element index),
      ObjectValue rules objectContext (motive index element))
    (nested : ∀ (name : String) (entry : IndexedPositiveContainer.Entry I)
      (registered : registry.lookup name = some entry)
      {context : List I.SortCode} (output : entry.OutputExpr context)
      (childIndex : I.IndexExpr context)
      (environment : IndexedPolynomial.Description.Env I.Value context)
      (shape : entry.container.Shape (entry.evalOutput output environment))
      (children : entry.container.Position shape →
        Element (I.evalIndex childIndex environment)),
      ObjectValue rules objectContext
        (((qualified.entryQualified name entry registered).bundle
          (motive (I.evalIndex childIndex environment))).Bundle
            ⟨shape, children⟩)) :
    PartialLeafProviders rules objectContext qualified motive where
  unit := unit
  direct? index element := some (direct index element)
  nested? := fun name entry registered {context} output childIndex environment shape
      children =>
    some (nested name entry registered (context := context) output childIndex environment
      shape children)

end PartialLeafProviders

/-- Recursively route the leaves of one constructor code through the selected
providers.  Missing direct evidence or a missing registered-container
provider refuses the whole realization. -/
noncomputable def realizeWithProviders?
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (providers : PartialLeafProviders rules objectContext qualified motive) :
    {context : List I.SortCode} →
    (code : IndexedPositiveContainer.Code I registry parameterCount context) →
    {environment : IndexedPolynomial.Description.Env I.Value context} →
    {index : I.Index} →
    (shape : IndexedPositiveContainer.Code.Shape code environment index) →
    (children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)) →
    Option (ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code shape children))
  | _, .result _, _, _, _, _ => some providers.unit
  | _, .data _ body, _, _, shape, children =>
      realizeWithProviders? algebra qualified motive providers body shape.2 children
  | _, .recursive expression rest, environment, _, shape, children =>
      match providers.direct? (I.evalIndex expression environment) (children none),
          realizeWithProviders? algebra qualified motive providers rest shape
            (fun position => children (some position)) with
      | some first, some remaining => some (algebra.pair first remaining)
      | _, _ => none
  | _, .nested name entry registered output childIndex rest,
      environment, _, shape, children =>
      match providers.nested? name entry registered output childIndex environment shape.1
          (fun position => children (.inl position)),
          realizeWithProviders? algebra qualified motive providers rest shape.2
            (fun position => children (.inr position)) with
      | some first, some remaining => some (algebra.pair first remaining)
      | _, _ => none

/-- A successful partial-provider compilation is already a complete selected
object realization and therefore covers every actual direct or nested
recursive position. -/
noncomputable def positionWitnessesOfProviderSuccess
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    {qualified : registry.InductionQualified}
    {Element : I.Index → Type}
    {motive : ∀ index, Element index → Type}
    {context : List I.SortCode}
    {code : IndexedPositiveContainer.Code I registry parameterCount context}
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    {shape : IndexedPositiveContainer.Code.Shape code environment index}
    {children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)}
    (realization : ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code shape children)) :
    ∀ position : IndexedPositiveContainer.Code.Position code shape,
      motive (IndexedPositiveContainer.Code.next code shape position)
        (children position) :=
  (IndexedPositiveContainer.Code.bundleExact qualified motive code shape children).toFun
    realization.value

/-- The semantic input needed to realize one constructor occurrence.  The
environment, result index, shape and recursive children remain tied to that
occurrence's actual code. -/
structure ConstructorRequest
    {Element : I.Index → Type}
    {context : List I.SortCode}
    (code : IndexedPositiveContainer.Code I registry parameterCount context) where
  environment : IndexedPolynomial.Description.Env I.Value context
  index : I.Index
  shape : IndexedPositiveContainer.Code.Shape code environment index
  children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
    Element (IndexedPositiveContainer.Code.next code shape position)

/-- Route one constructor occurrence through the generic provider compiler. -/
noncomputable def realizeRequest?
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (providers : PartialLeafProviders rules objectContext qualified motive)
    {context : List I.SortCode}
    {code : IndexedPositiveContainer.Code I registry parameterCount context}
    (request : ConstructorRequest (Element := Element) code) :
    Option (ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code
        request.shape request.children)) :=
  realizeWithProviders? algebra qualified motive providers code
    request.shape request.children

/-- One request for every ordered constructor occurrence. -/
abbrev InventoryRequests
    {Element : I.Index → Type} {context : List I.SortCode}
    (codes : List (IndexedPositiveContainer.Code I registry parameterCount context)) :=
  ∀ occurrence : Fin codes.length,
    ConstructorRequest (Element := Element) (codes.get occurrence)

/-- Lift provider routing pointwise over an ordered admitted inventory.  Each
result retains its occurrence-specific code, shape and refusal. -/
noncomputable def realizeInventory?
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (providers : PartialLeafProviders rules objectContext qualified motive)
    {context : List I.SortCode}
    (codes : List (IndexedPositiveContainer.Code I registry parameterCount context))
    (requests : InventoryRequests (Element := Element) codes) :
    ∀ occurrence : Fin codes.length,
      Option (ObjectValue rules objectContext
        (IndexedPositiveContainer.Code.Bundle qualified motive (codes.get occurrence)
          (requests occurrence).shape (requests occurrence).children)) :=
  fun occurrence => realizeRequest? algebra qualified motive providers (requests occurrence)

@[simp] theorem realizeInventory?_at
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (algebra : PairAlgebra rules objectContext)
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type)
    (providers : PartialLeafProviders rules objectContext qualified motive)
    {context : List I.SortCode}
    (codes : List (IndexedPositiveContainer.Code I registry parameterCount context))
    (requests : InventoryRequests (Element := Element) codes)
    (occurrence : Fin codes.length) :
    realizeInventory? algebra qualified motive providers codes requests occurrence =
      realizeRequest? algebra qualified motive providers (requests occurrence) := rfl

/-- Forget a recursively assembled object value to the code-wide selected
realization contract. -/
noncomputable def ObjectValue.toSelectedCode
    {qualified : registry.InductionQualified}
    {Element : I.Index → Type}
    {motive : ∀ index, Element index → Type}
    {context : List I.SortCode}
    {code : IndexedPositiveContainer.Code I registry parameterCount context}
    {environment : IndexedPolynomial.Description.Env I.Value context}
    {index : I.Index}
    {shape : IndexedPositiveContainer.Code.Shape code environment index}
    {children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
      Element (IndexedPositiveContainer.Code.next code shape position)}
    {Head : Type} {rules : Rules Head} {n : Nat} {objectContext : Ctx Head n}
    (realization : ObjectValue rules objectContext
      (IndexedPositiveContainer.Code.Bundle qualified motive code shape children)) :
    SelectedObjectBundle qualified motive code shape children rules objectContext
      realization.quote where
  bundle := realization.value
  objectType := realization.objectType
  objectTerm := realization.objectTerm
  formed := realization.formed
  computes := realization.computes

end Code

/-! ## Native List instance -/

namespace ListInstance

open NativeIndexedFamilies IntrinsicCanonicalSemantics
open FormationSensitiveRegisteredListGuestLift
open FormationSensitiveNativeList (Typing)

variable {n : Nat} {context : Tower.Ctx n}
variable {source target relation : Tower.Tm n}

/-- Every formation-qualified canonical List lift supplies one connected
object/semantic realization. -/
noncomputable def realization
    {sourceList : CanonicalList context source}
    (lift : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) :
    SelectedObjectBundle
      (IndexedContainer.listInductionBundle (ElementLift target relation))
      (semanticValue sourceList) IntrinsicRelator.rules context := by
  let canonical : CanonicalLift target relation sourceList :=
    ⟨lift.targetList, lift.evidence⟩
  let equivalent := canonicalLiftSemanticBundleEquiv
    target relation sourceList
  refine
    { bundle := equivalent canonical
      objectType := IntrinsicRelator.mapRelApp source target relation
        (encodeList source sourceList) (encodeList target lift.targetList)
      objectTerm := encodeMapRel lift.evidence
      quote := fun bundle =>
        let represented := equivalent.symm bundle
        encodeMapRel represented.2
      formed := (lift.judgment_and_positionEvidence formedContext
        sourceTyping targetTyping relationTyping).1
      computes := ?_ }
  have restored : equivalent.symm (equivalent canonical) = canonical :=
    equivalent.left_inv canonical
  change Relation.ReflTransGen
    (StepCore IntrinsicRelator.rules.computation IntrinsicRelator.rules.headEq)
    (encodeMapRel lift.evidence)
    (encodeMapRel (equivalent.symm (equivalent canonical)).2)
  rw [restored]

/-- The same instance can be viewed through any registry carrying the actual
registered List entry. -/
noncomputable def registeredRealization
    (I : IndexedPolynomial.Description.Interface)
    {sourceList : CanonicalList context source}
    (lift : QualifiedLift target relation sourceList)
    (formedContext : FormationSensitive.ContextFormation IntrinsicRelator.rules context)
    (sourceTyping : Typing context source (sortTm Intrinsic.elementLevel))
    (targetTyping : Typing context target (sortTm Intrinsic.elementLevel))
    (relationTyping : Typing context relation
      (.pi source (.pi (rename wk target) (sortTm Intrinsic.motiveLevel)))) :
    RegisteredSelectedObjectBundle
      (IndexedPositiveContainer.ListInstance.inductionQualified I)
      (name := "List") (entry := IndexedPositiveContainer.ListInstance.entry I)
      (by simp [IndexedPositiveContainer.ListInstance.registry])
      (ElementLift target relation)
      (semanticValue sourceList) IntrinsicRelator.rules context := by
  simpa [RegisteredSelectedObjectBundle,
    IndexedPositiveContainer.ListInstance.inductionQualified,
    IndexedPositiveContainer.ListInstance.entry] using
    realization lift formedContext sourceTyping targetTyping relationTyping

end ListInstance

/-! ## Native Vector instance -/

namespace VectorInstance

open NativeVectorAll
open NativeVectorAll.CanonicalAdequacy
open NativeVectorAll.Controls.CanonicalAdequacyControls
open NativeNaturalVectorFamilies

/-- The closed two-element reflexivity bundle is both formation-checked and
computationally tied to the exact semantic Vector bundle. -/
noncomputable def realization :
    SelectedObjectBundle
      (IndexedContainer.vectorInductionBundle (Witness reflexiveWitness))
      (semanticValue canonicalValues) NativeVectorAll.rules .nil where
  bundle := semanticBundle reflexiveWitness canonicalValues
  objectType := canonicalBundleType
  objectTerm := canonicalBundleEvidence
  quote := fun bundle =>
    quoteBundle (semanticBundleEquiv reflexiveWitness canonicalValues bundle)
  formed := canonicalBundle_formed
  computes := by
    simpa [canonicalBundleEvidence] using
      allEvidence_steps_semanticBundle natTm reflexivePredicate
        reflexiveWitness canonicalValues

/-- The Vector instance is selected by the actual indexed registry lookup. -/
noncomputable def registeredRealization :
    RegisteredSelectedObjectBundle
      IndexedPositiveContainer.VectorControl.inductionQualified
      (name := "Vector") (entry := IndexedPositiveContainer.VectorControl.entry)
      (by simp [IndexedPositiveContainer.VectorControl.registry])
      (Witness reflexiveWitness)
      (semanticValue canonicalValues) NativeVectorAll.rules .nil := by
  simpa [RegisteredSelectedObjectBundle,
    IndexedPositiveContainer.VectorControl.inductionQualified,
    IndexedPositiveContainer.VectorControl.entry] using realization

noncomputable def covers_two_positions :
    ∀ position : IndexedContainer.Examples.vector.Position
        (semanticValue canonicalValues).1,
      Witness reflexiveWitness ((semanticValue canonicalValues).2 position) :=
  SelectedObjectBundle.positionWitnesses registeredRealization

end VectorInstance

/-! ## Mixed direct/nested code control -/

namespace MixedControl

open NativeVectorAll
open NativeVectorAll.CanonicalAdequacy
open NativeVectorAll.Controls.CanonicalAdequacyControls
open NativeNaturalVectorFamilies

abbrev I := IndexedPositiveContainer.VectorControl.interface
abbrev registry := IndexedPositiveContainer.VectorControl.registry
noncomputable def qualified := IndexedPositiveContainer.VectorControl.inductionQualified
abbrev Element : Unit → Type := fun _ => Tower.Tm 0
abbrev motive : ∀ index, Element index → Type :=
  fun _ element => Witness reflexiveWitness element

/-- One direct child followed by a length-indexed Vector of children. -/
def code : IndexedPositiveContainer.Code I registry 0 [] :=
  .data .length
    (.recursive ()
      (.nested "Vector" IndexedPositiveContainer.VectorControl.entry
        (by simp [registry, IndexedPositiveContainer.VectorControl.registry])
        .here () (.result ())))

def environment : IndexedPolynomial.Description.Env I.Value [] := PUnit.unit

def shape : IndexedPositiveContainer.Code.Shape code environment () :=
  IndexedPositiveContainer.VectorControl.shapeAt 2

def vectorChildren : Fin 2 → Tower.Tm 0 :=
  Fin.cases zeroTm (fun _ => succApp zeroTm)

def values : List (Tower.Tm 0) := List.ofFn vectorChildren

def children : ∀ position : IndexedPositiveContainer.Code.Position code shape,
    Element (IndexedPositiveContainer.Code.next code shape position) := by
  intro position
  cases position with
  | none => exact zeroTm
  | some nested =>
      cases nested with
      | inl position =>
          change Fin 2 at position
          exact vectorChildren position
      | inr impossible => exact PEmpty.elim impossible

noncomputable def bundle :
    IndexedPositiveContainer.Code.Bundle qualified motive code shape children := by
  refine ⟨⟨.app reflexiveWitness zeroTm, rfl⟩, ?_, PUnit.unit⟩
  change ListAll (Witness reflexiveWitness) values
  exact pointwiseBundle reflexiveWitness values

noncomputable def quote :
    IndexedPositiveContainer.Code.Bundle qualified motive code shape children →
      Tower.Tm 0 :=
  Code.quoteBundle qualified motive unitEvidence Tm.pair
    (fun _ _ evidence => evidence.1)
    (by
      intro name entry registered context output childIndex environment
        nestedShape nestedChildren nestedBundle
      by_cases same : name = "Vector"
      · subst name
        simp [IndexedPositiveContainer.VectorControl.registry] at registered
        subst entry
        simpa [qualified,
          IndexedPositiveContainer.VectorControl.inductionQualified] using
          (NativeVectorAll.CanonicalAdequacy.quoteBundle nestedBundle)
      · simp [IndexedPositiveContainer.VectorControl.registry, same] at registered)
    code shape children

theorem quote_bundle :
    quote bundle =
      .pair (.app reflexiveWitness zeroTm)
        (.pair (NativeVectorAll.CanonicalAdequacy.quoteBundle
          (pointwiseBundle reflexiveWitness values)) unitEvidence) := by
  rfl

def directEvidence : Tower.Tm 0 :=
  .app reflexiveWitness zeroTm

def directType : Tower.Tm 0 :=
  .app reflexivePredicate zeroTm

def vectorEvidence : Tower.Tm 0 :=
  allEvidence natTm reflexivePredicate reflexiveWitness
    (numeral values.length) (encodeVector natTm values)

def vectorType : Tower.Tm 0 :=
  allType natTm reflexivePredicate (numeral values.length)
    (encodeVector natTm values)

def objectTerm : Tower.Tm 0 :=
  .pair directEvidence (.pair vectorEvidence unitEvidence)

def objectType : Tower.Tm 0 :=
  .sigma directType
    (rename wk (.sigma vectorType (rename wk unitType)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem directAccepted :
    accepted .nil directEvidence directType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem unitAccepted :
    accepted .nil unitEvidence unitType = true := by
  decide +kernel

theorem direct_formed :
    FormationSensitive.Judgment NativeVectorAll.rules .nil
      directEvidence directType :=
  accepted_sound directAccepted

theorem unit_formed :
    FormationSensitive.Judgment NativeVectorAll.rules .nil
      unitEvidence unitType :=
  accepted_sound unitAccepted

theorem values_eq_canonical : values = canonicalValues := by
  decide

theorem vector_formed :
    FormationSensitive.Judgment NativeVectorAll.rules .nil
      vectorEvidence vectorType := by
  simpa [vectorEvidence, vectorType, values_eq_canonical,
    canonicalBundleEvidence, canonicalBundleType] using canonicalBundle_formed

private theorem pair_formed {first firstType second secondType : Tower.Tm 0}
    (firstTyped : FormationSensitive.Judgment NativeVectorAll.rules .nil
      first firstType)
    (secondTyped : FormationSensitive.Judgment NativeVectorAll.rules .nil
      second secondType) :
    FormationSensitive.Judgment NativeVectorAll.rules .nil
      (.pair first second) (.sigma firstType (rename wk secondType)) := by
  let universes := FormationSensitive.towerUniverseRegularity.includeSignature
    NativeVectorAll.signature
  obtain ⟨firstLevel, firstUniverse, firstTypeFormed⟩ :=
    firstTyped.regularity universes
  obtain ⟨secondLevel, secondUniverse, secondTypeFormed⟩ :=
    secondTyped.regularity universes
  cases firstUniverse with
  | sort firstLevel =>
      cases secondUniverse with
      | sort secondLevel =>
          refine ⟨.nil, .pairIntro ?_
            (LevelTower.IsUniverse.sort (.max firstLevel secondLevel))
            firstTyped.typing ?_⟩
          · exact .sigmaForm firstTypeFormed.typing (.sort firstLevel)
              (by simpa only [rename] using
                secondTypeFormed.typing.weaken (extension := firstType))
              (.sort secondLevel) (.sorts firstLevel secondLevel)
          · simpa only [inst0_rename_wk] using secondTyped.typing

theorem object_formed :
    FormationSensitive.Judgment NativeVectorAll.rules .nil
      objectTerm objectType := by
  exact pair_formed direct_formed (pair_formed vector_formed unit_formed)

private theorem steps_pair_fst {left right : Tower.Tm 0}
    (second : Tower.Tm 0) (steps : NativeVectorAll.CanonicalAdequacy.Steps left right) :
    NativeVectorAll.CanonicalAdequacy.Steps
      (.pair left second) (.pair right second) := by
  induction steps with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (.congPairFst step)

private theorem steps_pair_snd {left right : Tower.Tm 0}
    (first : Tower.Tm 0) (steps : NativeVectorAll.CanonicalAdequacy.Steps left right) :
    NativeVectorAll.CanonicalAdequacy.Steps
      (.pair first left) (.pair first right) := by
  induction steps with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (.congPairSnd step)

noncomputable def pairAlgebra :
    Code.PairAlgebra NativeVectorAll.rules (.nil : Tower.Ctx 0) where
  pair first second :=
    { value := (first.value, second.value)
      objectType := .sigma first.objectType (rename wk second.objectType)
      objectTerm := .pair first.objectTerm second.objectTerm
      quote := fun value => .pair (first.quote value.1) (second.quote value.2)
      formed := pair_formed first.formed second.formed
      computes :=
        (steps_pair_fst second.objectTerm first.computes).trans
          (steps_pair_snd (first.quote first.value) second.computes) }

noncomputable def unitObject :
    Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0) PUnit where
  value := PUnit.unit
  objectType := unitType
  objectTerm := unitEvidence
  quote := fun _ => unitEvidence
  formed := unit_formed
  computes := .refl

/-! ### Automatic provider routing control -/

/-- A uniformly inhabited motive lets the control exercise provider routing
without assuming evidence for arbitrary open object terms. -/
abbrev unitMotive : ∀ index, Element index → Type := fun _ _ => PUnit

/-- Every registered container has a semantic induction bundle for the
constant unit motive.  The object realization is the already formed unit term;
the semantic value still comes from the selected registry entry's exactness
law. -/
noncomputable def unitNestedObject
    (name : String) (entry : IndexedPositiveContainer.Entry I)
    (registered : registry.lookup name = some entry)
    {context : List I.SortCode} (output : entry.OutputExpr context)
    (childIndex : I.IndexExpr context)
    (environment : IndexedPolynomial.Description.Env I.Value context)
    (nestedShape : entry.container.Shape (entry.evalOutput output environment))
    (nestedChildren : entry.container.Position nestedShape →
      Element (I.evalIndex childIndex environment)) :
    Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (((qualified.entryQualified name entry registered).bundle
        (unitMotive (I.evalIndex childIndex environment))).Bundle
          ⟨nestedShape, nestedChildren⟩) := by
  let semantic := (qualified.entryQualified name entry registered).bundle
    (unitMotive (I.evalIndex childIndex environment))
  let selected : semantic.Bundle ⟨nestedShape, nestedChildren⟩ :=
    (semantic.exact ⟨nestedShape, nestedChildren⟩).symm (fun _ => PUnit.unit)
  exact
    { value := selected
      objectType := unitType
      objectTerm := unitEvidence
      quote := fun _ => unitEvidence
      formed := unit_formed
      computes := .refl }

/-- A complete provider table: direct leaves use the unit realization and
nested leaves are selected through the actual registry lookup evidence. -/
noncomputable def completeProviders :
    Code.PartialLeafProviders NativeVectorAll.rules (.nil : Tower.Ctx 0)
      qualified unitMotive :=
  Code.PartialLeafProviders.ofTotal qualified unitMotive unitObject
    (fun _ _ => unitObject) unitNestedObject

/-- The corresponding total reference uses the same leaf producers. -/
noncomputable def providerObject :
    Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (IndexedPositiveContainer.Code.Bundle qualified unitMotive code shape children) :=
  Code.realizeBundle pairAlgebra qualified unitMotive unitObject
    (fun _ _ => unitObject) unitNestedObject code shape children

/-- Provider selection over the mixed direct/Vector code agrees exactly with
the total reference producer. -/
theorem completeProviders_compile :
    Code.realizeWithProviders? pairAlgebra qualified unitMotive completeProviders
      code shape children = some providerObject := by
  rfl

noncomputable def providerPositionWitnesses :
    ∀ position : IndexedPositiveContainer.Code.Position code shape,
      unitMotive (IndexedPositiveContainer.Code.next code shape position)
        (children position) :=
  Code.positionWitnessesOfProviderSuccess providerObject

/-- A provider table with no registered-container implementation refuses at
the actual Vector leaf even though the direct leaf is available. -/
noncomputable def missingNestedProviders :
    Code.PartialLeafProviders NativeVectorAll.rules (.nil : Tower.Ctx 0)
      qualified unitMotive where
  unit := unitObject
  direct? _ _ := some unitObject
  nested? := fun _ _ _ {_} _ _ _ _ _ => none

theorem missingNestedProvider_refused :
    Code.realizeWithProviders? pairAlgebra qualified unitMotive
      missingNestedProviders code shape children = none := by
  rfl

/-- Missing direct evidence is an independent refusal from a missing nested
provider. -/
noncomputable def missingDirectProviders :
    Code.PartialLeafProviders NativeVectorAll.rules (.nil : Tower.Ctx 0)
      qualified unitMotive where
  unit := unitObject
  direct? _ _ := none
  nested? := completeProviders.nested?

theorem missingDirectProvider_refused :
    Code.realizeWithProviders? pairAlgebra qualified unitMotive
      missingDirectProviders code shape children = none := by
  rfl

noncomputable def directObject :
    Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (Witness reflexiveWitness zeroTm) where
  value := ⟨directEvidence, rfl⟩
  objectType := directType
  objectTerm := directEvidence
  quote := fun evidence => evidence.1
  formed := direct_formed
  computes := .refl

noncomputable def vectorObject :
    Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (ListAll (Witness reflexiveWitness) values) where
  value := pointwiseBundle reflexiveWitness values
  objectType := vectorType
  objectTerm := vectorEvidence
  quote := NativeVectorAll.CanonicalAdequacy.quoteBundle
  formed := vector_formed
  computes := allEvidence_steps natTm reflexivePredicate reflexiveWitness values

noncomputable def leaves :
    Code.LeafRealizations NativeVectorAll.rules (.nil : Tower.Ctx 0)
      qualified motive code shape children := by
  change Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (Witness reflexiveWitness zeroTm) ×
    (Code.ObjectValue NativeVectorAll.rules (.nil : Tower.Ctx 0)
      (ListAll (Witness reflexiveWitness) values) × PUnit)
  exact ⟨directObject, vectorObject, PUnit.unit⟩

noncomputable def compiledObject :=
  Code.realizeFromLeaves pairAlgebra qualified motive unitObject
    code shape children leaves

noncomputable def compiledRealization :=
  Code.ObjectValue.toSelectedCode compiledObject

theorem compiled_value_eq : compiledObject.value = bundle := by
  rfl

theorem compiled_term_eq : compiledObject.objectTerm = objectTerm := by
  rfl

theorem compiled_type_eq : compiledObject.objectType = objectType := by
  rfl

theorem compiled_quote_eq : compiledObject.quote = quote := by
  funext selected
  rfl

noncomputable def compiledGenericRealization :
    Code.SelectedObjectBundle qualified motive code shape children
      NativeVectorAll.rules .nil quote := by
  rw [← compiled_quote_eq]
  exact compiledRealization

noncomputable def compiledPositionWitnesses :
    ∀ position : IndexedPositiveContainer.Code.Position code shape,
      motive (IndexedPositiveContainer.Code.next code shape position)
        (children position) :=
  Code.SelectedObjectBundle.positionWitnesses compiledGenericRealization

theorem object_steps_quote :
    NativeVectorAll.CanonicalAdequacy.Steps objectTerm (quote bundle) := by
  rw [quote_bundle]
  exact steps_pair_snd directEvidence
    (steps_pair_fst unitEvidence
      (allEvidence_steps natTm reflexivePredicate reflexiveWitness values))

noncomputable def realization :
    Code.SelectedObjectBundle qualified motive code shape children
      NativeVectorAll.rules .nil quote where
  bundle := bundle
  objectType := objectType
  objectTerm := objectTerm
  formed := object_formed
  computes := object_steps_quote

noncomputable def allPositionWitnesses :
    ∀ position : IndexedPositiveContainer.Code.Position code shape,
      motive (IndexedPositiveContainer.Code.next code shape position)
        (children position) :=
  Code.SelectedObjectBundle.positionWitnesses realization

end MixedControl

/-! ## Negative control -/

namespace ReaderNegative

abbrev I := IndexedPositiveContainer.VectorControl.interface
abbrev entry := IndexedPositiveContainer.ReaderControl.entry I
abbrev registry := IndexedPositiveContainer.ReaderControl.registry I

theorem found : registry.lookup "Reader" = some entry := by
  simp [registry, entry, IndexedPositiveContainer.ReaderControl.registry]

noncomputable def semantic :
    InductionBundle entry.container Unit (fun _ => Empty) :=
  ((IndexedPositiveContainer.ReaderControl.inductionQualified I).entryQualified
    "Reader" entry found).bundle (fun _ => Empty)

def value : entry.container.Extension Unit () :=
  ⟨(), fun _ => ()⟩

/-- A positive container with an impossible motive has no semantic induction
bundle to quote.  Object formation cannot manufacture the missing position
witnesses. -/
theorem semanticBundle_empty : IsEmpty (semantic.Bundle value) := by
  constructor
  intro bundle
  change Nat → Empty at bundle
  exact Empty.elim (bundle 0)

theorem noSelectedObjectBundle
    {Head : Type} (rules : Rules Head) {n : Nat} (context : Ctx Head n) :
    IsEmpty (SelectedObjectBundle semantic value rules context) := by
  constructor
  intro realization
  exact semanticBundle_empty.false realization.bundle

/-- The partial provider compiler cannot succeed for the same impossible
motive: any successful result would contain the missing semantic bundle as its
value. -/
theorem noObjectValue
    {Head : Type} (rules : Rules Head) {n : Nat} (context : Ctx Head n) :
    IsEmpty (Code.ObjectValue rules context (semantic.Bundle value)) := by
  constructor
  intro realization
  exact semanticBundle_empty.false realization.value

end ReaderNegative

section AxiomAudit

#print axioms SelectedObjectBundle.positionWitnesses
#print axioms Code.SelectedObjectBundle.positionWitnesses
#print axioms Code.realizeFromLeaves
#print axioms Code.realizeWithProviders?
#print axioms Code.positionWitnessesOfProviderSuccess
#print axioms Code.realizeRequest?
#print axioms Code.realizeInventory?
#print axioms Code.realizeInventory?_at
#print axioms Code.ObjectValue.toSelectedCode
#print axioms ListInstance.realization
#print axioms ListInstance.registeredRealization
#print axioms VectorInstance.realization
#print axioms VectorInstance.registeredRealization
#print axioms VectorInstance.covers_two_positions
#print axioms MixedControl.quote_bundle
#print axioms MixedControl.direct_formed
#print axioms MixedControl.unit_formed
#print axioms MixedControl.vector_formed
#print axioms MixedControl.object_formed
#print axioms MixedControl.object_steps_quote
#print axioms MixedControl.realization
#print axioms MixedControl.allPositionWitnesses
#print axioms MixedControl.pairAlgebra
#print axioms MixedControl.compiledObject
#print axioms MixedControl.compiled_value_eq
#print axioms MixedControl.compiled_term_eq
#print axioms MixedControl.compiled_type_eq
#print axioms MixedControl.compiled_quote_eq
#print axioms MixedControl.compiledGenericRealization
#print axioms MixedControl.compiledPositionWitnesses
#print axioms MixedControl.completeProviders_compile
#print axioms MixedControl.providerPositionWitnesses
#print axioms MixedControl.missingNestedProvider_refused
#print axioms MixedControl.missingDirectProvider_refused
#print axioms ReaderNegative.semanticBundle_empty
#print axioms ReaderNegative.noSelectedObjectBundle
#print axioms ReaderNegative.noObjectValue

end AxiomAudit

end FormationSensitiveIndexedContainerBundleRealization
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

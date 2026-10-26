import Mettapedia.TypeTheory.IndexedPolynomialDescription

/-!
# Environment-independent constructor data

A first-order constructor's nonrecursive data is a fixed product of its
source data sorts. Its result index is computed from that data and the
parameter environment. The dependent sum of all indexed shapes is equivalent
to the data product, preserving each original data value and index constraint.
Recursive child indices agree with independent telescope evaluation.

These are semantic descriptions with host equality in result constraints;
they do not erase object proof syntax or certify a native type declaration.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.IndexedPolynomial.Description
universe u
variable {I : Interface.{u}}

def dataSorts : {context : List I.SortCode} → Code I context → List I.SortCode
  | _, .result _ => []
  | _, .data sort body => sort :: dataSorts body
  | _, .recursive _ rest => dataSorts rest

abbrev ConstructorData {context : List I.SortCode} (code : Code I context) := Env I.Value (dataSorts code)

def dataResultIndex : {context : List I.SortCode} → (code : Code I context) →
    Env I.Value context → ConstructorData code → I.Index
  | _, .result expression, environment, _ => I.evalIndex expression environment
  | _, .data _ body, environment, data => dataResultIndex body (data.1, environment) data.2
  | _, .recursive _ rest, environment, data => dataResultIndex rest environment data

def shapeFromData : {context : List I.SortCode} → (code : Code I context) →
    (environment : Env I.Value context) → (data : ConstructorData code) →
    Shape code environment (dataResultIndex code environment data)
  | _, .result _, _, _ => ⟨⟨rfl⟩⟩
  | _, .data _ body, environment, data => ⟨data.1, shapeFromData body (data.1, environment) data.2⟩
  | _, .recursive _ rest, environment, data => shapeFromData rest environment data

def dataFromShape : {context : List I.SortCode} → (code : Code I context) →
    {environment : Env I.Value context} → {index : I.Index} →
    Shape code environment index → ConstructorData code
  | _, .result _, _, _, _ => PUnit.unit
  | _, .data _ body, _, _, shape => (shape.1, dataFromShape body shape.2)
  | _, .recursive _ rest, _, _, shape => dataFromShape rest shape

theorem dataFromShape_fromData {context : List I.SortCode} (code : Code I context)
    (environment : Env I.Value context) (data : ConstructorData code) :
    dataFromShape code (shapeFromData code environment data) = data := by
  induction code with
  | result => cases data; rfl
  | data sort body hypotheses =>
    rcases data with ⟨value, rest⟩
    exact congrArg (Prod.mk value) (hypotheses (value, environment) rest)
  | recursive expression rest hypotheses => exact hypotheses environment data

theorem shapeFromData_fromShape {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index) :
    (⟨dataResultIndex code environment (dataFromShape code shape), shapeFromData code environment (dataFromShape code shape)⟩ :
      Σ index, Shape code environment index) = ⟨index, shape⟩ := by
  induction code with
  | result =>
    rcases shape with ⟨⟨same⟩⟩
    cases same
    rfl
  | data sort body hypotheses =>
    exact congrArg (fun point : Σ index, Shape body (shape.1, environment) index =>
      (⟨point.1, ⟨shape.1, point.2⟩⟩ : Σ index, Shape (.data sort body) environment index)) (hypotheses shape.2)
  | recursive expression rest hypotheses => exact hypotheses shape

theorem dataResultIndex_fromShape {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index) :
    dataResultIndex code environment (dataFromShape code shape) = index :=
  congrArg Sigma.fst (shapeFromData_fromShape code shape)

theorem realizes_data_iff {context : List I.SortCode} (code : Code I context)
    (environment : Env I.Value context) (index : I.Index) (data : ConstructorData code) :
    (∃ shape : Shape code environment index, dataFromShape code shape = data) ↔
      dataResultIndex code environment data = index := by
  constructor
  · rintro ⟨shape, same⟩
    exact (congrArg (dataResultIndex code environment) same).symm.trans (dataResultIndex_fromShape code shape)
  · intro same
    cases same
    exact ⟨shapeFromData code environment data, dataFromShape_fromData code environment data⟩

def constructorDataEquiv {context : List I.SortCode} (code : Code I context) (environment : Env I.Value context) :
    (Σ index, Shape code environment index) ≃ ConstructorData code where
  toFun := fun point => dataFromShape code point.2
  invFun := fun data => ⟨dataResultIndex code environment data, shapeFromData code environment data⟩
  left_inv := fun point => shapeFromData_fromShape code point.2
  right_inv := dataFromShape_fromData code environment

def dataRecursiveIndexAt : {context : List I.SortCode} → (code : Code I context) →
    Env I.Value context → ConstructorData code → Fin (recursiveCount code) → I.Index
  | _, .result _, _, _, slot => Fin.elim0 slot
  | _, .data _ body, environment, data, slot => dataRecursiveIndexAt body (data.1, environment) data.2 slot
  | _, .recursive expression rest, environment, data, slot =>
    Fin.cases (I.evalIndex expression environment) (dataRecursiveIndexAt rest environment data) slot

theorem recursive_index_from_data {context : List I.SortCode} (code : Code I context)
    {environment : Env I.Value context} {index : I.Index} (shape : Shape code environment index)
    (slot : Fin (recursiveCount code)) :
    dataRecursiveIndexAt code environment (dataFromShape code shape) slot = recursiveIndexAt code shape slot := by
  induction code with
  | result => exact Fin.elim0 slot
  | data sort body hypotheses => exact hypotheses shape.2 slot
  | recursive expression rest hypotheses =>
    refine Fin.cases ?_ (fun prior => ?_) slot
    · rfl
    · exact hypotheses shape prior

abbrev InventoryData {context : List I.SortCode} (constructors : List (NamedConstructor I context)) :=
  Σ occurrence : Fin constructors.length, ConstructorData (constructors.get occurrence).body

def inventoryDataEquiv {context : List I.SortCode} (constructors : List (NamedConstructor I context))
    (environment : Env I.Value context) :
    (Σ index, (inventoryPolynomial constructors).Shape environment index) ≃ InventoryData constructors where
  toFun := fun point => ⟨point.2.1, dataFromShape (constructors.get point.2.1).body point.2.2⟩
  invFun := fun data => ⟨dataResultIndex (constructors.get data.1).body environment data.2,
    ⟨data.1, shapeFromData (constructors.get data.1).body environment data.2⟩⟩
  left_inv := by
    rintro ⟨index, occurrence, shape⟩
    exact congrArg (fun point : Σ index, Shape (constructors.get occurrence).body environment index =>
      (⟨point.1, ⟨occurrence, point.2⟩⟩ : Σ index, (inventoryPolynomial constructors).Shape environment index))
      (shapeFromData_fromShape (constructors.get occurrence).body shape)
  right_inv := by
    rintro ⟨occurrence, data⟩
    apply congrArg (Sigma.mk occurrence)
    exact dataFromShape_fromData (constructors.get occurrence).body environment data

#print axioms constructorDataEquiv
#print axioms recursive_index_from_data
#print axioms inventoryDataEquiv
end Mettapedia.TypeTheory.IndexedPolynomial.Description

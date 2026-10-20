import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGenerated

/-!
# Complete receipts of generated inductive computation

Every constructor row contributes exactly its generated iota schema. Receipts
retain the row index, all instantiated metavariables, and both endpoints.
Their existence is equivalent to the existing generator's root relation.
Typed receipts additionally carry a substitution through the generated iota
telescope. Judgmental authority is then supplied by the selected, admissible
declaration package, including its universe and formation requirements.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace IndexedPolynomialGenerated

open TypedEquality Normalization Annotated

variable {Head : Type}

/-- A source constructor occurrence, including the original ordinal. -/
structure Origin (ctors : List (DeclName × List (Field Head))) where
  index : Nat
  constructor : DeclName
  fields : List (Field Head)
  lookup : ctors[index]? = some (constructor, fields)

namespace Origin

variable {ctors : List (DeclName × List (Field Head))}

abbrev arity (origin : Origin ctors) : Nat := 1 + ctors.length + origin.fields.length

def left (origin : Origin ctors) (rec : DeclName) : Tm Head origin.arity :=
  iotaLeft rec origin.constructor ctors.length origin.fields.length

def right (origin : Origin ctors) (rec : DeclName) : Tm Head origin.arity :=
  iotaRight rec ctors.length origin.index origin.fields

def schema (origin : Origin ctors) (rec : DeclName) : Schema Head :=
  ⟨origin.arity, origin.left rec, origin.right rec⟩

theorem declared (origin : Origin ctors) (rec : DeclName) :
    iotaSchema rec ctors (origin.left rec) (origin.right rec) :=
  ⟨origin.index, origin.constructor, origin.fields, origin.lookup, rfl⟩

/-- Source ordinals bound the inventory; no default constructor is introduced. -/
theorem index_lt (origin : Origin ctors) : origin.index < ctors.length :=
  List.getElem?_eq_some_iff.mp origin.lookup |>.1

end Origin

/-- Enumerate actual constructor occurrences, retaining duplicate occurrences
until the separately checked distinct-name condition is applied. -/
def origins (ctors : List (DeclName × List (Field Head))) : List (Origin ctors) :=
  List.ofFn fun index : Fin ctors.length =>
    ⟨index.val, ctors[index].1, ctors[index].2, List.getElem?_eq_getElem index.isLt⟩

@[simp] theorem origins_length (ctors : List (DeclName × List (Field Head))) :
    (origins ctors).length = ctors.length := by simp [origins]

theorem origin_mem (ctors : List (DeclName × List (Field Head))) (origin : Origin ctors) :
    origin ∈ origins ctors := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨origin.index, origin.index_lt⟩, ?_⟩
  obtain ⟨index, name, fields, found⟩ := origin
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have get := (List.getElem?_eq_some_iff.mp found).2
  dsimp only
  change (⟨index, ctors[index].1, ctors[index].2, _⟩ : Origin ctors) = _
  simp only [get]

/-- The finite schema inventory is generated from the same source occurrences. -/
def schemas (ctors : List (DeclName × List (Field Head))) (rec : DeclName) : List (Schema Head) :=
  (origins ctors).map (fun origin => origin.schema rec)

theorem schemas_complete (ctors : List (DeclName × List (Field Head))) (rec : DeclName)
    {arity : Nat} (left right : Tm Head arity) :
    (⟨arity, left, right⟩ : Schema Head) ∈ schemas ctors rec ↔
      iotaSchema rec ctors left right := by
  constructor
  · intro member
    obtain ⟨origin, _, equality⟩ := List.mem_map.mp member
    have declared := origin.declared rec
    change origin.schema rec = ⟨arity, left, right⟩ at equality
    cases equality
    exact declared
  · rintro ⟨index, name, fields, lookup, equality⟩
    let origin : Origin ctors := ⟨index, name, fields, lookup⟩
    exact List.mem_map.mpr ⟨origin, origin_mem ctors origin, equality.symm⟩

/-- A full schema instance, with source origin and every metavariable retained. -/
structure Receipt (ctors : List (DeclName × List (Field Head))) (ambient : Nat) where
  origin : Origin ctors
  assignment : Sub Head origin.arity ambient

namespace Receipt

variable {ctors : List (DeclName × List (Field Head))} {ambient : Nat}

def left (receipt : Receipt ctors ambient) (rec : DeclName) : Tm Head ambient :=
  subst receipt.assignment (receipt.origin.left rec)

def right (receipt : Receipt ctors ambient) (rec : DeclName) : Tm Head ambient :=
  subst receipt.assignment (receipt.origin.right rec)

theorem sound (receipt : Receipt ctors ambient) (rec : DeclName) :
    IotaStep rec ctors (receipt.left rec) (receipt.right rec) :=
  (iota_presents rec ctors).mpr
    (.instantiate (receipt.origin.declared rec) receipt.assignment)

/-- Substitution changes captured values, retaining the constructor origin. -/
def substitute (receipt : Receipt ctors ambient) {other : Nat} (σ : Sub Head ambient other) :
    Receipt ctors other where
  origin := receipt.origin
  assignment := fun index => subst σ (receipt.assignment index)

theorem substitute_left (receipt : Receipt ctors ambient) (rec : DeclName)
    {other : Nat} (σ : Sub Head ambient other) :
    (receipt.substitute σ).left rec = subst σ (receipt.left rec) := by
  exact (subst_comp _ _ _).symm

theorem substitute_right (receipt : Receipt ctors ambient) (rec : DeclName)
    {other : Nat} (σ : Sub Head ambient other) :
    (receipt.substitute σ).right rec = subst σ (receipt.right rec) := by
  exact (subst_comp _ _ _).symm

end Receipt

/-- No generated root step is omitted, and no receipt invents a root step. -/
theorem receipt_iff (ctors : List (DeclName × List (Field Head))) (rec : DeclName)
    {ambient : Nat} (left right : Tm Head ambient) :
    IotaStep rec ctors left right ↔
      ∃ receipt : Receipt ctors ambient, receipt.left rec = left ∧ receipt.right rec = right := by
  constructor
  · intro step
    have schemaStep := (iota_presents rec ctors).mp step
    cases schemaStep with
    | instantiate rule assignment =>
      obtain ⟨index, name, fields, lookup, equality⟩ := rule
      cases equality
      exact ⟨⟨⟨index, name, fields, lookup⟩, assignment⟩, rfl, rfl⟩
  · rintro ⟨receipt, rfl, rfl⟩
    exact receipt.sound rec

/-- Typed instances retain the exact telescope of the source constructor's
schema, not just an arbitrary common result type. -/
structure TypedReceipt {R : Rules Head} (Q : ChurchRules R) (datatype : Datatype Head)
    {ambient : Nat} (context : CCtx Head ambient) where
  origin : Origin datatype.ctors
  assignment : CSub Head origin.arity ambient
  typed : CSubstMor Q
    (liftCtx (iotaTele datatype.type datatype.motiveUniverse datatype.ctors origin.fields))
    context assignment

/-- Every source constructor has a canonical typed receipt in the generated
metavariable telescope. No schema is supplied by the caller or omitted. -/
def canonicalTypedReceipt {R : Rules Head} (Q : ChurchRules R) (datatype : Datatype Head)
    (origin : Origin datatype.ctors) :
    TypedReceipt Q datatype
      (liftCtx (iotaTele datatype.type datatype.motiveUniverse datatype.ctors origin.fields)) where
  origin := origin
  assignment := CTm.ids
  typed := by
    intro index
    dsimp only [CTyped]
    rw [CTm.subst_ids]
    exact CDerivable.var index

namespace TypedReceipt

variable {R : Rules Head} {Q : ChurchRules R} {datatype : Datatype Head}
  {ambient : Nat} {context : CCtx Head ambient}

def erase (receipt : TypedReceipt Q datatype context) : Receipt datatype.ctors ambient where
  origin := receipt.origin
  assignment := CTm.eraseSub receipt.assignment

def left (receipt : TypedReceipt Q datatype context) : CTm Head ambient :=
  (liftTm (receipt.origin.left datatype.recursor)).subst receipt.assignment

def right (receipt : TypedReceipt Q datatype context) : CTm Head ambient :=
  (liftTm (receipt.origin.right datatype.recursor)).subst receipt.assignment

def type (receipt : TypedReceipt Q datatype context) : CTm Head ambient :=
  (liftTm (iotaTarget receipt.origin.constructor datatype.ctors.length
    receipt.origin.fields.length)).subst receipt.assignment

@[simp] theorem erase_left (receipt : TypedReceipt Q datatype context) :
    receipt.left.erase = receipt.erase.left datatype.recursor := by
  simp [left, erase, Receipt.left]

@[simp] theorem erase_right (receipt : TypedReceipt Q datatype context) :
    receipt.right.erase = receipt.erase.right datatype.recursor := by
  simp [right, erase, Receipt.right]

/-- A selected admissible declaration package grants the generated computation
its typed equality. The policy and formation premises are retained here. -/
theorem holds {L : Type} [UniverseLevel.LevelOrder L]
    (levels : LevelModel R L) {B : ChurchRules R} {declarations : List (Declaration Head)}
    (admissible : AdmissibleDeclarations B declarations)
    (member : Declaration.datatype datatype ∈ declarations)
    (receipt : TypedReceipt (withDeclarations B declarations) datatype context) :
    CEqual (withDeclarations B declarations) context receipt.left receipt.right receipt.type :=
  admissible.iota_holds levels member receipt.origin.lookup receipt.assignment receipt.typed

end TypedReceipt

end IndexedPolynomialGenerated
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

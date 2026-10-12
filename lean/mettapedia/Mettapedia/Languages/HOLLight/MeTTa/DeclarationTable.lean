import Mettapedia.Languages.HOLLight.MeTTa.OperatorTable

/-!
# Finite declared signatures at the authored HOL boundary

Both operator and constant tables are constructed along the existing registered
context extensions. Constant lookup retains the entire schema and the chosen
declaration identity payload. The registration proof concerns actual symbols,
including their definition provenance, rather than only their printed names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open DefinitionAdapters
open TypeSubstitution (nameAtom typeAtom)
open Representation (registeredOperatorAtom)

structure Table (context : TheoryContext) where
  operators : OperatorTable.Table context
  constants : List (Const × Ty)
  registered : ∀ entry ∈ constants, context.signature.constants entry.1 = some entry.2
  complete : ∀ constant schema, context.signature.constants constant = some schema →
    (constant, schema) ∈ constants

def empty : Table TheoryContext.empty :=
  { operators := OperatorTable.empty
    constants := []
    registered := by simp
    complete := by simp [TheoryContext.empty] }

def addTypeOperator {context : TheoryContext} (before : Table context)
    (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    Table (context.addTypeOperator operator arity fresh) :=
  { operators := OperatorTable.addTypeOperator before.operators operator arity fresh
    constants := before.constants
    registered := before.registered
    complete := before.complete }

def addConstant {context : TheoryContext} (before : Table context)
    (constant : Const) (schema : Ty) (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    Table (context.addConstant constant schema formed fresh) :=
  { operators := OperatorTable.addConstant before.operators constant schema formed fresh
    constants := (constant, schema) :: before.constants
    registered := by
      intro entry member
      rcases List.mem_cons.mp member with new | earlier
      · subst entry
        exact context.addConstant_registered constant schema formed fresh
      · exact (context.addConstant_includes constant schema formed fresh).2 _ _
          (before.registered entry earlier)
    complete := by
      intro candidate candidateSchema found
      by_cases same : Const.same candidate constant = true
      · have equal := (Const.same_eq_true_iff candidate constant).mp same
        subst candidate
        have schemaEqual : schema = candidateSchema := by
          simpa [TheoryContext.addConstant, Signature.addConstant, Const.same_eq_true_iff] using found
        subst candidateSchema
        exact List.mem_cons_self
      · have old : context.signature.constants candidate = some candidateSchema := by
          simpa [TheoryContext.addConstant, Signature.addConstant, same] using found
        exact List.mem_cons_of_mem _ (before.complete candidate candidateSchema old) }

def entryAtom (identity : Const → Atom) (entry : Const × Ty) : Atom × Atom :=
  (nameAtom (constantName entry.1), .expression [.symbol "HOL:Constant",
    typeAtom registeredOperatorAtom entry.2, identity entry.1])

def entriesAtom {context : TheoryContext} (table : Table context) (identity : Const → Atom) :
    List (Atom × Atom) := table.constants.map (entryAtom identity)

def tableAtom {context : TheoryContext} (table : Table context) (identity : Const → Atom) : Atom :=
  Lookup.table (entriesAtom table identity)

theorem registered_name_faithful (context : TheoryContext) (left right : Const)
    (leftSchema rightSchema : Ty)
    (leftFound : context.signature.constants left = some leftSchema)
    (rightFound : context.signature.constants right = some rightSchema)
    (same : nameAtom (constantName left) = nameAtom (constantName right)) : left = right :=
  context.uniqueConstantNames left right leftSchema rightSchema leftFound rightFound
    (TypeSubstitution.nameAtom_injective same)

private theorem lookup_registered_entries (context : TheoryContext) (entries : List (Const × Ty))
    (registered : ∀ entry ∈ entries, context.signature.constants entry.1 = some entry.2)
    (identity : Const → Atom) (constant : Const) (schema : Ty)
    (found : context.signature.constants constant = some schema)
    (member : (constant, schema) ∈ entries) :
    (entries.map (entryAtom identity)).lookup (nameAtom (constantName constant)) =
      some (.expression [.symbol "HOL:Constant", typeAtom registeredOperatorAtom schema, identity constant]) := by
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
      have firstFound := registered first List.mem_cons_self
      by_cases same : nameAtom (constantName constant) = nameAtom (constantName first.1)
      · have constantEqual := registered_name_faithful context constant first.1 schema first.2 found firstFound same
        have schemaEqual : schema = first.2 := by
          rw [← constantEqual, found] at firstFound
          exact Option.some.inj firstFound
        simp [entryAtom, constantEqual, schemaEqual]
      · have remaining : (constant, schema) ∈ rest := by
          rcases List.mem_cons.mp member with equal | member
          · exact False.elim (same (congrArg (nameAtom ∘ constantName ∘ Prod.fst) equal))
          · exact member
        have restRegistered : ∀ entry ∈ rest, context.signature.constants entry.1 = some entry.2 :=
          fun entry member => registered entry (List.mem_cons_of_mem _ member)
        simpa [List.lookup, entryAtom, same, beq_eq_decide] using ih restRegistered remaining

/-- The encoded row contains the exact registered schema and identity payload. -/
theorem lookup_registered {context : TheoryContext} (table : Table context)
    (identity : Const → Atom) (constant : Const) (schema : Ty)
    (found : context.signature.constants constant = some schema) :
    (entriesAtom table identity).lookup (nameAtom (constantName constant)) =
      some (.expression [.symbol "HOL:Constant", typeAtom registeredOperatorAtom schema, identity constant]) :=
  lookup_registered_entries context table.constants table.registered identity constant schema found
    (table.complete constant schema found)

theorem lookup_unregistered_name {context : TheoryContext} (table : Table context)
    (identity : Const → Atom) (name : Atom)
    (absent : ∀ constant schema, context.signature.constants constant = some schema →
      name ≠ nameAtom (constantName constant)) :
    (entriesAtom table identity).lookup name = none := by
  have each : ∀ entry ∈ table.constants, name ≠ nameAtom (constantName entry.1) :=
    fun entry member => absent entry.1 entry.2 (table.registered entry member)
  unfold entriesAtom
  generalize table.constants = entries at each ⊢
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      have firstDifferent := each first List.mem_cons_self
      have remaining : ∀ entry ∈ rest, name ≠ nameAtom (constantName entry.1) :=
        fun entry member => each entry (List.mem_cons_of_mem _ member)
      simpa [List.lookup, entryAtom, firstDifferent, beq_eq_decide] using ih remaining

theorem fresh_name_absent {context : TheoryContext} (table : Table context)
    (identity : Const → Atom) (name : Name) (fresh : .constant name ∉ context.names) :
    (entriesAtom table identity).lookup (nameAtom name) = none := by
  apply lookup_unregistered_name table identity
  intro constant schema found same
  have names := TypeSubstitution.nameAtom_injective same
  exact fresh (names ▸ context.constantNames constant schema found)

/-- A declaration extension changes only the fresh declaration's payload. -/
def extendIdentity (before : Const → Atom) (constant : Const) (identity : Atom) : Const → Atom :=
  fun candidate => if Const.same candidate constant then identity else before candidate

theorem old_constant_identity_preserved (context : TheoryContext) (constant old : Const)
    (oldSchema : Ty) (before : Const → Atom) (identity : Atom)
    (fresh : .constant (constantName constant) ∉ context.names)
    (registered : context.signature.constants old = some oldSchema) :
    extendIdentity before constant identity old = before old := by
  have different : old ≠ constant := by
    intro same
    subst old
    exact fresh (context.constantNames constant oldSchema registered)
  simp [extendIdentity, Const.same_eq_true_iff, different]

/-- Exact old-language lookup, including its identity, survives admission of
a fresh declaration. This does not merely compare the names in two tables. -/
theorem old_lookup_preserved {context : TheoryContext} (table : Table context)
    (constant : Const) (schema : Ty) (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names)
    (before : Const → Atom) (identity : Atom) (old : Const) (oldSchema : Ty)
    (registered : context.signature.constants old = some oldSchema) :
    (entriesAtom (addConstant table constant schema formed fresh)
      (extendIdentity before constant identity)).lookup (nameAtom (constantName old)) =
    (entriesAtom table before).lookup (nameAtom (constantName old)) := by
  rw [lookup_registered (addConstant table constant schema formed fresh) _ old oldSchema
    ((context.addConstant_includes constant schema formed fresh).2 _ _ registered),
    lookup_registered table before old oldSchema registered,
    old_constant_identity_preserved context constant old oldSchema before identity fresh registered]

/-- A name collision cannot overwrite a registered definition's identity. -/
theorem same_name_forces_same_declaration {context : TheoryContext} (table : Table context)
    (left right : Const) (leftSchema rightSchema : Ty)
    (leftMember : (left, leftSchema) ∈ table.constants)
    (rightMember : (right, rightSchema) ∈ table.constants)
    (sameName : constantName left = constantName right) : left = right ∧ leftSchema = rightSchema := by
  have leftFound := table.registered (left, leftSchema) leftMember
  have rightFound := table.registered (right, rightSchema) rightMember
  have constantSame := context.uniqueConstantNames left right leftSchema rightSchema leftFound rightFound sameName
  refine ⟨constantSame, ?_⟩
  rw [← constantSame, leftFound] at rightFound
  exact Option.some.inj rightFound

def boolean : Table ContextControls.booleanContext :=
  addTypeOperator empty TypeOp.bool 0 (by simp [TheoryContext.empty])
def base : Table ContextControls.baseContext :=
  addTypeOperator boolean TypeOp.function 2 (by
    simp [ContextControls.booleanContext, TheoryContext.addTypeOperator, TheoryContext.empty,
      operatorName, TypeOp.bool, TypeOp.function, Name.global])
def core : Table ContextControls.coreContext :=
  addConstant base Const.equality (Ty.equality (.var ContextControls.equalityParameter))
    ContextControls.equality_schema_formed
    (by simp [ContextControls.baseContext, ContextControls.booleanContext,
      TheoryContext.addTypeOperator, TheoryContext.empty, constantName, Const.equality])
def individual : Table SourceProfile.individualContext :=
  addTypeOperator core SourceProfile.individualOperator 0
    (by simp [ContextControls.coreContext, ContextControls.baseContext,
      ContextControls.booleanContext, TheoryContext.addConstant, TheoryContext.addTypeOperator,
      TheoryContext.empty, operatorName, SourceProfile.individualOperator, TypeOp.bool,
      TypeOp.function, Name.global])
def primitive : Table SourceProfile.primitiveContext :=
  addConstant individual ModelInterpretation.selectionConstant
    (ModelInterpretation.selectionType (.var ContextControls.equalityParameter))
    SourceProfile.selection_schema_formed
    (by simp [SourceProfile.individualContext, ContextControls.coreContext,
      ContextControls.baseContext, ContextControls.booleanContext, TheoryContext.addConstant,
      TheoryContext.addTypeOperator, TheoryContext.empty, constantName,
      ModelInterpretation.selectionConstant, Const.equality, Name.global])

theorem primitive_operator_entries : primitive.operators.entries = OperatorTable.primitive.entries := rfl
theorem primitive_constant_entries : primitive.constants =
    [(ModelInterpretation.selectionConstant,
      ModelInterpretation.selectionType (.var ContextControls.equalityParameter)),
     (Const.equality, Ty.equality (.var ContextControls.equalityParameter))] := rfl

/-- Preserve the presentation order used by the actual source initialization. -/
def sourcePrimitive : Table SourceProfile.primitiveContext :=
  { operators := OperatorTable.reverse primitive.operators
    constants := primitive.constants.reverse
    registered := fun entry member => primitive.registered entry (List.mem_reverse.mp member)
    complete := fun constant schema found => List.mem_reverse.mpr (primitive.complete constant schema found) }

theorem source_primitive_operator_table :
    OperatorTable.tableAtom sourcePrimitive.operators (fun _ => .symbol "HOL:Primitive") =
      OperatorTable.tableAtom OperatorTable.sourcePrimitive (fun _ => .symbol "HOL:Primitive") := rfl

def primitiveIdentity (constant : Const) : Atom :=
  .expression [.symbol "HOL:Primitive", nameAtom (constantName constant)]

theorem source_primitive_constant_table : tableAtom sourcePrimitive primitiveIdentity =
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "="),
      .expression [.symbol "HOL:Constant",
        typeAtom registeredOperatorAtom (Ty.equality (.var ContextControls.equalityParameter)),
        .expression [.symbol "HOL:Primitive", .grounded (.string "=")]]],
      .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "@"),
        .expression [.symbol "HOL:Constant", typeAtom registeredOperatorAtom
          (ModelInterpretation.selectionType (.var ContextControls.equalityParameter)),
          .expression [.symbol "HOL:Primitive", .grounded (.string "@")]]], .symbol "HOL:Nil"]] := by
  simp [tableAtom, entriesAtom, sourcePrimitive, primitive_constant_entries,
    Lookup.table, entryAtom, primitiveIdentity, constantName,
    Const.equality, ModelInterpretation.selectionConstant, Premises.keys]

/-- The name field of the actual authored constant-identity constructors.
Unknown vocabulary has no interpretation in this projection. The complete
identity payload remains in the declaration table. -/
def identityName? : Atom → Option Atom
  | .expression [.symbol "HOL:Primitive", name] => some name
  | .expression [.symbol "HOL:Defined", name, _, _] => some name
  | .expression [.symbol "HOL:Abstraction", name, _, _] => some name
  | .expression [.symbol "HOL:Representation", name, _, _] => some name
  | _ => none

def Identifies (context : TheoryContext) (identity : Const → Atom) : Prop :=
  ∀ constant schema, context.signature.constants constant = some schema →
    identityName? (identity constant) = some (nameAtom (constantName constant))

theorem primitiveIdentity_identifies (context : TheoryContext) :
    Identifies context primitiveIdentity := by
  intro constant _ _
  rfl

theorem defined_identity_name (name schema body : Atom) :
    identityName? (.expression [.symbol "HOL:Defined", name, schema, body]) = some name := rfl

theorem abstraction_identity_name (name operator predicate : Atom) :
    identityName? (.expression [.symbol "HOL:Abstraction", name, operator, predicate]) = some name := rfl

theorem representation_identity_name (name operator predicate : Atom) :
    identityName? (.expression [.symbol "HOL:Representation", name, operator, predicate]) = some name := rfl

theorem unknown_identity_refused (payload : Atom) :
    identityName? (.expression [.symbol "HOL:Unknown", payload]) = none := rfl

/-- Name-preserving identity payloads cannot alias distinct registered
declarations. The conclusion uses the actual context's uniqueness law. -/
theorem registered_identity_injective (context : TheoryContext) (identity : Const → Atom)
    (identified : Identifies context identity) (left right : Const) (leftSchema rightSchema : Ty)
    (leftFound : context.signature.constants left = some leftSchema)
    (rightFound : context.signature.constants right = some rightSchema)
    (same : identity left = identity right) : left = right := by
  have names := congrArg identityName? same
  rw [identified left leftSchema leftFound, identified right rightSchema rightFound] at names
  exact context.uniqueConstantNames left right leftSchema rightSchema leftFound rightFound
    (TypeSubstitution.nameAtom_injective (Option.some.inj names))

/-- Admitting a fresh definition retains the projection for every old
identity and proves it for the new source constructor. -/
theorem extended_identity_identifies (context : TheoryContext) (before : Const → Atom)
    (identified : Identifies context before) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) (identity : Atom)
    (named : identityName? identity = some (nameAtom (constantName constant))) :
    Identifies (context.addConstant constant schema formed fresh) (extendIdentity before constant identity) := by
  intro candidate candidateSchema registered
  by_cases same : candidate = constant
  · subst candidate
    simpa [extendIdentity, Const.same_eq_true_iff] using named
  · have old : context.signature.constants candidate = some candidateSchema := by
      simpa [TheoryContext.addConstant, Signature.addConstant, Const.same_eq_true_iff, same] using registered
    rw [old_constant_identity_preserved context constant candidate candidateSchema before identity fresh old]
    exact identified candidate candidateSchema old

end Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable

import Mettapedia.Languages.HOLLight.MeTTa.Representation
import Mettapedia.Languages.HOLLight.SourceProfile

/-!
# Finite operator tables for registered HOL theory contexts

The authored program stores operator arities in a finite first-match table.
This module constructs that table from the empty registered context and
preserves its correspondence through the existing declaration extensions.
The primitive HOL Light context is an instance of the construction. Origins
remain payloads of their declaration rows; they do not authorize a declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.OperatorTable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open DefinitionAdapters
open Representation (registeredOperatorAtom)

/-- A finite presentation of the existing context's operator signature. Both
directions are retained: every row is registered, and no registration is lost. -/
structure Table (context : TheoryContext) where
  entries : List (TypeOp × Nat)
  registered : ∀ entry ∈ entries,
    context.signature.typeOperators entry.1 = some entry.2
  complete : ∀ operator arity,
    context.signature.typeOperators operator = some arity → (operator, arity) ∈ entries

def empty : Table TheoryContext.empty :=
  { entries := []
    registered := by simp
    complete := by simp [TheoryContext.empty] }

def addTypeOperator {context : TheoryContext} (before : Table context)
    (operator : TypeOp) (arity : Nat)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    Table (context.addTypeOperator operator arity fresh) :=
  { entries := (operator, arity) :: before.entries
    registered := by
      intro entry member
      rcases List.mem_cons.mp member with new | earlier
      · subst entry
        exact context.addTypeOperator_registered operator arity fresh
      · exact (context.addTypeOperator_includes operator arity fresh).1 _ _
          (before.registered entry earlier)
    complete := by
      intro candidate candidateArity found
      by_cases same : TypeOp.same candidate operator = true
      · have equal := (TypeOp.same_eq_true_iff candidate operator).mp same
        subst candidate
        have arityEqual : arity = candidateArity := by
          simpa [TheoryContext.addTypeOperator, Signature.addTypeOperator,
            TypeOp.same_eq_true_iff] using found
        subst candidateArity
        exact List.mem_cons_self
      · have old : context.signature.typeOperators candidate = some candidateArity := by
          simpa [TheoryContext.addTypeOperator, Signature.addTypeOperator, same] using found
        exact List.mem_cons_of_mem _ (before.complete candidate candidateArity old) }

def addConstant {context : TheoryContext} (before : Table context)
    (constant : Const) (schema : Ty) (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    Table (context.addConstant constant schema formed fresh) :=
  { entries := before.entries
    registered := before.registered
    complete := before.complete }

def entryAtom (origin : TypeOp → Atom) (entry : TypeOp × Nat) : Atom × Atom :=
  (registeredOperatorAtom entry.1,
    .expression [.symbol "HOL:TypeOperator", .grounded (.int entry.2), origin entry.1])

def entriesAtom {context : TheoryContext} (table : Table context) (origin : TypeOp → Atom) :
    List (Atom × Atom) := table.entries.map (entryAtom origin)

def tableAtom {context : TheoryContext} (table : Table context) (origin : TypeOp → Atom) : Atom :=
  Lookup.table (entriesAtom table origin)

/-- Reordering rows retains the same registration correspondence. The source
primitive table presents its declarations in their original insertion order. -/
def reverse {context : TheoryContext} (table : Table context) : Table context :=
  { entries := table.entries.reverse
    registered := fun entry member => table.registered entry (List.mem_reverse.mp member)
    complete := fun operator arity found => List.mem_reverse.mpr (table.complete operator arity found) }

theorem registered_name_faithful (context : TheoryContext) (left right : TypeOp)
    (leftArity rightArity : Nat)
    (leftFound : context.signature.typeOperators left = some leftArity)
    (rightFound : context.signature.typeOperators right = some rightArity)
    (same : registeredOperatorAtom left = registeredOperatorAtom right) : left = right := by
  have names := sourceOperatorName_injective (TypeSubstitution.nameAtom_injective same)
  exact context.uniqueTypeNames left right leftArity rightArity leftFound rightFound names

private theorem lookup_registered_entries (context : TheoryContext) (entries : List (TypeOp × Nat))
    (registered : ∀ entry ∈ entries, context.signature.typeOperators entry.1 = some entry.2)
    (origin : TypeOp → Atom) (operator : TypeOp) (arity : Nat)
    (found : context.signature.typeOperators operator = some arity)
    (member : (operator, arity) ∈ entries) :
    (entries.map (entryAtom origin)).lookup (registeredOperatorAtom operator) =
      some (.expression [.symbol "HOL:TypeOperator", .grounded (.int arity), origin operator]) := by
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
      have firstFound := registered first List.mem_cons_self
      by_cases same : registeredOperatorAtom operator = registeredOperatorAtom first.1
      · have operatorEqual := registered_name_faithful context operator first.1 arity first.2
          found firstFound same
        have arityEqual : arity = first.2 := by
          rw [← operatorEqual, found] at firstFound
          exact Option.some.inj firstFound
        simp [entryAtom, operatorEqual, arityEqual]
      · have remaining : (operator, arity) ∈ rest := by
          rcases List.mem_cons.mp member with equal | member
          · exact False.elim (same (congrArg (registeredOperatorAtom ∘ Prod.fst) equal))
          · exact member
        have restRegistered : ∀ entry ∈ rest,
            context.signature.typeOperators entry.1 = some entry.2 :=
          fun entry member => registered entry (List.mem_cons_of_mem _ member)
        simpa [List.lookup, entryAtom, same, beq_eq_decide] using ih restRegistered remaining

/-- Name lookup is faithful because the rows were constructed from the
registered context, whose unique-name invariant retains declaration identity. -/
theorem lookup_registered {context : TheoryContext} (table : Table context)
    (origin : TypeOp → Atom) (operator : TypeOp) (arity : Nat)
    (found : context.signature.typeOperators operator = some arity) :
    (entriesAtom table origin).lookup (registeredOperatorAtom operator) =
      some (.expression [.symbol "HOL:TypeOperator", .grounded (.int arity), origin operator]) :=
  lookup_registered_entries context table.entries table.registered origin operator arity found
    (table.complete operator arity found)

/-- A name that belongs to no registered operator has no table entry. -/
theorem lookup_unregistered_name {context : TheoryContext} (table : Table context)
    (origin : TypeOp → Atom) (name : Atom)
    (absent : ∀ operator arity, context.signature.typeOperators operator = some arity →
      name ≠ registeredOperatorAtom operator) :
    (entriesAtom table origin).lookup name = none := by
  have each : ∀ entry ∈ table.entries, name ≠ registeredOperatorAtom entry.1 :=
    fun entry member => absent entry.1 entry.2 (table.registered entry member)
  unfold entriesAtom
  generalize table.entries = entries at each ⊢
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      have firstDifferent := each first List.mem_cons_self
      have remaining : ∀ entry ∈ rest, name ≠ registeredOperatorAtom entry.1 :=
        fun entry member => each entry (List.mem_cons_of_mem _ member)
      simpa [List.lookup, entryAtom, firstDifferent, beq_eq_decide] using ih remaining

theorem fresh_name_absent {context : TheoryContext} (table : Table context)
    (origin : TypeOp → Atom) (operator : TypeOp)
    (fresh : .typeOperator (operatorName operator) ∉ context.names) :
    (entriesAtom table origin).lookup (registeredOperatorAtom operator) = none := by
  apply lookup_unregistered_name table origin
  intro candidate arity found same
  have names := DefinitionAdapters.sourceOperatorName_injective
    (TypeSubstitution.nameAtom_injective same)
  exact fresh (names ▸ context.typeNames candidate arity found)

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

theorem primitive_entries : primitive.entries =
    [(SourceProfile.individualOperator, 0), (TypeOp.function, 2), (TypeOp.bool, 0)] := rfl

def sourcePrimitive : Table SourceProfile.primitiveContext := reverse primitive

theorem source_primitive_table : tableAtom sourcePrimitive (fun _ => .symbol "HOL:Primitive") =
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "bool"),
      .expression [.symbol "HOL:TypeOperator", .grounded (.int 0), .symbol "HOL:Primitive"]],
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "fun"),
      .expression [.symbol "HOL:TypeOperator", .grounded (.int 2), .symbol "HOL:Primitive"]],
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .grounded (.string "ind"),
      .expression [.symbol "HOL:TypeOperator", .grounded (.int 0), .symbol "HOL:Primitive"]],
      .symbol "HOL:Nil"]]] := by
  decide

theorem primitive_function_lookup (origin : TypeOp → Atom) :
    (entriesAtom primitive origin).lookup (.grounded (.string "fun")) =
      some (.expression [.symbol "HOL:TypeOperator", .grounded (.int 2), origin TypeOp.function]) := by
  apply lookup_registered primitive origin TypeOp.function 2
  exact SourceProfile.individual_includes.1 _ _
    (SourceProfile.core_includes_individual.1 _ _
      (ContextControls.core_includes.1 _ _ ContextControls.function_registered))

end Mettapedia.Languages.HOLLight.MeTTa.OperatorTable

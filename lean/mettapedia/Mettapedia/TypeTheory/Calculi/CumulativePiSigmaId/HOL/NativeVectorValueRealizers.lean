import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateFormation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedElimination
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotatedAppend

/-!
# Saturated Vec formation and constructor realizers

The original declared signatures supply source formation and typing. Their
selected HOL family predicate supplies membership. A saturated Vec type is
formed without asserting that the unapplied type former is a value of a
represented universe. Constructor inputs retain actual membership evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorValueRealizers
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
  (operations : NativeVectorComputationRows.Operations Base Const)
  {lex : LexicalReading Tower.Head Base Const}
  (compatible : LexicalMap (NativeVectorComputationRows.GuardedFamily.lexical operations) lex (fun head => head))
  (profile : Programs.ComputationProfiles.Selection) {Γ : HOL.Ctx Base}
  (context : GuardedContext (Programs.Annotated.church profile) lex Γ)
  (roots : List (HOL.ClosedFormula Const))

include compatible

theorem naturalRead : Reads lex (Γ := Γ) (.const natName) (HOL.PredicateProducts.full operations.number) := by
  let empty : HOL.Subst Const [] Γ := fun index => nomatch index
  have raised : HOL.weakenCtx Γ (HOL.PredicateProducts.full operations.number : HOL.ClosedTerm Const _) =
      HOL.PredicateProducts.full operations.number :=
    (HOL.subst_weakenCtx empty _).symm.trans (HOL.PredicateProducts.subst_full empty _)
  rw [← raised]
  apply Reads.constant
  apply compatible.constants
  simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
    natName, vecName]

theorem zeroRead : Reads lex (Γ := Γ) (.const zeroName) (HOL.weakenCtx Γ operations.zero) := by
  apply Reads.constant
  apply compatible.constants
  simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
    zeroName, natName, vecName]

theorem successorRead : Reads lex (Γ := Γ) (.const succName) (HOL.weakenCtx Γ operations.successor) := by
  apply Reads.constant
  apply compatible.constants
  simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
    succName, zeroName, natName, vecName]

theorem nilRead : Reads lex (Γ := Γ) (.const vnilName) (HOL.weakenCtx Γ operations.nilCode) := by
  apply Reads.constant
  apply compatible.constants
  simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
    vnilName, succName, zeroName, natName, vecName]

theorem consRead : Reads lex (Γ := Γ) (.const vconsName) (HOL.weakenCtx Γ operations.consCode) := by
  apply Reads.constant
  apply compatible.constants
  simp [NativeVectorComputationRows.GuardedFamily.lexical, NativeVectorComputationRows.Operations.lexicalReading,
    vconsName, vnilName, succName, zeroName, natName, vecName]

theorem familyRead : Reads lex (Γ := Γ) (.const vecName) (NativeVectorComputationRows.GuardedFamily.familyCode operations) := by
  simpa only [CTm.mapHead_id] using
    (NativeVectorComputationRows.GuardedFamily.family_reads (Γ := Γ) operations).mapLexical compatible

theorem eliminatorRead : Reads lex (Γ := Γ) (.const vecEliminateName) operations.eliminator := by
  have guarded := (operations.eliminator_reads Γ).mapLexical
    (NativeVectorComputationRows.GuardedFamily.extends_computation operations)
  simpa only [CTm.mapHead_id] using guarded.mapLexical compatible

def naturalFormation : GuardedTypeFormation context (.const natName) operations.number where
  formed := ⟨.sort Tower.zero, .sort _, Programs.Annotated.Functions.natural_typed profile⟩
  predicate := HOL.PredicateProducts.full operations.number
  reading := naturalRead operations compatible

def zero : GuardedRealizer roots context (.const zeroName) (.const natName) operations.number where
  typed := Programs.Annotated.Functions.zero_typed profile
  term := HOL.weakenCtx Γ operations.zero
  predicate := HOL.PredicateProducts.full operations.number
  termRead := zeroRead operations compatible
  typeRead := naturalRead operations compatible
  member := .impE (.eqPropER (.beta (HOL.weakenCtx Γ operations.zero) .top)) .topI

def successor {source : CTm Tower.Head Γ.length}
    (value : GuardedRealizer roots context source (.const natName) operations.number) :
    GuardedRealizer roots context (Programs.Annotated.Functions.successor source) (.const natName) operations.number where
  typed := Programs.Annotated.Functions.successor_typed profile value.typed
  term := .app (HOL.weakenCtx Γ operations.successor) value.term
  predicate := HOL.PredicateProducts.full operations.number
  termRead := .application (successorRead operations compatible) value.termRead
  typeRead := naturalRead operations compatible
  member := .impE (.eqPropER (.beta (.app (HOL.weakenCtx Γ operations.successor) value.term) .top)) .topI

def vectorFormation {A n : CTm Tower.Head Γ.length}
    (element : GuardedTypeFormation context A operations.element)
    (elementTyped : CTyped (Programs.Annotated.church profile) context.source A Programs.Annotated.Append.elementSort)
    (index : GuardedRealizer roots context n (.const natName) operations.number) :
    GuardedTypeFormation context (Programs.Annotated.Append.vector A n) operations.vector where
  formed := ⟨.sort (.param 0), .sort _, Programs.Annotated.Append.vector_typed profile elementTyped index.typed⟩
  predicate := .app (.app (NativeVectorComputationRows.GuardedFamily.familyCode operations) element.predicate) index.term
  reading := .application (.application (familyRead operations compatible) element.reading) index.termRead

def nil {A : CTm Tower.Head Γ.length} (element : GuardedTypeFormation context A operations.element)
    (elementTyped : CTyped (Programs.Annotated.church profile) context.source A Programs.Annotated.Append.elementSort) :
    GuardedRealizer roots context (Programs.Annotated.Append.nil A)
      (Programs.Annotated.Append.vector A (.const zeroName)) operations.vector where
  typed := Programs.Annotated.Append.nil_typed profile elementTyped
  term := .app (HOL.weakenCtx Γ operations.nilCode) element.predicate
  predicate := .app (.app (NativeVectorComputationRows.GuardedFamily.familyCode operations) element.predicate)
    (HOL.weakenCtx Γ operations.zero)
  termRead := .application (nilRead operations compatible) element.reading
  typeRead := .application (.application (familyRead operations compatible) element.reading) (zeroRead operations compatible)
  member := NativeVectorComputationRows.GuardedFamily.nil_member operations element.predicate

def cons [DecidableEq Base] {A n h t : CTm Tower.Head Γ.length}
    (element : GuardedTypeFormation context A operations.element)
    (elementTyped : CTyped (Programs.Annotated.church profile) context.source A Programs.Annotated.Append.elementSort)
    (index : GuardedRealizer roots context n (.const natName) operations.number)
    (head : GuardedRealizer roots context h A operations.element)
    (tail : GuardedRealizer roots context t (Programs.Annotated.Append.vector A n) operations.vector) :
    GuardedRealizer roots context (Programs.Annotated.Append.cons A n h t)
      (Programs.Annotated.Append.vector A (Programs.Annotated.Functions.successor n)) operations.vector := by
  have headSame := Reader.term_unique head.typeRead element.reading
  have tailSame := Reader.term_unique tail.typeRead
    (vectorFormation operations compatible profile context roots element elementTyped index).reading
  have headMember := HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate head.term) headSame) head.member
  have tailMember := HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate tail.term) tailSame) tail.member
  exact ⟨Programs.Annotated.Append.cons_typed profile elementTyped index.typed head.typed tail.typed,
    NativeVectorComputationRows.GuardedFamily.sourceCons operations element.predicate index.term head.term tail.term,
    .app (.app (NativeVectorComputationRows.GuardedFamily.familyCode operations) element.predicate)
      (.app (HOL.weakenCtx Γ operations.successor) index.term),
    .application (.application (.application (.application (consRead operations compatible) element.reading)
      index.termRead) head.termRead) tail.termRead,
    .application (.application (familyRead operations compatible) element.reading)
      (.application (successorRead operations compatible) index.termRead),
    NativeVectorComputationRows.GuardedFamily.cons_member operations element.predicate index.term head.term tail.term
      headMember tailMember⟩

theorem zero_free : (zero operations compatible profile context roots).Free := by
  simp [zero, GuardedRealizer.Free, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem successor_free {source : CTm Tower.Head Γ.length}
    (value : GuardedRealizer roots context source (.const natName) operations.number) :
    (successor operations compatible profile context roots value).Free := by
  simp [successor, GuardedRealizer.Free, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem nil_free {A : CTm Tower.Head Γ.length} (element : GuardedTypeFormation context A operations.element)
    (elementTyped : CTyped (Programs.Annotated.church profile) context.source A Programs.Annotated.Append.elementSort) :
    (nil operations compatible profile context roots element elementTyped).Free :=
  NativeVectorComputationRows.GuardedFamily.nil_member_free operations element.predicate

theorem cons_free [DecidableEq Base] {A n h t : CTm Tower.Head Γ.length}
    (element : GuardedTypeFormation context A operations.element)
    (elementTyped : CTyped (Programs.Annotated.church profile) context.source A Programs.Annotated.Append.elementSort)
    (index : GuardedRealizer roots context n (.const natName) operations.number)
    (head : GuardedRealizer roots context h A operations.element)
    (tail : GuardedRealizer roots context t (Programs.Annotated.Append.vector A n) operations.vector)
    (headFree : head.Free) (tailFree : tail.Free) :
    (cons operations compatible profile context roots element elementTyped index head tail).Free := by
  unfold GuardedRealizer.Free cons
  apply NativeVectorComputationRows.GuardedFamily.cons_member_free
  · simpa only [GuardedRealizer.Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using headFree
  · simpa only [GuardedRealizer.Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using tailFree

#print axioms vectorFormation
#print axioms nil
#print axioms cons
#print axioms cons_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorValueRealizers

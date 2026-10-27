import Mettapedia.Languages.HOLLight.IndexedConstructorGuardSource
import Mettapedia.Languages.HOLLight.SourceNaturalOrder
import Mettapedia.Logic.HOL.VectorContainerPositionPrograms
import Mettapedia.Logic.HOL.GeneratedFamilyPredicate

/-!
# Source guards for the registered Vector container

The constructor carries its recursive-vector length. Its slot bound uses the
successor-closure order whose source-model interpretation is proved from the
checked Peano facts. The unindexed outer family's index is represented by the
Boolean true value. Six source definitions expose the shared constructor/root
programs and the data-dependent position/edge programs.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.VectorContainerGuardSource
open Mettapedia.Logic Mettapedia.Languages.OpenTheory

def payload (operations : RecursiveSpaceSourceReadback.Operations) : Ty :=
  RecursiveSpaceTypeInstantiation.constructorPayload [[operations.number]]

def instanceOperations (operations : RecursiveSpaceSourceReadback.Operations) :=
  RecursiveSpaceTypeInstantiation.Operations.instantiate operations
    (RecursiveSpaceTypeInstantiation.effectiveTypes [(Name.global "A", payload operations)])

def constructors (operations : RecursiveSpaceSourceReadback.Operations) :=
  HOL.VectorContainerPositionPrograms.constructors operations.number.toHOL
    (IndexedConstructorGuardSource.numeral operations.natural.zero operations.natural.successor)

def positions (operations : RecursiveSpaceSourceReadback.Operations) :=
  HOL.VectorContainerPositionPrograms.positions operations.number.toHOL
    (IndexedConstructorGuardSource.numeral operations.natural.zero operations.natural.successor)
    (HOL.SuccessorOrder.less operations.natural.successor)

def constructor (operations : RecursiveSpaceSourceReadback.Operations) :=
  RecursiveSpaceTypeInstantiation.constructorAt operations
    (HOL.FiniteConstructorEncoding.payloadType (constructors operations).fields)
    (instanceOperations operations).space

def bottom (operations : RecursiveSpaceSourceReadback.Operations) :=
  (instanceOperations operations).recursive.bottom

def signature (operations : RecursiveSpaceSourceReadback.Operations) :=
  (positions operations).signature (bottom operations) (constructor operations)

/-- The recursive operations at the exact payload type of the generated guards. -/
def recursiveSignature (operations : RecursiveSpaceSourceReadback.Operations) :
    RecursiveSpaceModelComparison.Signature :=
  ⟨operations.number.toHOL, HOL.FiniteConstructorEncoding.payloadType [[operations.number.toHOL]],
    (instanceOperations operations).space.toHOL, bottom operations, constructor operations⟩

/-- Compatibility is syntactic: the type instance preserves numbers and uses
exactly the generated payload. No semantic or membership law is assumed. -/
structure Compatible (operations : RecursiveSpaceSourceReadback.Operations) : Type where
  number : (instanceOperations operations).number = operations.number
  payload : (instanceOperations operations).payload = VectorContainerGuardSource.payload operations

def compatible? (operations : RecursiveSpaceSourceReadback.Operations) : Option (Compatible operations) :=
  if number : Ty.same (instanceOperations operations).number operations.number = true then
    if payload : Ty.same (instanceOperations operations).payload (VectorContainerGuardSource.payload operations) = true then
      some ⟨(Ty.same_eq_true_iff _ _).mp number, (Ty.same_eq_true_iff _ _).mp payload⟩
    else none
  else none

private theorem constant_retype (symbol : Const) {first second : Ty}
    {left right : HOL.Ty AtomicTy} (leftTyped : first.toHOL = left) (rightTyped : second.toHOL = right)
    (same : first = second) :
    HEq (HOL.Term.const (.constant symbol first leftTyped) : HOL.ClosedTerm Symbol left)
      (HOL.Term.const (.constant symbol second rightTyped) : HOL.ClosedTerm Symbol right) := by
  cases same
  cases leftTyped
  cases rightTyped
  rfl

theorem instanceSignature_eq (operations : RecursiveSpaceSourceReadback.Operations)
    (compatible : Compatible operations) :
    (instanceOperations operations).recursive = recursiveSignature operations := by
  unfold RecursiveSpaceSourceReadback.Operations.recursive recursiveSignature bottom constructor
  congr 1
  · exact congrArg Ty.toHOL compatible.number
  · exact (congrArg Ty.toHOL compatible.payload).trans
      (RecursiveSpaceTypeInstantiation.constructorPayload_toHOL [[operations.number]])
  · apply constant_retype
    simp only [compatible.number, compatible.payload, payload,
      RecursiveSpaceTypeInstantiation.constructorPayload, List.map_cons, List.map_nil,
      constructors, HOL.VectorContainerPositionPrograms.constructors]

theorem instanceNatural_eq (operations : RecursiveSpaceSourceReadback.Operations)
    (compatible : Compatible operations) :
    (instanceOperations operations).natural = operations.natural := by
  change ({ operations with number := (instanceOperations operations).number } :
    RecursiveSpaceSourceReadback.Operations).natural = operations.natural
  rw [compatible.number]

#print axioms instanceSignature_eq


def definitions (operations : RecursiveSpaceSourceReadback.Operations) : List (Name × SourceTerm) :=
  let data := constructors operations
  let positions := positions operations
  [(Name.global "registeredVectorShape", IndexedConstructorDefinitions.source data.shapeProgram),
   (Name.global "registeredVectorActive", IndexedConstructorDefinitions.source positions.activeProgram),
   (Name.global "registeredVectorResult", IndexedConstructorDefinitions.source data.resultProgram),
   (Name.global "registeredVectorChild", IndexedConstructorDefinitions.source positions.childProgram),
   (Name.global "registeredVectorRoot", IndexedConstructorDefinitions.source (data.rootProgram (constructor operations))),
   (Name.global "registeredVectorEdge", IndexedConstructorDefinitions.source (positions.edgeProgram (constructor operations)))]

end Mettapedia.Languages.HOLLight.VectorContainerGuardSource

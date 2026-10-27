import Mettapedia.Logic.HOL.IndexedConstructorGuardPrograms
import Mettapedia.Logic.HOL.IndexedConstructorGuardCompilation
import Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions
import Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation

/-!
# Source programs for the Vector constructor guards

The executable inventory uses the original zero and successor operations,
the original element type and the two constructor field lists. Its index
programs agree with the generic descriptor compiler. The six guard programs
are translated to checked named source terms for ordinary constant admission.
The recursive-space constructor is instantiated at this exact payload type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedConstructorGuardSource

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL.FiniteConstructorEncoding HOL.CurriedPredicates
open Mettapedia.GSLT.LanguageDef
open IndexedInductiveNatVec IndexedInductiveHOLTerms
local infixr:60 " ⇒ " => HOL.Ty.arr

def fields (number element : HOL.Ty AtomicTy) := [[], [number, element]]

def numeral {number : HOL.Ty AtomicTy} (zero : HOL.ClosedTerm Symbol number)
    (successor : HOL.ClosedTerm Symbol (number ⇒ number)) : Nat → HOL.ClosedTerm Symbol number
  | 0 => zero
  | n + 1 => .app successor (numeral zero successor n)

def result (number element : HOL.Ty AtomicTy) (zero : HOL.ClosedTerm Symbol number)
    (successor : HOL.ClosedTerm Symbol (number ⇒ number)) :
    (occurrence : Fin (fields number element).length) →
      HOL.ClosedTerm Symbol (FunctionType ((fields number element).get occurrence) number)
  | ⟨0, _⟩ => zero
  | ⟨1, _⟩ => IndexedConstructorDefinitions.vectorResultBody number element successor
  | ⟨n + 2, bound⟩ => False.elim (by change n + 2 < 2 at bound; omega)

def childCount (number element : HOL.Ty AtomicTy) (occurrence : Fin (fields number element).length) : Nat :=
  if occurrence.val = 0 then 0 else 1

def child (number element : HOL.Ty AtomicTy) :
    (occurrence : Fin (fields number element).length) → Fin (childCount number element occurrence) →
      HOL.ClosedTerm Symbol (FunctionType ((fields number element).get occurrence) number)
  | ⟨0, _⟩, position => Fin.elim0 position
  | ⟨1, _⟩, _ => IndexedConstructorDefinitions.vectorChildBody number element
  | ⟨n + 2, bound⟩, _ => False.elim (by change n + 2 < 2 at bound; omega)

def inventory (number element : HOL.Ty AtomicTy) (zero : HOL.ClosedTerm Symbol number)
    (successor : HOL.ClosedTerm Symbol (number ⇒ number)) : HOL.IndexedConstructorGuards.Inventory Symbol [] where
  fields := fields number element
  number := number
  index := number
  numeral := numeral zero successor
  allowed := fun occurrence => HOL.CurriedPredicates.constant ((fields number element).get occurrence) .top
  result := result number element zero successor
  childCount := childCount number element
  child := child number element

set_option backward.isDefEq.respectTransparency false in
theorem inventory_generated (arithmetic : Arithmetic Symbol) (A : Type) :
    inventory arithmetic.number arithmetic.element arithmetic.zero arithmetic.successor =
      HOL.IndexedConstructorGuardCompilation.inventory (arithmetic.reading A) (Vectors.constructors A)
        arithmetic.number (numeral arithmetic.zero arithmetic.successor)
        (fun _ => HOL.CurriedPredicates.constant _ .top) := by
  unfold inventory HOL.IndexedConstructorGuardCompilation.inventory
  congr 1
  · congr 1
    funext occurrence
    fin_cases occurrence
    · simp [result, HOL.IndexedConstructorGuardCompilation.result,
        HOL.IndexedConstructorGuardCompilation.codeAt, HOL.IndexedConstructorGuardCompilation.sourceOccurrence,
        Arithmetic.reading, Vectors.constructors, Vectors.nilCode,
        HOL.IndexedConstructorTerms.Reading.resultProgram]
      rw [Arithmetic.term]
      exact (HOL.weakenCtx_nil _).symm
    · change IndexedConstructorDefinitions.vectorResultBody _ _ _ = arithmetic.resultProgram A
      exact IndexedConstructorDefinitions.vectorResultBody_generated arithmetic A
  · funext occurrence
    fin_cases occurrence <;> rfl
  · apply Function.hfunext rfl
    intro occurrence other same
    cases eq_of_heq same
    fin_cases occurrence
    · apply heq_of_eq
      funext position
      exact Fin.elim0 position
    · apply heq_of_eq
      funext position
      have same : position = ⟨0, by change 0 < 1; decide⟩ := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      subst position
      change IndexedConstructorDefinitions.vectorChildBody _ _ = arithmetic.childProgram A
      exact IndexedConstructorDefinitions.vectorChildBody_generated arithmetic A

def fromSource (operations : RecursiveSpaceSourceReadback.Operations) :=
  inventory operations.number.toHOL operations.payload.toHOL operations.natural.zero operations.natural.successor

def payload (operations : RecursiveSpaceSourceReadback.Operations) : Ty :=
  RecursiveSpaceTypeInstantiation.constructorPayload [[], [operations.number, operations.payload]]

def instanceOperations (operations : RecursiveSpaceSourceReadback.Operations) :=
  RecursiveSpaceTypeInstantiation.Operations.instantiate operations
    (RecursiveSpaceTypeInstantiation.effectiveTypes [(Name.global "A", payload operations)])

def constructor (operations : RecursiveSpaceSourceReadback.Operations) :
    HOL.ClosedTerm Symbol (operations.number.toHOL ⇒ payloadType (fromSource operations).fields ⇒
      (operations.number.toHOL ⇒ (instanceOperations operations).space.toHOL) ⇒
      (instanceOperations operations).space.toHOL) :=
  RecursiveSpaceTypeInstantiation.constructorAt operations
    (payloadType (fromSource operations).fields) (instanceOperations operations).space

def definitions (operations : RecursiveSpaceSourceReadback.Operations) : List (Name × SourceTerm) :=
  let table := fromSource operations
  [(Name.global "indexedVectorShape", IndexedConstructorDefinitions.source table.toConstructorPrograms.shapeProgram),
   (Name.global "indexedVectorActive", IndexedConstructorDefinitions.source table.activeProgram),
   (Name.global "indexedVectorResult", IndexedConstructorDefinitions.source table.toConstructorPrograms.resultProgram),
   (Name.global "indexedVectorChild", IndexedConstructorDefinitions.source table.childProgram),
   (Name.global "indexedVectorRoot", IndexedConstructorDefinitions.source (table.toConstructorPrograms.rootProgram (constructor operations))),
   (Name.global "indexedVectorEdge", IndexedConstructorDefinitions.source (table.edgeProgram (constructor operations)))]

#print axioms inventory_generated

end Mettapedia.Languages.HOLLight.IndexedConstructorGuardSource

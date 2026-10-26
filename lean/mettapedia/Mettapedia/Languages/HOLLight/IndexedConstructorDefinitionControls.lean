import Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

/-!
# Source-admission controls for constructor-index definitions

The child-index projection is closed and declares in the primitive core. A
result-index function with an unbound successor input is refused there.
The complete source-history qualification supplies the actual declared SUC.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions.Controls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
open ProofExecution DefinitionAdapters
local infixr:60 " ⇒ " => HOL.Ty.arr
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def number : HOL.Ty AtomicTy :=
  .base ⟨Ty.var (Name.global "ConstructorIndexNumber"), rfl, rfl⟩
def element : HOL.Ty AtomicTy :=
  .base ⟨Ty.var (Name.global "ConstructorIndexElement"), rfl, rfl⟩

def input (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.variable ⟨Name.global name, Ty.fromHOL type⟩ (by simp))

def arithmetic : Arithmetic Symbol :=
  ⟨number, element, input "indexZero" number,
    input "indexSuccessor" (number ⇒ number),
    input "indexAddition" (number ⇒ number ⇒ number)⟩

theorem result_source_agreement :
    vectorResultSource number element arithmetic.successor = source (arithmetic.resultProgram Bool) :=
  vectorResultSource_generated arithmetic Bool

theorem child_source_agreement :
    vectorChildSource number element = source (arithmetic.childProgram Bool) :=
  vectorChildSource_generated arithmetic Bool

def before : Registered.State := Registered.empty ContextControls.coreContext
def childDefinition : Option Registered.State :=
  define? emptyAxiomPolicy before ("child-index-definition", 0)
    (Name.global "childIndexProjection") (vectorChildSource number element)

theorem child_admitted : childDefinition.isSome = true := by decide +kernel

def freeSuccessorDefinition : Option Registered.State :=
  define? emptyAxiomPolicy before ("unbound-index-definition", 0)
    (Name.global "unboundResultIndex") (vectorResultSource number element arithmetic.successor)

theorem unbound_successor_refused : freeSuccessorDefinition.isNone = true := by decide +kernel

def verdicts : List (String × Bool) :=
  [("constructor child-index projection declares", childDefinition.isSome),
   ("constructor result-index unbound successor refused", freeSuccessorDefinition.isNone)]

theorem verdicts_all : ∀ verdict ∈ verdicts, verdict.2 = true := by
  intro verdict present
  simp only [verdicts, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact child_admitted
  · exact unbound_successor_refused

#print axioms result_source_agreement
#print axioms child_source_agreement
#print axioms child_admitted
#print axioms unbound_successor_refused

end Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions.Controls

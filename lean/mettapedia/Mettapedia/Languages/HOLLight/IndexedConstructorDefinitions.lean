import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Languages.HOLLight.ExportReplay

/-!
# Source definitions for constructor-index programs

Typed HOL programs are converted to checked named source syntax. The Vector
result and child functions have executable bodies equal to the specialization
of the generic telescope compiler, whose source semantic interface is
noncomputable. Declaration admission uses the existing registered receiver.
These definitions concern index functions, not a complete native datatype.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
open ReverseTranslation ProofExecution
local infixr:60 " ⇒ " => HOL.Ty.arr

def source {type : HOL.Ty AtomicTy} (program : HOL.ClosedTerm Symbol type) : SourceTerm :=
  (PrimitiveTransport.checkedSource
    (reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand program))).source

def vectorResultBody (number element : HOL.Ty AtomicTy)
    (successor : HOL.ClosedTerm Symbol (number ⇒ number)) :
    HOL.ClosedTerm Symbol (number ⇒ element ⇒ number) :=
  .lam (.lam (.app (HOL.weakenCtx _ successor) (.var (.vs .vz))))

def vectorChildBody (number element : HOL.Ty AtomicTy) :
    HOL.ClosedTerm Symbol (number ⇒ element ⇒ number) :=
  .lam (.lam (.var (.vs .vz)))

theorem vectorResultBody_generated (arithmetic : Arithmetic Symbol) (A : Type) :
    vectorResultBody arithmetic.number arithmetic.element arithmetic.successor =
      arithmetic.resultProgram A := (arithmetic.resultProgram_body A).symm

theorem vectorChildBody_generated (arithmetic : Arithmetic Symbol) (A : Type) :
    vectorChildBody arithmetic.number arithmetic.element = arithmetic.childProgram A :=
  (arithmetic.childProgram_body A).symm

def vectorResultSource (number element : HOL.Ty AtomicTy)
    (successor : HOL.ClosedTerm Symbol (number ⇒ number)) : SourceTerm :=
  source (vectorResultBody number element successor)

def vectorChildSource (number element : HOL.Ty AtomicTy) : SourceTerm :=
  source (vectorChildBody number element)

theorem vectorResultSource_generated (arithmetic : Arithmetic Symbol) (A : Type) :
    vectorResultSource arithmetic.number arithmetic.element arithmetic.successor =
      source (arithmetic.resultProgram A) :=
  congrArg source (vectorResultBody_generated arithmetic A)

theorem vectorChildSource_generated (arithmetic : Arithmetic Symbol) (A : Type) :
    vectorChildSource arithmetic.number arithmetic.element = source (arithmetic.childProgram A) :=
  congrArg source (vectorChildBody_generated arithmetic A)

/-- Instances are selected from the current declaration context for each body. -/
def command (state : Registered.State) (origin : Origin) (name : Name) (body : SourceTerm) :
    Registered.Command :=
  .constant origin name body (ExportReplay.instanceCertificates state.context.signature)

def define? (policy : AxiomPolicy) [DecidablePred policy] (state : Registered.State)
    (origin : Origin) (name : Name) (body : SourceTerm) : Option Registered.State :=
  Registered.apply policy state (command state origin name body)

#print axioms vectorResultSource_generated
#print axioms vectorChildSource_generated

end Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.OpenTheory.ReverseTranslation
import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Logic.HOL.RecursiveSpacePredicate

/-!
# Source definitions for constructor-index programs

Typed HOL programs are converted to checked named source syntax. The Vector
result and child functions have executable bodies equal to the specialization
of the generic telescope compiler, whose source semantic interface is
noncomputable. Declaration admission uses the existing registered receiver.
These definitions concern index functions, not a complete native datatype.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms
open ReverseTranslation ProofExecution
local infixr:60 " ⇒ " => HOL.Ty.arr
universe w

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

/-! ## Installed guard meanings -/

structure GuardIndices where
  shape : Nat
  active : Nat
  edge : Nat

/-- Exact cached defining equations, not assumed semantic guard laws. -/
structure GuardReadings (state : Registered.State) (signature : HOL.RecursiveSpacePredicate.Signature Symbol)
    (shape : HOL.ClosedTerm Symbol (signature.number ⇒ signature.payload ⇒ .prop))
    (active : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ .prop))
    (edge : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop)) where
  shapeEquation : ExactFormulaReadback.ReadMeaning state
    (.eq shape (HOL.ImpredicativeConnectives.expand signature.validShape))
  activeEquation : ExactFormulaReadback.ReadMeaning state
    (.eq active (HOL.ImpredicativeConnectives.expand signature.active))
  edgeEquation : ExactFormulaReadback.ReadMeaning state
    (.eq edge (HOL.ImpredicativeConnectives.expand signature.validEdge))

def readGuards? (state : Registered.State) (indices : GuardIndices)
    (signature : HOL.RecursiveSpacePredicate.Signature Symbol)
    (shape : HOL.ClosedTerm Symbol (signature.number ⇒ signature.payload ⇒ .prop))
    (active : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ .prop))
    (edge : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop)) :
    Option (GuardReadings state signature shape active edge) := do
  let shapeEquation ← ExactFormulaReadback.readEquation? state indices.shape shape signature.validShape
  let activeEquation ← ExactFormulaReadback.readEquation? state indices.active active signature.active
  let edgeEquation ← ExactFormulaReadback.readEquation? state indices.edge edge signature.validEdge
  return ⟨shapeEquation, activeEquation, edgeEquation⟩

theorem GuardReadings.operator_denote {initial : DefinitionAdapters.TheoryContext} {policy : AxiomPolicy}
    {state : Registered.State} (frame : RegisteredReplayModels.Frame.{w} initial policy state.context state.cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    {signature : HOL.RecursiveSpacePredicate.Signature Symbol}
    {shape : HOL.ClosedTerm Symbol (signature.number ⇒ signature.payload ⇒ .prop)}
    {active : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ .prop)}
    {edge : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop)}
    (readings : GuardReadings state signature shape active edge) :
    HOL.RecursiveSpacePredicate.Signature.denotes (frame.model other assignment)
      (signature.withGuards shape active edge).operator =
      HOL.RecursiveSpacePredicate.Signature.denotes (frame.model other assignment) signature.operator :=
  signature.withGuards_operator_denote (frame.model other assignment) (frame.model_fullDomains other assignment)
    shape active edge
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment shape signature.validShape readings.shapeEquation)
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment active signature.active readings.activeEquation)
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment edge signature.validEdge readings.edgeEquation)

theorem GuardReadings.least_denote {initial : DefinitionAdapters.TheoryContext} {policy : AxiomPolicy}
    {state : Registered.State} (frame : RegisteredReplayModels.Frame.{w} initial policy state.context state.cache)
    (other : TypeFamilySemantics.OperatorFamilies.{w}) (assignment : TypeFamilySemantics.Assignment.{w})
    {signature : HOL.RecursiveSpacePredicate.Signature Symbol}
    {shape : HOL.ClosedTerm Symbol (signature.number ⇒ signature.payload ⇒ .prop)}
    {active : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ .prop)}
    {edge : HOL.ClosedTerm Symbol (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop)}
    (readings : GuardReadings state signature shape active edge) :
    HOL.RecursiveSpacePredicate.Signature.denotes (frame.model other assignment)
      (HOL.PredicateFixedPoint.least (signature.withGuards shape active edge).operator) =
      HOL.RecursiveSpacePredicate.Signature.denotes (frame.model other assignment)
        (HOL.PredicateFixedPoint.least signature.operator) :=
  signature.withGuards_least_denote (frame.model other assignment) (frame.model_fullDomains other assignment)
    shape active edge
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment shape signature.validShape readings.shapeEquation)
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment active signature.active readings.activeEquation)
    (by simpa only [HOL.RecursiveSpacePredicate.Signature.denote_closed] using
      ExactFormulaReadback.readEquation_denote frame other assignment edge signature.validEdge readings.edgeEquation)

#print axioms vectorResultSource_generated
#print axioms vectorChildSource_generated
#print axioms GuardReadings.operator_denote
#print axioms GuardReadings.least_denote

end Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

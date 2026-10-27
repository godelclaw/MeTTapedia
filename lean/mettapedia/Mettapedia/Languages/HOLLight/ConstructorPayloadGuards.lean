import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs
import Mettapedia.Languages.HOLLight.ConstructorPayload
import Mettapedia.Languages.HOLLight.IndexedConstructorDefinitions

/-!
# Primitive certificates for constructor payload membership

The generic introduction program proves that each encoded argument tuple
belongs to the emitted constructor-image predicate. Compilation uses the empty
axiom policy. Registering the closed predicate body uses the existing source
definition checker; this is not the complete recursive datatype guard.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ConstructorPayloadGuards

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation ProofExecution DefinitionAdapters
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def introduce (signature : List (List (HOL.Ty AtomicTy))) (occurrence : Fin signature.length)
    (arguments : HOL.FiniteConstructorEncoding.Arguments Symbol [] (signature.get occurrence))
    (origin : Origin) :=
  compileWithoutFunctionExtensionality emptyAxiomPolicy
    (HOL.FiniteConstructorEncoding.predicate_intro signature occurrence arguments)
    (HOL.FiniteConstructorEncoding.predicate_intro_free signature occurrence arguments)
    Naming.empty origin

def first := introduce ConstructorPayload.signature ⟨0, by decide⟩
  (.top, .bot, PUnit.unit) ("first-constructor-membership", 0)
def second := introduce ConstructorPayload.signature ⟨1, by decide⟩
  (.top, .bot, PUnit.unit) ("second-constructor-membership", 0)
def changed := introduce ConstructorPayload.signature ⟨0, by decide⟩
  (.bot, .top, PUnit.unit) ("changed-fields-membership", 0)

theorem first_accepted : (ProofSystem.checker emptyAxiomPolicy).check first.proof.result first.proof.certificate = true :=
  first.proof.accepted

def predicateSource : SourceTerm :=
  IndexedConstructorDefinitions.source
    (HOL.FiniteConstructorEncoding.predicate (Const := Symbol) ConstructorPayload.signature)

def definition : Option Registered.State :=
  IndexedConstructorDefinitions.define? emptyAxiomPolicy (Registered.empty ContextControls.coreContext)
    ("constructor-image-predicate", 0) (Name.global "constructorPayloadImage") predicateSource

set_option maxRecDepth 8192 in
theorem definition_accepted : definition.isSome = true := by decide +kernel

def defined : Registered.State := definition.get definition_accepted

theorem repeated_definition_refused :
    (IndexedConstructorDefinitions.define? emptyAxiomPolicy defined
      ("constructor-image-repeated", 0) (Name.global "constructorPayloadImage") predicateSource).isNone = true := by
  decide +kernel

#print axioms introduce
#print axioms first_accepted
#print axioms definition_accepted
#print axioms repeated_definition_refused

end Mettapedia.Languages.HOLLight.ConstructorPayloadGuards

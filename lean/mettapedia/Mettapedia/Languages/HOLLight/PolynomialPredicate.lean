import Mettapedia.Logic.HOL.PolynomialPredicate
import Mettapedia.Languages.HOLLight.RetainedCompilation
import Mettapedia.Languages.HOLLight.InferenceOnlyReplay
import Mettapedia.Languages.HOLLight.ExportReplay

/-!
# Empty-policy primitive proofs for polynomial predicate operators

Both programs quantify over constructor and child relations at two source type
variables. Monotonicity is generated from the actual positive operator body.
The fixed-point program instantiates the retained generic theorem and supplies
that generated proof. The resulting pointwise law has no external
monotonicity premise. These are primitive proof graphs, not native datatype
definition or recursive-function packages.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PolynomialPredicate
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open RetainedCompilation ReverseTranslation
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def source : AtomicTy := ⟨.var (Name.global "PolynomialSource"), rfl, rfl⟩
def layer : AtomicTy := ⟨.var (Name.global "PolynomialLayer"), rfl, rfl⟩

def monotonicity := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.monotonicity_schema (Const := Symbol) (.base source) (.base layer))
  (HOL.PolynomialPredicate.monotonicity_schema_functionExtensionalityFree (.base source) (.base layer))
  Naming.empty ("polynomial-predicate-monotonicity", 0)

def fixedPoint := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.fixed_point_schema (Const := Symbol) (.base source) (.base layer))
  (HOL.PolynomialPredicate.fixed_point_schema_functionExtensionalityFree (.base source) (.base layer))
  Naming.empty ("polynomial-predicate-fixed-point", 0)

theorem monotonicity_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    monotonicity.proof.result monotonicity.proof.certificate = true := monotonicity.proof.accepted

theorem fixedPoint_accepted_empty : (ProofSystem.checker emptyAxiomPolicy).check
    fixedPoint.proof.result fixedPoint.proof.certificate = true := fixedPoint.proof.accepted

set_option maxRecDepth 65536 in
theorem monotonicity_inference_only :
    InferenceOnlyReplay.inferenceOnly monotonicity.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance _ _ monotonicity_accepted_empty

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem fixedPoint_inference_only :
    InferenceOnlyReplay.inferenceOnly fixedPoint.proof.certificate.1 = true :=
  InferenceOnlyReplay.inference_only_of_empty_acceptance
    fixedPoint.proof.result fixedPoint.proof.certificate fixedPoint_accepted_empty

set_option maxRecDepth 65536 in
theorem monotonicity_axioms_empty : monotonicity.proof.result.axioms = ∅ := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem fixedPoint_axioms_empty : fixedPoint.proof.result.axioms = ∅ := by
  decide +kernel

def verdicts : List (String × Bool) :=
  [("polynomial monotonicity empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      monotonicity.proof.result monotonicity.proof.certificate),
   ("polynomial fixed point empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      fixedPoint.proof.result fixedPoint.proof.certificate),
   ("polynomial monotonicity physical inference graph", InferenceOnlyReplay.inferenceOnly monotonicity.proof.certificate.1),
   ("polynomial fixed point physical inference graph", InferenceOnlyReplay.inferenceOnly fixedPoint.proof.certificate.1),
   ("polynomial monotonicity no axiom dependencies", decide (monotonicity.proof.result.axioms = ∅)),
   ("polynomial fixed point no axiom dependencies", decide (fixedPoint.proof.result.axioms = ∅))]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
theorem verdicts_all : ∀ result ∈ verdicts, result.2 = true := by
  intro result present
  simp only [verdicts, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact monotonicity_accepted_empty
  · exact fixedPoint_accepted_empty
  · exact monotonicity_inference_only
  · exact fixedPoint_inference_only
  · simpa using monotonicity_axioms_empty
  · simpa using fixedPoint_axioms_empty

set_option maxRecDepth 65536 in
theorem monotonicity_verdict : (ProofSystem.checker emptyAxiomPolicy).check
    monotonicity.proof.result monotonicity.proof.certificate = true :=
  verdicts_all
    ("polynomial monotonicity empty-policy replay", (ProofSystem.checker emptyAxiomPolicy).check
      monotonicity.proof.result monotonicity.proof.certificate)
    (by exact List.mem_cons_self)

#print axioms monotonicity_accepted_empty
#print axioms fixedPoint_accepted_empty
end Mettapedia.Languages.HOLLight.PolynomialPredicate

/-! Closed higher-order lambda bodies define constructor and child relations.
The native declaration checker registers the actual bodies and retains its
exact equations without adding axiom dependencies. Operation arguments are
explicit; these definitions do not supply a datatype representation. -/

namespace Mettapedia.Languages.HOLLight.PolynomialPredicate.Relations
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation ReverseTranslation RetainedCompilation
local infixr:60 " ⇒ " => HOL.Ty.arr
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def position : AtomicTy := ⟨.var (Name.global "PolynomialPosition"), rfl, rfl⟩

def constructorBody : HOL.ClosedTerm Symbol
    (((.base layer) ⇒ .prop) ⇒ ((.base layer) ⇒ .base source) ⇒ (.base layer) ⇒ .base source ⇒ .prop) :=
  HOL.PolynomialPredicate.Relations.constructorDefinition (.base source) (.base layer)

def childBody : HOL.ClosedTerm Symbol
    (((.base layer) ⇒ (.base position) ⇒ .prop) ⇒ ((.base layer) ⇒ (.base position) ⇒ .base source) ⇒
      (.base layer) ⇒ .base source ⇒ .prop) :=
  HOL.PolynomialPredicate.Relations.childDefinition (.base source) (.base layer) (.base position)

def constructorCanonical := reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand constructorBody)
def childCanonical := reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand childBody)
def constructorSource := (PrimitiveTransport.checkedSource constructorCanonical).source
def childSource := (PrimitiveTransport.checkedSource childCanonical).source

def constructorName := Name.global "indexedConstructorRelation"
def childName := Name.global "indexedChildRelation"
def coreInstances := ExportReplay.instanceCertificates ContextControls.coreContext.signature

theorem constructor_admitted :
    (admitConstantInTheory ContextControls.coreContext coreInstances constructorName constructorSource).isSome = true := by
  decide +kernel

def constructorResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory ContextControls.coreContext coreInstances constructorName constructorSource).get constructor_admitted

def childInstances := ExportReplay.instanceCertificates constructorResult.context.signature

theorem child_admitted :
    (admitConstantInTheory constructorResult.context childInstances childName childSource).isSome = true := by
  decide +kernel

def childResult : ContextConstantDefinitionResult :=
  (admitConstantInTheory constructorResult.context childInstances childName childSource).get child_admitted

theorem constructor_axioms_empty : constructorResult.output.definitionTheorem.axioms = ∅ := by
  decide +kernel

theorem child_axioms_empty : childResult.output.definitionTheorem.axioms = ∅ := by
  decide +kernel

#print axioms constructor_admitted
#print axioms child_admitted
#print axioms constructor_axioms_empty
#print axioms child_axioms_empty


def constructorNames : Naming
    [HOL.Ty.base source, HOL.Ty.base layer, (.base layer ⇒ .base source), (.base layer ⇒ .prop)] :=
  Naming.cons (Name.global "point") (Naming.cons (Name.global "layer")
    (Naming.cons (Name.global "build") (Naming.cons (Name.global "valid") Naming.empty)))

def childNames : Naming
    [HOL.Ty.base source, HOL.Ty.base layer, (.base layer ⇒ .base position ⇒ .base source),
      (.base layer ⇒ .base position ⇒ .prop)] :=
  Naming.cons (Name.global "point") (Naming.cons (Name.global "layer")
    (Naming.cons (Name.global "childAt") (Naming.cons (Name.global "validPosition") Naming.empty)))

def constructorBeta := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.Relations.constructor_beta (Δ := [])
    (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
  (HOL.PolynomialPredicate.Relations.constructor_beta_functionExtensionalityFree _ _ _ _)
  constructorNames ("constructor-relation-beta", 0)

def childBeta := compileWithoutFunctionExtensionality emptyAxiomPolicy
  (HOL.PolynomialPredicate.Relations.child_beta (Δ := [])
    (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
  (HOL.PolynomialPredicate.Relations.child_beta_functionExtensionalityFree _ _ _ _)
  childNames ("child-relation-beta", 0)

theorem constructorBeta_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    constructorBeta.proof.result constructorBeta.proof.certificate = true := constructorBeta.proof.accepted

theorem childBeta_accepted : (ProofSystem.checker emptyAxiomPolicy).check
    childBeta.proof.result childBeta.proof.certificate = true := childBeta.proof.accepted

#print axioms constructorBeta_accepted
#print axioms childBeta_accepted



def definitionCommands : List ProofExecution.Registered.Command :=
  [.constant ("constructor-relation-definition", 0) constructorName constructorSource coreInstances,
   .constant ("child-relation-definition", 1) childName childSource childInstances]

def definitions : Option ProofExecution.Registered.State :=
  ProofExecution.Registered.replayFrom emptyAxiomPolicy
    (ProofExecution.Registered.empty ContextControls.coreContext) definitionCommands

theorem definitions_admitted : definitions.isSome = true := by decide +kernel

def definedState : ProofExecution.Registered.State := definitions.get definitions_admitted

theorem defined_state_valid : ProofExecution.Registered.Valid emptyAxiomPolicy definedState :=
  ProofExecution.Registered.replayFrom_preserves_derivations _ _ _ _
    (ProofExecution.Registered.empty_valid _ _) (Option.some_get definitions_admitted).symm

def verdicts : List (String × Bool) :=
  [("constructor relation closed definition admitted", (admitConstantInTheory
      ContextControls.coreContext coreInstances constructorName constructorSource).isSome),
   ("child relation closed definition admitted", (admitConstantInTheory
      constructorResult.context childInstances childName childSource).isSome),
   ("relation definitions replay as registered commands", definitions.isSome),
   ("constructor relation beta receipt checks", (ProofSystem.checker emptyAxiomPolicy).check
      constructorBeta.proof.result constructorBeta.proof.certificate),
   ("child relation beta receipt checks", (ProofSystem.checker emptyAxiomPolicy).check
      childBeta.proof.result childBeta.proof.certificate),
   ("redeclared constructor relation refused", (admitConstantInTheory
      constructorResult.context childInstances constructorName constructorSource).isNone)]

#print axioms definitions_admitted
#print axioms defined_state_valid

end Mettapedia.Languages.HOLLight.PolynomialPredicate.Relations

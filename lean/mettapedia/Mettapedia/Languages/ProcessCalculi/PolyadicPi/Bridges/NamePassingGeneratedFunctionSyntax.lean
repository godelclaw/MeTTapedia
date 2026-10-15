import Mettapedia.TypeTheory.ContextualStableFamiliesProducts
import Mettapedia.TypeTheory.CwfYonedaComparisonUniverse
import Mettapedia.TypeTheory.Calculi.NativeDependent.SourceCwfDependentAbstractionComparison
import Mettapedia.TypeTheory.DisplayedPresheafRepresentableFunctionEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedSpecifications

/-!
# Generated dependent function syntax for actual compiler specifications

At every source-program point, an independently authored dependent body
returns the actual translated caller origin and the argument in its varying
finite type. The raw lambda has its own typing tree and parser. Decoding
its complete native function recovers the original source function, whose
application agrees with the independently constructed compiler receipt
specification.

These contexts and natural-number terms belong to certificate-expression
syntax. They do not extend the operational lambda language or assert that
the emitted rho code executes natural-number data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntax

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Calculi.NativeDependent.Refinement
open SourceCwfDeclarations ContextualModelTelescopes NativeLocalTypeFormers
open CwfYonedaComparisonUniverse
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafPi
open DisplayedPresheafEvidenceApplication
open NamePassingDependentEvidence NamePassingGeneratedIndexedEvidence
open NamePassingGeneratedIndexedSpecifications DisplayedPresheafRepresentableEvidence

noncomputable section

abbrev source : Cwf.{1, 1, 1, 0} := representedModel familiesCwf.{0}
abbrev products := representedProducts ContextualStableFamiliesProducts.products.{0}

namespace CompilerSpecification

abbrev input : DisplayedFamily compiledPrograms :=
  DisplayedPresheafRepresentableFunctionEvidence.arguments Nat

abbrev output (root : sourcePrograms.Elements) :=
  DisplayedPresheafRepresentableFunctionEvidence.answers compilerMap root Nat (fun n => Fin (n + 1))

def value (n : Nat) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

abbrev argument (n : Nat) := DisplayedPresheafRepresentableFunctionEvidence.argumentSection
  (Q := compiledPrograms) Nat n

def body (root : sourcePrograms.Elements) : origins root ⟶
    reindexDisplayed compilerMap (piDisplayed input (output root)) :=
  DisplayedPresheafRepresentableFunctionEvidence.functionBody compilerMap root Nat
    (fun n => Fin (n + 1)) value

end CompilerSpecification

variable (root point : sourcePrograms.Elements)

def context : source.Ctx := ⟨(origins root).obj point⟩

def domain : source.Ty (context root point) :=
  ⟨fun _ => Nat⟩

def codomain : source.Ty (source.ext (context root point) (domain root point)) :=
  ⟨fun (supplied : Sigma (fun _ : (origins root).obj point => Nat)) =>
    (origins (compilerMap.mapElements.obj root)).obj (compilerMap.mapElements.obj point) ×
      Fin (supplied.2 + 1)⟩

def body : source.Tm (source.ext (context root point) (domain root point))
    (codomain root point) :=
  ⟨fun supplied => ⟨compilerMap.mapElements.map supplied.1,
    ⟨supplied.2, Nat.lt_succ_self supplied.2⟩⟩⟩

def originalFunction :
    source.Tm (context root point) (products.operations.pi (domain root point) (codomain root point)) :=
  products.operations.lam (body root point)

def rawLambda : TermExpr (symbols source) 1 := dependentLambdaTerm (body root point)

def rawLambdaFormed :
    Derivation (signature source) (.term (objectContext (⟨context root point⟩ : Base source))
      (rawLambda root point) (generatedProductType (domain root point) (codomain root point))) :=
  dependentLambdaFormed (body root point)

def generatedFunction :
    (generatedProductMeaning (domain root point) (codomain root point)).decoded.sections :=
  (model source).products.lam (dependentBodyValue (body root point))

theorem parsed_lambda_complete :
    (model source).evaluateTerm (objectScope (⟨context root point⟩ : Base source)) (rawLambda root point) =
      some ⟨generatedProductMeaning (domain root point) (codomain root point),
        sourceProductTermEquiv products (domain root point) (codomain root point)
          (originalFunction root point)⟩ :=
  dependent_lambda_source_read products (body root point)

def recoveredFunction :
    source.Tm (context root point) (products.operations.pi (domain root point) (codomain root point)) :=
  (sourceProductTermEquiv products (domain root point) (codomain root point)).symm
    (generatedFunction root point)

theorem recovered_original_function : recoveredFunction root point = originalFunction root point := by
  rw [recoveredFunction, generatedFunction,
    ← sourceProductTermEquiv_abstraction products (body root point)]
  exact (sourceProductTermEquiv products (domain root point) (codomain root point)).symm_apply_apply
    (originalFunction root point)

def answer (origin : (origins root).obj point) (n : Nat) :
    (origins (compilerMap.mapElements.obj root)).obj (compilerMap.mapElements.obj point) × Fin (n + 1) :=
  (recoveredFunction root point).down origin n

theorem answer_exact (origin : (origins root).obj point) (n : Nat) :
    answer root point origin n = ⟨compilerMap.mapElements.map origin, ⟨n, Nat.lt_succ_self n⟩⟩ := by
  rw [answer, recovered_original_function]
  rfl

def compilerAnswer (origin : (origins root).obj point) (n : Nat) :
    (CompilerSpecification.output root).obj
      ((sectionLift CompilerSpecification.input (CompilerSpecification.argument n)).mapElements.obj
        (compilerMap.mapElements.obj point)) :=
  (applyAt CompilerSpecification.input (CompilerSpecification.output root)
      (CompilerSpecification.argument n)).app (compilerMap.mapElements.obj point)
    (NamePassingGeneratedIndexedSpecifications.specificationEquiv
      (piDisplayed CompilerSpecification.input (CompilerSpecification.output root))
      (compilerMap.mapElements.obj point)
      (applySpecification (CompilerSpecification.body root) (compilerMap.mapElements.obj point)
        (suppliedReceipt (origins root) point origin)))

theorem compiler_answer_exact (origin : (origins root).obj point) (n : Nat) :
    compilerAnswer root point origin n =
      ⟨compilerMap.mapElements.map origin, ⟨n, Nat.lt_succ_self n⟩⟩ := by
  unfold compilerAnswer
  rw [specification_current_read, supplied_receipt_read]
  exact DisplayedPresheafRepresentableFunctionEvidence.receipt_application compilerMap root Nat
    (fun n => Fin (n + 1)) CompilerSpecification.value point origin n

theorem generated_answer_matches_compiler_receipt (origin : (origins root).obj point) (n : Nat) :
    answer root point origin n = compilerAnswer root point origin n :=
  (answer_exact root point origin n).trans (compiler_answer_exact root point origin n).symm

variable {root point}

theorem future_caller_readout {before after : sourcePrograms.Elements} (change : before ⟶ after)
    (origin : (origins root).obj before) (n : Nat) :
    (answer root after ((origins root).map change origin) n).1 =
      (origins (compilerMap.mapElements.obj root)).map (compilerMap.mapElements.map change)
        (answer root before origin n).1 := by
  rw [answer_exact, answer_exact]
  exact compilerMap.mapElements.map_comp origin change

theorem future_dependent_witness {before after : sourcePrograms.Elements} (change : before ⟶ after)
    (origin : (origins root).obj before) (n : Nat) :
    (answer root after ((origins root).map change origin) n).2 = (answer root before origin n).2 := by
  rw [answer_exact, answer_exact]

theorem future_complete_answer {before after : sourcePrograms.Elements} (change : before ⟶ after)
    (origin : (origins root).obj before) (n : Nat) :
    answer root after ((origins root).map change origin) n =
      ⟨(origins (compilerMap.mapElements.obj root)).map (compilerMap.mapElements.map change)
        (answer root before origin n).1, (answer root before origin n).2⟩ :=
  Prod.ext (future_caller_readout change origin n) (future_dependent_witness change origin n)

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedFunctionSyntax

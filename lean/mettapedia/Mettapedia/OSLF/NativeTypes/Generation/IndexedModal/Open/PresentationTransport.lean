import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Classifying
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContextLaws
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPresentationTransport

/-!
# Original operational expressions in the full native classifying model

The concrete presentation route installs the curried classifier alphabet and
then source-to-classifier injections. Original operational declarations retain
their independent meanings. Every open dependent expression and every ordered
rule tree is transported by the generic presentation machinery, and its full
classifying section agrees across the original and enriched presentations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.PresentationTransport

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent Calculi.NativeDependent.Refinement

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.PresentationTransport

variable (installed : Joined.Installed)

abbrev source := Presentation.of installed.indexed.operational.signature
abbrev core := Presentation.of (SourceModel.coreSignature installed)
abbrev target := Presentation.of (SourceModel.signature installed)

theorem preservesOperational : SignatureExtension.Preserves
    installed.indexed.operational.signature (SourceModel.coreSignature installed) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters _ := rfl
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank _ := rfl

/-- This is the actual declaration route through the two distinct alphabets. -/
def route : Route (source installed) (target installed) :=
  (Route.include (source installed)
    (Declarations.symbols (D := Pipeline.classifierSignature installed.indexed.operational)
      (CurriedInterfaces.interface installed.indexed))
    (SourceModel.coreSignature installed) (preservesOperational installed)).comp
    (Route.include (core installed) (SourceInjection.injectionSymbols installed.indexed)
      (SourceModel.signature installed) (Formation.preservesCore installed))

@[simp] theorem source_type {n : Nat} (expression : TypeExpr installed.indexed.operational.symbols n) :
    (route installed).type expression = Open.sourceType installed expression := rfl

@[simp] theorem source_term {n : Nat} (expression : TermExpr installed.indexed.operational.symbols n) :
    (route installed).term expression = Open.sourceTerm installed expression := rfl

@[simp] theorem source_context {n : Nat} (expression : ContextExpr installed.indexed.operational.symbols n) :
    (route installed).context expression = Open.sourceContext installed expression := rfl

/-- Restriction recovers the original contextual constructor/event model,
rather than postulating whole-expression semantic agreement. -/
theorem restrict_source :
    (route installed).restrict (Interpretation.model installed) = SourceModel.source installed := rfl

/-- Raw evaluator failure is preserved and reflected by this enrichment;
this statement makes no claim about changing the selected logic vocabulary. -/
theorem evaluation_failure {n : Nat} (expression : TermExpr installed.indexed.operational.symbols n)
    (scope : Scope (Interpretation.worlds installed) n) :
    (Interpretation.model installed).evaluateTerm scope (Open.sourceTerm installed expression) = none ↔
      (SourceModel.source installed).evaluateTerm scope expression = none := by
  rw [← source_term, (route installed).evaluateTerm, restrict_source]

noncomputable section

variable {n : Nat} (rawContext : ContextExpr installed.indexed.operational.symbols n)
    (rawTerm : TermExpr installed.indexed.operational.symbols n)
    (rawType : TypeExpr installed.indexed.operational.symbols n)
    (scope : Scope (Interpretation.worlds installed) n)
    (meaning : NativeLocalTypeFormers.NativeType scope.1)
    (contextRead : ((route installed).restrict (Interpretation.model installed)).evaluateContext rawContext = some scope)
    (typeRead : ((route installed).restrict (Interpretation.model installed)).evaluateType scope rawType = some meaning)
    {program : (Interpretation.worlds installed)ᵒᵖ ⥤ Type} (interface : program ⟶ scope.1)

/-- Independent original and enriched generated term classes have exactly
the same complete dependent reading at every natural program client. -/
theorem classifying_sections
    (tree : Derivation installed.indexed.operational.signature (.term rawContext rawTerm rawType)) :
    (Route.targetClient (route installed) (Interpretation.model installed)
      (Interpretation.realization installed) rawContext rawTerm rawType scope meaning contextRead typeRead interface).classifyingValueSection (Classifying.headers installed) ((route installed).termDerivation tree) =
    (Route.sourceClient (route installed) (Interpretation.model installed)
      (Interpretation.realization installed) rawContext rawTerm rawType scope meaning contextRead typeRead interface).classifyingValueSection installed.indexed.operational.formation tree :=
  Route.classifying_client_sections (route installed) (Interpretation.model installed)
    (Interpretation.realization installed) rawContext rawTerm rawType scope meaning contextRead typeRead interface
    installed.indexed.operational.formation (Classifying.headers installed) tree

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.PresentationTransport

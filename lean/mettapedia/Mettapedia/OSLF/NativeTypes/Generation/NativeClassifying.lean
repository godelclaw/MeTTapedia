import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations
import Mettapedia.OSLF.NativeTypes.Certificates.ClassifyingInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingUniversalProperty

/-!
# Classifying native models of computed authored declarations

The header formation argument is computed by the declaration installer.
Its generated contexts, dependent terms, propositions and logical conversion
feed the existing classifying construction. Interpretation into any qualified
target retains the full native local operations and dependent evidence.

This is classification of the installed declaration grammar. Authored
operational firing fibres and their comparison are separate additions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Contextual

universe c s t m p

variable {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
variable (installed : Installation language)

/-- The source is the actual quotient contextual grammar with dependent
logical operations, not an identity extension of the authored signature. -/
noncomputable abbrev classifying := ClassifyingCells.sourceModel installed.formation

variable {C : CwfWithTerminal.{c,s,t,m}}
variable (target : Refinement.Contextual.Interpretation.QualifiedModel.{0,c,s,t,m,p} installed.signature C)

noncomputable def interpretation := Classifying.interpretation installed.formation target

@[instance_reducible] noncomputable def interpretation_unique
    (other : Refinement.Abstract.ModelMap
      (ClassifyingCells.sourceModel.{0,max c s t m} installed.formation).data
      (target.commonCarrierLift.{0,c,s,t,m,p,0,0}).data) :
    Unique (installed.interpretation target ≅ other) :=
  Classifying.comparisonUnique installed.formation target other

theorem generated_family_header (symbol : installed.symbols.TypeSymbol) :
    (Refinement.Contextual.SyntacticModel.C installed.signature).toCwf.tySub
      ((Refinement.Contextual.SyntacticModel.data installed.formation).typeFamily symbol)
      (Refinement.Contextual.SyntacticModel.parameterComparison
        (Refinement.Contextual.SyntacticModel.typeHeader installed.formation symbol)).inv =
      Refinement.Contextual.QType.mk
        (Refinement.Contextual.SyntacticModel.originalFamily installed.formation symbol) :=
  Refinement.Contextual.SyntacticModel.family_at_original_header installed.formation symbol

theorem generated_constructor_header (symbol : installed.symbols.TermSymbol) :
    (Refinement.Contextual.SyntacticModel.C installed.signature).toCwf.tySub
      ((Refinement.Contextual.SyntacticModel.data installed.formation).termType symbol)
      (Refinement.Contextual.SyntacticModel.parameterComparison
        (Refinement.Contextual.SyntacticModel.termHeader installed.formation symbol)).inv =
      Refinement.Contextual.QType.mk
        (Refinement.Contextual.SyntacticModel.originalResult installed.formation symbol) :=
  Refinement.Contextual.SyntacticModel.result_at_original_header installed.formation symbol

end Mettapedia.OSLF.NativeTypes.Generation.NativeSignature.Installation

import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline
import Mettapedia.OSLF.NativeTypes.Certificates.ClassifyingInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingUniversalProperty

/-!
# Classifying the joined authored native grammar

Computed constructor and operational headers enter one quotient contextual
grammar. The classifying construction supplies its full dependent logical
operations. Every qualified interpretation receives an interpretation map
unique up to the earned model isomorphism.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent
open Mettapedia.GSLT.Core.ContextualLadder
open Refinement.Contextual

universe c s t m p
variable (installed : BindingPipeline.Installed)

noncomputable abbrev classifying := ClassifyingCells.sourceModel installed.formation

variable {C : CwfWithTerminal.{c,s,t,m}}
variable (target : Interpretation.QualifiedModel.{0,c,s,t,m,p} installed.signature C)

noncomputable def nativeInterpretation := Classifying.interpretation installed.formation target

@[instance_reducible] noncomputable def nativeInterpretation_unique
    (other : Refinement.Abstract.ModelMap
      (ClassifyingCells.sourceModel.{0,max c s t m} installed.formation).data
      (target.commonCarrierLift.{0,c,s,t,m,p,0,0}).data) :
    Unique (installed.nativeInterpretation target ≅ other) :=
  Classifying.comparisonUnique installed.formation target other

theorem generated_family_header (symbol : installed.symbols.TypeSymbol) :
    (SyntacticModel.C installed.signature).toCwf.tySub
      ((SyntacticModel.data installed.formation).typeFamily symbol)
      (SyntacticModel.parameterComparison
        (SyntacticModel.typeHeader installed.formation symbol)).inv =
      Refinement.Contextual.QType.mk
        (SyntacticModel.originalFamily installed.formation symbol) :=
  SyntacticModel.family_at_original_header installed.formation symbol

theorem generated_operation_header (symbol : installed.symbols.TermSymbol) :
    (SyntacticModel.C installed.signature).toCwf.tySub
      ((SyntacticModel.data installed.formation).termType symbol)
      (SyntacticModel.parameterComparison
        (SyntacticModel.termHeader installed.formation symbol)).inv =
      Refinement.Contextual.QType.mk
        (SyntacticModel.originalResult installed.formation symbol) :=
  SyntacticModel.result_at_original_header installed.formation symbol

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed

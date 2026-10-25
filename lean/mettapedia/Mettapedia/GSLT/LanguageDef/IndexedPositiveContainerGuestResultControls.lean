import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestMethodSpecialization
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls

/-!
# Source-code controls for mixed direct and Vector result arguments

The existing authored constructor has a length, a direct child, a payload,
a Vector field at that length, and a final direct child. Its three hypothesis
slots remain ordered after specializing the five-field method telescope.
The nested slot contains the actual native Vector result-projection prefix.
These are source/interface and beta-computation controls; they do not admit
the mixed constructor or decode an arbitrary open Vector variable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultControls

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation FunctionArgumentAdapters
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies TypedEquality.Normalization
open IndexedInductive.Guest (TermEnv mapEnv)
open IndexedPositiveContainerGuestTypes IndexedPositiveContainerGuestPlans
open IndexedPositiveContainerGuestResultArguments IndexedPositiveContainerGuestMethodSpecialization
open IndexedPositiveContainerGuestControls.Vectors

def resultSyntax : ResultSyntax I registry Tower.Head where
  viewType := by
    intro context n name entry registered output environment _ _ _
    obtain rfl := registered_entry registered
    exact vecApp natTm (lengthTerm output environment)
  projection := by
    intro context n name entry registered output environment element _ field
    obtain rfl := registered_entry registered
    exact appSpine (.const PositiveInductiveVectorTreeGuest.ResultFold.projectionName)
      [element, natTm, lengthTerm output environment, field]
  viewType_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := registered_entry registered
    change subst sigma (vecApp natTm (lengthTerm output environment)) =
      vecApp natTm (lengthTerm output (mapEnv (subst sigma) environment))
    simp only [vecApp, subst, natTm]
    exact congrArg (Tm.app (.app (.const vecName) (.const natName)))
      (lengthTerm_substitute output environment sigma)
  projection_substitute := by
    intro context n m name entry registered output environment element predicate field sigma
    obtain rfl := registered_entry registered
    change subst sigma (appSpine (.const PositiveInductiveVectorTreeGuest.ResultFold.projectionName)
      [element, natTm, lengthTerm output environment, field]) =
      appSpine (.const PositiveInductiveVectorTreeGuest.ResultFold.projectionName)
        [subst sigma element, natTm, lengthTerm output (mapEnv (subst sigma) environment), subst sigma field]
    simp only [appSpine, List.foldl_cons, List.foldl_nil, subst, natTm]
    exact congrArg (fun length => appSpine (.const PositiveInductiveVectorTreeGuest.ResultFold.projectionName)
      [subst sigma element, natTm, length, subst sigma field])
      (lengthTerm_substitute output environment sigma)

abbrev code := Mixed.code
def fields : Fin (fieldCount code) → Tower.Tm 7 := fieldTerms (ambient := 2) code
def motive : Tower.Tm 7 := NativeVectorAll.ResultView.predicate natTm
def constructor : Tower.Tm 7 := .var 5
def argumentSlots : List (Slot Tower.Head 7) := slots indexing containers resultSyntax code types PUnit.unit motive fields

theorem input_slots_exact : argumentSlots.map Slot.input =
    [.app motive (.var 3), NativeVectorAll.allType PositiveInductiveVectorTreeGuest.treeTm
      motive (.var 4) (.var 1), .app motive (.var 0)] := by decide +kernel

theorem output_slots_exact : argumentSlots.map Slot.output =
    [.app motive (.var 3), vecApp natTm (.var 4), .app motive (.var 0)] := by decide +kernel

theorem projection_slots_exact : argumentSlots.map Slot.projection =
    [.lam (.var 0), appSpine (.const PositiveInductiveVectorTreeGuest.ResultFold.projectionName)
      [PositiveInductiveVectorTreeGuest.treeTm, natTm, .var 4, .var 1], .lam (.var 0)] := by decide +kernel

theorem outer_arity_exact : argumentSlots.length = 3 := by decide +kernel

def wrongArity : Tower.Tm 7 := vecApp natTm (.var 2)

theorem payload_is_not_arity : (argumentSlots.map Slot.output)[1]? ≠ some wrongArity := by decide +kernel

def inputMethod : Tower.Tm 7 := methodBody indexing containers code types PUnit.unit motive constructor []
def outputMethod : Tower.Tm 7 := methodBody indexing (resultSyntax.viewRegistry containers)
  code types PUnit.unit motive constructor []

theorem source_method_specialized : instantiateFields code fields inputMethod =
    some (hypotheses (argumentSlots.map Slot.input)
      (conclusion indexing code PUnit.unit motive constructor fields)) := by
  rw [argumentSlots, slots_inputs indexing containers resultSyntax code types PUnit.unit motive fields]
  simpa only [inputMethod, List.nil_append] using
    methodBody_specialize indexing containers code types PUnit.unit motive constructor [] fields

theorem view_method_specialized : instantiateFields code fields outputMethod =
    some (hypotheses (argumentSlots.map Slot.output)
      (conclusion indexing code PUnit.unit motive constructor fields)) := by
  rw [argumentSlots, slots_outputs indexing containers resultSyntax code types PUnit.unit motive fields]
  simpa only [outputMethod, List.nil_append] using
    methodBody_specialize indexing (resultSyntax.viewRegistry containers)
      code types PUnit.unit motive constructor [] fields

def inductionArguments : List (Tower.Tm 7) := [.var 2, .var 1, .var 0]

theorem ordered_adapter_application : TelescopeAbstraction.BetaSteps
    (inductionArguments.foldl Tm.app (adapt argumentSlots (.var 6)))
    (((argumentSlots.zip inductionArguments).map
      (fun pair => Tm.app pair.1.projection pair.2)).foldl Tm.app (.var 6)) :=
  adapt_apply argumentSlots inductionArguments (.var 6) rfl

theorem reversed_outer_arguments_differ :
    ((argumentSlots.zip inductionArguments).map (fun pair => Tm.app pair.1.projection pair.2)) ≠
      ((argumentSlots.zip inductionArguments.reverse).map (fun pair => Tm.app pair.1.projection pair.2)) := by
  decide +kernel

#print axioms source_method_specialized
#print axioms view_method_specialized
#print axioms ordered_adapter_application
#print axioms payload_is_not_arity
#print axioms reversed_outer_arguments_differ

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestResultControls

import Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking

open Mettapedia.OSLF.Framework

/-!
# Ordered native structural controls on the original rho signature

These executions distinguish visible and cancelled quotation origins, argument
order, binder bodies, empty collection values and multiplicity. A pause cannot
turn an uninspected fibre into a negative native judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
open Mettapedia.OSLF.NativeTypes.Instances.Rho.CarrierEquations
open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedDecomposition
open Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking

def zero : Pattern := .apply "PZero" []
def quoted : Pattern := .apply "NQuote" [zero]
def suspended : Pattern := .apply "PDrop" [quoted]
def output : Pattern := .apply "POutput" [quoted, zero]
def body : Pattern := .lambda none (.apply "PDrop" [.bvar 0])
def guarded : Pattern := .apply "PInput" [quoted, body]

def outputRule : GrammarRule := rhoCalc.terms[4]
def inputRule : GrammarRule := rhoCalc.terms[5]

def quotationRead (budget : Nat) (source expected : Pattern) : Option Bool :=
  evaluate FreeTypeContext.empty [] quoteRule (equalInputs quoteRule (fun _ => expected)) budget source

def parallelRead (budget : Nat) (source expected : Pattern) : Option Bool :=
  evaluate FreeTypeContext.empty [] pparRule (equalInputs pparRule (fun _ => expected)) budget source

def outputRead (budget : Nat) (source first second : Pattern) : Option Bool :=
  evaluate FreeTypeContext.empty [] outputRule
    (equalInputs outputRule (fun position => if position.val = 0 then first else second)) budget source

def inputRead (budget : Nat) (source channel binding : Pattern) : Option Bool :=
  evaluate FreeTypeContext.empty [] inputRule
    (equalInputs inputRule (fun position => if position.val = 0 then channel else binding)) budget source

theorem quotation_visible_checked : quotationRead 1 quoted zero = some true := by cbv

theorem quotation_cancelled_checked : quotationRead 3 quoted suspended = some true := by cbv

theorem quotation_cancelled_paused : quotationRead 2 quoted suspended = none := by cbv

theorem quotation_wrong_body_refuted : quotationRead 3 quoted output = some false := by cbv

theorem quotation_distinct_body_classes : canonicalize zero ≠ canonicalize suspended := by decide

theorem quotation_complete_ordered_receipts :
    (values FreeTypeContext.empty [] quoteRule 3 quoted).map (fun value => value.val.arguments) =
      [[zero], [suspended]] := by cbv

theorem output_order_checked : outputRead 1 output quoted zero = some true := by cbv

theorem output_order_swapped_refuted : outputRead 3 output zero quoted = some false := by cbv

theorem binding_body_checked : inputRead 1 guarded quoted body = some true := by cbv

theorem binding_body_changed_refuted :
    inputRead 3 guarded quoted (.lambda none zero) = some false := by cbv

theorem ill_sorted_binding_body_refuted :
    inputRead 3 (.apply "PInput" [quoted, .lambda none (.bvar 0)]) quoted body = some false := by cbv

theorem empty_collection_argument_checked :
    parallelRead 2 zero (.collection .hashBag [] none) = some true := by cbv

theorem singleton_collection_argument_checked :
    parallelRead 2 output (.collection .hashBag [output] none) = some true := by cbv

theorem collection_multiplicity_retained :
    parallelRead 3 (.collection .hashBag [output, output] none)
      (.collection .hashBag [output] none) = some false := by cbv

theorem empty_argument_keeps_wrapper : bagArgument zero = .collection .hashBag [] none := by cbv

#guard quotationRead 1 quoted zero == some true
#guard quotationRead 2 quoted suspended == none
#guard quotationRead 3 quoted suspended == some true
#guard quotationRead 3 quoted output == some false
#guard outputRead 1 output quoted zero == some true
#guard outputRead 3 output zero quoted == some false
#guard inputRead 1 guarded quoted body == some true
#guard inputRead 3 guarded quoted (.lambda none zero) == some false
#guard parallelRead 2 zero (.collection .hashBag [] none) == some true
#guard parallelRead 3 (.collection .hashBag [output, output] none)
    (.collection .hashBag [output] none) == some false

#print axioms quotation_complete_ordered_receipts
#print axioms collection_multiplicity_retained

end Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedControls

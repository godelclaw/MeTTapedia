import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildren
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperationControls

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildrenControls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained RetainedWire
open InferenceCettaWire.AuthoredRule (typeTerm)
open InferenceCettaWire (encodePattern)
open Eval BridgeKit WireKit

def source : Pattern := .collection .hashBag
  [.apply "unit" [],.collection .hashBag
    [RetainedOperationControls.a,RetainedOperationControls.a,RetainedOperationControls.b] none] none

def records : List SourceOccurrence := componentOccurrences "unit" source

def a₀ : SourceOccurrence := records[0]'(by decide +kernel)
def a₁ : SourceOccurrence := records[1]'(by decide +kernel)
def b : SourceOccurrence := records[2]'(by decide +kernel)

def schemaBound : List TypeExpr := [.base "Name",.arrow (.base "Proc") (.base "Name")]
def path : List Nat := [8,2]
def schemas : List Pattern := [.fvar "first",.lambda none (.fvar "later")]

def originalFocus : Focus :=
  .original [.base "Proc",.base "Name"] (.base "Proc") source RetainedOperationControls.outer

def groupedFocus : Focus :=
  .grouped [.base "Name",.base "Proc",.base "Name"] records

def next : Continuation .spelling :=
  .lambda RetainedOperationControls.parent (some "capture-kept")
    (.multiLambda RetainedOperationControls.parent 2 ["x","y"]
      (.tail (RetainedOperationControls.groupsQuery 5 schemas [[a₀],[a₁,b]])
        RetainedOperationControls.next))

abbrev Allocation := List (List SourceOccurrence) × List SourceOccurrence

inductive Operation where
  | one (focus : Focus) (allocation : Allocation) (rest : Option String)
  | many (focus : Focus) (allocations : List Allocation) (rest : Option String)

def Operation.callTerm : Operation → Term
  | .one focus allocation rest => .application "gslt:collection-presentation:view-allocation-child"
      [.string "Proc",encodeList typeTerm schemaBound,encodeList .natural path,focusTerm focus,
        encodeList encodePattern schemas,InferenceCettaWire.encodeRest rest,continuationTerm next,
        allocationTerm (AllocationChildren.ordered allocation)]
  | .many focus allocations rest => .application "gslt:collection-presentation:view-allocation-children"
      [.string "Proc",encodeList typeTerm schemaBound,encodeList .natural path,focusTerm focus,
        encodeList encodePattern schemas,InferenceCettaWire.encodeRest rest,continuationTerm next,
        encodeList allocationTerm (allocations.map AllocationChildren.ordered)]

def Operation.tasks : Operation → List Task
  | .one focus allocation rest => allocationTasks schemaBound path focus schemas rest next allocation
  | .many focus allocations rest =>
      allocations.flatMap (allocationTasks schemaBound path focus schemas rest next)

theorem operation_returns (host : Effects.State) (operation : Operation) :
    PureReturns AllocationChildren.runtime [] host (encoded operation.callTerm) host
      (encoded (encodeList taskTerm operation.tasks)) := by
  cases operation with
  | one focus allocation rest =>
      exact AllocationChildren.child_returns _ AllocationChildren.runtime_agreement host "Proc"
        schemaBound path focus schemas rest next allocation.1 allocation.2
  | many focus allocations rest =>
      exact AllocationChildren.children_returns _ AllocationChildren.runtime_agreement host "Proc"
        schemaBound path focus schemas rest next allocations

def controls : List (String × Operation) :=
  [("one-empty-allocation",.one originalFocus ([],[]) none),
   ("one-empty-groups",.one originalFocus ([[],[]],[]) none),
   ("one-two-equal-occurrences",.one originalFocus ([[a₀],[a₁]],[]) none),
   ("one-rejects-residual-without-rest",.one originalFocus ([[a₀]],[a₁]) none),
   ("one-orders-complete-residual-records",.one originalFocus ([],[b,a₁,a₀]) (some "rest")),
   ("one-empty-rest-name-is-present",.one originalFocus ([[a₀]],[b,a₁]) (some "")),
   ("one-grouped-focus-keeps-actual-bound-context",.one groupedFocus ([[a₀],[a₁]],[b]) (some "rest")),
   ("one-grouped-focus-without-rest",.one groupedFocus ([[],[a₀,a₁,b]],[]) none),
   ("one-missing-group-left-for-child-validation",.one originalFocus ([],[]) (some "rest")),
   ("one-full-dependent-continuation",.one groupedFocus ([[a₁,a₀]],[]) (some "retained")),
   ("batch-empty",.many originalFocus [] none),
   ("batch-all-residuals-rejected",.many originalFocus [([],[a₀]),([],[a₁,b])] none),
   ("batch-continues-after-rejection",.many originalFocus [([[]],[a₀]),([[a₁]],[])] none),
   ("batch-rejection-between-answers",.many originalFocus
      [([[a₀]],[]),([],[b]),([[a₁]],[])] none),
   ("batch-keeps-duplicate-allocation-occurrences",.many originalFocus
      [([[a₀]],[b]),([[a₀]],[b])] (some "rest")),
   ("batch-distinguishes-equal-token-origins",.many originalFocus
      [([[a₀]],[b,a₁]),([[a₁]],[b,a₀])] (some "rest")),
   ("batch-grouped-context",.many groupedFocus
      [([[],[a₀,a₁]],[]),([[b]],[a₁,a₀])] (some "rest")),
   ("batch-accepts-empty-name",.many groupedFocus [([],[b,a₁,a₀])] (some ""))]

theorem actual_physical_records :
    records.length = 3 ∧ a₀.value = a₁.value ∧ a₀.address ≠ a₁.address ∧
      a₀.context.fill a₀.original = source ∧ a₁.context.fill a₁.original = source := by
  decide +kernel

theorem rejects_leftover_without_rest :
    (Operation.one originalFocus ([[a₀]],[a₁]) none).tasks = [] := by decide +kernel

theorem duplicate_allocations_remain_two :
    (Operation.many originalFocus [([[a₀]],[b]),([[a₀]],[b])] (some "rest")).tasks.length = 2 := by
  decide +kernel

#guard controls.length == 18
#print axioms operation_returns
#print axioms actual_physical_records
#print axioms rejects_leftover_without_rest
#print axioms duplicate_allocations_remain_two

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildrenControls

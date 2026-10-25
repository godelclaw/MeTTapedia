import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CanonicalSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionLoggedSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionBackendSource

/-!
# Collection search in the complete runtime

The collection allocator, machine and chronological search load above the
existing canonical runtime.  Their earlier source-level computations transfer
by agreement on the retained heads, including argument demand and clause order.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open Eval BridgeKit LibraryCheck

def collectionSupportProgram : Program :=
  (CollectionSelectionExecution.source.program.append
    ScopedCollectionExecution.source.program).append
      CollectionLoggedSearchExecution.source.program |>.append
        CollectionMatcherBackendExecution.source.program

def collectionBaseLibrary : BridgeKit.Library :=
  ⟨canonicalLibrary.runtime, collectionSupportProgram,
    ["gslt:collection:", "gslt:collection-machine:",
      "gslt:collection-plan:", "gslt:collection-search:", "gslt:collection-backend:"]⟩

private theorem collection_base_scoped :
    keptBy collectionBaseLibrary RuleExecutionProgram.scopedProgram = true := by decide +kernel
private theorem collection_base_typed :
    keptBy collectionBaseLibrary GeneralTypedSiteExecution.source.program = true := by decide +kernel
private theorem collection_base_descent :
    keptBy collectionBaseLibrary descentSource.program = true := by decide +kernel
private theorem collection_base_complete :
    keptBy collectionBaseLibrary completeSource.program = true := by decide +kernel
private theorem collection_base_laws :
    keptBy collectionBaseLibrary lawsSource.program = true := by decide +kernel
private theorem collection_base_canonical :
    keptBy collectionBaseLibrary canonicalSource.program = true := by decide +kernel

theorem collection_base_checked : collectionBaseLibrary.check = true := by
  refine check_of collectionBaseLibrary (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel)
  change keptBy collectionBaseLibrary (((((emptyProgram.append
    RuleExecutionProgram.scopedProgram).append GeneralTypedSiteExecution.source.program).append
      descentSource.program).append completeSource.program).append lawsSource.program |>.append
        canonicalSource.program) = true
  simp only [keptBy_append, collection_base_scoped, collection_base_typed,
    collection_base_descent, collection_base_complete, collection_base_laws,
    collection_base_canonical, Bool.and_true]
  decide

/-- Heads of the earlier collection runtime; later complete-machine layers
have separate namespaces.  Captured payloads are not traversed by this test. -/
def collectionRetained (head : String) : Bool :=
  !(["gslt:sites:", "gslt:descent:", "gslt:deep:", "gslt:step:",
    "gslt:complete:", "gslt:equations:", "gslt:classes:", "gslt:laws:",
    "gslt:canon:", "gslt:collection-backend:"].any fun namespaceHead => namespaceHead.isPrefixOf head)

theorem collection_retained_closed :
    ProgramClosed collectionRetained CollectionLoggedSearchExecution.library.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

private theorem retained_typed_equations :
    GeneralTypedSiteExecution.source.program.equations.filter
      (fun equation => collectionRetained equation.head) = [] := by decide +kernel
private theorem retained_descent_equations :
    descentSource.program.equations.filter (fun equation => collectionRetained equation.head) = [] := by
  decide +kernel
private theorem retained_complete_equations :
    completeSource.program.equations.filter (fun equation => collectionRetained equation.head) = [] := by
  decide +kernel
private theorem retained_laws_equations :
    lawsSource.program.equations.filter (fun equation => collectionRetained equation.head) = [] := by
  decide +kernel
private theorem retained_canonical_equations :
    canonicalSource.program.equations.filter (fun equation => collectionRetained equation.head) = [] := by
  decide +kernel
private theorem retained_backend_equations :
    CollectionMatcherBackendExecution.source.program.equations.filter
      (fun equation => collectionRetained equation.head) = [] := by decide +kernel

private theorem retained_typed_declarations :
    GeneralTypedSiteExecution.source.program.declarations.filter
      (retainedCallDeclaration collectionRetained) = [] := by decide +kernel
private theorem retained_descent_declarations :
    descentSource.program.declarations.filter (retainedCallDeclaration collectionRetained) = [] := by
  decide +kernel
private theorem retained_complete_declarations :
    completeSource.program.declarations.filter (retainedCallDeclaration collectionRetained) = [] := by
  decide +kernel
private theorem retained_laws_declarations :
    lawsSource.program.declarations.filter (retainedCallDeclaration collectionRetained) = [] := by
  decide +kernel
private theorem retained_canonical_declarations :
    canonicalSource.program.declarations.filter (retainedCallDeclaration collectionRetained) = [] := by
  decide +kernel
private theorem retained_backend_declarations :
    CollectionMatcherBackendExecution.source.program.declarations.filter
      (retainedCallDeclaration collectionRetained) = [] := by decide +kernel

theorem collection_base_agreement :
    ProgramAgreementOn collectionRetained CollectionLoggedSearchExecution.library.runtime
      collectionBaseLibrary.runtime := by
  apply programAgreementOn_of_retained_rows
  all_goals
    simp only [collectionBaseLibrary, collectionSupportProgram,
      CollectionLoggedSearchExecution.library, ScopedCollectionExecution.library,
      CollectionSelectionExecution.library, CollectionSelectionExecution.scopedLibrary,
      canonicalLibrary, lawsLibrary, completeLibrary, descentLibrary, typedLibrary,
      scopedLibrary, Library.runtime, SpaceSemantics.Program.append,
      List.filter_append, retained_typed_equations, retained_descent_equations,
      retained_complete_equations, retained_laws_equations, retained_canonical_equations,
      retained_backend_equations,
      retained_typed_declarations, retained_descent_declarations,
      retained_complete_declarations, retained_laws_declarations,
      retained_canonical_declarations, retained_backend_declarations, List.nil_append, List.append_nil,
      emptyProgram, List.append_assoc]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

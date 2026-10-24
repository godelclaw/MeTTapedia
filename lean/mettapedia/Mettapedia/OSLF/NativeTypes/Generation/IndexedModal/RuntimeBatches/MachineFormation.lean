import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.PolicyControls

/-! Runtime controls for joined indexed modal formation and receipts.

The qualification command executes this action explicitly. Importing the
library retains the action without running the regression panel.
-/

open Mettapedia.OSLF.NativeTypes.Generation
open IndexedModal

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.RuntimeBatches.MachineFormation

def check : IO Unit :=
  JoinedRuntime.formation BindingPipeline.Controls.originalMachine

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.RuntimeBatches.MachineFormation

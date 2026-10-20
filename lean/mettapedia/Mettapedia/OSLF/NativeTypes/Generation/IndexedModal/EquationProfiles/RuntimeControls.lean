import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.ReceiptControls
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.OccurrenceControls

/-! # Executable full-receipt equation-profile controls -/

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.RuntimeControls

open Mettapedia.OSLF.MeTTaIL.GeneralCompletedFrontierControls

#guard (ReceiptControls.test ⟨0, by decide⟩).check (completed true)
#guard (ReceiptControls.test ⟨1, by decide⟩).check (completed true)
#guard !(ReceiptControls.test ⟨1, by decide⟩).check ReceiptControls.firstOnly
#guard (ReceiptControls.test ⟨1, by decide⟩).readout ReceiptControls.firstOnly == .unknown

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.EquationProfiles.RuntimeControls

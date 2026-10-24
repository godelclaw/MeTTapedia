import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestAdmission

/-!
# Independent source and target checks for the solved constructor.

The producer, checker, source requests and proof limits are unchanged.
-/

set_option autoImplicit false
set_option Elab.async false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem solvedLeftAccepted :
    endpointAccepted solvedContext solvedLeft solvedIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem solvedRightAccepted :
    endpointAccepted solvedContext solvedRight solvedIotaType = true := by
  decide +kernel


#print axioms solvedLeftAccepted
#print axioms solvedRightAccepted

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

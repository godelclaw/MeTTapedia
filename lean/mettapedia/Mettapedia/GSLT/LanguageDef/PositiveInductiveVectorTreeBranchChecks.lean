import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuestAdmission

/-!
# Independent source, bundle, target and refusal checks for the Vector branch.

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
theorem branchLeftAccepted :
    endpointAccepted branchContext branchLeft branchIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem branchBundleAccepted :
    endpointAccepted branchContext branchBundle branchBundleType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem branchRightAccepted :
    endpointAccepted branchContext branchRight branchIotaType = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem unbundledBranchRefused :
    endpointAccepted branchContext
      (.app (.app (.app (.var 2) (.var 1)) (.var 0)) (.var 0))
      branchIotaType = false := by
  decide +kernel


#print axioms branchLeftAccepted
#print axioms branchBundleAccepted
#print axioms branchRightAccepted
#print axioms unbundledBranchRefused

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

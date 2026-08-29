import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPairingTargetAwareBoundary

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24HexagonPairingTargetAwareBoundary

/-- The flat certificate checks every adversary word for the red--purple pair. -/
theorem allSixCandidateCheck_redPurple :
    allSixCandidateCheck .redPurple = true := by
  rfl

end GoertzelV24HexagonPairingTargetAwareBoundary
end Mettapedia.GraphTheory.FourColor

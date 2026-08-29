import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPersistentKempeAdversaryCore

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Red-blue certificate for the persistent hexagon adversary

This file isolates one closed Boolean computation so that the kernel audit
does not materialize all three colour-pair certificates in one term graph.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24HexagonPersistentKempeAdversary

open GoertzelV24HexagonPairingTargetAwareBoundary

/-- The persistent adversary audit succeeds for the red-blue pair. -/
theorem allPersistentRows_redBlue :
    allPersistentRows TaitColorPair.redBlue = true := by
  rfl

end GoertzelV24HexagonPersistentKempeAdversary
end Mettapedia.GraphTheory.FourColor

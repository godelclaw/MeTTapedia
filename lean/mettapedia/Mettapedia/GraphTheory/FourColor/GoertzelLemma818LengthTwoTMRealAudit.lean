import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMEmptyFibers0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMEmptyFibers1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMEmptyFibers2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMEmptyFibers3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMEmptyFibers4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMRealFiberSmallBridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberOnePassRealBridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberRemainingRealBridge

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTMRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Real `chainLKRInAudit` assembly for the length-two `normal,mirror` word

This module combines the 36 nonempty real-fiber bridge theorems with the 45
empty-fiber extraction theorems and proves the actual length-two audit Boolean
for `tmWord`.
-/

theorem tmAllRealFibersConnected :
    colorAssignments4.all (fun key =>
      chainFiberConnected tmWord (chainFiberFrom tmWord (allChainStates tmWord) key)) = true := by
  rw [tmColorAssignments_eq_fiberKeys]
  simp [tmFiber0RealFiberConnected,
    tmFiber1RealFiberConnected,
    tmFiber2RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber3RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber4RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber5RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber6RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber7RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber8RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber9RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber10RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber11RealFiberConnected,
    tmFiber12RealFiberConnected,
    tmFiber13RealFiberConnected,
    tmFiber14RealFiberConnected,
    tmFiber15RealFiberConnected,
    tmFiber16RealFiberConnected,
    tmFiber17RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber18RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber19RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber20RealFiberConnected,
    tmFiber21RealFiberConnected,
    tmFiber22RealFiberConnected,
    tmFiber23RealFiberConnected,
    tmFiber24RealFiberConnected,
    tmFiber25RealFiberConnected,
    tmFiber26RealFiberConnected,
    tmFiber27RealFiberConnected,
    tmFiber28RealFiberConnected,
    tmFiber29RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber30RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber31RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber32RealFiberConnected,
    tmFiber33RealFiberConnected,
    tmFiber34RealFiberConnected,
    tmFiber35RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber36RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber37RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber38RealFiberConnected,
    tmFiber39RealFiberConnected,
    tmFiber40RealFiberConnected,
    tmFiber41RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber42RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber43RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber44RealFiberConnected,
    tmFiber45RealFiberConnected,
    tmFiber46RealFiberConnected,
    tmFiber47RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber48RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber49RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber50RealFiberConnected,
    tmFiber51RealFiberConnected,
    tmFiber52RealFiberConnected,
    tmFiber53RealFiberConnected,
    tmFiber54RealFiberConnected,
    tmFiber55RealFiberConnected,
    tmFiber56RealFiberConnected,
    tmFiber57RealFiberConnected,
    tmFiber58RealFiberConnected,
    tmFiber59RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber60RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber61RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber62RealFiberConnected,
    tmFiber63RealFiberConnected,
    tmFiber64RealFiberConnected,
    tmFiber65RealFiberConnected,
    tmFiber66RealFiberConnected,
    tmFiber67RealFiberConnected,
    tmFiber68RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber69RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber70RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber71RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber72RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber73RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber74RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber75RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber76RealFiberConnected,
    GoertzelLemma818LengthTwoTMRealFiberBridge.tmFiber77RealFiberConnected,
    tmFiber78RealFiberConnected,
    tmFiber79RealFiberConnected,
    tmFiber80RealFiberConnected]

theorem tmChainLKRInAudit_ok :
    chainLKRInAudit tmWord = true := by
  unfold chainLKRInAudit
  simp [tmAllChainStates_compatible, tmAllRealFibersConnected]

end GoertzelLemma818LengthTwoTMRealAudit

end Mettapedia.GraphTheory.FourColor

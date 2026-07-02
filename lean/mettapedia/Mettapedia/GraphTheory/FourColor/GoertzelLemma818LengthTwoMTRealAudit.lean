import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTEmptyFibers0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTEmptyFibers1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTEmptyFibers2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTEmptyFibers3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTEmptyFibers4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTRealFiberSmallBridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMTLargeFiberRealBridge

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorTauCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Real `chainLKRInAudit` assembly for the length-two `mirror,normal` word
-/

theorem mtAllRealFibersConnected :
    colorAssignments4.all (fun key =>
      chainFiberConnected mtWord (chainFiberFrom mtWord (allChainStates mtWord) key)) = true := by
  rw [mtColorAssignments_eq_fiberKeys]
  simp [mtFiber0RealFiberConnected,
    mtFiber1RealFiberConnected,
    mtFiber2RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber3RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber4RealFiberConnected,
    mtFiber5RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber6RealFiberConnected,
    mtFiber7RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber8RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber9RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber10RealFiberConnected,
    mtFiber11RealFiberConnected,
    mtFiber12RealFiberConnected,
    mtFiber13RealFiberConnected,
    mtFiber14RealFiberConnected,
    mtFiber15RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber16RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber17RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber18RealFiberConnected,
    mtFiber19RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber20RealFiberConnected,
    mtFiber21RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber22RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber23RealFiberConnected,
    mtFiber24RealFiberConnected,
    mtFiber25RealFiberConnected,
    mtFiber26RealFiberConnected,
    mtFiber27RealFiberConnected,
    mtFiber28RealFiberConnected,
    mtFiber29RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber30RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber31RealFiberConnected,
    mtFiber32RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber33RealFiberConnected,
    mtFiber34RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber35RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber36RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber37RealFiberConnected,
    mtFiber38RealFiberConnected,
    mtFiber39RealFiberConnected,
    mtFiber40RealFiberConnected,
    mtFiber41RealFiberConnected,
    mtFiber42RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber43RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber44RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber45RealFiberConnected,
    mtFiber46RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber47RealFiberConnected,
    mtFiber48RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber49RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber50RealFiberConnected,
    mtFiber51RealFiberConnected,
    mtFiber52RealFiberConnected,
    mtFiber53RealFiberConnected,
    mtFiber54RealFiberConnected,
    mtFiber55RealFiberConnected,
    mtFiber56RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber57RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber58RealFiberConnected,
    mtFiber59RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber60RealFiberConnected,
    mtFiber61RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber62RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber63RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber64RealFiberConnected,
    mtFiber65RealFiberConnected,
    mtFiber66RealFiberConnected,
    mtFiber67RealFiberConnected,
    mtFiber68RealFiberConnected,
    mtFiber69RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber70RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber71RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber72RealFiberConnected,
    mtFiber73RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber74RealFiberConnected,
    mtFiber75RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber76RealFiberConnected,
    GoertzelLemma818LengthTwoMTRealFiberBridge.mtFiber77RealFiberConnected,
    mtFiber78RealFiberConnected,
    mtFiber79RealFiberConnected,
    mtFiber80RealFiberConnected]

theorem mtChainLKRInAudit_ok :
    chainLKRInAudit mtWord = true := by
  unfold chainLKRInAudit
  simp [mtAllChainStates_compatible, mtAllRealFibersConnected]

end GoertzelLemma818LengthTwoMTRealAudit

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMEmptyFibers0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMEmptyFibers1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMEmptyFibers2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMEmptyFibers3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMEmptyFibers4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMRealFiberSmallBridge5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoMMLargeFiberRealBridge

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoMMRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818MirrorMirrorCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Real `chainLKRInAudit` assembly for the length-two `mirror,mirror` word
-/

theorem mmAllRealFibersConnected :
    colorAssignments4.all (fun key =>
      chainFiberConnected mmWord (chainFiberFrom mmWord (allChainStates mmWord) key)) = true := by
  rw [mmColorAssignments_eq_fiberKeys]
  simp [mmFiber0RealFiberConnected,
    mmFiber1RealFiberConnected,
    mmFiber2RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber3RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber4RealFiberConnected,
    mmFiber5RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber6RealFiberConnected,
    mmFiber7RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber8RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber9RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber10RealFiberConnected,
    mmFiber11RealFiberConnected,
    mmFiber12RealFiberConnected,
    mmFiber13RealFiberConnected,
    mmFiber14RealFiberConnected,
    mmFiber15RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber16RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber17RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber18RealFiberConnected,
    mmFiber19RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber20RealFiberConnected,
    mmFiber21RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber22RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber23RealFiberConnected,
    mmFiber24RealFiberConnected,
    mmFiber25RealFiberConnected,
    mmFiber26RealFiberConnected,
    mmFiber27RealFiberConnected,
    mmFiber28RealFiberConnected,
    mmFiber29RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber30RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber31RealFiberConnected,
    mmFiber32RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber33RealFiberConnected,
    mmFiber34RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber35RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber36RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber37RealFiberConnected,
    mmFiber38RealFiberConnected,
    mmFiber39RealFiberConnected,
    mmFiber40RealFiberConnected,
    mmFiber41RealFiberConnected,
    mmFiber42RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber43RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber44RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber45RealFiberConnected,
    mmFiber46RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber47RealFiberConnected,
    mmFiber48RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber49RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber50RealFiberConnected,
    mmFiber51RealFiberConnected,
    mmFiber52RealFiberConnected,
    mmFiber53RealFiberConnected,
    mmFiber54RealFiberConnected,
    mmFiber55RealFiberConnected,
    mmFiber56RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber57RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber58RealFiberConnected,
    mmFiber59RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber60RealFiberConnected,
    mmFiber61RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber62RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber63RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber64RealFiberConnected,
    mmFiber65RealFiberConnected,
    mmFiber66RealFiberConnected,
    mmFiber67RealFiberConnected,
    mmFiber68RealFiberConnected,
    mmFiber69RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber70RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber71RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber72RealFiberConnected,
    mmFiber73RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber74RealFiberConnected,
    mmFiber75RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber76RealFiberConnected,
    GoertzelLemma818LengthTwoMMRealFiberBridge.mmFiber77RealFiberConnected,
    mmFiber78RealFiberConnected,
    mmFiber79RealFiberConnected,
    mmFiber80RealFiberConnected]

theorem mmChainLKRInAudit_ok :
    chainLKRInAudit mmWord = true := by
  unfold chainLKRInAudit
  simp [mmAllChainStates_compatible, mmAllRealFibersConnected]

end GoertzelLemma818LengthTwoMMRealAudit

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTEmptyFibers0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTEmptyFibers1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTEmptyFibers2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTEmptyFibers3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTTEmptyFibers4

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818LengthTwoTTRealAudit

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoRealFiberBridgePrototype

/-!
# Real `chainLKRInAudit` assembly for the length-two `tau,tau` word

This module combines the 36 nonempty real-fiber bridge theorems with the 45
empty-fiber extraction theorems and proves the actual length-two audit Boolean
for `ttWord`.
-/

theorem ttAllRealFibersConnected :
    colorAssignments4.all (fun key =>
      chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) key)) = true := by
  rw [ttColorAssignments_eq_fiberKeys]
  simp [ttFiber0RealFiberConnected,
    ttFiber1RealFiberConnected,
    ttFiber2RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber3RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber4RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber5RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber6RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber7RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber8RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber9RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber10RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber11RealFiberConnected,
    ttFiber12RealFiberConnected,
    ttFiber13RealFiberConnected,
    ttFiber14RealFiberConnected,
    ttFiber15RealFiberConnected,
    ttFiber16RealFiberConnected,
    ttFiber17RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber18RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber19RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber20RealFiberConnected,
    ttFiber21RealFiberConnected,
    ttFiber22RealFiberConnected,
    ttFiber23RealFiberConnected,
    ttFiber24RealFiberConnected,
    ttFiber25RealFiberConnected,
    ttFiber26RealFiberConnected,
    ttFiber27RealFiberConnected,
    ttFiber28RealFiberConnected,
    ttFiber29RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber30RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber31RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber32RealFiberConnected,
    ttFiber33RealFiberConnected,
    ttFiber34RealFiberConnected,
    ttFiber35RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber36RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber37RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber38RealFiberConnected,
    ttFiber39RealFiberConnected,
    ttFiber40RealFiberConnected,
    ttFiber41RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber42RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber43RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber44RealFiberConnected,
    ttFiber45RealFiberConnected,
    ttFiber46RealFiberConnected,
    ttFiber47RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber48RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber49RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber50RealFiberConnected,
    ttFiber51RealFiberConnected,
    ttFiber52RealFiberConnected,
    ttFiber53RealFiberConnected,
    ttFiber54RealFiberConnected,
    ttFiber55RealFiberConnected,
    ttFiber56RealFiberConnected,
    ttFiber57RealFiberConnected,
    ttFiber58RealFiberConnected,
    ttFiber59RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber60RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber61RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber62RealFiberConnected,
    ttFiber63RealFiberConnected,
    ttFiber64RealFiberConnected,
    ttFiber65RealFiberConnected,
    ttFiber66RealFiberConnected,
    ttFiber67RealFiberConnected,
    ttFiber68RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber69RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber70RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber71RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber72RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber73RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber74RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber75RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber76RealFiberConnected,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber77RealFiberConnected,
    ttFiber78RealFiberConnected,
    ttFiber79RealFiberConnected,
    ttFiber80RealFiberConnected]

theorem ttChainLKRInAudit_ok :
    chainLKRInAudit ttWord = true := by
  unfold chainLKRInAudit
  simp [ttAllChainStates_compatible, ttAllRealFibersConnected]

end GoertzelLemma818LengthTwoTTRealAudit

end Mettapedia.GraphTheory.FourColor

import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchShape
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchRedZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchRedRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchRedBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchRedPurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueContractSearchRed_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .red)
          [(twentiethCatalogueContractSearchFirstComponent, .red)]
            twentiethCatalogueContractSearchRemaining = true := by
  change
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .red)
          [(twentiethCatalogueContractSearchFirstComponent, .red)]
            (twentiethCatalogueContractSearchSecondComponent ::
              twentiethCatalogueContractSearchTail) = true
  apply SearchTree.checkBy_of_isNode_and_children
  · exact twentiethCatalogueContractSearchRed_isNode
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchRedZero_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchRedRed_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchRedBlue_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchRedPurple_checker

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor

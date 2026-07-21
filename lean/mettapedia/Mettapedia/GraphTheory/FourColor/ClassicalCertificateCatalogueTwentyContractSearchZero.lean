import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchShape
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchZeroZero
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchZeroRed
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchZeroBlue
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchZeroPurple

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

theorem twentiethCatalogueContractSearchZero_checker :
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .zero)
          [(twentiethCatalogueContractSearchFirstComponent, .zero)]
            twentiethCatalogueContractSearchRemaining = true := by
  change
    SearchTree.checkBy twentiethCatalogueComponentsValid
      twentiethCatalogueRing twentiethCatalogueHasContractTrace
        (twentiethCatalogueContractSearchFirstBranch .zero)
          [(twentiethCatalogueContractSearchFirstComponent, .zero)]
            (twentiethCatalogueContractSearchSecondComponent ::
              twentiethCatalogueContractSearchTail) = true
  apply SearchTree.checkBy_of_isNode_and_children
  · exact twentiethCatalogueContractSearchZero_isNode
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchZeroZero_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchZeroRed_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchZeroBlue_checker
  · simpa [twentiethCatalogueContractSearchBranch] using
      twentiethCatalogueContractSearchZeroPurple_checker

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
